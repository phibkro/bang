import { config } from "./config.ts";
import { runInJail } from "./jail.ts";
import { TokenBucket, ConcurrencyGate, QueueFullError } from "./limits.ts";

const rate = new TokenBucket(config.rateCapacity, config.rateRefillPerSec);
const gate = new ConcurrencyGate(config.maxConcurrent, config.maxQueue);
setInterval(() => rate.sweep(), 60_000).unref?.();

const json = (body: unknown, status = 200): Response =>
  new Response(JSON.stringify(body), {
    status,
    headers: { "content-type": "application/json" },
  });

function clientIp(req: Request, server: { requestIP?: (r: Request) => { address: string } | null }): string {
  // Trust XFF only if you front this with a proxy you control; otherwise it's
  // spoofable. Default to the socket peer (Bun's requestIP) — the honest source.
  const xff = req.headers.get("x-forwarded-for");
  if (xff) return xff.split(",")[0]!.trim();
  return server.requestIP?.(req)?.address ?? "unknown";
}

type RunBody = { source?: unknown; fuel?: unknown; stdin?: unknown };

const server = Bun.serve({
  port: config.port,
  // Cap total request wall-clock at the service edge (seconds), independent of
  // the jail's own kill — a slow/large upload can't hold a slot forever.
  idleTimeout: Math.ceil(config.requestTimeoutMs / 1000) + 5,

  async fetch(req, srv) {
    const url = new URL(req.url);

    if (req.method === "GET" && url.pathname === "/health") {
      return json({ ok: true, jail: config.jail.enabled });
    }

    if (req.method !== "POST" || url.pathname !== "/run") {
      return json({ error: "not found — POST /run" }, 404);
    }

    // Rate-limit by IP (cost control).
    const ip = clientIp(req, srv);
    if (!rate.take(ip)) {
      return json({ error: "rate limit exceeded" }, 429);
    }

    // Body-size cap BEFORE reading the whole thing into memory. Content-Length
    // is the cheap gate; the actual read is still bounded because Bun caps it,
    // but we reject early on a declared oversize.
    const declaredLen = Number(req.headers.get("content-length") ?? "0");
    if (declaredLen > config.maxBodyBytes) {
      return json({ error: `payload too large (max ${config.maxBodyBytes} bytes)` }, 413);
    }

    const raw = await req.arrayBuffer();
    if (raw.byteLength > config.maxBodyBytes) {
      return json({ error: `payload too large (max ${config.maxBodyBytes} bytes)` }, 413);
    }

    let body: RunBody;
    try {
      body = JSON.parse(new TextDecoder().decode(raw));
    } catch {
      return json({ error: "body must be JSON" }, 400);
    }

    if (typeof body.source !== "string" || body.source.length === 0) {
      return json({ error: "field 'source' (non-empty string) is required" }, 400);
    }
    if (body.stdin !== undefined && typeof body.stdin !== "string") {
      return json({ error: "field 'stdin' must be a string when present" }, 400);
    }

    // Fuel: caller declares intent; server caps it (config is the ceiling).
    let fuel = config.defaultFuel;
    if (body.fuel !== undefined) {
      if (typeof body.fuel !== "number" || !Number.isInteger(body.fuel) || body.fuel <= 0) {
        return json({ error: "field 'fuel' must be a positive integer" }, 400);
      }
      fuel = Math.min(body.fuel, config.maxFuel);
    }

    let release: (() => void) | undefined;
    try {
      release = await gate.acquire();
    } catch (e) {
      if (e instanceof QueueFullError) {
        return json({ error: "server busy — try again shortly" }, 503);
      }
      throw e;
    }

    try {
      const result = await runInJail(
        body.source,
        fuel,
        body.stdin as string | undefined,
        config,
      );
      return json({
        stdout: result.stdout,
        stderr: result.stderr,
        exit: result.exit,
        timed_out: result.timedOut,
        duration_ms: result.durationMs,
        fuel,
      });
    } catch (e) {
      // A jail-invocation failure (e.g. systemd-run missing) is a SERVER fault,
      // not a program result — surface it loudly, don't pretend the run happened.
      return json({ error: `run failed: ${(e as Error).message}` }, 500);
    } finally {
      release?.();
    }
  },
});

console.error(
  `bang /run service on :${server.port} — jail=${config.jail.enabled} ` +
    `maxBody=${config.maxBodyBytes}B fuelCap=${config.maxFuel} bin=${config.bangBin}`,
);
