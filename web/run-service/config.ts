// Every limit is a boundary the caller/operator declares — no surprising defaults.
// Overridable by env so the operator's systemd unit is the single source of truth
// for the deployed jail; the code just reads it.

const num = (name: string, fallback: number): number => {
  const v = process.env[name];
  if (v === undefined) return fallback;
  const n = Number(v);
  if (!Number.isFinite(n) || n <= 0) {
    throw new Error(`${name}=${v} is not a positive number`);
  }
  return n;
};

const bool = (name: string, fallback: boolean): boolean => {
  const v = process.env[name];
  if (v === undefined) return fallback;
  return v === "1" || v === "true";
};

export const config = {
  port: num("RUN_PORT", 8787),

  // Request-shape caps (the abuse surface is resource exhaustion — §3 of the
  // interactive-tour design; there is no data-isolation threat because the
  // language has no FS/net/ambient-IO op).
  maxBodyBytes: num("RUN_MAX_BODY_BYTES", 64 * 1024), // 64 KiB source cap → 413
  maxConcurrent: num("RUN_MAX_CONCURRENT", 4), // in-flight jailed runs; excess queues
  maxQueue: num("RUN_MAX_QUEUE", 32), // queued-and-waiting cap → 503
  requestTimeoutMs: num("RUN_REQUEST_TIMEOUT_MS", 15_000), // wall-clock the client waits

  // Per-IP token bucket (cost control, not safety — safety is the jail).
  rateCapacity: num("RUN_RATE_CAPACITY", 20), // bucket size (burst)
  rateRefillPerSec: num("RUN_RATE_REFILL_PER_SEC", 1), // tokens/sec sustained

  // Fuel: the language's built-in termination bound. Capped server-side so a
  // caller cannot ask for an unbounded ceiling. `bang`'s own default is 100000.
  defaultFuel: num("RUN_DEFAULT_FUEL", 100_000),
  maxFuel: num("RUN_MAX_FUEL", 5_000_000),

  // The jail (systemd-run --scope). These are the cgroup resource caps.
  jail: {
    enabled: bool("RUN_JAIL", true), // off only for local dev without user-systemd
    memoryMax: process.env.RUN_JAIL_MEMORY_MAX ?? "256M",
    cpuQuota: process.env.RUN_JAIL_CPU_QUOTA ?? "80%",
    tasksMax: num("RUN_JAIL_TASKS_MAX", 8), // fork-bomb guard
    wallClockSec: num("RUN_JAIL_WALL_SEC", 10), // hard kill backstop past fuel
  },

  // Absolute path to the built binary. The examples gate uses .lake/build/bin/bang.
  bangBin: process.env.RUN_BANG_BIN ?? ".lake/build/bin/bang",
} as const;

export type Config = typeof config;
