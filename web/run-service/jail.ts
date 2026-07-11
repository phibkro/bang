import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { Config } from "./config.ts";

export type RunResult = {
  stdout: string;
  stderr: string;
  exit: number | null; // null when killed by wall-clock / signal (timed out)
  timedOut: boolean;
  durationMs: number;
};

// `bang run` takes a FILE positional (Main.lean: `run` → resolveEntryFile <arg>),
// NOT stdin — so we materialise the source to a tmpfile and point the binary at it.
// A per-run tmpdir is the only writable surface the process is given.
//
// The jail is a RESOURCE jail, not a data-isolation jail: the language has no FS,
// net, or ambient-IO operation (interactive-tour-design.md §3), so the whole threat
// model is resource exhaustion. systemd-run --user --scope applies the cgroup caps;
// fuel is the language's own termination bound (passed as --fuel, capped in config).
export async function runInJail(
  source: string,
  fuel: number,
  stdinInput: string | undefined,
  cfg: Config,
): Promise<RunResult> {
  const dir = await mkdtemp(join(tmpdir(), "bang-run-"));
  const srcFile = join(dir, "main.bang");
  try {
    await writeFile(srcFile, source, "utf8");

    const bangArgs = [cfg.bangBin, "run", "--fuel", String(fuel), srcFile];

    // systemd-run --scope runs the command in a transient cgroup scope with the
    // resource properties applied, in the FOREGROUND (--scope blocks until exit).
    // The scope INHERITS our stdio (no --pipe — that flag is rejected in --scope
    // mode), so Bun.spawn's own stdin/stdout/stderr pipes reach the child through
    // the inherited fds. RuntimeMaxSec is the wall-clock kill in the cgroup itself.
    const cmd = cfg.jail.enabled
      ? [
          "systemd-run",
          "--user",
          "--scope",
          "--quiet",
          "--collect", // GC the transient unit even if it fails
          `--property=MemoryMax=${cfg.jail.memoryMax}`,
          `--property=CPUQuota=${cfg.jail.cpuQuota}`,
          `--property=TasksMax=${cfg.jail.tasksMax}`,
          `--property=RuntimeMaxSec=${cfg.jail.wallClockSec}`,
          "--",
          ...bangArgs,
        ]
      : bangArgs;

    const started = Date.now();
    // Bun.spawn: stdin from the provided input (Console-sim programs) or /dev/null.
    // No corpus program reads real stdin today (IO is a mock handler), so /dev/null
    // is the default; the field is the forward hook for a host-IO wedge.
    const proc = Bun.spawn(cmd, {
      stdin: stdinInput === undefined ? "ignore" : new TextEncoder().encode(stdinInput),
      stdout: "pipe",
      stderr: "pipe",
      // Belt to the jail's braces: kill the whole process tree if wall-clock is
      // exceeded even when systemd-run's RuntimeMaxSec is unavailable (dev mode).
    });

    // Wall-clock backstop in-process (redundant with RuntimeMaxSec when jailed,
    // the ONLY guard when not). Kill on timeout, then observe.
    let timedOut = false;
    const killer = setTimeout(() => {
      timedOut = true;
      proc.kill(9);
    }, cfg.jail.wallClockSec * 1000 + 1000);

    const [stdout, stderr, exit] = await Promise.all([
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
      proc.exited,
    ]);
    clearTimeout(killer);

    // The jail's RuntimeMaxSec kills the scope with SIGTERM (exit 143); a memory
    // cgroup kill is SIGKILL (137). Both mean "the resource jail stopped it", which
    // for the caller is a timeout-class outcome, not a program result. The in-proc
    // killer (dev mode, jail off) sets `timedOut` directly.
    const jailKilled = exit === 143 || exit === 137;
    return {
      stdout,
      stderr,
      exit: timedOut || jailKilled ? null : exit,
      timedOut: timedOut || jailKilled,
      durationMs: Date.now() - started,
    };
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}
