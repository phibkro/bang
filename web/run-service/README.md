# run-service — the `/run` playground exec service

The **door-2** workhorse of the interactive tour (`docs/notes/interactive-tour-design.md`):
a tiny HTTP service that takes bang source, runs it in a **resource jail**, and returns
`{stdout, stderr, exit, duration_ms}`. This is what the tour's editor POSTs to when a
reader edits a lesson and hits **Run**.

It is an independent app under `web/` (like `docs/` and `landing/`) — one endpoint,
[bun](https://bun.sh) runtime, no framework.

```
POST /run   {source, fuel?, stdin?}  →  {stdout, stderr, exit, timed_out, duration_ms, fuel}
GET  /health                          →  {ok, jail}
```

## Why the jail is a *resource* jail, not a data-isolation jail

The tour design's headline finding (`interactive-tour-design.md` §3): **v1 bang has no
filesystem, network, or ambient-IO operation** — IO is a *mock handler* (`examples/echo-mock`),
not a syscall. A program *cannot* open a socket or read a file because there is no operation
in the language to do so. And execution is **fuel-bounded by construction**: a non-terminating
program stops at a fuel ceiling, not a hang.

So the entire threat model is **resource exhaustion**. There is no data to isolate the
program from — no Docker-per-run, no seccomp data-egress filter needed at the language level.
The defense is *limits*, and limits are the whole story.

| Threat | Guard | Where |
|---|---|---|
| Infinite loop / non-termination | `--fuel` (built-in bound) **+** cgroup `RuntimeMaxSec` wall-clock kill | `--fuel` (server-capped) + jail |
| CPU exhaustion | cgroup `CPUQuota` | jail |
| Memory blowup (big data values) | cgroup `MemoryMax` (OOM-kill) | jail |
| Fork bomb (via the *process*, not the language) | cgroup `TasksMax` | jail |
| One client starving others | per-IP token bucket + bounded concurrency queue | service edge |
| Oversized upload | body-size cap → **413** | service edge |
| Native-runtime CVE (Lean/libc) | non-root user, read-only rootfs, no-new-privs | **operator's systemd unit** (see Deployment) |

**What is NOT guarded, and why it's fine**: there is no FS/net data-exfil filter, because
there is no FS/net operation to filter. The one genuine native surface — the `bang` binary
being a Lean runtime linked against libc — is contained by the operator's unit hardening
(`ProtectSystem`, `NoNewPrivileges`, a `nobody`-class `User`), *not* by this service's code.
The service assumes it runs *inside* that hardened unit; running it un-hardened as root would
be the operator's error, called out below.

## The jail mechanics

Each run:
1. writes `source` to a fresh per-run tmpdir file (`bang run` takes a **file** positional, not
   stdin — `Main.lean`'s `run` subcommand → `resolveEntryFile <arg>`);
2. invokes the binary under `systemd-run --user --scope` with the cgroup properties applied
   (`MemoryMax`, `CPUQuota`, `TasksMax`, `RuntimeMaxSec`);
3. captures stdout/stderr and the exit code, deletes the tmpdir.

The **exit code is the machine contract** the binary already defines (`Main.lean`):

| exit | meaning |
|---|---|
| 0 | value produced → on `stdout` |
| 1 | parse / type / elaboration error → diagnostic on `stderr` |
| 2 | out of fuel (`--engine=oracle`) |
| 3 | escaped capability (ADR-0063) |
| 4 | stuck (only via `--no-typecheck`) |
| 5 | env engine (the default, ADR-0094) collapsed no-value outcome (out-of-fuel / raise / escape) |
| `null` + `timed_out:true` | the jail's wall-clock/memory kill stopped it — a timeout, not a program result |

The service runs the binary's **default engine** (env, ADR-0094) — the same engine
`tools/check-examples.sh` gates the corpus with — so a lesson's `/run` output is byte-identical
to its gated `expected.txt`.

`stdin`: no v1 corpus program reads real stdin (IO is a mock handler), so the process gets
`/dev/null` stdin by default. The optional `stdin` field is the forward hook for a future
host-IO wedge (a Console-sim lesson) — it feeds the process's stdin when provided.

## Config (env → the operator's unit is the SSoT)

Every limit is env-overridable (`config.ts`); the deployed systemd unit sets them, and the
code just reads. Defaults:

| env | default | what |
|---|---|---|
| `RUN_PORT` | 8787 | listen port |
| `RUN_MAX_BODY_BYTES` | 65536 | source cap → 413 |
| `RUN_MAX_CONCURRENT` | 4 | in-flight jailed runs |
| `RUN_MAX_QUEUE` | 32 | queued-waiting cap → 503 |
| `RUN_RATE_CAPACITY` / `RUN_RATE_REFILL_PER_SEC` | 20 / 1 | per-IP token bucket |
| `RUN_DEFAULT_FUEL` / `RUN_MAX_FUEL` | 100000 / 5000000 | fuel default + server-side ceiling |
| `RUN_JAIL` | 1 | jail on (set 0 only for local dev without user-systemd) |
| `RUN_JAIL_MEMORY_MAX` | 256M | cgroup `MemoryMax` |
| `RUN_JAIL_CPU_QUOTA` | 80% | cgroup `CPUQuota` |
| `RUN_JAIL_TASKS_MAX` | 8 | cgroup `TasksMax` |
| `RUN_JAIL_WALL_SEC` | 10 | cgroup `RuntimeMaxSec` (hard kill past fuel) |
| `RUN_BANG_BIN` | `.lake/build/bin/bang` | absolute path to the built binary in production |

## Run it

```sh
# from the repo root, inside the dev shell (needs the built binary):
lake build bang
# bun is not in the Lean dev shell — get it via nix:
PATH="$(nix build nixpkgs#bun --no-link --print-out-paths)/bin:$PATH" \
  RUN_BANG_BIN="$PWD/.lake/build/bin/bang" \
  bun run web/run-service/server.ts
# → bang /run service on :8787 …

curl -sX POST localhost:8787/run -H 'content-type: application/json' \
  -d '{"source":"atomically (let a = new 100; z = write a (read a - 30) in read a)"}'
# {"stdout":"70\n","stderr":"","exit":0,"timed_out":false,"duration_ms":4,"fuel":100000}
```

## The gate — `tools/test-run-service.sh`

The smoke battery starts the service and asserts: the tour's **10 lessons** each return their
gated `expected.txt` (read straight from `examples/` — cannot drift), a **fuel-bomb** times out
cleanly (no hang), an **oversized body** 413s, a **parse error** returns the diagnostic at
exit 1, and a **burst** past the rate cap 429s. Green = all 17 assertions hold.

```sh
PATH="$(nix build nixpkgs#bun --no-link --print-out-paths)/bin:$PATH" \
  bash tools/test-run-service.sh
```

## Tour frontend hookup contract (the next lane, NOT built here)

The tour editor (`web/docs/` `<Lesson>` component, a future lane) wires to this endpoint:

- **Request**: `POST /run`, `content-type: application/json`, body `{source: string, fuel?: number, stdin?: string}`.
  Send the editor's current buffer as `source`; omit `fuel` to use the server default.
- **Response** (always HTTP 200 when the *program* ran, whatever its exit): render `stdout` in
  the output panel; if `exit !== 0` render `stderr` as the diagnostic (it is already
  plain-English, `Main.lean`'s `#67` messages). `timed_out:true` → show "timed out".
- **Non-200**: `413` (source too big), `429` (rate limited — back off), `503` (server busy —
  retry), `400` (malformed body). These are edge conditions, not program results.
- **Degradation**: when the service is down, fall back to the lesson's committed `expected.txt`
  (door 4, the no-exec floor) — the reader still sees the correct output, just not their edits.

The frontend lane needs: the deployed base URL (operator provides), CORS if the tour is served
from a different origin than this service (add an `access-control-allow-origin` header to
`server.ts` scoped to the docs origin — deferred until the deploy origins are known), and the
`<Lesson>` component's editable buffer + Run button (not this lane's scope).

## Deployment posture (recommend; the operator provisions)

This service is the app; the **hardening is the operator's systemd unit** — that's where the
non-language native surface (§ the table above) is contained. A sketch:

```ini
# /etc/systemd/system/bang-run.service  (or a home-manager module)
[Service]
ExecStart=/usr/bin/bun run /opt/bang/web/run-service/server.ts
Environment=RUN_BANG_BIN=/opt/bang/.lake/build/bin/bang
Environment=RUN_JAIL=1
User=bang-run                 # a nobody-class, non-login user
DynamicUser=yes
NoNewPrivileges=yes
ProtectSystem=strict          # read-only rootfs
ProtectHome=yes
PrivateTmp=yes                # each run's tmpdir is private
# The per-run jail uses `systemd-run --user`, so this service needs a user
# manager (loginctl enable-linger for the run user) OR switch jail.ts to the
# SYSTEM bus (`systemd-run` without --user) if it runs as a system service.
```

**One caveat to flag for the operator**: `jail.ts` uses `systemd-run --user`, which needs a
per-user systemd manager. Under `DynamicUser=yes` there is no lingering user manager, so
production should either (a) run the service under a real `User=` with `loginctl enable-linger`,
or (b) drop `--user` from `jail.ts` and grant the service the delegation to create **system**
transient scopes. Pick one at provision time; the smoke battery exercises the `--user` path.

Container alternative: a minimal image (bun + the `bang` binary + its `.olean`s) with the same
cgroup limits applied by the container runtime instead of `systemd-run`. The no-IO finding means
you do **not** need the network disabled for *safety* (the language can't reach it), only for
tidiness — `--network=none` costs nothing.
