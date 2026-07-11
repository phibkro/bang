# WASI-0.3 async spike (Q(conc-3) / G8 — the ADR-0101 backend gate)

The one leg the G2 bench (`../g2-components`) explicitly did NOT cover: does the
**WASI-0.3 async ABI** (`async func` / `stream<T>` / `future<T>`, the task/subtask
canon builtins) build+run on today's toolchain, and does its shape fit bang's
scheduler-as-handler model (ADR-0101 §G8)?

Verdict (see `docs/notes/wasm-concurrency-survey.md` §G8-SPIKE): **GO.** The ABI is
shipped and runnable on wasmtime 45 / wasm-tools 1.249; the per-async-call tax is
~0.7 µs (payload-orthogonal); the host-owned cooperative event loop is
scheduler-as-handler at the platform level with a clean grade→lift-mode lowering.

## Run

```
./run.sh
```

Pulls `wasm-tools`, `wasmtime`, `cargo`, `rustc` via nixpkgs (no repo dev-shell
needed). Prints pinned tool versions, then:

1. **Q1a** — round-trips `async func`/`stream<u8>`/`future<u32>` through `wasm-tools`.
2. **Q1b** — builds + validates a sync and an async-lifted component.
3. **Q1c** — **RUNS** the async component on wasmtime 45 (returns 42) — the real
   host event loop, `canon lift … async (callback …)` + `task.return`.
4. Enumerates the async canon builtins wasm-tools 1.249 implements.
5. **Q2** — builds the timing driver once, measures sync vs async µs/call (3 repeats).

First run cold-builds the `wasmtime` crate v45 (~2 min); re-runs are seconds.

## Layout

```
wat/
  sync_ret.wat    func() -> u32                     — the sync lift floor
  async_ret.wat   async func() -> u32 (task.return) — the async lift, completes immediately
fixtures/
  async.wit           interface with `next: async func() -> u32`  (WIT round-trip proof)
  stream_future.wit   interface with stream<u8> / future<u32>     (WIT round-trip proof)
driver/           the wasmtime-crate-45 timing driver (call-sync / call-async)
.build/           generated (.wasm + cargo target) — gitignored
```

## What was NOT covered (honest bounds)

- The async export **completes immediately** — a *suspending* task (real
  `waitable-set.wait` + host wakeup) adds a suspend/resume round-trip not in the
  ~0.7 µs figure.
- **`stream<T>` throughput was NOT measured** — the type round-trips and the
  `stream.read/write` builtins exist, but a real stream *producer* needs a guest
  with `wasm32-wasip3` std, which nixpkgs `rustc` does not prebuild (the named
  blocker — re-check when nixpkgs ships a wasip3 rust-std).
- The guest is hand-written WAT, not a bang-compiled component (bang has no
  concurrency backend yet; this de-risks building one).
