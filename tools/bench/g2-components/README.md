# G2 component-cost bench (issue #116)

Measures the two numbers the wasm-concurrency survey §G2 left unverified:

1. **Instantiation cost** — is a component instance µs-cheap (green-thread-plausible)
   or ms-coarse (a deployment unit)? Cold + warm, default vs pooling allocator,
   trivial vs stateful component.
2. **Canonical-ABI copy tax** — what does a value cost to cross a typed component
   boundary? Small flat message (`tuple`) + `list<u32>` at 1 / 1k / 100k, against a
   no-cross baseline.

## Run

```
./run.sh
```

Pulls `wasm-tools`, `cargo`, `rustc` via nixpkgs (no repo dev-shell needed). Prints
the pinned tool versions, builds the components from `wat/`, builds the timing driver
once, and prints both result tables. First run cold-builds the `wasmtime` crate
(~1.5 min); re-runs are seconds.

## Layout

```
wat/            component fixtures (SOURCE OF TRUTH; .wasm are generated into .build/)
  trivial       func() -> u32                      — instantiation floor + call floor
  stateful      + memory/table/global             — instantiation with state to set up
  list_sum      func(list<u32>) -> u32 (sums)     — copy + per-element compute
  copyonly      func(list<u32>) -> u32 (len)      — isolates the ABI copy-in
  baseline      func(u32) -> u32 (list internal)  — same sum, NO boundary crossing
  tuple         func(tuple<u32,u32>) -> u32       — small flat message (record proxy)
driver/         Rust timing harness (wasmtime crate); times ONLY the op under test
```

The driver builds the engine + compiles each component once, then times `Instance::new`
(instantiation) or a single component call (copy tax) in a warmed loop — the wasmtime
CLI cannot isolate this from process/JIT startup.

Findings live in `docs/notes/wasm-concurrency-survey.md` §G2-MEASURED (dated,
engine-pinned). Numbers are single-machine, orders-of-magnitude — not benchmarketing.
