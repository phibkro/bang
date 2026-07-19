# ADR-0119 · Represent emitted capability liveness as an exact GC-linked stack

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Replace the emitted scalar `id < $liveTop` approximation with a private GC-linked stack of live handler identities. Keep the `$capMint`, `$capExit`, and `$capGate` signatures frozen: mint pushes, gate searches for exact membership, and exit pops through its named frame (the frame and every newer node), because Wasm exception/transaction unwinding can skip inner normal exits. Missing exit ids and absent gate ids trap. This closes stale-state-reentry at the concrete helper boundary without claiming handler, compiler, or Wasm-semantic adequacy.
- **Refines**: 0055 (global-fresh identity), 0063 (escaped capability is fail-loud)
- **Depends-on**: 0055, 0063, 0110
- **See-also**: issue #133, issue #134

- **Date**: 2026-07-19
- **Deciders**: operator
- **Layer**: compiler / concrete WasmGC runtime representation

## Context

The concrete WasmGC emitter stamps each state, transaction, or custom capability with the
global-fresh handler id from ADR-0055 and calls a fixed helper ABI:

```wat
(func $capMint (result i64))
(func $capExit (param $m i64))
(func $capGate (param $id i64))
```

The original implementation retained only a scalar high-water mark. It rejected immediate escape,
but `stale-state-reentry.bang` refuted its equivalence to kernel stack membership: cap 0 exits, cap 1
mints, and `0 < liveTop = 2` silently revives cap 0. Env/oracle/compiled classify the program as the
defined escape terminal; the old emitted module printed `7`.

Exit behavior also cannot assume strict bracketing at helper-call sites. A `throw_ref` or transaction
abort can unwind past an inner handler's normal `$capExit`. When a surviving enclosing handler later
exits, the old scalar restore discarded all of those inner lifetimes. An exact replacement must retain
that cleanup behavior rather than trap merely because a skipped inner node is on top.

## Decision

Use a private GC-linked stack rooted at mutable global `$liveCaps`:

```wat
(type $capframe (struct
  (field $id i64)
  (field $prev (ref null $capframe))))
(global $liveCaps (mut (ref null $capframe)) (ref.null $capframe))
```

The helper signatures remain unchanged.

- `$capMint` obtains and increments `$nextId`, allocates a node `(id, $liveCaps)`, installs it as the
  new root, and returns the id.
- `$capGate(id)` linearly searches the linked stack. It returns exactly when `id` is present and
  executes `unreachable` when it reaches null.
- `$capExit(m)` linearly searches from the root. On finding `m`, it assigns `$liveCaps := m.prev`.
  This pops **through** `m`: `m` and all newer nodes are discarded. If `m` is absent, it executes
  `unreachable`.

Pop-through is load-bearing. In the trace `[inner, middle, outer]`, where inner's normal exit was
skipped, `$capExit(middle)` must leave `[outer]`. Strict-pop would reject a valid unwind, while removing
only the named node would preserve a stale inner lifetime.

This decision changes only the concrete helper representation. Capability ids and boxes keep their
existing layouts, handler lowering is not widened, and computed-update support remains out of scope.

## Considered alternatives

- **Scalar high-water mark** — rejected by the stale-reentry witness; freshness/order does not encode
  current membership after pop and later mint.
- **Strict exact stack pop** — rejected because real emitted control flow may skip an inner exit during
  exception/transaction unwinding.
- **Per-capability mutable live bit** — exact for gate, but adds mutable metadata and aliasing to every
  capability representation and still requires unwind cleanup for every skipped inner frame.
- **Dense table or bitset indexed by id** — exact under additional allocation/bounds machinery, but
  global-fresh ids are unbounded at this boundary and the representation adds more runtime policy than
  the linked live stack requires.

## Consequences

- Stale ids cannot revive merely because a later handler mints a larger id.
- Valid outer capabilities remain usable after a nested handler exits.
- Enclosing exits clean skipped inner nodes without adding cleanup calls to every throw path.
- Mint allocates one GC node; gate and exit cost linear time in current handler depth. No performance
  claim is made. Revisit only with measured handler-depth pressure and an exact alternative.
- The calculated model uses natural-number ids. Concrete signed-i64 counter wrap/duplicate ids remain
  excluded; no theorem or test here claims behavior after counter overflow.
- Throws capabilities still dispatch through a static per-site exception tag rather than `$capGate`.
  Ordinary post-exit use traps, but same-site re-entry may reactivate that tag and catch a stale
  throws capability. `stale-throws-reentry` is a named successor/candidate sixth escape witness; this
  decision closes exact membership only for the state, transaction, and custom caps that call the gate.
- The Lean model uses `List Nat` and executable `popThrough`; its theorems are axiom-clean at this
  helper level. They do not interpret WAT, official Wasm semantics, `Comp`, handler lowering, or the
  whole compiler.

## Confirmation

- `Bang.Backend.WgcCapCode.exact_exit_pops_through_skipped_inner` fixes the skipped-inner trace.
- `runExactGate_eq_live_membership` fixes the calculated gate to exact list membership, while the
  retained scalar theorem remains a counterexample to the superseded representation.
- `tools/emit-escape-diff.sh` requires all five escape witnesses, including stale reentry, to fail
  loud in Wasmtime with zero XFAILs.
- The same gate first runs legal nested state and requires oracle = Wasmtime = `105`; missing or broken
  Wasmtime therefore cannot make an all-negative run green.
- The rung-5 effects corpus remains the broader zero-false-fire differential outside the proved helper
  fragment.

ADR-0110's boundary remains binding: these checks do not constitute concrete-emitter adequacy or an
official WebAssembly semantic proof.
