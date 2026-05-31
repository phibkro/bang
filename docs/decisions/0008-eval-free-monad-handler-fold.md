# ADR-0008 · The definitional `eval` is a fuel-bounded free-monad interpreter; handlers are a deep fold

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0004 (the VM is *calculated from* this `eval`; this ADR fixes the shape it calculates against), 0001 (effect labels reuse the `Finset` row model), 0006 (capture scoping note), 0007 (`$` force / parens group drive the AST shape)

## Context

K2 calculates a VM from the Lean `eval` (Bahr–Hutton). A calculation needs an
executable `eval` to derive from, so the first artifact is a definitional
interpreter for the pinned core (thunks + `$` force, lambda + application, `let`,
ADTs + match, one-shot algebraic effect handlers with sample `State`/`Throws`).
The load-bearing choice is **how `eval` represents an effect handler's
resumption**, because defunctionalizing that resumption into machine code *is*
what the K2/K3 calculation does. The reference must therefore hold the resumption
in the form the calculation *consumes*, not in a form that pre-empts its output.

## Decision

Write `eval` in the **free-monad / algebraic-effects** style:

```
inductive Comp (α) where
  | pure : α → Comp α
  | op   : Label → OpId → Value → (Value → Comp α) → Comp α   -- effect request + resumption
  | oom  : Comp α                                             -- out-of-fuel sentinel (not a value)

eval   : Nat → Env → Expr → Comp Value      -- TOTAL def, termination_by fuel
handle : Nat → Handler → Comp α → Comp α    -- deep handler = fold over the tree
```

- The resumption is a **Lean function** `Value → Comp α` carried in the `op` node.
- A **handler is a deep fold** (`handle`): on an `op` whose `Label` it owns, it runs
  its clause with `resume := fun v => handle (k v)` (resuming **re-installs** the
  handler); on an `op` it does not own, it **forwards** the node outward so an
  enclosing handler catches it.
- Both `eval` and `handle` are **fuel-bounded total `def`s** (`termination_by fuel`),
  decaying to the explicit `oom` constructor; never `partial def`.
- The `op` node's `Label` **is** `Bang.EffectRow.Label`; a program's effect row is
  the `Finset` of labels it can emit. "All handlers installed ⇒ row empty ⇒ `run`
  succeeds" is the dynamic shadow of ADR-0001's subset/union.
- **Evaluation is call-by-name** (arguments pass as `thunk` descriptions; `$`
  forces to WHNF; no memoization).
- **Sample effects:** `State` (resume exactly once) and `Throws` (resume zero times).

## Rationale

- **Right altitude for a reference (ADR-0004).** The free-monad form is the
  *definitional semantics*; a CESK/defunctionalized machine is *already half a VM*.
  The calculation's job is to turn the function-typed resumption into a reified
  stack — so positing that stack in `eval` would be "hand-design the VM, then
  justify a compiler against it," the CompCert-mode trap ADR-0004 forbids. `eval`
  is the **input** to the calculation; the machine is its **output**.
- **Validated source shape.** Tsuyama et al. 2024 (*An Intrinsically Typed Compiler
  for Algebraic Effect Handlers*) and Geeson's MSc both calculate a handler machine
  *from* a CBPV/free-monad source — the same starting point.
- **Totality buys equational lemmas for K2.** A `partial def` is opaque (no
  defining equations), which would starve the equational reasoning the calculation
  runs on. Fuel + an explicit `oom` keeps `eval` total while staying honest about
  divergence-beyond-fuel (a documented DEFER, not a faked answer).
- **The row invariant stays literal, not parallel** (ADR-0001). Reusing
  `EffectRow.Label` means the interpreter and the verified unifier speak about the
  same effect-set algebra; handler installation is set subtraction.
- **One-shot is what the samples encode.** `State` uses `resume` once, `Throws`
  discards it (zero uses) — both ≤1, genuinely one-shot. Multi-shot is deferred and
  no golden program relies on it.
- **Call-by-name keeps the reference closest to the Bahr–Hutton/CBPV templates**
  and needs no store; sharing/memoization is a deferred optimization (invariant 7).

## Rejected alternatives

| option | why not |
|--------|---------|
| **CESK / defunctionalized continuation stack** as the reference | already half a machine; pre-empts the K2 calculation's output → CompCert mode (ADR-0004) |
| `partial def eval` (host-language recursion, no fuel) | opaque — no defining equations for the calculation; can't reason equationally; hides divergence instead of marking it |
| **shallow** handlers (resume does *not* re-install) | needs explicit re-wrapping at every resume site; deep is the common default and matches "runtimes are handlers" (design doc) |
| **call-by-need** (memoized thunks) | needs a store/heap, complicating the pure-core calculation, for no correctness gain; sharing is a perf concern (invariant 7), deferred |
| a fresh effect-set type for the interpreter | duplicates ADR-0001; two parallel row notions invite drift |

## Consequences

- `Comp` is a **reflexive inductive** (the resumption `Value → Comp α` is a positive
  occurrence — Lean accepts it). Neither `eval` nor `handle` recurses structurally
  across a resumption, so **both** thread fuel.
- **DEFERRED, as explicit `sorry`/TODO with a one-line plan, never faked:**
  multi-shot handlers (require reifying the continuation as data — a frontier item),
  STM (axiomatized machine primitive, *not* a handler — ADR-0003), `:`/`=`
  reactivity (ADR-0005), divergence beyond fuel.
- **Capture (ADR-0006) is not enforced in `eval`.** The core is *post-elaboration*:
  the front end (K4) compiles an explicit capture list into exactly the `Env` a
  closure carries, so the discipline lives *above* `eval`. Using an `Env`-closure
  here neither implements nor contradicts explicit-capture; it is its denotation.
- An `op` escaping all handlers is a loud **`uncaught-effect`** result, not a value.
- The differential harness gains an `eval` oracle op alongside `unify`, same
  newline-delimited JSON protocol.

## Revisit if

- The K2 calculation needs the resumption reified as **data** earlier than expected
  (e.g. multi-shot lands sooner) → introduce a defunctionalized `Comp` *as a
  calculated step*, not by editing the reference. The reference stays free-monad.
- Call-by-name proves wrong for the `:`/`=` reactivity semantics when that lands
  (reactivity may demand sharing/identity) → revisit the strategy then, with an ADR,
  against a real reactive program.
- Fuel-as-`Nat` becomes a proof bottleneck for divergence at K3 (the partiality
  monad / coinduction spot flagged in ADR-0002/0004) → reconsider the divergence
  representation, not the handler encoding.
