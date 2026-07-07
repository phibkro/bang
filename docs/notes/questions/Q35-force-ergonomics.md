---
type: design-question
title: "Force ergonomics: auto-force a thunk-of-function at the call site; reserve visible `$` for meaningful observation"
description: "surface ergonomics; sugar, no kernel change"
status: open
area: surface
ties: ["Q29", "Q33", "ADR-0007", "ADR-0030", "ADR-0073"]
see-also: []
---
**Question**: should a plain function call auto-insert the force — so `concat "ab" "cd"` works, not only
`($concat) "ab" "cd"` — reserving the VISIBLE `$` for observations that are a genuine CHOICE (forcing a
deferred/reactive computation; reading a mutable cell)? Pure surface sugar (elaborate-away, invariant #5).

**Why it matters**: `let rec` binds a function as a thunk-of-function (`concat : U(Str -> Str -> F Str)`,
ADR-0073), so calling it today needs `($concat) args` — force the thunk to the function, then apply. That
EXPOSES CBPV machinery at every call. At a function call the force is MECHANICAL (you always force-to-call,
never a choice), so the visible `$` communicates plumbing, not meaning. bang deliberately exposes `$` (bare
= description, `$` = value, ADR-0007) — its VALUE is marking WHEN you observe a deferred/reactive value; at
a call it's noise.

**The semantics (why `($f) args`, not `$(f args)`)**: `concat` is a THUNK (a value), not a function — CBPV
binds a function as a thunk-value (a name binds a value; a function is a computation). `$` forces the thunk
`concat` to the function, which is then applied. `$(concat args)` does NOT type-check: `concat args`
applies the thunk before forcing (the "callee is not a function" error). The force lands on the thunk, not
the result — faithful, but ergonomically surprising (the user's model is "call concat," not "retrieve, then
call").

**The forks:**
1. **Auto-force at application (recommended)** — elaborate `f a` (f : thunk-of-fn) → `($f) a`. Bare
   `concat "ab" "cd"` works; `($f) a` still works (additive, backward-compatible); bare UNAPPLIED `concat`
   stays the thunk (pass it as a value, e.g. `map concat xs`); `$x` for a thunk-of-VALUE is unchanged (the
   force stays visible where it's a choice). Hides the mechanical force, keeps the meaningful one.
2. **Keep `$` fully explicit** — purist consistency; pays an ergonomic tax exposing a force that's never a
   choice.

**The principle (the real content)**: `$` should be VISIBLE where observing is a DECISION (a deferred /
lazy / reactive value; a MUTABLE-cell read), HIDDEN where mechanical (function application). Syntax then
tracks semantics — `$` marks an observation *choice*, not machinery. Directly the [[Q29 eliminator
syntax]] "syntax serves semantics" move applied to force.

**Mental-model corollaries (from the 2026-07-06 design conversation — preserved; they recur):**
- **Thunk ≈ an IMMUTABLE handle to a COMPUTATION** (≈ a lazy value / closure, NOT a mutable pointer); `$` ≈
  dereference-and-run, PURE (same value each force). You never mutate the pointee — you build NEW
  descriptions (compose thunks); manipulation is functional, not imperative.
- **A MUTABLE function thunk = a state cell holding a thunk** (opt-in mutability, ADR-0030): reassign WHICH
  function (a mutable fn-pointer), not mutate its code (recipes are immutable). Reading the cell is a STATE
  EFFECT, so CALLING it is effectful — `f a : … ! {state}` vs an immutable thunk's `… ! ⊥`. The
  mutable-vs-immutable cost is VISIBLE in the row (correct by construction). This is the dynamic-dispatch /
  hot-swap mechanism.
- **Partial application is FUNCTIONAL**: `($concat) "ab" : Str -> F Str` is a new function-computation
  (nothing mutated); to STORE it as a value you THUNK it (`{($concat) "ab"}`). The thunk is the
  storage/passing form, the computation the callable form. Currying is this repeated — build intermediate
  functions, thunk-and-pass at any stage.

**Recommended**: auto-force at application (fork 1) — cheap surface sugar, on-thesis (sharpens `$`'s
meaning), backward-compatible. Bundle with mutable-cell reads STAYING visibly `$`-marked (where the force
IS a choice).

**Blocked on**: nothing hard — a surface-elaboration change (like the stdlib injection / `paramHole`);
sequence after the current polymorphism/tooling work, a small focused increment.

**Revisit signal**: the `($f)` convention shows up as real friction (the tokenizer already reads
`($tokenize)`-heavy); OR the mutable-function-cell / dynamic-dispatch pattern is taken up (decide the
effectful-call surface then). Ties [[Q29 eliminator syntax]], [[Q33 memory model]] (immutable-handle vs
mutable-cell), ADR-0007 (force), ADR-0030 (opt-in mutability), ADR-0073 (let-rec = thunk-of-fn).
