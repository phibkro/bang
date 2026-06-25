# 0045 — Pivot to a typed logical relation + static/capability dispatch

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: bang-lang pivots from an UNTYPED-dynamic kernel to a TYPED logical relation + STATIC (capability) handler dispatch. The ADR-0043 resume-through-a-wrap edge is an ARTIFACT of dynamic dispatch, not a fundamental limit: a static-link kernel dissolves it (build-gated). The pivot stays inside graded CBPV (Levy already types the CK machine), is bounded (LR changes only its index set; dispatch is a `perform`-semantics swap, no 6th primitive), build-confirmed to preserve set-rows (no ordered evidence / no rank-2 polymorphism), and demotes dynamic dispatch to a tested shell macro.
- **Amends**: 0043, 0044, 0023, 0024
- **Depends-on**: 0016, 0043, 0044, 0001

## Context

ADR-0043 established — exhaustively, from three angles (the typed-CrelK probe, a literature sweep, a
narrowing probe) — that the resume-through-a-wrap edge is the "verified-final" boundary of `lr_sound`. But
every one of those results was final *for the DYNAMIC-dispatch kernel*. A subsequent exploration
(`docs/notes/dispatch-verification-landscape.md`, `kernel-shell-library.md`, `typed-static-pivot-scope.md` +
two fact-checked deep-research sweeps + three build-gated spikes) reframed the question: **the edge exists
*because* dispatch is dynamic** — `splitAt`'s walk-past-a-non-matching-handler (`Operational.lean:259`) is the
only thing that puts a non-catching handler into a captured continuation, and that walk is exactly what
dynamic search does and static dispatch does not.

## Decision

**Pivot the kernel to typed + static, on two coupled axes:**

1. **Static / capability dispatch.** `up ℓ op v` + `splitAt`-search → `perform cap op v` + `staticSplit`
   (dispatch counts a de-Bruijn capability into the runtime stack; it never tests `handlesOp` to decide
   skipping). The runtime still erases types and dispatches on the **cap marker**, not a type. Dynamic
   dispatch is **demoted to a shell macro** (Effekt-style capability threading: `perform name` elaborates to a
   reader-effect lookup resolving the name → cap by lexical scope), tested vs the kernel oracle.

2. **Typed logical relation.** Re-index the biorthogonal LR from raw untyped stacks to the type structure
   (`Vτ`/`Cτ`/`Tτ`). The Nat-step-indexed + `▷` biorthogonal **substrate is unchanged** — it is exactly what
   the current Lean LR uses; only the index set moves.

## Rationale (build-gated, not argued)

- **The edge dissolves.** `static-dispatch-spike` @ `b1330db` (`[propext, Quot.sound]`, 725 jobs green): at
  cap=0 (nearest handler — the common case) the captured continuation is handler-free ⇒ the edge **dissolves,
  structurally, UNTYPED**. At cap>0 (resume-into-outer) the strip relocates but is **cap-indexed** — the static
  count is the answer-type witness, so it never reintroduces the untyped-LR's missing recovery. The typed LR
  cleanly covers the cap>0 residue.
- **It stays inside graded CBPV.** Levy types the CK machine (thesis §3.3.3 — typed stacks, subject reduction),
  so a typed continuation-relation is native; System F is orthogonal (not entailed); the typed biorthogonal
  handler-LR is published (Biernacki, Matache) on the same Nat-step + `▷` substrate.
- **Bounded cost.** No 6th primitive (`perform cap` REPLACES `up`+`splitAt`-search); calculated-VM impact LOW
  (static dispatch is a *simpler* `splitAt` → Bahr–Hutton re-runs a smaller obligation); `dispatchOn`
  (throws/state/txn) unchanged.
- **Set-rows preserved (the one flagged tension, build-cleared).** `setrow-tension-spike` @ `f92a504`
  (`[propext, Classical.choice, Quot.sound]` / `[propext]`, 725 green): the typed `perform cap` rule's
  effect-row premise is `labelEff ℓ ≤ φ` (identical to `HasCTy.up`); the cap is a **separate `Nat`** absent from
  the row premise; discharge stays the `⊔`-semilattice (idempotent + commutative); well-scopedness is
  **decidable structural recursion** (`CapResolves`), **no rank-2 polymorphism**. The ordering lives on the
  stack (already ordered); the **row stays a `Finset Label`** (invariant #2 untouched). This refutes the
  Koka-evidence-vector / named-handler-polymorphism pressure.
- **Structural safety + product win.** `no_accidental_handling` becomes **structural** at cap=0 (a perform can
  only reach its cap-named handler — the bad state is unrepresentable, not detected). Rich shell types buy the
  static-analysis + error-message wins.

## What this amends

- **ADR-0023 / 0024 (dynamic dispatch + `no_accidental_handling` via lacks-constraints):** the KERNEL dispatch
  becomes static-link; `no_accidental_handling` becomes structural. Dynamic dispatch + the lacks-discipline
  survive in the SHELL (the dynamic-dispatch macro), tested.
- **ADR-0043 (the resume-edge seam):** the seam was an artifact of dynamic dispatch; the pivot **dissolves** it.
  ADR-0043's analysis stands as the proof that the edge is *unclosable under dynamic dispatch* — which is
  precisely why the kernel moves to static.
- **ADR-0044 (dynamic vs lexical):** **resolved** — the kernel is static-link; dynamic dispatch is the derived
  shell default. The "support both" becomes "static kernel + dynamic-as-derived-shell."

## Rejected alternatives

- **Keep dynamic + the tested seam** — the edge stays tested-not-proved forever; rejected now that static
  dissolves it at bounded cost.
- **Typed-`CrelK` reshape on the dynamic kernel** — NO-GO / rabbit-hole (ADR-0043): typing can't recover the
  intermediate answer type while dispatch is dynamic.
- **Pure-lexical (replace, no dynamic surface)** — a different language; rejected (ADR-0044). The shell macro
  keeps the dynamic ergonomics.

## Consequences

- Architecture = the kernel/shell/library layering (`kernel-shell-library.md`): static-link kernel (machine),
  dynamic-dispatch + rich types in the shell (user), ordinary code in the library. The runtime stays
  untyped-at-execution.
- Implementation is **`paths/PATH-typed-static-pivot.md`** — the build sequence (cap/`staticSplit` kernel diff →
  LR re-index `Vτ/Cτ/Tτ` → dynamic-as-shell-macro), each step build-gated.
- Evidence: `static-dispatch-spike@b1330db`, `setrow-tension-spike@f92a504`, the two deep-research sweeps
  (`wf_60f94539-140`, `wf_9cda0b3f-5f2`), and the scope note.
- Open design choice carried into the PATH: cap>0 (resume-into-an-outer-handler) — keep it (typed cap-witness)
  or forbid it (nearest-only caps, total untyped dissolve, an expressivity cut).

## Amendment (2026-06-25) — the de-Bruijn cap is LEXICAL: `handle` is a cap-binder

Implementing the pivot (`paths/PATH-typed-static-pivot.md`, Phase B) surfaced that ADR-0045's
"de-Bruijn capability into the runtime stack" carries an obligation the original decision left
implicit: **a de-Bruijn index must be shifted under its binders.** The capability's binder is
`handle`. The transitional B1 kernel (cap carried but `Comp.shiftFrom`/`substFrom` leaving it
**unshifted**) is therefore **unsound**, not merely unprovable.

**Verified divergence** (run on the real `Source.eval`, static-dispatch branch, 2026-06-25):

```
handle (state 1 5) (let c = {get} in handle (throws 2) ($c))
  cap=0 (as-lowered, unshifted)      → done (other val)   ✗ WRONG — get mis-dispatches to throws(2)
  cap=1 (shifted to skip the throws) → done (vint 5)      ✓ correct
```

An ordinary thunk-bound `get` forced under an unrelated `handle` migrates (via `letC`/β subst into
a position beneath the wrapper); with the cap unshifted, static dispatch sends it to the WRONG
handler. The old dynamic LABEL search skipped the wrong-label `throws` and found the state; static
positional dispatch cannot, unless the cap is shifted as it crosses the `handle`. This is the
standard de-Bruijn capture/shift pattern (Lexa/Effekt lexical capabilities), now build-pinned.

**Decision (refinement, not a new fork):** `Comp.shiftFrom`/`substFrom` SHIFT the `cap` field when
crossing a `handle` wrapper — `handle` is a binder for capabilities exactly as `lam`/`letC` are for
variables. The surface keeps emitting nearest-at-binding-site caps; subst maintains correctness under
migration. (Full lexical cap *computation* for non-trivial scopes remains the shell elaborator's job,
PATH step 4.) Frozen-statement impact: `type_safety` gains a `WellCapped` premise (or a
closed-well-typed ⟹ well-capped lemma); `preservation`/`progress` stand byte-identical (`WellCapped`
folded into `HasConfig`).

**Resolves the carried open choice (cap>0 keep-vs-forbid):** the divergence program needs `get` to
reach PAST `throws` to `state` — a cap>0 dispatch. **KEEP is forced**; forbidding cap>0 (nearest-only)
would make this ordinary program ill-typed. The forbid fallback is off the table for v1.

### Correction (2026-06-25, same day) — the uniform cap-shift is INCOMPLETE: fixes case A, breaks case B

The amendment above (`shiftFrom`/`substFrom` shift the cap under every `handle`) is **necessary but not
sufficient**, and as a standalone mechanism it is UNSOUND. Build-gated reliable A/B (compiled `lake build`
`#guard`, NOT `lake env lean` — see below):

```
progB = let c = {get} in handle (state 1) ($c)      -- well-typed (axiom-clean), an "open cap"
  DYNAMIC kernel:   done   (terminates)
  CAP-SHIFT kernel: STUCK  ← REGRESSION
```

`perform 0` conflates two meanings with identical syntax:
- **case A (closed cap)** — the target handler lexically ENCLOSES the perform's author site; the cap must
  SHIFT under handlers crossed during migration (the B1-wall divergence; the cap-shift fixes it — `capMigrate`).
- **case B (open cap)** — there is NO enclosing handler at the author site; the effect is latent in the
  thunk's TYPE, to be discharged by a handler placed UNDER it later. The cap must NOT shift. The uniform
  shift breaks these (`progB`/`e1`): well-typed, terminate under dynamic, STUCK under the cap-shift.

So `progress`/`type_safety` are genuinely FALSE for the naive-cap-shift kernel (`progB` is the
counterexample). **There is NO `type_safety` hole in the dynamic kernel** (progB terminates there).

**Root incoherence:** the effect-ROW type system is DYNAMIC (label-based, admits late binding — case B),
but static cap dispatch is LEXICAL (cap fixed at author site). The fix is to make the TYPE SYSTEM lexical
too — a `perform` must have its handler in scope at its author site (a handler-context in `HasCTy`), making
case B ILL-TYPED. Then caps are always closed, the uniform shift is sound, and progress holds. This is the
typed-capability discipline (Effekt second-class capabilities) — being de-risked by a bounded spike before
further impl. Expressivity note: this FORBIDS late-bound effects (handler placed under the perform's
definition); confirm no v1 rung needs it.

**Measurement reliability (a hard-won tooling lesson):** `Source.eval` does not reduce under
`lake env lean` (`#eval`/`#guard` give garbage — interpreted can't unfold the recursion); only compiled
`lake build` `#guard`s are reliable. An earlier "no regression" reading came from `lake env lean` and was
WRONG. Gate eval behaviour with compiled `#guard`s only.
