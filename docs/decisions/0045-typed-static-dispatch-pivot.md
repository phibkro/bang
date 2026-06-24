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
