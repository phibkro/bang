# Scoping the typed + static-dispatch pivot

> Synthesis of two fact-checked deep-research sweeps (`wf_60f94539-140`, `wf_9cda0b3f-5f2`) + a build-gated
> spike (`static-dispatch-spike` @ `b1330db`). Question: how much change to pivot bang-lang to a **typed
> logical relation + static/capability dispatch**, and is it bounded? **Verdict: BOUNDED, IN-FAMILY, and
> build-confirmed to dissolve the ADR-0043 edge.** This is a scope + recommendation, not yet a committed ADR.

## Verdict in one line

The pivot stays **inside graded CBPV** — it deepens an already-typed calculus, it does not change the calculus
family. The dispatch change is a `perform`-semantics swap with **no new primitive**, and a build-gated spike
shows it **dissolves the resume-edge**. The one real tension (set-rows vs the reference designs' ordered
evidence) is plausibly side-stepped by our capability-as-stack-index design — the thing to verify first.

## Theory placement — CONFIRMED on every axis (high confidence)

- **CBPV is already a typed lambda-family calculus** (value/computation polarity; `U`/`F` shifts) — Levy, Harper.
  Typing the relation *deepens* this; it is not a move "into typed lambda."
- **System F is orthogonal + separable.** Levy develops CBPV simply-typed and only *speculates* polymorphism;
  the inference literature literally calls its calculus "CBPV plus polymorphism" (Chen & Dunfield). The pivot
  does **not** entail System F.
- **Levy already TYPES the CK machine** (thesis §3.3.3): reachable configurations carry types, stacks form a
  category of computation types with subject reduction. So a **typed continuation-stack is native to CBPV** —
  this directly de-risks our untyped→typed LR move (typed stacks already exist in the canon).
- **The runtime still erases types** and dispatches on a **marker/token**, not a type (Xie/Leijen; Lexa; System
  C). "Typing the machine/relation" deepens what the *types* carry, not what the *runtime* consults.

## What actually changes (the concrete delta)

```
COMPONENT            CHANGE                                                          MAGNITUDE
─────────────────────────────────────────────────────────────────────────────────────────────
the logical relation  the INDEX SET: raw untyped stacks → type-stratified Vτ/Cτ/Tτ.  IN-FAMILY.
                      The biorthogonal ⊥⊥-closure + Nat-step-indexing + ▷ modality    Only the index
                      substrate is UNCHANGED — it's exactly what our Lean LR already   moves; the
                      uses (ConvergesC_le n, ▷). Typed biorthogonal handler LRs are    technique stays.
                      published (Biernacki POPL'18, Matache, Biernacki–Polesiuk).

the dispatch          `up ℓ op v` + `splitAt`-search  →  `perform cap op v` +          BOUNDED. A
                      `staticSplit` (count a capability; never test handlesOp to        front-end swap,
                      decide skipping). A try/with binds a fresh marker; perform        NO new primitive.
                      yields to it directly. Runtime dispatches on the marker.

the kernel            perform-cap REPLACES up+splitAt-search. `dispatchOn`              NEUTRAL on #5
                      (throws/state/txn arms) UNCHANGED. `no_accidental_handling`       (no 6th primitive);
                      becomes STRUCTURAL at cap=0.                                      structural win.

the calculated VM     static dispatch is a SIMPLER splitAt → Bahr–Hutton re-runs a      LOW risk.
                      strictly smaller obligation.

frozen statements     untouched (dispatchOn consumers identical).                       NONE.
```

**What does NOT change:** the 5-primitive count, the calculated-VM architecture (ADR-0016), the effect-row
*algebra* (labels stay a set), the metatheoretic substrate (Nat-step + ▷). The pivot is a deepening +
front-end swap, not a rewrite.

## The build-gated feasibility (the spike, recorded in `kernel-shell-library.md` #1)

Static-link dispatch (`Bang/StaticSpike.lean`, `[propext, Quot.sound]`, 725 jobs green):
- **cap=0** (nearest handler — common case): captured continuation is handler-free ⇒ **edge DISSOLVES,
  structurally, UNTYPED.**
- **cap>0** (resume-into-outer): strip relocates but **cap-indexed** — the static count is the answer-type
  witness, so it does NOT reintroduce the untyped-LR's missing recovery.

So the typed pivot is *more than enough*: the untyped form already dissolves the common case; typing cleanly
covers the cap>0 residue.

## The one tension to verify first (medium confidence)

The published static-dispatch reference designs lean on machinery that sits against our invariants:
- **Koka's evidence vectors are ORDERED maps** (`lᵢ ⩽ lᵢ₊₁`); **named-handler well-scopedness uses System-F
  higher-rank polymorphism.** Our invariants are **effect-rows-as-idempotent-SETS** (#2) and a
  **non-polymorphic** 5-primitive kernel. Adopting those designs *wholesale* would pressure both.

**Why our design likely side-steps it:** the spike's capability is a **de-Bruijn count into the runtime
STACK**, not an ordered evidence-vector over the row. A stack is *intrinsically* ordered (it always was); the
effect **row stays a set of labels**. And the de-Bruijn cap gives well-scopedness **positionally**, without
higher-rank polymorphism. So the ordering lives where ordering already lived (the stack), and the row algebra
is untouched. **This is the #1 thing to confirm under the typed relation** before committing — it is the only
place the research flags real friction.

## Honest residue (from the spike)

`cap>0` (resume-into-an-outer-handler) needs **either** nearest-only caps (an expressivity cut — no
resume-into-outer, but then the dissolve is *total* and untyped) **or** the typed cap-witness (the pivot's
intent). A design choice, named so it is not a surprise.

## Recommendation

**The typed+static pivot is GO-worthy.** It is bounded (in-family CBPV deepening + a dispatch front-end swap),
build-confirmed to dissolve the ADR-0043 edge, low-cost on every invariant, and it buys the structural
`no_accidental_handling` + the analysis/error-message wins of a richer type discipline. It reframes ADR-0043's
"verified-final seam" as an *artifact of dynamic dispatch* that the pivot removes.

**Suggested next steps (if committing):**
1. An **ADR** recording the pivot decision (typed LR + static/capability dispatch; the rationale + this scope).
2. A **PATH** with the first build step: the de-Bruijn-cap-vs-set-row check (verify the tension is side-stepped)
   + the `perform cap`/`staticSplit` kernel diff, then the LR re-index (Vτ/Cτ/Tτ) reusing the Nat-step+▷ substrate.
3. Keep the **dynamic-dispatch-as-shell-macro** (Effekt-style capability threading) as the ergonomic default,
   tested vs the kernel oracle — the kernel↓shell derivability test, now passing.

*Sources: Levy CBPV thesis (§3.3.3 typed CK machine); Harper ATPL; Chen–Dunfield Implicit Polarized F; Biernacki
POPL'18; Matache; Effekt/System-C; Koka evidence-passing; Lexa. See `dispatch-verification-landscape.md`,
`kernel-shell-library.md`, ADR-0043, ADR-0044.*
