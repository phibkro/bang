# 0036 — LR closed-value carrier: enforced at Krel/Srel quantification, not EnvRel alone

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: LR closed-value carrier enforced at `Krel`/`Srel` quantification (not `EnvRel` alone); unblocks `closeC_subst_comm` + the binder cases.
- **Depends-on**: 0034, 0033, 0025, 0030, 0016

- **Layer:** P (LR / proof-statement, with 0033 / 0034)
- **Status:** Accepted
- **Depends on:** 0034 (env-closed fundamental), 0033 (LR relations row-indexed), 0025 (closed CK focus), 0030 (closed heap cells), 0016

## Context

The env-closed fundamental theorem (ADR-0034) relates an open computation to itself under
`Vrel`-related closing environments (`EnvRel`/`closeC`, `Bang/Meta/LR.lean §5.2b`). The ◊4 resume
point proposed adding a **closedness carrier to `EnvRel`** to discharge `closeC_subst_comm` —
the substitution-descent lemma that unblocks every binder case of the induction.

Proving `closeC_subst_comm` (◊4 U6 Phase 1) showed the `EnvRel`-only carrier is **insufficient**.

## Decision

Enforce closed values — `Val.Closed v := ∀ k, Val.shiftFrom k v = v` — at the **quantification
sites where values enter the relations**: `Krel`'s return-half (`∀ v₁ v₂, Val.Closed v₁ →
Val.Closed v₂ → Vrel … → …`) and `Srel`'s resume-half; PLUS an explicit `Val.Closed` conjunct on
`EnvRel` fillers (maintained by construction under binders in the fundamental induction). **Not
`EnvRel` alone.** Landed `f6d0ce2`.

## Why this model

1. **The binder cases force it.** The `letC` fundamental case extends the environment via
   `EnvRel n (A::Γ) (v₁::δ₁) (v₂::δ₂)`, where the plug-values `v₁ v₂` flow from `Krel`'s return-half
   `∀ v₁ v₂, Vrel n A v₁ v₂ → …`. **`Vrel` is not closed in general** — decisive case: `Vrel n (U φ B)
   v₁ v₂ ⟹ v₁ = vthunk c₁ ∧ Crel n B φ c₁ c₂`, and `Crel` (biorthogonal/behavioural) puts *zero*
   syntactic constraint on `c₁`, so a `vthunk` of an *open* computation is `Vrel`-related. Closedness
   must therefore be enforced where the values are quantified, not merely asserted on the env.
2. **Faithful to the machine.** The CK machine only ever plugs/returns CLOSED values (ADR-0025 closed
   focus, ADR-0030 closed heap cells — the same invariant the heap-cell shift-identity uses).
   Restricting `Krel`/`Srel` to closed values matches what the operational semantics actually feeds in.
3. **`closeC_subst_comm` needs BOTH fillers closed.** The de Bruijn substitution-swap traverses into
   each filler, so the env filler `v` AND the substituted bound value `w` must each be shift-invariant
   to survive the other's renumbering. `w` is itself a returned value (closed), so this is free;
   `crel_ret` correspondingly gained `Val.Closed v₁ v₂` hypotheses, supplied by the closed return-half.

## What it commits to

- `Krel`/`Srel`/`EnvRel` carry `Val.Closed`; `crel_ret` carries `Val.Closed` hypotheses.
- `closeC_subst_comm`, `closeCUnderBinders` (general `d`-binder fold; `closeCUnderBinder = …Binders 1`),
  `closeC_letC/_lam/_case/_split`, `substFrom_swap_closed` all proven **sorry-free** (`f6d0ce2`).
- Ripple absorbed with **no statement smell**: `krel_nil_succ`/`lr_sound_closed`/`crel_force`
  unaffected; ◊2 `no_accidental_handling` stayed 0-axiom; ◊3 CalcVM trusted-three intact (gated on the
  committed tree).

## Rejected alternatives

1. **Closedness on `EnvRel` alone** (the resume-point recipe). Why not: incomplete — the binder cases'
   plug-values come from `Krel`'s ∀-quantifier; without a guard there, they may be open, breaking
   `closeC_subst_comm` at nested binders.
2. **A `Val.Closed` conjunct on every `Vrel` clause.** Why not: larger blast radius (every `Vrel` use)
   and wrong locus — values become open-relevant only where plugged (`Krel`/`Srel`), so guard there.
3. **Carry typing (`HasVTy [] []`) as the closedness witness.** Why not: couples the LR to the typing
   judgment; the semantic `Val.Closed` (shift-invariance) is the minimal fact and reuses the existing
   `Val.substFrom_shiftFrom` cancellation — no new induction.

## Revisit if

- A future `Vrel` clause introduces values that are not closed by plug-time (none in the current
  kernel), OR the CK closed-focus invariant (ADR-0025/0030) is relaxed.

_Surfaced + landed by ◊4 U6 Phase 1 (`f6d0ce2`, 2026-06-23); main-loop design pin confirmed against the
`letC` trace, then proven by the proof-engineer thread._
