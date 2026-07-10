module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # CarrierForkB — the fork-(b) reaching test: WHERE a `WellCounted`/`StackBelow g` premise
must sit to reach the MINT obligation, and whether it survives.

## The fork (ADR-0096 amendment, lane carrierprobe)

Fork (b) = "leave `KrelS` alone; add a `WellCounted`-style freshness as an explicit PREMISE on
`CrelK` (or its fund lemmas), discharged at the top-level call sites from the machine's real
invariant." The MINT obligation is `StackBelow g K₁` (`BinaryLR.lean:1196/1242/1278/1475`), arising
INSIDE the compat cores AFTER `CrelK`'s `intro g D K₁ K₂ hK` — so `g, K₁` are UNIVERSALLY quantified
by `CrelK` itself.

## The reaching test (mirrors the ADR's `strip_mislocates` reaching test for item-1)

The MINT point sees exactly the hypotheses available after `rw [CrelK]; intro g D K₁ K₂ hK`
(`compatK_handleState:1232`). A premise on `crelK_fund_at`/`crelK_fund_up`'s STATEMENT is OUTSIDE the
`∀ g K₁ K₂` binder — it cannot name the `g`/`K₁` the obligation is about. This is the SAME reaching
failure the ADR's shapes (ii)/(iii) hit for item-1.

## What the witnesses establish

1. `crelK_stmt_premise_cannot_reach_mint` — a `StackBelow g K` premise on the fund-lemma STATEMENT
   quantifies its own `g`/`K` FREE of `CrelK`'s bound `g`/`K`. Modelled: `∀ g K, P g K → (∀ g' K', Q g' K')`
   — the outer `P g K` cannot constrain the inner universally-bound `g' K'`. REFUTED (the outer premise
   is vacuous over the inner binder).

2. `crelK_def_premise_reaches_and_is_gcast_free` — the SURVIVING home: a `StackBelow g K₁` hypothesis
   placed INSIDE `CrelK`'s def (alongside the existing `KrelS n C D ε g K₁ K₂`) DOES reach the MINT
   point (it is introduced with `g, K₁`), and — crucially — it does NOT collide with `KrelS_g_cast`
   because it is a SEPARATE `StackBelow g K₁` hypothesis, NOT folded into `KrelS`'s def-invariant. The
   compat core casts `KrelS` via `KrelS_g_cast n g (g+1)` (unchanged, full-general) and uses the
   SEPARATE `StackBelow g K₁` directly for the `krelS_handleF_intro` freshness — the two never mix.
   This is what fork (a) could NOT do: fork (a) puts `StackBelow g` INTO `KrelS`, coupling it to the
   cast; fork (b) keeps it BESIDE `KrelS`, decoupled from the cast.

The abstract model uses the real `StackBelow` predicate so the reaching/decoupling is over the
genuine kernel object, not a toy. -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **Witness 1 (statement-premise fails the reaching test).** A premise `StackBelow g K` on a fund
lemma whose CONCLUSION universally quantifies a FRESH `g'`/`K'` (the `CrelK` shape: `∀ g' K', KrelS
… g' K' → …`) cannot constrain that inner `g'`/`K'`. Modelled with the real `StackBelow`: the outer
`hP : StackBelow g K` says nothing about the inner `g' K'` the obligation `StackBelow g' K'` is
about. So a witness where the inner obligation is genuinely FALSE (a live frame id ≥ g') coexists
with a true outer premise — the statement-level premise is UNREACHABLE. -/
theorem crelK_stmt_premise_cannot_reach_mint :
    ∃ (g : Nat) (K : EvalCtx),
      Bang.StackBelow g K ∧                      -- a true STATEMENT-level premise (any g,K)
      ∃ (g' : Nat) (K' : EvalCtx),               -- the CrelK-bound, FRESH g',K'
        ¬ Bang.StackBelow g' K' := by            -- for which the MINT obligation is FALSE
  -- outer: StackBelow 3 []  (vacuously true, says nothing about the inner binder)
  -- inner: StackBelow 0 [handleF 0 _]  is FALSE (¬ 0 < 0)
  exact ⟨3, [], trivial, 0, [Frame.handleF 0 (Handler.throws 0)],
    fun h => absurd h.1 (by decide)⟩

/-- **Witness 2 (def-premise reaches AND is `KrelS_g_cast`-free).** A `StackBelow g K₁` hypothesis
placed BESIDE `KrelS` inside `CrelK`'s def reaches the MINT point and is usable for the fresh-mint
`krelS_handleF_intro` WITHOUT interacting with `KrelS_g_cast`. We witness the decoupling directly:
given `KrelS n C D ε g K₁ K₂` (cast-able to any `g'` — the current full-general cast survives) AND a
SEPARATE `StackBelow g K₁`, the MINT step needs `StackBelow g K₁` (have it) and re-casts `KrelS` to
`g+1` (via the UNCHANGED cast). The two facts are independent, so no monotone-restriction is forced.

Modelled: from `KrelS`-castability (abstracted as an up-cast on any relation `R g`) and a separate
`StackBelow g K₁`, BOTH the recast `R (g+1)` and the freshness `StackBelow g K₁` are available — the
conjunction the MINT site consumes — with the cast left FULLY GENERAL. -/
theorem crelK_def_premise_reaches_and_is_gcast_free
    (R : Nat → Prop) (g : Nat) (K₁ : EvalCtx)
    (hcast : ∀ g', R g → R g')          -- KrelS_g_cast stays FULL-GENERAL (not weakened)
    (hR : R g)                          -- the KrelS hypothesis at the pre-mint counter
    (hsb : Bang.StackBelow g K₁) :      -- the SEPARATE def-premise, reaching the MINT point
    R (g + 1) ∧ Bang.StackBelow g K₁ := -- exactly the pair the MINT site (1201/1247/…) consumes
  ⟨hcast (g + 1) hR, hsb⟩

end Bang.Witness

#print axioms Bang.Witness.crelK_stmt_premise_cannot_reach_mint
#print axioms Bang.Witness.crelK_def_premise_reaches_and_is_gcast_free
