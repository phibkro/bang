import Bang.Meta.BinaryLR

/-! # DecompFreshStrip — route B′ (task #29 item 1) VERDICT.

`splitAtId_append_boundary` (below, GREEN): with `nid ∉ Q` the split of `Q ++ handleF nid hh :: Ko'`
lands on the appended boundary — the split-location half the STRIP needs, IF a uniqueness/freshness
premise supplies `splitAtId cfg₁.1 nid = none`.

VERDICT on route B′ (uniqueness-as-lemma-hypothesis, per lead ruling): the caller-discharge check
FAILS. The future caller of krelS_splitAtId_decomp is crelK_fund_up's resolved arm, but the LR
(KrelS/CrelK/crelK_fund_up/lr_sound) is FRESHNESS-FREE BY DESIGN — ADR-0058 route-1 DISSOLVED the
CapsBelow/Canonical/run_bump counter machinery (BinaryLR:515). No FreshCfg/UniqueHId is threaded into
the LR, so the caller CANNOT discharge a uniqueness premise without RE-INTRODUCING the dissolved
machinery (a def/statement-shape change, not a free discharge).

And route (A) needs the SAME uniqueness: the resume-result inner stack `cfg₁.1 = Kᵢ ++ reinstall :: Ki'`
has `Kᵢ` UNIVERSALLY quantified (arbitrary captured continuation), so `nid` can appear in it — both the
self-recursive krelS_splitAtId_decomp strip AND the un-append need `nid ∉ cfg₁.1` to locate the
boundary. So item 1 genuinely needs freshness/id-uniqueness re-introduced into the LR — route (B), the
def-shape change → kernel-engineer + operator. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- split of `Q ++ handleF nid hh :: Ko'` lands on the boundary when nid absent from Q.
theorem splitAtId_append_boundary {nid : Nat} {hh : Handler} :
    ∀ (Q Ko' : Stack), Bang.splitAtId Q nid = none →
    Bang.splitAtId (Q ++ Frame.handleF nid hh :: Ko') nid = some (Q, hh, Ko') := by
  intro Q
  induction Q with
  | nil => intro Ko' _; simp [splitAtId]
  | cons fr Q₀ ih =>
      intro Ko' hnone
      cases fr with
      | handleF m hd =>
          simp only [splitAtId] at hnone
          by_cases hmj : m = nid
          · rw [if_pos hmj] at hnone; simp at hnone
          · rw [if_neg hmj] at hnone
            have hi : splitAtId Q₀ nid = none := Option.map_eq_none_iff.mp hnone
            simp only [List.cons_append, splitAtId, if_neg hmj, ih Ko' hi, Option.map_some]
      | letF N =>
          simp only [splitAtId, Option.map_eq_none_iff] at hnone
          simp only [List.cons_append, splitAtId, ih Ko' hnone, Option.map_some]
      | appF w =>
          simp only [splitAtId, Option.map_eq_none_iff] at hnone
          simp only [List.cons_append, splitAtId, ih Ko' hnone, Option.map_some]

end Bang
