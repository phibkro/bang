/-
  scratch/WellScopedReshapeProbe.lean — DE-RISK the wsCfg_step WellScoped reshape (inc5-endgame, task #34).

  The diagonal's last sorry `wsCfg_step` (Bang.Model:185) fails because `WellScoped` collects caps
  SYNTACTICALLY THROUGH thunks (`capsV (.vthunk c) = capsC c`), so the handleF-pop's carry-drop breaks it.
  PROPOSED FIX (lead-endorsed, WellScoped is the PROOF invariant — reshape freely): a SHALLOW surface-caps
  collection that does NOT descend into thunks (a thunk's dormant caps are inert until forced).

  THE KEY LEVER this de-risks (GREEN below): with shallow surface-caps, the POP arm closes via a clean B-occ
  contradiction — a SURFACE `vcap n ℓ` in the returned value `v : A` forces `LabelOccurs ℓ A`, contradicting
  the popping handle's `¬LabelOccurs ℓ A`. So no surface cap of the returned value targets the popped handler;
  every surface cap of the return still resolves in the popped tail. The `vthunk` case is `[]` ⇒ the
  carry-drop DISSOLVES. (`fold`/μ corner needs a `labelOccurs (unrollMu A) → labelOccurs A` lemma — seamed.)
-/
import Bang.Metatheory

namespace Bang.WellScopedReshapeProbe
open Bang
open Bang.EffectRow (Label)

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult]

/-- SHALLOW surface caps — does NOT descend into `vthunk` (the reshape's heart: dormant thunk caps are
inert, re-resolved when forced, so they don't burden the surface invariant). -/
def surfaceCapsV : Val → List (Nat × Label)
  | .vcap n ℓ   => [(n, ℓ)]
  | .inl v      => surfaceCapsV v
  | .inr v      => surfaceCapsV v
  | .pair a b   => surfaceCapsV a ++ surfaceCapsV b
  | .fold v     => surfaceCapsV v
  | .vthunk _   => []          -- SHALLOW — the carry-drop dissolves here
  | _           => []

/-- **THE B-occ LEVER** (de-risked): a SURFACE cap of a well-typed value FORCES `LabelOccurs` of its label
in the value's type. Contrapositive (the pop arm): `¬LabelOccurs ℓ A` ⟹ no surface `vcap _ ℓ` in any
`v : A` ⟹ a value returned past `handleF` (answer `A`, `¬LabelOccurs ℓ A`) carries no surface cap of the
popped label ⟹ every surface cap of the return resolves in the popped tail. Structural recursion on `v`
(equation compiler handles the mutual `Val`; recursion descends only into sub-VALUES). -/
theorem surfaceCaps_labelOccurs : (v : Val) → ∀ {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {A : VTy Eff Mult}, HasVTy γ Γ v A → ∀ p ∈ surfaceCapsV v, LabelOccurs (Eff := Eff) p.2 A
  | .vunit    => fun _ _ hp => by simp [surfaceCapsV] at hp
  | .vint _   => fun _ _ hp => by simp [surfaceCapsV] at hp
  | .vvar _   => fun _ _ hp => by simp [surfaceCapsV] at hp
  | .vthunk _ => fun _ _ hp => by simp [surfaceCapsV] at hp
  | .vcap n ℓ => fun h p hp => by
      cases h; simp only [surfaceCapsV, List.mem_singleton] at hp; subst hp
      simp [LabelOccurs, VTy.labelOccurs]
  | .inl w => fun h p hp => by
      cases h with
      | inl hw => exact Or.inl (surfaceCaps_labelOccurs w hw p (by simpa only [surfaceCapsV] using hp))
  | .inr w => fun h p hp => by
      cases h with
      | inr hw => exact Or.inr (surfaceCaps_labelOccurs w hw p (by simpa only [surfaceCapsV] using hp))
  | .pair a b => fun h p hp => by
      cases h with
      | pair ha hb _ =>
          simp only [surfaceCapsV, List.mem_append] at hp
          rcases hp with hp | hp
          · exact Or.inl (surfaceCaps_labelOccurs a ha p hp)
          · exact Or.inr (surfaceCaps_labelOccurs b hb p hp)
  | .fold w => fun h p hp => by
      cases h with
      | fold hw =>
          have hu := surfaceCaps_labelOccurs w hw p (by simpa only [surfaceCapsV] using hp)
          -- hu : labelOccurs p.2 (unrollMu A); goal labelOccurs p.2 (mu A) = labelOccurs p.2 A.
          -- the μ corner — needs `labelOccurs ℓ (unrollMu A) → labelOccurs ℓ A`. SEAMED (one lemma).
          sorry

/-- **LEG 2 (force re-establishment) — the WALL for a PURE shallow invariant.** `force (vthunk c) → c`.
The pre-step surface caps of `force (vthunk c)` are `surfaceCapsV (Val.vthunk c) = []` (shallow drops them,
below), so a pure-shallow `WellScoped` carries NOTHING about `c`'s caps — yet post-step `surfaceCapsV c`
must resolve in `K`. The pre is STRICTLY weaker than the post ⇒ pure-shallow `WellScoped` is NOT preserved
by force, and `HasConfigTy` alone can't supply the resolution (ADR-0056: typing-is-by-LABEL, dispatch-is-
by-ID). So the two legs are in TENSION: leg 1 (pop) wants SHALLOW (drop thunk caps to dodge carry-drop);
leg 2 (force) wants DEEP (track them so force re-establishes). The reconciling invariant: track caps DEEP
but require resolution only MODULO NON-PERFORMABILITY (a cap at a position whose row excludes its label is
inert by B-occ ⇒ not required to resolve; this is exactly what dodges carry-drop at pop AND covers force).
Its preservation IS the reachability/typing argument = the genuine multi-session `wsCfg_step` content. -/
theorem surfaceCapsV_vthunk (c : Comp) : surfaceCapsV (Val.vthunk c) = [] := rfl

end Bang.WellScopedReshapeProbe
