module

public import Bang.Model

/-! INTERFACE RECORD for the `wsCfg_step` LWSC-preservation half (#44/#46). These axiom-clean
probes lock WHERE cap-resolution enters the assembly and confirm the graded subst `lwscg_subst`
(and its `∀γ'` consumability "PIECE 2") are OFF the critical path:

  • REDUCE live-arg β (`reduce_live_preserves_lwsc`): the live arg's LWSC preservation = PIECE 1
    (`lwsvg_of_typed` at flag `true` ⇒ project `lwsvg_to_lwsv` ⇒ `LWSV K true v`) feeding the
    TYPELESS `lwsc_subst` (§2′.2). The ONE caps-resolve obligation sits HERE (on the substituted
    value `v`); the consumer discharges it from the typing + WScfg's installed handlers (#44 gap).
  • MINT (`mint_preserves_lwsc`): NO caps-resolve obligation — the minted cap resolves under its
    OWN freshly-pushed `handleF g` frame (`splitAtId (handleF g h :: K) g = some ([],h,K)`).
    Inputs are the handle body's LWSC + `StackBelow g K` (freshness, from WellCounted).

So `lwscg_subst` is a valid banked lemma but the consumer never calls it; the live β is typeless,
MINT is self-resolving, PUSH is a frame-restack (no subst), POP is the pop-restack escape. -/

namespace Bang.Model

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult] [NoZeroDivisors Mult] [Nontrivial Mult]

/-- REDUCE appF / letF / MINT live-arg β: a CLOSED, caps-resolving value `v` substituted into
a flag-`true` body `M` preserves `LWSC` at flag `true` — via PIECE 1 + the typeless `lwsc_subst`. -/
theorem reduce_live_preserves_lwsc {K : EvalCtx} {v : Val} {M : Comp} {A : VTy Eff Mult} (k : Nat)
    (hvty : HasVTy (Eff := Eff) (Mult := Mult) [] [] v A)
    (hcaps : ∀ p ∈ capsV v, ResolvesLabel K p.1 p.2)
    (hcl : ∀ j, Val.shiftFrom j v = v)
    (hM : LWSC K true M) :
    LWSC K true (Comp.substFrom k v M) :=
  lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true hvty hcaps)) hcl k hM

end Bang.Model

namespace Bang.Model
variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult] [NoZeroDivisors Mult] [Nontrivial Mult]
open Bang.EffectRow (Label)

/-- MINT (handle h M → handleF g h :: K, subst (vcap g h.label) M): LWSC preservation needs NO
caps-resolve sorry — the minted cap RESOLVES under its OWN freshly-pushed handler frame. Inputs:
the handle body's LWSC (from WScfg) + StackBelow g K (freshness, from WellCounted). -/
theorem mint_preserves_lwsc {g : Nat} {h : Handler} {K : EvalCtx} {M : Comp}
    (hsb : StackBelow g K) (hM : LWSC K true M) :
    LWSC (Frame.handleF g h :: K) true (Comp.subst (Val.vcap g h.label) M) := by
  -- the minted cap is live: it resolves at its own frame
  have hres : ResolvesLabel (Frame.handleF g h :: K) g h.label :=
    ⟨[], h, K, by simp [splitAtId], rfl⟩
  have hcapL : LWSV (Frame.handleF g h :: K) true (Val.vcap g h.label) := .vcap_live hres
  -- restack M under the new frame, then substitute the live cap
  exact lwsc_subst hcapL (fun _ => rfl) 0 (lwsc_restack_handleF g h hsb hM)

end Bang.Model
