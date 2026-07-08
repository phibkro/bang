import Bang.Backend.AbstractMachine

/-! # U5b-handler — ported de-risk lemmas (current layout, ns Bang.CalcVM). -/

namespace Bang.CalcVM.U5bPort
open Bang (Val Comp Frame Config Result Handler)
open Bang.CalcVM

theorem handle_state_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (s0 : Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) (σ.push g s0) τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.state ℓ0 s0) M)
               = some (.term (.ret v0), g', σ'.tail, τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_txn_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (Θ : List Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.transaction ℓ0 Θ) M)
               = some (.term (.ret v0), g', σ', τ'.tail) := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_throws_normal_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret v0), g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_throws_caught_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised g "raise" w, g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret w), g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, and_self, if_true]

theorem handle_throws_forward_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hne : ¬ (n = g ∧ op = "raise"))
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.raised n op w, g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, if_neg hne]

theorem perform_get_resolves
    (f g : Nat) (σ : SStore) (τ : THeap) (n : Nat) (ℓ : Bang.EffectRow.Label) (v sv : Val)
    (hget : σ.get? n = some sv) :
    evalD (f+1) g σ τ (Comp.perform (Val.vcap n ℓ) "get" v)
      = some (.term (.ret sv), g, σ, τ) := by
  simp only [evalD, if_true, hget]

end Bang.CalcVM.U5bPort
