import Bang.Backend.AbstractMachine

/-! # `CustomFree` — no `Handler.custom` node anywhere (the amended-premise predicate).
Weaker than `Comp.Pure`: allows perform/handle(state/throws/txn), forbids only custom. Threaded
through `evalD_complete_gen_full` to discharge the ONLY non-closing arm (custom). -/

namespace Bang.CustomFree
open Bang (Val Comp Handler)

mutual
def CFComp : Comp → Prop
  | .ret v            => CFVal v
  | .letC M N         => CFComp M ∧ CFComp N
  | .force v          => CFVal v
  | .lam M            => CFComp M
  | .app M v          => CFComp M ∧ CFVal v
  | .perform c _ v    => CFVal c ∧ CFVal v
  | .handle h M       => CFHandler h ∧ CFComp M
  | .case v N₁ N₂     => CFVal v ∧ CFComp N₁ ∧ CFComp N₂
  | .split v N        => CFVal v ∧ CFComp N
  | .unfold v         => CFVal v
  | .binop _ a b      => CFVal a ∧ CFVal b
  | .oom              => True
  | .wrong _          => True
def CFVal : Val → Prop
  | .vunit | .vint _ | .vvar _ | .vcap _ _ => True
  | .vthunk c         => CFComp c
  | .inl v | .inr v | .fold v => CFVal v
  | .pair a b         => CFVal a ∧ CFVal b
def CFHandler : Handler → Prop
  | .state _ v        => CFVal v
  | .throws _         => True
  | .transaction _ Θ  => ∀ w ∈ Θ, CFVal w
  | .custom _ _ _     => False
end

/-! ### Shift preservation (CFVal/CFComp survive `shiftFrom`). -/
mutual
theorem CFVal_shiftFrom (k : Nat) : ∀ {t : Val}, CFVal t → CFVal (Val.shiftFrom k t)
  | .vunit, _ => by simp [Val.shiftFrom, CFVal]
  | .vint _, _ => by simp [Val.shiftFrom, CFVal]
  | .vcap _ _, _ => by simp [Val.shiftFrom, CFVal]
  | .vvar i, _ => by by_cases hi : i < k <;> simp [Val.shiftFrom, hi, CFVal]
  | .vthunk M, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFComp_shiftFrom k h
  | .inl w, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFVal_shiftFrom k h
  | .inr w, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFVal_shiftFrom k h
  | .pair a b, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .fold w, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFVal_shiftFrom k h
theorem CFHandler_shiftFrom (k : Nat) : ∀ {hd : Handler}, CFHandler hd → CFHandler (Handler.shiftFrom k hd)
  | .state ℓ s, h => by simp only [Handler.shiftFrom, CFHandler] at h ⊢; exact CFVal_shiftFrom k h
  | .throws ℓ, _ => by simp [Handler.shiftFrom, CFHandler]
  | .transaction ℓ Θ, h => by simpa only [Handler.shiftFrom, CFHandler] using h
  | .custom ℓ p cl, h => by simp only [CFHandler] at h
theorem CFComp_shiftFrom (k : Nat) : ∀ {t : Comp}, CFComp t → CFComp (Comp.shiftFrom k t)
  | .ret w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFVal_shiftFrom k h
  | .letC M N, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFComp_shiftFrom k h.1, CFComp_shiftFrom (k+1) h.2⟩
  | .force w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFVal_shiftFrom k h
  | .lam M, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFComp_shiftFrom (k+1) h
  | .app M w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFComp_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .perform c op w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .handle hd M, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFHandler_shiftFrom k h.1, CFComp_shiftFrom (k+1) h.2⟩
  | .case w N₁ N₂, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFComp_shiftFrom (k+1) h.2.1, CFComp_shiftFrom (k+1) h.2.2⟩
  | .split w N, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFComp_shiftFrom (k+2) h.2⟩
  | .unfold w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFVal_shiftFrom k h
  | .binop op a b, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .oom, _ => by simp [Comp.shiftFrom, CFComp]
  | .wrong s, _ => by simp [Comp.shiftFrom, CFComp]
end

/-! ### Subst preservation (filler CFVal). -/
mutual
theorem CFVal_substFrom (k : Nat) {v : Val} (hv : CFVal v) : ∀ {t : Val}, CFVal t → CFVal (Val.substFrom k v t)
  | .vunit, _ => by simp [Val.substFrom, CFVal]
  | .vint _, _ => by simp [Val.substFrom, CFVal]
  | .vcap _ _, _ => by simp [Val.substFrom, CFVal]
  | .vvar i, _ => by
      simp only [Val.substFrom]; by_cases h1 : i = k
      · simp [h1, hv]
      · by_cases h2 : i > k <;> simp [h1, h2, CFVal]
  | .vthunk M, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFComp_substFrom k hv h
  | .inl w, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFVal_substFrom k hv h
  | .inr w, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFVal_substFrom k hv h
  | .pair a b, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .fold w, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFVal_substFrom k hv h
theorem CFHandler_substFrom (k : Nat) {v : Val} (hv : CFVal v) : ∀ {hd : Handler}, CFHandler hd → CFHandler (Handler.substFrom k v hd)
  | .state ℓ s, h => by simp only [Handler.substFrom, CFHandler] at h ⊢; exact CFVal_substFrom k hv h
  | .throws ℓ, _ => by simp [Handler.substFrom, CFHandler]
  | .transaction ℓ Θ, h => by simpa only [Handler.substFrom, CFHandler] using h
  | .custom ℓ p cl, h => by simp only [CFHandler] at h
theorem CFComp_substFrom (k : Nat) {v : Val} (hv : CFVal v) : ∀ {t : Comp}, CFComp t → CFComp (Comp.substFrom k v t)
  | .ret w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFVal_substFrom k hv h
  | .letC M N, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFComp_substFrom k hv h.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2⟩
  | .force w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFVal_substFrom k hv h
  | .lam M, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h
  | .app M w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFComp_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .perform c op w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .handle hd M, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFHandler_substFrom k hv h.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2⟩
  | .case w N₁ N₂, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2.2⟩
  | .split w N, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFComp_substFrom (k+2) (CFVal_shiftFrom 0 (CFVal_shiftFrom 0 hv)) h.2⟩
  | .unfold w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFVal_substFrom k hv h
  | .binop op a b, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .oom, _ => by simp [Comp.substFrom, CFComp]
  | .wrong s, _ => by simp [Comp.substFrom, CFComp]
end

theorem CFComp_subst {v : Val} {N : Comp} (hv : CFVal v) (hN : CFComp N) : CFComp (Comp.subst v N) :=
  CFComp_substFrom 0 hv hN

end Bang.CustomFree
