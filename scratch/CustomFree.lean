import Bang.Backend.AbstractMachine

/-! # `CustomFree` — no `Handler.custom` node anywhere in a term (the amended-premise predicate).
Weaker than `Comp.Pure`: allows perform/handle(state/throws/txn), forbids only custom. Mutual with a
Val version (thunks carry Comps). Threaded through `evalD_complete_gen_full` to discharge the ONLY
non-closing arm (custom). subst-preservation (`CustomFree` survives `Comp.subst`) is the key lemma. -/

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

end Bang.CustomFree
