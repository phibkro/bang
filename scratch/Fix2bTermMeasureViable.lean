import Bang.Core.IR
open Bang
open Bang.EffectRow (Label)

/-!
# Fix-2b SURVIVING-DIRECTION viability (krnl2, 2026-07-10, task #16)

After scratch/Fix2bHeightRefute.lean REFUTED the derivation-height Fix-2b (HasCTy is
Prop → large-elim forbids `htC : HasCTy → Nat`), this file BUILD-CONFIRMS the surviving
direction: a well-founded induction indexed on `sizeOf (c : Comp)` — the Type-valued
TERM, not the Prop derivation — where the two recursive calls the custom arm needs are
both strictly decreasing:
  (a) the body call `crelK_fund hM` : `sizeOf M < sizeOf (handle (custom ℓ p cl) M)`.
  (b) the clause-value call `vrelK_fund` on `w` (from `(op, ret w) ∈ cl`) :
      `sizeOf w < sizeOf (handle (custom ℓ p ((op, ret w)::rest)) M)`.
Both close by `simp [*.sizeOf_spec]; omega` (below, EXIT 0).

This does NOT yet build the fundamental theorem — it removes the doubt that the
term-measure route is a dead end too. Remaining design (fresh grind, pending steer):
recast the mutual `vrelK_fund`/`crelK_fund` on a shared `sizeOf`-measure over
`Comp ⊕ Val`, threading each arm's existing recursive call as a sub-term decrease.
The frozen post-block wrappers stay byte-identical.
-/

-- (a) body M is a direct sub-term of the handleCustom scrutinee:
example (ℓ : Label) (p : Val) (clauses : List (OpId × Comp)) (M : Comp) :
    sizeOf M < sizeOf (Comp.handle (Handler.custom ℓ p clauses) M) := by
  simp only [Comp.handle.sizeOf_spec, Handler.custom.sizeOf_spec]
  omega

-- (b) a clause value w, where (op, Comp.ret w) is a MEMBER of clauses:
example (ℓ : Label) (p : Val) (op : OpId) (w : Val) (rest : List (OpId × Comp)) (M : Comp) :
    sizeOf w < sizeOf (Comp.handle (Handler.custom ℓ p ((op, Comp.ret w) :: rest)) M) := by
  simp only [Comp.handle.sizeOf_spec, Handler.custom.sizeOf_spec,
             List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, Comp.ret.sizeOf_spec]
  omega
