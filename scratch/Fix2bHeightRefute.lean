import Bang.Core.Typing
open Bang

/-!
# Fix-2b machine-checked REFUTATION (krnl2, 2026-07-10, task #16)

The `stage5-lr-design.md §RESOLUTION` pin proposes Fix-2b for the `crelK_fund`
handleCustom arm: define height functions `htV/htC/htCl : HasVTy/HasCTy/HasClauses
→ Nat`, then prove height-indexed twins `vrelK_fund_at/crelK_fund_at` by
`induction k`, dodging the structural-recursion checker.

**This file REFUTES that mechanism at the foundation.** `HasVTy`/`HasCTy`/
`HasClauses` are `Prop`-valued (Typing.lean:103/138/344). Any `Nat`-height measure
over them requires eliminating a multi-constructor `Prop` into `Type` — the LARGE
ELIMINATION restriction forbids exactly this. Both routes the pin names are dead:

  (1) hand-rolled `htC : HasCTy → Nat` by recursion  → `propRecLargeElim`
      ("recursor `HasCTy.casesOn` can only eliminate into `Prop`").
  (2) auto-`sizeOf` on the Prop  → the DEGENERATE Prop `SizeOf` instance
      (`sizeOf _ = 0` for every Prop), so `sizeOf hM < sizeOf (handleCustom …)` is
      `0 < 0`, and `decreasing_tactic` fails "failed to prove termination".

The pin's "TRY sizeOf first" hedge assumed sizeOf might carry the derivation
structure; on a Prop it is definitionally trivial. Fix-2b as specified is
UNBUILDABLE — the wall is not the recursion shape, it is `HasCTy : Prop`.

SURVIVING DIRECTION (not attempted here — a fresh design): the well-founded
measure must live on a `Type`-valued object. `Comp`/`Val`/`Handler` ARE `Type`
(IR.lean:113/…), and the clause body + handler body are genuine sub-TERMS of the
scrutinee `Comp.handle (Handler.custom ℓ p clauses) M`. An induction indexed on
`sizeOf (c : Comp)` (the term, not the derivation) can eliminate into `Type` and
is the route to re-examine — modulo whether `sizeOf w < sizeOf c` holds for the
clause value `w` nested in `clauses : List (OpId × Comp)`.
-/

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- REFUTATION (1): a height function must PROJECT the sub-derivations to recurse
    on them (`htC (handleCustom hcl … hM …) = 1 + max (htCl hcl) (htC hM)`). The
    moment the `match` binds a constructor's data field, the elaborator rejects it:
    `recursor HasCTy.casesOn can only eliminate into Prop` (`propRecLargeElim`).
    This file is EXPECTED to ERROR here — it is the machine-checked refutation of
    the pin's step 1, scratch, imported by nothing. -/
def htC {γ Γ c e B} (h : HasCTy (Eff := Eff) (Mult := Mult) γ Γ c e B) : Nat :=
  match h with
  | .handleCustom _ _ _ hM _ _ => 1 + htC hM
  | _ => 1
