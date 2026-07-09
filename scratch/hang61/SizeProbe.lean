/-
  scratch/hang61/SizeProbe.lean — issue #61 diagnosis (diag61 lane, READ-ONLY on production).

  Measures the ELABORATED KERNEL TERM SIZE (constructor count) of the lowered
  `Comp` for minimal N-sibling nested-`let rec` programs (N = 1,2,3), the shape
  the dogfood JSON lane isolated as the hang trigger. If size is geometric in N,
  the root cause is elaboration term-blowup; if linear, the cost is runtime.

  Compiled evaluation via `#guard` (the repo gotcha: `lake env lean` #eval is
  unreliable for FUEL recursion — but term SIZE of an already-lowered `Comp` is a
  pure structural fold, no fuel; still, we gate on a KNOWN-size sanity case first).

  Run: nix develop -c lake env lean scratch/hang61/SizeProbe.lean
-/
import Bang.Frontend.TypeCheck
import Bang.Core.IR

namespace Bang.Hang61
open Bang Bang.TypeCheck

/-! ### term-size fold over the CBPV Val/Comp/Handler AST (Bang.Core.IR) -/

mutual
def sizeV : Val → Nat
  | .vunit => 1
  | .vint _ => 1
  | .vvar _ => 1
  | .vcap _ _ => 1
  | .vthunk c => 1 + sizeC c
  | .inl v => 1 + sizeV v
  | .inr v => 1 + sizeV v
  | .pair a b => 1 + sizeV a + sizeV b
  | .fold v => 1 + sizeV v
termination_by v => sizeOf v

def sizeC : Comp → Nat
  | .ret v => 1 + sizeV v
  | .letC m n => 1 + sizeC m + sizeC n
  | .force v => 1 + sizeV v
  | .lam m => 1 + sizeC m
  | .app m v => 1 + sizeC m + sizeV v
  | .perform c _ v => 1 + sizeV c + sizeV v
  | .handle h m => 1 + sizeH h + sizeC m
  | .case v a b => 1 + sizeV v + sizeC a + sizeC b
  | .split v n => 1 + sizeV v + sizeC n
  | .unfold v => 1 + sizeV v
  | .binop _ a b => 1 + sizeV a + sizeV b
  | .oom => 1
  | .wrong _ => 1
termination_by c => sizeOf c

def sizeH : Handler → Nat
  | .state _ v => 1 + sizeV v
  | .throws _ => 1
  | .transaction _ vs => 1 + sizeVList vs
  | .custom _ v cls => 1 + sizeV v + sizeClauses cls
termination_by h => sizeOf h

def sizeVList : List Val → Nat
  | [] => 0
  | v :: vs => sizeV v + sizeVList vs
termination_by vs => sizeOf vs

def sizeClauses : List (OpId × Comp) → Nat
  | [] => 0
  | (_, c) :: ps => sizeC c + sizeClauses ps
termination_by ps => sizeOf ps
end

/-- Elaborate a source string to its lowered `Comp` size, or `0` on any elab/type error. -/
def elabSize (src : String) : Nat :=
  match checkAndLower src with
  | .ok c => sizeC c
  | .error _ => 0

/-! ### sanity: a tiny known program has a small, hand-checkable size -/
-- `$(3 + 4)` : force (thunk (binop add (vint 3) (vint 4)))  → small constant
#eval elabSize "3 + 4"
#eval elabSize "let x = 3 in $x"

/-! ### the blowup curve: N = 1, 2, 3 sibling nested Div-declared let recs -/
#eval elabSize (include_str "sib1.bang")
#eval elabSize (include_str "sib2.bang")
#eval elabSize (include_str "sib3.bang")

end Bang.Hang61
