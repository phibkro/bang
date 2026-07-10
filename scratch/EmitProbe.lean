import Bang.Backend.AbstractMachine

open Bang Bang.CalcVM

-- Probe: the pure arithmetic fragment. Nested binops need let-sequencing in CBPV
-- because binop operands are VALUES, not computations:  let x = 1+2 in x*3.
def prog1 : Comp :=
  .letC (.binop .add (.vint 1) (.vint 2))
        (.binop .mul (.vvar 0) (.vint 3))
def prog0 : Comp := .binop .add (.vint 1) (.vint 2)
def prog2 : Comp :=
  .letC (.ret (.vint 5)) (.binop .add (.vvar 0) (.vint 10))

-- binop constant-folds at COMPILE time. Verify the compiled Code shape exactly.
example : compile prog0 [] = [Instr.RET (.vint 3)] := by rfl
example : compile prog1 [] =
  [Instr.RET (.vint 3), Instr.SUBST (.binop .mul (.vvar 0) (.vint 3))] := by rfl
example : compile prog2 [] =
  [Instr.RET (.vint 5), Instr.SUBST (.binop .add (.vvar 0) (.vint 10))] := by rfl

-- exec results
example : exec 50 0 (compile prog0 []) [] [] = some [.ret (.vint 3)] := by rfl
example : exec 50 0 (compile prog1 []) [] [] = some [.ret (.vint 9)] := by rfl
example : exec 50 0 (compile prog2 []) [] [] = some [.ret (.vint 15)] := by rfl

-- Source.eval oracle agrees
example : Source.eval 50 prog0 = .done (.vint 3) := by rfl
example : Source.eval 50 prog1 = .done (.vint 9) := by rfl
example : Source.eval 50 prog2 = .done (.vint 15) := by rfl
