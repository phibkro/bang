/-!
# K2, increment 1: a stack machine CALCULATED from `eval` (arithmetic kernel)

The first stage of the Bahr–Hutton calculation (ADR-0004, ADR-0009): from the
denotational semantics `eval` of the arithmetic kernel, *derive* a compiler and a
stack machine such that `exec ∘ compile ≡ eval`. The machine is the **output** of
the derivation, not hand-designed — `Instr`, `compile`, and `exec` are exactly
what the specification

    exec (compile e c) s  =  exec c (eval e :: s)

forces into existence under induction on `e`. The corollary `exec (compile e []) []
= [eval e]` is the correctness statement, **proven** below (no `sorry`).

This is increment 1: the kernel is `val · add · mul`. Later increments grow `Src`
toward the pinned core (`if` → `let`/`var` → `force`/application → effects), each
extending `Instr`/`compile`/`exec` and re-proving the theorem (ADR-0009). The
harness diff-tests this calculated machine against the operational `eval` oracle
(`Bang.Eval`) on arithmetic programs, closing the loop machine ≡ eval.
-/

namespace Bang.Calc

/-! ## Source: the arithmetic kernel, with its denotational semantics -/

inductive Src where
  | val : Int → Src
  | add : Src → Src → Src
  | mul : Src → Src → Src
deriving Repr, Inhabited

/-- The semantics we calculate *from*. -/
def eval : Src → Int
  | .val n   => n
  | .add x y => eval x + eval y
  | .mul x y => eval x * eval y

/-! ## The machine — derived, not designed

`Instr`/`compile`/`exec` below are the result of the calculation. The derivation
(sketch): posit `exec (compile e c) s = exec c (eval e :: s)` and compute the RHS
by induction on `e`.

* `e = val n`: need `exec (compile (val n) c) s = exec c (n :: s)`. Take
  `compile (val n) c = PUSH n :: c` and define `exec (PUSH n :: c) s = exec c (n :: s)`.
* `e = add x y`: need `… = exec c ((eval x + eval y) :: s)`. Push `eval x` then
  `eval y` (via the IHs) and combine: `compile (add x y) c = compile x (compile y
  (ADD :: c))`, with `exec (ADD :: c) (m :: n :: s) = exec c (n + m :: s)`. `mul`
  is identical with `MUL`/`*`.

So the instruction set falls out as exactly `{PUSH, ADD, MUL}`. -/

inductive Instr where
  | PUSH : Int → Instr
  | ADD : Instr
  | MUL : Instr
deriving Repr, Inhabited

abbrev Code  := List Instr
abbrev Stack := List Int

def compile : Src → Code → Code
  | .val n,   c => Instr.PUSH n :: c
  | .add x y, c => compile x (compile y (Instr.ADD :: c))
  | .mul x y, c => compile x (compile y (Instr.MUL :: c))

-- Structural on the `Code` list (recurse on the tail `c`); the inner match on
-- (instruction, stack) is non-recursive. Stack underflow on a combinator is
-- unreachable for compiled code (the theorem shows the operands are always
-- present), but handled so `exec` is total — a real machine never gets stuck.
def exec : Code → Stack → Stack
  | [],     s => s
  | i :: c, s =>
    match i, s with
    | Instr.PUSH n, s             => exec c (n :: s)
    | Instr.ADD,    (m :: n :: s) => exec c ((n + m) :: s)   -- `::` binds tighter than `+`
    | Instr.MUL,    (m :: n :: s) => exec c ((n * m) :: s)
    | _,            s             => exec c s

/-! ## The calculation is correct (proven) -/

/-- The key lemma the whole calculation is organized around: running compiled code
with continuation `c` over stack `s` is the same as running `c` over `s` with the
value of `e` pushed on top. Induction on `e`, generalizing the continuation and
the stack. -/
theorem exec_compile (e : Src) (c : Code) (s : Stack) :
    exec (compile e c) s = exec c (eval e :: s) := by
  induction e generalizing c s with
  | val n     => rfl
  | add x y ihx ihy => simp [compile, eval, ihx, ihy, exec]
  | mul x y ihx ihy => simp [compile, eval, ihx, ihy, exec]

/-- Correctness of the calculated machine: compiling a closed program and running
it on the empty stack yields exactly the singleton stack `[eval e]`. -/
theorem compile_correct (e : Src) : exec (compile e []) [] = [eval e] := by
  simpa using exec_compile e [] []

end Bang.Calc
