/-!
# K2 calculation: a stack machine CALCULATED from `eval`

The Bahr–Hutton calculation (ADR-0004, ADR-0009): from the denotational `eval`,
*derive* a compiler and a stack machine such that `exec ∘ compile ≡ eval`. The
machine is the **output** of the derivation, not hand-designed — `Instr`,
`compile`, and `exec` are exactly what the specification

    exec (compile e c) env s  =  exec c env (eval env e :: s)

forces into existence under induction on `e`. The corollary
`exec (compile e []) [] [] = [eval [] e]` is the correctness statement, **proven**
below (no `sorry`).

Increments (ADR-0009 staging — extrinsic, grown one constructor at a time):
* **1 · arithmetic kernel** — `val · add · mul`, instructions `PUSH/ADD/MUL`.
* **2 · let-bindings + variables** ← *this increment*. de Bruijn indices; the
  machine gains a runtime **environment** and the instructions `LOOKUP/BIND/UNBIND`
  fall out. `eval`/`compile`/`exec` thread the environment; the theorem is re-proven.
* next: `if` (needs a Bool/value story to diff-test against `Bang.Eval`) → `force`
  / application (closures) → effects (swap in the effect monad).

The harness diff-tests this calculated machine (`exec` op) against the operational
`eval` oracle (`Bang.Eval`) on arithmetic + let/var programs, closing the loop
machine ≡ eval. (On the pure, total fragment, `Bang.Eval`'s call-by-name `let` and
this strict `let` denote the same value.)
-/

namespace Bang.Calc

/-! ## Source: arithmetic + let/var, with its denotational semantics -/

/-- de Bruijn-indexed source. `var i` reads the `i`-th enclosing binding (0 =
innermost); `letE e1 e2` evaluates `e1`, binds it at index 0, then evaluates `e2`. -/
inductive Src where
  | val  : Int → Src
  | add  : Src → Src → Src
  | mul  : Src → Src → Src
  | var  : Nat → Src
  | letE : Src → Src → Src
deriving Repr, Inhabited

/-- Runtime environment: bound values, innermost first. -/
abbrev Env   := List Int
abbrev Stack := List Int

/-- The semantics we calculate *from*. Out-of-range `var` defaults to 0 (the core
is post-elaboration / well-scoped; the default keeps `eval` total). -/
def eval : Env → Src → Int
  | _,   .val n     => n
  | env, .add x y   => eval env x + eval env y
  | env, .mul x y   => eval env x * eval env y
  | env, .var i     => env.getD i 0
  | env, .letE e1 e2 => eval (eval env e1 :: env) e2

/-! ## The machine — derived, not designed

Posit `exec (compile e c) env s = exec c env (eval env e :: s)` and compute the
RHS by induction on `e`; each constructor forces an instruction:

* `val n`  → `PUSH n`  : `exec (PUSH n :: c) env s = exec c env (n :: s)`.
* `add/mul`→ `ADD/MUL` : combine the top two stack values.
* `var i`  → `LOOKUP i`: `exec (LOOKUP i :: c) env s = exec c env (env.getD i 0 :: s)`.
* `letE e1 e2` → `compile e1 (BIND :: compile e2 (UNBIND :: c))`, with
  `BIND`   : pop the stack top into the environment, and
  `UNBIND` : drop the innermost binding (restore the env for the continuation).

So the instruction set falls out as `{PUSH, ADD, MUL, LOOKUP, BIND, UNBIND}`. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | MUL    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
deriving Repr, Inhabited

abbrev Code := List Instr

def compile : Src → Code → Code
  | .val n,      c => Instr.PUSH n :: c
  | .add x y,    c => compile x (compile y (Instr.ADD :: c))
  | .mul x y,    c => compile x (compile y (Instr.MUL :: c))
  | .var i,      c => Instr.LOOKUP i :: c
  | .letE e1 e2, c => compile e1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c))

-- Structural on the `Code` list (recurse on the tail `c`); the inner match on
-- (instruction, env, stack) is non-recursive. Stack/env underflow on a combinator
-- is unreachable for compiled code (the theorem shows the operands and bindings
-- are always present), but handled so `exec` is total.
def exec : Code → Env → Stack → Stack
  | [],     _,   s => s
  | i :: c, env, s =>
    match i, env, s with
    | Instr.PUSH n,   e,        s             => exec c e (n :: s)
    | Instr.ADD,      e,        (m :: n :: s) => exec c e ((n + m) :: s)   -- `::` binds tighter than `+`
    | Instr.MUL,      e,        (m :: n :: s) => exec c e ((n * m) :: s)
    | Instr.LOOKUP i, e,        s             => exec c e (e.getD i 0 :: s)
    | Instr.BIND,     e,        (v :: s)      => exec c (v :: e) s
    | Instr.UNBIND,   (_ :: e), s             => exec c e s
    | _,              e,        s             => exec c e s

/-! ## The calculation is correct (proven) -/

/-- The key lemma the whole calculation is organized around: running compiled code
with continuation `c`, environment `env`, stack `s` equals running `c` over `env`
and `s` with the value of `e` pushed on top. Induction on `e`, generalizing the
continuation, the environment, and the stack. -/
theorem exec_compile (e : Src) (c : Code) (env : Env) (s : Stack) :
    exec (compile e c) env s = exec c env (eval env e :: s) := by
  induction e generalizing c env s with
  | val n            => rfl
  | add x y ihx ihy  => simp [compile, eval, exec, ihx, ihy]
  | mul x y ihx ihy  => simp [compile, eval, exec, ihx, ihy]
  | var i            => simp [compile, eval, exec]
  | letE e1 e2 ih1 ih2 => simp [compile, eval, exec, ih1, ih2]

/-- Correctness of the calculated machine: compiling a closed program and running
it on the empty environment and stack yields exactly `[eval [] e]`. -/
theorem compile_correct (e : Src) : exec (compile e []) [] [] = [eval [] e] := by
  simpa using exec_compile e [] [] []

end Bang.Calc
