/-!
# K3: State — a calculated machine that threads a state register

The second effect (after `CalcEff`'s Throws). `get`/`put` resume the computation
exactly once and **in tail position**, so — unlike a general resumable handler —
the machine needs no continuation *reification*: it just continues, threading a
**state register**. This is the Bahr–Hutton *Monadic Compiler Calculation* (2022)
"swap to the State monad" approach.

Because nothing diverges or unwinds, the source `eval` is **total** and the machine
is **structurally recursive (no fuel)** — so correctness is a *direct equality*,
like the first-order `Bang/Calc.lean`. The spec the machine is derived from:

    exec (compile e c) env s st = exec c env (v :: s) st'   where (v, st') = eval st env e

Honest scope: this exercises one-shot *tail* resumption (state threading); explicit
continuation **reification** (non-tail / multi-shot handlers, Tsuyama-style) remains
the deferred frontier. Single state cell; `Int` values; compose with the closure
core and with `CalcEff`'s handler stack later.
-/

namespace Bang.CalcSt

/-! ## Source and its total, state-threading semantics -/

inductive Src where
  | val      : Int → Src
  | add      : Src → Src → Src
  | var      : Nat → Src
  | letE     : Src → Src → Src
  | get      : Src                 -- read the state
  | put      : Src → Src           -- set the state to the value of the arg; returns 0 (unit)
  | runState : Src → Src → Src     -- runState init body: run body with a local state cell = init
deriving Repr, Inhabited

abbrev Env := List Int

/-- Total, structural semantics threading a state register: `eval st env e` returns
`(value, newState)`. `runState` localises the cell (restores the outer state). -/
def eval : Int → Env → Src → Int × Int
  | st, _,   .val n   => (n, st)
  | st, env, .var i   => (env[i]?.getD 0, st)
  | st, env, .add x y =>
      let (a, st1) := eval st env x
      let (b, st2) := eval st1 env y
      (a + b, st2)
  | st, env, .letE e1 e2 =>
      let (v, st1) := eval st env e1
      eval st1 (v :: env) e2
  | st, _,   .get     => (st, st)
  | st, env, .put e   =>
      let (v, _) := eval st env e
      (0, v)                        -- new state := v (the arg's value), result 0
  | st, env, .runState init body =>
      let (i, st1) := eval st env init
      let (v, _)   := eval i env body
      (v, st1)                      -- body's value, outer state restored

/-! ## The machine — derived, not designed

`GET`/`PUT` fall out of `get`/`put`; `ENTER`/`LEAVE` bracket `runState` (save the
outer state, install the initial; restore on exit). All instructions *continue*
(no unwinding) — the register is the implicit resumption. Structural on the code. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
  | GET    : Instr                 -- push the current state
  | PUT    : Instr                 -- pop v, set state := v, push 0
  | ENTER  : Instr                 -- pop i, save the current state on the stack, set state := i
  | LEAVE  : Instr                 -- pop v and the saved state st1, restore state := st1, push v
deriving Inhabited

abbrev Code  := List Instr
abbrev Stack := List Int

def compile : Src → Code → Code
  | .val n,       c => Instr.PUSH n :: c
  | .add x y,     c => compile x (compile y (Instr.ADD :: c))
  | .var i,       c => Instr.LOOKUP i :: c
  | .letE e1 e2,  c => compile e1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c))
  | .get,         c => Instr.GET :: c
  | .put e,       c => compile e (Instr.PUT :: c)
  | .runState i b, c => compile i (Instr.ENTER :: compile b (Instr.LEAVE :: c))

/-- The machine: a value stack + a state register, structurally recursive on the
code. Returns the final (stack, state), or `none` if stuck. -/
def exec : Code → Env → Stack → Int → Option (Stack × Int)
  | [],            _,   s, st => some (s, st)
  | Instr.PUSH n   :: c, env, s,            st => exec c env (n :: s) st
  | Instr.ADD      :: c, env, (b :: a :: s), st => exec c env ((a + b) :: s) st
  | Instr.LOOKUP i :: c, env, s,            st => exec c env ((env[i]?.getD 0) :: s) st
  | Instr.BIND     :: c, env, (v :: s),     st => exec c (v :: env) s st
  | Instr.UNBIND   :: c, env, s,            st => match env with
                                                  | _ :: env' => exec c env' s st
                                                  | []        => none
  | Instr.GET      :: c, env, s,            st => exec c env (st :: s) st
  | Instr.PUT      :: c, env, (v :: s),     _  => exec c env (0 :: s) v
  | Instr.ENTER    :: c, env, (i :: s),     st => exec c env (st :: s) i
  | Instr.LEAVE    :: c, env, (v :: st1 :: s), _ => exec c env (v :: s) st1
  | _ :: _,        _,   _,                  _  => none   -- stuck

/-- Run a closed program: empty env/stack, initial state 0. -/
def run (e : Src) : Option (Stack × Int) := exec (compile e []) [] [] 0

/-! ## The calculation is correct (proven) -/

/-- The calculation's key equality: running compiled `e` then `c` from state `st`
equals running `c` from the resulting state with `e`'s value pushed. No fuel — a
direct structural induction on `e`, threading the state register. -/
theorem exec_compile (e : Src) : ∀ (st : Int) (env : Env) (c : Code) (s : Stack),
    exec (compile e c) env s st = exec c env ((eval st env e).1 :: s) (eval st env e).2 := by
  induction e with
  | val n => intro st env c s; rfl
  | var i => intro st env c s; rfl
  | get => intro st env c s; rfl
  | add x y ihx ihy =>
    intro st env c s
    cases hx : eval st env x with
    | mk a st1 => cases hy : eval st1 env y with
      | mk b st2 => simp only [compile, eval, ihx, ihy, hx, hy, exec]
  | letE e1 e2 ih1 ih2 =>
    intro st env c s
    cases h1 : eval st env e1 with
    | mk v st1 => simp only [compile, eval, ih1, ih2, h1, exec]
  | put e ih =>
    intro st env c s
    cases he : eval st env e with
    | mk v st1 => simp only [compile, eval, ih, he, exec]
  | runState i b ihi ihb =>
    intro st env c s
    cases hi : eval st env i with
    | mk vi st1 => cases hb : eval vi env b with
      | mk vb st2 => simp only [compile, eval, ihi, ihb, hi, hb, exec]

/-- **Correctness of the calculated State machine.** Running the compiled program
on the empty stack and initial state `0` halts on `[v]` with the final state,
where `(v, st') = eval 0 [] e`. No `sorry`. -/
theorem compile_correct (e : Src) :
    run e = some ([(eval 0 [] e).1], (eval 0 [] e).2) := by
  simp only [run, exec_compile, exec]

end Bang.CalcSt
