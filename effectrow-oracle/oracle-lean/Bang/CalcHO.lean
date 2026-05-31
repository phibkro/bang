/-!
# K2 increment 3: closures — a higher-order CBV machine calculated from `eval`

The frontier increment (ADR-0009 staging; design choices recorded in **ADR-0010**):
add `λ`/application to the calculated machine. Two things change versus the
first-order `Bang/Calc.lean`:

* **Values are no longer just `Int`.** A value is a machine integer or a
  **closure** capturing a source body + the environment it was defined in
  (`vclo : Src → Env`). The *same* `Value` type is shared by `eval` and the
  machine, so correctness can stay an *equality* (no cross-representation
  relation): the machine closure and the denotational closure are literally the
  same object.
* **`eval` and `exec` are fuel-bounded and partial** (`Option`). Untyped `λ`
  diverges (`(λx.x x)(λx.x x)`), so neither can be a plain total function — we use
  fuel exactly as the operational reference `Bang.Eval` does (ADR-0008), instead
  of Lean coinduction. Calling convention is **call-by-value** (eager args); on
  the pure, *total* fragment CBV and `Bang.Eval`'s call-by-name agree, so the
  harness diff-test against the `eval` oracle is sound. Thunk/force + CBN are a
  later increment.

The instruction set still *falls out* of the spec
  `exec (compile e c) env s ≃ exec c env (eval e :: s)`
— `CLOS` (capture a closure) and `APP` (apply) are what the `lam`/`app` cases of
that equation force into existence (derivation sketch at each `compile` clause).

**Proof status (honest):** the machine is calculated and **differentially tested
green** against `eval` (the standing guarantee, invariant 1). The Lean equivalence
`compile_correct` is a fuel-indexed simulation; it is shipped here as `sorry` with
a concrete proof plan (below), exactly as `unify_sound` ships in `EffectRow.lean`.
This is the next proof to land — it is *not* claimed as proven.
-/

namespace Bang.CalcHO

/-! ## Source and values -/

/-- de Bruijn-indexed source: arithmetic + let/var (as in `Calc`) + `lam`/`app`. -/
inductive Src where
  | val  : Int → Src
  | add  : Src → Src → Src
  | mul  : Src → Src → Src
  | var  : Nat → Src
  | letE : Src → Src → Src
  | lam  : Src → Src           -- λ. body   (the parameter is de Bruijn index 0 in body)
  | app  : Src → Src → Src
deriving Repr, Inhabited

/-- A runtime value: a machine integer or a closure (body + captured env). Shared
between `eval` and the machine. `Value`/`Env` are nested through `List`. -/
inductive Value where
  | vint : Int → Value
  | vclo : Src → List Value → Value
deriving Inhabited

abbrev Env   := List Value
abbrev Stack := List Value

/-! ## Denotational semantics (fuel-bounded, call-by-value, partial) -/

/-- `eval fuel env e` evaluates `e` to a value, or `none` on out-of-fuel / stuck
(type error / unbound). Call-by-value: `app` evaluates the argument before the
call. Total in Lean by structural recursion on `fuel`. -/
def eval : Nat → Env → Src → Option Value
  | 0,    _,   _          => none
  | _+1,  _,   .val n     => some (.vint n)
  | f+1,  env, .add x y   =>
      match eval f env x, eval f env y with
      | some (.vint a), some (.vint b) => some (.vint (a + b))
      | _,              _              => none
  | f+1,  env, .mul x y   =>
      match eval f env x, eval f env y with
      | some (.vint a), some (.vint b) => some (.vint (a * b))
      | _,              _              => none
  | _+1,  env, .var i     => env[i]?
  | f+1,  env, .letE e1 e2 =>
      match eval f env e1 with
      | some v => eval f (v :: env) e2
      | none   => none
  | _+1,  env, .lam body  => some (.vclo body env)
  | f+1,  env, .app g a   =>
      match eval f env g, eval f env a with
      | some (.vclo body cenv), some va => eval f (va :: cenv) body
      | _,                      _       => none
termination_by fuel => fuel

/-! ## The machine — derived, not designed

`CLOS`/`APP` fall out of the `lam`/`app` cases of `exec (compile e c) env s ≃
exec c env (eval e :: s)`:

* `lam body` → `CLOS body`: push the closure capturing the current env —
  `exec (CLOS body :: c) env s = exec c env (vclo body env :: s)` mirrors
  `eval (lam body) = vclo body env`.
* `app g a` → `compile g (compile a (APP :: c))`: evaluate the function then the
  argument (CBV, left-to-right), leaving `[va, vclo body cenv, …]` on the stack;
  `APP` runs the body in `va :: cenv` and pushes its result —
  `exec (APP :: c) env (va :: vclo body cenv :: s) = exec c env (eval (va::cenv) body :: s)`. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | MUL    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
  | CLOS   : Src → Instr        -- push a closure capturing the current env
  | APP    : Instr              -- apply a closure to an argument
deriving Inhabited

abbrev Code := List Instr

def compile : Src → Code → Code
  | .val n,      c => Instr.PUSH n :: c
  | .add x y,    c => compile x (compile y (Instr.ADD :: c))
  | .mul x y,    c => compile x (compile y (Instr.MUL :: c))
  | .var i,      c => Instr.LOOKUP i :: c
  | .letE e1 e2, c => compile e1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c))
  | .lam body,   c => Instr.CLOS body :: c
  | .app g a,    c => compile g (compile a (Instr.APP :: c))

/-- The machine. Fuel-bounded and partial (`none` = out-of-fuel or stuck). `APP`
runs the callee's compiled body as a sub-computation in the extended environment
and pushes its single result value — the host-stack call models the dump. -/
def exec : Nat → Code → Env → Stack → Option Stack
  | 0,   _,       _,        _ => none
  | _+1, [],      _,        s => some s
  | f+1, i :: c,  env,      s =>
    match i, env, s with
    | Instr.PUSH n,   e,        s                       => exec f c e (.vint n :: s)
    | Instr.ADD,      e, (.vint m :: .vint n :: s)      => exec f c e (.vint (n + m) :: s)
    | Instr.MUL,      e, (.vint m :: .vint n :: s)      => exec f c e (.vint (n * m) :: s)
    | Instr.LOOKUP i, e,        s                       =>
        match e[i]? with | some v => exec f c e (v :: s) | none => none
    | Instr.BIND,     e, (v :: s)                       => exec f c (v :: e) s
    | Instr.UNBIND,   (_ :: e), s                       => exec f c e s
    | Instr.CLOS body, e,       s                       => exec f c e (.vclo body e :: s)
    | Instr.APP,      e, (va :: .vclo body cenv :: s)   =>
        match exec f (compile body []) (va :: cenv) [] with
        | some (rv :: _) => exec f c e (rv :: s)
        | _              => none
    | _,              _,        _                       => none      -- stuck
termination_by fuel => fuel

/-! ## Correctness — the calculation's theorem (PROOF PENDING)

Goal (the fuel-indexed simulation): if the denotational `eval` terminates with a
value, the compiled machine, given enough fuel, terminates with that value pushed
onto the stack.

    eval fe env e = some v  →  ∃ F, exec F (compile e c) env s = exec F c env (v :: s)

with corollary `exec_run`: `eval fe [] e = some v → ∃ F, exec F (compile e []) [] []
= some [v]`.

Proof plan (the next proof to land):
1. **Fuel monotonicity** for `exec`: `exec f code env s = some r → f ≤ f' → exec f'
   code env s = some r`. By induction on `f`/`code`. (Same for `eval`.)
2. Strengthen to thread the continuation `c` and stack `s`, by induction on the
   `eval` fuel and `e`. First-order cases (`val/add/mul/var/letE`) mirror the
   proven `Calc.exec_compile`, now under `Option`/monotonicity.
3. **`app` / `lam` cases** are where closures bite: `CLOS` matches `eval`'s `lam`
   by definition (shared `vclo`); `APP` needs the IH on the callee body run under
   `va :: cenv` plus fuel monotonicity to reconcile the nested `exec` with the
   `eval` of the body. The shared `Value` representation keeps this an equality,
   not a logical relation.

Until that lands, the standing guarantee is the **harness diff-test** vs the
`eval` oracle (invariant 1). Shipped as `sorry`, not faked (cf. `unify_sound`). -/
theorem compile_correct (fe : Nat) (env : Env) (e : Src) (v : Value)
    (h : eval fe env e = some v) (c : Code) (s : Stack) :
    ∃ F, exec F (compile e c) env s = exec F c env (v :: s) := by
  sorry

end Bang.CalcHO
