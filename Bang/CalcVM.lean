import Bang.Operational

/-!
# CalcVM — the ◊3 graded-CBPV calculated machine (Unit 2: pure core)

The Bahr–Hutton calculation (ADR-0016, ADR-0017; invariant #4) ported ONCE to
the new graded-CBPV `Comp`/`Val` (`Bang.Core`), replacing the K2 `Calc*.lean`
matrix over the old free-monad `Expr`/`Value`.

This file lands the **pure CBPV core** (PATH-calcvm-port Unit 2): the
returner/sequencing spine `ret` · `letC`, plus value lookup against a runtime
environment. Forcing/abstraction/application (`force`/`lam`/`app`), the ADT
eliminators, and deep handlers (`up`/`handle`) extend this in later increments;
the `evalD ≡ Source.eval` agreement (D1-A bridge) and the diff-test battery are
later units too. Nothing here is `sorry`/`axiom`.

## What we calculate FROM (D1-A, environment-flavoured)

`evalD : Env → Comp → Option Val` — a fuel-bounded *denotational* big-step
evaluator over a runtime environment `Env := List Val` (de-Bruijn values,
innermost first), exactly the shape `Bang.Calc.eval` uses, lifted to CBPV. The
environment (rather than substitution) is what lets a FLAT stack machine fall
out: `letC` becomes `BIND`/`UNBIND`, value variables become `LOOKUP`. `Option`
is the partiality monad (Bahr–Hutton *Monadic Compiler Calculation* §3): `none`
= diverges / stuck / out-of-scope.

A value is resolved against the environment by `meaningV` (`vvar i` ↦ the i-th
binding); `ret`/`letC` are the only computations in THIS increment.

## What the calculation forces into existence

Posit, in the partiality monad — *whenever `evalD` converges to `w`*,

    evalD n env M = some w  →  exec (compile M c) env s = exec c env (w :: s)   (★)

and compute the RHS by induction on the fuel `n`. Each constructor forces an
instruction; the instruction set `{RET, BIND, UNBIND}` is the OUTPUT, never
hand-designed (invariant #4). The corollary
`evalD n [] M = some w → exec (compile M []) [] [] = some [w]` is the headline,
**proven** below (no `sorry`).

`-- shape: bahr-hutton monadic-compiler-calculation §3 (partiality monad)`
`-- env/LOOKUP/BIND pattern per Bang.Calc (K2 let/var increment)`
-/

namespace Bang.CalcVM

open Bang (Val Comp Handler)

/-- Runtime environment: bound (closed) values, innermost first. -/
abbrev Env   := List Val
abbrev Stack := List Val

/-! ## Value meaning (the only `Val` cases this increment denotes)

`meaningV env v` resolves a *value* against the environment. In the pure
returner/sequencing core the values flowing through `ret`/`letC` are `vunit`,
`vint`, and `vvar` (a let-bound name); the structured formers (`vthunk`, `inl`,
`pair`, …) come online with their eliminators in later increments, so here they
denote themselves modulo a deep `vvar` resolve. `vvar i` reads the `i`-th
binding; out of range = `none` (open term, the partiality ⊥). -/
def meaningV : Env → Val → Option Val
  | env, .vvar i   => env[i]?
  | _,   .vunit    => some .vunit
  | _,   .vint n   => some (.vint n)
  | _,   v         => some v          -- structured formers: inert in this increment

/-! ## The denotational source `evalD` (pure returner/sequencing core)

Fuel-bounded (`letC` sequences two sub-evals; the language is Turing-complete
once `force` lands, so fuel is structural insurance). `evalD env (ret v)` resolves
`v`; `evalD env (letC M N)` runs `M`, binds its value at index 0, runs `N`. -/
def evalD : Nat → Env → Comp → Option Val
  | 0,          _,   _           => none
  | Nat.succ _, env, .ret v      => meaningV env v
  | Nat.succ f, env, .letC M N   =>
      (evalD f env M).bind (fun w => evalD f (w :: env) N)
  | _,          _,   _           => none      -- out of scope this increment

/-! ## The machine — derived, not designed

Computing the RHS of (★) by induction on `M`:

* `ret v` → resolve `v`, push it. A `vvar` resolves at runtime ⇒ `LOOKUP i`; a
  literal/unit ⇒ `PUSH v`. We keep one `RET` instruction carrying the `Val` and
  let `exec` resolve via `meaningV` (so `compile` stays a pure structural map and
  the runtime env is threaded uniformly).
* `letC M N` → `compile M (BIND :: compile N (UNBIND :: c))`: run `M`, `BIND` its
  result into the env, run `N`, `UNBIND` to restore the env for `c`. This is the
  CBPV sequencing analogue of `Bang.Calc`'s `letE` (BIND/UNBIND fall out).

So the instruction set is `{RET, BIND, UNBIND}` for this increment; `LOOKUP`/`PUSH`
are the two runtime behaviours of `RET` (resolve-or-literal), kept fused for now. -/

inductive Instr where
  | RET    : Val → Instr      -- resolve the value against env, push it
  | BIND   : Instr            -- pop top, push it onto the env
  | UNBIND : Instr            -- drop the innermost env binding
  deriving Inhabited

abbrev Code := List Instr

def compile : Comp → Code → Code
  | .ret v,    c => Instr.RET v :: c
  | .letC M N, c => compile M (Instr.BIND :: compile N (Instr.UNBIND :: c))
  | M,         c => Instr.RET (.vthunk M) :: c   -- residual (out of scope) — inert placeholder

/-- The machine. Structural on `code`; the `RET` resolve can fail (`none`) on an
out-of-range `vvar` (open term), so `exec` is `Option`-valued — the partiality
monad threaded through. -/
def exec : Code → Env → Stack → Option Stack
  | [],                  _,   s => some s
  | Instr.RET v :: c,    env, s => (meaningV env v).bind (fun w => exec c env (w :: s))
  | Instr.BIND :: c,     env, s =>
      match s with
      | w :: s' => exec c (w :: env) s'
      | []      => none
  | Instr.UNBIND :: c,   env, s =>
      match env with
      | _ :: env' => exec c env' s
      | []        => none

/-! ## The calculation is correct (proven)

The key lemma (★): running compiled code with continuation `c`, env `env`, stack
`s` equals running `c` over `env`, `s` with the value of `M` pushed — in the
partiality monad. Induction on `M`, generalizing `c`, `env`, `s`. The two live
constructors close by `simp`; the residual default is `vthunk M` which `meaningV`
returns verbatim, and `evalD` on out-of-scope `M` is `none` — so (★) holds
vacuously on that branch only when fuel is `0`, hence we state (★) for the
in-scope fragment via an explicit recursion on the same shape as `evalD`. -/

/-- (★) for the pure returner/sequencing core, indexed by the SAME fuel as
`evalD` so the inductive hypotheses line up (Bahr–Hutton: the calculation mirrors
the evaluator's recursion). Whenever `evalD n M` converges (`= some w`), the
machine reproduces it: running `compile M c` pushes `w` then runs `c`. Stated as
an implication from `evalD n M = some w` (rather than `.isSome`) so the rewrite
chain is purely equational. Induction on the fuel `n`, generalizing everything. -/
theorem exec_compile :
    ∀ (n : Nat) (env : Env) (M : Comp) (w : Val) (c : Code) (s : Stack),
      evalD n env M = some w →
      exec (compile M c) env s = exec c env (w :: s) := by
  intro n
  induction n with
  | zero => intro env M w c s h; simp [evalD] at h
  | succ f ih =>
    intro env M w c s h
    cases M with
    | ret v =>
        -- evalD (ret v) = meaningV env v; compile (ret v) = RET v :: c
        simp only [evalD] at h
        simp only [compile, exec, h, Option.bind_some]
    | letC M N =>
        -- evalD (letC M N) env = (evalD f env M) >>= fun w0 => evalD f (w0::env) N
        simp only [evalD] at h
        rcases hM : evalD f env M with _ | w0
        · rw [hM] at h; simp at h
        · rw [hM] at h; simp only [Option.bind_some] at h
          -- compile (letC M N) c = compile M (BIND :: compile N (UNBIND :: c))
          show exec (compile M (Instr.BIND :: compile N (Instr.UNBIND :: c))) env s
                = exec c env (w :: s)
          rw [ih env M w0 (Instr.BIND :: compile N (Instr.UNBIND :: c)) s hM]
          simp only [exec]
          rw [ih (w0 :: env) N w (Instr.UNBIND :: c) s h]
          simp only [exec]
    | _ =>
        -- residual / out of scope: evalD (succ f) M = none, so the hypothesis is absurd
        simp [evalD] at h

/-- Headline: compiling a closed computation and running it on the empty env and
stack yields exactly `[w]` where `evalD n [] M = some w` (the convergent pure
core). Pure-core ◊3 increment — the `compile_correct` analogue of `Bang.Calc`. -/
theorem compile_correct (n : Nat) (M : Comp) (w : Val) (h : evalD n [] M = some w) :
    exec (compile M []) [] [] = some [w] := by
  rw [exec_compile n [] M w [] [] h]; rfl

/-! ## Diff-test seeds (PATH-calcvm-port Unit 4)

The Lean-side replacement for the deleted TS differential harness: assert
`exec (compile M []) [] [] = (evalD M).map (·::[])` on curated programs, by `rfl`
(decidable, closed). The first grains of the `native_decide` battery the ◊3 gate
will grow. -/

/-- `let x = 1 in x` — `letC (ret 1) (ret (vvar 0))`. Both the evaluator and the
calculated machine produce `1`. -/
example :
    let M := Comp.letC (.ret (.vint 1)) (.ret (.vvar 0))
    evalD 5 [] M = some (.vint 1) ∧ exec (compile M []) [] [] = some [.vint 1] := by
  refine ⟨rfl, rfl⟩

/-- `let x = 7 in let y = x in y` — nested binders, inner reads the outer. -/
example :
    let M := Comp.letC (.ret (.vint 7)) (.letC (.ret (.vvar 0)) (.ret (.vvar 0)))
    evalD 5 [] M = some (.vint 7) ∧ exec (compile M []) [] [] = some [.vint 7] := by
  refine ⟨rfl, rfl⟩

/-- The agreement the battery asserts, witnessed concretely: machine ≡ evaluator
on a let-program returning the OUTER of two bindings (`let a=3 in let b=9 in a`),
exercising `UNBIND` (the continuation sees the restored env). -/
example :
    let M := Comp.letC (.ret (.vint 3)) (.letC (.ret (.vint 9)) (.ret (.vvar 1)))
    exec (compile M []) [] [] = (evalD 5 [] M).map (fun w => [w]) := by
  rfl

end Bang.CalcVM
