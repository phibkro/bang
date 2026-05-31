/-!
# K2 increment 4: call-by-name + `$`force — the CBN closure machine

BANG's actual kernel (ADR-0007/0008): bindings hold **descriptions** (thunks);
`$` forces to WHNF; arguments pass unevaluated. This is `CalcHO` with the calling
convention flipped from call-by-value to **call-by-name** — so unlike `CalcHO`,
this machine matches the operational reference `Bang.Eval` *exactly* (which is also
CBN), a strictly stronger cross-check than CBV-on-the-total-fragment.

Reads against `docs/notes/k2-calculation-playbook.md`. Shares `CalcHO`'s design
(ADR-0010): fuel-bounded partial `eval`/`exec`, source-closures and now
**source-thunks** (`vthunk Src Env`) shared between `eval` and the machine, so
correctness stays an equality. Two operators force into existence beyond the
closure set: **`THUNK`** (capture a description) and **`FORCE`** (reduce to WHNF).

Calculation spec (unchanged shape): `exec (compile e c) env s ≃ exec c env
(eval e :: s)`. Forcing points (`$e`, both `binop` operands, the function of an
application) compile to a `FORCE`; binding points (`let`, app argument, `thnk`)
compile to a `THUNK` that captures the current env.
-/

namespace Bang.CalcCBN

/-! ## Source, values, and the call-by-name denotational semantics -/

/-- de Bruijn source: arithmetic + var + λ/app + `let` + explicit `thnk`/`force`. -/
inductive Src where
  | val   : Int → Src
  | add   : Src → Src → Src
  | mul   : Src → Src → Src
  | var   : Nat → Src
  | lam   : Src → Src
  | app   : Src → Src → Src
  | letE  : Src → Src → Src
  | thnk  : Src → Src           -- an explicit description (delay)
  | force : Src → Src           -- `$e` : reduce to WHNF
deriving Repr, Inhabited

/-- WHNF values plus first-class closures and **thunks** (unforced descriptions),
all sharing one `Value` between `eval` and the machine. -/
inductive Value where
  | vint   : Int → Value
  | vclo   : Src → List Value → Value
  | vthunk : Src → List Value → Value
deriving Inhabited

abbrev Env   := List Value
abbrev Stack := List Value

/- Call-by-name semantics, fuel-bounded and partial. Bindings (`let`, the app
argument, `thnk`) hold *descriptions*; `force`, `binop` operands, and the app
function position reduce to WHNF via `forceV`. Structurally recursive on fuel. -/
mutual
def eval : Nat → Env → Src → Option Value
  | 0,   _,   _         => none
  | _+1, _,   .val n    => some (.vint n)
  | _+1, env, .var i    => env[i]?                       -- the binding, unforced
  | _+1, env, .lam b    => some (.vclo b env)
  | _+1, env, .thnk e   => some (.vthunk e env)          -- a description
  | f+1, env, .force e  => (eval f env e).bind (forceV f)
  | f+1, env, .letE e1 e2 => eval f (.vthunk e1 env :: env) e2
  | f+1, env, .app g a  =>
      match (eval f env g).bind (forceV f) with
      | some (.vclo b cenv) => eval f (.vthunk a env :: cenv) b   -- arg passed as a thunk
      | _                   => none
  | f+1, env, .add x y  =>
      match (eval f env x).bind (forceV f), (eval f env y).bind (forceV f) with
      | some (.vint a), some (.vint b) => some (.vint (a + b))
      | _,              _              => none
  | f+1, env, .mul x y  =>
      match (eval f env x).bind (forceV f), (eval f env y).bind (forceV f) with
      | some (.vint a), some (.vint b) => some (.vint (a * b))
      | _,              _              => none
/-- Force a value to weak head normal form (chase the thunk chain). -/
def forceV : Nat → Value → Option Value
  | 0,   _            => none
  | f+1, .vthunk e env => (eval f env e).bind (forceV f)
  | _+1, v            => some v
end

/-! ## The machine — derived, not designed

Beyond `CalcHO`'s `{PUSH,ADD,MUL,LOOKUP,BIND,UNBIND,CLOS,APP}`:
* `thnk e` / binding positions → **`THUNK e`**: push `vthunk e env` (capture env,
  like `CLOS` but a thunk). Mirrors `eval`'s `vthunk`.
* `force e` / strict positions → **`FORCE`**: reduce the stack top to WHNF; on a
  `vthunk body tenv` run `compile body [FORCE]` in `tenv` (chase to WHNF, like the
  nested callee run of `APP`). Mirrors `forceV`.
The convention flip lives in `compile`: app/let/thnk emit `THUNK`; `$`, both
`binop` operands, and the app function emit `FORCE`. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | MUL    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
  | CLOS   : Src → Instr
  | APP    : Instr
  | THUNK  : Src → Instr
  | FORCE  : Instr
deriving Inhabited

abbrev Code := List Instr

def compile : Src → Code → Code
  | .val n,      c => Instr.PUSH n :: c
  | .var i,      c => Instr.LOOKUP i :: c
  | .lam b,      c => Instr.CLOS b :: c
  | .thnk e,     c => Instr.THUNK e :: c
  | .force e,    c => compile e (Instr.FORCE :: c)
  | .letE e1 e2, c => Instr.THUNK e1 :: Instr.BIND :: compile e2 (Instr.UNBIND :: c)
  | .app g a,    c => compile g (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c)
  | .add x y,    c => compile x (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c))
  | .mul x y,    c => compile x (Instr.FORCE :: compile y (Instr.FORCE :: Instr.MUL :: c))

def exec : Nat → Code → Env → Stack → Option Stack
  | 0,   _,       _,        _ => none
  | _+1, [],      _,        s => some s
  | f+1, i :: c,  env,      s =>
    match i, env, s with
    | Instr.PUSH n,    e,        s                  => exec f c e (.vint n :: s)
    | Instr.ADD,       e, (.vint m :: .vint n :: s) => exec f c e ((.vint (n + m)) :: s)
    | Instr.MUL,       e, (.vint m :: .vint n :: s) => exec f c e ((.vint (n * m)) :: s)
    | Instr.LOOKUP i,  e,        s                  =>
        match e[i]? with | some v => exec f c e (v :: s) | none => none
    | Instr.BIND,      e, (v :: s)                  => exec f c (v :: e) s
    | Instr.UNBIND,    (_ :: e), s                  => exec f c e s
    | Instr.CLOS b,    e,        s                  => exec f c e (.vclo b e :: s)
    | Instr.THUNK e',  e,        s                  => exec f c e (.vthunk e' e :: s)
    | Instr.APP,       e, (va :: .vclo b cenv :: s) =>
        match exec f (compile b []) (va :: cenv) [] with
        | some (rv :: _) => exec f c e (rv :: s)
        | _              => none
    | Instr.FORCE,     e, (.vthunk body tenv :: s)  =>
        match exec f (compile body [Instr.FORCE]) tenv [] with
        | some (w :: _) => exec f c e (w :: s)
        | _             => none
    | Instr.FORCE,     e, (v :: s)                  => exec f c e (v :: s)   -- already WHNF
    | _,               _,        _                  => none                  -- stuck

/-! ## Correctness (PROOF PENDING — harness-green, proof is the next step)

The machine is calculated and **differentially tested green** against the `eval`
oracle — and because `Bang.Eval` is *itself* call-by-name, the agreement holds on
every program, laziness included (the standing guarantee, invariant 1).

The Lean equivalence `exec ∘ compile ≡ eval` is shipped as `sorry` with a plan,
exactly as CBV's `CalcHO.compile_correct` first was (then proven). It reuses the
playbook (`docs/notes/k2-calculation-playbook.md`) but needs one extra piece
because `eval`/`forceV` are **mutually recursive**:

1. `exec_succ`/`exec_mono` (fuel monotonicity) — as in `CalcHO`, but two nested
   arms now (`APP` *and* `FORCE` on a `vthunk`).
2. A **mutual** simulation, by induction on the eval fuel, proving together:
   - `eval`-sim: `eval fe env e = some v → ∀ c s F r, exec F c env (v::s) = some r
     → ∃ F', exec F' (compile e c) env s = some r`;
   - `forceV`-sim: `forceV fe v = some w → ∀ env c s F r, exec F c env (w::s) =
     some r → ∃ F', exec F' (Instr.FORCE :: c) env (v::s) = some r`.
   The `force`/`app`/`add` cases of the eval-sim invoke the forceV-sim; the
   `FORCE`-on-`vthunk` step of the forceV-sim invokes the eval-sim on the thunk
   body (shared `vthunk` keeps it an equality). `exec_mono` aligns the sub-fuels.
3. `compile_correct` as the corollary. -/
theorem compile_correct (fe : Nat) (env : Env) (e : Src) (v : Value)
    (h : eval fe env e = some v) : ∃ F, exec F (compile e []) env [] = some [v] := by
  sorry

end Bang.CalcCBN
