/-!
# K3 frontier: continuation **reification** — multi-shot / non-tail handlers

The deferred frontier (ADR-0011/0012/0013/0014): a handler whose operation clause
receives the **resumption** as a first-class value and may invoke it **zero, one
(non-tail), or many times**. The five prior effect machines all avoided this —
Throws is zero-shot, State resumes only in tail position. Reification is the step
that *needs* it.

Two facts force the shape of this machine (grounded in Hillerström–Lindley–Atkey,
*Effect handlers via generalised continuations*, and Tsuyama et al. 2024):

1. **Reification = defunctionalization.** A resumption can't be a meta-level
   function value (`vcont : (Value → …) → Value` fails Lean's positivity check) —
   which is *precisely why* the continuation must be made **data**. The reified
   resumption is a `vcont` holding a captured **prefix of the generalised
   continuation**: `(capturedCode, capturedEnv, capturedStack, clause, clauseEnv)`.
2. **It forces the machine flatten** the prior ADRs predicted. The closure
   machines use *nested meta-`exec`* to reduce a subterm; a resumption can't be
   captured across that meta-boundary. So this is a **flat** machine whose
   continuation is explicit `Kont` data — a genuinely different shape, not an
   extension of the others.

The mechanism (deep handlers, single op, minimal calculus — ADR-0015 scope):
* `handle clause body` installs a handler **frame** (the clause + the *return*
  continuation to run when the body finishes). The clause binds the **payload** at
  de Bruijn index 0 and the **resumption** at index 1.
* `perform e` evaluates `e`, then captures the current pure continuation up to the
  handler as a `vcont`, and runs the clause with `(payload, vcont)`.
* `resume k v` **splices** the captured continuation back — re-installing the
  handler around it and arranging the result to flow to the clause's continuation
  (so `resume` is a *call that returns*: the clause may use its result). Calling it
  twice runs the captured continuation twice — multi-shot.

Scope (kept minimal so it is fully provable, ADR-0009/0015): arithmetic + `let` +
one op + `handle`/`resume`, **single handler depth** (a `perform` is handled by the
innermost frame; nested-handler forwarding through pure-return frames is the
documented follow-up). No closures/CBN (composing reification with the closure core
is a separate step).
-/

namespace Bang.CalcReify

/-! ## Instructions, values, frames -/

inductive Instr where
  | PUSH    : Int → Instr
  | ADD     : Instr
  | LOOKUP  : Nat → Instr
  | BIND    : Instr
  | UNBIND  : Instr
  | INSTALL : List Instr → List Instr → Instr   -- install a handler: clause code + outer continuation
  | PERFORM : Instr
  | RESUME  : Instr
deriving Inhabited, Repr

abbrev Code := List Instr

/-- de Bruijn source: arithmetic + `let` + one op (`perform`), `handle clause body`
(clause binds payload@0, resume@1), and `resume k v`. -/
inductive Src where
  | val     : Int → Src
  | add     : Src → Src → Src
  | var     : Nat → Src
  | letE    : Src → Src → Src
  | perform : Src → Src
  | handle  : Src → Src → Src
  | resume  : Src → Src → Src
deriving Repr, Inhabited

/-- WHNF values: ints and **reified resumptions**. A `vcont` is a captured prefix
of the generalised continuation: the pure continuation `(capturedCode, capturedEnv,
capturedStack)` together with the handler `(clause, clauseEnv)` to re-install. -/
inductive Value where
  | vint  : Int → Value
  | vcont : Code → List Value → List Value → Code → List Value → Value
deriving Inhabited, Repr

abbrev Env   := List Value
abbrev Stack := List Value

/-- A continuation frame. `clause = some (code, env)` is a handler frame (its op
clause); `clause = none` is a **pure return** frame. Either way, on a *normal*
value reaching it the value is passed to `(retCode, retEnv, retStack)`. -/
structure Frame where
  clause   : Option (Code × Env)
  retCode  : Code
  retEnv   : Env
  retStack : Stack
deriving Inhabited

abbrev Kont := List Frame

/-! ## The machine — a flat generalised-continuation machine

`exec fuel code env stack K` runs `code`; the *current pure continuation* is
`(code, stack)`, and `K` is the enclosing stack of handler/return frames. On empty
code the value on the stack is returned **through** `K`. -/

def exec : Nat → Code → Env → Stack → Kont → Option Value
  | 0,   _,      _,   _, _ => none
  | f+1, [],     _,   s, K =>
      match s, K with
      | v :: _, []       => some v                                   -- halt
      | v :: _, fr :: K' => exec f fr.retCode fr.retEnv (v :: fr.retStack) K'  -- return through the frame
      | [],     _        => none
  | f+1, i :: c, env, s, K =>
    match i with
    | Instr.PUSH n   => exec f c env (.vint n :: s) K
    | Instr.ADD      => match s with
                        | .vint b :: .vint a :: s' => exec f c env (.vint (a + b) :: s') K
                        | _                        => none
    | Instr.LOOKUP j => match env[j]? with
                        | some v => exec f c env (v :: s) K
                        | none   => none
    | Instr.BIND     => match s with
                        | v :: s' => exec f c (v :: env) s' K
                        | _       => none
    | Instr.UNBIND   => match env with
                        | _ :: env' => exec f c env' s K
                        | _         => none
    | Instr.INSTALL clauseCode oc =>
        -- push a handler frame whose return continuation is the outer `oc`; run the body (`c`)
        exec f c env s ({ clause := some (clauseCode, env), retCode := oc, retEnv := env, retStack := s } :: K)
    | Instr.PERFORM  =>
        match s, K with
        | p :: s', fr :: K' =>
            match fr.clause with
            | some (clauseCode, clauseEnv) =>
                -- capture the pure continuation up to this handler as a vcont; run the clause
                let k : Value := .vcont c env s' clauseCode clauseEnv
                exec f clauseCode (p :: k :: clauseEnv) []
                  ({ clause := none, retCode := fr.retCode, retEnv := fr.retEnv, retStack := fr.retStack } :: K')
            | none => none      -- head is a pure-return frame ⇒ unhandled (single-handler-depth scope)
        | _, _ => none
    | Instr.RESUME   =>
        match s with
        | w :: .vcont cCode cEnv cStack clCode clEnv :: s' =>
            -- splice the captured continuation back: re-install the handler, and a
            -- pure frame carrying the clause's own continuation `c` (so resume returns to it)
            exec f cCode cEnv (w :: cStack)
              ({ clause := some (clCode, clEnv), retCode := [], retEnv := env, retStack := [] }
                :: { clause := none, retCode := c, retEnv := env, retStack := s' } :: K)
        | _ => none

/-! ## Compiler and top-level run -/

def compile : Src → Code → Code
  | .val n,            c => Instr.PUSH n :: c
  | .add x y,          c => compile x (compile y (Instr.ADD :: c))
  | .var i,            c => Instr.LOOKUP i :: c
  | .letE e1 e2,       c => compile e1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c))
  | .perform e,        c => compile e (Instr.PERFORM :: c)
  | .handle clause body, c => Instr.INSTALL (compile clause []) c :: compile body []
  | .resume k v,       c => compile k (compile v (Instr.RESUME :: c))

/-- Run a closed program: empty env/stack/continuation, generous fuel from the caller. -/
def run (fuel : Nat) (e : Src) : Option Value := exec fuel (compile e []) [] [] []

/-! ## Foundation: fuel monotonicity

The bedrock any correctness simulation for this machine needs: a successful run is
preserved by more fuel. Every recursive step of `exec` — including the empty-code
return-through, `PERFORM` (run the clause), and `RESUME` (run the spliced
continuation) — decreases fuel, so the machine is structurally recursive on fuel
and `simp [exec]` unfolds cleanly. -/

/-- **Fuel monotonicity (one step).** -/
theorem exec_succ : ∀ (f : Nat) (code : Code) (env : Env) (s : Stack) (K : Kont) (res : Value),
    exec f code env s K = some res → exec (f + 1) code env s K = some res := by
  intro f
  induction f with
  | zero => intro code env s K res h; simp [exec] at h
  | succ f ih =>
    intro code env s K res h
    cases code with
    | nil =>
      cases s with
      | nil => simp [exec] at h
      | cons v s'' => cases K with
        | nil => simpa only [exec] using h
        | cons fr K' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
    | cons i c =>
      cases i with
      | PUSH n => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | ADD =>
        cases s with
        | nil => simp [exec] at h
        | cons v1 r1 => cases v1 with
          | vcont _ _ _ _ _ => simp [exec] at h
          | vint b => cases r1 with
            | nil => simp [exec] at h
            | cons v2 _ => cases v2 with
              | vcont _ _ _ _ _ => simp [exec] at h
              | vint a => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | LOOKUP j =>
        simp only [exec] at h ⊢
        cases hj : env[j]? with
        | none => rw [hj] at h; simp at h
        | some v => rw [hj] at h; exact ih _ _ _ _ _ h
      | BIND =>
        cases s with
        | nil => simp [exec] at h
        | cons v s' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | UNBIND =>
        cases env with
        | nil => simp [exec] at h
        | cons _ env' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | INSTALL cl oc => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | PERFORM =>
        cases s with
        | nil => simp [exec] at h
        | cons p s' => cases K with
          | nil => simp [exec] at h
          | cons fr K' => cases hcl : fr.clause with
            | none => simp only [exec, hcl] at h; simp at h
            | some cl => obtain ⟨clauseCode, clauseEnv⟩ := cl
                         simp only [exec, hcl] at h ⊢; exact ih _ _ _ _ _ h
      | RESUME =>
        cases s with
        | nil => simp [exec] at h
        | cons w r1 => cases r1 with
          | nil => simp [exec] at h
          | cons v2 s' => cases v2 with
            | vint _ => simp [exec] at h
            | vcont cC cE cS clC clE => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h

/-- **Fuel monotonicity.** More fuel never changes a successful result. -/
theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s : Stack) (K : Kont) (res : Value)
    (h : exec f code env s K = some res) (hle : f ≤ f') : exec f' code env s K = some res := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle; clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ _ ih

/-! ## Sanity checks (the reification demonstrators) -/

section Demos
open Src
-- body `add (perform 5) 1000`: the captured continuation is "λr. r + 1000".
private def bodyP : Src := add (perform (val 5)) (val 1000)
-- resume@1 with 7, then add 100  →  (7+1000)+100 = 1107   (one-shot, NON-TAIL)
example : run 1000 (handle (add (resume (var 1) (val 7)) (val 100)) bodyP) = some (.vint 1107) := by rfl
-- resume@1 in tail position with 7  →  7+1000 = 1007       (one-shot, tail)
example : run 1000 (handle (resume (var 1) (val 7)) bodyP) = some (.vint 1007) := by rfl
-- resume twice  →  (7+1000)+(20+1000) = 2027               (MULTI-SHOT)
example : run 1000 (handle (add (resume (var 1) (val 7)) (resume (var 1) (val 20))) bodyP) = some (.vint 2027) := by
  rfl
-- clause ignores the resumption  →  999                    (ZERO-shot: discards the continuation)
example : run 1000 (handle (val 999) bodyP) = some (.vint 999) := by rfl
-- no perform: body value passes through                    →  42
example : run 1000 (handle (var 0) (val 42)) = some (.vint 42) := by rfl
-- a perform INSIDE a resumed continuation (re-handling): body `add (perform 1) (perform 2)`,
-- clause always `resume@1 with 7`. perform1 resumes → perform2 resumes → 7+7 = 14.
example : run 1000 (handle (resume (var 1) (val 7)) (add (perform (val 1)) (perform (val 2)))) = some (.vint 14) := by
  rfl
-- payload reaches the clause: `let x=5 in handle (x + resume@1 3) (perform x)`  →  5+3 = 8
example : run 1000 (letE (val 5) (handle (add (var 0) (resume (var 1) (val 3))) (perform (var 0)))) = some (.vint 8) := by
  rfl
end Demos

end Bang.CalcReify
