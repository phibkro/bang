/-!
# K3 composition: effects over the closure/CBN core — Throws, calculated

The first *real* K3 step (roadmap K3; ADR-0012): fuse the zero-shot **Throws**
effect of `CalcEff` into the full **call-by-name closure core** of `CalcCBN`,
rather than running each over a separate minimal base. This is Bahr–Hutton's
"swap the underlying monad" applied to `CalcCBN`: its evaluation monad `Maybe`
(`Option`, the fuel/divergence device) is composed with the exception monad
`Outcome`, giving `eval : Nat → Env → Src → Option Outcome`.

The one genuinely new semantic interaction — and where any bug hides — is that
**forcing can raise**: in a lazy language, forcing a thunk runs a suspended
computation that may itself `perform`/`throw`. So `forceV` returns an `Outcome`
too, and every *forcing point* (`$e`, both `add` operands, the function position
of an application, a `perform` payload) becomes an effect-propagation point.

The machine decision that falls out — clean **only** because `raise` is zero-shot
(it abandons its continuation): `CalcCBN`'s APP/FORCE run a *nested* meta-`exec`
to reduce a subterm to a value. A `THROW` is a non-local jump that cannot cross
that meta-boundary. So each nested run executes with a **fresh empty handler
stack**; if it returns `uncaught ℓ p`, the boundary **re-throws** against the live
(outer) handler stack via `unwindFind`. Because the nested computation is
abandoned on a throw anyway, empty-nested + re-throw is equivalent to dynamic
scoping, and keeps each frame's recovery code in the stream that owns it. (This
equivalence breaks for *resumable* effects — which is exactly why State-over-
closures and continuation reification are separate, harder steps; ADR-0011/0012.)

Scope: arithmetic uses `add` only — `mul` would be a verbatim duplicate of `add`'s
effect-threading, adding proof bulk but no new content (ADR-0012, simplicity).

Reads against `docs/notes/k2-calculation-playbook.md`. The proof is the *fusion*
of `CalcCBN`'s mutual `eval`/`forceV` simulation and `CalcEff`'s two-part ret/exc
simulation — a **four-part** mutual simulation, plus the new nested-uncaught
re-throw cases in APP/FORCE.
-/

namespace Bang.CalcCBNEff

abbrev Label := Nat

/-! ## Source, values, outcomes, and the call-by-name + exceptions semantics -/

/-- de Bruijn source: the CBN core (`CalcCBN`) plus `perform`/`handle`. -/
inductive Src where
  | val     : Int → Src
  | add     : Src → Src → Src
  | var     : Nat → Src
  | lam     : Src → Src
  | app     : Src → Src → Src
  | letE    : Src → Src → Src
  | thnk    : Src → Src                 -- an explicit description (delay)
  | force   : Src → Src                 -- `$e` : reduce to WHNF
  | perform : Label → Src → Src         -- raise ℓ carrying the (forced) value of the arg
  | handle  : Label → Src → Src → Src   -- handle ℓ onRaise body  (onRaise binds the payload at index 0)
deriving Repr, Inhabited

/-- WHNF values: ints, source-closures, and source-thunks (unforced
descriptions) — shared between `eval` and the machine, so correctness is an
equality, not a logical relation. -/
inductive Value where
  | vint   : Int → Value
  | vclo   : Src → List Value → Value
  | vthunk : Src → List Value → Value
deriving Inhabited

/-- The result of evaluating: a normal value, or a propagating effect carrying
its label and (forced) payload, looking for a handler. -/
inductive Outcome where
  | ret : Value → Outcome
  | exc : Label → Value → Outcome
deriving Inhabited

abbrev Env   := List Value
abbrev Stack := List Value

/- Call-by-name + exceptions, fuel-bounded. Bindings (`let`, the app argument,
`thnk`) hold *descriptions*; forcing points (`force`, both `add` operands, the
app function, a `perform` payload) reduce to WHNF via `forceV` and can raise.
`none` = out of fuel (or stuck); `some (.ret v)` = a value; `some (.exc ℓ p)` = a
propagating effect. Structurally recursive on fuel. -/
mutual
def eval : Nat → Env → Src → Option Outcome
  | 0,   _,   _          => none
  | _+1, _,   .val n     => some (.ret (.vint n))
  | _+1, env, .var i     => match env[i]? with | some v => some (.ret v) | none => none
  | _+1, env, .lam b     => some (.ret (.vclo b env))
  | _+1, env, .thnk e    => some (.ret (.vthunk e env))
  | f+1, env, .force e   =>
      match eval f env e with
      | some (.ret v) => forceV f v
      | o             => o
  | f+1, env, .letE e1 e2 => eval f (.vthunk e1 env :: env) e2
  | f+1, env, .app g a   =>
      match eval f env g with
      | some (.ret vg) =>
          match forceV f vg with
          | some (.ret (.vclo b cenv)) => eval f (.vthunk a env :: cenv) b
          | some (.ret _)              => none      -- not a function: stuck
          | o                          => o         -- none / exc propagate
      | o => o
  | f+1, env, .add x y   =>
      -- force BOTH operands (each can raise) before the int-check, matching the
      -- machine's order `compile x (FORCE :: compile y (FORCE :: ADD :: c))`: a
      -- non-int operand is stuck (`none`) only *after* the other's effects run.
      match eval f env x with
      | some (.ret vx) =>
          match forceV f vx with
          | some (.ret wx) =>
              match eval f env y with
              | some (.ret vy) =>
                  match forceV f vy with
                  | some (.ret wy) =>
                      match wx, wy with
                      | .vint a, .vint b => some (.ret (.vint (a + b)))
                      | _,       _       => none
                  | o => o
              | o => o
          | o => o
      | o => o
  | f+1, env, .perform l argE =>
      match eval f env argE with
      | some (.ret v) =>
          match forceV f v with
          | some (.ret w) => some (.exc l w)        -- raise ℓ with the forced payload
          | o             => o
      | o => o
  | f+1, env, .handle l onRaise body =>
      match eval f env body with
      | some (.ret v)    => some (.ret v)           -- normal completion: pass through
      | some (.exc l' p) => if l' = l then eval f (p :: env) onRaise   -- caught: payload at index 0
                            else some (.exc l' p)                       -- forward to an outer handler
      | none             => none
/-- Force to weak head normal form (chase the thunk chain); can raise. -/
def forceV : Nat → Value → Option Outcome
  | 0,   _             => none
  | f+1, .vthunk e env =>
      match eval f env e with
      | some (.ret v) => forceV f v
      | o             => o
  | _+1, v             => some (.ret v)
end

/-! ## The machine — derived, not designed

`CalcCBN`'s `{PUSH,ADD,LOOKUP,BIND,UNBIND,CLOS,APP,THUNK,FORCE}` plus `CalcEff`'s
`{MARK,UNMARK,THROW}`. The new piece is that the nested meta-runs of APP/FORCE
now return a machine `Result` (halt | uncaught); an `uncaught` is **re-thrown at
the boundary** against the outer handler stack. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
  | CLOS   : Src → Instr
  | APP    : Instr
  | THUNK  : Src → Instr
  | FORCE  : Instr
  | MARK   : Label → List Instr → Instr   -- install a handler: label + recovery code
  | UNMARK : Instr                         -- pop the handler frame (body finished normally)
  | THROW  : Label → Instr                 -- unwind to the nearest handler for the label
deriving Inhabited

abbrev Code := List Instr

/-- A handler frame: the label it catches, its recovery code, and the env+stack
to restore on unwinding. -/
structure Frame where
  label : Label
  recovery : Code
  savedEnv : Env
  savedStack : Stack
deriving Inhabited

abbrev HStack := List Frame

/-- The machine's outcome: a normal halt (final value stack) or an effect that
escaped every handler. -/
inductive Result where
  | halt     : Stack → Result
  | uncaught : Label → Value → Result
deriving Inhabited

def compile : Src → Code → Code
  | .val n,      c => Instr.PUSH n :: c
  | .var i,      c => Instr.LOOKUP i :: c
  | .lam b,      c => Instr.CLOS b :: c
  | .thnk e,     c => Instr.THUNK e :: c
  | .force e,    c => compile e (Instr.FORCE :: c)
  | .letE e1 e2, c => Instr.THUNK e1 :: Instr.BIND :: compile e2 (Instr.UNBIND :: c)
  | .app g a,    c => compile g (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c)
  | .add x y,    c => compile x (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c))
  | .perform l e, c => compile e (Instr.FORCE :: Instr.THROW l :: c)   -- force the payload, then throw
  | .handle l onRaise body, c =>
      Instr.MARK l (Instr.BIND :: compile onRaise (Instr.UNBIND :: c))
        :: compile body (Instr.UNMARK :: c)

/-- Find the nearest handler frame catching `l`: the recovery code + restored
config (env, payload-on-stack, remaining handler stack), or `uncaught`. A *pure*
function (no `exec` argument), so `exec` stays structurally recursive. -/
def unwindFind : Label → Value → HStack → (Code × Env × Stack × HStack) ⊕ Result
  | l, p, []       => .inr (.uncaught l p)
  | l, p, fr :: hs => if fr.label = l
                      then .inl (fr.recovery, fr.savedEnv, p :: fr.savedStack, hs)
                      else unwindFind l p hs

/-- The machine. Fuel-bounded; structurally recursive on fuel. APP/FORCE run a
nested meta-`exec` with an empty handler stack and re-throw an escaping
`uncaught` against the outer handler stack `hs`. -/
def exec : Nat → Code → Env → Stack → HStack → Option Result
  | 0,   _,       _,   _, _  => none
  | _+1, [],      _,   s, _  => some (.halt s)
  | f+1, i :: c,  env, s, hs =>
    match i, s with
    | Instr.PUSH n,   s                  => exec f c env (.vint n :: s) hs
    | Instr.ADD,      (.vint b :: .vint a :: s) => exec f c env (.vint (a + b) :: s) hs
    | Instr.LOOKUP i, s                  => match env[i]? with
                                            | some v => exec f c env (v :: s) hs
                                            | none   => none
    | Instr.BIND,     (v :: s)           => exec f c (v :: env) s hs
    | Instr.UNBIND,   s                  => match env with
                                            | _ :: env' => exec f c env' s hs
                                            | []        => none
    | Instr.CLOS b,   s                  => exec f c env (.vclo b env :: s) hs
    | Instr.THUNK e', s                  => exec f c env (.vthunk e' env :: s) hs
    | Instr.MARK l recov, s              => exec f c env s (Frame.mk l recov env s :: hs)
    | Instr.UNMARK,   s                  => match hs with
                                            | _ :: hs' => exec f c env s hs'
                                            | []       => none
    | Instr.APP,      (va :: .vclo b cenv :: s) =>
        match exec f (compile b []) (va :: cenv) [] [] with
        | some (.halt (rv :: _)) => exec f c env (rv :: s) hs
        | some (.uncaught l p)   => match unwindFind l p hs with     -- re-throw at the boundary
                                    | .inl (recov, e', s', hs') => exec f recov e' s' hs'
                                    | .inr res                => some res
        | _                      => none
    | Instr.FORCE,    (.vthunk body tenv :: s) =>
        match exec f (compile body [Instr.FORCE]) tenv [] [] with
        | some (.halt (w :: _)) => exec f c env (w :: s) hs
        | some (.uncaught l p)  => match unwindFind l p hs with      -- re-throw at the boundary
                                   | .inl (recov, e', s', hs') => exec f recov e' s' hs'
                                   | .inr res                => some res
        | _                     => none
    | Instr.FORCE,    (v :: s)           => exec f c env (v :: s) hs   -- already WHNF (vint/vclo)
    | Instr.THROW l,  (p :: _)           =>
        match unwindFind l p hs with
        | .inl (recov, e', s', hs') => exec f recov e' s' hs'
        | .inr res                => some res
    | _,              _                  => none                       -- stuck

/-- The result of throwing `l p` against `hs` with `f` fuel: run the nearest
matching frame's recovery, or report uncaught. (`exec`'s `THROW`/re-throw logic,
factored out for the proof; definitionally equal to the inlined arms.) -/
def throwExec (f : Nat) (l : Label) (p : Value) (hs : HStack) : Option Result :=
  match unwindFind l p hs with
  | .inl (recov, e', s', hs') => exec f recov e' s' hs'
  | .inr res                  => some res

/-- Run a closed program: enough fuel, empty env/stack/handler-stack. -/
def run (fuel : Nat) (e : Src) : Option Result := exec fuel (compile e []) [] [] []

/-- Map a reference `Outcome` to the machine `Result` it should produce. -/
def outcomeToResult : Outcome → Result
  | .ret v   => .halt [v]
  | .exc l p => .uncaught l p

/-! ## Correctness — calculated `exec ∘ compile ≡ eval`

The proof fuses `CalcCBN` (mutual `eval`/`forceV`, nested APP/FORCE) and `CalcEff`
(two-part ret/exc, handler stack + `unwindFind`). Structure:

1. `exec_succ`/`exec_mono`, `throwExec_mono` — fuel monotonicity.
2. `sim` — a **four-part** mutual simulation by induction on the eval fuel:
   eval-ret, eval-exc, forceV-ret, forceV-exc. The new content vs the two parents
   is the nested-`uncaught` re-throw in APP/FORCE (eval-exc app body-raises;
   forceV-exc on a thunk whose forcing raises).
3. `compile_correct` — the corollary. -/

/-- **Fuel monotonicity (one step).** Explicit per-instruction, so the two nested
arms (`APP`, `FORCE`-on-a-thunk) — each with a `halt` and an `uncaught`-re-throw
sub-case — stay unambiguous. -/
theorem exec_succ : ∀ (f : Nat) (code : Code) (env : Env) (s : Stack) (hs : HStack) (r : Result),
    exec f code env s hs = some r → exec (f + 1) code env s hs = some r := by
  intro f
  induction f with
  | zero => intro code env s hs r h; simp [exec] at h
  | succ f ih =>
    intro code env s hs r h
    cases code with
    | nil => simpa only [exec] using h
    | cons i c =>
      cases i with
      | PUSH n     => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | CLOS b     => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | THUNK e    => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | MARK l rcv => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | ADD =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v1 r1 => cases v1 with
            | vthunk _ _ => simp only [exec] at h; simp at h
            | vclo _ _ => simp only [exec] at h; simp at h
            | vint _ => cases r1 with
              | nil => simp only [exec] at h; simp at h
              | cons v2 _ => cases v2 with
                | vthunk _ _ => simp only [exec] at h; simp at h
                | vclo _ _ => simp only [exec] at h; simp at h
                | vint _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | LOOKUP j =>
          simp only [exec] at h ⊢
          cases hj : env[j]? with
          | none => rw [hj] at h; simp at h
          | some v => rw [hj] at h; exact ih _ _ _ _ _ h
      | BIND =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v s' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | UNBIND =>
          cases env with
          | nil => simp only [exec] at h; simp at h
          | cons _ env' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | UNMARK =>
          cases hs with
          | nil => simp only [exec] at h; simp at h
          | cons _ hs' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | THROW l =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons p s' =>
              simp only [exec] at h ⊢
              cases hu : unwindFind l p hs with
              | inl x => obtain ⟨recov, e', s'', hs''⟩ := x; rw [hu] at h; exact ih _ _ _ _ _ h
              | inr res => rw [hu] at h; exact h
      | APP =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons va rest => cases rest with
            | nil => simp only [exec] at h; simp at h
            | cons v1 s' => cases v1 with
              | vint _ => simp only [exec] at h; simp at h
              | vthunk _ _ => simp only [exec] at h; simp at h
              | vclo body cenv =>
                  simp only [exec] at h ⊢
                  cases hb : exec f (compile body []) (va :: cenv) [] [] with
                  | none => rw [hb] at h; simp at h
                  | some res => cases res with
                    | halt rs => cases rs with
                      | nil => rw [hb] at h; simp at h
                      | cons rv _ => rw [hb] at h; rw [ih _ _ _ _ _ hb]; exact ih _ _ _ _ _ h
                    | uncaught l p =>
                        rw [hb] at h; rw [ih _ _ _ _ _ hb]
                        simp only [] at h ⊢
                        cases hu : unwindFind l p hs with
                        | inl x => obtain ⟨recov, e', s'', hs''⟩ := x; rw [hu] at h; exact ih _ _ _ _ _ h
                        | inr res => rw [hu] at h; exact h
      | FORCE =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v0 s' => cases v0 with
            | vint _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
            | vclo _ _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
            | vthunk body tenv =>
                simp only [exec] at h ⊢
                cases hb : exec f (compile body [Instr.FORCE]) tenv [] [] with
                | none => rw [hb] at h; simp at h
                | some res => cases res with
                  | halt rs => cases rs with
                    | nil => rw [hb] at h; simp at h
                    | cons w _ => rw [hb] at h; rw [ih _ _ _ _ _ hb]; exact ih _ _ _ _ _ h
                  | uncaught l p =>
                      rw [hb] at h; rw [ih _ _ _ _ _ hb]
                      simp only [] at h ⊢
                      cases hu : unwindFind l p hs with
                      | inl x => obtain ⟨recov, e', s'', hs''⟩ := x; rw [hu] at h; exact ih _ _ _ _ _ h
                      | inr res => rw [hu] at h; exact h

/-- **Fuel monotonicity.** -/
theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s : Stack) (hs : HStack) (r : Result)
    (h : exec f code env s hs = some r) (hle : f ≤ f') : exec f' code env s hs = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle; clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ _ ih

/-- **Throw monotonicity.** -/
theorem throwExec_mono (f f' : Nat) (l : Label) (p : Value) (hs : HStack) (r : Result)
    (h : throwExec f l p hs = some r) (hle : f ≤ f') : throwExec f' l p hs = some r := by
  simp only [throwExec] at h ⊢
  cases hu : unwindFind l p hs with
  | inl x => obtain ⟨rc, e', s', hs'⟩ := x; rw [hu] at h; exact exec_mono _ _ _ _ _ _ _ h hle
  | inr res => rw [hu] at h; exact h

/-- **The four-part mutual simulation**, by induction on the eval fuel: eval-ret,
eval-exc, forceV-ret, forceV-exc proved together. The new content vs the two
parents (`CalcCBN`, `CalcEff`) is the nested-`uncaught` re-throw in APP/FORCE — a
function call / thunk-force whose body raises returns `uncaught` from the nested
meta-run, which the boundary re-throws against the outer handler stack. -/
theorem sim : ∀ (fe : Nat),
    (∀ env e v, eval fe env e = some (.ret v) → ∀ c s hs F r,
        exec F c env (v :: s) hs = some r → ∃ F', exec F' (compile e c) env s hs = some r) ∧
    (∀ env e l p, eval fe env e = some (.exc l p) → ∀ c s hs F r,
        throwExec F l p hs = some r → ∃ F', exec F' (compile e c) env s hs = some r) ∧
    (∀ v w, forceV fe v = some (.ret w) → ∀ env c s hs F r,
        exec F c env (w :: s) hs = some r → ∃ F', exec F' (Instr.FORCE :: c) env (v :: s) hs = some r) ∧
    (∀ v l p, forceV fe v = some (.exc l p) → ∀ env c s hs F r,
        throwExec F l p hs = some r → ∃ F', exec F' (Instr.FORCE :: c) env (v :: s) hs = some r) := by
  intro fe
  induction fe with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro env e v h; simp [eval] at h
    · intro env e l p h; simp [eval] at h
    · intro v w h; simp [forceV] at h
    · intro v l p h; simp [forceV] at h
  | succ fe ih =>
    obtain ⟨ihe, ihx, ihfr, ihfx⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ============================ eval-ret ============================
      intro env e
      cases e with
      | val n => intro v h c s hs F r hr
                 simp only [eval, Option.some.injEq, Outcome.ret.injEq] at h; subst h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | var i => intro v h c s hs F r hr
                 simp only [eval] at h
                 cases hi : env[i]? with
                 | none => simp [hi] at h
                 | some vv =>
                   simp only [hi, Option.some.injEq, Outcome.ret.injEq] at h; subst h
                   exact ⟨F + 1, by simp only [compile, exec, hi]; exact hr⟩
      | lam b => intro v h c s hs F r hr
                 simp only [eval, Option.some.injEq, Outcome.ret.injEq] at h; subst h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | thnk e => intro v h c s hs F r hr
                  simp only [eval, Option.some.injEq, Outcome.ret.injEq] at h; subst h
                  exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | force e => intro v h c s hs F r hr
                   simp only [eval] at h
                   cases he : eval fe env e with
                   | none => simp [he] at h
                   | some oe => cases oe with
                     | exc l p => simp [he] at h
                     | ret v' =>
                       simp only [he] at h
                       obtain ⟨G, hG⟩ := ihfr v' v h env c s hs F r hr
                       obtain ⟨F', hF'⟩ := ihe env e v' he (Instr.FORCE :: c) s hs G r hG
                       exact ⟨F', by simpa only [compile] using hF'⟩
      | letE e1 e2 => intro v h c s hs F r hr
                      simp only [eval] at h
                      obtain ⟨G2, hG2⟩ := ihe (.vthunk e1 env :: env) e2 v h (Instr.UNBIND :: c) s hs (F + 1) r
                        (by simp only [exec]; exact hr)
                      exact ⟨G2 + 2, by simp only [compile, exec]; exact hG2⟩
      | add x y => intro v h c s hs F r hr
                   simp only [eval] at h
                   cases hx : eval fe env x with
                   | none => simp [hx] at h
                   | some ox => cases ox with
                     | exc l p => simp [hx] at h
                     | ret vx =>
                       simp only [hx] at h
                       cases hfx : forceV fe vx with
                       | none => simp [hfx] at h
                       | some ofx => cases ofx with
                         | exc l p => simp [hfx] at h
                         | ret wx =>
                           simp only [hfx] at h
                           cases hy : eval fe env y with
                           | none => simp [hy] at h
                           | some oy => cases oy with
                             | exc l p => simp [hy] at h
                             | ret vy =>
                               simp only [hy] at h
                               cases hfy : forceV fe vy with
                               | none => simp [hfy] at h
                               | some ofy => cases ofy with
                                 | exc l p => simp [hfy] at h
                                 | ret wy =>
                                   simp only [hfy] at h
                                   cases wx with
                                   | vclo _ _ => simp at h
                                   | vthunk _ _ => simp at h
                                   | vint a => cases wy with
                                     | vclo _ _ => simp at h
                                     | vthunk _ _ => simp at h
                                     | vint b =>
                                       simp only [Option.some.injEq, Outcome.ret.injEq] at h; subst h
                                       have hadd : exec (F + 1) (Instr.ADD :: c) env (.vint b :: .vint a :: s) hs = some r := by
                                         simp only [exec]; exact hr
                                       obtain ⟨Gy, hGy⟩ := ihfr vy (.vint b) hfy env (Instr.ADD :: c) (.vint a :: s) hs (F + 1) r hadd
                                       obtain ⟨Hy, hHy⟩ := ihe env y vy hy (Instr.FORCE :: Instr.ADD :: c) (.vint a :: s) hs Gy r hGy
                                       obtain ⟨Gx, hGx⟩ := ihfr vx (.vint a) hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Hy r hHy
                                       obtain ⟨F', hF'⟩ := ihe env x vx hx
                                         (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gx r hGx
                                       exact ⟨F', by simpa only [compile] using hF'⟩
      | app g a => intro v h c s hs F r hr
                   simp only [eval] at h
                   cases hg : eval fe env g with
                   | none => simp [hg] at h
                   | some og => cases og with
                     | exc l p => simp [hg] at h
                     | ret vg =>
                       simp only [hg] at h
                       cases hfg : forceV fe vg with
                       | none => simp [hfg] at h
                       | some ofg => cases ofg with
                         | exc l p => simp [hfg] at h
                         | ret wg => cases wg with
                           | vint _ => simp [hfg] at h
                           | vthunk _ _ => simp [hfg] at h
                           | vclo b cenv =>
                             simp only [hfg] at h
                             obtain ⟨G, hG⟩ := ihe (.vthunk a env :: cenv) b v h [] [] [] 1 (.halt [v]) (by simp [exec])
                             have hGbig : exec (G + F) (compile b []) (.vthunk a env :: cenv) [] [] = some (.halt [v]) :=
                               exec_mono _ (G + F) _ _ _ _ _ hG (by omega)
                             have hrbig : exec (G + F) c env (v :: s) hs = some r := exec_mono _ (G + F) _ _ _ _ _ hr (by omega)
                             have happ : exec (G + F + 1) (Instr.APP :: c) env (.vthunk a env :: .vclo b cenv :: s) hs = some r := by
                               simp only [exec, hGbig]; exact hrbig
                             have hthunk : exec (G + F + 2) (Instr.THUNK a :: Instr.APP :: c) env (.vclo b cenv :: s) hs = some r := by
                               simp only [exec]; exact happ
                             obtain ⟨H, hH⟩ := ihfr vg (.vclo b cenv) hfg env (Instr.THUNK a :: Instr.APP :: c) s hs (G + F + 2) r hthunk
                             obtain ⟨F', hF'⟩ := ihe env g vg hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs H r hH
                             exact ⟨F', by simpa only [compile] using hF'⟩
      | perform lab argE => intro v h c s hs F r hr
                            simp only [eval] at h
                            cases ha : eval fe env argE with
                            | none => simp [ha] at h
                            | some oa => cases oa with
                              | exc l p => simp [ha] at h
                              | ret va =>
                                simp only [ha] at h
                                cases hfa : forceV fe va with
                                | none => simp [hfa] at h
                                | some ofa => cases ofa with
                                  | exc l p => simp [hfa] at h
                                  | ret w => simp [hfa] at h
      | handle lab onRaise body =>
          intro v h c s hs F r hr
          simp only [eval] at h
          cases hb : eval fe env body with
          | none => simp [hb] at h
          | some ob => cases ob with
            | ret w =>
              simp only [hb, Option.some.injEq, Outcome.ret.injEq] at h; subst h
              obtain ⟨Gb, hGb⟩ := ihe env body w hb (Instr.UNMARK :: c) s
                (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) (F + 1) r
                (by simp only [exec]; exact hr)
              exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
            | exc l' p =>
              simp only [hb] at h
              by_cases hc : l' = lab
              · rw [if_pos hc] at h
                obtain ⟨Go, hGo⟩ := ihe (p :: env) onRaise v h (Instr.UNBIND :: c) s hs (F + 1) r
                  (by simp only [exec]; exact hr)
                have hthr : throwExec (Go + 1) l' p
                    (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) = some r := by
                  simp only [throwExec, unwindFind]; rw [if_pos hc.symm]; simp only [exec]; exact hGo
                obtain ⟨Gb, hGb⟩ := ihx env body l' p hb (Instr.UNMARK :: c) s
                  (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) (Go + 1) r hthr
                exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
              · rw [if_neg hc] at h; simp at h
    · -- ============================ eval-exc ============================
      intro env e
      cases e with
      | val n => intro l p h c s hs F r hu; simp [eval] at h
      | var i => intro l p h c s hs F r hu
                 simp only [eval] at h
                 cases hi : env[i]? with
                 | none => simp [hi] at h
                 | some vv => simp [hi] at h
      | lam b => intro l p h c s hs F r hu; simp [eval] at h
      | thnk e => intro l p h c s hs F r hu; simp [eval] at h
      | force e => intro l p h c s hs F r hu
                   simp only [eval] at h
                   cases he : eval fe env e with
                   | none => simp [he] at h
                   | some oe => cases oe with
                     | exc l' p' =>
                       simp only [he, Option.some.injEq, Outcome.exc.injEq] at h
                       obtain ⟨hl, hp⟩ := h; subst l'; subst p'
                       have := ihx env e l p he (Instr.FORCE :: c) s hs F r hu
                       simpa only [compile] using this
                     | ret v' =>
                       simp only [he] at h
                       obtain ⟨G, hG⟩ := ihfx v' l p h env c s hs F r hu
                       obtain ⟨F', hF'⟩ := ihe env e v' he (Instr.FORCE :: c) s hs G r hG
                       exact ⟨F', by simpa only [compile] using hF'⟩
      | letE e1 e2 => intro l p h c s hs F r hu
                      simp only [eval] at h
                      obtain ⟨G2, hG2⟩ := ihx (.vthunk e1 env :: env) e2 l p h (Instr.UNBIND :: c) s hs F r hu
                      exact ⟨G2 + 2, by simp only [compile, exec]; exact hG2⟩
      | add x y => intro l p h c s hs F r hu
                   simp only [eval] at h
                   cases hx : eval fe env x with
                   | none => simp [hx] at h
                   | some ox => cases ox with
                     | exc lx px =>
                       simp only [hx, Option.some.injEq, Outcome.exc.injEq] at h
                       obtain ⟨hl, hp⟩ := h; subst lx; subst px
                       have := ihx env x l p hx (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs F r hu
                       simpa only [compile] using this
                     | ret vx =>
                       simp only [hx] at h
                       cases hfx : forceV fe vx with
                       | none => simp [hfx] at h
                       | some ofx => cases ofx with
                         | exc lx px =>
                           simp only [hfx, Option.some.injEq, Outcome.exc.injEq] at h
                           obtain ⟨hl, hp⟩ := h; subst lx; subst px
                           obtain ⟨G, hG⟩ := ihfx vx l p hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs F r hu
                           obtain ⟨F', hF'⟩ := ihe env x vx hx
                             (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs G r hG
                           exact ⟨F', by simpa only [compile] using hF'⟩
                         | ret wx =>
                           simp only [hfx] at h
                           cases hy : eval fe env y with
                           | none => simp [hy] at h
                           | some oy => cases oy with
                             | exc ly py =>
                               simp only [hy, Option.some.injEq, Outcome.exc.injEq] at h
                               obtain ⟨hl, hp⟩ := h; subst ly; subst py
                               obtain ⟨Gy, hGy⟩ := ihx env y l p hy (Instr.FORCE :: Instr.ADD :: c) (wx :: s) hs F r hu
                               obtain ⟨Gx, hGx⟩ := ihfr vx wx hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gy r hGy
                               obtain ⟨F', hF'⟩ := ihe env x vx hx
                                 (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gx r hGx
                               exact ⟨F', by simpa only [compile] using hF'⟩
                             | ret vy =>
                               simp only [hy] at h
                               cases hfy : forceV fe vy with
                               | none => simp [hfy] at h
                               | some ofy => cases ofy with
                                 | exc ly py =>
                                   simp only [hfy, Option.some.injEq, Outcome.exc.injEq] at h
                                   obtain ⟨hl, hp⟩ := h; subst ly; subst py
                                   obtain ⟨Gy, hGy⟩ := ihfx vy l p hfy env (Instr.ADD :: c) (wx :: s) hs F r hu
                                   obtain ⟨Hy, hHy⟩ := ihe env y vy hy (Instr.FORCE :: Instr.ADD :: c) (wx :: s) hs Gy r hGy
                                   obtain ⟨Gx, hGx⟩ := ihfr vx wx hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Hy r hHy
                                   obtain ⟨F', hF'⟩ := ihe env x vx hx
                                     (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gx r hGx
                                   exact ⟨F', by simpa only [compile] using hF'⟩
                                 | ret wy =>
                                   simp only [hfy] at h
                                   cases wx with
                                   | vclo _ _ => simp at h
                                   | vthunk _ _ => simp at h
                                   | vint a => cases wy with
                                     | vclo _ _ => simp at h
                                     | vthunk _ _ => simp at h
                                     | vint b => simp at h
      | app g a => intro l p h c s hs F r hu
                   simp only [eval] at h
                   cases hg : eval fe env g with
                   | none => simp [hg] at h
                   | some og => cases og with
                     | exc lg pg =>
                       simp only [hg, Option.some.injEq, Outcome.exc.injEq] at h
                       obtain ⟨hl, hp⟩ := h; subst lg; subst pg
                       have := ihx env g l p hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs F r hu
                       simpa only [compile] using this
                     | ret vg =>
                       simp only [hg] at h
                       cases hfg : forceV fe vg with
                       | none => simp [hfg] at h
                       | some ofg => cases ofg with
                         | exc lf pf =>
                           simp only [hfg, Option.some.injEq, Outcome.exc.injEq] at h
                           obtain ⟨hl, hp⟩ := h; subst lf; subst pf
                           obtain ⟨G, hG⟩ := ihfx vg l p hfg env (Instr.THUNK a :: Instr.APP :: c) s hs F r hu
                           obtain ⟨F', hF'⟩ := ihe env g vg hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs G r hG
                           exact ⟨F', by simpa only [compile] using hF'⟩
                         | ret wg => cases wg with
                           | vint _ => simp [hfg] at h
                           | vthunk _ _ => simp [hfg] at h
                           | vclo b cenv =>
                             simp only [hfg] at h
                             obtain ⟨G, hG⟩ := ihx (.vthunk a env :: cenv) b l p h [] [] [] 0 (.uncaught l p)
                               (by simp [throwExec, unwindFind])
                             have hGbig : exec (G + F) (compile b []) (.vthunk a env :: cenv) [] [] = some (.uncaught l p) :=
                               exec_mono _ (G + F) _ _ _ _ _ hG (by omega)
                             have huF : throwExec (G + F) l p hs = some r := throwExec_mono F (G + F) l p hs r hu (by omega)
                             have happ : exec (G + F + 1) (Instr.APP :: c) env (.vthunk a env :: .vclo b cenv :: s) hs = some r := by
                               simp only [exec, hGbig]; exact huF
                             have hthunk : exec (G + F + 2) (Instr.THUNK a :: Instr.APP :: c) env (.vclo b cenv :: s) hs = some r := by
                               simp only [exec]; exact happ
                             obtain ⟨H, hH⟩ := ihfr vg (.vclo b cenv) hfg env (Instr.THUNK a :: Instr.APP :: c) s hs (G + F + 2) r hthunk
                             obtain ⟨F', hF'⟩ := ihe env g vg hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs H r hH
                             exact ⟨F', by simpa only [compile] using hF'⟩
      | perform lab argE =>
          intro l p h c s hs F r hu
          simp only [eval] at h
          cases ha : eval fe env argE with
          | none => simp [ha] at h
          | some oa => cases oa with
            | exc l' p' =>
              simp only [ha, Option.some.injEq, Outcome.exc.injEq] at h
              obtain ⟨hl, hp⟩ := h; subst l'; subst p'
              have := ihx env argE l p ha (Instr.FORCE :: Instr.THROW lab :: c) s hs F r hu
              simpa only [compile] using this
            | ret va =>
              simp only [ha] at h
              cases hfa : forceV fe va with
              | none => simp [hfa] at h
              | some ofa => cases ofa with
                | exc l' p' =>
                  simp only [hfa, Option.some.injEq, Outcome.exc.injEq] at h
                  obtain ⟨hl, hp⟩ := h; subst l'; subst p'
                  obtain ⟨G, hG⟩ := ihfx va l p hfa env (Instr.THROW lab :: c) s hs F r hu
                  obtain ⟨F', hF'⟩ := ihe env argE va ha (Instr.FORCE :: Instr.THROW lab :: c) s hs G r hG
                  exact ⟨F', by simpa only [compile] using hF'⟩
                | ret w =>
                  simp only [hfa, Option.some.injEq, Outcome.exc.injEq] at h
                  obtain ⟨hl, hp⟩ := h; subst l; subst p
                  have hthrow : exec (F + 1) (Instr.THROW lab :: c) env (w :: s) hs = some r := by
                    simp only [exec]; exact hu
                  obtain ⟨G, hG⟩ := ihfr va w hfa env (Instr.THROW lab :: c) s hs (F + 1) r hthrow
                  obtain ⟨F', hF'⟩ := ihe env argE va ha (Instr.FORCE :: Instr.THROW lab :: c) s hs G r hG
                  exact ⟨F', by simpa only [compile] using hF'⟩
      | handle lab onRaise body =>
          intro l p h c s hs F r hu
          simp only [eval] at h
          cases hb : eval fe env body with
          | none => simp [hb] at h
          | some ob => cases ob with
            | ret w => simp [hb] at h
            | exc l' p' =>
              simp only [hb] at h
              by_cases hc : l' = lab
              · rw [if_pos hc] at h
                obtain ⟨Go, hGo⟩ := ihx (p' :: env) onRaise l p h (Instr.UNBIND :: c) s hs F r hu
                have hthr : throwExec (Go + 1) l' p'
                    (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) = some r := by
                  simp only [throwExec, unwindFind]; rw [if_pos hc.symm]; simp only [exec]; exact hGo
                obtain ⟨Gb, hGb⟩ := ihx env body l' p' hb (Instr.UNMARK :: c) s
                  (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) (Go + 1) r hthr
                exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
              · rw [if_neg hc] at h; simp only [Option.some.injEq, Outcome.exc.injEq] at h
                obtain ⟨hl, hp⟩ := h; subst l'; subst p'
                have hthr : throwExec F l p
                    (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) = some r := by
                  simp only [throwExec, unwindFind]; rw [if_neg (Ne.symm hc)]; exact hu
                obtain ⟨Gb, hGb⟩ := ihx env body l p hb (Instr.UNMARK :: c) s
                  (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) F r hthr
                exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
    · -- ============================ forceV-ret ============================
      intro v w h env c s hs F r hr
      cases v with
      | vint n => simp only [forceV, Option.some.injEq, Outcome.ret.injEq] at h; subst h
                  exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vclo b ve => simp only [forceV, Option.some.injEq, Outcome.ret.injEq] at h; subst h
                     exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vthunk e ve =>
        simp only [forceV] at h
        cases he : eval fe ve e with
        | none => simp [he] at h
        | some oe => cases oe with
          | exc l p => simp [he] at h
          | ret v' =>
            simp only [he] at h
            obtain ⟨A, hA⟩ := ihfr v' w h ve [] [] [] 1 (.halt [w]) (by simp [exec])
            obtain ⟨B, hB⟩ := ihe ve e v' he [Instr.FORCE] [] [] A (.halt [w]) hA
            have hBbig : exec (B + F) (compile e [Instr.FORCE]) ve [] [] = some (.halt [w]) :=
              exec_mono _ (B + F) _ _ _ _ _ hB (by omega)
            have hrbig : exec (B + F) c env (w :: s) hs = some r := exec_mono _ (B + F) _ _ _ _ _ hr (by omega)
            exact ⟨B + F + 1, by simp only [exec, hBbig]; exact hrbig⟩
    · -- ============================ forceV-exc ============================
      intro v l p h env c s hs F r hu
      cases v with
      | vint n => simp [forceV] at h
      | vclo b ve => simp [forceV] at h
      | vthunk e ve =>
        simp only [forceV] at h
        cases he : eval fe ve e with
        | none => simp [he] at h
        | some oe => cases oe with
          | exc l' p' =>
            simp only [he, Option.some.injEq, Outcome.exc.injEq] at h
            obtain ⟨hl, hp⟩ := h; subst l'; subst p'
            obtain ⟨G, hG⟩ := ihx ve e l p he [Instr.FORCE] [] [] 0 (.uncaught l p) (by simp [throwExec, unwindFind])
            have hGbig : exec (G + F) (compile e [Instr.FORCE]) ve [] [] = some (.uncaught l p) :=
              exec_mono _ (G + F) _ _ _ _ _ hG (by omega)
            have huF : throwExec (G + F) l p hs = some r := throwExec_mono F (G + F) l p hs r hu (by omega)
            exact ⟨G + F + 1, by simp only [exec, hGbig]; exact huF⟩
          | ret v' =>
            simp only [he] at h
            obtain ⟨A, hA⟩ := ihfx v' l p h ve [] [] [] 0 (.uncaught l p) (by simp [throwExec, unwindFind])
            obtain ⟨G, hG⟩ := ihe ve e v' he [Instr.FORCE] [] [] A (.uncaught l p) hA
            have hGbig : exec (G + F) (compile e [Instr.FORCE]) ve [] [] = some (.uncaught l p) :=
              exec_mono _ (G + F) _ _ _ _ _ hG (by omega)
            have huF : throwExec (G + F) l p hs = some r := throwExec_mono F (G + F) l p hs r hu (by omega)
            exact ⟨G + F + 1, by simp only [exec, hGbig]; exact huF⟩

/-- **Correctness of the calculated CBN+Throws machine.** If `eval` produces an
outcome `o`, the compiled program (with enough fuel) halts on `[v]` for `ret v`
and reports `uncaught ℓ p` for `exc ℓ p`. -/
theorem compile_correct (fe : Nat) (e : Src) (o : Outcome)
    (h : eval fe [] e = some o) : ∃ F, run F e = some (outcomeToResult o) := by
  cases o with
  | ret v =>
    obtain ⟨F, hF⟩ := (sim fe).1 [] e v h [] [] [] 1 (.halt [v]) (by simp [exec])
    exact ⟨F, by simpa only [run, outcomeToResult] using hF⟩
  | exc l p =>
    obtain ⟨F, hF⟩ := (sim fe).2.1 [] e l p h [] [] [] 1 (.uncaught l p)
      (by simp [throwExec, unwindFind])
    exact ⟨F, by simpa only [run, outcomeToResult] using hF⟩

end Bang.CalcCBNEff
