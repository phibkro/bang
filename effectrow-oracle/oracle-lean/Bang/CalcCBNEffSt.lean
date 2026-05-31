/-!
# K3 capstone: Throws *and* State together over the closure/CBN core

Both effects in **one** machine (ADR-0014): the handler stack of `CalcCBNEff`
*and* the threaded state register of `CalcCBNSt`, over the call-by-name
closure/thunk core. This realises the effect-row model in the machine — a program
may use both effects at once; its row is the *set* `{Throws, State}`.

`eval : Nat → State → Env → Src → Option (Outcome × State)` — every result carries
the current state. On a normal value, `(.ret v, st')`; on a propagating effect,
`(.exc ℓ p, st_throw)` — the state **at the point of the throw**.

The interaction (the design decision): **State persists through a throw.** The
register simply threads through unwinding; a `put` before a `throw` is kept, and a
handler catching the throw resumes from the throw-time state. Rationale: STM is
BANG's privileged *transactional* primitive (ADR-0003), so plain `State` is the
simple mutable register and rollback is STM's job (the rejected alternative).

This is the union of the two parents' mechanisms: State **threads** (resumable, no
re-throw) while Throws **re-throws** an `uncaught` at the meta-call boundary
(zero-shot). Both happen at once — the nested meta-run returns `(Result × State)`;
on `uncaught` the boundary re-throws *carrying the throw-time state*.

Scope: `get`/`put` (a single global register; `runState` scoping × throw — leak vs
restore — is a documented follow-up) + `perform`/`handle` + the CBN core, `add`
only (ADR-0009/0014). Proof: `CalcCBNEff`'s **four-part** mutual simulation
(eval/forceV × ret/exc) with the state register threaded through every step.
-/

namespace Bang.CalcCBNEffSt

abbrev Label := Nat
abbrev State := Int

/-! ## Source, values, outcomes -/

inductive Src where
  | val     : Int → Src
  | add     : Src → Src → Src
  | var     : Nat → Src
  | lam     : Src → Src
  | app     : Src → Src → Src
  | letE    : Src → Src → Src
  | thnk    : Src → Src
  | force   : Src → Src
  | get     : Src
  | put     : Src → Src
  | perform : Label → Src → Src
  | handle  : Label → Src → Src → Src
deriving Repr, Inhabited

inductive Value where
  | vint   : Int → Value
  | vclo   : Src → List Value → Value
  | vthunk : Src → List Value → Value
deriving Inhabited

inductive Outcome where
  | ret : Value → Outcome
  | exc : Label → Value → Outcome
deriving Inhabited

abbrev Env   := List Value
abbrev Stack := List Value

/- Call-by-name + Throws + State, fuel-bounded, threading a state register. On a
propagating effect the carried state is the state at the throw. -/
mutual
def eval : Nat → State → Env → Src → Option (Outcome × State)
  | 0,   _,  _,   _         => none
  | _+1, st, _,   .val n    => some (.ret (.vint n), st)
  | _+1, st, env, .var i    => match env[i]? with | some v => some (.ret v, st) | none => none
  | _+1, st, env, .lam b    => some (.ret (.vclo b env), st)
  | _+1, st, env, .thnk e   => some (.ret (.vthunk e env), st)
  | _+1, st, _,   .get      => some (.ret (.vint st), st)
  | f+1, st, env, .force e  =>
      match eval f st env e with
      | some (.ret v, st1)   => forceV f st1 v
      | some (.exc l p, st1) => some (.exc l p, st1)
      | none                 => none
  | f+1, st, env, .letE e1 e2 => eval f st (.vthunk e1 env :: env) e2
  | f+1, st, env, .app g a  =>
      match eval f st env g with
      | some (.ret vg, st1) =>
          match forceV f st1 vg with
          | some (.ret (.vclo b cenv), st2) => eval f st2 (.vthunk a env :: cenv) b
          | some (.ret _, _)                => none
          | some (.exc l p, st2)            => some (.exc l p, st2)
          | none                            => none
      | some (.exc l p, st1) => some (.exc l p, st1)
      | none                 => none
  | f+1, st, env, .add x y  =>
      match eval f st env x with
      | some (.ret vx, st1) =>
          match forceV f st1 vx with
          | some (.ret wx, st2) =>
              match eval f st2 env y with
              | some (.ret vy, st3) =>
                  match forceV f st3 vy with
                  | some (.ret wy, st4) =>
                      match wx, wy with
                      | .vint a, .vint b => some (.ret (.vint (a + b)), st4)
                      | _,       _       => none
                  | some (.exc l p, st4) => some (.exc l p, st4)
                  | none                 => none
              | some (.exc l p, st3) => some (.exc l p, st3)
              | none                 => none
          | some (.exc l p, st2) => some (.exc l p, st2)
          | none                 => none
      | some (.exc l p, st1) => some (.exc l p, st1)
      | none                 => none
  | f+1, st, env, .put e    =>
      match eval f st env e with
      | some (.ret v, st1) =>
          match forceV f st1 v with
          | some (.ret (.vint n), _) => some (.ret (.vint 0), n)
          | some (.ret _, _)         => none
          | some (.exc l p, st2)     => some (.exc l p, st2)
          | none                     => none
      | some (.exc l p, st1) => some (.exc l p, st1)
      | none                 => none
  | f+1, st, env, .perform l argE =>
      match eval f st env argE with
      | some (.ret v, st1) =>
          match forceV f st1 v with
          | some (.ret w, st2)    => some (.exc l w, st2)          -- raise, carrying state
          | some (.exc l' p, st2) => some (.exc l' p, st2)
          | none                  => none
      | some (.exc l' p, st1) => some (.exc l' p, st1)
      | none                  => none
  | f+1, st, env, .handle l onRaise body =>
      match eval f st env body with
      | some (.ret v, st1)    => some (.ret v, st1)
      | some (.exc l' p, st1) => if l' = l then eval f st1 (p :: env) onRaise   -- caught: resume from throw-time state
                                 else some (.exc l' p, st1)                      -- forward
      | none                  => none
/-- Force to WHNF, threading the state; can raise. -/
def forceV : Nat → State → Value → Option (Outcome × State)
  | 0,   _,  _             => none
  | f+1, st, .vthunk e env =>
      match eval f st env e with
      | some (.ret v, st1)   => forceV f st1 v
      | some (.exc l p, st1) => some (.exc l p, st1)
      | none                 => none
  | _+1, st, v             => some (.ret v, st)
end

/-! ## The machine — derived, not designed

`CalcCBNEff`'s `{…,MARK,UNMARK,THROW}` + `CalcCBNSt`'s `{GET,PUT}`, every
instruction threading the state register. The nested APP/FORCE meta-runs return
`(Result × State)`; an escaping `uncaught` is re-thrown at the boundary **carrying
the throw-time state**. The handler frame saves env+stack but **not** state (state
persists — it threads through unwinding rather than being restored). -/

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
  | GET    : Instr
  | PUT    : Instr
  | MARK   : Label → List Instr → Instr
  | UNMARK : Instr
  | THROW  : Label → Instr
deriving Inhabited

abbrev Code := List Instr

structure Frame where
  label : Label
  recovery : Code
  savedEnv : Env
  savedStack : Stack
deriving Inhabited

abbrev HStack := List Frame

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
  | .get,        c => Instr.GET :: c
  | .put e,      c => compile e (Instr.FORCE :: Instr.PUT :: c)
  | .perform l e, c => compile e (Instr.FORCE :: Instr.THROW l :: c)
  | .handle l onRaise body, c =>
      Instr.MARK l (Instr.BIND :: compile onRaise (Instr.UNBIND :: c))
        :: compile body (Instr.UNMARK :: c)

/-- Nearest handler frame catching `l`: recovery + restored config (payload already
pushed), or `uncaught`. Pure — `exec` stays structural. State is threaded by `exec`,
not stored in the frame (persist). -/
def unwindFind : Label → Value → HStack → (Code × Env × Stack × HStack) ⊕ Result
  | l, p, []       => .inr (.uncaught l p)
  | l, p, fr :: hs => if fr.label = l
                      then .inl (fr.recovery, fr.savedEnv, p :: fr.savedStack, hs)
                      else unwindFind l p hs

/-- The machine: value stack + state register + handler stack, fuel-bounded. -/
def exec : Nat → Code → Env → Stack → State → HStack → Option (Result × State)
  | 0,   _,       _,   _, _,  _  => none
  | _+1, [],      _,   s, st, _  => some (.halt s, st)
  | f+1, i :: c,  env, s, st, hs =>
    match i, s with
    | Instr.PUSH n,   s                  => exec f c env (.vint n :: s) st hs
    | Instr.ADD,      (.vint b :: .vint a :: s) => exec f c env (.vint (a + b) :: s) st hs
    | Instr.LOOKUP i, s                  => match env[i]? with
                                            | some v => exec f c env (v :: s) st hs
                                            | none   => none
    | Instr.BIND,     (v :: s)           => exec f c (v :: env) s st hs
    | Instr.UNBIND,   s                  => match env with
                                            | _ :: env' => exec f c env' s st hs
                                            | []        => none
    | Instr.CLOS b,   s                  => exec f c env (.vclo b env :: s) st hs
    | Instr.THUNK e', s                  => exec f c env (.vthunk e' env :: s) st hs
    | Instr.GET,      s                  => exec f c env (.vint st :: s) st hs
    | Instr.PUT,      (.vint n :: s)     => exec f c env (.vint 0 :: s) n hs
    | Instr.APP,      (va :: .vclo b cenv :: s) =>
        match exec f (compile b []) (va :: cenv) [] st [] with
        | some (.halt (rv :: _), st') => exec f c env (rv :: s) st' hs
        | some (.uncaught l p, st')   => match unwindFind l p hs with
                                         | .inl (recov, e', s', hs') => exec f recov e' s' st' hs'
                                         | .inr res                  => some (res, st')
        | _                           => none
    | Instr.FORCE,    (.vthunk body tenv :: s) =>
        match exec f (compile body [Instr.FORCE]) tenv [] st [] with
        | some (.halt (w :: _), st') => exec f c env (w :: s) st' hs
        | some (.uncaught l p, st')  => match unwindFind l p hs with
                                        | .inl (recov, e', s', hs') => exec f recov e' s' st' hs'
                                        | .inr res                  => some (res, st')
        | _                          => none
    | Instr.FORCE,    (v :: s)           => exec f c env (v :: s) st hs
    | Instr.MARK l recov, s              => exec f c env s st (Frame.mk l recov env s :: hs)
    | Instr.UNMARK,   s                  => match hs with
                                            | _ :: hs' => exec f c env s st hs'
                                            | []       => none
    | Instr.THROW l,  (p :: _)           =>
        match unwindFind l p hs with
        | .inl (recov, e', s', hs') => exec f recov e' s' st hs'
        | .inr res                  => some (res, st)
    | _,              _                  => none

/-- `exec`'s `THROW`/re-throw logic, factored for the proof (defeq to the inlined
arms). Threads the throw-time state `st`. -/
def throwExec (f : Nat) (l : Label) (p : Value) (st : State) (hs : HStack) : Option (Result × State) :=
  match unwindFind l p hs with
  | .inl (recov, e', s', hs') => exec f recov e' s' st hs'
  | .inr res                  => some (res, st)

def run (fuel : Nat) (e : Src) : Option (Result × State) := exec fuel (compile e []) [] [] 0 []

def outcomeToResult : Outcome → Result
  | .ret v   => .halt [v]
  | .exc l p => .uncaught l p

/-! ## Correctness — calculated `exec ∘ compile ≡ eval` -/

/-- **Fuel monotonicity (one step).** -/
theorem exec_succ : ∀ (f : Nat) (code : Code) (env : Env) (s : Stack) (st : State) (hs : HStack) (res : Result × State),
    exec f code env s st hs = some res → exec (f + 1) code env s st hs = some res := by
  intro f
  induction f with
  | zero => intro code env s st hs res h; simp [exec] at h
  | succ f ih =>
    intro code env s st hs res h
    cases code with
    | nil => simpa only [exec] using h
    | cons i c =>
      cases i with
      | PUSH n   => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | CLOS b   => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | THUNK e  => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | GET      => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | MARK l rcv => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
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
                | vint _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | LOOKUP j =>
          simp only [exec] at h ⊢
          cases hj : env[j]? with
          | none => rw [hj] at h; simp at h
          | some v => rw [hj] at h; exact ih _ _ _ _ _ _ h
      | BIND =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v s' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | UNBIND =>
          cases env with
          | nil => simp only [exec] at h; simp at h
          | cons _ env' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | PUT =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v s' => cases v with
            | vthunk _ _ => simp only [exec] at h; simp at h
            | vclo _ _ => simp only [exec] at h; simp at h
            | vint n => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | UNMARK =>
          cases hs with
          | nil => simp only [exec] at h; simp at h
          | cons _ hs' => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
      | THROW l =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons p s' =>
              simp only [exec] at h ⊢
              cases hu : unwindFind l p hs with
              | inl x => obtain ⟨recov, e', s'', hs''⟩ := x; rw [hu] at h; exact ih _ _ _ _ _ _ h
              | inr res2 => rw [hu] at h; exact h
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
                  cases hb : exec f (compile body []) (va :: cenv) [] st [] with
                  | none => rw [hb] at h; simp at h
                  | some res2 => obtain ⟨br, st'⟩ := res2; cases br with
                    | halt rs => cases rs with
                      | nil => rw [hb] at h; simp at h
                      | cons rv _ => rw [hb] at h; rw [ih _ _ _ _ _ _ hb]; exact ih _ _ _ _ _ _ h
                    | uncaught l p =>
                        rw [hb] at h; rw [ih _ _ _ _ _ _ hb]
                        simp only [] at h ⊢
                        cases hu : unwindFind l p hs with
                        | inl x => obtain ⟨recov, e', s'', hs''⟩ := x; rw [hu] at h; exact ih _ _ _ _ _ _ h
                        | inr res3 => rw [hu] at h; exact h
      | FORCE =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v0 s' => cases v0 with
            | vint _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
            | vclo _ _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ _ h
            | vthunk body tenv =>
                simp only [exec] at h ⊢
                cases hb : exec f (compile body [Instr.FORCE]) tenv [] st [] with
                | none => rw [hb] at h; simp at h
                | some res2 => obtain ⟨br, st'⟩ := res2; cases br with
                  | halt rs => cases rs with
                    | nil => rw [hb] at h; simp at h
                    | cons w _ => rw [hb] at h; rw [ih _ _ _ _ _ _ hb]; exact ih _ _ _ _ _ _ h
                  | uncaught l p =>
                      rw [hb] at h; rw [ih _ _ _ _ _ _ hb]
                      simp only [] at h ⊢
                      cases hu : unwindFind l p hs with
                      | inl x => obtain ⟨recov, e', s'', hs''⟩ := x; rw [hu] at h; exact ih _ _ _ _ _ _ h
                      | inr res3 => rw [hu] at h; exact h

/-- **Fuel monotonicity.** -/
theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s : Stack) (st : State) (hs : HStack) (res : Result × State)
    (h : exec f code env s st hs = some res) (hle : f ≤ f') : exec f' code env s st hs = some res := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle; clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ _ _ ih

/-- **Throw monotonicity.** -/
theorem throwExec_mono (f f' : Nat) (l : Label) (p : Value) (st : State) (hs : HStack) (res : Result × State)
    (h : throwExec f l p st hs = some res) (hle : f ≤ f') : throwExec f' l p st hs = some res := by
  simp only [throwExec] at h ⊢
  cases hu : unwindFind l p hs with
  | inl x => obtain ⟨recov, e', s', hs'⟩ := x; rw [hu] at h; exact exec_mono _ _ _ _ _ _ _ _ h hle
  | inr res2 => rw [hu] at h; exact h

/-- **The four-part mutual simulation**, with the state register threaded. -/
theorem sim : ∀ (fe : Nat),
    (∀ st env e v st', eval fe st env e = some (.ret v, st') → ∀ c s hs F res,
        exec F c env (v :: s) st' hs = some res → ∃ F', exec F' (compile e c) env s st hs = some res) ∧
    (∀ st env e l p st', eval fe st env e = some (.exc l p, st') → ∀ c s hs F res,
        throwExec F l p st' hs = some res → ∃ F', exec F' (compile e c) env s st hs = some res) ∧
    (∀ st v w st', forceV fe st v = some (.ret w, st') → ∀ env c s hs F res,
        exec F c env (w :: s) st' hs = some res → ∃ F', exec F' (Instr.FORCE :: c) env (v :: s) st hs = some res) ∧
    (∀ st v l p st', forceV fe st v = some (.exc l p, st') → ∀ env c s hs F res,
        throwExec F l p st' hs = some res → ∃ F', exec F' (Instr.FORCE :: c) env (v :: s) st hs = some res) := by
  intro fe
  induction fe with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro st env e v st' h; simp [eval] at h
    · intro st env e l p st' h; simp [eval] at h
    · intro st v w st' h; simp [forceV] at h
    · intro st v l p st' h; simp [forceV] at h
  | succ fe ih =>
    obtain ⟨ihe, ihx, ihf, ihfx⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ============================ eval-ret ============================
      intro st env e
      cases e with
      | val n => intro v st' h c s hs F res hr
                 simp only [eval, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | var i => intro v st' h c s hs F res hr
                 simp only [eval] at h
                 cases hi : env[i]? with
                 | none => simp [hi] at h
                 | some vv =>
                   simp only [hi, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                   exact ⟨F + 1, by simp only [compile, exec, hi]; exact hr⟩
      | lam b => intro v st' h c s hs F res hr
                 simp only [eval, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | thnk e => intro v st' h c s hs F res hr
                  simp only [eval, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | get => intro v st' h c s hs F res hr
               simp only [eval, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
               exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | force e => intro v st' h c s hs F res hr
                   simp only [eval] at h
                   cases he : eval fe st env e with
                   | none => simp [he] at h
                   | some pe => obtain ⟨oe, st1⟩ := pe; cases oe with
                     | exc l p => simp [he] at h
                     | ret v' =>
                       simp only [he] at h
                       obtain ⟨G, hG⟩ := ihf st1 v' v st' h env c s hs F res hr
                       obtain ⟨F', hF'⟩ := ihe st env e v' st1 he (Instr.FORCE :: c) s hs G res hG
                       exact ⟨F', by simpa only [compile] using hF'⟩
      | letE e1 e2 => intro v st' h c s hs F res hr
                      simp only [eval] at h
                      obtain ⟨G2, hG2⟩ := ihe st (.vthunk e1 env :: env) e2 v st' h (Instr.UNBIND :: c) s hs (F + 1) res
                        (by simp only [exec]; exact hr)
                      exact ⟨G2 + 2, by simp only [compile, exec]; exact hG2⟩
      | add x y => intro v st' h c s hs F res hr
                   simp only [eval] at h
                   cases hx : eval fe st env x with
                   | none => simp [hx] at h
                   | some px => obtain ⟨ox, st1⟩ := px; cases ox with
                     | exc l p => simp [hx] at h
                     | ret vx =>
                       simp only [hx] at h
                       cases hfx : forceV fe st1 vx with
                       | none => simp [hfx] at h
                       | some pfx => obtain ⟨ofx, st2⟩ := pfx; cases ofx with
                         | exc l p => simp [hfx] at h
                         | ret wx =>
                           simp only [hfx] at h
                           cases hy : eval fe st2 env y with
                           | none => simp [hy] at h
                           | some py => obtain ⟨oy, st3⟩ := py; cases oy with
                             | exc l p => simp [hy] at h
                             | ret vy =>
                               simp only [hy] at h
                               cases hfy : forceV fe st3 vy with
                               | none => simp [hfy] at h
                               | some pfy => obtain ⟨ofy, st4⟩ := pfy; cases ofy with
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
                                       simp only [Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                                       have hadd : exec (F + 1) (Instr.ADD :: c) env (.vint b :: .vint a :: s) st4 hs = some res := by
                                         simp only [exec]; exact hr
                                       obtain ⟨Gy, hGy⟩ := ihf st3 vy (.vint b) st4 hfy env (Instr.ADD :: c) (.vint a :: s) hs (F + 1) res hadd
                                       obtain ⟨Hy, hHy⟩ := ihe st2 env y vy st3 hy (Instr.FORCE :: Instr.ADD :: c) (.vint a :: s) hs Gy res hGy
                                       obtain ⟨Gx, hGx⟩ := ihf st1 vx (.vint a) st2 hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Hy res hHy
                                       obtain ⟨F', hF'⟩ := ihe st env x vx st1 hx
                                         (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gx res hGx
                                       exact ⟨F', by simpa only [compile] using hF'⟩
      | app g a => intro v st' h c s hs F res hr
                   simp only [eval] at h
                   cases hg : eval fe st env g with
                   | none => simp [hg] at h
                   | some pg => obtain ⟨og, st1⟩ := pg; cases og with
                     | exc l p => simp [hg] at h
                     | ret vg =>
                       simp only [hg] at h
                       cases hfg : forceV fe st1 vg with
                       | none => simp [hfg] at h
                       | some pfg => obtain ⟨ofg, st2⟩ := pfg; cases ofg with
                         | exc l p => simp [hfg] at h
                         | ret wg => cases wg with
                           | vint _ => simp [hfg] at h
                           | vthunk _ _ => simp [hfg] at h
                           | vclo b cenv =>
                             simp only [hfg] at h
                             obtain ⟨G, hG⟩ := ihe st2 (.vthunk a env :: cenv) b v st' h [] [] [] 1 (.halt [v], st') (by simp [exec])
                             have hGbig : exec (G + F) (compile b []) (.vthunk a env :: cenv) [] st2 [] = some (.halt [v], st') :=
                               exec_mono _ (G + F) _ _ _ _ _ _ hG (by omega)
                             have hrbig : exec (G + F) c env (v :: s) st' hs = some res := exec_mono _ (G + F) _ _ _ _ _ _ hr (by omega)
                             have happ : exec (G + F + 1) (Instr.APP :: c) env (.vthunk a env :: .vclo b cenv :: s) st2 hs = some res := by
                               simp only [exec, hGbig]; exact hrbig
                             have hthunk : exec (G + F + 2) (Instr.THUNK a :: Instr.APP :: c) env (.vclo b cenv :: s) st2 hs = some res := by
                               simp only [exec]; exact happ
                             obtain ⟨H, hH⟩ := ihf st1 vg (.vclo b cenv) st2 hfg env (Instr.THUNK a :: Instr.APP :: c) s hs (G + F + 2) res hthunk
                             obtain ⟨F', hF'⟩ := ihe st env g vg st1 hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs H res hH
                             exact ⟨F', by simpa only [compile] using hF'⟩
      | put e => intro v st' h c s hs F res hr
                 simp only [eval] at h
                 cases he : eval fe st env e with
                 | none => simp [he] at h
                 | some pe => obtain ⟨oe, st1⟩ := pe; cases oe with
                   | exc l p => simp [he] at h
                   | ret v' =>
                     simp only [he] at h
                     cases hfe : forceV fe st1 v' with
                     | none => simp [hfe] at h
                     | some pf => obtain ⟨ofe, st2⟩ := pf; cases ofe with
                       | exc l p => simp [hfe] at h
                       | ret w => cases w with
                         | vclo _ _ => simp [hfe] at h
                         | vthunk _ _ => simp [hfe] at h
                         | vint n =>
                           simp only [hfe, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                           have hput : exec (F + 1) (Instr.PUT :: c) env (.vint n :: s) st2 hs = some res := by
                             simp only [exec]; exact hr
                           obtain ⟨G, hG⟩ := ihf st1 v' (.vint n) st2 hfe env (Instr.PUT :: c) s hs (F + 1) res hput
                           obtain ⟨F', hF'⟩ := ihe st env e v' st1 he (Instr.FORCE :: Instr.PUT :: c) s hs G res hG
                           exact ⟨F', by simpa only [compile] using hF'⟩
      | perform lab argE => intro v st' h c s hs F res hr
                            simp only [eval] at h
                            cases ha : eval fe st env argE with
                            | none => simp [ha] at h
                            | some pa => obtain ⟨oa, st1⟩ := pa; cases oa with
                              | exc l p => simp [ha] at h
                              | ret va =>
                                simp only [ha] at h
                                cases hfa : forceV fe st1 va with
                                | none => simp [hfa] at h
                                | some pf => obtain ⟨ofa, st2⟩ := pf; cases ofa with
                                  | exc l p => simp [hfa] at h
                                  | ret w => simp [hfa] at h
      | handle lab onRaise body =>
          intro v st' h c s hs F res hr
          simp only [eval] at h
          cases hb : eval fe st env body with
          | none => simp [hb] at h
          | some pb => obtain ⟨ob, st1⟩ := pb; cases ob with
            | ret w =>
              simp only [hb, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              obtain ⟨Gb, hGb⟩ := ihe st env body w st1 hb (Instr.UNMARK :: c) s
                (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) (F + 1) res
                (by simp only [exec]; exact hr)
              exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
            | exc l' p =>
              simp only [hb] at h
              by_cases hc : l' = lab
              · rw [if_pos hc] at h
                obtain ⟨Go, hGo⟩ := ihe st1 (p :: env) onRaise v st' h (Instr.UNBIND :: c) s hs (F + 1) res
                  (by simp only [exec]; exact hr)
                have hthr : throwExec (Go + 1) l' p st1
                    (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) = some res := by
                  simp only [throwExec, unwindFind]; rw [if_pos hc.symm]; simp only [exec]; exact hGo
                obtain ⟨Gb, hGb⟩ := ihx st env body l' p st1 hb (Instr.UNMARK :: c) s
                  (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) (Go + 1) res hthr
                exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
              · rw [if_neg hc] at h; simp at h
    · -- ============================ eval-exc ============================
      intro st env e
      cases e with
      | val n => intro l p st' h c s hs F res hu; simp [eval] at h
      | var i => intro l p st' h c s hs F res hu
                 simp only [eval] at h
                 cases hi : env[i]? with
                 | none => simp [hi] at h
                 | some vv => simp [hi] at h
      | lam b => intro l p st' h c s hs F res hu; simp [eval] at h
      | thnk e => intro l p st' h c s hs F res hu; simp [eval] at h
      | get => intro l p st' h c s hs F res hu; simp [eval] at h
      | force e => intro l p st' h c s hs F res hu
                   simp only [eval] at h
                   cases he : eval fe st env e with
                   | none => simp [he] at h
                   | some pe => obtain ⟨oe, st1⟩ := pe; cases oe with
                     | exc l' p' =>
                       simp only [he, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                       obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                       have := ihx st env e l' p' st1 he (Instr.FORCE :: c) s hs F res hu
                       simpa only [compile] using this
                     | ret v' =>
                       simp only [he] at h
                       obtain ⟨G, hG⟩ := ihfx st1 v' l p st' h env c s hs F res hu
                       obtain ⟨F', hF'⟩ := ihe st env e v' st1 he (Instr.FORCE :: c) s hs G res hG
                       exact ⟨F', by simpa only [compile] using hF'⟩
      | letE e1 e2 => intro l p st' h c s hs F res hu
                      simp only [eval] at h
                      obtain ⟨G2, hG2⟩ := ihx st (.vthunk e1 env :: env) e2 l p st' h (Instr.UNBIND :: c) s hs F res hu
                      exact ⟨G2 + 2, by simp only [compile, exec]; exact hG2⟩
      | add x y => intro l p st' h c s hs F res hu
                   simp only [eval] at h
                   cases hx : eval fe st env x with
                   | none => simp [hx] at h
                   | some px => obtain ⟨ox, st1⟩ := px; cases ox with
                     | exc lx px2 =>
                       simp only [hx, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                       obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                       have := ihx st env x lx px2 st1 hx (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs F res hu
                       simpa only [compile] using this
                     | ret vx =>
                       simp only [hx] at h
                       cases hfx : forceV fe st1 vx with
                       | none => simp [hfx] at h
                       | some pfx => obtain ⟨ofx, st2⟩ := pfx; cases ofx with
                         | exc lx px2 =>
                           simp only [hfx, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                           obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                           obtain ⟨G, hG⟩ := ihfx st1 vx lx px2 st2 hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs F res hu
                           obtain ⟨F', hF'⟩ := ihe st env x vx st1 hx
                             (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs G res hG
                           exact ⟨F', by simpa only [compile] using hF'⟩
                         | ret wx =>
                           simp only [hfx] at h
                           cases hy : eval fe st2 env y with
                           | none => simp [hy] at h
                           | some py => obtain ⟨oy, st3⟩ := py; cases oy with
                             | exc ly py2 =>
                               simp only [hy, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                               obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                               obtain ⟨Gy, hGy⟩ := ihx st2 env y ly py2 st3 hy (Instr.FORCE :: Instr.ADD :: c) (wx :: s) hs F res hu
                               obtain ⟨Gx, hGx⟩ := ihf st1 vx wx st2 hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gy res hGy
                               obtain ⟨F', hF'⟩ := ihe st env x vx st1 hx
                                 (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gx res hGx
                               exact ⟨F', by simpa only [compile] using hF'⟩
                             | ret vy =>
                               simp only [hy] at h
                               cases hfy : forceV fe st3 vy with
                               | none => simp [hfy] at h
                               | some pfy => obtain ⟨ofy, st4⟩ := pfy; cases ofy with
                                 | exc ly py2 =>
                                   simp only [hfy, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                                   obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                                   obtain ⟨Gy, hGy⟩ := ihfx st3 vy ly py2 st4 hfy env (Instr.ADD :: c) (wx :: s) hs F res hu
                                   obtain ⟨Hy, hHy⟩ := ihe st2 env y vy st3 hy (Instr.FORCE :: Instr.ADD :: c) (wx :: s) hs Gy res hGy
                                   obtain ⟨Gx, hGx⟩ := ihf st1 vx wx st2 hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Hy res hHy
                                   obtain ⟨F', hF'⟩ := ihe st env x vx st1 hx
                                     (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s hs Gx res hGx
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
      | app g a => intro l p st' h c s hs F res hu
                   simp only [eval] at h
                   cases hg : eval fe st env g with
                   | none => simp [hg] at h
                   | some pg => obtain ⟨og, st1⟩ := pg; cases og with
                     | exc lg pg2 =>
                       simp only [hg, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                       obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                       have := ihx st env g lg pg2 st1 hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs F res hu
                       simpa only [compile] using this
                     | ret vg =>
                       simp only [hg] at h
                       cases hfg : forceV fe st1 vg with
                       | none => simp [hfg] at h
                       | some pfg => obtain ⟨ofg, st2⟩ := pfg; cases ofg with
                         | exc lf pf2 =>
                           simp only [hfg, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                           obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                           obtain ⟨G, hG⟩ := ihfx st1 vg lf pf2 st2 hfg env (Instr.THUNK a :: Instr.APP :: c) s hs F res hu
                           obtain ⟨F', hF'⟩ := ihe st env g vg st1 hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs G res hG
                           exact ⟨F', by simpa only [compile] using hF'⟩
                         | ret wg => cases wg with
                           | vint _ => simp [hfg] at h
                           | vthunk _ _ => simp [hfg] at h
                           | vclo b cenv =>
                             simp only [hfg] at h
                             obtain ⟨G, hG⟩ := ihx st2 (.vthunk a env :: cenv) b l p st' h [] [] [] 0 (.uncaught l p, st')
                               (by simp [throwExec, unwindFind])
                             have hGbig : exec (G + F) (compile b []) (.vthunk a env :: cenv) [] st2 [] = some (.uncaught l p, st') :=
                               exec_mono _ (G + F) _ _ _ _ _ _ hG (by omega)
                             have huF : throwExec (G + F) l p st' hs = some res := throwExec_mono F (G + F) l p st' hs res hu (by omega)
                             have happ : exec (G + F + 1) (Instr.APP :: c) env (.vthunk a env :: .vclo b cenv :: s) st2 hs = some res := by
                               simp only [exec, hGbig]; exact huF
                             have hthunk : exec (G + F + 2) (Instr.THUNK a :: Instr.APP :: c) env (.vclo b cenv :: s) st2 hs = some res := by
                               simp only [exec]; exact happ
                             obtain ⟨H, hH⟩ := ihf st1 vg (.vclo b cenv) st2 hfg env (Instr.THUNK a :: Instr.APP :: c) s hs (G + F + 2) res hthunk
                             obtain ⟨F', hF'⟩ := ihe st env g vg st1 hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s hs H res hH
                             exact ⟨F', by simpa only [compile] using hF'⟩
      | put e => intro l p st' h c s hs F res hu
                 simp only [eval] at h
                 cases he : eval fe st env e with
                 | none => simp [he] at h
                 | some pe => obtain ⟨oe, st1⟩ := pe; cases oe with
                   | exc l' p' =>
                     simp only [he, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                     obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                     have := ihx st env e l' p' st1 he (Instr.FORCE :: Instr.PUT :: c) s hs F res hu
                     simpa only [compile] using this
                   | ret v' =>
                     simp only [he] at h
                     cases hfe : forceV fe st1 v' with
                     | none => simp [hfe] at h
                     | some pf => obtain ⟨ofe, st2⟩ := pf; cases ofe with
                       | exc l' p' =>
                         simp only [hfe, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                         obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                         obtain ⟨G, hG⟩ := ihfx st1 v' l' p' st2 hfe env (Instr.PUT :: c) s hs F res hu
                         obtain ⟨F', hF'⟩ := ihe st env e v' st1 he (Instr.FORCE :: Instr.PUT :: c) s hs G res hG
                         exact ⟨F', by simpa only [compile] using hF'⟩
                       | ret w => cases w with
                         | vclo _ _ => simp [hfe] at h
                         | vthunk _ _ => simp [hfe] at h
                         | vint n => simp [hfe] at h
      | perform lab argE =>
          intro l p st' h c s hs F res hu
          simp only [eval] at h
          cases ha : eval fe st env argE with
          | none => simp [ha] at h
          | some pa => obtain ⟨oa, st1⟩ := pa; cases oa with
            | exc l' p' =>
              simp only [ha, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              have := ihx st env argE l' p' st1 ha (Instr.FORCE :: Instr.THROW lab :: c) s hs F res hu
              simpa only [compile] using this
            | ret va =>
              simp only [ha] at h
              cases hfa : forceV fe st1 va with
              | none => simp [hfa] at h
              | some pf => obtain ⟨ofa, st2⟩ := pf; cases ofa with
                | exc l' p' =>
                  simp only [hfa, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                  obtain ⟨G, hG⟩ := ihfx st1 va l' p' st2 hfa env (Instr.THROW lab :: c) s hs F res hu
                  obtain ⟨F', hF'⟩ := ihe st env argE va st1 ha (Instr.FORCE :: Instr.THROW lab :: c) s hs G res hG
                  exact ⟨F', by simpa only [compile] using hF'⟩
                | ret w =>
                  simp only [hfa, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                  obtain ⟨⟨hl, hp⟩, hst⟩ := h; subst l; subst p; subst st'
                  have hthrow : exec (F + 1) (Instr.THROW lab :: c) env (w :: s) st2 hs = some res := by
                    simp only [exec]; exact hu
                  obtain ⟨G, hG⟩ := ihf st1 va w st2 hfa env (Instr.THROW lab :: c) s hs (F + 1) res hthrow
                  obtain ⟨F', hF'⟩ := ihe st env argE va st1 ha (Instr.FORCE :: Instr.THROW lab :: c) s hs G res hG
                  exact ⟨F', by simpa only [compile] using hF'⟩
      | handle lab onRaise body =>
          intro l p st' h c s hs F res hu
          simp only [eval] at h
          cases hb : eval fe st env body with
          | none => simp [hb] at h
          | some pb => obtain ⟨ob, st1⟩ := pb; cases ob with
            | ret w => simp [hb] at h
            | exc l' p' =>
              simp only [hb] at h
              by_cases hc : l' = lab
              · rw [if_pos hc] at h
                obtain ⟨Go, hGo⟩ := ihx st1 (p' :: env) onRaise l p st' h (Instr.UNBIND :: c) s hs F res hu
                have hthr : throwExec (Go + 1) l' p' st1
                    (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) = some res := by
                  simp only [throwExec, unwindFind]; rw [if_pos hc.symm]; simp only [exec]; exact hGo
                obtain ⟨Gb, hGb⟩ := ihx st env body l' p' st1 hb (Instr.UNMARK :: c) s
                  (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) (Go + 1) res hthr
                exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
              · rw [if_neg hc] at h
                simp only [Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                have hthr : throwExec F l' p' st1
                    (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) = some res := by
                  simp only [throwExec, unwindFind]; rw [if_neg (Ne.symm hc)]; exact hu
                obtain ⟨Gb, hGb⟩ := ihx st env body l' p' st1 hb (Instr.UNMARK :: c) s
                  (Frame.mk lab (Instr.BIND :: compile onRaise (Instr.UNBIND :: c)) env s :: hs) F res hthr
                exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
    · -- ============================ forceV-ret ============================
      intro st v w st' h env c s hs F res hr
      cases v with
      | vint n => simp only [forceV, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vclo b ve => simp only [forceV, Option.some.injEq, Prod.mk.injEq, Outcome.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                     exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vthunk e ve =>
        simp only [forceV] at h
        cases he : eval fe st ve e with
        | none => simp [he] at h
        | some pe => obtain ⟨oe, st1⟩ := pe; cases oe with
          | exc l p => simp [he] at h
          | ret v' =>
            simp only [he] at h
            obtain ⟨A, hA⟩ := ihf st1 v' w st' h ve [] [] [] 1 (.halt [w], st') (by simp [exec])
            obtain ⟨B, hB⟩ := ihe st ve e v' st1 he [Instr.FORCE] [] [] A (.halt [w], st') hA
            have hBbig : exec (B + F) (compile e [Instr.FORCE]) ve [] st [] = some (.halt [w], st') :=
              exec_mono _ (B + F) _ _ _ _ _ _ hB (by omega)
            have hrbig : exec (B + F) c env (w :: s) st' hs = some res := exec_mono _ (B + F) _ _ _ _ _ _ hr (by omega)
            exact ⟨B + F + 1, by simp only [exec, hBbig]; exact hrbig⟩
    · -- ============================ forceV-exc ============================
      intro st v l p st' h env c s hs F res hu
      cases v with
      | vint n => simp [forceV] at h
      | vclo b ve => simp [forceV] at h
      | vthunk e ve =>
        simp only [forceV] at h
        cases he : eval fe st ve e with
        | none => simp [he] at h
        | some pe => obtain ⟨oe, st1⟩ := pe; cases oe with
          | exc l' p' =>
            simp only [he, Option.some.injEq, Prod.mk.injEq, Outcome.exc.injEq] at h
            obtain ⟨⟨e1, e2⟩, e3⟩ := h; subst l'; subst p'; subst st1
            obtain ⟨G, hG⟩ := ihx st ve e l p st' he [Instr.FORCE] [] [] 0 (.uncaught l p, st') (by simp [throwExec, unwindFind])
            have hGbig : exec (G + F) (compile e [Instr.FORCE]) ve [] st [] = some (.uncaught l p, st') :=
              exec_mono _ (G + F) _ _ _ _ _ _ hG (by omega)
            have huF : throwExec (G + F) l p st' hs = some res := throwExec_mono F (G + F) l p st' hs res hu (by omega)
            exact ⟨G + F + 1, by simp only [exec, hGbig]; exact huF⟩
          | ret v' =>
            simp only [he] at h
            obtain ⟨A, hA⟩ := ihfx st1 v' l p st' h ve [] [] [] 0 (.uncaught l p, st') (by simp [throwExec, unwindFind])
            obtain ⟨G, hG⟩ := ihe st ve e v' st1 he [Instr.FORCE] [] [] A (.uncaught l p, st') hA
            have hGbig : exec (G + F) (compile e [Instr.FORCE]) ve [] st [] = some (.uncaught l p, st') :=
              exec_mono _ (G + F) _ _ _ _ _ _ hG (by omega)
            have huF : throwExec (G + F) l p st' hs = some res := throwExec_mono F (G + F) l p st' hs res hu (by omega)
            exact ⟨G + F + 1, by simp only [exec, hGbig]; exact huF⟩

/-- **Correctness of the calculated CBN + Throws + State machine.** -/
theorem compile_correct (fe : Nat) (e : Src) (o : Outcome) (st' : State)
    (h : eval fe 0 [] e = some (o, st')) : ∃ F, run F e = some (outcomeToResult o, st') := by
  cases o with
  | ret v =>
    obtain ⟨F, hF⟩ := (sim fe).1 0 [] e v st' h [] [] [] 1 (.halt [v], st') (by simp [exec])
    exact ⟨F, by simpa only [run, outcomeToResult] using hF⟩
  | exc l p =>
    obtain ⟨F, hF⟩ := (sim fe).2.1 0 [] e l p st' h [] [] [] 1 (.uncaught l p, st')
      (by simp [throwExec, unwindFind])
    exact ⟨F, by simpa only [run, outcomeToResult] using hF⟩

end Bang.CalcCBNEffSt
