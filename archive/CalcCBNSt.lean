/-!
# K3 composition: State over the closure/CBN core — calculated

The second composition (after `CalcCBNEff`'s Throws; roadmap K3, ADR-0013): fuse
**State** (`get`/`put`/`runState`) into the **call-by-name closure/thunk core**.
This is Bahr–Hutton's "swap to the State monad" applied to `CalcCBN`: its
evaluation monad `Maybe` (`Option`, the fuel device) is composed with the State
monad, giving `eval : Nat → State → Env → Src → Option (Value × State)` and
`forceV : Nat → State → Value → Option (Value × State)` — **forcing threads the
state** (forcing a thunk runs a computation that may `get`/`put`).

The contrast with `CalcCBNEff` (and the reason this confirms the composition
doesn't *yet* force a machine flatten): State **resumes** — `get`/`put` continue
in tail position, the register just threads. So unlike a zero-shot `raise` (which
abandons its continuation and needs the empty-nested + re-throw trick), State
threads **cleanly** through `CalcCBN`'s nested meta-runs: a called function / a
forced thunk takes the current state in and hands a new state out, which the
caller threads forward. No unwinding, no re-throw.

State model (single `Int` register, from `CalcSt`/ADR-0011): `get` reads it,
`put` forces its arg to an int and sets it, `runState init body` **localises** the
register — body runs from `init`, and the outer register (the value after
evaluating `init`) is restored on exit (`ENTER`/`LEAVE` bracket it, saving the
outer state on the value stack). `put`/`runState init` are forcing points (the
state is an `Int`, so the arg is forced to a `vint`).

Scope: arithmetic uses `add` only (`mul` is a verbatim duplicate; ADR-0009). The
proof is **CalcCBN's two-part mutual `eval`/`forceV` simulation with the state
register threaded through**, plus the `get`/`put`/`runState` cases.
-/

namespace Bang.CalcCBNSt

abbrev State := Int

/-! ## Source, values, and the call-by-name + state semantics -/

/-- de Bruijn source: the CBN core (`CalcCBN`) plus `get`/`put`/`runState`. -/
inductive Src where
  | val      : Int → Src
  | add      : Src → Src → Src
  | var      : Nat → Src
  | lam      : Src → Src
  | app      : Src → Src → Src
  | letE     : Src → Src → Src
  | thnk     : Src → Src
  | force    : Src → Src
  | get      : Src                 -- read the state
  | put      : Src → Src           -- set the state to the (forced int) value of the arg; returns 0
  | runState : Src → Src → Src     -- runState init body: run body with a local state cell = init
deriving Repr, Inhabited

/-- WHNF values: ints, source-closures, source-thunks. Shared between `eval` and
the machine. -/
inductive Value where
  | vint   : Int → Value
  | vclo   : Src → List Value → Value
  | vthunk : Src → List Value → Value
deriving Inhabited

abbrev Env   := List Value
abbrev Stack := List Value

/- Call-by-name + state, fuel-bounded, threading a state register. `eval st env e`
returns `(value, newState)`. Bindings hold descriptions (`let`/app arg/`thnk`);
forcing points (`force`, both `add` operands, the app function, a `put`/`runState`
arg) reduce to WHNF via `forceV` and thread the state. Structural on fuel. -/
mutual
def eval : Nat → State → Env → Src → Option (Value × State)
  | 0,   _,  _,   _         => none
  | _+1, st, _,   .val n    => some (.vint n, st)
  | _+1, st, env, .var i    => match env[i]? with | some v => some (v, st) | none => none
  | _+1, st, env, .lam b    => some (.vclo b env, st)
  | _+1, st, env, .thnk e   => some (.vthunk e env, st)
  | f+1, st, env, .force e  =>
      match eval f st env e with
      | some (v, st1) => forceV f st1 v
      | none          => none
  | f+1, st, env, .letE e1 e2 => eval f st (.vthunk e1 env :: env) e2
  | f+1, st, env, .app g a  =>
      match eval f st env g with
      | some (vg, st1) =>
          match forceV f st1 vg with
          | some (.vclo b cenv, st2) => eval f st2 (.vthunk a env :: cenv) b
          | some (_, _)              => none
          | none                     => none
      | none => none
  | f+1, st, env, .add x y  =>
      match eval f st env x with
      | some (vx, st1) =>
          match forceV f st1 vx with
          | some (wx, st2) =>
              match eval f st2 env y with
              | some (vy, st3) =>
                  match forceV f st3 vy with
                  | some (wy, st4) =>
                      match wx, wy with
                      | .vint a, .vint b => some (.vint (a + b), st4)
                      | _,       _       => none
                  | none => none
              | none => none
          | none => none
      | none => none
  | _+1, st, _,   .get      => some (.vint st, st)
  | f+1, st, env, .put e    =>
      match eval f st env e with
      | some (v, st1) =>
          match forceV f st1 v with
          | some (.vint n, _) => some (.vint 0, n)        -- state := n, result unit (0)
          | some (_, _)       => none
          | none              => none
      | none => none
  | f+1, st, env, .runState init body =>
      match eval f st env init with
      | some (vi, st1) =>
          match forceV f st1 vi with
          | some (.vint i, st2) =>
              match eval f i env body with               -- body runs from state i
              | some (vb, _) => some (vb, st2)           -- body's value; outer state st2 restored
              | none         => none
          | some (_, _) => none
          | none        => none
      | none => none
/-- Force to WHNF (chase the thunk chain), threading the state. -/
def forceV : Nat → State → Value → Option (Value × State)
  | 0,   _,  _             => none
  | f+1, st, .vthunk e env =>
      match eval f st env e with
      | some (v, st1) => forceV f st1 v
      | none          => none
  | _+1, st, v             => some (v, st)
end

/-! ## The machine — derived, not designed

`CalcCBN`'s `{PUSH,ADD,LOOKUP,BIND,UNBIND,CLOS,APP,THUNK,FORCE}` plus `CalcSt`'s
`{GET,PUT,ENTER,LEAVE}`. Every instruction threads the state register; the nested
APP/FORCE meta-runs take the current state in and hand a new state out (State
resumes — no re-throw). `ENTER`/`LEAVE` save/restore the outer state on the value
stack (boxed as a `vint`) to localise `runState`. -/

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
  | GET    : Instr                 -- push the current state (as a vint)
  | PUT    : Instr                 -- pop vint n, set state := n, push 0
  | ENTER  : Instr                 -- pop vint i, save the current state (vint) on the stack, set state := i
  | LEAVE  : Instr                 -- pop v and the saved vint st1, restore state := st1, push v
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
  | .get,        c => Instr.GET :: c
  | .put e,      c => compile e (Instr.FORCE :: Instr.PUT :: c)
  | .runState i b, c => compile i (Instr.FORCE :: Instr.ENTER :: compile b (Instr.LEAVE :: c))

/-- The machine: a value stack + a state register, fuel-bounded. Structurally
recursive on fuel. -/
def exec : Nat → Code → Env → Stack → State → Option (Stack × State)
  | 0,   _,       _,   _, _  => none
  | _+1, [],      _,   s, st => some (s, st)
  | f+1, i :: c,  env, s, st =>
    match i, s with
    | Instr.PUSH n,   s                  => exec f c env (.vint n :: s) st
    | Instr.ADD,      (.vint b :: .vint a :: s) => exec f c env (.vint (a + b) :: s) st
    | Instr.LOOKUP i, s                  => match env[i]? with
                                            | some v => exec f c env (v :: s) st
                                            | none   => none
    | Instr.BIND,     (v :: s)           => exec f c (v :: env) s st
    | Instr.UNBIND,   s                  => match env with
                                            | _ :: env' => exec f c env' s st
                                            | []        => none
    | Instr.CLOS b,   s                  => exec f c env (.vclo b env :: s) st
    | Instr.THUNK e', s                  => exec f c env (.vthunk e' env :: s) st
    | Instr.APP,      (va :: .vclo b cenv :: s) =>
        match exec f (compile b []) (va :: cenv) [] st with
        | some (rv :: _, st') => exec f c env (rv :: s) st'
        | _                   => none
    | Instr.FORCE,    (.vthunk body tenv :: s) =>
        match exec f (compile body [Instr.FORCE]) tenv [] st with
        | some (w :: _, st') => exec f c env (w :: s) st'
        | _                  => none
    | Instr.FORCE,    (v :: s)           => exec f c env (v :: s) st   -- already WHNF
    | Instr.GET,      s                  => exec f c env (.vint st :: s) st
    | Instr.PUT,      (.vint n :: s)     => exec f c env (.vint 0 :: s) n
    | Instr.ENTER,    (.vint i :: s)     => exec f c env (.vint st :: s) i
    | Instr.LEAVE,    (v :: .vint st1 :: s) => exec f c env (v :: s) st1
    | _,              _                  => none                       -- stuck

/-- Run a closed program: empty env/stack, initial state `0`. -/
def run (fuel : Nat) (e : Src) : Option (Stack × State) := exec fuel (compile e []) [] [] 0

/-! ## Correctness — calculated `exec ∘ compile ≡ eval`

`CalcCBN`'s two-part mutual `eval`/`forceV` simulation (no `exc` part — State never
raises) with the **state register threaded** through every step and the
`get`/`put`/`runState` cases added. -/

/-- **Fuel monotonicity (one step).** -/
theorem exec_succ : ∀ (f : Nat) (code : Code) (env : Env) (s : Stack) (st : State) (res : Stack × State),
    exec f code env s st = some res → exec (f + 1) code env s st = some res := by
  intro f
  induction f with
  | zero => intro code env s st res h; simp [exec] at h
  | succ f ih =>
    intro code env s st res h
    cases code with
    | nil => simpa only [exec] using h
    | cons i c =>
      cases i with
      | PUSH n   => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | CLOS b   => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | THUNK e  => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | GET      => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
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
      | PUT =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v s' => cases v with
            | vthunk _ _ => simp only [exec] at h; simp at h
            | vclo _ _ => simp only [exec] at h; simp at h
            | vint n => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | ENTER =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v s' => cases v with
            | vthunk _ _ => simp only [exec] at h; simp at h
            | vclo _ _ => simp only [exec] at h; simp at h
            | vint i => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | LEAVE =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v s' => cases s' with
            | nil => simp only [exec] at h; simp at h
            | cons v2 s'' => cases v2 with
              | vthunk _ _ => simp only [exec] at h; simp at h
              | vclo _ _ => simp only [exec] at h; simp at h
              | vint st1 => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
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
                  cases hb : exec f (compile body []) (va :: cenv) [] st with
                  | none => rw [hb] at h; simp at h
                  | some res2 => obtain ⟨bs, st'⟩ := res2; cases bs with
                    | nil => rw [hb] at h; simp at h
                    | cons rv _ => rw [hb] at h; rw [ih _ _ _ _ _ hb]; exact ih _ _ _ _ _ h
      | FORCE =>
          cases s with
          | nil => simp only [exec] at h; simp at h
          | cons v0 s' => cases v0 with
            | vint _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
            | vclo _ _ => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
            | vthunk body tenv =>
                simp only [exec] at h ⊢
                cases hb : exec f (compile body [Instr.FORCE]) tenv [] st with
                | none => rw [hb] at h; simp at h
                | some res2 => obtain ⟨bs, st'⟩ := res2; cases bs with
                  | nil => rw [hb] at h; simp at h
                  | cons w _ => rw [hb] at h; rw [ih _ _ _ _ _ hb]; exact ih _ _ _ _ _ h

/-- **Fuel monotonicity.** -/
theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s : Stack) (st : State) (res : Stack × State)
    (h : exec f code env s st = some res) (hle : f ≤ f') : exec f' code env s st = some res := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle; clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ _ ih

/-- **The two-part mutual simulation**, by induction on fuel: eval-sim and
forceV-sim, with the state register threaded. -/
theorem sim : ∀ (fe : Nat),
    (∀ st env e v st', eval fe st env e = some (v, st') → ∀ c s F res,
        exec F c env (v :: s) st' = some res → ∃ F', exec F' (compile e c) env s st = some res) ∧
    (∀ st v w st', forceV fe st v = some (w, st') → ∀ env c s F res,
        exec F c env (w :: s) st' = some res → ∃ F', exec F' (Instr.FORCE :: c) env (v :: s) st = some res) := by
  intro fe
  induction fe with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro st env e v st' h; simp [eval] at h
    · intro st v w st' h; simp [forceV] at h
  | succ fe ih =>
    obtain ⟨ihe, ihf⟩ := ih
    refine ⟨?_, ?_⟩
    · -- ============================ eval-sim ============================
      intro st env e
      cases e with
      | val n => intro v st' h c s F res hr
                 simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | var i => intro v st' h c s F res hr
                 simp only [eval] at h
                 cases hi : env[i]? with
                 | none => simp [hi] at h
                 | some vv =>
                   simp only [hi, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                   exact ⟨F + 1, by simp only [compile, exec, hi]; exact hr⟩
      | lam b => intro v st' h c s F res hr
                 simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | thnk e => intro v st' h c s F res hr
                  simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | get => intro v st' h c s F res hr
               simp only [eval, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
               exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | force e => intro v st' h c s F res hr
                   simp only [eval] at h
                   cases he : eval fe st env e with
                   | none => simp [he] at h
                   | some p =>
                     obtain ⟨v', st1⟩ := p; simp only [he] at h
                     obtain ⟨G, hG⟩ := ihf st1 v' v st' h env c s F res hr
                     obtain ⟨F', hF'⟩ := ihe st env e v' st1 he (Instr.FORCE :: c) s G res hG
                     exact ⟨F', by simpa only [compile] using hF'⟩
      | letE e1 e2 => intro v st' h c s F res hr
                      simp only [eval] at h
                      obtain ⟨G2, hG2⟩ := ihe st (.vthunk e1 env :: env) e2 v st' h (Instr.UNBIND :: c) s (F + 1) res
                        (by simp only [exec]; exact hr)
                      exact ⟨G2 + 2, by simp only [compile, exec]; exact hG2⟩
      | add x y => intro v st' h c s F res hr
                   simp only [eval] at h
                   cases hx : eval fe st env x with
                   | none => simp [hx] at h
                   | some px =>
                     obtain ⟨vx, st1⟩ := px; simp only [hx] at h
                     cases hfx : forceV fe st1 vx with
                     | none => simp [hfx] at h
                     | some pfx =>
                       obtain ⟨wx, st2⟩ := pfx; simp only [hfx] at h
                       cases hy : eval fe st2 env y with
                       | none => simp [hy] at h
                       | some py =>
                         obtain ⟨vy, st3⟩ := py; simp only [hy] at h
                         cases hfy : forceV fe st3 vy with
                         | none => simp [hfy] at h
                         | some pfy =>
                           obtain ⟨wy, st4⟩ := pfy; simp only [hfy] at h
                           cases wx with
                           | vclo _ _ => simp at h
                           | vthunk _ _ => simp at h
                           | vint a => cases wy with
                             | vclo _ _ => simp at h
                             | vthunk _ _ => simp at h
                             | vint b =>
                               simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                               have hadd : exec (F + 1) (Instr.ADD :: c) env (.vint b :: .vint a :: s) st4 = some res := by
                                 simp only [exec]; exact hr
                               obtain ⟨Gy, hGy⟩ := ihf st3 vy (.vint b) st4 hfy env (Instr.ADD :: c) (.vint a :: s) (F + 1) res hadd
                               obtain ⟨Hy, hHy⟩ := ihe st2 env y vy st3 hy (Instr.FORCE :: Instr.ADD :: c) (.vint a :: s) Gy res hGy
                               obtain ⟨Gx, hGx⟩ := ihf st1 vx (.vint a) st2 hfx env (compile y (Instr.FORCE :: Instr.ADD :: c)) s Hy res hHy
                               obtain ⟨F', hF'⟩ := ihe st env x vx st1 hx
                                 (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s Gx res hGx
                               exact ⟨F', by simpa only [compile] using hF'⟩
      | app g a => intro v st' h c s F res hr
                   simp only [eval] at h
                   cases hg : eval fe st env g with
                   | none => simp [hg] at h
                   | some pg =>
                     obtain ⟨vg, st1⟩ := pg; simp only [hg] at h
                     cases hfg : forceV fe st1 vg with
                     | none => simp [hfg] at h
                     | some pfg =>
                       obtain ⟨wg, st2⟩ := pfg; simp only [hfg] at h
                       cases wg with
                       | vint _ => simp at h
                       | vthunk _ _ => simp at h
                       | vclo b cenv =>
                         obtain ⟨G, hG⟩ := ihe st2 (.vthunk a env :: cenv) b v st' h [] [] 1 ([v], st') (by simp [exec])
                         have hGbig : exec (G + F) (compile b []) (.vthunk a env :: cenv) [] st2 = some ([v], st') :=
                           exec_mono _ (G + F) _ _ _ _ _ hG (by omega)
                         have hrbig : exec (G + F) c env (v :: s) st' = some res := exec_mono _ (G + F) _ _ _ _ _ hr (by omega)
                         have happ : exec (G + F + 1) (Instr.APP :: c) env (.vthunk a env :: .vclo b cenv :: s) st2 = some res := by
                           simp only [exec, hGbig]; exact hrbig
                         have hthunk : exec (G + F + 2) (Instr.THUNK a :: Instr.APP :: c) env (.vclo b cenv :: s) st2 = some res := by
                           simp only [exec]; exact happ
                         obtain ⟨H, hH⟩ := ihf st1 vg (.vclo b cenv) st2 hfg env (Instr.THUNK a :: Instr.APP :: c) s (G + F + 2) res hthunk
                         obtain ⟨F', hF'⟩ := ihe st env g vg st1 hg (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s H res hH
                         exact ⟨F', by simpa only [compile] using hF'⟩
      | put e => intro v st' h c s F res hr
                 simp only [eval] at h
                 cases he : eval fe st env e with
                 | none => simp [he] at h
                 | some p =>
                   obtain ⟨v', st1⟩ := p; simp only [he] at h
                   cases hfe : forceV fe st1 v' with
                   | none => simp [hfe] at h
                   | some pf =>
                     obtain ⟨w, st2⟩ := pf; simp only [hfe] at h
                     cases w with
                     | vclo _ _ => simp at h
                     | vthunk _ _ => simp at h
                     | vint n =>
                       simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                       have hput : exec (F + 1) (Instr.PUT :: c) env (.vint n :: s) st2 = some res := by
                         simp only [exec]; exact hr
                       obtain ⟨G, hG⟩ := ihf st1 v' (.vint n) st2 hfe env (Instr.PUT :: c) s (F + 1) res hput
                       obtain ⟨F', hF'⟩ := ihe st env e v' st1 he (Instr.FORCE :: Instr.PUT :: c) s G res hG
                       exact ⟨F', by simpa only [compile] using hF'⟩
      | runState init body =>
          intro v st' h c s F res hr
          simp only [eval] at h
          cases hi : eval fe st env init with
          | none => simp [hi] at h
          | some pi =>
            obtain ⟨vi, st1⟩ := pi; simp only [hi] at h
            cases hfi : forceV fe st1 vi with
            | none => simp [hfi] at h
            | some pfi =>
              obtain ⟨wi, st2⟩ := pfi; simp only [hfi] at h
              cases wi with
              | vclo _ _ => simp at h
              | vthunk _ _ => simp at h
              | vint i =>
                cases hb : eval fe i env body with
                | none => simp [hb] at h
                | some pb =>
                  obtain ⟨vb, stb⟩ := pb; simp only [hb] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  have hleave : exec (F + 1) (Instr.LEAVE :: c) env (vb :: .vint st2 :: s) stb = some res := by
                    simp only [exec]; exact hr
                  obtain ⟨Gb, hGb⟩ := ihe i env body vb stb hb (Instr.LEAVE :: c) (.vint st2 :: s) (F + 1) res hleave
                  have henter : exec (Gb + 1) (Instr.ENTER :: compile body (Instr.LEAVE :: c)) env (.vint i :: s) st2 = some res := by
                    simp only [exec]; exact hGb
                  obtain ⟨H, hH⟩ := ihf st1 vi (.vint i) st2 hfi env
                    (Instr.ENTER :: compile body (Instr.LEAVE :: c)) s (Gb + 1) res henter
                  obtain ⟨F', hF'⟩ := ihe st env init vi st1 hi
                    (Instr.FORCE :: Instr.ENTER :: compile body (Instr.LEAVE :: c)) s H res hH
                  exact ⟨F', by simpa only [compile] using hF'⟩
    · -- ============================ forceV-sim ============================
      intro st v w st' h env c s F res hr
      cases v with
      | vint n => simp only [forceV, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vclo b ve => simp only [forceV, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                     exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vthunk e ve =>
        simp only [forceV] at h
        cases he : eval fe st ve e with
        | none => simp [he] at h
        | some p =>
          obtain ⟨v', st1⟩ := p; simp only [he] at h
          obtain ⟨A, hA⟩ := ihf st1 v' w st' h ve [] [] 1 ([w], st') (by simp [exec])
          obtain ⟨B, hB⟩ := ihe st ve e v' st1 he [Instr.FORCE] [] A ([w], st') hA
          have hBbig : exec (B + F) (compile e [Instr.FORCE]) ve [] st = some ([w], st') :=
            exec_mono _ (B + F) _ _ _ _ _ hB (by omega)
          have hrbig : exec (B + F) c env (w :: s) st' = some res := exec_mono _ (B + F) _ _ _ _ _ hr (by omega)
          exact ⟨B + F + 1, by simp only [exec, hBbig]; exact hrbig⟩

/-- **Correctness of the calculated CBN+State machine.** If `eval` produces
`(v, st')`, the compiled program (with enough fuel) halts on `[v]` with final
state `st'`. -/
theorem compile_correct (fe : Nat) (e : Src) (v : Value) (st' : State)
    (h : eval fe 0 [] e = some (v, st')) : ∃ F, run F e = some ([v], st') :=
  (sim fe).1 0 [] e v st' h [] [] 1 ([v], st') (by simp [exec])

end Bang.CalcCBNSt
