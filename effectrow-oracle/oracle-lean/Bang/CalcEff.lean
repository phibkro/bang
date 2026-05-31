/-!
# K3 start: effects — a general handler machine calculated from `eval` (Throws)

The first effect stage (roadmap K3; Bahr–Hutton *Monadic Compiler Calculation*
2022 + Hutton–Wright exception-machine lineage). We add **general algebraic
handlers** (`perform`/`handle`, label-dispatched, nesting, forwarding) over a
minimal arithmetic+`let` base, with **Throws** as the first operation.

`raise` is **zero-shot** (it discards its continuation), so this increment needs
no continuation reification — that is deferred to the resumption-using effects
(`State`, one-shot). What *does* fall out of the calculation is the Hutton–Wright
**exception machine, generalised to labelled handlers**: a runtime **handler
stack**, with `MARK ℓ recovery` (install), `UNMARK` (pop on normal completion),
and `THROW ℓ` (unwind to the nearest ℓ-handler) — derived, not designed.

Design notes (vs the closure machines):
* The source is total (exceptions short-circuit but don't diverge), so **`eval`
  is total, no fuel** — it returns an `Outcome` (a value, or a propagating
  effect). Values are `Int` here (no closures yet; compose with `CalcCBN` later).
* The **machine** `exec` is still fuel-bounded — `THROW` jumps to recovery code,
  which isn't a structural subterm — and carries a handler stack, returning a
  machine `Result` (halt, or an uncaught effect).
* Correctness (next): relate `eval`'s `Outcome` to the machine's `Result` —
  `ret v ↔ halt [v]`, `exc ℓ p ↔ uncaught ℓ p` — via the playbook.
-/

namespace Bang.CalcEff

abbrev Label := Nat

/-! ## Source and its total denotational semantics -/

inductive Src where
  | val     : Int → Src
  | add     : Src → Src → Src
  | var     : Nat → Src
  | letE    : Src → Src → Src
  | perform : Label → Src → Src         -- raise effect ℓ carrying the value of the arg
  | handle  : Label → Src → Src → Src   -- handle ℓ onRaise body  (onRaise binds the payload at index 0)
deriving Repr, Inhabited

abbrev Env := List Int

/-- The result of evaluating: a normal value, or a propagating effect (`raise`)
carrying its label and payload, looking for a handler. -/
inductive Outcome where
  | ret : Int → Outcome
  | exc : Label → Int → Outcome
deriving Repr, DecidableEq, Inhabited

/-- Total, structural semantics. `add`/`let`/`perform` short-circuit on a
propagating effect; `handle` catches its own label (running the recovery with the
payload bound) and forwards the rest. -/
def eval : Env → Src → Outcome
  | _,   .val n  => .ret n
  | env, .var i  => .ret (env[i]?.getD 0)
  | env, .add x y =>
      match eval env x with
      | .exc l p => .exc l p
      | .ret a   => match eval env y with
                    | .exc l p => .exc l p
                    | .ret b   => .ret (a + b)
  | env, .letE e1 e2 =>
      match eval env e1 with
      | .exc l p => .exc l p
      | .ret v   => eval (v :: env) e2
  | env, .perform l argE =>
      match eval env argE with
      | .exc l' p => .exc l' p
      | .ret e    => .exc l e            -- raise ℓ with the payload
  | env, .handle l onRaise body =>
      match eval env body with
      | .ret v    => .ret v              -- normal completion: pass through
      | .exc l' p => if l' = l then eval (p :: env) onRaise   -- caught: run recovery, payload at index 0
                     else .exc l' p                            -- forward to an outer handler

/-! ## The machine — derived, not designed

The handler stack and `MARK`/`UNMARK`/`THROW` fall out of the `perform`/`handle`
cases of the calculation spec (Hutton–Wright, generalised to labels):

* `handle ℓ onRaise body` → `MARK ℓ recovery :: compile body (UNMARK :: c)`, where
  `recovery = BIND :: compile onRaise (UNBIND :: c)`: install a handler frame
  capturing (ℓ, recovery, env, stack); run the body; `UNMARK` pops the frame on
  normal completion. The recovery, when reached, `BIND`s the payload (so `onRaise`
  sees it at index 0), runs `onRaise`, `UNBIND`s, and continues with `c`.
* `perform ℓ argE` → `compile argE (THROW ℓ :: c)`: evaluate the payload, then
  `THROW ℓ` unwinds the handler stack to the nearest ℓ-frame, restores its
  env+stack, pushes the payload, and jumps to its recovery. `c` is discarded — the
  continuation is abandoned (zero-shot). No matching frame ⇒ an uncaught effect. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
  | MARK   : Label → List Instr → Instr   -- install a handler: label + recovery code
  | UNMARK : Instr                         -- pop the handler frame (body finished normally)
  | THROW  : Label → Instr                 -- unwind to the nearest handler for the label
deriving Inhabited

abbrev Code  := List Instr
abbrev Stack := List Int

/-- A handler frame on the machine's handler stack: the label it catches, its
recovery code, and the env+value-stack to restore on unwinding. -/
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
  | uncaught : Label → Int → Result
deriving Repr, DecidableEq, Inhabited

def compile : Src → Code → Code
  | .val n,       c => Instr.PUSH n :: c
  | .add x y,     c => compile x (compile y (Instr.ADD :: c))
  | .var i,       c => Instr.LOOKUP i :: c
  | .letE e1 e2,  c => compile e1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c))
  | .perform l e, c => compile e (Instr.THROW l :: c)
  | .handle l onRaise body, c =>
      Instr.MARK l (Instr.BIND :: compile onRaise (Instr.UNBIND :: c))
        :: compile body (Instr.UNMARK :: c)

/-- Find the nearest handler frame catching `l`: return the recovery code + the
restored config (env, payload-on-stack, remaining handler stack), or `uncaught`.
A *pure* function (no `exec` argument), so `exec` stays structurally recursive. -/
def unwindFind : Label → Int → HStack → (Code × Env × Stack × HStack) ⊕ Result
  | l, p, []       => .inr (.uncaught l p)
  | l, p, fr :: hs => if fr.label = l
                      then .inl (fr.recovery, fr.savedEnv, p :: fr.savedStack, hs)
                      else unwindFind l p hs

/-- The machine. Fuel-bounded (`THROW` jumps to recovery code), structurally
recursive on fuel. -/
def exec : Nat → Code → Env → Stack → HStack → Option Result
  | 0,    _,       _,   _, _  => none
  | _+1,  [],      _,   s, _  => some (.halt s)
  | f+1,  i :: c,  env, s, hs =>
    match i, s with
    | Instr.PUSH n,   s              => exec f c env (n :: s) hs
    | Instr.ADD,      (b :: a :: s)  => exec f c env ((a + b) :: s) hs
    | Instr.LOOKUP i, s              => exec f c env ((env[i]?.getD 0) :: s) hs  -- default 0 = eval's var
    | Instr.BIND,     (v :: s)       => exec f c (v :: env) s hs
    | Instr.UNBIND,   s              => match env with
                                        | _ :: env' => exec f c env' s hs
                                        | []        => none
    | Instr.MARK l rec, s            => exec f c env s ({ label := l, recovery := rec,
                                                          savedEnv := env, savedStack := s } :: hs)
    | Instr.UNMARK,   s              => match hs with
                                        | _ :: hs' => exec f c env s hs'   -- drop the handler frame
                                        | []       => none
    | Instr.THROW l,  (p :: _)       =>
        match unwindFind l p hs with
        | .inl (rec, e', s', hs') => exec f rec e' s' hs'   -- direct recursive call: structural
        | .inr res                => some res
    | _,              _              => none                                -- stuck

/-- The result of throwing `l p` against handler stack `hs` with `f` fuel: run the
nearest matching frame's recovery, or report uncaught. (`exec`'s `THROW` arm,
factored out for the proof.) -/
def throwOutcome (f : Nat) (l : Label) (p : Int) (hs : HStack) : Option Result :=
  match unwindFind l p hs with
  | .inl (rec, e', s', hs') => exec f rec e' s' hs'
  | .inr res                => some res

/-- Run a closed program: enough fuel, empty env/stack/handler-stack. -/
def run (fuel : Nat) (e : Src) : Option Result := exec fuel (compile e []) [] [] []

/-! ## Correctness — PROVEN

`exec ∘ compile ≡ eval` for the handler machine, with **no `sorry`** (also
differentially tested green against `eval`). The hardest so far — the new piece is
the **handler stack + unwinding**, so the simulation is *two-part*:

* **`exec_succ`/`exec_mono`** — fuel monotonicity. `exec` is now structurally
  recursive (the `THROW` arm uses the pure `unwindFind`, a direct recursive call —
  not a higher-order `exec` argument), so `simp [exec]` unfolds cleanly.
* **`sim`** — by induction on `e`, two outcomes proved together:
  - *ret*: `eval env e = ret v → ∀ c s hs F r, exec F c env (v::s) hs = some r →
    ∃ F', exec F' (compile e c) env s hs = some r`;
  - *exc*: `eval env e = exc ℓ p → ∀ c s hs F r, throwOutcome F ℓ p hs = some r →
    ∃ F', exec F' (compile e c) env s hs = some r` — a raise compiles to a `THROW`
    whose `throwOutcome` unwinds `hs` exactly as `eval`'s exception propagates. The
    `handle` case links them: a caught exception (eval runs the recovery) matches
    the machine unwinding into that frame's recovery code; `MARK`/`UNMARK` bracket
    the body; a forwarded effect skips the frame both in `eval` and in `unwindFind`.
* **`compile_correct`** — corollary: `run` halts on `[v]` for `ret v`, and reports
  `uncaught ℓ p` for `exc ℓ p`. -/

/-- Map a reference `Outcome` to the machine `Result` it should produce. -/
def outcomeToResult : Outcome → Result
  | .ret n   => .halt [n]
  | .exc l p => .uncaught l p

/-! ### Fuel monotonicity -/

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
      simp only [exec] at h ⊢
      split at h <;>
        first
        | exact ih _ _ _ _ _ h                                                       -- simple recursive
        | simp at h                                                                  -- stuck
        | (split at h <;> first | exact ih _ _ _ _ _ h | exact h | simp at h)        -- UNBIND/UNMARK/THROW

theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s : Stack) (hs : HStack) (r : Result)
    (h : exec f code env s hs = some r) (hle : f ≤ f') : exec f' code env s hs = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle; clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ _ ih

/-! ### The two-part simulation

For every `e`, env, continuation `c`, stack `s`, handler stack `hs`:
* if `eval env e = ret v`, running `compile e c` simulates pushing `v` and running `c`;
* if `eval env e = exc ℓ p`, running `compile e c` simulates `THROW ℓ p` unwinding `hs`
  (the continuation `c` is abandoned). Structural induction on `e`; `exec_mono`
  aligns sub-fuels. The `handle` case installs/pops the frame (`MARK`/`UNMARK`) and
  links a caught exception to unwinding into that frame's recovery. -/
theorem sim : ∀ (e : Src) (env : Env) (c : Code) (s : Stack) (hs : HStack),
    (∀ v, eval env e = .ret v → ∀ F r, exec F c env (v :: s) hs = some r →
        ∃ F', exec F' (compile e c) env s hs = some r) ∧
    (∀ l p, eval env e = .exc l p → ∀ F r, throwOutcome F l p hs = some r →
        ∃ F', exec F' (compile e c) env s hs = some r) := by
  intro e
  induction e with
  | val n =>
    intro env c s hs; refine ⟨?_, ?_⟩
    · intro v hv F r hr; simp only [eval] at hv; obtain rfl := Outcome.ret.inj hv
      exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
    · intro l p hv; simp [eval] at hv
  | var i =>
    intro env c s hs; refine ⟨?_, ?_⟩
    · intro v hv F r hr; simp only [eval] at hv; obtain rfl := Outcome.ret.inj hv
      exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
    · intro l p hv; simp [eval] at hv
  | add x y ihx ihy =>
    intro env c s hs; refine ⟨?_, ?_⟩
    · intro v hv F r hr
      simp only [eval] at hv
      cases hxo : eval env x with
      | exc l p => rw [hxo] at hv; simp at hv
      | ret a =>
        cases hyo : eval env y with
        | exc l p => rw [hxo, hyo] at hv; simp at hv
        | ret b =>
          rw [hxo, hyo] at hv; simp only [Outcome.ret.injEq] at hv; subst hv
          obtain ⟨Gy, hGy⟩ := (ihy env (Instr.ADD :: c) (a :: s) hs).1 b hyo (F + 1) r
            (by simp only [exec]; exact hr)
          exact (ihx env (compile y (Instr.ADD :: c)) s hs).1 a hxo Gy r hGy
    · intro l p hv
      simp only [eval] at hv
      cases hxo : eval env x with
      | exc lx px =>
        rw [hxo] at hv; simp only [Outcome.exc.injEq] at hv; obtain ⟨hl, hp⟩ := hv
        subst lx; subst px
        intro F r hu
        exact (ihx env (compile y (Instr.ADD :: c)) s hs).2 l p hxo F r hu
      | ret a =>
        cases hyo : eval env y with
        | exc ly py =>
          rw [hxo, hyo] at hv; simp only [Outcome.exc.injEq] at hv; obtain ⟨hl, hp⟩ := hv
          subst ly; subst py
          intro F r hu
          obtain ⟨Gy, hGy⟩ := (ihy env (Instr.ADD :: c) (a :: s) hs).2 l p hyo F r hu
          exact (ihx env (compile y (Instr.ADD :: c)) s hs).1 a hxo Gy r hGy
        | ret b => rw [hxo, hyo] at hv; simp at hv
  | letE e1 e2 ih1 ih2 =>
    intro env c s hs; refine ⟨?_, ?_⟩
    · intro v hv F r hr
      simp only [eval] at hv
      cases h1 : eval env e1 with
      | exc l p => rw [h1] at hv; simp at hv
      | ret v1 =>
        rw [h1] at hv               -- hv : eval (v1 :: env) e2 = .ret v
        obtain ⟨G2, hG2⟩ := (ih2 (v1 :: env) (Instr.UNBIND :: c) s hs).1 v hv (F + 1) r
          (by simp only [exec]; exact hr)
        obtain ⟨G1, hG1⟩ := (ih1 env (Instr.BIND :: compile e2 (Instr.UNBIND :: c)) s hs).1 v1 h1
          (G2 + 1) r (by simp only [exec]; exact hG2)
        exact ⟨G1, by simpa only [compile] using hG1⟩
    · intro l p hv
      simp only [eval] at hv
      cases h1 : eval env e1 with
      | exc l' p' =>
        rw [h1] at hv; simp only [Outcome.exc.injEq] at hv; obtain ⟨hl, hp⟩ := hv
        subst l'; subst p'
        intro F r hu
        obtain ⟨G1, hG1⟩ := (ih1 env (Instr.BIND :: compile e2 (Instr.UNBIND :: c)) s hs).2 l p h1 F r hu
        exact ⟨G1, by simpa only [compile] using hG1⟩
      | ret v1 =>
        rw [h1] at hv               -- hv : eval (v1 :: env) e2 = .exc l p
        intro F r hu
        obtain ⟨G2, hG2⟩ := (ih2 (v1 :: env) (Instr.UNBIND :: c) s hs).2 l p hv F r hu
        obtain ⟨G1, hG1⟩ := (ih1 env (Instr.BIND :: compile e2 (Instr.UNBIND :: c)) s hs).1 v1 h1
          (G2 + 1) r (by simp only [exec]; exact hG2)
        exact ⟨G1, by simpa only [compile] using hG1⟩
  | perform lab argE ih =>
    intro env c s hs; refine ⟨?_, ?_⟩
    · intro v hv; simp only [eval] at hv
      cases ha : eval env argE with
      | exc l p => rw [ha] at hv; simp at hv
      | ret e  => rw [ha] at hv; simp at hv
    · intro l p hv
      simp only [eval] at hv
      cases ha : eval env argE with
      | exc l' p' =>
        rw [ha] at hv; simp only [Outcome.exc.injEq] at hv; obtain ⟨hl, hp⟩ := hv
        subst l'; subst p'
        intro F r hu
        exact (ih env (Instr.THROW lab :: c) s hs).2 l p ha F r hu
      | ret e =>
        rw [ha] at hv; simp only [Outcome.exc.injEq] at hv; obtain ⟨hl, hp⟩ := hv
        intro F r hu                 -- hl : lab = l, hp : e = p, hu : throwOutcome F l p hs = some r
        refine (ih env (Instr.THROW lab :: c) s hs).1 e ha (F + 1) r ?_
        show throwOutcome F lab e hs = some r
        rw [hl, hp]; exact hu
  | handle lab onRaise body ihOn ihBody =>
    intro env c s hs
    -- the handler frame `MARK` installs (inlined; `CalcEff` imports no Mathlib `set`)
    refine ⟨?_, ?_⟩
    · intro v hv F r hr
      simp only [eval] at hv
      cases hb : eval env body with
      | ret w =>
        simp only [hb] at hv
        obtain ⟨Gb, hGb⟩ := (ihBody env (Instr.UNMARK :: c) s
            (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs)).1
          w hb (F + 1) r (by simp only [exec]; rw [Outcome.ret.inj hv]; exact hr)
        exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
      | exc l' p =>
        simp only [hb] at hv
        by_cases hc : l' = lab
        · rw [if_pos hc] at hv                 -- hv : eval (p :: env) onRaise = .ret v
          obtain ⟨Go, hGo⟩ := (ihOn (p :: env) (Instr.UNBIND :: c) s hs).1 v hv (F + 1) r
            (by simp only [exec]; exact hr)
          have hthr : throwOutcome (Go + 1) l' p
              (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs) = some r := by
            simp only [throwOutcome, unwindFind]; rw [if_pos hc.symm]; simp only [exec]; exact hGo
          obtain ⟨Gb, hGb⟩ := (ihBody env (Instr.UNMARK :: c) s
            (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs)).2
            l' p hb (Go + 1) r hthr
          exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
        · rw [if_neg hc] at hv; simp at hv      -- forwarded → eval is exc, not ret: vacuous
    · intro l p hv
      simp only [eval] at hv
      cases hb : eval env body with
      | ret w => simp only [hb] at hv; simp at hv
      | exc l' p' =>
        simp only [hb] at hv
        by_cases hc : l' = lab
        · rw [if_pos hc] at hv                  -- hv : eval (p' :: env) onRaise = .exc l p
          intro F r hu
          obtain ⟨Go, hGo⟩ := (ihOn (p' :: env) (Instr.UNBIND :: c) s hs).2 l p hv F r hu
          have hthr : throwOutcome (Go + 1) l' p'
              (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs) = some r := by
            simp only [throwOutcome, unwindFind]; rw [if_pos hc.symm]; simp only [exec]; exact hGo
          obtain ⟨Gb, hGb⟩ := (ihBody env (Instr.UNMARK :: c) s
            (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs)).2
            l' p' hb (Go + 1) r hthr
          exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩
        · rw [if_neg hc] at hv; simp only [Outcome.exc.injEq] at hv; obtain ⟨hl, hp⟩ := hv
          subst l'; subst p'
          intro F r hu
          have hthr : throwOutcome F l p
              (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs) = some r := by
            simp only [throwOutcome, unwindFind]; rw [if_neg (Ne.symm hc)]; exact hu
          obtain ⟨Gb, hGb⟩ := (ihBody env (Instr.UNMARK :: c) s
            (⟨lab, Instr.BIND :: compile onRaise (Instr.UNBIND :: c), env, s⟩ :: hs)).2
            l p hb F r hthr
          exact ⟨Gb + 1, by simp only [compile, exec]; exact hGb⟩

/-- **Correctness of the calculated handler machine.** Running the compiled
program halts on `[v]` when `eval` returns `v`, and reports `uncaught ℓ p` when
`eval` raises an effect that escapes every handler. No `sorry`. -/
theorem compile_correct (e : Src) :
    ∃ F, run F e = some (outcomeToResult (eval [] e)) := by
  cases ho : eval [] e with
  | ret v =>
    obtain ⟨F, hF⟩ := (sim e [] [] [] []).1 v ho 1 (.halt [v]) (by simp [exec])
    exact ⟨F, by simpa only [run, outcomeToResult] using hF⟩
  | exc l p =>
    obtain ⟨F, hF⟩ := (sim e [] [] [] []).2 l p ho 1 (.uncaught l p) (by simp [throwOutcome, unwindFind])
    exact ⟨F, by simpa only [run, outcomeToResult] using hF⟩

end Bang.CalcEff
