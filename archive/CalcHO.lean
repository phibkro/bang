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

**Proof status:** the machine is calculated and the equivalence `exec ∘ compile ≡
eval` is **PROVEN** — `compile_correct` (via the `sim` simulation), no `sorry`. It
is *also* differentially tested green against the `eval` oracle. The proof is a
fuel-indexed simulation resting on fuel-monotonicity (`exec_succ`/`exec_mono`).
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

/-! ## Correctness — the calculation's theorem (PROVEN)

`exec ∘ compile ≡ eval` for the higher-order closure machine, in three steps:

1. **Fuel monotonicity** — `exec_succ` / `exec_mono`: more fuel never changes a
   successful result. Induction on fuel; the `APP` case uses the IH on the nested
   callee run.
2. **The simulation** — `sim`: `eval fe env e = some v → ∀ c s F r,
   exec F c env (v :: s) = some r → ∃ F', exec F' (compile e c) env s = some r`.
   Induction on the eval fuel; each case chains the IH on subterms through the
   derived instructions. The concrete target `some r` (not `exec F c …`) is what
   lets `exec_mono` align the sub-fuels — the `app` case bumps the callee and the
   continuation to a common fuel. The shared `vclo` keeps `lam`/`app` an equality,
   not a logical relation.
3. **`compile_correct`** — the corollary: `eval fe env e = some v → ∃ F,
   exec F (compile e []) env [] = some [v]`.

The machine is *also* differentially tested green against the `eval` oracle. -/

/-- **Fuel monotonicity (one step).** If the machine succeeds with `f` fuel it
succeeds identically with `f+1`. Proof plan step 1. -/
theorem exec_succ : ∀ (f : Nat) (code : Code) (env : Env) (s r : Stack),
    exec f code env s = some r → exec (f + 1) code env s = some r := by
  intro f
  induction f with
  | zero => intro code env s r h; simp [exec] at h
  | succ f ih =>
    intro code env s r h
    cases code with
    | nil => simpa only [exec] using h
    | cons i c =>
      simp only [exec] at h ⊢
      split at h <;>
        first
        | exact ih _ _ _ _ h                              -- simple recursive arms
        | simp at h                                       -- stuck arms: none = some r
        | (split at h <;>                                 -- LOOKUP: nested option match
            first | exact ih _ _ _ _ h | simp at h)
        | skip                                            -- leave the APP arm
      -- the remaining goal(s): the APP arm, whose nested callee run needs the IH
      all_goals (
        rename_i va body cenv s'
        cases hb : exec f (compile body []) (va :: cenv) [] with
        | none      => rw [hb] at h; simp at h
        | some bs   =>
          cases bs with
          | nil          => rw [hb] at h; simp at h
          | cons rv rest =>
            rw [hb] at h
            rw [ih _ _ _ _ hb]
            exact ih _ _ _ _ h)

/-- **Fuel monotonicity.** More fuel never changes a successful result. -/
theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s r : Stack)
    (h : exec f code env s = some r) (hle : f ≤ f') : exec f' code env s = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ ih

/-- **The simulation (forward).** If `eval` produces `v`, then for any
continuation `c` whose run with `v` pushed reaches `r`, the compiled program
`compile e c` reaches the same `r` given enough fuel. The concrete target `some r`
(rather than `exec F c …`) lets `exec_mono` align the sub-fuels. Induction on the
eval fuel; each case chains the IH on subterms through the derived instructions. -/
theorem sim : ∀ (fe : Nat) (env : Env) (e : Src) (v : Value),
    eval fe env e = some v → ∀ (c : Code) (s : Stack) (F : Nat) (r : Stack),
    exec F c env (v :: s) = some r → ∃ F', exec F' (compile e c) env s = some r := by
  intro fe
  induction fe with
  | zero => intro env e v h; simp [eval] at h
  | succ fe ih =>
    intro env e v h c s F r hr
    cases e with
    | val n =>
      simp only [eval] at h; obtain rfl := Option.some.inj h
      exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
    | var i =>
      simp only [eval] at h
      exact ⟨F + 1, by simp only [compile, exec, h]; exact hr⟩
    | lam body =>
      simp only [eval] at h; obtain rfl := Option.some.inj h
      exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
    | add x y =>
      simp only [eval] at h
      cases hx : eval fe env x with
      | none => rw [hx] at h; simp at h
      | some vx => cases vx with
        | vclo _ _ => rw [hx] at h; simp at h
        | vint a => cases hy : eval fe env y with
          | none => rw [hx, hy] at h; simp at h
          | some vy => cases vy with
            | vclo _ _ => rw [hx, hy] at h; simp at h
            | vint b =>
              rw [hx, hy] at h; simp only [Option.some.injEq] at h; subst h
              obtain ⟨Fy, hFy⟩ := ih env y (.vint b) hy (Instr.ADD :: c) (.vint a :: s)
                (F + 1) r (by simp only [exec]; exact hr)
              obtain ⟨Fx, hFx⟩ := ih env x (.vint a) hx (compile y (Instr.ADD :: c)) s Fy r hFy
              exact ⟨Fx, by simpa only [compile] using hFx⟩
    | mul x y =>
      simp only [eval] at h
      cases hx : eval fe env x with
      | none => rw [hx] at h; simp at h
      | some vx => cases vx with
        | vclo _ _ => rw [hx] at h; simp at h
        | vint a => cases hy : eval fe env y with
          | none => rw [hx, hy] at h; simp at h
          | some vy => cases vy with
            | vclo _ _ => rw [hx, hy] at h; simp at h
            | vint b =>
              rw [hx, hy] at h; simp only [Option.some.injEq] at h; subst h
              obtain ⟨Fy, hFy⟩ := ih env y (.vint b) hy (Instr.MUL :: c) (.vint a :: s)
                (F + 1) r (by simp only [exec]; exact hr)
              obtain ⟨Fx, hFx⟩ := ih env x (.vint a) hx (compile y (Instr.MUL :: c)) s Fy r hFy
              exact ⟨Fx, by simpa only [compile] using hFx⟩
    | letE e1 e2 =>
      simp only [eval] at h
      cases h1 : eval fe env e1 with
      | none => rw [h1] at h; simp at h
      | some v1 =>
        rw [h1] at h; simp only at h        -- h : eval fe (v1 :: env) e2 = some v
        obtain ⟨F2, hF2⟩ := ih (v1 :: env) e2 v h (Instr.UNBIND :: c) s (F + 1) r
          (by simp only [exec]; exact hr)
        obtain ⟨F1, hF1⟩ := ih env e1 v1 h1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c)) s
          (F2 + 1) r (by simp only [exec]; exact hF2)
        exact ⟨F1, by simpa only [compile] using hF1⟩
    | app g a =>
      simp only [eval] at h
      cases hg : eval fe env g with
      | none => rw [hg] at h; simp at h
      | some vg => cases vg with
        | vint _ => rw [hg] at h; simp at h
        | vclo body cenv => cases ha : eval fe env a with
          | none => rw [hg, ha] at h; simp at h
          | some va =>
            rw [hg, ha] at h; simp only at h    -- h : eval fe (va :: cenv) body = some v
            -- 1. run the callee body to [v]
            obtain ⟨G, hG⟩ := ih (va :: cenv) body v h [] [] 1 [v] (by simp [exec])
            -- 2. APP step, with fuel big enough for both the callee and the continuation
            have hGbig : exec (G + F) (compile body []) (va :: cenv) [] = some [v] :=
              exec_mono _ _ _ _ _ _ hG (by omega)
            have hrbig : exec (G + F) c env (v :: s) = some r :=
              exec_mono _ _ _ _ _ _ hr (by omega)
            have happ : exec (G + F + 1) (Instr.APP :: c) env (va :: .vclo body cenv :: s) = some r := by
              simp only [exec, hGbig]; exact hrbig
            -- 3. chain ih on the argument, then the function
            obtain ⟨H, hH⟩ := ih env a va ha (Instr.APP :: c) (.vclo body cenv :: s)
              (G + F + 1) r happ
            obtain ⟨F', hF'⟩ := ih env g (.vclo body cenv) hg (compile a (Instr.APP :: c)) s H r hH
            exact ⟨F', by simpa only [compile] using hF'⟩

/-- **Correctness of the calculated higher-order machine.** If the definitional
`eval` produces `v`, the compiled program halts (with enough fuel) on `[v]`. The
calculation `exec ∘ compile ≡ eval` for closures — no longer `sorry`. -/
theorem compile_correct (fe : Nat) (env : Env) (e : Src) (v : Value)
    (h : eval fe env e = some v) : ∃ F, exec F (compile e []) env [] = some [v] :=
  sim fe env e v h [] [] 1 [v] (by simp [exec])

end Bang.CalcHO
