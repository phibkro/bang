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

/-! ## Correctness — PROVEN

`exec ∘ compile ≡ eval` for the call-by-name machine, with **no `sorry`**. It is
*also* differentially tested green against the `eval` oracle — and because
`Bang.Eval` is itself call-by-name, that agreement holds on every program,
laziness included (invariant 1). Structure (reuses the playbook
`docs/notes/k2-calculation-playbook.md`, plus a mutual twist for `eval`/`forceV`):

1. `exec_succ`/`exec_mono` (fuel monotonicity) — as in `CalcHO`, but two nested
   arms now (`APP` *and* `FORCE` on a `vthunk`).
2. `sim` — a **mutual** simulation, by induction on the eval fuel, proving together
   the `eval`-sim (compiled `e` then `c` simulates pushing `eval e`) and the
   `forceV`-sim (`FORCE` then `c` simulates pushing the forced value). The
   `force`/`app`/`add`/`mul` cases of the eval-sim invoke the forceV-sim; the
   `FORCE`-on-`vthunk` step of the forceV-sim invokes the eval-sim on the thunk
   body. Shared `vthunk`/`vclo` keep both sides equalities; `exec_mono` aligns the
   sub-fuels.
3. `compile_correct` — the corollary. -/

/-- **Fuel monotonicity (one step).** As in `CalcHO`, but with two nested arms:
`APP` and `FORCE`-on-a-thunk. -/
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
        | exact ih _ _ _ _ h                                     -- simple recursive arms
        | simp at h                                              -- stuck arms
        | (split at h <;> first | exact ih _ _ _ _ h | simp at h) -- LOOKUP nested option
        | skip                                                   -- leave the nested arms
      all_goals first
        | (-- APP arm
           rename_i va body cenv s'
           cases hb : exec f (compile body []) (va :: cenv) [] with
           | none => rw [hb] at h; simp at h
           | some bs => cases bs with
             | nil => rw [hb] at h; simp at h
             | cons rv _ => rw [hb] at h; rw [ih _ _ _ _ hb]; exact ih _ _ _ _ h)
        | (-- FORCE-on-thunk arm
           rename_i body tenv s'
           cases hb : exec f (compile body [Instr.FORCE]) tenv [] with
           | none => rw [hb] at h; simp at h
           | some bs => cases bs with
             | nil => rw [hb] at h; simp at h
             | cons w _ => rw [hb] at h; rw [ih _ _ _ _ hb]; exact ih _ _ _ _ h)

/-- **Fuel monotonicity.** More fuel never changes a successful result. -/
theorem exec_mono (f f' : Nat) (code : Code) (env : Env) (s r : Stack)
    (h : exec f code env s = some r) (hle : f ≤ f') : exec f' code env s = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ ih

/-- **The mutual simulation.** Proved together by induction on the eval fuel:
the `eval`-sim (compiled `e` then `c` simulates pushing `eval e`) and the
`forceV`-sim (`FORCE` then `c` simulates pushing the forced value). Each uses the
other on subterms; `exec_mono` aligns the sub-fuels; the shared `vthunk`/`vclo`
keep both sides equalities. -/
theorem sim : ∀ (fe : Nat),
    (∀ env e v, eval fe env e = some v → ∀ c s F r,
        exec F c env (v :: s) = some r → ∃ F', exec F' (compile e c) env s = some r) ∧
    (∀ v w, forceV fe v = some w → ∀ env c s F r,
        exec F c env (w :: s) = some r → ∃ F', exec F' (Instr.FORCE :: c) env (v :: s) = some r) := by
  intro fe
  induction fe with
  | zero => exact ⟨fun env e v h => by simp [eval] at h, fun v w h => by simp [forceV] at h⟩
  | succ fe ih =>
    obtain ⟨ihe, ihf⟩ := ih
    refine ⟨?_, ?_⟩
    · -- eval-sim at fe+1
      intro env e v h c s F r hr
      cases e with
      | val n => simp only [eval] at h; obtain rfl := Option.some.inj h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | var i => simp only [eval] at h
                 exact ⟨F + 1, by simp only [compile, exec, h]; exact hr⟩
      | lam b => simp only [eval] at h; obtain rfl := Option.some.inj h
                 exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | thnk e => simp only [eval] at h; obtain rfl := Option.some.inj h
                  exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
      | force e =>
        simp only [eval, Option.bind_eq_some_iff] at h
        obtain ⟨ve, he, hf⟩ := h
        obtain ⟨G, hG⟩ := ihf ve v hf env c s F r hr
        obtain ⟨F', hF'⟩ := ihe env e ve he (Instr.FORCE :: c) s G r hG
        exact ⟨F', by simpa only [compile] using hF'⟩
      | letE e1 e2 =>
        simp only [eval] at h
        obtain ⟨G2, hG2⟩ := ihe (.vthunk e1 env :: env) e2 v h (Instr.UNBIND :: c) s (F + 1) r
          (by simp only [exec]; exact hr)
        exact ⟨G2 + 2, by simp only [compile, exec]; exact hG2⟩
      | add x y =>
        simp only [eval] at h
        cases hx : (eval fe env x).bind (forceV fe) with
        | none => rw [hx] at h; simp at h
        | some vx => cases vx with
          | vclo _ _ => rw [hx] at h; simp at h
          | vthunk _ _ => rw [hx] at h; simp at h
          | vint a => cases hy : (eval fe env y).bind (forceV fe) with
            | none => rw [hx, hy] at h; simp at h
            | some vy => cases vy with
              | vclo _ _ => rw [hx, hy] at h; simp at h
              | vthunk _ _ => rw [hx, hy] at h; simp at h
              | vint b =>
                rw [hx, hy] at h; simp only [Option.some.injEq] at h; subst h
                obtain ⟨vyv, hyv, hyf⟩ := Option.bind_eq_some_iff.mp hy
                obtain ⟨vxv, hxv, hxf⟩ := Option.bind_eq_some_iff.mp hx
                obtain ⟨Gy, hGy⟩ := ihf vyv (.vint b) hyf env (Instr.ADD :: c) (.vint a :: s) (F + 1) r
                  (by simp only [exec]; exact hr)
                obtain ⟨Hy, hHy⟩ := ihe env y vyv hyv (Instr.FORCE :: Instr.ADD :: c) (.vint a :: s) Gy r hGy
                obtain ⟨Gx, hGx⟩ := ihf vxv (.vint a) hxf env (compile y (Instr.FORCE :: Instr.ADD :: c)) s Hy r hHy
                obtain ⟨F', hF'⟩ := ihe env x vxv hxv
                  (Instr.FORCE :: compile y (Instr.FORCE :: Instr.ADD :: c)) s Gx r hGx
                exact ⟨F', by simpa only [compile] using hF'⟩
      | mul x y =>
        simp only [eval] at h
        cases hx : (eval fe env x).bind (forceV fe) with
        | none => rw [hx] at h; simp at h
        | some vx => cases vx with
          | vclo _ _ => rw [hx] at h; simp at h
          | vthunk _ _ => rw [hx] at h; simp at h
          | vint a => cases hy : (eval fe env y).bind (forceV fe) with
            | none => rw [hx, hy] at h; simp at h
            | some vy => cases vy with
              | vclo _ _ => rw [hx, hy] at h; simp at h
              | vthunk _ _ => rw [hx, hy] at h; simp at h
              | vint b =>
                rw [hx, hy] at h; simp only [Option.some.injEq] at h; subst h
                obtain ⟨vyv, hyv, hyf⟩ := Option.bind_eq_some_iff.mp hy
                obtain ⟨vxv, hxv, hxf⟩ := Option.bind_eq_some_iff.mp hx
                obtain ⟨Gy, hGy⟩ := ihf vyv (.vint b) hyf env (Instr.MUL :: c) (.vint a :: s) (F + 1) r
                  (by simp only [exec]; exact hr)
                obtain ⟨Hy, hHy⟩ := ihe env y vyv hyv (Instr.FORCE :: Instr.MUL :: c) (.vint a :: s) Gy r hGy
                obtain ⟨Gx, hGx⟩ := ihf vxv (.vint a) hxf env (compile y (Instr.FORCE :: Instr.MUL :: c)) s Hy r hHy
                obtain ⟨F', hF'⟩ := ihe env x vxv hxv
                  (Instr.FORCE :: compile y (Instr.FORCE :: Instr.MUL :: c)) s Gx r hGx
                exact ⟨F', by simpa only [compile] using hF'⟩
      | app g a =>
        simp only [eval] at h
        cases hgf : (eval fe env g).bind (forceV fe) with
        | none => rw [hgf] at h; simp at h
        | some vgf => cases vgf with
          | vint _ => rw [hgf] at h; simp at h
          | vthunk _ _ => rw [hgf] at h; simp at h
          | vclo b cenv =>
            rw [hgf] at h; simp only at h        -- h : eval fe (vthunk a env :: cenv) b = some v
            obtain ⟨vg, hgv, hgforce⟩ := Option.bind_eq_some_iff.mp hgf
            obtain ⟨G, hG⟩ := ihe (.vthunk a env :: cenv) b v h [] [] 1 [v] (by simp [exec])
            have hGbig : exec (G + F) (compile b []) (.vthunk a env :: cenv) [] = some [v] :=
              exec_mono _ _ _ _ _ _ hG (by omega)
            have hrbig : exec (G + F) c env (v :: s) = some r := exec_mono _ _ _ _ _ _ hr (by omega)
            have happ : exec (G + F + 1) (Instr.APP :: c) env (.vthunk a env :: .vclo b cenv :: s) = some r := by
              simp only [exec, hGbig]; exact hrbig
            have hthunk : exec (G + F + 2) (Instr.THUNK a :: Instr.APP :: c) env (.vclo b cenv :: s) = some r := by
              simp only [exec]; exact happ
            obtain ⟨H, hH⟩ := ihf vg (.vclo b cenv) hgforce env (Instr.THUNK a :: Instr.APP :: c) s
              (G + F + 2) r hthunk
            obtain ⟨F', hF'⟩ := ihe env g vg hgv (Instr.FORCE :: Instr.THUNK a :: Instr.APP :: c) s H r hH
            exact ⟨F', by simpa only [compile] using hF'⟩
    · -- forceV-sim at fe+1
      intro v w h env c s F r hr
      cases v with
      | vint n => simp only [forceV] at h; obtain rfl := Option.some.inj h
                  exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vclo b ve => simp only [forceV] at h; obtain rfl := Option.some.inj h
                     exact ⟨F + 1, by simp only [exec]; exact hr⟩
      | vthunk e ve =>
        simp only [forceV, Option.bind_eq_some_iff] at h
        obtain ⟨ve', he, hf⟩ := h
        obtain ⟨A, hA⟩ := ihf ve' w hf ve [] [] 1 [w] (by simp [exec])
        obtain ⟨B, hB⟩ := ihe ve e ve' he [Instr.FORCE] [] A [w] hA
        have hBbig : exec (B + F) (compile e [Instr.FORCE]) ve [] = some [w] :=
          exec_mono _ _ _ _ _ _ hB (by omega)
        have hrbig : exec (B + F) c env (w :: s) = some r := exec_mono _ _ _ _ _ _ hr (by omega)
        exact ⟨B + F + 1, by simp only [exec, hBbig]; exact hrbig⟩

/-- **Correctness of the calculated call-by-name machine.** If the definitional
`eval` produces `v`, the compiled program halts (with enough fuel) on `[v]`. -/
theorem compile_correct (fe : Nat) (env : Env) (e : Src) (v : Value)
    (h : eval fe env e = some v) : ∃ F, exec F (compile e []) env [] = some [v] :=
  (sim fe).1 env e v h [] [] 1 [v] (by simp [exec])

end Bang.CalcCBN
