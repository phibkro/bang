import Bang.Operational

/-!
# CalcVM — the ◊3 graded-CBPV calculated machine (pure CBPV spine)

The Bahr–Hutton calculation (ADR-0016, ADR-0017; invariant #4) ported ONCE to
the new graded-CBPV `Comp`/`Val` (`Bang.Core`), replacing the K2 `Calc*.lean`
matrix over the old free-monad `Expr`/`Value`.

This file lands the **pure CBPV spine** (PATH-calcvm-port): the
returner/sequencing/abstraction core `ret` · `letC` · `force`/`vthunk` ·
`lam` · `app`, the calculated machine over it, AND the **`evalD ≡ Source.eval`
agreement (the D1-A bridge)** for that spine. Deep handlers (`up`/`handle`), the
ADT eliminators (`case`/`split`/`unfold`), and the full diff-test battery are
later increments. Nothing here is `sorry`/`axiom`.

## Design lock: substitution / closed-focus, mirroring the kernel (option b)

The kernel's own machine `Source.step` (`Bang/Operational.lean`) is
**substitution-based with a CLOSED focus** — there is NO environment and NO
closure: `force (vthunk M) ↦ M`, `letC`/`app` reduce by `Comp.subst`. We mirror
it. So `evalD` here is substitution-based (NOT the env-based K2 `Calc.lean`
shape), which (a) keeps the machine kernel-faithful (invariant #1 — rides the
reference) and (b) makes the future `evalD ≡ Source.eval` bridge nearly
mechanical (subst-vs-subst, only a big/small-step gap), which is the whole point
of D1-A (type-safety inheritance).

**CBPV wrinkle:** `evalD` returns a *terminal computation* `Option Comp`
(`ret v` OR `lam M`), not `Option Val` — a function-typed computation reduces to
`lam`, which is a `Comp`, not a value. `app M v` runs `M` to a `lam N` then
β-substitutes; `letC M N` runs `M` to a `ret v` then substitutes.

## DEFERRED (a later calculation increment, NOT abandoned)

This is the RIGHT FIRST STAGE, a CK-style machine: its `SUBST`/`APP` instructions
carry a *residual `Comp`* and re-`compile` `N[v]` at runtime, so the machine is
NOT yet "flat" (no numeric-only stack). A FURTHER calculation step —
**defunctionalize the frames + compile substitution away** — flattens it toward a
real numeric-stack VM / the WasmFX target. Invariant #7 (perf second-class) backs
staging that AFTER the spine is feature-complete (force/lam/app/effects). Do not
lose the flat-machine goal; it is the next-but-one increment.

## What the calculation forces into existence

Posit, forward to a concrete result (the fuel-alignment key, k2-playbook §1):

    evalD n M = some t  →  exec F c (t :: s) = some r  →  ∃ F', exec F' (compile M c) s = some r   (★)

and compute by induction on the eval fuel `n`. Each constructor forces an
instruction; `{RET, LAMI, SUBST, APP}` is the OUTPUT, never hand-designed
(invariant #4). Fuel monotonicity (`exec_mono`) bumps sub-fuels to a common
value. `compile_correct` is the `c = []`, `s = []` corollary, **proven** below.

`-- shape: bahr-hutton monadic-compiler-calculation §3 (partiality monad)`
`-- some-r forward statement + exec_mono per k2-calculation-playbook §1–2`
-/

namespace Bang.CalcVM

open Bang (Val Comp Frame Config Result)

/-! ## The denotational source `evalD` (substitution, terminal-Comp)

Fuel-bounded, structurally recursive on the fuel (NO `termination_by`, so the
equations unfold under `simp`/`rw`; k2-playbook §3). `none` = stuck / out-of-fuel
/ out-of-scope (the partiality ⊥). `ret`/`lam` are terminal; `letC`/`app` sequence
through a sub-eval and substitute; `force (vthunk M)` runs the (closed) body. -/
def evalD : Nat → Comp → Option Comp
  | 0,          _                  => none
  | Nat.succ _, .ret v             => some (.ret v)
  | Nat.succ _, .lam M             => some (.lam M)
  | Nat.succ f, .letC M N          =>
      (evalD f M).bind (fun t => match t with
        | .ret v => evalD f (Comp.subst v N)         -- M : F _ ⇒ terminal is `ret v`
        | _      => none)
  | Nat.succ f, .force (.vthunk M) => evalD f M       -- force∘thunk = run the closed body
  | Nat.succ f, .app M v           =>
      (evalD f M).bind (fun t => match t with
        | .lam N => evalD f (Comp.subst v N)          -- β: M ⇒ lam N, then N[v]
        | _      => none)
  | _,          _                  => none            -- out of scope (handlers / ADT elim)

/-! ## The machine — derived, not designed

Each `evalD` clause forces an instruction (computing the RHS of (★)):

* `ret v`  → `RET v`  : push the terminal `ret v`.
* `lam M`  → `LAMI M` : push the terminal `lam M`.
* `letC M N` → `compile M (SUBST N :: c)`: run `M`; `SUBST N` pops its `ret v`,
  then runs `N[v]` (re-`compile`d) before `c`.
* `force (vthunk M)` → `compile M c`: forcing a thunk just runs its closed body —
  no instruction; the calculation collapses it.
* `app M v` → `compile M (APP v :: c)`: run `M`; `APP v` pops its `lam N`, runs
  `N[v]`.

`{RET, LAMI, SUBST, APP}` falls out. `SUBST`/`APP` carry the residual `Comp` (the
CK-flavour noted in the header — flattened in a later increment). -/

inductive Instr where
  | RET   : Val → Instr      -- push the terminal `ret v`
  | LAMI  : Comp → Instr     -- push the terminal `lam M`
  | SUBST : Comp → Instr     -- pop `ret v`; compile+run `N[v]` before continuing
  | APP   : Val → Instr      -- pop `lam N`; compile+run `N[v]` before continuing
  deriving Inhabited

abbrev Code  := List Instr
/-- The machine stack holds *terminal computations* (`ret v` / `lam M`) — the
shared value representation both `evalD` and `exec` produce, keeping correctness a
plain equality (no logical relation; k2-playbook §2). -/
abbrev Stack := List Comp

def compile : Comp → Code → Code
  | .ret v,             c => Instr.RET v :: c
  | .lam M,             c => Instr.LAMI M :: c
  | .letC M N,          c => compile M (Instr.SUBST N :: c)
  | .force (.vthunk M), c => compile M c
  | .app M v,           c => compile M (Instr.APP v :: c)
  | _,                  c => c               -- out of scope: emit nothing (residual)

/-- The machine. Structurally recursive on the fuel (k2-playbook §3); `SUBST`/`APP`
re-enter `compile` on the substituted body (the CK re-compile), guarded by fuel. -/
def exec : Nat → Code → Stack → Option Stack
  | 0,          _,                  _ => none
  | Nat.succ _, [],                 s => some s
  | Nat.succ f, Instr.RET v :: c,   s => exec f c (.ret v :: s)
  | Nat.succ f, Instr.LAMI M :: c,  s => exec f c (.lam M :: s)
  | Nat.succ f, Instr.SUBST N :: c, s =>
      match s with
      | .ret v :: s' => exec f (compile (Comp.subst v N) c) s'
      | _            => none
  | Nat.succ f, Instr.APP v :: c, s =>
      match s with
      | .lam N :: s' => exec f (compile (Comp.subst v N) c) s'
      | _            => none

/-! ## The calculation is correct (proven) -/

/-- Fuel monotonicity, one step (k2-playbook §2 bedrock): more fuel never changes a
`some`. Induction on fuel, `cases` on the head instruction; `SUBST`/`APP`'s nested
stack-match resolves the same way. -/
theorem exec_succ : ∀ f c s r, exec f c s = some r → exec (f+1) c s = some r := by
  intro f
  induction f with
  | zero => intro c s r h; simp [exec] at h
  | succ f ih =>
    intro c s r h
    cases c with
    | nil => simpa [exec] using h
    | cons i c =>
      cases i with
      | RET v => simp only [exec] at h ⊢; exact ih _ _ _ h
      | LAMI M => simp only [exec] at h ⊢; exact ih _ _ _ h
      | SUBST N =>
        simp only [exec] at h ⊢
        cases s with
        | nil => simp at h
        | cons hd s' => cases hd with
          | ret v => simp only [] at h ⊢; exact ih _ _ _ h
          | _ => simp at h
      | APP v =>
        simp only [exec] at h ⊢
        cases s with
        | nil => simp at h
        | cons hd s' => cases hd with
          | lam N => simp only [] at h ⊢; exact ih _ _ _ h
          | _ => simp at h

/-- Fuel monotonicity, `≤` (k2-playbook §2): bump any sub-fuel to a common value. -/
theorem exec_mono : ∀ f g c s r, f ≤ g → exec f c s = some r → exec g c s = some r := by
  intro f g c s r hle h
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ ih

/-- (★) the simulation, forward to a concrete `some r` with fuels aligned via
`exec_mono` (k2-playbook §1). Induction on the eval fuel `fe`, `cases` on `M`;
`SUBST`/`APP` chain the IH right-to-left through the derived instructions. The
shared terminal-`Comp` representation keeps each step an equality (k2-playbook §2). -/
theorem sim : ∀ fe M t, evalD fe M = some t →
    ∀ c s F r, exec F c (t :: s) = some r → ∃ F', exec F' (compile M c) s = some r := by
  intro fe
  induction fe with
  | zero => intro M t h; simp [evalD] at h
  | succ fe ih =>
    intro M t h c s F r hr
    cases M with
    | ret v =>
        simp only [evalD, Option.some.injEq] at h; subst h
        exact ⟨F+1, by simp only [compile, exec]; exact hr⟩
    | lam M =>
        simp only [evalD, Option.some.injEq] at h; subst h
        exact ⟨F+1, by simp only [compile, exec]; exact hr⟩
    | letC M N =>
        simp only [evalD] at h
        cases hM : evalD fe M with
        | none => rw [hM] at h; simp at h
        | some tM =>
          rw [hM] at h
          match tM, h with
          | .ret v, h =>
              simp only [Option.bind_some] at h
              obtain ⟨F1, hF1⟩ := ih (Comp.subst v N) t h c s F r hr
              have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v :: s) = some r := by
                simp only [exec]; exact hF1
              obtain ⟨F2, hF2⟩ := ih M (.ret v) hM (Instr.SUBST N :: c) s (F1+1) r hstep
              exact ⟨F2, by simpa [compile] using hF2⟩
          | .lam M2, h => simp [Option.bind] at h
          | .letC a b, h => simp [Option.bind] at h
          | .force a, h => simp [Option.bind] at h
          | .app a b, h => simp [Option.bind] at h
          | .up a b d, h => simp [Option.bind] at h
          | .handle a b, h => simp [Option.bind] at h
          | .case a b d, h => simp [Option.bind] at h
          | .split a b, h => simp [Option.bind] at h
          | .unfold a, h => simp [Option.bind] at h
          | .oom, h => simp [Option.bind] at h
          | .wrong a, h => simp [Option.bind] at h
    | force a =>
        cases a with
        | vthunk M =>
            simp only [evalD] at h
            obtain ⟨F', hF'⟩ := ih M t h c s F r hr
            exact ⟨F', by simpa only [compile] using hF'⟩
        | vunit => simp [evalD] at h
        | vint n => simp [evalD] at h
        | vvar i => simp [evalD] at h
        | inl w => simp [evalD] at h
        | inr w => simp [evalD] at h
        | pair w1 w2 => simp [evalD] at h
        | fold w => simp [evalD] at h
    | app M v =>
        simp only [evalD] at h
        cases hM : evalD fe M with
        | none => rw [hM] at h; simp at h
        | some tM =>
          rw [hM] at h
          match tM, h with
          | .lam N, h =>
              simp only [Option.bind_some] at h
              obtain ⟨F1, hF1⟩ := ih (Comp.subst v N) t h c s F r hr
              have hstep : exec (F1+1) (Instr.APP v :: c) (.lam N :: s) = some r := by
                simp only [exec]; exact hF1
              obtain ⟨F2, hF2⟩ := ih M (.lam N) hM (Instr.APP v :: c) s (F1+1) r hstep
              exact ⟨F2, by simpa [compile] using hF2⟩
          | .ret w, h => simp [Option.bind] at h
          | .letC a b, h => simp [Option.bind] at h
          | .force a, h => simp [Option.bind] at h
          | .app a b, h => simp [Option.bind] at h
          | .up a b d, h => simp [Option.bind] at h
          | .handle a b, h => simp [Option.bind] at h
          | .case a b d, h => simp [Option.bind] at h
          | .split a b, h => simp [Option.bind] at h
          | .unfold a, h => simp [Option.bind] at h
          | .oom, h => simp [Option.bind] at h
          | .wrong a, h => simp [Option.bind] at h
    | up a b d => simp [evalD] at h
    | handle a b => simp [evalD] at h
    | case a b d => simp [evalD] at h
    | split a b => simp [evalD] at h
    | unfold a => simp [evalD] at h
    | oom => simp [evalD] at h
    | wrong a => simp [evalD] at h

/-- Headline: compiling a closed computation and running it on the empty stack
yields exactly `[t]` where `evalD n M = some t` (the convergent pure spine).
Pure-spine ◊3 increment — the `compile_correct` analogue of `Bang.Calc`. -/
theorem compile_correct (n : Nat) (M : Comp) (t : Comp) (h : evalD n M = some t) :
    ∃ F, exec F (compile M []) [] = some [t] := by
  have hbase : exec 1 [] (t :: []) = some [t] := by simp [exec]
  obtain ⟨F, hF⟩ := sim n M t h [] [] 1 [t] hbase
  exact ⟨F, hF⟩

/-! ## Diff-test seeds (PATH-calcvm-port Unit 4)

The Lean-side replacement for the deleted TS differential harness: assert the
machine reproduces `evalD` on curated programs by `rfl`. First grains of the
`native_decide` battery the ◊3 gate will grow. -/

/-- `(λ. ret #0) 5` ⇒ `[ret 5]` — β through `LAMI`/`APP`. -/
example :
    exec 10 (compile (.app (.lam (.ret (.vvar 0))) (.vint 5)) []) [] = some [.ret (.vint 5)] := by
  rfl

/-- `let x = (λ.ret #0) 5 in ret x` ⇒ `[ret 5]` — `SUBST` over an applied lambda. -/
example :
    exec 12 (compile (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0))) []) []
      = some [.ret (.vint 5)] := by
  rfl

/-- `force (thunk (ret 9))` ⇒ `[ret 9]` — `force`∘`vthunk` collapses to the body. -/
example :
    exec 10 (compile (.force (.vthunk (.ret (.vint 9)))) []) [] = some [.ret (.vint 9)] := by
  rfl

/-! ## The D1-A bridge: `evalD ≡ Source.eval` (pure spine)

The agreement that makes the substitution `evalD` worth calculating from (D1-A):
the denotational big-step `evalD` agrees with the kernel's *type-safety-verified*
small-step `Source.eval` (`Bang/Operational.lean`). Because both are substitution-
based with a closed focus, the bridge is a plain big/small-step simulation — no
cross-representation logical relation (the payoff of decision (b)).

`run_evalD` is the simulation, forward to a concrete `Config.run` result (the
fuel-alignment key, k2-playbook §1) over an arbitrary CK context `K`. Each `evalD`
clause maps to the matching `Source.step` PUSH+REDUCE pair:
`letC`→`letF`-frame, `app`→`appF`-frame, `force (vthunk)`→drop-the-thunk. The
`evalD_agrees_source` corollary (`K = []`, terminal `ret v`) is the headline: an
`evalD` that returns `v` is witnessed by `Source.eval … = .done v`, so the
verified kernel's `type_safety` now backs the calculated machine's `ret`-results
(invariant #1). Handlers/ADT eliminators extend this in later increments. -/

/-- Multi-step simulation: running the CK machine (`Config.run`) on focus `M`
under context `K` reaches the terminal `t` under `K`, for ANY continuation fuel
`n`, in `F` extra steps. Induction on the eval fuel `fe`, `cases` on `M`; the
`letC`/`app` cases chain the IH through the PUSH+REDUCE step pair. -/
theorem run_evalD :
    ∀ fe M t, evalD fe M = some t →
      ∀ (K : Bang.EvalCtx) (n : Nat) (r : Result Val),
        Config.run n (K, t) = r → ∃ F, Config.run F (K, M) = r := by
  intro fe
  induction fe with
  | zero => intro M t h; simp [evalD] at h
  | succ fe ih =>
    intro M t h K n r hr
    cases M with
    | ret v =>
        simp only [evalD, Option.some.injEq] at h; subst h
        exact ⟨n, hr⟩
    | lam M =>
        simp only [evalD, Option.some.injEq] at h; subst h
        exact ⟨n, hr⟩
    | letC M N =>
        simp only [evalD] at h
        cases hM : evalD fe M with
        | none => rw [hM] at h; simp at h
        | some tM =>
          rw [hM] at h
          cases tM with
          | ret v =>
              simp only [Option.bind_some] at h
              -- PUSH (K, letC M N) ↦ (letF N :: K, M); REDUCE (letF N :: K, ret v) ↦ (K, N[v]).
              obtain ⟨F2, hF2⟩ := ih (Comp.subst v N) t h K n r hr
              have hstep : Config.run (F2+1) (Frame.letF N :: K, .ret v) = r := by
                simp only [Config.run, Source.step]; exact hF2
              obtain ⟨F1, hF1⟩ := ih M (.ret v) hM (Frame.letF N :: K) (F2+1) r hstep
              exact ⟨F1+1, by simp only [Config.run, Source.step]; exact hF1⟩
          | lam M2 => simp [Option.bind] at h
          | letC a b => simp [Option.bind] at h
          | force a => simp [Option.bind] at h
          | app a b => simp [Option.bind] at h
          | up a b d => simp [Option.bind] at h
          | handle a b => simp [Option.bind] at h
          | case a b d => simp [Option.bind] at h
          | split a b => simp [Option.bind] at h
          | unfold a => simp [Option.bind] at h
          | oom => simp [Option.bind] at h
          | wrong a => simp [Option.bind] at h
    | force a =>
        cases a with
        | vthunk M =>
            simp only [evalD] at h
            -- PUSH: Source.step (K, force (vthunk M)) = some (K, M).
            obtain ⟨F', hF'⟩ := ih M t h K n r hr
            exact ⟨F'+1, by simp only [Config.run, Source.step]; exact hF'⟩
        | vunit => simp [evalD] at h
        | vint x => simp [evalD] at h
        | vvar i => simp [evalD] at h
        | inl w => simp [evalD] at h
        | inr w => simp [evalD] at h
        | pair w1 w2 => simp [evalD] at h
        | fold w => simp [evalD] at h
    | app M v =>
        simp only [evalD] at h
        cases hM : evalD fe M with
        | none => rw [hM] at h; simp at h
        | some tM =>
          rw [hM] at h
          cases tM with
          | lam N =>
              simp only [Option.bind_some] at h
              -- PUSH (K, app M v) ↦ (appF v :: K, M); REDUCE (appF v :: K, lam N) ↦ (K, N[v]).
              obtain ⟨F2, hF2⟩ := ih (Comp.subst v N) t h K n r hr
              have hstep : Config.run (F2+1) (Frame.appF v :: K, .lam N) = r := by
                simp only [Config.run, Source.step]; exact hF2
              obtain ⟨F1, hF1⟩ := ih M (.lam N) hM (Frame.appF v :: K) (F2+1) r hstep
              exact ⟨F1+1, by simp only [Config.run, Source.step]; exact hF1⟩
          | ret w => simp [Option.bind] at h
          | letC a b => simp [Option.bind] at h
          | force a => simp [Option.bind] at h
          | app a b => simp [Option.bind] at h
          | up a b d => simp [Option.bind] at h
          | handle a b => simp [Option.bind] at h
          | case a b d => simp [Option.bind] at h
          | split a b => simp [Option.bind] at h
          | unfold a => simp [Option.bind] at h
          | oom => simp [Option.bind] at h
          | wrong a => simp [Option.bind] at h
    | up a b d => simp [evalD] at h
    | handle a b => simp [evalD] at h
    | case a b d => simp [evalD] at h
    | split a b => simp [evalD] at h
    | unfold a => simp [evalD] at h
    | oom => simp [evalD] at h
    | wrong a => simp [evalD] at h

/-- **The D1-A bridge** (headline): when `evalD` says a closed computation returns
`v`, the kernel's verified `Source.eval` agrees (`.done v`). Ties the calculated
machine to the type-safety reference (invariant #1) — `Source.eval`'s `type_safety`
now backs `evalD`'s `ret`-results. Pure spine; handlers/ADT elim later. -/
theorem evalD_agrees_source (f : Nat) (M : Comp) (v : Val) (h : evalD f M = some (.ret v)) :
    ∃ F, Source.eval F M = Result.done v := by
  have hbase : Config.run 1 ([], .ret v) = Result.done v := by simp only [Config.run]
  obtain ⟨F, hF⟩ := run_evalD f M (.ret v) h [] 1 (Result.done v) hbase
  exact ⟨F, hF⟩

/-- Bridge witnessed concretely: `(λ.ret #0) 5` — `evalD` returns `ret 5` AND
`Source.eval` reaches `.done 5`. The two semantics agree. -/
example :
    let M := Comp.app (.lam (.ret (.vvar 0))) (.vint 5)
    evalD 5 M = some (.ret (.vint 5)) ∧ Source.eval 5 M = Result.done (.vint 5) := by
  refine ⟨by rfl, by rfl⟩

end Bang.CalcVM
