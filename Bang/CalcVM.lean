import Bang.Operational

/-!
# CalcVM — the ◊3 graded-CBPV calculated machine (pure CBPV spine)

The Bahr–Hutton calculation (ADR-0016, ADR-0017; invariant #4) ported ONCE to
the new graded-CBPV `Comp`/`Val` (`Bang.Core`), replacing the K2 `Calc*.lean`
matrix over the old free-monad `Expr`/`Value`.

This file lands the **pure CBPV spine** (`ret` · `letC` · `force`/`vthunk` ·
`lam` · `app`) PLUS **deep-handler INSTALL** (`handle`) — the calculated machine,
`compile_correct`, AND the **`evalD ≡ Source.eval` bridge** (D1-A) over all of it.
The handler **abort/dispatch** (an `up` raising to its handler, the THROW-jump) is
sub-step 2; the ADT eliminators (`case`/`split`/`unfold`) and the full diff-test
battery are later increments. Nothing here is `sorry`/`axiom`.

### Effects: two-part `Outcome` + (A) explicit HANDLE-frame (throws-only, D2)

`evalD` returns an `Outcome` = `term` (normal terminal) | `raised` (an `up` en
route to its handler) — the denotational big-step exception shape (k2-playbook
§Effects); `letC`/`app` short-circuit on `raised`, `handle` catches it. The
machine installs handlers with explicit **`MARK`/`UNMARK` frames** (shape (A),
chosen over (B) defunctionalized continuations): throws are zero-shot (abort
DISCARDS the continuation), so (B)'s resumption capture is unused — `MARK` is a
THROW-jump target, mirroring the kernel's `splitAt`/`dispatch`, which keeps the
bridge's `up` case a tight `THROW ↔ dispatch` correspondence. (A) is the
**throws-only shape, not the final one**: resumptive handlers (state-resume
ADR-0025, multi-shot ADR-0015) — the reification frontier — will need (B) when
the machine must capture/resume a continuation. This sub-step lands INSTALL only:
`MARK`/`UNMARK` are identity on a normal return (handler-return = identity, Q6).

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
/-- A computation's big-step result: a normal `term`inal computation (`ret v` |
`lam M`), OR a `raised` operation propagating outward toward its handler (the
exception dimension; throws-only per D2). `letC`/`app` short-circuit on `raised`;
`handle` catches it. NOTE (staging): `raised` carries an unhandled `up`; this
sub-step INSTALLS handlers over non-raising bodies only — the abort/catch REDUCE
(THROW-jump) is sub-step 2. -/
inductive Outcome where
  | term   : Comp → Outcome                       -- normal terminal (ret v | lam M)
  | raised : Bang.EffectRow.Label → Bang.OpId → Val → Outcome   -- an `up` en route to its handler
  deriving Inhabited

def evalD : Nat → Comp → Option Outcome
  | 0,          _                  => none
  | Nat.succ _, .ret v             => some (.term (.ret v))
  | Nat.succ _, .lam M             => some (.term (.lam M))
  | Nat.succ f, .letC M N          =>
      (evalD f M).bind (fun o => match o with
        | .term (.ret v) => evalD f (Comp.subst v N)    -- M : F _ ⇒ terminal is `ret v`
        | .term _        => none                         -- ill-typed (letC of a lam)
        | .raised ℓ op w => some (.raised ℓ op w))       -- propagate the raise outward
  | Nat.succ f, .force (.vthunk M) => evalD f M           -- force∘thunk = run the closed body
  | Nat.succ f, .app M v           =>
      (evalD f M).bind (fun o => match o with
        | .term (.lam N) => evalD f (Comp.subst v N)     -- β: M ⇒ lam N, then N[v]
        | .term _        => none                          -- ill-typed (app of a non-lam)
        | .raised ℓ op w => some (.raised ℓ op w))        -- propagate the raise outward
  -- handle h M (INSTALL, sub-step 1): the body is a RETURNER (handle : F A), so its
  -- terminal is `ret v` and the handler-return is identity (Q6) ⇒ result is `term (ret v)`.
  -- A non-`ret` terminal is ill-typed (kernel handler-return fires only on `ret`) ⇒ `none`.
  -- sub-step 2 will CATCH a `raised ℓ "raise" w` here and yield `term (ret w)`.
  -- up ℓ op v: raise an operation toward its handler (the denotational `dispatch`).
  | Nat.succ _, .up ℓ op v         => some (.raised ℓ op v)
  -- handle h M: run the body; `ret v` passes through (handler-return = identity, Q6);
  -- a `raised` CAUGHT by `h` aborts to `term (ret w)` (the payload is the handled value);
  -- an uncaught `raised` is FORWARDED. A non-`ret` normal terminal is ill-typed ⇒ none.
  | Nat.succ f, .handle h M        =>
      (evalD f M).bind (fun o => match o with
        | .term (.ret v) => some (.term (.ret v))
        | .term _        => none
        | .raised ℓ' op' w =>
            -- CATCH is the zero-shot THROWS abort only (ADR-0023): a `throws ℓ` handler
            -- catches `(ℓ, "raise")` ⇒ yields the payload `term (ret w)`. Other handler kinds
            -- (state/transaction) RESUME — the reification frontier, out of D2 scope — so they
            -- do NOT catch here; the raise is forwarded. Matches `handlesOp`'s throws clause.
            match h with
            | .throws ℓ0 => if ℓ0 = ℓ' ∧ op' = "raise" then some (.term (.ret w))
                            else some (.raised ℓ' op' w)
            | _          => some (.raised ℓ' op' w))
  | _,          _                  => none                -- out of scope (ADT elim)

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
  -- handler frames (deep handlers, throws-only, ADR-0023 abort). `MARK h` installs the
  -- handler boundary (records the OUTER continuation to resume on abort); `UNMARK` pops
  -- it (handler-return = identity, Q6); `THROW ℓ op v` unwinds to the nearest catching
  -- `MARK`, DISCARDING the inner continuation (zero-shot abort) — the `splitAt`/`dispatch`
  -- analog (shape (A), CalcEff template).
  | MARK   : Handler → List Instr → Instr  -- install handler + the POST-handle resume code (abort target)
  | UNMARK : Instr
  | THROW  : Bang.EffectRow.Label → Bang.OpId → Val → Instr
  deriving Inhabited

abbrev Code  := List Instr
/-- The machine stack holds *terminal computations* (`ret v` / `lam M`) — the
shared value representation both `evalD` and `exec` produce, keeping correctness a
plain equality (no logical relation; k2-playbook §2). -/
abbrev Stack := List Comp

/-- A saved handler frame: the handler + the OUTER continuation (`Code` × `Stack`) to
resume on a zero-shot abort (= the kernel's `Kₒ`). The inner continuation between the
`up` and the `MARK` is DISCARDED on abort (throws are zero-shot), so it is NOT saved. -/
structure HFrame where
  handler    : Handler
  savedCode  : Code
  savedStack : Stack

abbrev HStack := List HFrame

def compile : Comp → Code → Code
  | .ret v,             c => Instr.RET v :: c
  | .lam M,             c => Instr.LAMI M :: c
  | .letC M N,          c => compile M (Instr.SUBST N :: c)
  | .force (.vthunk M), c => compile M c
  | .app M v,           c => compile M (Instr.APP v :: c)
  | .handle h M,        c => Instr.MARK h c :: compile M (Instr.UNMARK :: c)
  | .up ℓ op v,         c => Instr.THROW ℓ op v :: c   -- the `c` (inner cont) is discarded on abort
  | _,                  c => c               -- out of scope: emit nothing (residual, ADT elim)

/-- Find the nearest **throws** frame catching `(ℓ, op)`: return its saved OUTER
continuation (`savedCode`, `savedStack`), discarding the inner frames (zero-shot
abort). `none` = uncaught (no catching `throws` frame). The `splitAt`/`dispatch`
analog; PURE (no `exec` arg) so `exec` stays structurally recursive (CalcEff §THROW).

**THROWS-ONLY (D2, ADR-0023/0025):** the THROW-abort fires ONLY for a `throws`
handler — i.e. `handler = throws ℓ0` with `ℓ0 = ℓ ∧ op = "raise"`. `state`/
`transaction` frames RESUME (the reification frontier, deferred) so they do NOT
catch a THROW here — they are SKIPPED by the unwind. This ALIGNS `unwindFind` with
`evalD`'s `handle`-catch (throws-only) and the kernel's zero-shot abort, so a
non-throws (state/transaction) program never has the machine THROW-abort while
`evalD` forwards. A `MARK` may still carry any `Handler` (forward-compat for when
resumptive handlers land), but only `throws` frames are abort targets. -/
def unwindFind : Bang.EffectRow.Label → Bang.OpId → HStack → Option (Code × Stack × HStack)
  | _, _, []        => none
  | ℓ, op, fr :: hs =>
      match fr.handler with
      | .throws ℓ0 => if ℓ0 = ℓ ∧ op = "raise" then some (fr.savedCode, fr.savedStack, hs)
                      else unwindFind ℓ op hs
      | _          => unwindFind ℓ op hs   -- state/transaction RESUME — skip (deferred)

/-- The machine. Structurally recursive on the fuel (k2-playbook §3); `SUBST`/`APP`
re-enter `compile` on the substituted body, `THROW` jumps via the pure `unwindFind`
(both direct recursive calls — structural). Carries an `HStack` of installed
handlers (deep dispatch). -/
def exec : Nat → Code → Stack → HStack → Option Stack
  | 0,          _,                  _, _  => none
  | Nat.succ _, [],                 s, _  => some s
  | Nat.succ f, Instr.RET v :: c,   s, hs => exec f c (.ret v :: s) hs
  | Nat.succ f, Instr.LAMI M :: c,  s, hs => exec f c (.lam M :: s) hs
  | Nat.succ f, Instr.SUBST N :: c, s, hs =>
      match s with
      | .ret v :: s' => exec f (compile (Comp.subst v N) c) s' hs
      | _            => none
  | Nat.succ f, Instr.APP v :: c, s, hs =>
      match s with
      | .lam N :: s' => exec f (compile (Comp.subst v N) c) s' hs
      | _            => none
  -- MARK installs: record the OUTER continuation (this `c`, `s`) to resume on abort.
  | Nat.succ f, Instr.MARK h cr :: c, s, hs =>
      exec f c s ({ handler := h, savedCode := cr, savedStack := s } :: hs)
  -- UNMARK pops on normal return (handler-return = identity, Q6).
  | Nat.succ f, Instr.UNMARK :: c, s, hs =>
      match hs with
      | _ :: hs' => exec f c s hs'
      | []       => none
  -- THROW unwinds to the nearest catching MARK, DISCARDING the inner continuation:
  -- resume its saved OUTER continuation with `ret v` pushed (abort yields the payload).
  | Nat.succ f, Instr.THROW ℓ op v :: _, _, hs =>
      match unwindFind ℓ op hs with
      | some (c', s', hs') => exec f c' (.ret v :: s') hs'   -- ABORT to (Kₒ, ret v), frame popped
      | none               => none                            -- uncaught = stuck

/-! ## The calculation is correct (proven) -/

/-- Fuel monotonicity, one step (k2-playbook §2 bedrock): more fuel never changes a
`some`. Induction on fuel, `cases` on the head instruction; `SUBST`/`APP`'s nested
stack-match resolves the same way. -/
theorem exec_succ : ∀ f c s hs r, exec f c s hs = some r → exec (f+1) c s hs = some r := by
  intro f
  induction f with
  | zero => intro c s hs r h; simp [exec] at h
  | succ f ih =>
    intro c s hs r h
    cases c with
    | nil => simpa [exec] using h
    | cons i c =>
      cases i with
      | RET v => simp only [exec] at h ⊢; exact ih _ _ _ _ h
      | LAMI M => simp only [exec] at h ⊢; exact ih _ _ _ _ h
      | SUBST N =>
        simp only [exec] at h ⊢
        cases s with
        | nil => simp at h
        | cons hd s' => cases hd with
          | ret v => simp only [] at h ⊢; exact ih _ _ _ _ h
          | _ => simp at h
      | APP v =>
        simp only [exec] at h ⊢
        cases s with
        | nil => simp at h
        | cons hd s' => cases hd with
          | lam N => simp only [] at h ⊢; exact ih _ _ _ _ h
          | _ => simp at h
      | MARK hh => simp only [exec] at h ⊢; exact ih _ _ _ _ h
      | UNMARK =>
        simp only [exec] at h ⊢
        cases hs with
        | nil => simp at h
        | cons hd hs' => simp only [] at h ⊢; exact ih _ _ _ _ h
      | THROW ℓ op v =>
        simp only [exec] at h ⊢
        cases hu : unwindFind ℓ op hs with
        | none => rw [hu] at h; simp at h
        | some cs => obtain ⟨c', s', hs'⟩ := cs; rw [hu] at h; exact ih _ _ _ _ h

/-- Fuel monotonicity, `≤` (k2-playbook §2): bump any sub-fuel to a common value. -/
theorem exec_mono : ∀ f g c s hs r, f ≤ g → exec f c s hs = some r → exec g c s hs = some r := by
  intro f g c s hs r hle h
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ ih

/-- The machine outcome of a `raised ℓ op v` hitting handler stack `hs`: unwind to
the nearest catching frame and resume its saved continuation with `ret v` pushed
(the abort), or `none` (uncaught). Factored out of `exec`'s THROW arm so the two-part
`sim` can target it (CalcEff §throwOutcome). -/
def throwOutcome (F : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Val)
    (hs : HStack) : Option Stack :=
  match unwindFind ℓ op hs with
  | some (c', s', hs') => exec F c' (.ret v :: s') hs'
  | none               => none

/-- (★) the **two-part** simulation (k2-playbook §Effects): a `term` part (the
machine reaches the result normally) AND a `raised` part (the machine THROWs to its
handler). Forward to a concrete `some r`, fuels aligned via `exec_mono`. One
conjunction, induction on the eval fuel `fe`. The `handle` case is the crux: a
body that RAISES and is CAUGHT links `evalD`'s catch to the machine's THROW-jump
into the MARK frame — the `THROW ↔ dispatch` correspondence. -/
theorem sim : ∀ fe,
    (∀ M t, evalD fe M = some (.term t) →
      ∀ c s hs F r, exec F c (t :: s) hs = some r →
        ∃ F', exec F' (compile M c) s hs = some r)
    ∧ (∀ M ℓ op v, evalD fe M = some (.raised ℓ op v) →
      ∀ c s hs F r, throwOutcome F ℓ op v hs = some r →
        ∃ F', exec F' (compile M c) s hs = some r) := by
  intro fe
  induction fe with
  | zero =>
      exact ⟨fun M t h => by simp [evalD] at h, fun M ℓ op v h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M t h c s hs F r hr
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Outcome.term.injEq] at h; subst h
          exact ⟨F+1, by simp only [compile, exec]; exact hr⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Outcome.term.injEq] at h; subst h
          exact ⟨F+1, by simp only [compile, exec]; exact hr⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .term (.ret v), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F1, hF1⟩ := ihT (Comp.subst v N) t h c s hs F r hr
                have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v :: s) hs = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := ihT M (.ret v) hM (Instr.SUBST N :: c) s hs (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | .term (.lam M2), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
            | .raised ℓ op w, h =>
                -- letC propagates a raise: evalD (letC M N) = raised ⇒ h : raised = term, absurd
                simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨F', hF'⟩ := ihT M t h c s hs F r hr
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
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .term (.lam N), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F1, hF1⟩ := ihT (Comp.subst v N) t h c s hs F r hr
                have hstep : exec (F1+1) (Instr.APP v :: c) (.lam N :: s) hs = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := ihT M (.lam N) hM (Instr.APP v :: c) s hs (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | .term (.ret w), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
            | .raised ℓ op w, h => simp [Option.bind] at h
      | up ℓ op v => simp [evalD] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .term (.ret v), h =>
                -- body returns normally: MARK installs, UNMARK pops, identity.
                simp only [Option.bind_some, Option.some.injEq, Outcome.term.injEq] at h
                subst h
                obtain ⟨F1, hF1⟩ := ihT M (.ret v) hM (Instr.UNMARK :: c) s
                  ({ handler := h0, savedCode := c, savedStack := s } :: hs) (F+1) r
                  (by simp only [exec]; exact hr)
                refine ⟨F1+1, ?_⟩
                simp only [compile, exec]; exact hF1
            | .term (.lam M2), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
            | .raised ℓ' op' w, h =>
                -- body RAISES; CAUGHT only by a THROWS h0 on (ℓ', "raise"); else forwarded (absurd in term mode).
                cases h0 with
                | throws ℓ0 =>
                    by_cases hc : ℓ0 = ℓ' ∧ op' = "raise"
                    · -- caught: h reduces to some (term (ret w)) = some (term t) ⇒ t = ret w
                      simp only [Option.bind_some, if_pos hc, Option.some.injEq, Outcome.term.injEq] at h
                      subst h
                      obtain ⟨rfl, rfl⟩ := hc
                      -- machine: M raises ⇒ THROW into the MARK (throws ℓ0) frame (the unwind catches
                      -- a throws frame on (ℓ0, "raise")) ⇒ abort to (savedCode = c, savedStack = s)
                      -- with ret w pushed = hr.
                      have hthrow : throwOutcome F ℓ0 "raise" w
                          ({ handler := Handler.throws ℓ0, savedCode := c, savedStack := s } :: hs)
                          = some r := by
                        simp only [throwOutcome, unwindFind, and_self, if_true]; exact hr
                      obtain ⟨F1, hF1⟩ := ihR M ℓ0 "raise" w hM (Instr.UNMARK :: c) s
                        ({ handler := Handler.throws ℓ0, savedCode := c, savedStack := s } :: hs)
                        F r hthrow
                      refine ⟨F1+1, ?_⟩
                      simp only [compile, exec]; exact hF1
                    · -- not caught: handle yields raised ⇒ h : raised = term, absurd
                      simp [Option.bind_some, if_neg hc] at h
                | state ℓ0 s0 => simp [Option.bind_some] at h
                | transaction ℓ0 Θ => simp [Option.bind_some] at h
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
    · -- RAISED PART
      intro M ℓ op v h c s hs F r hr
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | up ℓ2 op2 v2 =>
          -- evalD (up …) = raised ℓ2 op2 v2 = raised ℓ op v ; compile = THROW ℓ op v :: c
          simp only [evalD, Option.some.injEq, Outcome.raised.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          -- exec (F+1) (THROW ℓ op v :: c) s hs = throwOutcome via unwindFind = hr
          refine ⟨F+1, ?_⟩
          simp only [compile, exec]
          -- goal = throwOutcome F ℓ op v hs = some r = hr
          exact hr
      | letC M N =>
          -- raise comes from M (propagated) since N runs only after ret.
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .raised ℓ' op' w, h =>
                simp only [Option.bind_some, Option.some.injEq, Outcome.raised.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                -- machine: M raises under (SUBST N :: c); the THROW propagates through hs unchanged.
                obtain ⟨F1, hF1⟩ := ihR M ℓ' op' w hM (Instr.SUBST N :: c) s hs F r hr
                exact ⟨F1, by simpa [compile] using hF1⟩
            | .term (.ret v0), h =>
                -- M returns; then evalD (letC) = evalD (N[v0]) which raised ⇒ recurse on N[v0].
                simp only [Option.bind_some] at h
                obtain ⟨F1, hF1⟩ := ihR (Comp.subst v0 N) ℓ op v h c s hs F r hr
                -- need: machine runs M to ret v0 (SUBST), then N[v0] raises. Use ihT on M then chain.
                have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v0 :: s) hs = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := ihT M (.ret v0) hM (Instr.SUBST N :: c) s hs (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | .term (.lam a), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨F', hF'⟩ := ihR M ℓ op v h c s hs F r hr
              exact ⟨F', by simpa only [compile] using hF'⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | app M v0 =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .raised ℓ' op' w, h =>
                simp only [Option.bind_some, Option.some.injEq, Outcome.raised.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨F1, hF1⟩ := ihR M ℓ' op' w hM (Instr.APP v0 :: c) s hs F r hr
                exact ⟨F1, by simpa [compile] using hF1⟩
            | .term (.lam N), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F1, hF1⟩ := ihR (Comp.subst v0 N) ℓ op v h c s hs F r hr
                have hstep : exec (F1+1) (Instr.APP v0 :: c) (.lam N :: s) hs = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := ihT M (.lam N) hM (Instr.APP v0 :: c) s hs (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | .term (.ret w), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .raised ℓ' op' w, h =>
                -- body raises; FORWARDED iff h0 doesn't CATCH-as-throws (non-throws ⇒ always
                -- forwarded — RESUME is deferred; throws ⇒ forwarded unless (ℓ0, "raise") matches).
                -- THROWS-ONLY unwind: the machine SKIPS state/transaction frames, so the
                -- state-divergence is GONE (those subcases are "never catch" — closed cleanly, no sorry).
                -- One `cases h0`: extract the raise equality from `h` (already evalD-unfolded), and the
                -- machine's `unwindFind`-skip; then a uniform tail through `ihR`.
                simp only [Option.bind_some] at h
                cases h0 with
                | throws ℓ0 =>
                    -- forwarded ⇒ ¬(ℓ0 = ℓ' ∧ op' = "raise"); both evalD and unwindFind skip on that.
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp [if_pos hk] at h   -- caught ⇒ term, but h says raised: absurd
                    · simp only [if_neg hk, Option.some.injEq, Outcome.raised.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      have hfwd : throwOutcome F ℓ' op' w
                          ({ handler := Handler.throws ℓ0, savedCode := c, savedStack := s } :: hs)
                          = some r := by
                        simp only [throwOutcome, unwindFind, if_neg hk]; exact hr
                      obtain ⟨F1, hF1⟩ := ihR M ℓ' op' w hM (Instr.UNMARK :: c) s
                        ({ handler := Handler.throws ℓ0, savedCode := c, savedStack := s } :: hs) F r hfwd
                      exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | state ℓ0 s0 =>
                    -- non-throws: evalD forwards via the `_` arm; unwindFind skips a non-throws frame.
                    simp only [Option.some.injEq, Outcome.raised.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have hfwd : throwOutcome F ℓ' op' w
                        ({ handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s } :: hs)
                        = some r := by
                      simp only [throwOutcome, unwindFind]; exact hr
                    obtain ⟨F1, hF1⟩ := ihR M ℓ' op' w hM (Instr.UNMARK :: c) s
                      ({ handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s } :: hs) F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | transaction ℓ0 Θ =>
                    simp only [Option.some.injEq, Outcome.raised.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have hfwd : throwOutcome F ℓ' op' w
                        ({ handler := Handler.transaction ℓ0 Θ, savedCode := c, savedStack := s } :: hs)
                        = some r := by
                      simp only [throwOutcome, unwindFind]; exact hr
                    obtain ⟨F1, hF1⟩ := ihR M ℓ' op' w hM (Instr.UNMARK :: c) s
                      ({ handler := Handler.transaction ℓ0 Θ, savedCode := c, savedStack := s } :: hs) F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
            | .term (.ret v0), h =>
                -- body returns normally ⇒ handle returns term, not raised ⇒ absurd
                simp [Option.bind] at h
            | .term (.lam a), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h


/-- Headline: compiling a closed computation and running it on the empty stack
yields exactly `[t]` where `evalD n M = some t` (the convergent pure spine).
Pure-spine ◊3 increment — the `compile_correct` analogue of `Bang.Calc`. -/
theorem compile_correct (n : Nat) (M : Comp) (t : Comp) (h : evalD n M = some (.term t)) :
    ∃ F, exec F (compile M []) [] [] = some [t] := by
  have hbase : exec 1 [] (t :: []) [] = some [t] := by simp [exec]
  obtain ⟨F, hF⟩ := (sim n).1 M t h [] [] [] 1 [t] hbase
  exact ⟨F, hF⟩

/-! ## Diff-test seeds (PATH-calcvm-port Unit 4)

The Lean-side replacement for the deleted TS differential harness: assert the
machine reproduces `evalD` on curated programs by `rfl`. First grains of the
`native_decide` battery the ◊3 gate will grow. -/

/-- `(λ. ret #0) 5` ⇒ `[ret 5]` — β through `LAMI`/`APP`. -/
example :
    exec 10 (compile (.app (.lam (.ret (.vvar 0))) (.vint 5)) []) [] [] = some [.ret (.vint 5)] := by
  rfl

/-- `let x = (λ.ret #0) 5 in ret x` ⇒ `[ret 5]` — `SUBST` over an applied lambda. -/
example :
    exec 12 (compile (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0))) []) [] []
      = some [.ret (.vint 5)] := by
  rfl

/-- `force (thunk (ret 9))` ⇒ `[ret 9]` — `force`∘`vthunk` collapses to the body. -/
example :
    exec 10 (compile (.force (.vthunk (.ret (.vint 9)))) []) [] [] = some [.ret (.vint 9)] := by
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

/-! ## The D1-A bridge: `evalD ≡ Source.eval` (two-part, with handlers)

`run_evalD` is the **two-part** big/small-step simulation: a `term` part (M runs to
its terminal under context `K`) AND a `raised` part (M raises an op the kernel
`dispatch`es — the `THROW ↔ dispatch` correspondence). Subst-vs-subst ⇒ a plain
simulation, no cross-rep logical relation (the (b) payoff). `evalD_agrees_source`
(`K = []`, `ret v`) is the headline tying the calculated machine to the kernel's
type-safety-verified `Source.eval`.

### `splitAt`/`dispatch` commutation (throws-only, D2)

A throws-abort resumes the OUTER continuation `Kₒ` and DISCARDS the inner prefix
`Kᵢ`; prepending a non-handler frame (`letF`/`appF`) only grows that discarded
`Kᵢ`, so the dispatch result is unchanged. Conditioned on `splitAt` finding a
`throws` handler (the only catching kind in D2). Facts about the imported
`Bang.splitAt`/`dispatch` (read-only); CANDIDATES TO PROMOTE to `Operational.lean`'s
splitAt API if the kernel side later needs them (single-source-of-truth, deferred). -/

theorem dispatch_letF (N : Comp) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId)
    (v : Val) {Kᵢ Kₒ : Bang.EvalCtx} {ℓ0 : Bang.EffectRow.Label}
    (hs : Bang.splitAt K ℓ op = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    Bang.dispatch (Frame.letF N :: K) ℓ op v = Bang.dispatch K ℓ op v := by
  simp only [Bang.dispatch, Bang.splitAt, hs, Option.map_some, Option.bind_some, Bang.dispatchOn]

theorem dispatch_appF (w : Val) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId)
    (v : Val) {Kᵢ Kₒ : Bang.EvalCtx} {ℓ0 : Bang.EffectRow.Label}
    (hs : Bang.splitAt K ℓ op = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    Bang.dispatch (Frame.appF w :: K) ℓ op v = Bang.dispatch K ℓ op v := by
  simp only [Bang.dispatch, Bang.splitAt, hs, Option.map_some, Option.bind_some, Bang.dispatchOn]

/-- A `raise` propagating PAST a NON-catching `handleF h0` frame: same `dispatch` outcome.
`splitAt` skips the frame (the `else` branch), only prepending `handleF h0` to the discarded
inner prefix `Kᵢ` — and `dispatchOn` on a `throws` handler DISCARDS `Kᵢ`, so the `Kₒ`-resume is
unchanged. Conditioned on `handlesOp h0 ℓ op = false` (the unwind/dispatch skip criterion). -/
theorem dispatch_handleF_skip (h0 : Handler) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label)
    (op : Bang.OpId) (v : Val) {Kᵢ Kₒ : Bang.EvalCtx} {ℓ0 : Bang.EffectRow.Label}
    (hnc : Bang.handlesOp h0 ℓ op = false)
    (hs : Bang.splitAt K ℓ op = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    Bang.dispatch (Frame.handleF h0 :: K) ℓ op v = Bang.dispatch K ℓ op v := by
  simp only [Bang.dispatch, Bang.splitAt, hnc, Bool.false_eq_true, if_false, hs, Option.map_some,
    Option.bind_some, Bang.dispatchOn]

/-- The kernel-side outcome of a `raised ℓ op v` reaching context `K`: it's exactly
running the machine from the `up` config (`Source.step (K, up ℓ op v) = dispatch …`),
so DEFINITIONALLY `Config.run (n+1) (K, up ℓ op v)`. The `Config.run` analog of the
machine's `throwOutcome` — the two-part bridge's raised target. -/
def dispatchRun (n : Nat) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId)
    (v : Val) : Bang.Result Val := Bang.Config.run (n+1) (K, .up ℓ op v)

/-- `splitAt` returns a handler that actually catches `(ℓ, op)` (induction on `K`). -/
theorem splitAt_handles {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {h : Handler},
      Bang.splitAt K ℓ op = some (Kᵢ, h, Kₒ) → Bang.handlesOp h ℓ op = true := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hs; simp [Bang.splitAt] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ h hs
    cases fr with
    | handleF h0 =>
        simp only [Bang.splitAt] at hs
        by_cases hc : Bang.handlesOp h0 ℓ op = true
        · rw [if_pos hc] at hs; simp only [Option.some.injEq] at hs
          obtain ⟨_, rfl, _⟩ := hs; exact hc
        · rw [if_neg hc] at hs
          cases hsp : Bang.splitAt K ℓ op with
          | none => rw [hsp] at hs; simp at hs
          | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                      simp only [Option.map_some, Option.some.injEq] at hs
                      obtain ⟨_, rfl, _⟩ := hs; exact ih hsp
    | letF N =>
        simp only [Bang.splitAt] at hs
        cases hsp : Bang.splitAt K ℓ op with
        | none => rw [hsp] at hs; simp at hs
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                    simp only [Option.map_some, Option.some.injEq] at hs
                    obtain ⟨_, rfl, _⟩ := hs; exact ih hsp
    | appF w =>
        simp only [Bang.splitAt] at hs
        cases hsp : Bang.splitAt K ℓ op with
        | none => rw [hsp] at hs; simp at hs
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                    simp only [Option.map_some, Option.some.injEq] at hs
                    obtain ⟨_, rfl, _⟩ := hs; exact ih hsp

/-- For the `raise` op only `throws` catches, so `splitAt` returns a `throws` handler. -/
theorem splitAt_throws {K Kᵢ Kₒ : Bang.EvalCtx} {ℓ : Bang.EffectRow.Label} {h : Handler}
    (hs : Bang.splitAt K ℓ "raise" = some (Kᵢ, h, Kₒ)) : ∃ ℓ0, h = Handler.throws ℓ0 := by
  have hh := splitAt_handles hs
  cases h with
  | throws ℓ0 => exact ⟨ℓ0, rfl⟩
  | state ℓ0 s => simp [Bang.handlesOp] at hh
  | transaction ℓ0 Θ => simp [Bang.handlesOp] at hh

/-- A `raise` propagating under a `letF` frame: same `Config.run` outcome (the abort
discards the inner prefix the frame grows). Caught ⇒ throws (`splitAt_throws`) ⇒
`dispatch_letF`; uncaught ⇒ both stuck. -/
theorem dispatchRun_letF (n : Nat) (N : Comp) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label)
    (v : Val) : dispatchRun n (Frame.letF N :: K) ℓ "raise" v = dispatchRun n K ℓ "raise" v := by
  simp only [dispatchRun, Bang.Config.run, Source.step]
  cases hsp : Bang.splitAt K ℓ "raise" with
  | none => simp only [Bang.dispatch, Bang.splitAt, hsp, Option.map_none, Option.bind_none]
  | some t =>
      obtain ⟨Kᵢ, h, Kₒ⟩ := t
      obtain ⟨ℓ0, rfl⟩ := splitAt_throws hsp
      rw [dispatch_letF N K ℓ "raise" v hsp]

/-- A `raise` propagating under an `appF` frame: same outcome (as `dispatchRun_letF`). -/
theorem dispatchRun_appF (n : Nat) (w : Val) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label)
    (v : Val) : dispatchRun n (Frame.appF w :: K) ℓ "raise" v = dispatchRun n K ℓ "raise" v := by
  simp only [dispatchRun, Bang.Config.run, Source.step]
  cases hsp : Bang.splitAt K ℓ "raise" with
  | none => simp only [Bang.dispatch, Bang.splitAt, hsp, Option.map_none, Option.bind_none]
  | some t =>
      obtain ⟨Kᵢ, h, Kₒ⟩ := t
      obtain ⟨ℓ0, rfl⟩ := splitAt_throws hsp
      rw [dispatch_appF w K ℓ "raise" v hsp]

/-- A `raise` propagating PAST a NON-catching `handleF h0` frame: same `Config.run` outcome.
The forwarded case of the bridge's `handle` raised arm (`dispatchRun_letF`/`appF` analog for the
non-catching handler frame). Caught-below ⇒ `dispatch_handleF_skip`; uncaught ⇒ both stuck. -/
theorem dispatchRun_handleF_skip (n : Nat) (h0 : Handler) (K : Bang.EvalCtx)
    (ℓ : Bang.EffectRow.Label) (v : Val) (hnc : Bang.handlesOp h0 ℓ "raise" = false) :
    dispatchRun n (Frame.handleF h0 :: K) ℓ "raise" v = dispatchRun n K ℓ "raise" v := by
  simp only [dispatchRun, Bang.Config.run, Source.step]
  cases hsp : Bang.splitAt K ℓ "raise" with
  | none =>
      simp only [Bang.dispatch, Bang.splitAt, hnc, Bool.false_eq_true, if_false, hsp,
        Option.map_none, Option.bind_none]
  | some t =>
      obtain ⟨Kᵢ, h, Kₒ⟩ := t
      obtain ⟨ℓ0, rfl⟩ := splitAt_throws hsp
      rw [dispatch_handleF_skip h0 K ℓ "raise" v hnc hsp]

/-- (★bridge) the **two-part** `evalD ≡ Source.eval` simulation: a `term` part (M
runs to its terminal under K) AND a `raised` part (M raises, dispatched by the
kernel — the `THROW ↔ dispatch` correspondence). Subst-vs-subst, no cross-rep LR.
Induction on the eval fuel `fe`. -/
theorem run_evalD : ∀ fe,
    (∀ M t, evalD fe M = some (.term t) →
      ∀ (K : Bang.EvalCtx) (n : Nat) (r : Bang.Result Val),
        Bang.Config.run n (K, t) = r → ∃ F, Bang.Config.run F (K, M) = r)
    ∧ (∀ M ℓ v, evalD fe M = some (.raised ℓ "raise" v) →
      ∀ (K : Bang.EvalCtx) (n : Nat) (r : Bang.Result Val),
        dispatchRun n K ℓ "raise" v = r → ∃ F, Bang.Config.run F (K, M) = r) := by
  intro fe
  induction fe with
  | zero => exact ⟨fun M t h => by simp [evalD] at h, fun M ℓ v h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M t h K n r hr
      cases M with
      | ret v => simp only [evalD, Option.some.injEq, Outcome.term.injEq] at h; subst h; exact ⟨n, hr⟩
      | lam M => simp only [evalD, Option.some.injEq, Outcome.term.injEq] at h; subst h; exact ⟨n, hr⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .term (.ret v), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F2, hF2⟩ := ihT (Comp.subst v N) t h K n r hr
                have hstep : Bang.Config.run (F2+1) (Frame.letF N :: K, .ret v) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                obtain ⟨F1, hF1⟩ := ihT M (.ret v) hM (Frame.letF N :: K) (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | .term (.lam a), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
            | .raised ℓ op w, h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨F', hF'⟩ := ihT M t h K n r hr
              exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩
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
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .term (.lam N), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F2, hF2⟩ := ihT (Comp.subst v N) t h K n r hr
                have hstep : Bang.Config.run (F2+1) (Frame.appF v :: K, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                obtain ⟨F1, hF1⟩ := ihT M (.lam N) hM (Frame.appF v :: K) (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | .term (.ret w), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
            | .raised ℓ op w, h => simp [Option.bind] at h
      | up ℓ op v => simp [evalD] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .term (.ret v), h =>
                simp only [Option.bind_some, Option.some.injEq, Outcome.term.injEq] at h
                subst h
                have hstep : Bang.Config.run (n+1) (Frame.handleF h0 :: K, .ret v) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hr
                obtain ⟨F1, hF1⟩ := ihT M (.ret v) hM (Frame.handleF h0 :: K) (n+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | .term (.lam a), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
            | .raised ℓ' op' w, h =>
                -- body raises; CAUGHT only by a THROWS h0 on (ℓ', "raise") ⇒ term (ret w); else
                -- forwarded ⇒ raised (absurd in the term part). Mirrors `evalD`'s throws-only catch.
                simp only [Option.bind_some] at h
                cases h0 with
                | throws ℓ0 =>
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · -- caught: handle yields term (ret w) = term t ⇒ t = ret w. Kernel: M raises to
                      -- (handleF (throws ℓ') :: K), dispatch ABORTS to (K, ret w) — matching hr.
                      simp only [if_pos hk, Option.some.injEq, Outcome.term.injEq] at h
                      subst h
                      obtain ⟨rfl, rfl⟩ := hk
                      have hd : dispatchRun n (Frame.handleF (Handler.throws ℓ0) :: K) ℓ0 "raise" w = r := by
                        simp only [dispatchRun, Bang.Config.run, Source.step, Bang.dispatch, Bang.splitAt,
                          Bang.handlesOp, beq_self_eq_true, Bool.and_true, Bang.dispatchOn]
                        simpa using hr
                      obtain ⟨F1, hF1⟩ := ihR M ℓ0 w hM (Frame.handleF (Handler.throws ℓ0) :: K) n r hd
                      exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                    · -- not caught (throws, wrong label/op): handle forwards ⇒ raised, but h says term: absurd
                      simp [if_neg hk] at h
                | state ℓ0 s => simp at h   -- non-throws forwards ⇒ raised, but h says term: absurd
                | transaction ℓ0 Θ => simp at h
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
    · -- RAISED PART
      intro M ℓ v h K n r hr
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | up ℓ2 op2 v2 =>
          simp only [evalD, Option.some.injEq, Outcome.raised.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          -- dispatchRun n K ℓ op v = Config.run (n+1) (K, up ℓ op v) DEFINITIONALLY ⇒ hr closes it.
          exact ⟨n+1, hr⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .raised ℓ' op' w, h =>
                simp only [Option.bind_some, Option.some.injEq, Outcome.raised.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                -- M raises under (letF N :: K); dispatch walks past letF to the same handler.
                obtain ⟨F1, hF1⟩ := ihR M ℓ' w hM (Frame.letF N :: K) n r (by
                  rw [dispatchRun_letF]; exact hr)
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | .term (.ret v0), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F1, hF1⟩ := ihR (Comp.subst v0 N) ℓ v h K n r hr
                have hstep : Bang.Config.run (F1+1) (Frame.letF N :: K, .ret v0) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF1
                obtain ⟨F2, hF2⟩ := ihT M (.ret v0) hM (Frame.letF N :: K) (F1+1) r hstep
                exact ⟨F2+1, by simp only [Bang.Config.run, Source.step]; exact hF2⟩
            | .term (.lam a), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨F', hF'⟩ := ihR M ℓ v h K n r hr
              exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | app M v0 =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .raised ℓ' op' w, h =>
                simp only [Option.bind_some, Option.some.injEq, Outcome.raised.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨F1, hF1⟩ := ihR M ℓ' w hM (Frame.appF v0 :: K) n r (by
                  rw [dispatchRun_appF]; exact hr)
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | .term (.lam N), h =>
                simp only [Option.bind_some] at h
                obtain ⟨F1, hF1⟩ := ihR (Comp.subst v0 N) ℓ v h K n r hr
                have hstep : Bang.Config.run (F1+1) (Frame.appF v0 :: K, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF1
                obtain ⟨F2, hF2⟩ := ihT M (.lam N) hM (Frame.appF v0 :: K) (F1+1) r hstep
                exact ⟨F2+1, by simp only [Bang.Config.run, Source.step]; exact hF2⟩
            | .term (.ret w), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases hM : evalD fe M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | .raised ℓ' op' w, h =>
                -- the headline raised part is op-fixed to "raise"; forwarding forces op' = "raise".
                -- evalD forwards (throws non-matching, or non-throws); kernel dispatch SKIPS h0 too,
                -- since `handlesOp h0 ℓ' "raise" = false` for every non-catching frame. One `cases h0`.
                simp only [Option.bind_some] at h
                cases h0 with
                | throws ℓ0 =>
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp [if_pos hk] at h   -- caught ⇒ term, but h says raised: absurd
                    · -- not caught: `obtain ⟨rfl,rfl,rfl⟩` keeps ℓ'/w (eliminates outer ℓ/v), op'→"raise".
                      simp only [if_neg hk, Option.some.injEq, Outcome.raised.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      have hne : ℓ0 ≠ ℓ' := fun he => hk ⟨he, rfl⟩
                      have hnc : Bang.handlesOp (Handler.throws ℓ0) ℓ' "raise" = false := by
                        simp [Bang.handlesOp, hne]
                      obtain ⟨F1, hF1⟩ := ihR M ℓ' w hM (Frame.handleF (Handler.throws ℓ0) :: K) n r (by
                        rw [dispatchRun_handleF_skip n (Handler.throws ℓ0) K ℓ' w hnc]; exact hr)
                      exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | state ℓ0 s =>
                    -- non-throws forwards (the `_` arm); op' forced to "raise" ⇒ handlesOp = false.
                    simp only [Option.some.injEq, Outcome.raised.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have hnc : Bang.handlesOp (Handler.state ℓ0 s) ℓ' "raise" = false := by
                      simp [Bang.handlesOp]
                    obtain ⟨F1, hF1⟩ := ihR M ℓ' w hM (Frame.handleF (Handler.state ℓ0 s) :: K) n r (by
                      rw [dispatchRun_handleF_skip n (Handler.state ℓ0 s) K ℓ' w hnc]; exact hr)
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | transaction ℓ0 Θ =>
                    simp only [Option.some.injEq, Outcome.raised.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have hnc : Bang.handlesOp (Handler.transaction ℓ0 Θ) ℓ' "raise" = false := by
                      simp [Bang.handlesOp]
                    obtain ⟨F1, hF1⟩ := ihR M ℓ' w hM (Frame.handleF (Handler.transaction ℓ0 Θ) :: K) n r (by
                      rw [dispatchRun_handleF_skip n (Handler.transaction ℓ0 Θ) K ℓ' w hnc]; exact hr)
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | .term (.ret v0), h => simp [Option.bind] at h
            | .term (.lam a), h => simp [Option.bind] at h
            | .term (.letC a b), h => simp [Option.bind] at h
            | .term (.force a), h => simp [Option.bind] at h
            | .term (.app a b), h => simp [Option.bind] at h
            | .term (.up a b d), h => simp [Option.bind] at h
            | .term (.handle a b), h => simp [Option.bind] at h
            | .term (.case a b d), h => simp [Option.bind] at h
            | .term (.split a b), h => simp [Option.bind] at h
            | .term (.unfold a), h => simp [Option.bind] at h
            | .term .oom, h => simp [Option.bind] at h
            | .term (.wrong a), h => simp [Option.bind] at h
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h

/-- **The D1-A bridge** (headline): when `evalD` says a closed computation returns
`v`, the kernel's verified `Source.eval` agrees (`.done v`). Ties the calculated
machine to the type-safety reference (invariant #1) — `Source.eval`'s `type_safety`
now backs `evalD`'s `ret`-results. Pure spine; handlers/ADT elim later. -/
theorem evalD_agrees_source (f : Nat) (M : Comp) (v : Val) (h : evalD f M = some (.term (.ret v))) :
    ∃ F, Source.eval F M = Result.done v := by
  have hbase : Config.run 1 ([], .ret v) = Result.done v := by simp only [Config.run]
  obtain ⟨F, hF⟩ := (run_evalD f).1 M (.ret v) h [] 1 (Result.done v) hbase
  exact ⟨F, hF⟩

/-- `handle`-install over a non-raising body: `handle (throws ℓ) (ret 7)` ⇒ `ret 7`
(handler-return = identity). Machine `MARK`/`UNMARK` are identity on normal return;
evalD and Source.eval agree. -/
example :
    let M := Comp.handle (.throws default) (.ret (.vint 7))
    evalD 5 M = some (.term (.ret (.vint 7)))
      ∧ exec 10 (compile M []) [] [] = some [.ret (.vint 7)]
      ∧ Source.eval 5 M = Result.done (.vint 7) := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- Bridge witnessed concretely: `(λ.ret #0) 5` — `evalD` returns `ret 5` AND
`Source.eval` reaches `.done 5`. The two semantics agree. -/
example :
    let M := Comp.app (.lam (.ret (.vvar 0))) (.vint 5)
    evalD 5 M = some (.term (.ret (.vint 5))) ∧ Source.eval 5 M = Result.done (.vint 5) := by
  refine ⟨by rfl, by rfl⟩

end Bang.CalcVM
