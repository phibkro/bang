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
battery are later increments. ADR-0031 (resumptive state) adds the store thread:
`evalD` services `get`/`put` inline, the machine RESUMES with a non-discarding `OP`,
and the `compile_correct` (`sim`) + `evalD ≡ Source.eval` (`run_evalD`) proofs are
both axiom-clean over the WHOLE state-resuming semantics — no `sorry`. The throws⊗state
nesting (an outer `put` before a caught inner raise) is handled: the abort keeps the
outer put (evalD-caught = the at-raise store `σ'`, machine-faithful).

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

/-! ## The state store (ADR-0031 D1): a 1:1 mirror of the active `state ℓ s` frames

`SStore` is the resumptive mechanism `evalD` threads (ADR-0031 D1). It is a **stack** of
`(label ↦ value)` bindings that mirrors the machine's active `state ℓ s` frames **1:1, in order**
(D3): `handle (state ℓ s) M` PUSHES `(ℓ, s)` for the dynamic extent of `M` and POPS it on exit;
`get` reads the nearest binding for `ℓ`; `put` UPDATES the nearest binding **in place** (NOT a
prepend — this exactly mirrors the machine's in-place `stateUpdate` on the HStack, so the store and
the HStack-state-projection stay structurally identical, which is what makes the bridge invariant a
direct correspondence rather than a representation translation). `∉ store` ⟺ no active `state`
frame for `ℓ` ⟹ the op propagates as a throws-path `raised`. -/
abbrev SStore := List (Bang.EffectRow.Label × Val)

/-- The nearest stored value for label `ℓ` (innermost binding wins — shadowing). -/
def SStore.get? (σ : SStore) (ℓ : Bang.EffectRow.Label) : Option Val :=
  (σ.find? (fun p => p.1 = ℓ)).map (·.2)

/-- UPDATE the nearest binding for `ℓ` **in place** (mirrors the machine's `stateUpdate`-put). If
`ℓ` is unbound the store is unchanged (source-unreachable: `put` only fires when a frame is active). -/
def SStore.put : SStore → Bang.EffectRow.Label → Val → SStore
  | [],            _, _ => []
  | (ℓ0, w) :: σ, ℓ, v => if ℓ0 = ℓ then (ℓ0, v) :: σ else (ℓ0, w) :: SStore.put σ ℓ v

/-- PUSH a fresh binding (a `handle (state ℓ s)` install). -/
def SStore.push (σ : SStore) (ℓ : Bang.EffectRow.Label) (v : Val) : SStore := (ℓ, v) :: σ

/-! ## The denotational source `evalD` (substitution, terminal-Comp, store-threaded)

Fuel-bounded, structurally recursive on the fuel (NO `termination_by`, so the
equations unfold under `simp`/`rw`; k2-playbook §3). `none` = stuck / out-of-fuel
/ out-of-scope (the partiality ⊥). `ret`/`lam` are terminal; `letC`/`app` sequence
through a sub-eval and substitute; `force (vthunk M)` runs the (closed) body.

**ADR-0031 D1 (store-thread):** `evalD` threads an `SStore` in and out. State ops
(`get`/`put` on a label with an active `state` frame) are serviced **inline** — they
never escape as `raised` — which is what dissolves the big-step "no continuation to
resume" difficulty: state is serviced *during* the recursive descent. `raised` is
**reserved for throws** after this ADR (D1). -/
/-- A computation's big-step result: a normal `term`inal computation (`ret v` |
`lam M`), OR a `raised` operation propagating outward toward its handler. After
ADR-0031, `raised` is the THROWS dimension only — state `get`/`put` are serviced
inline against the store and yield a `term`. `letC`/`app` short-circuit on `raised`;
a `throws` `handle` catches it. -/
inductive Outcome where
  | term   : Comp → Outcome                       -- normal terminal (ret v | lam M)
  | raised : Bang.EffectRow.Label → Bang.OpId → Val → Outcome   -- a throws-`up` en route to its handler
  deriving Inhabited

def evalD : Nat → SStore → Comp → Option (Outcome × SStore)
  | 0,          _, _               => none
  | Nat.succ _, σ, .ret v          => some (.term (.ret v), σ)
  | Nat.succ _, σ, .lam M          => some (.term (.lam M), σ)
  | Nat.succ f, σ, .letC M N       =>
      (evalD f σ M).bind (fun p => match p with
        | (.term (.ret v), σ') => evalD f σ' (Comp.subst v N)    -- M : F _ ⇒ terminal is `ret v`
        | (.term _, _)         => none                            -- ill-typed (letC of a lam)
        | (.raised ℓ op w, σ') => some (.raised ℓ op w, σ'))      -- propagate the raise outward
  | Nat.succ f, σ, .force (.vthunk M) => evalD f σ M              -- force∘thunk = run the closed body
  | Nat.succ f, σ, .app M v        =>
      (evalD f σ M).bind (fun p => match p with
        | (.term (.lam N), σ') => evalD f σ' (Comp.subst v N)     -- β: M ⇒ lam N, then N[v]
        | (.term _, _)         => none                            -- ill-typed (app of a non-lam)
        | (.raised ℓ op w, σ') => some (.raised ℓ op w, σ'))      -- propagate the raise outward
  -- up ℓ op v: a state `get`/`put` (ℓ has an active `state` frame in σ) is serviced
  -- INLINE — `get` returns the stored s, `put` threads s := v, both yield `term (ret …)`.
  -- An op on a label with NO active state frame (∉ σ) propagates as `raised` (the throws path).
  | Nat.succ _, σ, .up ℓ op v      =>
      match σ.get? ℓ with
      | some s =>
          if op = "get" then some (.term (.ret s), σ)              -- get: return stored s, σ unchanged
          else if op = "put" then some (.term (.ret .vunit), σ.put ℓ v)  -- put: thread s := v
          else some (.raised ℓ op v, σ)                            -- a non-state op on a state label (none here)
      | none => some (.raised ℓ op v, σ)                           -- no state frame ⇒ throws path
  -- handle h M: dispatch on the handler kind.
  --  · state ℓ s : push (ℓ ↦ s) for M's extent; on a normal `ret v` RESTORE the outer σ
  --    (lexical shadowing — D1); the handler-return is identity (Q6). A raise still forwards.
  --  · throws ℓ0 : CATCH a `raised (ℓ0, "raise")` ⇒ yield the payload `term (ret w)` (zero-shot
  --    abort, ADR-0023); else forward. State ops never reach here as `raised` (serviced inline).
  --  · transaction : forward (the list-heap fold-in is a follow-on increment, D4).
  | Nat.succ f, σ, .handle h M     =>
      match h with
      | .state ℓ s =>
          (evalD f (σ.push ℓ s) M).bind (fun p => match p with
            | (.term (.ret v), σ') => some (.term (.ret v), σ'.tail)   -- POP the pushed ℓ entry (keep outer puts)
            | (.term _, _)         => none
            | (.raised ℓ' op' w, σ') => some (.raised ℓ' op' w, σ'.tail)) -- forward; pop the pushed entry
      | .throws ℓ0 =>
          (evalD f σ M).bind (fun p => match p with
            | (.term (.ret v), σ') => some (.term (.ret v), σ')
            | (.term _, _)         => none
            | (.raised ℓ' op' w, σ') =>
                -- CAUGHT (zero-shot abort): discard the captured CONTINUATION (control unwinds to this
                -- handler), but KEEP the at-raise store `σ'`. The abort unwinds only `Kᵢ` (the control
                -- between this throws handler and the raise point); the OUTER `state ℓ` frames live in
                -- `Kₒ` and are NOT rewound (kernel `dispatchOn` THROW = `(Kₒ, ret v)` — `Operational.lean`).
                -- So an outer `put` performed before a caught raise PERSISTS. Inner `state` handles nested
                -- under this throws handler have already popped their pushed entry on the way out
                -- (`handle (state)` forwards a raise via `σ'.tail`), so `σ'` retains exactly the outer puts.
                if ℓ0 = ℓ' ∧ op' = "raise" then some (.term (.ret w), σ')
                else some (.raised ℓ' op' w, σ'))
      | _ =>
          (evalD f σ M).bind (fun p => match p with
            | (.term (.ret v), σ') => some (.term (.ret v), σ')
            | (.term _, _)         => none
            | (.raised ℓ' op' w, σ') => some (.raised ℓ' op' w, σ'))
  | _,          _, _               => none                -- out of scope (ADT elim)

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
  -- OP (ADR-0031 D2): the RESUMPTIVE op instruction. `compile (up ℓ op v) c` emits `OP ℓ op v :: c`;
  -- the inner continuation `c` IS Kᵢ and is KEPT (not discarded). On execution: find the nearest
  -- `state ℓ` frame in `hs`, service `get`/`put` IN PLACE (push `ret s`/`ret unit`, update the frame's
  -- stored state), and CONTINUE `c` (one-shot in-place resume, shape (A) — no continuation reified).
  -- If `ℓ` is NOT a state frame (a throws label), fall through to the THROW/unwind path (zero-shot).
  | OP     : Bang.EffectRow.Label → Bang.OpId → Val → Instr
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
  | .up ℓ op v,         c => Instr.OP ℓ op v :: c      -- RESUMPTIVE: `c` IS Kᵢ, KEPT (D2); throws falls through to unwind
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
      | _          => unwindFind ℓ op hs   -- state/transaction RESUME — skip (handled by `stateUpdate`)

/-- Find the nearest **state** frame for `ℓ` and service `get`/`put` IN PLACE (ADR-0031 D2,
the resume analog of `unwindFind`). `get` returns the stored `s`, leaving `hs` unchanged; `put`
returns `unit` and UPDATES that frame's stored state to `v` **in `hs`** — the frames ABOVE it
(Kᵢ's handlers) are KEPT (deep handler). Returns `(resultValue, hs')`. `none` = no `state ℓ` frame
(a throws label) ⇒ the caller falls through to `unwindFind`. PURE (no `exec` arg), mirroring the
kernel's `dispatchOn` state arm (KEEP `Kᵢ`, reinstall a deep `state ℓ s'` frame). -/
def stateUpdate : Bang.EffectRow.Label → Bang.OpId → Val → HStack → Option (Val × HStack)
  | _, _, _, []       => none
  | ℓ, op, v, fr :: hs =>
      match fr.handler with
      | .state ℓ0 s =>
          if ℓ0 = ℓ then
            if op = "get" then some (s, fr :: hs)                                  -- get: return s, frame kept
            else if op = "put" then some (.vunit, { fr with handler := .state ℓ0 v } :: hs)  -- put: store v in place
            else none                                                             -- non-get/put on ℓ ⇒ throws path (mirrors evalD)
          else (stateUpdate ℓ op v hs).map (fun p => (p.1, fr :: p.2))            -- different label ⇒ keep frame, recurse
      | _ => (stateUpdate ℓ op v hs).map (fun p => (p.1, fr :: p.2))              -- non-state frame ⇒ keep, recurse

/-! ### Store ↔ HStack correspondence (ADR-0031 D3): the invariant the resume proof rides

`hsState hs ℓ` reads the nearest `state ℓ` frame's stored value out of the machine's
HStack — the machine-side mirror of `evalD`'s `SStore.get?`. `Corr σ hs` is the
bridge invariant: the denotational store agrees with the machine's active state
frames at every label. The two lemmas below relate `stateUpdate` (the machine's
in-place service) to `SStore.get?`/`SStore.put` (the store's), so the `sim` `up`/
`handle (state)` cases close by a direct correspondence (D3), not a representation
translation. -/

/-- The nearest `state ℓ` frame's stored value in `hs` (the machine-side `SStore.get?`). -/
def hsState : HStack → Bang.EffectRow.Label → Option Val
  | [],       _ => none
  | fr :: hs, ℓ =>
      match fr.handler with
      | .state ℓ0 s => if ℓ0 = ℓ then some s else hsState hs ℓ
      | _           => hsState hs ℓ

/-- Project the machine's HStack to the store it mirrors: the `state ℓ s` frames, in order,
as `(ℓ, s)` entries (throws/transaction frames carry no state ⇒ skipped). This is the canonical
store for a given HStack; `Corr` says `evalD`'s threaded store IS exactly this projection. -/
def hsStates : HStack → SStore
  | []        => []
  | fr :: hs  =>
      match fr.handler with
      | .state ℓ0 s => (ℓ0, s) :: hsStates hs
      | _           => hsStates hs

/-- The bridge invariant (D3), STRUCTURAL form: the denotational store IS the projection of the
machine's active state frames. An equation (not just extensional agreement), so tail/push/pop go
through definitionally — the whole reason the store mirrors the HStack 1:1 on state frames. -/
def Corr (σ : SStore) (hs : HStack) : Prop := σ = hsStates hs

/-- Overwrite each `state` frame's stored value in `hs` with the head of `σ` (consumed in order).
This is `M`'s **net HStack effect** as a PURE function of `hs` and the post-`M` store — NOT of the
body's compiled continuation — so the `handle` term cases can name the post-`M` HStack BEFORE the
MARK frame's saved continuation is in scope (ADR-0031 W3). Non-state frames pass through. -/
def updateStates : HStack → SStore → HStack
  | [],       _ => []
  | fr :: hs, σ =>
      match fr.handler with
      | .state ℓ0 _ =>
          match σ with
          | (_, v) :: σ' => { fr with handler := .state ℓ0 v } :: updateStates hs σ'
          | []           => fr :: updateStates hs []     -- σ exhausted (unreachable under Corr)
      | _ => fr :: updateStates hs σ

/-- `get?` of the projection reads the nearest state frame (ties `hsStates` back to `hsState`). -/
theorem get?_hsStates : ∀ (hs : HStack) (ℓ : Bang.EffectRow.Label),
    (hsStates hs).get? ℓ = hsState hs ℓ := by
  intro hs
  induction hs with
  | nil => intro ℓ; rfl
  | cons fr hs ih =>
    intro ℓ
    cases hh : fr.handler with
    | state ℓ0 s =>
        simp only [hsStates, hsState, hh]
        by_cases hc : ℓ0 = ℓ
        · subst hc; simp [SStore.get?, List.find?]
        · simp only [if_neg hc, SStore.get?, List.find?, hc, decide_false, Bool.false_eq_true,
            if_false]; exact ih ℓ
    | throws ℓ0 => simp only [hsStates, hsState, hh]; exact ih ℓ
    | transaction ℓ0 Θ => simp only [hsStates, hsState, hh]; exact ih ℓ

/-- Under `Corr`, the store read equals the machine read. -/
theorem Corr.get? {σ : SStore} {hs : HStack} (hC : Corr σ hs) (ℓ : Bang.EffectRow.Label) :
    σ.get? ℓ = hsState hs ℓ := by rw [hC]; exact get?_hsStates hs ℓ

/-- `SStore.put` hits at its own label when that label is BOUND (an active frame). Induction on σ. -/
theorem SStore.get?_put_self : ∀ (σ : SStore) (ℓ : Bang.EffectRow.Label) (v s : Val),
    σ.get? ℓ = some s → (σ.put ℓ v).get? ℓ = some v := by
  intro σ
  induction σ with
  | nil => intro ℓ v s hg; simp [SStore.get?, List.find?] at hg
  | cons p σ ih =>
    obtain ⟨ℓ0, w⟩ := p
    intro ℓ v s hg
    by_cases hc : ℓ0 = ℓ
    · subst hc; simp [SStore.put, SStore.get?, List.find?]
    · have hne : ¬ (ℓ0 = ℓ) := hc
      simp only [SStore.get?, List.find?, hne, decide_false, Bool.false_eq_true, if_false] at hg ⊢
      simp only [SStore.put, if_neg hne, SStore.get?, List.find?, hne, decide_false,
        Bool.false_eq_true, if_false]
      exact ih ℓ v s hg

/-- `SStore.put` is transparent at a different label. Induction on σ. -/
theorem SStore.get?_put_ne : ∀ (σ : SStore) {ℓ ℓ' : Bang.EffectRow.Label} (v : Val), ℓ' ≠ ℓ →
    (σ.put ℓ v).get? ℓ' = σ.get? ℓ' := by
  intro σ
  induction σ with
  | nil => intro ℓ ℓ' v h; rfl
  | cons p σ ih =>
    obtain ⟨ℓ0, w⟩ := p
    intro ℓ ℓ' v h
    by_cases hc : ℓ0 = ℓ
    · subst hc
      have hne : ¬ (ℓ0 = ℓ') := fun he => h he.symm
      simp [SStore.put, SStore.get?, List.find?, hne]
    · simp only [SStore.put, if_neg hc]
      by_cases hc' : ℓ0 = ℓ'
      · subst hc'; simp [SStore.get?, List.find?]
      · simp only [SStore.get?, List.find?, hc', decide_false, Bool.false_eq_true, if_false]
        exact ih v h

/-- `get` correspondence: when `hsState hs ℓ = some s`, the machine's `stateUpdate`
returns `(s, hs)` unchanged (the deep frame is kept). Induction on `hs`. -/
theorem stateUpdate_get {ℓ : Bang.EffectRow.Label} {v : Val} :
    ∀ {hs : HStack} {s : Val}, hsState hs ℓ = some s → stateUpdate ℓ "get" v hs = some (s, hs) := by
  intro hs
  induction hs with
  | nil => intro s hg; simp [hsState] at hg
  | cons fr hs ih =>
    intro s hg
    cases hh : fr.handler with
    | state ℓ0 s0 =>
        simp only [hsState, hh] at hg
        by_cases hc : ℓ0 = ℓ
        · simp only [if_pos hc, Option.some.injEq] at hg; subst hg
          simp [stateUpdate, hh, hc]
        · simp only [if_neg hc] at hg
          simp [stateUpdate, hh, hc, ih hg]
    | throws ℓ0 =>
        simp only [hsState, hh] at hg
        simp [stateUpdate, hh, ih hg]
    | transaction ℓ0 Θ =>
        simp only [hsState, hh] at hg
        simp [stateUpdate, hh, ih hg]

/-- `put` correspondence: when `hsState hs ℓ = some s₀`, `stateUpdate ℓ "put" v hs` returns
`(vunit, hs')` whose state-projection is exactly the store after an in-place `put` —
`hsStates hs' = (hsStates hs).put ℓ v`. This is the structural `Corr`-preservation fact (D3): the
machine's in-place HStack update mirrors the store's in-place `put`. Induction on `hs`. -/
theorem stateUpdate_put {ℓ : Bang.EffectRow.Label} {v : Val} :
    ∀ {hs : HStack} {s0 : Val}, hsState hs ℓ = some s0 →
      ∃ hs', stateUpdate ℓ "put" v hs = some (.vunit, hs')
        ∧ hsStates hs' = (hsStates hs).put ℓ v := by
  intro hs
  induction hs with
  | nil => intro s0 hg; simp [hsState] at hg
  | cons fr hs ih =>
    intro s0 hg
    cases hh : fr.handler with
    | state ℓ0 s0' =>
        by_cases hc : ℓ0 = ℓ
        · -- found here: update this frame in place
          subst hc
          refine ⟨{ fr with handler := .state ℓ0 v } :: hs, ?_, ?_⟩
          · simp [stateUpdate, hh]
          · simp [hsStates, hh, SStore.put]
        · -- not here: recurse
          simp only [hsState, hh, if_neg hc] at hg
          obtain ⟨hs', hsu, heq⟩ := ih hg
          refine ⟨fr :: hs', ?_, ?_⟩
          · simp [stateUpdate, hh, hc, hsu]
          · simp only [hsStates, hh, heq, SStore.put, if_neg hc]
    | throws ℓ0 =>
        simp only [hsState, hh] at hg
        obtain ⟨hs', hsu, heq⟩ := ih hg
        refine ⟨fr :: hs', ?_, ?_⟩
        · simp only [stateUpdate, hh, hsu, Option.map_some]
        · simp only [hsStates, hh, heq]
    | transaction ℓ0 Θ =>
        simp only [hsState, hh] at hg
        obtain ⟨hs', hsu, heq⟩ := ih hg
        refine ⟨fr :: hs', ?_, ?_⟩
        · simp only [stateUpdate, hh, hsu, Option.map_some]
        · simp only [hsStates, hh, heq]

/-- `Corr` is preserved by a matched `put` (structural form): the machine's in-place update and
the store's in-place `put` produce mirrored states. -/
theorem Corr_put {σ : SStore} {hs hs' : HStack} {ℓ : Bang.EffectRow.Label} {v : Val}
    (hC : Corr σ hs) (heq : hsStates hs' = (hsStates hs).put ℓ v) :
    Corr (σ.put ℓ v) hs' := by
  unfold Corr at hC ⊢; rw [hC, heq]

/-! ### `HMut`: structure-preserving HStack mutation (the body's net hstack effect)

A returning body's net effect on the HStack is to mutate **state-frame values in place**, never
to push/pop or change a frame's `savedCode`/`savedStack`/handler-shape. `HMut hs hsf` captures
exactly that: same length, frame-by-frame the `savedCode`/`savedStack` agree and the handlers agree
up to a `state` frame's stored value. This is the invariant that lets the `handle` term cases pop
the installed frame and recover `Corr` on the tail (the frame the body kept is structurally the one
that was installed). -/

/-- Two frames agree up to a `state` handler's stored value. -/
def FrameMut (a b : HFrame) : Prop :=
  a.savedCode = b.savedCode ∧ a.savedStack = b.savedStack ∧
    (match a.handler, b.handler with
     | .state ℓ1 _, .state ℓ2 _ => ℓ1 = ℓ2
     | .throws ℓ1, .throws ℓ2 => ℓ1 = ℓ2
     | .transaction ℓ1 Θ1, .transaction ℓ2 Θ2 => ℓ1 = ℓ2 ∧ Θ1 = Θ2
     | _, _ => False)

/-- `HMut hs hsf`: `hsf` is `hs` with state-frame values possibly changed, no push/pop, frame
structure preserved (savedCode/savedStack/handler-shape identical). -/
def HMut : HStack → HStack → Prop
  | [], []           => True
  | a :: x, b :: y   => FrameMut a b ∧ HMut x y
  | _, _             => False

theorem HMut.refl : ∀ hs, HMut hs hs
  | []      => trivial
  | fr :: hs => ⟨by
      refine ⟨rfl, rfl, ?_⟩
      cases fr.handler <;> simp, HMut.refl hs⟩

/-- If the body was installed under a NON-state top frame (throws/transaction) and `HMut` holds,
the resulting top is also non-state ⇒ the projection drops it ⇒ `Corr` passes to the tail. -/
theorem Corr_pop_nonstate {σ : SStore} {fr top : HFrame} {hs tail : HStack}
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) (hmut : HMut (fr :: hs) (top :: tail))
    (hC : Corr σ (top :: tail)) : Corr σ tail := by
  obtain ⟨⟨_, _, hsh⟩, _⟩ := hmut
  unfold Corr at hC ⊢; rw [hC]
  cases hfr : fr.handler with
  | state ℓ1 s1 => exact absurd hfr (hns ℓ1 s1)
  | throws ℓ1 =>
      cases hth : top.handler with
      | throws ℓ2 => simp [hsStates, hth]
      | state _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | transaction _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
  | transaction ℓ1 Θ1 =>
      cases hth : top.handler with
      | transaction ℓ2 Θ2 => simp [hsStates, hth]
      | state _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | throws _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)

/-- `stateUpdate`-put preserves `HMut` (it mutates one state-frame value in place). -/
theorem HMut.of_stateUpdate_put {ℓ : Bang.EffectRow.Label} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, stateUpdate ℓ "put" v hs = some (r, hs') → HMut hs hs' := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [stateUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | state ℓ0 s =>
        simp only [stateUpdate, hh] at hsu
        by_cases hc : ℓ0 = ℓ
        · simp only [if_pos hc, if_neg (by decide : ¬ ("put" = "get")), Option.some.injEq,
            Prod.mk.injEq] at hsu
          obtain ⟨_, rfl⟩ := hsu
          exact ⟨⟨rfl, rfl, by simp [hh]⟩, HMut.refl hs⟩
        · simp only [if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          exact ⟨⟨rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | throws ℓ0 =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | transaction ℓ0 Θ =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, by simp [hh]⟩, ih hsu1⟩

/-- `HMut` is transitive (chaining `letC`/`app` sub-runs). -/
theorem HMut.trans : ∀ {x y z : HStack}, HMut x y → HMut y z → HMut x z := by
  intro x
  induction x with
  | nil =>
      intro y z hxy hyz
      cases y with
      | nil => cases z with | nil => trivial | cons => simp [HMut] at hyz
      | cons => simp [HMut] at hxy
  | cons a x ih =>
      intro y z hxy hyz
      cases y with
      | nil => simp [HMut] at hxy
      | cons b y =>
        cases z with
        | nil => simp [HMut] at hyz
        | cons c z =>
          obtain ⟨hab, hxy⟩ := hxy
          obtain ⟨hbc, hyz⟩ := hyz
          refine ⟨⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, ?_⟩, ih hxy hyz⟩
          obtain ⟨_, _, h1⟩ := hab; obtain ⟨_, _, h2⟩ := hbc
          cases ha : a.handler <;> cases hb : b.handler <;> cases hc : c.handler <;>
            rw [ha, hb] at h1 <;> rw [hb, hc] at h2 <;> simp_all

/-- A pushed frame on top: `HMut (fr :: hs) (top :: tail)` gives `HMut hs tail` (peel the top). -/
theorem HMut.tail {fr top : HFrame} {hs tail : HStack}
    (hmut : HMut (fr :: hs) (top :: tail)) : HMut hs tail := hmut.2

/-- The reconstruction lemma: a machine HStack `k` that is `HMut`-related to `hs` AND whose
state-projection is `σ'` is **exactly** `updateStates hs σ'`. So the post-`M` HStack — which the
term-part proves satisfies both — is the pure function `updateStates hs σ'` (frame-independent). -/
theorem updateStates_eq : ∀ {hs k : HStack} {σ' : SStore},
    HMut hs k → Corr σ' k → k = updateStates hs σ' := by
  intro hs
  induction hs with
  | nil =>
      intro k σ' hmut _
      cases k with
      | nil => rfl
      | cons => simp [HMut] at hmut
  | cons fr hs ih =>
      intro k σ' hmut hC
      cases k with
      | nil => simp [HMut] at hmut
      | cons fk k =>
        obtain ⟨hfm, hmut'⟩ := hmut
        obtain ⟨hscode, hsstack, hsh⟩ := hfm
        unfold Corr at hC
        cases hfr : fr.handler with
        | state ℓ0 s0 =>
            cases hfk : fk.handler with
            | state ℓ1 s1 =>
                rw [hfr, hfk] at hsh; simp only at hsh; subst hsh
                rw [hsStates, hfk] at hC; subst hC
                simp only [updateStates, hfr]
                rw [← ih hmut' (rfl : Corr (hsStates k) k)]
                cases fr; cases fk; simp_all
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
        | throws ℓ0 =>
            cases hfk : fk.handler with
            | throws ℓ1 =>
                rw [hsStates, hfk] at hC
                simp only [updateStates, hfr]
                rw [← ih hmut' (hC : Corr σ' k)]
                cases fr; cases fk; simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
        | transaction ℓ0 Θ0 =>
            cases hfk : fk.handler with
            | transaction ℓ1 Θ1 =>
                rw [hsStates, hfk] at hC
                simp only [updateStates, hfr]
                rw [← ih hmut' (hC : Corr σ' k)]
                cases fr; cases fk; simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)

/-- `updateStates` with the store a HStack already mirrors (`Corr σ hs`) is the identity — overwriting
each state value with the value it already has. (The `updateStates_eq` corollary at `k = hs`,
`HMut.refl`.) -/
theorem updateStates_self {σ : SStore} {hs : HStack} (hC : Corr σ hs) : updateStates hs σ = hs :=
  (updateStates_eq (HMut.refl hs) hC).symm


/-- `updateStates` depends only on a HStack's STATE-FRAME STRUCTURE, not its values: `HMut`-related
stacks update identically. This is the re-base that lets a `letC`/`app` raised chain restate the
at-raise HStack on the ORIGINAL `hs` (since `HMut hs hsM`, `updateStates hsM σ = updateStates hs σ`).
The COVERING hypothesis `Corr σ (updateStates k σ)` (σ mirrors `k`'s state frames — exactly what the
at-raise store satisfies) rules out the only divergent branch: σ exhausted AT a state frame, where
`updateStates` would otherwise keep each stack's OWN (possibly differing) value. Induction on `hs`/`k`
(paired by `HMut`). -/
theorem updateStates_congr_HMut : ∀ {hs k : HStack} (σ : SStore),
    HMut hs k → Corr σ (updateStates k σ) → updateStates k σ = updateStates hs σ := by
  intro hs
  induction hs with
  | nil =>
      intro k σ hmut _
      cases k with | nil => rfl | cons => simp [HMut] at hmut
  | cons fr hs ih =>
    intro k σ hmut hcov
    cases k with
    | nil => simp [HMut] at hmut
    | cons fk k =>
      obtain ⟨⟨hcode, hstack, hsh⟩, hmut'⟩ := hmut
      cases hfr : fr.handler with
      | state ℓ0 s =>
          cases hfk : fk.handler with
          | state ℓ1 s1 =>
              cases σ with
              | nil =>
                  -- σ exhausted AT a state frame ⇒ `updateStates (fk::k) [] = fk :: updateStates k []`,
                  -- whose projection leads with `(ℓ1, s1)`; the covering `Corr [] …` then asserts
                  -- `[] = (ℓ1,s1) :: …`, impossible. (Under Corr the store always covers the state frames.)
                  exfalso; unfold Corr at hcov
                  rw [updateStates] at hcov; simp only [hfk] at hcov
                  rw [hsStates] at hcov; simp only [hfk] at hcov
                  exact (List.cons_ne_nil _ _ hcov.symm)
              | cons p σ' =>
                  obtain ⟨ℓq, wq⟩ := p
                  have hcov' : Corr σ' (updateStates k σ') := by
                    unfold Corr at hcov ⊢; simp only [updateStates, hfk, hsStates] at hcov
                    exact (List.cons.injEq _ _ _ _).mp hcov |>.2
                  simp only [updateStates, hfr, hfk]; rw [ih σ' hmut' hcov']
                  cases fr; cases fk; simp_all
          | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
          | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
      | throws ℓ0 =>
          cases hfk : fk.handler with
          | throws ℓ1 =>
              have hcov' : Corr σ (updateStates k σ) := by
                unfold Corr at hcov ⊢; simpa only [updateStates, hfk, hsStates] using hcov
              simp only [updateStates, hfr, hfk]; rw [ih σ hmut' hcov']; cases fr; cases fk; simp_all
          | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
          | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
      | transaction ℓ0 Θ =>
          cases hfk : fk.handler with
          | transaction ℓ1 Θ1 =>
              have hcov' : Corr σ (updateStates k σ) := by
                unfold Corr at hcov ⊢; simpa only [updateStates, hfk, hsStates] using hcov
              simp only [updateStates, hfr, hfk]; rw [ih σ hmut' hcov']; cases fr; cases fk; simp_all
          | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
          | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)

/-- A NON-state frame `fr` is transparent to `updateStates`: `updateStates (fr::hs) σ = fr ::
updateStates hs σ` (the σ-cursor is not advanced — only `state` frames consume an entry). -/
theorem updateStates_cons_nonstate {fr : HFrame} {hs : HStack} (σ : SStore)
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) :
    updateStates (fr :: hs) σ = fr :: updateStates hs σ := by
  cases hh : fr.handler with
  | state ℓ s => exact absurd hh (hns ℓ s)
  | throws ℓ => simp only [updateStates, hh]
  | transaction ℓ Θ => simp only [updateStates, hh]

/-- The raised-part at-raise correspondence pops a NON-state install frame: a throws/transaction
frame carries no store entry, so `Corr`/`HMut` over `fr::hs` (the body's at-raise pair) pass to the
tail `hs` (the forwarded pair). The `sim` raised handle(throws)/handle(transaction) escape cases. -/
theorem raisedPair_pop_nonstate {fr : HFrame} {hs : HStack} {σ' : SStore}
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s)
    (hCr : Corr σ' (updateStates (fr :: hs) σ'))
    (hmutr : HMut (fr :: hs) (updateStates (fr :: hs) σ')) :
    Corr σ' (updateStates hs σ') ∧ HMut hs (updateStates hs σ') := by
  have hupd : updateStates (fr :: hs) σ' = fr :: updateStates hs σ' :=
    updateStates_cons_nonstate σ' hns
  rw [hupd] at hCr hmutr
  refine ⟨?_, HMut.tail hmutr⟩
  -- `fr` non-state ⇒ its projection contributes nothing: `hsStates (fr :: t) = hsStates t`.
  unfold Corr at hCr ⊢
  have hproj : hsStates (fr :: updateStates hs σ') = hsStates (updateStates hs σ') := by
    cases hh : fr.handler with
    | state ℓ s => exact absurd hh (hns ℓ s)
    | throws ℓ => simp only [hsStates, hh]
    | transaction ℓ Θ => simp only [hsStates, hh]
  rw [hproj] at hCr; exact hCr

/-- The raised-part at-raise correspondence pops a `state` install frame: `handle (state ℓ0 s0)`'s
forward of a raise pops the pushed entry (`σ'.tail`), and the machine skips the state frame on the
throws-unwind. From the body's at-raise pair over `fr::hs` (`fr` a state frame) at store `σ'`, the
forwarded pair over `hs` at `σ'.tail` follows. The `sim` raised handle(state) escape case. -/
theorem raisedPair_pop_state {fr : HFrame} {hs : HStack} {σ' : SStore} {ℓ0 : Bang.EffectRow.Label}
    {s0 : Val} (hfr : fr.handler = .state ℓ0 s0)
    (hCr : Corr σ' (updateStates (fr :: hs) σ'))
    (hmutr : HMut (fr :: hs) (updateStates (fr :: hs) σ')) :
    Corr σ'.tail (updateStates hs σ'.tail) ∧ HMut hs (updateStates hs σ'.tail) := by
  -- `Corr` forces `σ'` non-empty: its head IS `fr`'s entry. Destruct it.
  cases σ' with
  | nil =>
      -- `updateStates (fr::hs) [] = fr :: updateStates hs []`; projection has `(ℓ0,s0)` ⇒ Corr says
      -- `[] = (ℓ0,s0) :: …`, impossible.
      exfalso
      unfold Corr at hCr
      rw [updateStates] at hCr; simp only [hfr] at hCr
      rw [hsStates] at hCr; simp only [hfr] at hCr
      exact (List.cons_ne_nil _ _ hCr.symm)
  | cons p σ1' =>
      obtain ⟨ℓa, wa⟩ := p
      have hupd : updateStates (fr :: hs) ((ℓa, wa) :: σ1') =
          { fr with handler := .state ℓ0 wa } :: updateStates hs σ1' := by
        simp only [updateStates, hfr]
      rw [hupd] at hCr hmutr
      simp only [List.tail]
      refine ⟨?_, HMut.tail hmutr⟩
      unfold Corr at hCr ⊢
      simp only [hsStates] at hCr
      exact (List.cons.injEq _ _ _ _).mp hCr |>.2

/-- An op that is neither `get` nor `put` is NOT serviced by `stateUpdate` (it guards op ∈ {get,put}),
so the machine OP falls through to the throws/unwind path — mirroring `evalD`'s `raised` for such ops
on a state label. Induction on `hs`. -/
theorem stateUpdate_none_of_non_getput (ℓ : Bang.EffectRow.Label) (v : Val) :
    ∀ (hs : HStack) {op : Bang.OpId}, op ≠ "get" → op ≠ "put" → stateUpdate ℓ op v hs = none := by
  intro hs
  induction hs with
  | nil => intro op _ _; rfl
  | cons fr hs ih =>
    intro op hng hnp
    cases hh : fr.handler with
    | state ℓ0 s =>
        by_cases hc : ℓ0 = ℓ
        · simp [stateUpdate, hh, hc, hng, hnp]
        · simp [stateUpdate, hh, hc, ih hng hnp]
    | throws ℓ0 => simp [stateUpdate, hh, ih hng hnp]
    | transaction ℓ0 Θ => simp [stateUpdate, hh, ih hng hnp]

/-- When no state frame for `ℓ` is active, `stateUpdate` finds nothing (the machine OP then
falls through to `unwindFind`, the throws path). The contrapositive mirror of `hsState … = none`. -/
theorem stateUpdate_none_of_get?_none {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val} :
    ∀ {hs : HStack}, hsState hs ℓ = none → stateUpdate ℓ op v hs = none := by
  intro hs
  induction hs with
  | nil => intro _; rfl
  | cons fr hs ih =>
    intro hns
    cases hh : fr.handler with
    | state ℓ0 s =>
        simp only [hsState, hh] at hns
        by_cases hc : ℓ0 = ℓ
        · simp [if_pos hc] at hns
        · simp only [if_neg hc] at hns
          simp [stateUpdate, hh, hc, ih hns]
    | throws ℓ0 => simp only [hsState, hh] at hns; simp [stateUpdate, hh, ih hns]
    | transaction ℓ0 Θ => simp only [hsState, hh] at hns; simp [stateUpdate, hh, ih hns]

/-- `Corr` is preserved by a `handle (state ℓ s)` install: PUSHING `(ℓ ↦ s)` on the store
mirrors pushing a `state ℓ s` frame on the HStack. -/
theorem Corr_install {σ : SStore} {hs : HStack} (ℓ : Bang.EffectRow.Label) (s : Val) (fr : HFrame)
    (hfr : fr.handler = .state ℓ s) (hC : Corr σ hs) : Corr (σ.push ℓ s) (fr :: hs) := by
  unfold Corr at hC ⊢; rw [hC]; simp [hsStates, hfr, SStore.push]

/-- A NON-state frame (throws/transaction) carries no store entry: pushing it preserves `Corr`. -/
theorem Corr_install_nonstate {σ : SStore} {hs : HStack} (fr : HFrame)
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) (hC : Corr σ hs) : Corr σ (fr :: hs) := by
  unfold Corr at hC ⊢; rw [hC]
  cases hh : fr.handler with
  | state ℓ0 s => exact absurd hh (hns ℓ0 s)
  | throws ℓ0 => simp [hsStates, hh]
  | transaction ℓ0 Θ => simp [hsStates, hh]

/-- `Corr` for the tail when the top is a `state` frame (the `handle (state)` POP): the store's
tail mirrors the HStack's tail. -/
theorem Corr_pop_state {σ : SStore} {fr : HFrame} {hs : HStack} {ℓ0 : Bang.EffectRow.Label}
    {s : Val} (hfr : fr.handler = .state ℓ0 s) (hC : Corr σ (fr :: hs)) : Corr σ.tail hs := by
  unfold Corr at hC ⊢; rw [hC]; simp [hsStates, hfr]

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
  -- OP (ADR-0031 D2): the RESUMPTIVE dispatch. Try `stateUpdate` first (state get/put, in-place,
  -- CONTINUE `c` = Kᵢ with the result pushed — one-shot resume). If no state frame, fall through to
  -- the THROW/unwind path (zero-shot abort, DISCARDING `c`). This unifies state-resume and throws-abort
  -- in one instruction, matching the kernel's `dispatch` (= `splitAt >>= dispatchOn`).
  | Nat.succ f, Instr.OP ℓ op v :: c, s, hs =>
      match stateUpdate ℓ op v hs with
      | some (r, hs') => exec f c (.ret r :: s) hs'            -- RESUME: continue c (Kᵢ) with ret r
      | none =>                                                -- not a state frame ⇒ throws abort
          match unwindFind ℓ op hs with
          | some (c', s', hs') => exec f c' (.ret v :: s') hs' -- ABORT to (Kₒ, ret v), c discarded
          | none               => none                         -- uncaught = stuck

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
      | OP ℓ op v =>
        simp only [exec] at h ⊢
        cases hsu : stateUpdate ℓ op v hs with
        | some ru =>
          obtain ⟨r, hs'⟩ := ru
          simp only [hsu] at h ⊢; exact ih _ _ _ _ h
        | none =>
          simp only [hsu] at h ⊢
          cases hu : unwindFind ℓ op hs with
          | none => simp only [hu] at h; simp at h
          | some cs => obtain ⟨c', s', hs'⟩ := cs; simp only [hu] at h ⊢; exact ih _ _ _ _ h

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

/-- A non-throws top frame (state/transaction) is SKIPPED by the throws unwind ⇒ `throwOutcome`
is unchanged by prepending it (the abort target is found deeper). -/
theorem throwOutcome_cons_nonthrows (F : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Val)
    (fr : HFrame) (hs : HStack) (hnt : ∀ ℓ0, fr.handler ≠ Handler.throws ℓ0) :
    throwOutcome F ℓ op v (fr :: hs) = throwOutcome F ℓ op v hs := by
  cases hh : fr.handler with
  | throws ℓ0 => exact absurd hh (hnt ℓ0)
  | state ℓ0 s => simp only [throwOutcome, unwindFind, hh]
  | transaction ℓ0 Θ => simp only [throwOutcome, unwindFind, hh]

/-- (★) the **two-part, store-threaded** simulation (k2-playbook §Effects + ADR-0031):
a `term` part AND a `raised` part. The store-thread is the resume mechanism — the
`term` part is now an EXISTENTIAL over the machine's resulting HStack `hsf` (M
transforms `hs ↝ hsf`, the continuation `c` runs from `hsf`), with `Corr σ' hsf`
(the store mirrors the machine's active state frames, D3). The `up`/`handle (state)`
cases use `stateUpdate_get`/`stateUpdate_put`/`Corr_install` to align the inline
store service with the in-place HStack update. The `handle (throws)` catch is the
zero-shot `THROW ↔ dispatch` correspondence (unchanged from O2, now σ-threaded).
Induction on the eval fuel `fe`. -/
theorem sim : ∀ fe,
    (∀ M σ t σ', evalD fe σ M = some (.term t, σ') →
      ∀ hs, Corr σ hs →
        ∃ hsf, Corr σ' hsf ∧ HMut hs hsf ∧
          ∀ c s F r, exec F c (t :: s) hsf = some r →
            ∃ F', exec F' (compile M c) s hs = some r)
    ∧ (∀ M σ ℓ op v σ', evalD fe σ M = some (.raised ℓ op v, σ') →
      ∀ hs, Corr σ hs →
        -- the at-raise HStack `updateStates hs σ'` mirrors the at-raise store σ' (D3) and is a state-
        -- mutation of the at-handle `hs` — threaded so the throws-CAUGHT term subcase can name it as
        -- its existential witness (an outer `put` before a caught raise persists; ADR-0031 caught = σ').
        (Corr σ' (updateStates hs σ') ∧ HMut hs (updateStates hs σ')) ∧
        ∀ c s F r, throwOutcome F ℓ op v (updateStates hs σ') = some r →
        ∃ F', exec F' (compile M c) s hs = some r) := by
  intro fe
  induction fe with
  | zero =>
      exact ⟨fun M σ t σ' h => by simp [evalD] at h, fun M σ ℓ op v σ' h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M σ t σ' h hs hC
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
          exact ⟨hs, hC, HMut.refl hs, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
          exact ⟨hs, hC, HMut.refl hs, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.ret v), σ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hlenM, kM⟩ := ihT M σ (.ret v) σ1 hM hs hC
                obtain ⟨hsf, hCf, hlenf, kN⟩ := ihT (Comp.subst v N) σ1 t σ' h hsM hCM
                refine ⟨hsf, hCf, HMut.trans hlenM hlenf, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kN c s F r hr
                have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.SUBST N :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.lam M2), _), h => simp [Option.bind] at h
            | (.term (.letC a b), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term (.unfold a), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _), h =>
                -- letC propagates a raise: evalD (letC M N) = raised ⇒ h : raised = term, absurd
                simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hlenf, k⟩ := ihT M σ t σ' h hs hC
              exact ⟨hsf, hCf, hlenf, fun c s F r hr => by
                obtain ⟨F', hF'⟩ := k c s F r hr; exact ⟨F', by simpa only [compile] using hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | app M v =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.lam N), σ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hlenM, kM⟩ := ihT M σ (.lam N) σ1 hM hs hC
                obtain ⟨hsf, hCf, hlenf, kN⟩ := ihT (Comp.subst v N) σ1 t σ' h hsM hCM
                refine ⟨hsf, hCf, HMut.trans hlenM hlenf, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kN c s F r hr
                have hstep : exec (F1+1) (Instr.APP v :: c) (.lam N :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.APP v :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.ret w), _), h => simp [Option.bind] at h
            | (.term (.letC a b), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term (.unfold a), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _), h => simp [Option.bind] at h
      | up ℓ op v =>
          -- STATE RESUME (D1/D2): get/put serviced inline against σ, mirrored by stateUpdate on hs.
          simp only [evalD] at h
          cases hg : σ.get? ℓ with
          | none =>
              -- no state frame ⇒ raised; but term part ⇒ contradiction
              rw [hg] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hraised, _⟩ := h; exact absurd hraised (by simp)
          | some sv =>
              rw [hg] at h
              by_cases hop : op = "get"
              · -- get: t = ret sv, σ' = σ; machine OP does stateUpdate-get (hs unchanged).
                simp only [if_pos hop, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                have hgState : hsState hs ℓ = some sv := by rw [← Corr.get? hC ℓ]; exact hg
                refine ⟨hs, hC, HMut.refl hs, fun c s F r hr => ⟨F+1, ?_⟩⟩
                subst hop
                simp only [compile, exec, stateUpdate_get hgState]; exact hr
              · by_cases hop2 : op = "put"
                · -- put: t = ret unit, σ' = σ.put ℓ v; machine OP does stateUpdate-put (hs updated).
                  simp only [if_neg hop, if_pos hop2, Option.some.injEq, Prod.mk.injEq,
                    Outcome.term.injEq] at h
                  obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                  have hgState : hsState hs ℓ = some sv := by rw [← Corr.get? hC ℓ]; exact hg
                  obtain ⟨hs', hsu, heq⟩ := stateUpdate_put (v := v) hgState
                  refine ⟨hs', Corr_put hC heq, HMut.of_stateUpdate_put hsu, fun c s F r hr => ⟨F+1, ?_⟩⟩
                  subst hop2
                  simp only [compile, exec, hsu]; exact hr
                · -- a non-get/put op on a state label: evalD raises ⇒ term part contradiction
                  simp only [if_neg hop, if_neg hop2, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hraised, _⟩ := h; exact absurd hraised (by simp)
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              -- INSTALL a state frame: body runs under σ.push ℓ0 s0 / a pushed state frame.
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                    -- The existential = `updateStates hs σ1.tail` — M's net HStack effect as a PURE
                    -- function of `hs`/post-store, named BEFORE the MARK saved-cont (c2,s2) is in scope.
                    -- `body cc ss` runs M under the REAL frame `{state ℓ0 s0, cc, ss}` and shows its tail
                    -- IS `updateStates hs σ1.tail` (`updateStates_eq`), supplying Corr/HMut + continuation.
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 cc (.ret v :: ss) (updateStates hs σ1.tail) = some r2 →
                        (∃ F', exec F' (compile M (Instr.UNMARK :: cc)) ss
                          ({ handler := Handler.state ℓ0 s0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1.tail (updateStates hs σ1.tail) ∧ HMut hs (updateStates hs σ1.tail) := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { handler := Handler.state ℓ0 s0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hCinstall : Corr (σ.push ℓ0 s0) (fr :: hs) :=
                        Corr_install ℓ0 s0 fr (by rw [hfrdef]) hC
                      obtain ⟨hsM, hCM, hmutM, kM⟩ := ihT M (σ.push ℓ0 s0) (.ret v) σ1 hM (fr :: hs) hCinstall
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have htop : ∃ s', top.handler = .state ℓ0 s' := by
                        have hh := hmutM.1.2.2
                        cases hth : top.handler with
                        | state ℓ1 s1 => rw [hfrdef, hth] at hh; simp only at hh; subst hh; exact ⟨s1, rfl⟩
                        | throws _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | transaction _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                      obtain ⟨s', hts⟩ := htop
                      have hCtail := Corr_pop_state hts hCM
                      have htaileq : tail = updateStates hs σ1.tail := updateStates_eq (HMut.tail hmutM) hCtail
                      -- the body's terminal config `top :: tail`; UNMARK pops `top` ⇒ run `cc` from `tail`.
                      have hstep : exec (F2+1) (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ (HMut.tail hmutM)⟩
                    obtain ⟨_, hCf, hmutf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨updateStates hs σ1.tail, hCf, hmutf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.lam M2), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _), h =>
                    -- body raises past the state frame (state never catches a throws) ⇒ handle forwards
                    -- ⇒ raised, contradicting the term part.
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                    -- throws-install + normal return: existential = `updateStates hs σ1` (throws stores
                    -- no state ⇒ σ' = σ1). `body cc ss` runs M under `{throws ℓ0, cc, ss}` and shows the
                    -- popped tail IS `updateStates hs σ1` (`updateStates_eq` via `Corr_pop_nonstate`).
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 cc (.ret v :: ss) (updateStates hs σ1) = some r2 →
                        (∃ F', exec F' (compile M (Instr.UNMARK :: cc)) ss
                          ({ handler := Handler.throws ℓ0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (updateStates hs σ1) ∧ HMut hs (updateStates hs σ1) := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { handler := Handler.throws ℓ0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hns : ∀ ℓ s, fr.handler ≠ Handler.state ℓ s := by rw [hfrdef]; intro ℓ s; simp
                      have hCinstall : Corr σ (fr :: hs) := Corr_install_nonstate fr hns hC
                      obtain ⟨hsM, hCM, hmutM, kM⟩ := ihT M σ (.ret v) σ1 hM (fr :: hs) hCinstall
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have hCtail := Corr_pop_nonstate hns hmutM hCM
                      have htaileq : tail = updateStates hs σ1 := updateStates_eq (HMut.tail hmutM) hCtail
                      have hstep : exec (F2+1) (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ (HMut.tail hmutM)⟩
                    obtain ⟨_, hCf, hmutf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨updateStates hs σ1, hCf, hmutf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.lam M2), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, σ1), h =>
                    by_cases hc : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp only [Option.bind_some, if_pos hc, Option.some.injEq, Prod.mk.injEq,
                        Outcome.term.injEq] at h
                      obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                      obtain ⟨rfl, rfl⟩ := hc
                      -- caught: M raises `(ℓ0,raise)` ⇒ machine OP catches the throws frame, aborts to the
                      -- MARK's saved (c2,s2) with `ret w`. The abort unwinds only the CONTINUATION; the
                      -- store stays at the at-raise `σ1` (ADR-0031 caught = σ', keeping outer puts), so the
                      -- existential HStack is the at-raise `updateStates hs σ1`. The outer pair over `hs`
                      -- comes from popping the throws install frame (non-state) off the raised IH's pair.
                      have hns0 : ∀ ℓ s, (Handler.throws ℓ0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                      have hpair : Corr σ1 (updateStates hs σ1) ∧ HMut hs (updateStates hs σ1) := by
                        set fr0 : HFrame := { handler := Handler.throws ℓ0, savedCode := [], savedStack := [] }
                        have hns : ∀ ℓ s, fr0.handler ≠ Handler.state ℓ s := hns0
                        obtain ⟨⟨hCr, hmutr⟩, _⟩ :=
                          ihR M σ ℓ0 "raise" w σ1 hM (fr0 :: hs) (Corr_install_nonstate fr0 hns hC)
                        exact raisedPair_pop_nonstate hns hCr hmutr
                      refine ⟨updateStates hs σ1, hpair.1, hpair.2, fun c2 s2 F2 r2 hr2 => ?_⟩
                      -- run the raised IH over the ACTUAL installed frame (savedCode/Stack = c2/s2): the
                      -- throws-unwind catches it (`if_true`) and aborts to `(c2, s2)` over the at-raise
                      -- tail `updateStates hs σ1` with `ret w` pushed = `hr2`.
                      set fr2 : HFrame := { handler := Handler.throws ℓ0, savedCode := c2, savedStack := s2 }
                        with hfrdef
                      have hCinstall2 : Corr σ (fr2 :: hs) := Corr_install_nonstate fr2 hns0 hC
                      obtain ⟨_, kR2⟩ := ihR M σ ℓ0 "raise" w σ1 hM (fr2 :: hs) hCinstall2
                      have hthrow : throwOutcome F2 ℓ0 "raise" w (updateStates (fr2 :: hs) σ1) = some r2 := by
                        simp only [updateStates, hfrdef, throwOutcome, unwindFind, and_self, if_true]
                        exact hr2
                      obtain ⟨F1, hF1⟩ := kR2 (Instr.UNMARK :: c2) s2 F2 r2 hthrow
                      exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                    · simp [Option.bind_some, if_neg hc] at h
          | transaction ℓ0 Θ =>
              -- non-throws forward: body raises ⇒ handle forwards ⇒ raised, contradicting term.
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                    -- transaction-install + normal return (mirror of throws-return): existential =
                    -- `updateStates hs σ1` (a transaction frame stores no `state` ⇒ σ' = σ1).
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 cc (.ret v :: ss) (updateStates hs σ1) = some r2 →
                        (∃ F', exec F' (compile M (Instr.UNMARK :: cc)) ss
                          ({ handler := Handler.transaction ℓ0 Θ, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (updateStates hs σ1) ∧ HMut hs (updateStates hs σ1) := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { handler := Handler.transaction ℓ0 Θ, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hns : ∀ ℓ s, fr.handler ≠ Handler.state ℓ s := by rw [hfrdef]; intro ℓ s; simp
                      have hCinstall : Corr σ (fr :: hs) := Corr_install_nonstate fr hns hC
                      obtain ⟨hsM, hCM, hmutM, kM⟩ := ihT M σ (.ret v) σ1 hM (fr :: hs) hCinstall
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have hCtail := Corr_pop_nonstate hns hmutM hCM
                      have htaileq : tail = updateStates hs σ1 := updateStates_eq (HMut.tail hmutM) hCtail
                      have hstep : exec (F2+1) (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ (HMut.tail hmutM)⟩
                    obtain ⟨_, hCf, hmutf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨updateStates hs σ1, hCf, hmutf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.lam M2), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
    · -- RAISED PART
      intro M σ ℓ op v σ' h hs hC
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | up ℓ2 op2 v2 =>
          simp only [evalD] at h
          cases hg : σ.get? ℓ2 with
          | none =>
              rw [hg] at h
              simp only [Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
              obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
              -- no state frame for ℓ2 ⇒ machine OP falls through to unwindFind = throwOutcome = hr
              have hus : updateStates hs σ = hs := updateStates_self hC
              refine ⟨⟨by rw [hus]; exact hC, by rw [hus]; exact HMut.refl hs⟩, fun c s F r hr => ?_⟩
              rw [updateStates_self hC] at hr
              refine ⟨F+1, ?_⟩
              have hns : stateUpdate ℓ2 op2 v2 hs = none := by
                apply stateUpdate_none_of_get?_none; rw [← Corr.get? hC ℓ2]; exact hg
              simp only [compile, exec, hns]; exact hr
          | some sv =>
              rw [hg] at h
              by_cases hop : op2 = "get"
              · simp only [if_pos hop, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
              · by_cases hop2 : op2 = "put"
                · simp only [if_neg hop, if_pos hop2, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                · simp only [if_neg hop, if_neg hop2, Option.some.injEq, Prod.mk.injEq,
                    Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                  -- op ∉ {get,put} (source-unreachable — a state label carries only get/put). evalD
                  -- RAISES; `stateUpdate` returns `none` (it guards op ∈ {get,put}), so the machine OP
                  -- falls straight to the `unwindFind`/throw path = `throwOutcome` = `hr`.
                  have hus : updateStates hs σ = hs := updateStates_self hC
                  refine ⟨⟨by rw [hus]; exact hC, by rw [hus]; exact HMut.refl hs⟩, fun c s F r hr => ?_⟩
                  rw [updateStates_self hC] at hr
                  refine ⟨F+1, ?_⟩
                  have hsu : stateUpdate ℓ2 op2 v2 hs = none :=
                    stateUpdate_none_of_non_getput ℓ2 v2 hs hop hop2
                  simp only [compile, exec, hsu]; exact hr
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                obtain ⟨hpair, kR⟩ := ihR M σ ℓ' op' w σ1 hM hs hC
                exact ⟨hpair, fun c s F r hr => by
                  obtain ⟨F1, hF1⟩ := kR (Instr.SUBST N :: c) s F r hr
                  exact ⟨F1, by simpa [compile] using hF1⟩⟩
            | (.term (.ret v0), σ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hmutM, kM⟩ := ihT M σ (.ret v0) σ1 hM hs hC
                -- the inner raise is over hsM = updateStates hs σ1; re-base via composition so the inner
                -- `ihR` over `updateStates hsM σ'` reuses the outer `hr` over `updateStates hs σ'`. The
                -- raised IH's at-raise `Corr σ' (updateStates hsM σ')` IS the covering `updateStates_congr`
                -- needs.
                obtain ⟨⟨hCr, hmutr⟩, kR⟩ := ihR (Comp.subst v0 N) σ1 ℓ op v σ' h hsM hCM
                have hreb : updateStates hsM σ' = updateStates hs σ' := updateStates_congr_HMut σ' hmutM hCr
                refine ⟨⟨hreb ▸ hCr, HMut.trans hmutM (hreb ▸ hmutr)⟩, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR c s F r (by rw [hreb]; exact hr)
                have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v0 :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.SUBST N :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.lam a), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term (.unfold a), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hpair, kR⟩ := ihR M σ ℓ op v σ' h hs hC
              exact ⟨hpair, fun c s F r hr => by
                obtain ⟨F', hF'⟩ := kR c s F r hr; exact ⟨F', by simpa only [compile] using hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | app M v0 =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                obtain ⟨hpair, kR⟩ := ihR M σ ℓ' op' w σ1 hM hs hC
                exact ⟨hpair, fun c s F r hr => by
                  obtain ⟨F1, hF1⟩ := kR (Instr.APP v0 :: c) s F r hr
                  exact ⟨F1, by simpa [compile] using hF1⟩⟩
            | (.term (.lam N), σ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hmutM, kM⟩ := ihT M σ (.lam N) σ1 hM hs hC
                obtain ⟨⟨hCr, hmutr⟩, kR⟩ := ihR (Comp.subst v0 N) σ1 ℓ op v σ' h hsM hCM
                have hreb : updateStates hsM σ' = updateStates hs σ' := updateStates_congr_HMut σ' hmutM hCr
                refine ⟨⟨hreb ▸ hCr, HMut.trans hmutM (hreb ▸ hmutr)⟩, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR c s F r (by rw [hreb]; exact hr)
                have hstep : exec (F1+1) (Instr.APP v0 :: c) (.lam N :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.APP v0 :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.ret w), _), h => simp [Option.bind] at h
            | (.term (.letC a b), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term (.unfold a), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                    -- at-raise PAIR (store/stack only, continuation-independent): one IH over a dummy
                    -- install frame, popped through the state frame (`raisedPair_pop_state`).
                    have hpair : Corr σ1.tail (updateStates hs σ1.tail) ∧ HMut hs (updateStates hs σ1.tail) := by
                      set fr0 : HFrame := { handler := Handler.state ℓ0 s0, savedCode := [], savedStack := [] }
                        with hfr0
                      obtain ⟨⟨hCr, hmutr⟩, _⟩ :=
                        ihR M (σ.push ℓ0 s0) ℓ' op' w σ1 hM (fr0 :: hs)
                          (Corr_install ℓ0 s0 fr0 (by rw [hfr0]) hC)
                      exact raisedPair_pop_state (by rw [hfr0]) hCr hmutr
                    refine ⟨hpair, fun c s F r hr => ?_⟩
                    -- the IMPLICATION installs the REAL frame (savedCode/Stack = c/s, the MARK target).
                    set fr : HFrame := { handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, kR⟩ := ihR M (σ.push ℓ0 s0) ℓ' op' w σ1 hM (fr :: hs)
                      (Corr_install ℓ0 s0 fr (by rw [hfrdef]) hC)
                    -- inner needs throwOutcome over `updateStates (fr::hs) σ1`; the state frame is skipped
                    -- by the throws-unwind, reducing it to `updateStates hs σ1.tail` = `hr`.
                    have hfwd : throwOutcome F ℓ' op' w (updateStates (fr :: hs) σ1) = some r := by
                      have hskip : throwOutcome F ℓ' op' w (updateStates (fr :: hs) σ1)
                          = throwOutcome F ℓ' op' w (updateStates hs σ1.tail) := by
                        cases σ1 with
                        | nil =>
                            simp only [updateStates, hfrdef, List.tail]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)
                        | cons p σ1' =>
                            obtain ⟨ℓa, wa⟩ := p
                            simp only [updateStates, hfrdef, List.tail]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)
                      rw [hskip]; exact hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.ret v0), _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp [if_pos hk] at h
                    · simp only [if_neg hk, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                      obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                      have hns0 : ∀ ℓ s, (Handler.throws ℓ0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                      have hpair : Corr σ1 (updateStates hs σ1) ∧ HMut hs (updateStates hs σ1) := by
                        set fr0 : HFrame := { handler := Handler.throws ℓ0, savedCode := [], savedStack := [] }
                        obtain ⟨⟨hCr, hmutr⟩, _⟩ :=
                          ihR M σ ℓ' op' w σ1 hM (fr0 :: hs) (Corr_install_nonstate fr0 hns0 hC)
                        exact raisedPair_pop_nonstate hns0 hCr hmutr
                      refine ⟨hpair, fun c s F r hr => ?_⟩
                      set fr : HFrame := { handler := Handler.throws ℓ0, savedCode := c, savedStack := s }
                        with hfrdef
                      obtain ⟨_, kR⟩ := ihR M σ ℓ' op' w σ1 hM (fr :: hs) (Corr_install_nonstate fr hns0 hC)
                      -- inner needs throwOutcome over `updateStates (fr::hs) σ1` = `fr :: updateStates hs σ1`
                      -- (throws frame copies through); fr is throws but does NOT catch (if_neg hk) ⇒ skipped.
                      have hfwd : throwOutcome F ℓ' op' w (updateStates (fr :: hs) σ1) = some r := by
                        simp only [updateStates, hfrdef, throwOutcome, unwindFind, if_neg hk]; exact hr
                      obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                      exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.ret v0), _), h => simp [Option.bind] at h
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
          | transaction ℓ0 Θ =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                    have hns0 : ∀ ℓ s, (Handler.transaction ℓ0 Θ) ≠ Handler.state ℓ s := by intro ℓ s; simp
                    have hpair : Corr σ1 (updateStates hs σ1) ∧ HMut hs (updateStates hs σ1) := by
                      set fr0 : HFrame := { handler := Handler.transaction ℓ0 Θ, savedCode := [], savedStack := [] }
                      obtain ⟨⟨hCr, hmutr⟩, _⟩ :=
                        ihR M σ ℓ' op' w σ1 hM (fr0 :: hs) (Corr_install_nonstate fr0 hns0 hC)
                      exact raisedPair_pop_nonstate hns0 hCr hmutr
                    refine ⟨hpair, fun c s F r hr => ?_⟩
                    set fr : HFrame := { handler := Handler.transaction ℓ0 Θ, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, kR⟩ := ihR M σ ℓ' op' w σ1 hM (fr :: hs) (Corr_install_nonstate fr hns0 hC)
                    -- inner needs throwOutcome over `updateStates (fr::hs) σ1` = `fr :: updateStates hs σ1`
                    -- (transaction frame copies through); the txn frame is skipped by the throws-unwind.
                    have hfwd : throwOutcome F ℓ' op' w (updateStates (fr :: hs) σ1) = some r := by
                      simp only [updateStates, hfrdef]
                      exact (throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)).trans hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.ret v0), _), h => simp [Option.bind] at h
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h


/-- Headline: compiling a closed computation and running it on the empty stack/store yields exactly
`[t]` where `evalD n [] M = some (.term t, σ')` (the convergent spine, now over the resumptive-state
store-thread). `compile_correct` analogue of `Bang.Calc`; the `c=[]`, `s=[]`, `hs=[]` corollary of
`sim` (`Corr [] []` holds by `rfl`, the empty store mirrors the empty HStack). -/
theorem compile_correct (n : Nat) (M : Comp) (t : Comp) (σ' : SStore)
    (h : evalD n [] M = some (.term t, σ')) :
    ∃ F, exec F (compile M []) [] [] = some [t] := by
  have hbase : exec 1 [] (t :: []) [] = some [t] := by simp [exec]
  obtain ⟨hsf, _, hmutf, k⟩ := (sim n).1 M [] t σ' h [] rfl
  -- HMut [] hsf forces hsf = [] (a closed program at empty HStack ends at empty), so the continuation
  -- runs on the empty stack — `hbase`.
  have hempty : hsf = [] := by cases hsf with | nil => rfl | cons => simp [HMut] at hmutf
  subst hempty
  obtain ⟨F, hF⟩ := k [] [] 1 [t] hbase
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

/-! ### D3 store ↔ kernel-`EvalCtx` correspondence (state)

The kernel resumes state in its `EvalCtx`: a `handleF (state ℓ s)` frame stores `s`, and `dispatch`
threads it on `get`/`put` (KEEP `Kᵢ`, reinstall `handleF (state ℓ s')` — `Operational.lean`
`dispatchOn`). `evalD`'s store σ is the kernel side's `state` frames projected, exactly mirroring the
machine-side `Corr σ hs`/`hsStates`/`updateStates` triad but over `EvalCtx`. -/

/-- Project a kernel `EvalCtx` to the store it mirrors: the `handleF (state ℓ s)` frames, innermost
first, as `(ℓ, s)` entries. The `Config.run`-side analog of `hsStates`. -/
def ctxStates : Bang.EvalCtx → SStore
  | []                              => []
  | Frame.handleF (.state ℓ s) :: K => (ℓ, s) :: ctxStates K
  | _ :: K                          => ctxStates K

/-- The bridge's D3 invariant: `evalD`'s threaded store IS the kernel context's active state frames. -/
def CtxCorr (σ : SStore) (K : Bang.EvalCtx) : Prop := σ = ctxStates K

/-- Overwrite each `state` frame's stored value in `K` with the store `σ` (consumed in order) — the
kernel context AFTER M's state ops have fired (the at-term/at-raise context the continuation runs on).
The `Config.run`-side analog of `updateStates`; non-state frames pass through. -/
def updateCtxStates : Bang.EvalCtx → SStore → Bang.EvalCtx
  | [],                                  _ => []
  | Frame.handleF (.state ℓ0 _) :: K, σ =>
      match σ with
      | (_, v) :: σ' => Frame.handleF (.state ℓ0 v) :: updateCtxStates K σ'
      | []           => Frame.handleF (.state ℓ0 default) :: updateCtxStates K []  -- σ-exhausted (∉ Corr)
  | fr :: K,                             σ => fr :: updateCtxStates K σ

/-- Under `CtxCorr`, `updateCtxStates` is the identity (overwriting each value with itself). -/
theorem updateCtxStates_self {σ : SStore} {K : Bang.EvalCtx} (hC : CtxCorr σ K) :
    updateCtxStates K σ = K := by
  unfold CtxCorr at hC; subst hC
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF h =>
        cases h with
        | state ℓ s => simp only [ctxStates, updateCtxStates]; rw [ih]
        | throws ℓ => simp only [ctxStates, updateCtxStates]; rw [ih]
        | transaction ℓ Θ => simp only [ctxStates, updateCtxStates]; rw [ih]
    | letF N => simp only [ctxStates, updateCtxStates]; rw [ih]
    | appF v => simp only [ctxStates, updateCtxStates]; rw [ih]

/-- A NON-state frame is transparent to `updateCtxStates`. -/
theorem updateCtxStates_cons_nonstate {fr : Bang.Frame} {K : Bang.EvalCtx} (σ : SStore)
    (hns : ∀ ℓ s, fr ≠ Frame.handleF (.state ℓ s)) :
    updateCtxStates (fr :: K) σ = fr :: updateCtxStates K σ := by
  cases fr with
  | handleF h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns ℓ s)
      | throws ℓ => simp only [updateCtxStates]
      | transaction ℓ Θ => simp only [updateCtxStates]
  | letF N => simp only [updateCtxStates]
  | appF v => simp only [updateCtxStates]

/-- `updateCtxStates` depends only on `K`'s STATE-FRAME STRUCTURE, which it preserves ⇒ it is
idempotent in the K-slot: `updateCtxStates (updateCtxStates K σ1) σ = updateCtxStates K σ`. Lets the
spine compose the at-M-term context with the continuation's update. Induction on `K`. -/
theorem updateCtxStates_updateCtxStates : ∀ {K : Bang.EvalCtx} (σ1 σ : SStore),
    updateCtxStates (updateCtxStates K σ1) σ = updateCtxStates K σ := by
  intro K
  induction K with
  | nil => intro σ1 σ; rfl
  | cons fr K ih =>
    intro σ1 σ
    cases fr with
    | handleF h =>
        cases h with
        | state ℓ s =>
            cases σ1 with
            | nil =>
                cases σ with
                | nil => simp only [updateCtxStates]; rw [ih]
                | cons p σ' => simp only [updateCtxStates]; rw [ih]
            | cons p1 σ1' =>
                cases σ with
                | nil => simp only [updateCtxStates]; rw [ih]
                | cons p σ' => simp only [updateCtxStates]; rw [ih]
        | throws ℓ => simp only [updateCtxStates]; rw [ih]
        | transaction ℓ Θ => simp only [updateCtxStates]; rw [ih]
    | letF N => simp only [updateCtxStates]; rw [ih]
    | appF v => simp only [updateCtxStates]; rw [ih]

/-- A NON-state frame carries no store entry ⇒ `CtxCorr` passes through its install (and pop). -/
theorem CtxCorr_cons_nonstate {σ : SStore} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ ℓ s, fr ≠ Frame.handleF (.state ℓ s)) (hC : CtxCorr σ K) :
    CtxCorr σ (fr :: K) := by
  unfold CtxCorr at hC ⊢; rw [hC]
  cases fr with
  | handleF h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns ℓ s)
      | throws ℓ => simp only [ctxStates]
      | transaction ℓ Θ => simp only [ctxStates]
  | letF N => simp only [ctxStates]
  | appF v => simp only [ctxStates]

/-- A `state ℓ s` install PUSHES `(ℓ ↦ s)` on the store, preserving `CtxCorr`. -/
theorem CtxCorr_install {σ : SStore} {ℓ : Bang.EffectRow.Label} {s : Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ K) : CtxCorr (σ.push ℓ s) (Frame.handleF (.state ℓ s) :: K) := by
  unfold CtxCorr at hC ⊢; rw [hC]; simp only [ctxStates, SStore.push]

/-- `at-term/at-raise` non-state install: `updateCtxStates (fr :: K) σ' = fr :: updateCtxStates K σ'`
and its `CtxCorr`/structure pass through (the non-state install case of the run_evalD spine). -/
theorem CtxCorr_updateCtx_nonstate {σ' : SStore} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ ℓ s, fr ≠ Frame.handleF (.state ℓ s))
    (hC : CtxCorr σ' (updateCtxStates (fr :: K) σ')) : CtxCorr σ' (updateCtxStates K σ') := by
  rw [updateCtxStates_cons_nonstate σ' hns] at hC
  unfold CtxCorr at hC ⊢
  cases fr with
  | handleF h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns ℓ s)
      | throws ℓ => simpa only [ctxStates] using hC
      | transaction ℓ Θ => simpa only [ctxStates] using hC
  | letF N => simpa only [ctxStates] using hC
  | appF v => simpa only [ctxStates] using hC

/-- `handle (state ℓ0)`-POP at-term correspondence: from the body's at-term `CtxCorr σ1 (updateCtxStates
(handleF (state ℓ0 s0) :: K) σ1)`, the popped pair holds — `σ1.tail` covers `K` and the resume context
after the handler-return is `updateCtxStates K σ1.tail`. The kernel `handleF _ :: K, ret v ↦ K, ret v`
(handler-return = identity). Forces σ1 non-empty (its head IS the installed state frame). -/
theorem CtxCorr_updateCtx_pop_state {σ1 : SStore} {ℓ0 : Bang.EffectRow.Label} {s0 : Val}
    {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (updateCtxStates (Frame.handleF (.state ℓ0 s0) :: K) σ1)) :
    CtxCorr σ1.tail (updateCtxStates K σ1.tail) ∧
      updateCtxStates (Frame.handleF (.state ℓ0 s0) :: K) σ1
        = Frame.handleF (.state ℓ0 (σ1.headD (default, default)).2) :: updateCtxStates K σ1.tail := by
  cases σ1 with
  | nil =>
      exfalso; unfold CtxCorr at hC
      simp only [updateCtxStates, ctxStates] at hC
      exact (List.cons_ne_nil _ _ hC.symm)
  | cons p σ1' =>
      obtain ⟨ℓa, wa⟩ := p
      have hupd : updateCtxStates (Frame.handleF (.state ℓ0 s0) :: K) ((ℓa, wa) :: σ1')
          = Frame.handleF (.state ℓ0 wa) :: updateCtxStates K σ1' := by
        simp only [updateCtxStates]
      rw [hupd] at hC
      refine ⟨?_, ?_⟩
      · unfold CtxCorr at hC ⊢
        simp only [ctxStates, List.tail] at hC ⊢
        exact (List.cons.injEq _ _ _ _).mp hC |>.2
      · simp only [List.headD, List.tail]; exact hupd

/-- `splitAt` RECONSTRUCTS its input: `K = Kᵢ ++ handleF h :: Kₒ`. The decomposition is lossless —
the inner prefix, the catching frame, and the outer suffix re-concatenate to `K`. Induction on `K`. -/
theorem splitAt_reconstruct {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {h : Handler},
      Bang.splitAt K ℓ op = some (Kᵢ, h, Kₒ) → Kᵢ ++ Frame.handleF h :: Kₒ = K := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hs; simp [Bang.splitAt] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ h hs
    cases fr with
    | handleF h0 =>
        simp only [Bang.splitAt] at hs
        by_cases hc : Bang.handlesOp h0 ℓ op = true
        · rw [if_pos hc] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs; simp
        · rw [if_neg hc] at hs
          cases hsp : Bang.splitAt K ℓ op with
          | none => rw [hsp] at hs; simp at hs
          | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                      obtain ⟨rfl, rfl, rfl⟩ := hs; simp only [List.cons_append]; rw [ih hsp]
    | letF N =>
        simp only [Bang.splitAt] at hs
        cases hsp : Bang.splitAt K ℓ op with
        | none => rw [hsp] at hs; simp at hs
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                    obtain ⟨rfl, rfl, rfl⟩ := hs; simp only [List.cons_append]; rw [ih hsp]
    | appF w =>
        simp only [Bang.splitAt] at hs
        cases hsp : Bang.splitAt K ℓ op with
        | none => rw [hsp] at hs; simp at hs
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                    obtain ⟨rfl, rfl, rfl⟩ := hs; simp only [List.cons_append]; rw [ih hsp]

/-- `splitAt` for a `get`/`put` on `ℓ` finds a `state ℓ s` frame whose stored `s` is exactly the
nearest `ctxStates`-value (`(ctxStates K).get? ℓ`). Induction on `K`. -/
theorem splitAt_state_value {ℓ : Bang.EffectRow.Label} {op : Bang.OpId}
    (hop : op = "get" ∨ op = "put") :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {s : Val},
      Bang.splitAt K ℓ op = some (Kᵢ, Handler.state ℓ s, Kₒ) →
        (ctxStates K).get? ℓ = some s := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ s hs; simp [Bang.splitAt] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ s hs
    cases fr with
    | handleF h0 =>
        cases hh : h0 with
        | state ℓ0 s0 =>
            simp only [Bang.splitAt, hh] at hs
            by_cases hc : ℓ0 = ℓ
            · subst hc
              have hcatch : Bang.handlesOp (Handler.state ℓ0 s0) ℓ0 op = true := by
                cases hop with
                | inl h => subst h; simp [Bang.handlesOp]
                | inr h => subst h; simp [Bang.handlesOp]
              rw [if_pos hcatch] at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨_, ⟨rfl, rfl⟩, _⟩ := hs
              simp [ctxStates, SStore.get?, List.find?]
            · have hnc : Bang.handlesOp (Handler.state ℓ0 s0) ℓ op = false := by
                simp [Bang.handlesOp, hc]
              rw [if_neg (by simp [hnc])] at hs
              cases hsp : Bang.splitAt K ℓ op with
              | none => rw [hsp] at hs; simp at hs
              | some t =>
                  obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                  obtain ⟨_, rfl, _⟩ := hs
                  have := ih hsp
                  simpa [ctxStates, SStore.get?, List.find?, hc] using this
        | throws ℓ0 =>
            simp only [Bang.splitAt, hh] at hs
            have hnc : Bang.handlesOp (Handler.throws ℓ0) ℓ op = false := by
              cases hop with
              | inl h => subst h; simp [Bang.handlesOp]
              | inr h => subst h; simp [Bang.handlesOp]
            rw [if_neg (by simp [hnc])] at hs
            cases hsp : Bang.splitAt K ℓ op with
            | none => rw [hsp] at hs; simp at hs
            | some t =>
                obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨_, rfl, _⟩ := hs
                simpa [ctxStates] using ih hsp
        | transaction ℓ0 Θ0 =>
            simp only [Bang.splitAt, hh] at hs
            have hnc : Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ op = false := by
              cases hop with
              | inl h => subst h; simp [Bang.handlesOp]
              | inr h => subst h; simp [Bang.handlesOp]
            rw [if_neg (by simp [hnc])] at hs
            cases hsp : Bang.splitAt K ℓ op with
            | none => rw [hsp] at hs; simp at hs
            | some t =>
                obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨_, rfl, _⟩ := hs
                simpa [ctxStates] using ih hsp
    | letF N =>
        simp only [Bang.splitAt] at hs
        cases hsp : Bang.splitAt K ℓ op with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxStates] using ih hsp
    | appF w =>
        simp only [Bang.splitAt] at hs
        cases hsp : Bang.splitAt K ℓ op with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxStates] using ih hsp

/-- `splitAt` for a `get`/`put` on `ℓ` SUCCEEDS (finds a state frame) whenever `ℓ` has an active
`state` frame, i.e. `(ctxStates K).get? ℓ = some s`. The existence companion of `splitAt_state_value`.
Induction on `K`. -/
theorem splitAt_state_some {ℓ : Bang.EffectRow.Label} {op : Bang.OpId}
    (hop : op = "get" ∨ op = "put") :
    ∀ {K : Bang.EvalCtx} {s : Val}, (ctxStates K).get? ℓ = some s →
      ∃ Kᵢ Kₒ, Bang.splitAt K ℓ op = some (Kᵢ, Handler.state ℓ s, Kₒ) := by
  intro K
  induction K with
  | nil => intro s hg; simp [ctxStates, SStore.get?] at hg
  | cons fr K ih =>
    intro s hg
    cases fr with
    | handleF h0 =>
        cases h0 with
        | state ℓ0 s0 =>
            by_cases hc : ℓ0 = ℓ
            · subst hc
              simp only [ctxStates, SStore.get?, List.find?, decide_true, Option.map_some,
                Option.some.injEq] at hg
              subst hg
              have hcatch : Bang.handlesOp (Handler.state ℓ0 s0) ℓ0 op = true := by
                cases hop with
                | inl h => subst h; simp [Bang.handlesOp]
                | inr h => subst h; simp [Bang.handlesOp]
              exact ⟨[], K, by simp only [Bang.splitAt, if_pos hcatch]⟩
            · have hg' : (ctxStates K).get? ℓ = some s := by
                simp only [ctxStates, SStore.get?, List.find?, hc, decide_false,
                  Bool.false_eq_true, if_false] at hg; simpa [SStore.get?] using hg
              obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
              have hnc : ¬ Bang.handlesOp (Handler.state ℓ0 s0) ℓ op = true := by
                simp [Bang.handlesOp, hc]
              exact ⟨Frame.handleF (Handler.state ℓ0 s0) :: Kᵢ, Kₒ, by
                simp only [Bang.splitAt, if_neg hnc, hsp, Option.map_some]⟩
        | throws ℓ0 =>
            have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
            obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
            have hnc : ¬ Bang.handlesOp (Handler.throws ℓ0) ℓ op = true := by
              cases hop with
              | inl h => subst h; simp [Bang.handlesOp]
              | inr h => subst h; simp [Bang.handlesOp]
            exact ⟨Frame.handleF (Handler.throws ℓ0) :: Kᵢ, Kₒ, by
              simp only [Bang.splitAt, if_neg hnc, hsp, Option.map_some]⟩
        | transaction ℓ0 Θ0 =>
            have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
            obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
            have hnc : ¬ Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ op = true := by
              cases hop with
              | inl h => subst h; simp [Bang.handlesOp]
              | inr h => subst h; simp [Bang.handlesOp]
            exact ⟨Frame.handleF (Handler.transaction ℓ0 Θ0) :: Kᵢ, Kₒ, by
              simp only [Bang.splitAt, if_neg hnc, hsp, Option.map_some]⟩
    | letF N =>
        have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
        obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
        exact ⟨Frame.letF N :: Kᵢ, Kₒ, by simp only [Bang.splitAt, hsp, Option.map_some]⟩
    | appF w =>
        have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
        obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
        exact ⟨Frame.appF w :: Kᵢ, Kₒ, by simp only [Bang.splitAt, hsp, Option.map_some]⟩

/-- A `state`-`get` dispatch RESUMES in place: under `(ctxStates K).get? ℓ = some s`, the kernel finds
the nearest `state ℓ s` frame and resumes `(K, .ret s)` — context structurally unchanged (same frame
re-installed; `get` does not mutate). Via `splitAt_state_some` + `splitAt_reconstruct`. -/
theorem dispatch_state_get {ℓ : Bang.EffectRow.Label} {v s : Val} {K : Bang.EvalCtx}
    (hg : (ctxStates K).get? ℓ = some s) : Bang.dispatch K ℓ "get" v = some (K, .ret s) := by
  obtain ⟨Kᵢ, Kₒ, hsp⟩ := splitAt_state_some (Or.inl rfl) hg
  have hrec : Kᵢ ++ Frame.handleF (Handler.state ℓ s) :: Kₒ = K := splitAt_reconstruct hsp
  simp only [Bang.dispatch, hsp, Option.bind_some, Bang.dispatchOn, beq_self_eq_true, if_true]
  rw [hrec]

/-- A `state`-`put` dispatch RESUMES with the value updated: finds `state ℓ s`, reinstalls `state ℓ w`,
resumes `(updateCtxStates K ((ctxStates K).put ℓ w), .ret unit)` — the context `K` with ℓ's nearest
state frame's value set to `w`. Induction on `K` (mirroring `splitAt`'s walk + `dispatchOn` put). -/
theorem updateCtxStates_put_split {ℓ : Bang.EffectRow.Label} {w : Val} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {s : Val},
      Bang.splitAt K ℓ "put" = some (Kᵢ, Handler.state ℓ s, Kₒ) →
        updateCtxStates K ((ctxStates K).put ℓ w) = Kᵢ ++ Frame.handleF (Handler.state ℓ w) :: Kₒ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ s hsp; simp [Bang.splitAt] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ s hsp
    cases fr with
    | handleF h0 =>
        cases h0 with
        | state ℓ0 s0 =>
            by_cases hc : ℓ0 = ℓ
            · subst hc
              -- the head frame catches ⇒ splitAt = ([], state ℓ0 s0, K); put updates head value.
              simp only [Bang.splitAt, Bang.handlesOp, beq_self_eq_true, Bool.or_true, Bool.and_true,
                decide_true, if_true, Option.some.injEq, Prod.mk.injEq] at hsp
              obtain ⟨rfl, _, rfl⟩ := hsp
              simp only [ctxStates, SStore.put, if_true, updateCtxStates, List.nil_append]
              rw [updateCtxStates_self rfl]
            · -- head doesn't catch ⇒ splitAt recurses; put updates a DEEPER frame.
              have hnc : ¬ Bang.handlesOp (Handler.state ℓ0 s0) ℓ "put" = true := by
                simp [Bang.handlesOp, hc]
              simp only [Bang.splitAt, if_neg hnc] at hsp
              cases hsp2 : Bang.splitAt K ℓ "put" with
              | none => rw [hsp2] at hsp; simp at hsp
              | some t =>
                  obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                  obtain ⟨rfl, rfl, rfl⟩ := hsp
                  simp only [ctxStates, SStore.put, hc, if_false, updateCtxStates, List.cons_append]
                  rw [ih hsp2]
        | throws ℓ0 =>
            have hnc : ¬ Bang.handlesOp (Handler.throws ℓ0) ℓ "put" = true := by simp [Bang.handlesOp]
            simp only [Bang.splitAt, if_neg hnc] at hsp
            cases hsp2 : Bang.splitAt K ℓ "put" with
            | none => rw [hsp2] at hsp; simp at hsp
            | some t =>
                obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := hsp
                simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]
        | transaction ℓ0 Θ0 =>
            have hnc : ¬ Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ "put" = true := by simp [Bang.handlesOp]
            simp only [Bang.splitAt, if_neg hnc] at hsp
            cases hsp2 : Bang.splitAt K ℓ "put" with
            | none => rw [hsp2] at hsp; simp at hsp
            | some t =>
                obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := hsp
                simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]
    | letF N =>
        simp only [Bang.splitAt] at hsp
        cases hsp2 : Bang.splitAt K ℓ "put" with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp
            simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]
    | appF w0 =>
        simp only [Bang.splitAt] at hsp
        cases hsp2 : Bang.splitAt K ℓ "put" with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp
            simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]

theorem dispatch_state_put {ℓ : Bang.EffectRow.Label} {w s : Val} {K : Bang.EvalCtx}
    (hg : (ctxStates K).get? ℓ = some s) :
    Bang.dispatch K ℓ "put" w
      = some (updateCtxStates K ((ctxStates K).put ℓ w), .ret .vunit) := by
  obtain ⟨Kᵢ, Kₒ, hsp⟩ := splitAt_state_some (Or.inr rfl) hg
  rw [updateCtxStates_put_split hsp]
  simp only [Bang.dispatch, hsp, Option.bind_some, Bang.dispatchOn, beq_iff_eq,
    if_neg (by decide : ¬ ("put" = "get"))]

/-- After a `put`, the resume context's `ctxStates` IS the put-updated store: `ctxStates
(updateCtxStates K (σ.put ℓ w)) = (ctxStates K).put ℓ w` where σ = ctxStates K. The `CtxCorr`-
preservation of a state `put` (the kernel `dispatchOn`-put restores the D3 correspondence). Via
`updateCtxStates_put_split` + `ctxStates` of the split reconstruction. Induction on `K`. -/
theorem ctxStates_updateCtxStates_put {ℓ : Bang.EffectRow.Label} {w : Val} :
    ∀ {K : Bang.EvalCtx} {s : Val}, (ctxStates K).get? ℓ = some s →
      ctxStates (updateCtxStates K ((ctxStates K).put ℓ w)) = (ctxStates K).put ℓ w := by
  intro K
  induction K with
  | nil => intro s hg; simp [ctxStates, SStore.get?] at hg
  | cons fr K ih =>
    intro s hg
    cases fr with
    | handleF h0 =>
        cases h0 with
        | state ℓ0 s0 =>
            by_cases hc : ℓ0 = ℓ
            · subst hc
              simp only [ctxStates, SStore.put, if_true, updateCtxStates]
              rw [updateCtxStates_self rfl]
            · have hg' : (ctxStates K).get? ℓ = some s := by
                simp only [ctxStates, SStore.get?, List.find?, hc, decide_false,
                  Bool.false_eq_true, if_false] at hg; simpa [SStore.get?] using hg
              simp only [ctxStates, SStore.put, hc, if_false, updateCtxStates]; rw [ih hg']
        | throws ℓ0 =>
            have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
            simp only [ctxStates, updateCtxStates]; rw [ih hg']
        | transaction ℓ0 Θ0 =>
            have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
            simp only [ctxStates, updateCtxStates]; rw [ih hg']
    | letF N =>
        have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
        simp only [ctxStates, updateCtxStates]; rw [ih hg']
    | appF v0 =>
        have hg' : (ctxStates K).get? ℓ = some s := by simpa only [ctxStates] using hg
        simp only [ctxStates, updateCtxStates]; rw [ih hg']

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
    (∀ M σ t σ', evalD fe σ M = some (.term t, σ') →
      ∀ (K : Bang.EvalCtx), CtxCorr σ K →
        CtxCorr σ' (updateCtxStates K σ') ∧
        ∀ (n : Nat) (r : Bang.Result Val),
          Bang.Config.run n (updateCtxStates K σ', t) = r → ∃ F, Bang.Config.run F (K, M) = r)
    ∧ (∀ M σ ℓ v σ', evalD fe σ M = some (.raised ℓ "raise" v, σ') →
      ∀ (K : Bang.EvalCtx), CtxCorr σ K →
        CtxCorr σ' (updateCtxStates K σ') ∧
        ∀ (n : Nat) (r : Bang.Result Val),
          dispatchRun n (updateCtxStates K σ') ℓ "raise" v = r → ∃ F, Bang.Config.run F (K, M) = r) := by
  intro fe
  induction fe with
  | zero => exact ⟨fun M σ t σ' h => by simp [evalD] at h, fun M σ ℓ v σ' h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M σ t σ' h K hCtx
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
          rw [updateCtxStates_self hCtx]
          exact ⟨hCtx, fun n r hr => ⟨n, hr⟩⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
          rw [updateCtxStates_self hCtx]
          exact ⟨hCtx, fun n r hr => ⟨n, hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.ret v), σ1), h =>
                simp only [Option.bind_some] at h
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                obtain ⟨hCM, kM⟩ := ihT M σ (.ret v) σ1 hM (Frame.letF N :: K) hCletF
                have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                  CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                obtain ⟨hCf, kN⟩ := ihT (Comp.subst v N) σ1 t σ' h (updateCtxStates K σ1) hCM'
                rw [updateCtxStates_updateCtxStates] at hCf
                refine ⟨hCf, fun n r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kN n r (by rw [updateCtxStates_updateCtxStates]; exact hr)
                have hstep : Bang.Config.run (F2+1) (Frame.letF N :: updateCtxStates K σ1, .ret v) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.lam a), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term (.unfold a), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hCf, kf⟩ := ihT M σ t σ' h K hCtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kf n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | app M v =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.lam N), σ1), h =>
                simp only [Option.bind_some] at h
                have hCappF : CtxCorr σ (Frame.appF v :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                obtain ⟨hCM, kM⟩ := ihT M σ (.lam N) σ1 hM (Frame.appF v :: K) hCappF
                have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                  CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                obtain ⟨hCf, kN⟩ := ihT (Comp.subst v N) σ1 t σ' h (updateCtxStates K σ1) hCM'
                rw [updateCtxStates_updateCtxStates] at hCf
                refine ⟨hCf, fun n r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kN n r (by rw [updateCtxStates_updateCtxStates]; exact hr)
                have hstep : Bang.Config.run (F2+1) (Frame.appF v :: updateCtxStates K σ1, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.ret w), _), h => simp [Option.bind] at h
            | (.term (.letC a b), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _), h => simp [Option.bind] at h
      | up ℓ2 op2 v2 =>
          simp only [evalD] at h
          cases hg : σ.get? ℓ2 with
          | none =>
              rw [hg] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨ht, _⟩ := h; exact absurd ht (by simp)
          | some sv =>
              rw [hg] at h
              by_cases hop : op2 = "get"
              · -- state GET: evalD returns `term (ret sv)`, σ unchanged. Kernel: dispatch resumes (K, ret sv).
                simp only [if_pos hop, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ; subst hop
                rw [updateCtxStates_self hCtx]
                refine ⟨hCtx, fun n r hr => ?_⟩
                have hgc : (ctxStates K).get? ℓ2 = some sv := by rw [← hCtx]; exact hg
                refine ⟨n+1, ?_⟩
                simp only [Bang.Config.run, Source.step, dispatch_state_get hgc]; exact hr
              · by_cases hop2 : op2 = "put"
                · -- state PUT: evalD threads σ.put; kernel dispatch reinstalls (updateCtxStates …, ret unit).
                  simp only [if_neg hop, if_pos hop2, Option.some.injEq, Prod.mk.injEq,
                    Outcome.term.injEq] at h
                  obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ; subst hop2
                  subst hCtx
                  -- σ = ctxStates K; the put-resume context mirrors the put-updated store (D3 preserved).
                  refine ⟨?_, fun n r hr => ?_⟩
                  · unfold CtxCorr; exact (ctxStates_updateCtxStates_put (w := v2) hg).symm
                  · refine ⟨n+1, ?_⟩
                    simp only [Bang.Config.run, Source.step, dispatch_state_put (w := v2) hg]
                    exact hr
                · simp only [if_neg hop, if_neg hop2, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨ht, _⟩ := h; exact absurd ht (by simp)
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                    -- handle (state ℓ0 s0): install handleF (state ℓ0 s0), run M, POP on return.
                    have hCins : CtxCorr (σ.push ℓ0 s0) (Frame.handleF (.state ℓ0 s0) :: K) :=
                      CtxCorr_install hCtx
                    obtain ⟨hCM, kM⟩ := ihT M (σ.push ℓ0 s0) (.ret v) σ1 hM
                      (Frame.handleF (.state ℓ0 s0) :: K) hCins
                    obtain ⟨hCpop, hupd⟩ := CtxCorr_updateCtx_pop_state hCM
                    refine ⟨hCpop, fun n r hr => ?_⟩
                    -- the body ends at `handleF (state ℓ0 _) :: updateCtxStates K σ1.tail`; the
                    -- handler-return REDUCE pops it, landing at `updateCtxStates K σ1.tail` = `hr`.
                    have hstep : Bang.Config.run (n+1)
                        (updateCtxStates (Frame.handleF (.state ℓ0 s0) :: K) σ1, .ret v) = r := by
                      rw [hupd]; simp only [Bang.Config.run, Source.step]; exact hr
                    obtain ⟨F1, hF1⟩ := kM (n+1) r hstep
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                    have hCins : CtxCorr σ (Frame.handleF (.throws ℓ0) :: K) :=
                      CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                    obtain ⟨hCM, kM⟩ := ihT M σ (.ret v) σ1 hM (Frame.handleF (.throws ℓ0) :: K) hCins
                    have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                      CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                    refine ⟨hCM', fun n r hr => ?_⟩
                    have hstep : Bang.Config.run (n+1)
                        (Frame.handleF (.throws ℓ0) :: updateCtxStates K σ1, .ret v) = r := by
                      simp only [Bang.Config.run, Source.step]; exact hr
                    rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hstep
                    obtain ⟨F1, hF1⟩ := kM (n+1) r hstep
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp only [if_pos hk, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                      obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                      obtain ⟨rfl, rfl⟩ := hk
                      have hCins : CtxCorr σ (Frame.handleF (.throws ℓ0) :: K) :=
                        CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                      obtain ⟨hCM, kR⟩ := ihR M σ ℓ0 w σ1 hM (Frame.handleF (.throws ℓ0) :: K) hCins
                      have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                        CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                      refine ⟨hCM', fun n r hr => ?_⟩
                      -- the abort lands at (updateCtxStates K σ1, ret w): dispatch over the installed
                      -- throws frame catches and resumes Kₒ = updateCtxStates K σ1.
                      have hd : dispatchRun n
                          (Frame.handleF (.throws ℓ0) :: updateCtxStates K σ1) ℓ0 "raise" w = r := by
                        simp only [dispatchRun, Bang.Config.run, Source.step, Bang.dispatch,
                          Bang.splitAt, Bang.handlesOp, beq_self_eq_true, Bool.and_true, decide_true,
                          if_true, Option.bind_some, Bang.dispatchOn]
                        simpa using hr
                      rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hd
                      obtain ⟨F1, hF1⟩ := kR n r hd
                      exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                    · simp [if_neg hk] at h
          | transaction ℓ0 Θ =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ⟩ := h; subst ht; subst hσ
                    have hCins : CtxCorr σ (Frame.handleF (.transaction ℓ0 Θ) :: K) :=
                      CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                    obtain ⟨hCM, kM⟩ := ihT M σ (.ret v) σ1 hM (Frame.handleF (.transaction ℓ0 Θ) :: K) hCins
                    have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                      CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                    refine ⟨hCM', fun n r hr => ?_⟩
                    have hstep : Bang.Config.run (n+1)
                        (Frame.handleF (.transaction ℓ0 Θ) :: updateCtxStates K σ1, .ret v) = r := by
                      simp only [Bang.Config.run, Source.step]; exact hr
                    rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hstep
                    obtain ⟨F1, hF1⟩ := kM (n+1) r hstep
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
    · -- RAISED PART
      intro M σ ℓ v σ' h K hCtx
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | up ℓ2 op2 v2 =>
          simp only [evalD] at h
          cases hg : σ.get? ℓ2 with
          | none =>
              rw [hg] at h
              simp only [Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
              obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
              -- no state frame for ℓ ⇒ raised; σ unchanged ⇒ updateCtxStates K σ = K.
              rw [updateCtxStates_self hCtx]
              refine ⟨hCtx, fun n r hr => ⟨n+1, hr⟩⟩
          | some sv =>
              rw [hg] at h
              by_cases hop : op2 = "get"
              · simp only [if_pos hop, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
              · by_cases hop2 : op2 = "put"
                · simp only [if_neg hop, if_pos hop2, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                · simp only [if_neg hop, if_neg hop2, Option.some.injEq, Prod.mk.injEq,
                    Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                  -- op ∉ {get,put} on a state label (source-unreachable) ⇒ raised; σ unchanged.
                  rw [updateCtxStates_self hCtx]
                  refine ⟨hCtx, fun n r hr => ⟨n+1, hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst σ1
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                obtain ⟨hCM, kR⟩ := ihR M σ ℓ' w σ' hM (Frame.letF N :: K) hCletF
                refine ⟨CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM, fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by
                  rw [updateCtxStates_cons_nonstate σ' (by intro ℓ s; simp), dispatchRun_letF]; exact hr)
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.ret v0), σ1), h =>
                simp only [Option.bind_some] at h
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                obtain ⟨hCM, kM⟩ := ihT M σ (.ret v0) σ1 hM (Frame.letF N :: K) hCletF
                have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                  CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                obtain ⟨hCf, kR⟩ := ihR (Comp.subst v0 N) σ1 ℓ v σ' h (updateCtxStates K σ1) hCM'
                rw [updateCtxStates_updateCtxStates] at hCf
                refine ⟨hCf, fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by rw [updateCtxStates_updateCtxStates]; exact hr)
                have hstep : Bang.Config.run (F1+1) (Frame.letF N :: updateCtxStates K σ1, .ret v0) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF1
                rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hstep
                obtain ⟨F2, hF2⟩ := kM (F1+1) r hstep
                exact ⟨F2+1, by simp only [Bang.Config.run, Source.step]; exact hF2⟩
            | (.term (.lam a), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term (.unfold a), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hCf, kR⟩ := ihR M σ ℓ v σ' h K hCtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kR n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | app M v0 =>
          simp only [evalD] at h
          cases hM : evalD fe σ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst σ1
                have hCappF : CtxCorr σ (Frame.appF v0 :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                obtain ⟨hCM, kR⟩ := ihR M σ ℓ' w σ' hM (Frame.appF v0 :: K) hCappF
                refine ⟨CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM, fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by
                  rw [updateCtxStates_cons_nonstate σ' (by intro ℓ s; simp), dispatchRun_appF]; exact hr)
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.lam N), σ1), h =>
                simp only [Option.bind_some] at h
                have hCappF : CtxCorr σ (Frame.appF v0 :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                obtain ⟨hCM, kM⟩ := ihT M σ (.lam N) σ1 hM (Frame.appF v0 :: K) hCappF
                have hCM' : CtxCorr σ1 (updateCtxStates K σ1) :=
                  CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM
                obtain ⟨hCf, kR⟩ := ihR (Comp.subst v0 N) σ1 ℓ v σ' h (updateCtxStates K σ1) hCM'
                rw [updateCtxStates_updateCtxStates] at hCf
                refine ⟨hCf, fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by rw [updateCtxStates_updateCtxStates]; exact hr)
                have hstep : Bang.Config.run (F1+1) (Frame.appF v0 :: updateCtxStates K σ1, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF1
                rw [← updateCtxStates_cons_nonstate σ1 (by intro ℓ s; simp)] at hstep
                obtain ⟨F2, hF2⟩ := kM (F1+1) r hstep
                exact ⟨F2+1, by simp only [Bang.Config.run, Source.step]; exact hF2⟩
            | (.term (.ret w), _), h => simp [Option.bind] at h
            | (.term (.letC a b), _), h => simp [Option.bind] at h
            | (.term (.force a), _), h => simp [Option.bind] at h
            | (.term (.app a b), _), h => simp [Option.bind] at h
            | (.term (.up a b d), _), h => simp [Option.bind] at h
            | (.term (.handle a b), _), h => simp [Option.bind] at h
            | (.term (.case a b d), _), h => simp [Option.bind] at h
            | (.term (.split a b), _), h => simp [Option.bind] at h
            | (.term .oom, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    -- evalD forwards `raised ℓ' op' w σ1.tail` (pops the pushed entry) ⇒ `σ' = σ1.tail`.
                    obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst hσ
                    have hCins : CtxCorr (σ.push ℓ0 s0) (Frame.handleF (.state ℓ0 s0) :: K) :=
                      CtxCorr_install hCtx
                    obtain ⟨hCM, kR⟩ := ihR M (σ.push ℓ0 s0) ℓ' w σ1 hM
                      (Frame.handleF (.state ℓ0 s0) :: K) hCins
                    obtain ⟨hCpop, hupd⟩ := CtxCorr_updateCtx_pop_state hCM
                    refine ⟨hCpop, fun n r hr => ?_⟩
                    -- the raise dispatches past the state frame (handlesOp state ℓ0 "raise" = false).
                    have hnc : Bang.handlesOp (Handler.state ℓ0 (σ1.headD (default, default)).2) ℓ' "raise"
                        = false := by simp [Bang.handlesOp]
                    have hd : dispatchRun n (updateCtxStates (Frame.handleF (.state ℓ0 s0) :: K) σ1)
                        ℓ' "raise" w = r := by
                      rw [hupd, dispatchRun_handleF_skip n _ _ ℓ' w hnc]; exact hr
                    obtain ⟨F1, hF1⟩ := kR n r hd
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.ret v0), _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term (.unfold a), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp [if_pos hk] at h   -- caught ⇒ term, but h says raised: absurd
                    · simp only [if_neg hk, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                      obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst σ1
                      have hne : ℓ0 ≠ ℓ' := fun he => hk ⟨he, rfl⟩
                      have hnc : Bang.handlesOp (Handler.throws ℓ0) ℓ' "raise" = false := by
                        simp [Bang.handlesOp, hne]
                      have hCins : CtxCorr σ (Frame.handleF (.throws ℓ0) :: K) :=
                        CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                      obtain ⟨hCM, kR⟩ := ihR M σ ℓ' w σ' hM (Frame.handleF (.throws ℓ0) :: K) hCins
                      refine ⟨CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM, fun n r hr => ?_⟩
                      obtain ⟨F1, hF1⟩ := kR n r (by
                        rw [updateCtxStates_cons_nonstate σ' (by intro ℓ s; simp),
                          dispatchRun_handleF_skip n (Handler.throws ℓ0) _ ℓ' w hnc]; exact hr)
                      exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.ret v0), _), h => simp [Option.bind] at h
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
          | transaction ℓ0 Θ =>
              simp only at h
              cases hM : evalD fe σ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, hσ⟩ := h; subst σ1
                    have hnc : Bang.handlesOp (Handler.transaction ℓ0 Θ) ℓ' "raise" = false := by
                      simp [Bang.handlesOp]
                    have hCins : CtxCorr σ (Frame.handleF (.transaction ℓ0 Θ) :: K) :=
                      CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                    obtain ⟨hCM, kR⟩ := ihR M σ ℓ' w σ' hM
                      (Frame.handleF (.transaction ℓ0 Θ) :: K) hCins
                    refine ⟨CtxCorr_updateCtx_nonstate (by intro ℓ s; simp) hCM, fun n r hr => ?_⟩
                    obtain ⟨F1, hF1⟩ := kR n r (by
                      rw [updateCtxStates_cons_nonstate σ' (by intro ℓ s; simp),
                        dispatchRun_handleF_skip n (Handler.transaction ℓ0 Θ) _ ℓ' w hnc]; exact hr)
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.ret v0), _), h => simp [Option.bind] at h
                | (.term (.lam a), _), h => simp [Option.bind] at h
                | (.term (.letC a b), _), h => simp [Option.bind] at h
                | (.term (.force a), _), h => simp [Option.bind] at h
                | (.term (.app a b), _), h => simp [Option.bind] at h
                | (.term (.up a b d), _), h => simp [Option.bind] at h
                | (.term (.handle a b), _), h => simp [Option.bind] at h
                | (.term (.case a b d), _), h => simp [Option.bind] at h
                | (.term (.split a b), _), h => simp [Option.bind] at h
                | (.term .oom, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _), h => simp [Option.bind] at h
      | case a b d => simp [evalD] at h
      | split a b => simp [evalD] at h
      | unfold a => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h

/-- **The D1-A bridge** (headline): when `evalD` says a closed computation returns
`v`, the kernel's verified `Source.eval` agrees (`.done v`). Ties the calculated
machine to the type-safety reference (invariant #1) — `Source.eval`'s `type_safety`
now backs `evalD`'s `ret`-results. Pure spine; handlers/ADT elim later. -/
theorem evalD_agrees_source (f : Nat) (M : Comp) (v : Val) (σ' : SStore)
    (h : evalD f [] M = some (.term (.ret v), σ')) :
    ∃ F, Source.eval F M = Result.done v := by
  -- the empty store mirrors the empty kernel context (`CtxCorr [] []` by `rfl`); a closed program
  -- has no state frames ⇒ `updateCtxStates [] σ' = []`, so the continuation runs at `([], ret v)`.
  obtain ⟨_, k⟩ := (run_evalD f).1 M [] (.ret v) σ' h [] rfl
  have hbase : Config.run 1 (updateCtxStates [] σ', .ret v) = Result.done v := by
    simp only [updateCtxStates, Config.run]
  obtain ⟨F, hF⟩ := k 1 (Result.done v) hbase
  exact ⟨F, hF⟩

/-- `handle`-install over a non-raising body: `handle (throws ℓ) (ret 7)` ⇒ `ret 7`
(handler-return = identity). Machine `MARK`/`UNMARK` are identity on normal return;
evalD and Source.eval agree. -/
example :
    let M := Comp.handle (.throws default) (.ret (.vint 7))
    evalD 5 [] M = some (.term (.ret (.vint 7)), [])
      ∧ exec 10 (compile M []) [] [] = some [.ret (.vint 7)]
      ∧ Source.eval 5 M = Result.done (.vint 7) := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- Bridge witnessed concretely: `(λ.ret #0) 5` — `evalD` returns `ret 5` AND
`Source.eval` reaches `.done 5`. The two semantics agree. -/
example :
    let M := Comp.app (.lam (.ret (.vvar 0))) (.vint 5)
    evalD 5 [] M = some (.term (.ret (.vint 5)), []) ∧ Source.eval 5 M = Result.done (.vint 5) := by
  refine ⟨by rfl, by rfl⟩

end Bang.CalcVM
