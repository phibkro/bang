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
sub-step 2. The ADT eliminators are calculated too: `case`/`split` defer to runtime
`CASE`/`SPLIT` instructions (their erasure `compile (subst …)` is non-structural, so
they re-`compile` the branch under fuel exactly as `SUBST`/`APP` do), while
`unfold (fold v)` ERASES at compile time onto `RET v` (structural — like
`force (vthunk M) ↦ compile M`; no dedicated instruction, invariant #4).
ADR-0031 (resumptive state) adds the store thread:
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

/-! ## The transaction heap store (ADR-0031 D4): the list-heap analog of `SStore`

`THeap` is the resumptive mechanism `evalD` threads for **transaction** frames — `SStore`
generalized from a single `Val` cell to a list-heap `List Val` (the TVar store, ADR-0030).
It mirrors the machine's active `transaction ℓ Θ` frames 1:1, in order, exactly as `SStore`
mirrors `state ℓ s` frames.

**INVARIANT (op-disjointness — the load-bearing correctness argument).** This is a SEPARATE
parallel store from `SStore`, NOT a unified `List (Label × Cell)`, because state ops
`{get,put}` are op-disjoint from transaction ops `{newTVar,readTVar,writeTVar}` (`handlesOp`,
`Operational.lean`). `splitAt` finds the nearest frame *catching `(ℓ,op)`*, gated on op-id —
so a label shared across both a `state` and a `transaction` frame still resolves
UNAMBIGUOUSLY by op-id, and within-kind shadowing (nearest state frame for `get`; nearest
txn frame for `readTVar`) is all that each per-projection order must preserve. The two
projections never cross. A unified store would add structure to enforce an invariant that is
ALREADY structural via op-disjointness — the inverse of correctness-by-construction.

**INVARIANT (soundness boundary).** This parallel rep is sound ONLY while the state and
transaction op-sets stay disjoint. Adding an op handled by BOTH kinds would reintroduce
cross-kind ambiguity (a label could resolve to either projection) — re-examine the rep
(unify into one ordered store) BEFORE doing so. -/
abbrev THeap := List (Bang.EffectRow.Label × List Bang.Val)

/-- The nearest stored heap for label `ℓ` (innermost transaction frame wins — shadowing). -/
def THeap.get? (τ : THeap) (ℓ : Bang.EffectRow.Label) : Option (List Bang.Val) :=
  (τ.find? (fun p => p.1 = ℓ)).map (·.2)

/-- UPDATE the nearest binding for `ℓ` **in place** to heap `Θ` (mirrors `SStore.put`; the txn
machine's in-place heap update). Unbound ⇒ unchanged (source-unreachable: ops fire only under a
live frame). -/
def THeap.put : THeap → Bang.EffectRow.Label → List Bang.Val → THeap
  | [],            _, _ => []
  | (ℓ0, w) :: τ, ℓ, Θ => if ℓ0 = ℓ then (ℓ0, Θ) :: τ else (ℓ0, w) :: THeap.put τ ℓ Θ

/-- PUSH a fresh transaction binding (a `handle (transaction ℓ Θ)` install). -/
def THeap.push (τ : THeap) (ℓ : Bang.EffectRow.Label) (Θ : List Bang.Val) : THeap := (ℓ, Θ) :: τ

/-- Service a transaction op against heap `Θ`, returning `(resultValue, Θ')` — the PURE
heap-threading core shared by `evalD` and the machine (mirrors `dispatchOn`'s transaction arm,
`Operational.lean`). `newTVar v`: append `v`, return its index. `readTVar (vint i)`: return cell
`i` (TOTAL — default `vint 0`), heap unchanged. `writeTVar (pair (vint i) w)`: set cell `i`,
return unit. A malformed payload is a type-safe no-op resume. -/
def txnService (op : Bang.OpId) (v : Val) (Θ : List Bang.Val) : Bang.Val × List Bang.Val :=
  if op = "newTVar" then (.vint Θ.length, Θ ++ [v])
  else if op = "readTVar" then (Θ.getD ((Bang.tvarIdx v).getD 0) (.vint 0), Θ)
  else
    match v with
    | .pair iv w => (.vunit, Bang.storeSet Θ ((Bang.tvarIdx iv).getD 0) w)
    | _          => (.vunit, Θ)

/-- Is `op` one of the three transaction ops? (the txn-cell op-guard, mirrors `stateUpdate`'s
get/put guard). A non-txn op on a transaction label ⇒ `none` ⇒ falls through to the throws path. -/
def isTxnOp (op : Bang.OpId) : Bool := op = "newTVar" || op = "readTVar" || op = "writeTVar"

/-- `isTxnOp` unfolds to membership in the three-op set. -/
theorem isTxnOp_iff {op : Bang.OpId} :
    isTxnOp op = true ↔ op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := by
  simp only [isTxnOp, Bool.or_eq_true, decide_eq_true_eq, or_assoc]

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

def evalD : Nat → SStore → THeap → Comp → Option (Outcome × SStore × THeap)
  | 0,          _, _, _            => none
  | Nat.succ _, σ, τ, .ret v       => some (.term (.ret v), σ, τ)
  | Nat.succ _, σ, τ, .lam M       => some (.term (.lam M), σ, τ)
  | Nat.succ f, σ, τ, .letC M N    =>
      (evalD f σ τ M).bind (fun p => match p with
        | (.term (.ret v), σ', τ') => evalD f σ' τ' (Comp.subst v N) -- M : F _ ⇒ terminal is `ret v`
        | (.term _, _, _)          => none                            -- ill-typed (letC of a lam)
        | (.raised ℓ op w, σ', τ') => some (.raised ℓ op w, σ', τ'))  -- propagate the raise outward
  | Nat.succ f, σ, τ, .force (.vthunk M) => evalD f σ τ M           -- force∘thunk = run the closed body
  | Nat.succ f, σ, τ, .app M v     =>
      (evalD f σ τ M).bind (fun p => match p with
        | (.term (.lam N), σ', τ') => evalD f σ' τ' (Comp.subst v N) -- β: M ⇒ lam N, then N[v]
        | (.term _, _, _)          => none                            -- ill-typed (app of a non-lam)
        | (.raised ℓ op w, σ', τ') => some (.raised ℓ op w, σ', τ'))  -- propagate the raise outward
  -- up ℓ op v: dispatch is OP-FIRST (mirroring the kernel's `handlesOp`, `Operational.lean`): a state
  -- `get`/`put` resolves to the nearest `state ℓ` frame in σ; a transaction `newTVar`/`readTVar`/
  -- `writeTVar` resolves to the nearest `transaction ℓ` frame in τ. The op-id alone selects the
  -- projection (state and txn op-sets are DISJOINT), so a label shared by both kinds resolves
  -- unambiguously — and the machine's `stateUpdate` (op-guarded {get,put}) / `txnUpdate` (op-guarded
  -- isTxnOp) stay in lockstep. Any other op, or a state/txn op with no active frame, raises (throws).
  | Nat.succ _, σ, τ, .perform _ ℓ op v   =>
      if op = "get" then
        match σ.get? ℓ with
        | some s => some (.term (.ret s), σ, τ)                      -- get: return stored s, σ unchanged
        | none   => some (.raised ℓ op v, σ, τ)                      -- no state frame ⇒ throws path
      else if op = "put" then
        match σ.get? ℓ with
        | some _ => some (.term (.ret .vunit), σ.put ℓ v, τ)         -- put: thread s := v
        | none   => some (.raised ℓ op v, σ, τ)
      else if isTxnOp op then
        match τ.get? ℓ with
        | some Θ =>
            -- serviced against the heap: thread Θ := Θ' in place (mirrors the machine's txnUpdate).
            let (r, Θ') := txnService op v Θ
            some (.term (.ret r), σ, τ.put ℓ Θ')
        | none => some (.raised ℓ op v, σ, τ)                        -- no txn frame ⇒ throws path
      else some (.raised ℓ op v, σ, τ)                               -- neither a state nor a txn op
  -- handle h M: dispatch on the handler kind.
  --  · state ℓ s : push (ℓ ↦ s) for M's extent; on a normal `ret v` RESTORE the outer σ
  --    (lexical shadowing — D1); the handler-return is identity (Q6). A raise still forwards.
  --  · transaction ℓ Θ : the list-heap analog (ADR-0031 D4). Push (ℓ ↦ Θ) on τ for M's extent; POP on
  --    exit. Rollback is FREE: an abort is a foreign `throws` over a DIFFERENT label that escapes this
  --    frame, so the threaded heap is discarded with the popped τ entry and never commits.
  --  · throws ℓ0 : CATCH a `raised (ℓ0, "raise")` ⇒ yield the payload `term (ret w)` (zero-shot
  --    abort, ADR-0023); else forward. Resumptive ops never reach here as `raised` (serviced inline).
  | Nat.succ f, σ, τ, .handle h M  =>
      match h with
      | .state ℓ s =>
          (evalD f (σ.push ℓ s) τ M).bind (fun p => match p with
            | (.term (.ret v), σ', τ') => some (.term (.ret v), σ'.tail, τ')  -- POP the pushed ℓ entry
            | (.term _, _, _)          => none
            | (.raised ℓ' op' w, σ', τ') => some (.raised ℓ' op' w, σ'.tail, τ')) -- forward; pop entry
      | .transaction ℓ Θ =>
          (evalD f σ (τ.push ℓ Θ) M).bind (fun p => match p with
            | (.term (.ret v), σ', τ') => some (.term (.ret v), σ', τ'.tail)  -- POP the pushed ℓ heap
            | (.term _, _, _)          => none
            | (.raised ℓ' op' w, σ', τ') => some (.raised ℓ' op' w, σ', τ'.tail)) -- forward; pop heap
      | .throws ℓ0 =>
          (evalD f σ τ M).bind (fun p => match p with
            | (.term (.ret v), σ', τ') => some (.term (.ret v), σ', τ')
            | (.term _, _, _)          => none
            | (.raised ℓ' op' w, σ', τ') =>
                -- CAUGHT (zero-shot abort): discard the captured CONTINUATION (control unwinds to this
                -- handler), but KEEP the at-raise stores `σ'`/`τ'`. The abort unwinds only `Kᵢ` (the
                -- control between this throws handler and the raise point); the OUTER `state`/`transaction`
                -- frames live in `Kₒ` and are NOT rewound (kernel `dispatchOn` THROW = `(Kₒ, ret v)` —
                -- `Operational.lean`). So an outer `put`/`writeTVar` performed before a caught raise
                -- PERSISTS. Inner `state`/`transaction` handles nested under this throws handler have
                -- already popped their pushed entry on the way out (`handle` forwards a raise via the
                -- tail), so `σ'`/`τ'` retain exactly the outer effects.
                if ℓ0 = ℓ' ∧ op' = "raise" then some (.term (.ret w), σ', τ')
                else some (.raised ℓ' op' w, σ', τ'))
  -- ADT eliminators (Unit 6): PURE reductions — closed-value scrutinee, NO σ/τ threading change, NO
  -- handler/raise interaction. Mirror the kernel's `Source.step` (`Operational.lean` 259-263) exactly:
  -- `case`/`split` re-`subst` into a branch (recursing on fuel), `unfold` erases to `ret v`. The
  -- `none` fall-through keeps the catch-all for ill-formed scrutinees (source-unreachable, well-typed).
  | Nat.succ f, σ, τ, .case (.inl v) N₁ _  => evalD f σ τ (Comp.subst v N₁)
  | Nat.succ f, σ, τ, .case (.inr v) _  N₂ => evalD f σ τ (Comp.subst v N₂)
  | Nat.succ f, σ, τ, .split (.pair v w) N => evalD f σ τ (Comp.subst v (Comp.subst (Val.shift w) N))
  | Nat.succ _, σ, τ, .unfold (.fold v)    => some (.term (.ret v), σ, τ)
  | _,          _, _, _            => none                -- out of scope (ill-formed scrutinee)

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
  -- ADT eliminators (Unit 6): same residual-`Comp`-in-instruction pattern as `SUBST`/`APP`. `compile`
  -- emits the instruction WITHOUT recursing into the branches (keeping `compile` structural); `exec`
  -- inspects the closed-value scrutinee and re-`compile`s the chosen branch at runtime (fuel-bounded).
  | CASE   : Val → Comp → Comp → Instr  -- sum elim: inl/inr ⇒ compile+run the matching branch[v]
  | SPLIT  : Val → Comp → Instr         -- product elim: pair ⇒ compile+run N[v][shift w] (DOUBLE subst)
  -- (no UNFOLD: `unfold (fold v)` erases to `RET v` at compile time — see `compile`.)
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
  | .perform _ ℓ op v,  c => Instr.OP ℓ op v :: c      -- RESUMPTIVE: `c` IS Kᵢ, KEPT (D2); 1a: cap ignored, OP stays label-dispatched; throws falls through to unwind
  -- case/split: erasure (`compile (case (inl v) N₁ N₂) c = compile (subst v N₁) c`) is what the
  -- calculation forces, but it is NON-structural (`subst v N₁` is not a subterm) — so, EXACTLY as
  -- `SUBST`/`APP` resolve the same non-structural `compile (subst …)`, defer it to a runtime instruction
  -- that re-`compile`s the chosen branch under fuel. The scrutinee `w` may be open (`vvar n`) in a branch
  -- body, so `compile` cannot peek-and-reduce here the way `force (vthunk M)` can.
  | .case w N₁ N₂,      c => Instr.CASE w N₁ N₂ :: c
  | .split w N,         c => Instr.SPLIT w N :: c
  -- unfold: ERASES at compile time, exactly like `force (vthunk M) ↦ compile M c`. `unfold (fold v) ↦
  -- ret v` is STRUCTURAL (`v` is in hand, `RET v :: c` does not recurse non-structurally), so the
  -- calculation collapses it onto the existing `RET` — NO dedicated instruction (invariant #4: the
  -- machine is the calculation's output; an `UNFOLD` instr would be hand-added redundancy).
  | .unfold (.fold v), c => Instr.RET v :: c
  | _,                  c => c               -- out of scope: emit nothing (residual; open/ill-formed)

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

/-- Find the nearest **transaction** frame for `ℓ` and service `newTVar`/`readTVar`/`writeTVar` IN
PLACE (ADR-0031 D4, the list-heap analog of `stateUpdate`). Returns `(resultValue, hs')` where `hs'`
has that frame's heap updated to `txnService`'s threaded `Θ'`; the frames ABOVE it (Kᵢ's handlers)
are KEPT (deep handler). `none` = no `transaction ℓ` frame OR a non-txn op on a txn label ⇒ the caller
falls through to `unwindFind` (throws path). Mirrors `dispatchOn`'s transaction arm. -/
def txnUpdate : Bang.EffectRow.Label → Bang.OpId → Val → HStack → Option (Val × HStack)
  | _, _, _, []       => none
  | ℓ, op, v, fr :: hs =>
      match fr.handler with
      | .transaction ℓ0 Θ =>
          if ℓ0 = ℓ then
            if isTxnOp op then
              let (r, Θ') := txnService op v Θ
              some (r, { fr with handler := .transaction ℓ0 Θ' } :: hs)            -- service: store Θ' in place
            else none                                                             -- non-txn op on ℓ ⇒ throws path
          else (txnUpdate ℓ op v hs).map (fun p => (p.1, fr :: p.2))              -- different label ⇒ keep, recurse
      | _ => (txnUpdate ℓ op v hs).map (fun p => (p.1, fr :: p.2))                -- non-txn frame ⇒ keep, recurse

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

/-! ### Transaction ↔ HStack correspondence (ADR-0031 D4): the list-heap analog of the state bridge

`hsTxn`/`hsTxns`/`updateTxns`/`TCorr` are the EXACT mirror of `hsState`/`hsStates`/`updateStates`/
`Corr`, projecting `transaction ℓ Θ` frames into a `THeap` instead of `state ℓ s` frames into an
`SStore`. They are a SEPARATE projection from the state one (op-disjointness — see `THeap`): the
state projection skips txn frames, the txn projection skips state frames, and no op crosses. -/

/-- The nearest `transaction ℓ` frame's stored heap in `hs` (machine-side `THeap.get?`). -/
def hsTxn : HStack → Bang.EffectRow.Label → Option (List Val)
  | [],       _ => none
  | fr :: hs, ℓ =>
      match fr.handler with
      | .transaction ℓ0 Θ => if ℓ0 = ℓ then some Θ else hsTxn hs ℓ
      | _                 => hsTxn hs ℓ

/-- Project the HStack to the txn-heap store it mirrors: the `transaction ℓ Θ` frames, in order
(state/throws frames carry no heap ⇒ skipped). `TCorr` says `evalD`'s threaded τ IS this projection. -/
def hsTxns : HStack → THeap
  | []        => []
  | fr :: hs  =>
      match fr.handler with
      | .transaction ℓ0 Θ => (ℓ0, Θ) :: hsTxns hs
      | _                 => hsTxns hs

/-- The bridge invariant (D4), STRUCTURAL form: `evalD`'s threaded τ IS the projection of the
machine's active transaction frames. The list-heap analog of `Corr`. -/
def TCorr (τ : THeap) (hs : HStack) : Prop := τ = hsTxns hs

/-- Overwrite each `transaction` frame's stored heap in `hs` with the head of `τ` (consumed in
order). `M`'s net HStack effect on txn frames, as a PURE function of `hs`/post-τ. The analog of
`updateStates`; non-txn frames pass through. -/
def updateTxns : HStack → THeap → HStack
  | [],       _ => []
  | fr :: hs, τ =>
      match fr.handler with
      | .transaction ℓ0 _ =>
          match τ with
          | (_, Θ) :: τ' => { fr with handler := .transaction ℓ0 Θ } :: updateTxns hs τ'
          | []           => fr :: updateTxns hs []     -- τ exhausted (unreachable under TCorr)
      | _ => fr :: updateTxns hs τ

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

/-- Two frames agree up to a `state` handler's stored value OR a `transaction` handler's stored
heap. The transaction clause permits `Θ` to differ (ADR-0031 D4) exactly as the state clause
permits the value to differ — a returning body may have mutated the heap via `writeTVar`. -/
def FrameMut (a b : HFrame) : Prop :=
  a.savedCode = b.savedCode ∧ a.savedStack = b.savedStack ∧
    (match a.handler, b.handler with
     | .state ℓ1 _, .state ℓ2 _ => ℓ1 = ℓ2
     | .throws ℓ1, .throws ℓ2 => ℓ1 = ℓ2
     | .transaction ℓ1 _, .transaction ℓ2 _ => ℓ1 = ℓ2
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

/-- `updateTxns` SKIPS a `state`-frame head (copies it through): the two passes are independent. -/
theorem updateTxns_cons_state {fr : HFrame} {hs : HStack} (τ : THeap) {ℓ : Bang.EffectRow.Label}
    {s : Val} (hh : fr.handler = .state ℓ s) :
    updateTxns (fr :: hs) τ = fr :: updateTxns hs τ := by
  simp only [updateTxns, hh]

/-- `updateTxns` SKIPS a `throws`-frame head. -/
theorem updateTxns_cons_throws {fr : HFrame} {hs : HStack} (τ : THeap) {ℓ : Bang.EffectRow.Label}
    (hh : fr.handler = .throws ℓ) : updateTxns (fr :: hs) τ = fr :: updateTxns hs τ := by
  simp only [updateTxns, hh]

/-- `updateStates` SKIPS a `transaction`-frame head (copies it through). -/
theorem updateStates_cons_txn {fr : HFrame} {hs : HStack} (σ : SStore) {ℓ : Bang.EffectRow.Label}
    {Θ : List Val} (hh : fr.handler = .transaction ℓ Θ) :
    updateStates (fr :: hs) σ = fr :: updateStates hs σ := by
  simp only [updateStates, hh]

/-- The reconstruction lemma: a machine HStack `k` that is `HMut`-related to `hs` AND whose
state-projection is `σ'` AND whose txn-projection is `τ'` is **exactly** `updateTxns (updateStates
hs σ') τ'`. So the post-`M` HStack — which the term-part proves satisfies all three — is the pure
net-effect function `updateTxns (updateStates hs σ') τ'` (frame-independent). The two passes are
independent (state and txn frames are disjoint), so they compose cleanly. -/
theorem updateStates_eq : ∀ {hs k : HStack} {σ' : SStore} {τ' : THeap},
    HMut hs k → Corr σ' k → TCorr τ' k → k = updateTxns (updateStates hs σ') τ' := by
  intro hs
  induction hs with
  | nil =>
      intro k σ' τ' hmut _ _
      cases k with
      | nil => rfl
      | cons => simp [HMut] at hmut
  | cons fr hs ih =>
      intro k σ' τ' hmut hC hT
      cases k with
      | nil => simp [HMut] at hmut
      | cons fk k =>
        obtain ⟨hfm, hmut'⟩ := hmut
        obtain ⟨hscode, hsstack, hsh⟩ := hfm
        unfold Corr at hC; unfold TCorr at hT
        cases hfr : fr.handler with
        | state ℓ0 s0 =>
            cases hfk : fk.handler with
            | state ℓ1 s1 =>
                rw [hfr, hfk] at hsh; simp only at hsh; subst hsh
                rw [hsStates, hfk] at hC
                rw [hsTxns, hfk] at hT
                -- σ' covers `(ℓ0,s1) :: hsStates k`; updateStates overwrites fr's value to s1, then
                -- updateTxns SKIPS the resulting state frame. The tail closes by IH.
                obtain ⟨p, σ'', rfl⟩ : ∃ p σ'', σ' = p :: σ'' := by
                  rw [hC]; exact ⟨_, _, rfl⟩
                simp only [List.cons.injEq] at hC; obtain ⟨hp, hCtl⟩ := hC; subst hp
                simp only [hsTxns, hfk] at hT
                simp only [updateStates, hfr, updateTxns]
                rw [← ih hmut' (hCtl ▸ rfl : Corr σ'' k) (hT : TCorr τ' k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
        | throws ℓ0 =>
            cases hfk : fk.handler with
            | throws ℓ1 =>
                simp only [hsStates, hfk] at hC
                simp only [hsTxns, hfk] at hT
                simp only [updateStates, hfr, updateTxns]
                rw [← ih hmut' (hC : Corr σ' k) (hT : TCorr τ' k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
        | transaction ℓ0 Θ0 =>
            cases hfk : fk.handler with
            | transaction ℓ1 Θ1 =>
                rw [hfr, hfk] at hsh; simp only at hsh; subst hsh
                simp only [hsStates, hfk] at hC
                rw [hsTxns, hfk] at hT
                -- τ' covers `(ℓ0,Θ1) :: hsTxns k`; updateStates SKIPS the txn frame (copies fr), then
                -- updateTxns overwrites fr's heap to Θ1. The tail closes by IH.
                obtain ⟨p, τ'', rfl⟩ : ∃ p τ'', τ' = p :: τ'' := by
                  rw [hT]; exact ⟨_, _, rfl⟩
                simp only [List.cons.injEq] at hT; obtain ⟨hp, hTtl⟩ := hT; subst hp
                simp only [updateStates, hfr, updateTxns]
                rw [← ih hmut' (hC : Corr σ' k) (hTtl ▸ rfl : TCorr τ'' k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)

/-- The combined net-HStack-effect: overwrite state values from `σ`, then txn heaps from `τ`. The
post-`M` HStack as a PURE function of the at-handle `hs` and the post-`M` stores (ADR-0031 D4). -/
def netEffect (hs : HStack) (σ : SStore) (τ : THeap) : HStack := updateTxns (updateStates hs σ) τ

/-- `netEffect` with stores a HStack already mirrors (`Corr σ hs ∧ TCorr τ hs`) is the identity —
overwriting each value/heap with the one it already has. (`updateStates_eq` at `k = hs`, `HMut.refl`.) -/
theorem updateStates_self {σ : SStore} {τ : THeap} {hs : HStack} (hC : Corr σ hs) (hT : TCorr τ hs) :
    netEffect hs σ τ = hs := (updateStates_eq (HMut.refl hs) hC hT).symm


/-- `netEffect k σ τ` is `HMut`-related to `k`: net-update mutates state values / txn heaps in place,
preserving frame structure. -/
theorem HMut_netEffect : ∀ (hs : HStack) (σ : SStore) (τ : THeap), HMut hs (netEffect hs σ τ) := by
  intro hs
  induction hs with
  | nil => intro σ τ; exact HMut.refl []
  | cons fr hs ih =>
    intro σ τ
    cases hfr : fr.handler with
    | state ℓ0 s0 =>
        cases σ with
        | nil =>
            show HMut (fr :: hs) (updateTxns (updateStates (fr :: hs) []) τ)
            rw [show updateStates (fr :: hs) [] = fr :: updateStates hs [] from by simp only [updateStates, hfr]]
            rw [updateTxns_cons_state τ hfr]
            exact ⟨⟨rfl, rfl, by simp [hfr]⟩, ih [] τ⟩
        | cons p σ' =>
            obtain ⟨ℓq, wq⟩ := p
            show HMut (fr :: hs) (updateTxns (updateStates (fr :: hs) ((ℓq, wq) :: σ')) τ)
            rw [show updateStates (fr :: hs) ((ℓq, wq) :: σ') = { fr with handler := .state ℓ0 wq } :: updateStates hs σ' from by simp only [updateStates, hfr]]
            rw [updateTxns_cons_state τ (show ({ fr with handler := .state ℓ0 wq } : HFrame).handler = .state ℓ0 wq from rfl)]
            exact ⟨⟨rfl, rfl, by simp [hfr]⟩, ih σ' τ⟩
    | throws ℓ0 =>
        simp only [netEffect, updateStates, hfr, updateTxns_cons_throws τ hfr]
        exact ⟨⟨rfl, rfl, by simp [hfr]⟩, ih σ τ⟩
    | transaction ℓ0 Θ0 =>
        cases τ with
        | nil =>
            simp only [netEffect, updateStates_cons_txn σ hfr, updateTxns, hfr]
            exact ⟨⟨rfl, rfl, by simp [hfr]⟩, ih σ []⟩
        | cons p τ' =>
            obtain ⟨ℓq, Θq⟩ := p
            simp only [netEffect, updateStates_cons_txn σ hfr, updateTxns, hfr]
            exact ⟨⟨rfl, rfl, by simp [hfr]⟩, ih σ τ'⟩

/-- `netEffect` depends only on a HStack's FRAME STRUCTURE, not its stored values/heaps: `HMut`-
related stacks net-update identically. The re-base that lets a `letC`/`app` raised chain restate the
at-raise HStack on the ORIGINAL `hs`. Because `netEffect` overwrites BOTH state values and txn heaps,
the relaxed-HMut txn frames (differing `Θ`) are erased to the common store head — so this holds where
the state-only `updateStates` version would not. Reduced to `updateStates_eq` (the unique HStack
pinned by `HMut hs ·`, `Corr σ ·`, `TCorr τ ·`). -/
theorem netEffect_congr_HMut {hs k : HStack} (σ : SStore) (τ : THeap)
    (hmut : HMut hs k) (hcovS : Corr σ (netEffect k σ τ)) (hcovT : TCorr τ (netEffect k σ τ)) :
    netEffect k σ τ = netEffect hs σ τ := by
  have hmutNet : HMut hs (netEffect k σ τ) := HMut.trans hmut (HMut_netEffect k σ τ)
  show netEffect k σ τ = updateTxns (updateStates hs σ) τ
  exact updateStates_eq hmutNet hcovS hcovT

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

/-- `netEffect` distributes over a `throws`-frame head (it carries neither a state value nor a heap,
so both passes skip it). Used to push the at-raise tail through the throws install in `sim`. -/
theorem netEffect_cons_throws {fr : HFrame} {hs : HStack} {σ : SStore} {τ : THeap}
    {ℓ0 : Bang.EffectRow.Label} (hfr : fr.handler = .throws ℓ0) :
    netEffect (fr :: hs) σ τ = fr :: netEffect hs σ τ := by
  unfold netEffect
  rw [updateStates_cons_nonstate σ (by rw [hfr]; intro ℓ s; simp)]
  exact updateTxns_cons_throws τ hfr

/-- The raised-part at-raise correspondence pops a NON-state, NON-txn (throws) install frame from the
COMBINED net-effect triple: a throws frame carries neither store entry, so `Corr`/`TCorr`/`HMut` over
`netEffect (fr::hs) σ' τ'` pass to the tail. The `sim` raised handle(throws) escape case (triple form). -/
theorem raisedTriple_pop_nontxn {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap}
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) (hnt : ∀ ℓ Θ, fr.handler ≠ .transaction ℓ Θ)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ')) :
    Corr σ' (netEffect hs σ' τ') ∧ TCorr τ' (netEffect hs σ' τ') ∧ HMut hs (netEffect hs σ' τ') := by
  have hupd : netEffect (fr :: hs) σ' τ' = fr :: netEffect hs σ' τ' := by
    unfold netEffect
    rw [updateStates_cons_nonstate σ' hns]
    cases hh : fr.handler with
    | state ℓ s => exact absurd hh (hns ℓ s)
    | transaction ℓ Θ => exact absurd hh (hnt ℓ Θ)
    | throws ℓ => exact updateTxns_cons_throws τ' hh
  rw [hupd] at hCr hTr hmutr
  refine ⟨?_, ?_, HMut.tail hmutr⟩
  · unfold Corr at hCr ⊢
    have hproj : hsStates (fr :: netEffect hs σ' τ') = hsStates (netEffect hs σ' τ') := by
      cases hh : fr.handler with
      | state ℓ s => exact absurd hh (hns ℓ s)
      | throws ℓ => simp only [hsStates, hh]
      | transaction ℓ Θ => exact absurd hh (hnt ℓ Θ)
    rw [hproj] at hCr; exact hCr
  · unfold TCorr at hTr ⊢
    have hproj : hsTxns (fr :: netEffect hs σ' τ') = hsTxns (netEffect hs σ' τ') := by
      cases hh : fr.handler with
      | transaction ℓ Θ => exact absurd hh (hnt ℓ Θ)
      | state ℓ s => simp only [hsTxns, hh]
      | throws ℓ => simp only [hsTxns, hh]
    rw [hproj] at hTr; exact hTr

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

/-- The COMBINED (triple) raised-pop for a `state` install frame: pops `σ'.tail` (state side), `τ'`
unchanged (a state frame carries no heap). The `sim` raised handle(state) escape case (triple form). -/
theorem raisedTriple_pop_state {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap}
    {ℓ0 : Bang.EffectRow.Label} {s0 : Val} (hfr : fr.handler = .state ℓ0 s0)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ')) :
    Corr σ'.tail (netEffect hs σ'.tail τ') ∧ TCorr τ' (netEffect hs σ'.tail τ')
      ∧ HMut hs (netEffect hs σ'.tail τ') := by
  cases σ' with
  | nil =>
      exfalso; unfold Corr netEffect at hCr
      rw [updateStates] at hCr; simp only [hfr] at hCr
      rw [updateTxns_cons_state τ' hfr] at hCr
      rw [hsStates] at hCr; simp only [hfr] at hCr
      exact (List.cons_ne_nil _ _ hCr.symm)
  | cons p σ1' =>
      obtain ⟨ℓa, wa⟩ := p
      have hupd : netEffect (fr :: hs) ((ℓa, wa) :: σ1') τ' =
          { fr with handler := .state ℓ0 wa } :: netEffect hs σ1' τ' := by
        unfold netEffect; rw [updateStates]; simp only [hfr]
        rw [updateTxns_cons_state τ' (show ({ fr with handler := .state ℓ0 wa } : HFrame).handler = .state ℓ0 wa from rfl)]
      rw [hupd] at hCr hTr hmutr
      simp only [List.tail]
      refine ⟨?_, ?_, HMut.tail hmutr⟩
      · unfold Corr at hCr ⊢; simp only [hsStates] at hCr
        exact (List.cons.injEq _ _ _ _).mp hCr |>.2
      · unfold TCorr at hTr ⊢; simpa only [hsTxns] using hTr

/-- The COMBINED (triple) raised-pop for a `transaction` install frame: pops `τ'.tail` (txn side),
`σ'` unchanged (a txn frame carries no state). The `sim` raised handle(transaction) escape case. -/
theorem raisedTriple_pop_txn {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap}
    {ℓ0 : Bang.EffectRow.Label} {Θ0 : List Val} (hfr : fr.handler = .transaction ℓ0 Θ0)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ')) :
    Corr σ' (netEffect hs σ' τ'.tail) ∧ TCorr τ'.tail (netEffect hs σ' τ'.tail)
      ∧ HMut hs (netEffect hs σ' τ'.tail) := by
  cases τ' with
  | nil =>
      exfalso; unfold TCorr netEffect at hTr
      rw [updateStates_cons_txn σ' hfr] at hTr
      rw [updateTxns] at hTr; simp only [hfr] at hTr
      rw [hsTxns] at hTr; simp only [hfr] at hTr
      exact (List.cons_ne_nil _ _ hTr.symm)
  | cons p τ1' =>
      obtain ⟨ℓa, Θa⟩ := p
      have hupd : netEffect (fr :: hs) σ' ((ℓa, Θa) :: τ1') =
          { fr with handler := .transaction ℓ0 Θa } :: netEffect hs σ' τ1' := by
        unfold netEffect; rw [updateStates_cons_txn σ' hfr, updateTxns]; simp only [hfr]
      rw [hupd] at hCr hTr hmutr
      simp only [List.tail]
      refine ⟨?_, ?_, HMut.tail hmutr⟩
      · unfold Corr at hCr ⊢; simpa only [hsStates] using hCr
      · unfold TCorr at hTr ⊢; simp only [hsTxns] at hTr
        exact (List.cons.injEq _ _ _ _).mp hTr |>.2

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

/-! ### Transaction-side service/correspondence lemmas (ADR-0031 D4 mirror of the state lemmas) -/

/-- `get?` of the txn projection reads the nearest transaction frame (ties `hsTxns` to `hsTxn`). -/
theorem get?_hsTxns : ∀ (hs : HStack) (ℓ : Bang.EffectRow.Label),
    (hsTxns hs).get? ℓ = hsTxn hs ℓ := by
  intro hs
  induction hs with
  | nil => intro ℓ; rfl
  | cons fr hs ih =>
    intro ℓ
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        simp only [hsTxns, hsTxn, hh]
        by_cases hc : ℓ0 = ℓ
        · subst hc; simp [THeap.get?, List.find?]
        · simp only [if_neg hc, THeap.get?, List.find?, hc, decide_false, Bool.false_eq_true,
            if_false]; exact ih ℓ
    | state ℓ0 s => simp only [hsTxns, hsTxn, hh]; exact ih ℓ
    | throws ℓ0 => simp only [hsTxns, hsTxn, hh]; exact ih ℓ

/-- Under `TCorr`, the heap read equals the machine read. -/
theorem TCorr.get? {τ : THeap} {hs : HStack} (hT : TCorr τ hs) (ℓ : Bang.EffectRow.Label) :
    τ.get? ℓ = hsTxn hs ℓ := by rw [hT]; exact get?_hsTxns hs ℓ

/-- `THeap.put` hits at its own label when bound. Induction on τ. -/
theorem THeap.get?_put_self : ∀ (τ : THeap) (ℓ : Bang.EffectRow.Label) (Θ : List Val) (Θ0 : List Val),
    τ.get? ℓ = some Θ0 → (τ.put ℓ Θ).get? ℓ = some Θ := by
  intro τ
  induction τ with
  | nil => intro ℓ Θ Θ0 hg; simp [THeap.get?, List.find?] at hg
  | cons p τ ih =>
    obtain ⟨ℓ0, w⟩ := p
    intro ℓ Θ Θ0 hg
    by_cases hc : ℓ0 = ℓ
    · subst hc; simp [THeap.put, THeap.get?, List.find?]
    · have hne : ¬ (ℓ0 = ℓ) := hc
      simp only [THeap.get?, List.find?, hne, decide_false, Bool.false_eq_true, if_false] at hg ⊢
      simp only [THeap.put, if_neg hne, THeap.get?, List.find?, hne, decide_false,
        Bool.false_eq_true, if_false]
      exact ih ℓ Θ Θ0 hg

/-- `txnUpdate` services a txn op via `txnService`: when `hsTxn hs ℓ = some Θ` and `op` is a txn op,
`txnUpdate ℓ op v hs` returns `(r, hs')` where `(r, Θ') = txnService op v Θ` and `hsTxns hs' =
(hsTxns hs).put ℓ Θ'`. The structural `TCorr`-preservation fact (D4). Induction on `hs`. -/
theorem txnUpdate_service {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val} (hop : isTxnOp op = true) :
    ∀ {hs : HStack} {Θ : List Val}, hsTxn hs ℓ = some Θ →
      ∃ hs', txnUpdate ℓ op v hs = some ((txnService op v Θ).1, hs')
        ∧ hsTxns hs' = (hsTxns hs).put ℓ (txnService op v Θ).2 := by
  intro hs
  induction hs with
  | nil => intro Θ hg; simp [hsTxn] at hg
  | cons fr hs ih =>
    intro Θ hg
    cases hh : fr.handler with
    | transaction ℓ0 Θ0 =>
        by_cases hc : ℓ0 = ℓ
        · subst hc
          simp only [hsTxn, hh, ↓reduceIte, Option.some.injEq] at hg
          subst hg
          refine ⟨{ fr with handler := .transaction ℓ0 (txnService op v Θ0).2 } :: hs, ?_, ?_⟩
          · simp only [txnUpdate, hh, ↓reduceIte, hop]
          · simp [hsTxns, hh, THeap.put]
        · simp only [hsTxn, hh, if_neg hc] at hg
          obtain ⟨hs', hsu, heq⟩ := ih hg
          refine ⟨fr :: hs', ?_, ?_⟩
          · simp [txnUpdate, hh, hc, hsu]
          · simp only [hsTxns, hh, heq, THeap.put, if_neg hc]
    | state ℓ0 s =>
        simp only [hsTxn, hh] at hg
        obtain ⟨hs', hsu, heq⟩ := ih hg
        refine ⟨fr :: hs', ?_, ?_⟩
        · simp only [txnUpdate, hh, hsu, Option.map_some]
        · simp only [hsTxns, hh, heq]
    | throws ℓ0 =>
        simp only [hsTxn, hh] at hg
        obtain ⟨hs', hsu, heq⟩ := ih hg
        refine ⟨fr :: hs', ?_, ?_⟩
        · simp only [txnUpdate, hh, hsu, Option.map_some]
        · simp only [hsTxns, hh, heq]

/-- `txnUpdate` finds nothing when no transaction frame for `ℓ` is active (the OP then falls through
to `unwindFind`). Mirror of `stateUpdate_none_of_get?_none`. Induction on `hs`. -/
theorem txnUpdate_none_of_hsTxn_none {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val} :
    ∀ {hs : HStack}, hsTxn hs ℓ = none → txnUpdate ℓ op v hs = none := by
  intro hs
  induction hs with
  | nil => intro _; rfl
  | cons fr hs ih =>
    intro hns
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        simp only [hsTxn, hh] at hns
        by_cases hc : ℓ0 = ℓ
        · simp [if_pos hc] at hns
        · simp only [if_neg hc] at hns
          simp [txnUpdate, hh, hc, ih hns]
    | state ℓ0 s => simp only [hsTxn, hh] at hns; simp [txnUpdate, hh, ih hns]
    | throws ℓ0 => simp only [hsTxn, hh] at hns; simp [txnUpdate, hh, ih hns]

/-- `txnUpdate` finds nothing for a non-txn op (it guards `isTxnOp`), so the OP falls through to the
throws path — mirroring `evalD`'s `raised` for such ops on a txn label. Induction on `hs`. -/
theorem txnUpdate_none_of_non_txnop (ℓ : Bang.EffectRow.Label) (v : Val) :
    ∀ (hs : HStack) {op : Bang.OpId}, isTxnOp op = false → txnUpdate ℓ op v hs = none := by
  intro hs
  induction hs with
  | nil => intro op _; rfl
  | cons fr hs ih =>
    intro op hop
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        by_cases hc : ℓ0 = ℓ
        · simp [txnUpdate, hh, hc, hop]
        · simp [txnUpdate, hh, hc, ih hop]
    | state ℓ0 s => simp [txnUpdate, hh, ih hop]
    | throws ℓ0 => simp [txnUpdate, hh, ih hop]

/-- `TCorr` is preserved by a `handle (transaction ℓ Θ)` install: PUSHING `(ℓ ↦ Θ)` on the heap-store
mirrors pushing a `transaction ℓ Θ` frame. -/
theorem TCorr_install {τ : THeap} {hs : HStack} (ℓ : Bang.EffectRow.Label) (Θ : List Val) (fr : HFrame)
    (hfr : fr.handler = .transaction ℓ Θ) (hT : TCorr τ hs) : TCorr (τ.push ℓ Θ) (fr :: hs) := by
  unfold TCorr at hT ⊢; rw [hT]; simp [hsTxns, hfr, THeap.push]

/-- A NON-txn frame (state/throws) carries no heap entry: pushing it preserves `TCorr`. -/
theorem TCorr_install_nontxn {τ : THeap} {hs : HStack} (fr : HFrame)
    (hnt : ∀ ℓ Θ, fr.handler ≠ .transaction ℓ Θ) (hT : TCorr τ hs) : TCorr τ (fr :: hs) := by
  unfold TCorr at hT ⊢; rw [hT]
  cases hh : fr.handler with
  | transaction ℓ0 Θ => exact absurd hh (hnt ℓ0 Θ)
  | state ℓ0 s => simp [hsTxns, hh]
  | throws ℓ0 => simp [hsTxns, hh]

/-- `TCorr` for the tail when the top is a `transaction` frame (the `handle (transaction)` POP). -/
theorem TCorr_pop_txn {τ : THeap} {fr : HFrame} {hs : HStack} {ℓ0 : Bang.EffectRow.Label}
    {Θ : List Val} (hfr : fr.handler = .transaction ℓ0 Θ) (hT : TCorr τ (fr :: hs)) :
    TCorr τ.tail hs := by unfold TCorr at hT ⊢; rw [hT]; simp [hsTxns, hfr]

/-- `TCorr` passes to the tail under a NON-txn (state/throws) top frame: it carries no heap entry, so
the txn projection of `fr :: hs` equals that of `hs`. The `handle (state)`-POP txn-side fact. -/
theorem TCorr_pop_nontxn {τ : THeap} {fr : HFrame} {hs : HStack}
    (hnt : ∀ ℓ Θ, fr.handler ≠ .transaction ℓ Θ) (hT : TCorr τ (fr :: hs)) : TCorr τ hs := by
  unfold TCorr at hT ⊢; rw [hT]
  cases hh : fr.handler with
  | transaction ℓ0 Θ => exact absurd hh (hnt ℓ0 Θ)
  | state ℓ0 s => simp [hsTxns, hh]
  | throws ℓ0 => simp [hsTxns, hh]

/-! ### Cross-projection stability (op-disjointness made structural): a txn service leaves the STATE
projection unchanged, and a state put leaves the TXN projection unchanged. These are the facts that
let the two parallel stores coexist soundly — the load-bearing op-disjointness invariant, used in
`sim`'s `up` case. -/

/-- `txnUpdate`-service leaves the STATE projection unchanged (a txn op never touches a state frame).
Induction on the `txnUpdate` recursion. -/
theorem hsStates_txnUpdate {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, txnUpdate ℓ op v hs = some (r, hs') → hsStates hs' = hsStates hs := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [txnUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        by_cases hc : ℓ0 = ℓ
        · subst hc
          by_cases hop : isTxnOp op = true
          · simp only [txnUpdate, hh, ↓reduceIte, hop, Option.some.injEq] at hsu
            obtain ⟨_, rfl⟩ := hsu; simp [hsStates, hh]
          · simp only [txnUpdate, hh, ↓reduceIte, hop] at hsu; simp at hsu
        · simp only [txnUpdate, hh, if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          simp only [hsStates, hh]; exact ih hsu1
    | state ℓ0 s =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsStates, hh]; rw [ih hsu1]
    | throws ℓ0 =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsStates, hh]; exact ih hsu1

/-- Under `Corr σ hs`, a `txnUpdate` (which leaves the state projection fixed) preserves `Corr σ`. -/
theorem Corr_txnUpdate_eq {σ : SStore} {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v r : Val}
    {hs hs' : HStack} (hsu : txnUpdate ℓ op v hs = some (r, hs')) : Corr σ hs → Corr σ hs' := by
  intro hC; unfold Corr at hC ⊢; rw [hC, hsStates_txnUpdate hsu]

/-- `txnUpdate`-service preserves `HMut` (it mutates one txn-frame heap in place). -/
theorem HMut_of_txnUpdate {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, txnUpdate ℓ op v hs = some (r, hs') → HMut hs hs' := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [txnUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        by_cases hc : ℓ0 = ℓ
        · subst hc
          by_cases hop : isTxnOp op = true
          · simp only [txnUpdate, hh, ↓reduceIte, hop, Option.some.injEq] at hsu
            obtain ⟨_, rfl⟩ := hsu
            exact ⟨⟨rfl, rfl, by simp [hh]⟩, HMut.refl hs⟩
          · simp only [txnUpdate, hh, ↓reduceIte, hop] at hsu; simp at hsu
        · simp only [txnUpdate, hh, if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          exact ⟨⟨rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | state ℓ0 s =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | throws ℓ0 =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, by simp [hh]⟩, ih hsu1⟩

/-- `stateUpdate`-put leaves the TXN projection unchanged (a state op never touches a txn frame).
The mirror of `hsStates_txnUpdate`. Induction on the `stateUpdate` recursion. -/
theorem hsTxns_stateUpdate_put {ℓ : Bang.EffectRow.Label} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, stateUpdate ℓ "put" v hs = some (r, hs') → hsTxns hs' = hsTxns hs := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [stateUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | state ℓ0 s =>
        by_cases hc : ℓ0 = ℓ
        · subst hc
          simp only [stateUpdate, hh, ↓reduceIte, if_neg (by decide : ¬ ("put" = "get")),
            Option.some.injEq] at hsu
          obtain ⟨_, rfl⟩ := hsu; simp [hsTxns, hh]
        · simp only [stateUpdate, hh, if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          simp only [hsTxns, hh]; exact ih hsu1
    | throws ℓ0 =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsTxns, hh]; exact ih hsu1
    | transaction ℓ0 Θ =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsTxns, hh]; rw [ih hsu1]

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
      | some (r, hs') => exec f c (.ret r :: s) hs'            -- RESUME (state): continue c with ret r
      | none =>                                                -- not a state frame: try transaction
          match txnUpdate ℓ op v hs with
          | some (r, hs') => exec f c (.ret r :: s) hs'        -- RESUME (txn): continue c with ret r
          | none =>                                            -- not a resumptive frame ⇒ throws abort
              match unwindFind ℓ op hs with
              | some (c', s', hs') => exec f c' (.ret v :: s') hs' -- ABORT to (Kₒ, ret v), c discarded
              | none               => none                     -- uncaught = stuck
  -- ADT eliminators (Unit 6): inspect the closed-value scrutinee in place, re-`compile` the chosen
  -- branch[v] (fuel-bounded ⇒ terminating), mirroring the `SUBST` exec arm. PURE — no `hs` change.
  | Nat.succ f, Instr.CASE w N₁ N₂ :: c, s, hs =>
      match w with
      | .inl v => exec f (compile (Comp.subst v N₁) c) s hs
      | .inr v => exec f (compile (Comp.subst v N₂) c) s hs
      | _      => none
  | Nat.succ f, Instr.SPLIT w N :: c, s, hs =>
      match w with
      | .pair v u => exec f (compile (Comp.subst v (Comp.subst (Val.shift u) N)) c) s hs
      | _         => none

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
          cases htu : txnUpdate ℓ op v hs with
          | some ru =>
            obtain ⟨r, hs'⟩ := ru
            simp only [htu] at h ⊢; exact ih _ _ _ _ h
          | none =>
            simp only [htu] at h ⊢
            cases hu : unwindFind ℓ op hs with
            | none => simp only [hu] at h; simp at h
            | some cs => obtain ⟨c', s', hs'⟩ := cs; simp only [hu] at h ⊢; exact ih _ _ _ _ h
      | CASE w N₁ N₂ =>
        simp only [exec] at h ⊢
        cases w with
        | inl v => simp only [] at h ⊢; exact ih _ _ _ _ h
        | inr v => simp only [] at h ⊢; exact ih _ _ _ _ h
        | _ => simp at h
      | SPLIT w N =>
        simp only [exec] at h ⊢
        cases w with
        | pair v u => simp only [] at h ⊢; exact ih _ _ _ _ h
        | _ => simp at h

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
    (∀ M σ τ t σ' τ', evalD fe σ τ M = some (.term t, σ', τ') →
      ∀ hs, Corr σ hs → TCorr τ hs →
        ∃ hsf, Corr σ' hsf ∧ TCorr τ' hsf ∧ HMut hs hsf ∧
          ∀ c s F r, exec F c (t :: s) hsf = some r →
            ∃ F', exec F' (compile M c) s hs = some r)
    ∧ (∀ M σ τ ℓ op v σ' τ', evalD fe σ τ M = some (.raised ℓ op v, σ', τ') →
      ∀ hs, Corr σ hs → TCorr τ hs →
        -- the at-raise HStack `netEffect hs σ' τ'` mirrors the at-raise stores σ'/τ' (D3/D4) and is a
        -- value/heap-mutation of the at-handle `hs` — threaded so the throws-CAUGHT term subcase can
        -- name it as its existential witness (an outer put/writeTVar before a caught raise persists).
        (Corr σ' (netEffect hs σ' τ') ∧ TCorr τ' (netEffect hs σ' τ') ∧ HMut hs (netEffect hs σ' τ')) ∧
        ∀ c s F r, throwOutcome F ℓ op v (netEffect hs σ' τ') = some r →
        ∃ F', exec F' (compile M c) s hs = some r) := by
  intro fe
  induction fe with
  | zero =>
      exact ⟨fun M σ τ t σ' τ' h => by simp [evalD] at h,
             fun M σ τ ℓ op v σ' τ' h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M σ τ t σ' τ' h hs hC hT
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
          exact ⟨hs, hC, hT, HMut.refl hs, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
          exact ⟨hs, hC, hT, HMut.refl hs, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.ret v), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hlenM, kM⟩ := ihT M σ τ (.ret v) σ1 τ1 hM hs hC hT
                obtain ⟨hsf, hCf, hTf, hlenf, kN⟩ := ihT (Comp.subst v N) σ1 τ1 t σ' τ' h hsM hCM hTM
                refine ⟨hsf, hCf, hTf, HMut.trans hlenM hlenf, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kN c s F r hr
                have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.SUBST N :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.lam M2), _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _, _), h =>
                -- letC propagates a raise: evalD (letC M N) = raised ⇒ h : raised = term, absurd
                simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hlenf, k⟩ := ihT M σ τ t σ' τ' h hs hC hT
              exact ⟨hsf, hCf, hTf, hlenf, fun c s F r hr => by
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
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.lam N), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hlenM, kM⟩ := ihT M σ τ (.lam N) σ1 τ1 hM hs hC hT
                obtain ⟨hsf, hCf, hTf, hlenf, kN⟩ := ihT (Comp.subst v N) σ1 τ1 t σ' τ' h hsM hCM hTM
                refine ⟨hsf, hCf, hTf, HMut.trans hlenM hlenf, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kN c s F r hr
                have hstep : exec (F1+1) (Instr.APP v :: c) (.lam N :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.APP v :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.ret w), _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _, _), h => simp [Option.bind] at h
      | perform _ ℓ op v =>
          -- RESUME (D1/D2/D4), OP-FIRST: get/put serviced against σ (state), txn ops against τ. Mirrored
          -- by stateUpdate (op-guard {get,put}) then txnUpdate (op-guard isTxnOp) on hs.
          simp only [evalD] at h
          by_cases hop : op = "get"
          · subst hop
            simp only [if_pos rfl] at h
            cases hg : σ.get? ℓ with
            | none => rw [hg] at h; simp at h
            | some sv =>
                rw [hg] at h
                simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have hgState : hsState hs ℓ = some sv := by rw [← Corr.get? hC ℓ]; exact hg
                refine ⟨hs, hC, hT, HMut.refl hs, fun c s F r hr => ⟨F+1, ?_⟩⟩
                simp only [compile, exec, stateUpdate_get hgState]; exact hr
          · by_cases hop2 : op = "put"
            · subst hop2
              simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl] at h
              cases hg : σ.get? ℓ with
              | none => rw [hg] at h; simp at h
              | some sv =>
                  rw [hg] at h
                  simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  have hgState : hsState hs ℓ = some sv := by rw [← Corr.get? hC ℓ]; exact hg
                  obtain ⟨hs', hsu, heq⟩ := stateUpdate_put (v := v) hgState
                  refine ⟨hs', Corr_put hC heq, ?_, HMut.of_stateUpdate_put hsu, fun c s F r hr => ⟨F+1, ?_⟩⟩
                  · unfold TCorr; rw [hsTxns_stateUpdate_put hsu, ← hT]
                  · simp only [compile, exec, hsu]; exact hr
            · by_cases hopt : isTxnOp op = true
              · -- txn op: t = ret r, σ' = σ, τ' = τ.put ℓ Θ'. Machine: stateUpdate none (not get/put) ⇒ txnUpdate.
                simp only [if_neg hop, if_neg hop2, hopt, if_true] at h
                cases hgt : τ.get? ℓ with
                | none => rw [hgt] at h; simp at h
                | some Θ =>
                    rw [hgt] at h
                    simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have hgTxn : hsTxn hs ℓ = some Θ := by rw [← TCorr.get? hT ℓ]; exact hgt
                    obtain ⟨hs', hsu, heq⟩ := txnUpdate_service (v := v) hopt hgTxn
                    refine ⟨hs', Corr_txnUpdate_eq hsu hC, ?_, HMut_of_txnUpdate hsu,
                      fun c s F r hr => ⟨F+1, ?_⟩⟩
                    · unfold TCorr; rw [heq, ← hT]
                    · have hns : stateUpdate ℓ op v hs = none :=
                        stateUpdate_none_of_non_getput ℓ v hs hop hop2
                      simp only [compile, exec, hns, hsu]; exact hr
              · -- neither a state nor a txn op: evalD raises ⇒ term part contradiction.
                rw [Bool.not_eq_true] at hopt
                simp only [if_neg hop, if_neg hop2, hopt, if_false, Option.some.injEq,
                  Prod.mk.injEq, reduceCtorEq, false_and] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              -- INSTALL a state frame: body runs under σ.push ℓ0 s0 / a pushed state frame.
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                    -- The existential = `netEffect hs σ1.tail τ1` — M's net HStack effect as a PURE
                    -- function of `hs`/post-stores. `body cc ss` runs M under the REAL frame
                    -- `{state ℓ0 s0, cc, ss}` and shows its popped tail IS `netEffect hs σ1.tail τ1`.
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 cc (.ret v :: ss) (netEffect hs σ1.tail τ1) = some r2 →
                        (∃ F', exec F' (compile M (Instr.UNMARK :: cc)) ss
                          ({ handler := Handler.state ℓ0 s0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1.tail (netEffect hs σ1.tail τ1) ∧ TCorr τ1 (netEffect hs σ1.tail τ1)
                        ∧ HMut hs (netEffect hs σ1.tail τ1) := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { handler := Handler.state ℓ0 s0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hCinstall : Corr (σ.push ℓ0 s0) (fr :: hs) :=
                        Corr_install ℓ0 s0 fr (by rw [hfrdef]) hC
                      have hTinstall : TCorr τ (fr :: hs) :=
                        TCorr_install_nontxn fr (by rw [hfrdef]; intro ℓ Θ; simp) hT
                      obtain ⟨hsM, hCM, hTM, hmutM, kM⟩ :=
                        ihT M (σ.push ℓ0 s0) τ (.ret v) σ1 τ1 hM (fr :: hs) hCinstall hTinstall
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
                      have hTtail : TCorr τ1 tail :=
                        TCorr_pop_nontxn (by rw [hts]; intro ℓ Θ; simp) hTM
                      have htaileq : tail = netEffect hs σ1.tail τ1 :=
                        updateStates_eq (HMut.tail hmutM) hCtail hTtail
                      -- the body's terminal config `top :: tail`; UNMARK pops `top` ⇒ run `cc` from `tail`.
                      have hstep : exec (F2+1) (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ (HMut.tail hmutM)⟩
                    obtain ⟨_, hCf, hTf, hmutf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1.tail τ1, hCf, hTf, hmutf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.lam M2), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _, _), h =>
                    -- body raises past the state frame (state never catches a throws) ⇒ handle forwards
                    -- ⇒ raised, contradicting the term part.
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                    -- throws-install + normal return: existential = `netEffect hs σ1 τ1` (throws carries
                    -- no state/heap ⇒ both stores pass through). Pop the throws frame (non-state, non-txn).
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 cc (.ret v :: ss) (netEffect hs σ1 τ1) = some r2 →
                        (∃ F', exec F' (compile M (Instr.UNMARK :: cc)) ss
                          ({ handler := Handler.throws ℓ0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (netEffect hs σ1 τ1) ∧ TCorr τ1 (netEffect hs σ1 τ1)
                        ∧ HMut hs (netEffect hs σ1 τ1) := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { handler := Handler.throws ℓ0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hns : ∀ ℓ s, fr.handler ≠ Handler.state ℓ s := by rw [hfrdef]; intro ℓ s; simp
                      have hnt : ∀ ℓ Θ, fr.handler ≠ Handler.transaction ℓ Θ := by rw [hfrdef]; intro ℓ Θ; simp
                      have hCinstall : Corr σ (fr :: hs) := Corr_install_nonstate fr hns hC
                      have hTinstall : TCorr τ (fr :: hs) := TCorr_install_nontxn fr hnt hT
                      obtain ⟨hsM, hCM, hTM, hmutM, kM⟩ := ihT M σ τ (.ret v) σ1 τ1 hM (fr :: hs) hCinstall hTinstall
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have hCtail := Corr_pop_nonstate hns hmutM hCM
                      have hTtail : TCorr τ1 tail := TCorr_pop_nontxn (by
                        obtain ⟨⟨_, _, hsh⟩, _⟩ := hmutM
                        intro ℓ Θ
                        cases hth : top.handler with
                        | transaction _ _ => rw [hfrdef, hth] at hsh; exact absurd hsh (by simp)
                        | state _ _ => simp [hth]
                        | throws _ => simp [hth]) hTM
                      have htaileq : tail = netEffect hs σ1 τ1 := updateStates_eq (HMut.tail hmutM) hCtail hTtail
                      have hstep : exec (F2+1) (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ (HMut.tail hmutM)⟩
                    obtain ⟨_, hCf, hTf, hmutf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1 τ1, hCf, hTf, hmutf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.lam M2), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    by_cases hc : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp only [Option.bind_some, if_pos hc, Option.some.injEq, Prod.mk.injEq,
                        Outcome.term.injEq] at h
                      obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                      obtain ⟨rfl, rfl⟩ := hc
                      -- caught: M raises `(ℓ0,raise)` ⇒ machine OP catches the throws frame, aborts to the
                      -- MARK's saved (c2,s2) with `ret w`. The abort unwinds only the CONTINUATION; the
                      -- stores stay at the at-raise `σ1`/`τ1` (caught = at-raise, keeping outer puts/writes),
                      -- so the existential HStack is `netEffect hs σ1 τ1`. The outer triple over `hs` comes
                      -- from popping the throws install frame (non-state, non-txn) off the raised IH's triple.
                      have hns0 : ∀ ℓ s, (Handler.throws ℓ0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                      have hnt0 : ∀ ℓ Θ, (Handler.throws ℓ0) ≠ Handler.transaction ℓ Θ := by intro ℓ Θ; simp
                      have htriple : Corr σ1 (netEffect hs σ1 τ1) ∧ TCorr τ1 (netEffect hs σ1 τ1)
                          ∧ HMut hs (netEffect hs σ1 τ1) := by
                        set fr0 : HFrame := { handler := Handler.throws ℓ0, savedCode := [], savedStack := [] }
                        have hns : ∀ ℓ s, fr0.handler ≠ Handler.state ℓ s := hns0
                        have hnt : ∀ ℓ Θ, fr0.handler ≠ Handler.transaction ℓ Θ := hnt0
                        obtain ⟨⟨hCr, hTr, hmutr⟩, _⟩ :=
                          ihR M σ τ ℓ0 "raise" w σ1 τ1 hM (fr0 :: hs)
                            (Corr_install_nonstate fr0 hns hC) (TCorr_install_nontxn fr0 hnt hT)
                        exact raisedTriple_pop_nontxn hns hnt hCr hTr hmutr
                      refine ⟨netEffect hs σ1 τ1, htriple.1, htriple.2.1, htriple.2.2, fun c2 s2 F2 r2 hr2 => ?_⟩
                      set fr2 : HFrame := { handler := Handler.throws ℓ0, savedCode := c2, savedStack := s2 }
                        with hfrdef
                      have hCinstall2 : Corr σ (fr2 :: hs) := Corr_install_nonstate fr2 hns0 hC
                      have hTinstall2 : TCorr τ (fr2 :: hs) := TCorr_install_nontxn fr2 hnt0 hT
                      obtain ⟨_, kR2⟩ := ihR M σ τ ℓ0 "raise" w σ1 τ1 hM (fr2 :: hs) hCinstall2 hTinstall2
                      have hthrow : throwOutcome F2 ℓ0 "raise" w (netEffect (fr2 :: hs) σ1 τ1) = some r2 := by
                        rw [netEffect_cons_throws (show fr2.handler = .throws ℓ0 from by rw [hfrdef])]
                        simp only [throwOutcome, unwindFind, hfrdef, and_self, if_true]; exact hr2
                      obtain ⟨F1, hF1⟩ := kR2 (Instr.UNMARK :: c2) s2 F2 r2 hthrow
                      exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                    · simp [Option.bind_some, if_neg hc] at h
          | transaction ℓ0 Θ =>
              -- INSTALL a transaction frame: body runs under τ.push ℓ0 Θ / a pushed txn frame; on a
              -- normal return POP the heap (τ1.tail). Mirror of the state install, on the τ side.
              simp only at h
              cases hM : evalD fe σ (τ.push ℓ0 Θ) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 cc (.ret v :: ss) (netEffect hs σ1 τ1.tail) = some r2 →
                        (∃ F', exec F' (compile M (Instr.UNMARK :: cc)) ss
                          ({ handler := Handler.transaction ℓ0 Θ, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (netEffect hs σ1 τ1.tail) ∧ TCorr τ1.tail (netEffect hs σ1 τ1.tail)
                        ∧ HMut hs (netEffect hs σ1 τ1.tail) := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { handler := Handler.transaction ℓ0 Θ, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hCinstall : Corr σ (fr :: hs) :=
                        Corr_install_nonstate fr (by rw [hfrdef]; intro ℓ s; simp) hC
                      have hTinstall : TCorr (τ.push ℓ0 Θ) (fr :: hs) :=
                        TCorr_install ℓ0 Θ fr (by rw [hfrdef]) hT
                      obtain ⟨hsM, hCM, hTM, hmutM, kM⟩ :=
                        ihT M σ (τ.push ℓ0 Θ) (.ret v) σ1 τ1 hM (fr :: hs) hCinstall hTinstall
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have htop : ∃ Θ', top.handler = .transaction ℓ0 Θ' := by
                        have hh := hmutM.1.2.2
                        cases hth : top.handler with
                        | transaction ℓ1 Θ1 => rw [hfrdef, hth] at hh; simp only at hh; subst hh; exact ⟨Θ1, rfl⟩
                        | state _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | throws _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                      obtain ⟨Θ', hts⟩ := htop
                      have hTtail := TCorr_pop_txn hts hTM
                      have hCtail : Corr σ1 tail :=
                        Corr_pop_nonstate (by rw [hfrdef]; intro ℓ s; simp) hmutM hCM
                      have htaileq : tail = netEffect hs σ1 τ1.tail :=
                        updateStates_eq (HMut.tail hmutM) hCtail hTtail
                      have hstep : exec (F2+1) (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ (HMut.tail hmutM)⟩
                    obtain ⟨_, hCf, hTf, hmutf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1 τ1.tail, hCf, hTf, hmutf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.lam M2), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
      | case a b d =>
          -- ADT sum elim (Unit 6): closed-value scrutinee, PURE reduction. evalD reduces into a branch;
          -- the IH on `subst v branch` carries it; `CASE` exec re-compiles that branch (mirrors SUBST).
          cases a with
          | inl v =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hlenf, k⟩ := ihT (Comp.subst v b) σ τ t σ' τ' h hs hC hT
              refine ⟨hsf, hCf, hTf, hlenf, fun c s F r hr => ?_⟩
              obtain ⟨F', hF'⟩ := k c s F r hr
              exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩
          | inr v =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hlenf, k⟩ := ihT (Comp.subst v d) σ τ t σ' τ' h hs hC hT
              refine ⟨hsf, hCf, hTf, hlenf, fun c s F r hr => ?_⟩
              obtain ⟨F', hF'⟩ := k c s F r hr
              exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | split a b =>
          -- ADT product elim (Unit 6): DOUBLE subst (note the `shift`), mirroring the kernel.
          cases a with
          | pair v w =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hlenf, k⟩ :=
                ihT (Comp.subst v (Comp.subst (Val.shift w) b)) σ τ t σ' τ' h hs hC hT
              refine ⟨hsf, hCf, hTf, hlenf, fun c s F r hr => ?_⟩
              obtain ⟨F', hF'⟩ := k c s F r hr
              exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | fold w => simp [evalD] at h
      | unfold a =>
          -- ADT μ elim (Unit 6): fold/unfold erase to `ret v`. Terminal — no recursion, no IH needed.
          cases a with
          | fold v =>
              simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
              obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
              exact ⟨hs, hC, hT, HMut.refl hs, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
    · -- RAISED PART
      intro M σ τ ℓ op v σ' τ' h hs hC hT
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | perform _ ℓ2 op2 v2 =>
          -- OP-FIRST raise: a `raised` from `up` means the op matched no resumptive frame — either a
          -- get/put with no state frame, a txn op with no txn frame, or a non-resumptive op. In ALL of
          -- these the machine's stateUpdate/txnUpdate both return none and the OP falls to the throw path.
          -- The net-effect is the identity (no store changed), so the existential HStack is `hs`.
          simp only [evalD] at h
          -- A single helper closing every raise-subcase: stores unchanged ⇒ netEffect = hs, machine OP
          -- falls to unwindFind = throwOutcome.
          have close : ∀ (hns : stateUpdate ℓ op v hs = none) (hnt : txnUpdate ℓ op v hs = none),
              (Corr σ (netEffect hs σ τ) ∧ TCorr τ (netEffect hs σ τ) ∧ HMut hs (netEffect hs σ τ)) ∧
              ∀ c s F r, throwOutcome F ℓ op v (netEffect hs σ τ) = some r →
                ∃ F', exec F' (compile (.perform 0 ℓ op v) c) s hs = some r := by
            intro hns hnt
            have hus : netEffect hs σ τ = hs := updateStates_self hC hT
            refine ⟨⟨by rw [hus]; exact hC, by rw [hus]; exact hT, by rw [hus]; exact HMut.refl hs⟩,
              fun c s F r hr => ?_⟩
            rw [hus] at hr
            refine ⟨F+1, ?_⟩
            simp only [compile, exec, hns, hnt]
            simpa only [throwOutcome] using hr
          by_cases hop : op2 = "get"
          · subst hop
            simp only [if_pos rfl] at h
            cases hg : σ.get? ℓ2 with
            | none =>
                rw [hg] at h; simp only [Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                exact close (stateUpdate_none_of_get?_none (Corr.get? hC ℓ ▸ hg))
                  (txnUpdate_none_of_non_txnop ℓ v hs (by decide))
            | some sv => rw [hg] at h; simp at h
          · by_cases hop2 : op2 = "put"
            · subst hop2
              simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl] at h
              cases hg : σ.get? ℓ2 with
              | none =>
                  rw [hg] at h; simp only [Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                  exact close (stateUpdate_none_of_get?_none (Corr.get? hC ℓ ▸ hg))
                    (txnUpdate_none_of_non_txnop ℓ v hs (by decide))
              | some sv => rw [hg] at h; simp at h
            · by_cases hopt : isTxnOp op2 = true
              · simp only [if_neg hop, if_neg hop2, hopt, if_true] at h
                cases hgt : τ.get? ℓ2 with
                | none =>
                    rw [hgt] at h; simp only [Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                    exact close (stateUpdate_none_of_non_getput ℓ2 v2 hs hop hop2)
                      (txnUpdate_none_of_hsTxn_none (TCorr.get? hT ℓ2 ▸ hgt))
                | some Θ => rw [hgt] at h; simp at h
              · rw [Bool.not_eq_true] at hopt
                simp only [if_neg hop, if_neg hop2, hopt, if_false, Option.some.injEq, Prod.mk.injEq,
                  Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                exact close (stateUpdate_none_of_non_getput ℓ v hs hop hop2)
                  (txnUpdate_none_of_non_txnop ℓ v hs hopt)
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1, τ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                obtain ⟨hpair, kR⟩ := ihR M σ τ ℓ' op' w σ1 τ1 hM hs hC hT
                exact ⟨hpair, fun c s F r hr => by
                  obtain ⟨F1, hF1⟩ := kR (Instr.SUBST N :: c) s F r hr
                  exact ⟨F1, by simpa [compile] using hF1⟩⟩
            | (.term (.ret v0), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hmutM, kM⟩ := ihT M σ τ (.ret v0) σ1 τ1 hM hs hC hT
                -- the inner raise is over hsM (HMut hs); re-base via `netEffect_congr_HMut` so the inner
                -- `ihR` over `netEffect hsM σ' τ'` reuses the outer `hr` over `netEffect hs σ' τ'`.
                obtain ⟨⟨hCr, hTr, hmutr⟩, kR⟩ := ihR (Comp.subst v0 N) σ1 τ1 ℓ op v σ' τ' h hsM hCM hTM
                have hreb : netEffect hsM σ' τ' = netEffect hs σ' τ' := netEffect_congr_HMut σ' τ' hmutM hCr hTr
                refine ⟨⟨hreb ▸ hCr, hreb ▸ hTr, HMut.trans hmutM (hreb ▸ hmutr)⟩, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR c s F r (by rw [hreb]; exact hr)
                have hstep : exec (F1+1) (Instr.SUBST N :: c) (.ret v0 :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.SUBST N :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.lam a), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hpair, kR⟩ := ihR M σ τ ℓ op v σ' τ' h hs hC hT
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
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1, τ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                obtain ⟨hpair, kR⟩ := ihR M σ τ ℓ' op' w σ1 τ1 hM hs hC hT
                exact ⟨hpair, fun c s F r hr => by
                  obtain ⟨F1, hF1⟩ := kR (Instr.APP v0 :: c) s F r hr
                  exact ⟨F1, by simpa [compile] using hF1⟩⟩
            | (.term (.lam N), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hmutM, kM⟩ := ihT M σ τ (.lam N) σ1 τ1 hM hs hC hT
                obtain ⟨⟨hCr, hTr, hmutr⟩, kR⟩ := ihR (Comp.subst v0 N) σ1 τ1 ℓ op v σ' τ' h hsM hCM hTM
                have hreb : netEffect hsM σ' τ' = netEffect hs σ' τ' := netEffect_congr_HMut σ' τ' hmutM hCr hTr
                refine ⟨⟨hreb ▸ hCr, hreb ▸ hTr, HMut.trans hmutM (hreb ▸ hmutr)⟩, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR c s F r (by rw [hreb]; exact hr)
                have hstep : exec (F1+1) (Instr.APP v0 :: c) (.lam N :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.APP v0 :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.ret w), _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                    -- at-raise TRIPLE: one IH over a dummy install frame, popped through the state frame.
                    have htriple : Corr σ1.tail (netEffect hs σ1.tail τ1) ∧ TCorr τ1 (netEffect hs σ1.tail τ1)
                        ∧ HMut hs (netEffect hs σ1.tail τ1) := by
                      set fr0 : HFrame := { handler := Handler.state ℓ0 s0, savedCode := [], savedStack := [] }
                        with hfr0
                      obtain ⟨⟨hCr, hTr, hmutr⟩, _⟩ :=
                        ihR M (σ.push ℓ0 s0) τ ℓ' op' w σ1 τ1 hM (fr0 :: hs)
                          (Corr_install ℓ0 s0 fr0 (by rw [hfr0]) hC)
                          (TCorr_install_nontxn fr0 (by rw [hfr0]; intro ℓ Θ; simp) hT)
                      exact raisedTriple_pop_state (by rw [hfr0]) hCr hTr hmutr
                    refine ⟨htriple, fun c s F r hr => ?_⟩
                    set fr : HFrame := { handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, kR⟩ := ihR M (σ.push ℓ0 s0) τ ℓ' op' w σ1 τ1 hM (fr :: hs)
                      (Corr_install ℓ0 s0 fr (by rw [hfrdef]) hC)
                      (TCorr_install_nontxn fr (by rw [hfrdef]; intro ℓ Θ; simp) hT)
                    have hfwd : throwOutcome F ℓ' op' w (netEffect (fr :: hs) σ1 τ1) = some r := by
                      have hskip : throwOutcome F ℓ' op' w (netEffect (fr :: hs) σ1 τ1)
                          = throwOutcome F ℓ' op' w (netEffect hs σ1.tail τ1) := by
                        cases σ1 with
                        | nil =>
                            unfold netEffect; rw [updateStates]; simp only [hfrdef, List.tail]
                            rw [updateTxns_cons_state τ1 (show ({ handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s : HFrame } : HFrame).handler = .state ℓ0 s0 from rfl)]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)
                        | cons p σ1' =>
                            obtain ⟨ℓa, wa⟩ := p
                            unfold netEffect; rw [updateStates]; simp only [hfrdef, List.tail]
                            rw [updateTxns_cons_state τ1 (show ({ handler := Handler.state ℓ0 wa, savedCode := c, savedStack := s : HFrame } : HFrame).handler = .state ℓ0 wa from rfl)]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)
                      rw [hskip]; exact hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.ret v0), _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp [if_pos hk] at h
                    · simp only [if_neg hk, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                      have hns0 : ∀ ℓ s, (Handler.throws ℓ0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                      have hnt0 : ∀ ℓ Θ, (Handler.throws ℓ0) ≠ Handler.transaction ℓ Θ := by intro ℓ Θ; simp
                      have htriple : Corr σ1 (netEffect hs σ1 τ1) ∧ TCorr τ1 (netEffect hs σ1 τ1)
                          ∧ HMut hs (netEffect hs σ1 τ1) := by
                        set fr0 : HFrame := { handler := Handler.throws ℓ0, savedCode := [], savedStack := [] }
                        obtain ⟨⟨hCr, hTr, hmutr⟩, _⟩ :=
                          ihR M σ τ ℓ' op' w σ1 τ1 hM (fr0 :: hs)
                            (Corr_install_nonstate fr0 hns0 hC) (TCorr_install_nontxn fr0 hnt0 hT)
                        exact raisedTriple_pop_nontxn hns0 hnt0 hCr hTr hmutr
                      refine ⟨htriple, fun c s F r hr => ?_⟩
                      set fr : HFrame := { handler := Handler.throws ℓ0, savedCode := c, savedStack := s }
                        with hfrdef
                      obtain ⟨_, kR⟩ := ihR M σ τ ℓ' op' w σ1 τ1 hM (fr :: hs)
                        (Corr_install_nonstate fr hns0 hC) (TCorr_install_nontxn fr hnt0 hT)
                      have hfwd : throwOutcome F ℓ' op' w (netEffect (fr :: hs) σ1 τ1) = some r := by
                        rw [netEffect_cons_throws (show fr.handler = .throws ℓ0 from by rw [hfrdef])]
                        simp only [throwOutcome, unwindFind, hfrdef, if_neg hk]; exact hr
                      obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                      exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.ret v0), _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
          | transaction ℓ0 Θ =>
              simp only at h
              cases hM : evalD fe σ (τ.push ℓ0 Θ) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                    -- transaction-install + raise FORWARD: pop the pushed heap (τ1.tail). The txn frame
                    -- does NOT catch a foreign throws (different label), so the heap is discarded with
                    -- the frame — ROLLBACK IS FREE (ADR-0031 D4). Mirror of the state forward.
                    have htriple : Corr σ1 (netEffect hs σ1 τ1.tail) ∧ TCorr τ1.tail (netEffect hs σ1 τ1.tail)
                        ∧ HMut hs (netEffect hs σ1 τ1.tail) := by
                      set fr0 : HFrame := { handler := Handler.transaction ℓ0 Θ, savedCode := [], savedStack := [] }
                        with hfr0
                      obtain ⟨⟨hCr, hTr, hmutr⟩, _⟩ :=
                        ihR M σ (τ.push ℓ0 Θ) ℓ' op' w σ1 τ1 hM (fr0 :: hs)
                          (Corr_install_nonstate fr0 (by rw [hfr0]; intro ℓ s; simp) hC)
                          (TCorr_install ℓ0 Θ fr0 (by rw [hfr0]) hT)
                      exact raisedTriple_pop_txn (by rw [hfr0]) hCr hTr hmutr
                    refine ⟨htriple, fun c s F r hr => ?_⟩
                    set fr : HFrame := { handler := Handler.transaction ℓ0 Θ, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, kR⟩ := ihR M σ (τ.push ℓ0 Θ) ℓ' op' w σ1 τ1 hM (fr :: hs)
                      (Corr_install_nonstate fr (by rw [hfrdef]; intro ℓ s; simp) hC)
                      (TCorr_install ℓ0 Θ fr (by rw [hfrdef]) hT)
                    have hfwd : throwOutcome F ℓ' op' w (netEffect (fr :: hs) σ1 τ1) = some r := by
                      -- the txn install frame is skipped by the throws-unwind; the heap τ1.tail is what
                      -- the popped triple sees, and netEffect over the txn frame copies it through.
                      have hskip : throwOutcome F ℓ' op' w (netEffect (fr :: hs) σ1 τ1)
                          = throwOutcome F ℓ' op' w (netEffect hs σ1 τ1.tail) := by
                        cases τ1 with
                        | nil =>
                            unfold netEffect; rw [updateStates_cons_txn σ1 (show fr.handler = .transaction ℓ0 Θ from by rw [hfrdef])]
                            simp only [updateTxns, hfrdef, List.tail]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)
                        | cons p τ1' =>
                            obtain ⟨ℓa, Θa⟩ := p
                            unfold netEffect; rw [updateStates_cons_txn σ1 (show fr.handler = .transaction ℓ0 Θ from by rw [hfrdef])]
                            simp only [updateTxns, hfrdef, List.tail]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ (by simp)
                      rw [hskip]; exact hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec]; exact hF1⟩
                | (.term (.ret v0), _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
      | case a b d =>
          -- ADT sum elim (Unit 6) raising: the chosen branch raises. `ihR` on `subst v branch` carries
          -- the at-raise triple + throwOutcome; the `CASE` exec bumps one fuel to re-compile the branch.
          cases a with
          | inl sv =>
              simp only [evalD] at h
              obtain ⟨hpair, kR⟩ := ihR (Comp.subst sv b) σ τ ℓ op v σ' τ' h hs hC hT
              exact ⟨hpair, fun c s F r hr => by
                obtain ⟨F', hF'⟩ := kR c s F r hr; exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩⟩
          | inr sv =>
              simp only [evalD] at h
              obtain ⟨hpair, kR⟩ := ihR (Comp.subst sv d) σ τ ℓ op v σ' τ' h hs hC hT
              exact ⟨hpair, fun c s F r hr => by
                obtain ⟨F', hF'⟩ := kR c s F r hr; exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | split a b =>
          -- ADT product elim (Unit 6) raising: DOUBLE subst, then the branch raises.
          cases a with
          | pair sv sw =>
              simp only [evalD] at h
              obtain ⟨hpair, kR⟩ :=
                ihR (Comp.subst sv (Comp.subst (Val.shift sw) b)) σ τ ℓ op v σ' τ' h hs hC hT
              exact ⟨hpair, fun c s F r hr => by
                obtain ⟨F', hF'⟩ := kR c s F r hr; exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | fold w => simp [evalD] at h
      | unfold a =>
          -- ADT μ elim (Unit 6): always yields `term (ret v)` — never `raised`, so vacuous here.
          cases a with
          | fold v => simp [evalD] at h
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h


/-- Headline: compiling a closed computation and running it on the empty stack/store yields exactly
`[t]` where `evalD n [] M = some (.term t, σ')` (the convergent spine, now over the resumptive-state
store-thread). `compile_correct` analogue of `Bang.Calc`; the `c=[]`, `s=[]`, `hs=[]` corollary of
`sim` (`Corr [] []` holds by `rfl`, the empty store mirrors the empty HStack). -/
theorem compile_correct (n : Nat) (M : Comp) (t : Comp) (σ' : SStore) (τ' : THeap)
    (h : evalD n [] [] M = some (.term t, σ', τ')) :
    ∃ F, exec F (compile M []) [] [] = some [t] := by
  have hbase : exec 1 [] (t :: []) [] = some [t] := by simp [exec]
  obtain ⟨hsf, _, _, hmutf, k⟩ := (sim n).1 M [] [] t σ' τ' h [] rfl rfl
  -- HMut [] hsf forces hsf = [] (a closed program at empty HStack ends at empty), so the continuation
  -- runs on the empty stack — `hbase`.
  have hempty : hsf = [] := by cases hsf with | nil => rfl | cons => simp [HMut] at hmutf
  subst hempty
  obtain ⟨F, hF⟩ := k [] [] 1 [t] hbase
  exact ⟨F, hF⟩

/-! ## The ◊3 diff-test battery — `exec ∘ compile ≡ Source.eval` on a curated program set

The ROADMAP-named ◊3 gate artifact (ADR-0017 / PATH-calcvm-port D3). `compile_correct`
+ `evalD_agrees_source` already PROVE this equality *in general*; this curated battery
is the concrete cross-check that catches definitional drift and DOCUMENTS coverage of
all five feature axes. Curated, not a fuzzer (a generator is a deferred nice-to-have).

The honesty discipline: each case asserts agreement on the **observable value** via
`Agree` — the calculated machine (`exec ∘ compile`, yielding `Option Stack` with the
terminal `ret v` on the stack) and the type-safety-verified kernel (`Source.eval`,
yielding `Result Val`) both produce the SAME `Val v`. Tying both reps to a single `v`
makes a false "they agree" structurally unrepresentable — you cannot satisfy `Agree`
by having the two sides return *different* values. Every case closes by `rfl`
(empirically: the curated programs reduce symbolically, so no `native_decide` and
hence no `Lean.ofReduceBool` in the axiom set — the battery stays axiom-clean). The
empty stores `σ=[]`/`τ=[]` and empty `HStack`/`EvalCtx` mirror the closed-program load.

Coverage (the five axes; a `#guard`-style build failure = a red gate, so green = passing):
  · PURE        — let / app / force·thunk
  · THROWS      — caught raise (`Agree`) + UNCAUGHT raise (no value; asserted separately)
  · STATE       — get-default / put-then-get / outer-put-persists-past-a-caught-throw
  · TRANSACTION — new+read (heap thread) + abort-rollback (write discarded on foreign throw)
  · ADT         — case·inl / case·inr / split / unfold -/

/-- End-to-end agreement at one observable value: the calculated machine
(`exec ∘ compile`) and the kernel reference (`Source.eval`) both yield the SAME
`Val v`. The shared `v` is what makes a false "agree" unrepresentable. -/
def Agree (fuel : Nat) (M : Comp) (v : Val) : Prop :=
  exec fuel (compile M []) [] [] = some [.ret v] ∧ Source.eval fuel M = .done v

-- ─── PURE axis (let / app / force) ───────────────────────────────────────────

/-- `(λ. ret #0) 5` ⇒ `5` — β through `LAMI`/`APP`. -/
example : Agree 12 (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.vint 5) := ⟨by rfl, by rfl⟩

/-- `let x = (λ.ret #0) 5 in ret x` ⇒ `5` — `SUBST` over an applied lambda. -/
example : Agree 16 (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0))) (.vint 5) :=
  ⟨by rfl, by rfl⟩

/-- `force (thunk (ret 9))` ⇒ `9` — `force`∘`vthunk` collapses to the body. -/
example : Agree 12 (.force (.vthunk (.ret (.vint 9)))) (.vint 9) := ⟨by rfl, by rfl⟩

-- ─── THROWS axis (caught + uncaught) ─────────────────────────────────────────

/-- `handle (throws ℓ) (raise 7)` ⇒ `7` — the deep handler catches and aborts with the payload. -/
example : Agree 20 (.handle (.throws 0) (.perform 0 0 "raise" (.vint 7))) (.vint 7) := ⟨by rfl, by rfl⟩

/-- DEEP throws: `handle (throws ℓ) (let _ = raise 7 in 99)` ⇒ `7` — the handler reaches PAST a
`letF` frame and DISCARDS the captured continuation (`99` is never returned). -/
example : Agree 24 (.handle (.throws 0) (.letC (.perform 0 0 "raise" (.vint 7)) (.ret (.vint 99)))) (.vint 7) :=
  ⟨by rfl, by rfl⟩

/-- UNCAUGHT `raise` (no handler in scope) yields NO observable value — so it falls OUTSIDE
`Agree`. Both reps signal it: the machine gets STUCK (`exec = none`), the kernel returns
`.stuck`. The axis is covered by asserting that shared stuckness (not a value agreement). -/
example : exec 20 (compile (.perform 0 0 "raise" (.vint 7)) []) [] [] = none := by rfl
example : Source.eval 20 (Comp.perform 0 0 "raise" (.vint 7)) = .stuck := by rfl

-- ─── STATE axis (get-default / put-then-get / persist-past-caught-throw) ──────

/-- `handle (state ℓ 5) (get ())` ⇒ `5` — read the initial state. -/
example : Agree 40 (.handle (.state 1 (.vint 5)) (.perform 0 1 "get" .vunit)) (.vint 5) := ⟨by rfl, by rfl⟩

/-- `handle (state ℓ 0) (let _ = put 7 in get ())` ⇒ `7` — the RESUMPTIVE handler KEEPS the captured
`letF` continuation and threads the store; `get` reads the `put`. -/
example : Agree 80
    (.handle (.state 1 (.vint 0)) (.letC (.perform 0 1 "put" (.vint 7)) (.perform 0 1 "get" .vunit)))
    (.vint 7) := ⟨by rfl, by rfl⟩

/-- OUTER STATE PERSISTS PAST A CAUGHT THROW: `handle (state ℓ 0) (put 7; handle (throws) (raise);
get)` ⇒ `7`. The inner zero-shot throw is caught and discarded, but the outer resumptive store
survives — `get` still sees the `put 7`. The interaction the resumptive/zero-shot split must get right. -/
example : Agree 100
    (.handle (.state 1 (.vint 0))
      (.letC (.perform 0 1 "put" (.vint 7))
        (.letC (.handle (.throws 0) (.perform 0 0 "raise" .vunit))
          (.perform 0 1 "get" .vunit))))
    (.vint 7) := ⟨by rfl, by rfl⟩

-- ─── TRANSACTION axis (new+read heap-thread / abort-rollback) ─────────────────

/-- `handle (transaction ℓ []) (newTVar 9; readTVar 0)` ⇒ `9` — allocate then read back; the heap
threads through both ops (ADR-0031 D4). -/
example : Agree 40
    (.handle (.transaction 2 []) (.letC (.perform 0 2 "newTVar" (.vint 9)) (.perform 0 2 "readTVar" (.vvar 0))))
    (.vint 9) := ⟨by rfl, by rfl⟩

/-- ABORT-ROLLBACK: an outer `throws` wraps `transaction (newTVar 100; writeTVar 0:=70; raise 100)`.
The `raise` is FOREIGN to the transaction frame, so it escapes it (zero-shot) — the threaded heap with
the `writeTVar 70` is DISCARDED with the frame (never commits). The abort payload `100` is the ORIGINAL
balance, the observable proof the write rolled back. -/
example : Agree 80
    (.handle (.throws 0)
      (.handle (.transaction 2 [])
        (.letC (.perform 0 2 "newTVar" (.vint 100))
          (.letC (.perform 0 2 "writeTVar" (.pair (.vint 0) (.vint 70)))
            (.perform 0 0 "raise" (.vint 100))))))
    (.vint 100) := ⟨by rfl, by rfl⟩

-- ─── ADT axis (case·inl / case·inr / split / unfold) ─────────────────────────
-- `CASE`/`SPLIT` reduce a closed-value scrutinee at runtime; `unfold` ERASES at compile time onto
-- `RET` (like `force∘vthunk`). Both reps agree on the observable value.

/-- `case (inl 5) (ret #0) (ret 99)` ⇒ `5` — sum elim, LEFT branch binds the payload. -/
example : Agree 12 (.case (.inl (.vint 5)) (.ret (.vvar 0)) (.ret (.vint 99))) (.vint 5) :=
  ⟨by rfl, by rfl⟩

/-- `case (inr 7) (ret 99) (ret #0)` ⇒ `7` — sum elim, RIGHT branch. -/
example : Agree 12 (.case (.inr (.vint 7)) (.ret (.vint 99)) (.ret (.vvar 0))) (.vint 7) :=
  ⟨by rfl, by rfl⟩

/-- `split (pair 3 4) (ret #1)` ⇒ `3` — product elim. The DOUBLE subst binds `v=3` at #1 and `w=4`
(shifted) at #0; `ret #1` selects the first component. -/
example : Agree 14 (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1))) (.vint 3) := ⟨by rfl, by rfl⟩

/-- `unfold (fold 8)` ⇒ `8` — μ elim: fold/unfold erase. -/
example : Agree 12 (.unfold (.fold (.vint 8))) (.vint 8) := ⟨by rfl, by rfl⟩

-- The intermediate `evalD` rep agrees too (it sits between the two `Agree` sides): a sample across
-- the ADT axis, documenting that the substitution `evalD` calculated-from is itself faithful.
example : evalD 12 [] [] (.case (.inl (.vint 5)) (.ret (.vvar 0)) (.ret (.vint 99)))
    = some (.term (.ret (.vint 5)), [], []) := by rfl
example : evalD 14 [] [] (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1)))
    = some (.term (.ret (.vint 3)), [], []) := by rfl
example : evalD 12 [] [] (.unfold (.fold (.vint 8)))
    = some (.term (.ret (.vint 8)), [], []) := by rfl

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
    (v : Val) : Bang.Result Val := Bang.Config.run (n+1) (K, .perform 0 ℓ op v)

/-- `dispatchRun` is independent of the carried `cap` field (1a: `Source.step` ignores it).
The raised-config bridge target equals the run from `.perform cap …` for ANY `cap`. -/
theorem dispatchRun_perform (n : Nat) (cap : Nat) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label)
    (op : Bang.OpId) (v : Val) :
    Bang.Config.run (n+1) (K, .perform cap ℓ op v) = dispatchRun n K ℓ op v := by
  cases K with
  | nil => simp only [dispatchRun, Bang.Config.run, Source.step]
  | cons fr K' => simp only [dispatchRun, Bang.Config.run, Source.step]

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

/-! ### Transaction EvalCtx-bridge (ADR-0031 D4): the `Config.run`-side mirror of the txn HStack bridge.
Parallel `THeap` projection of the kernel context's `transaction` frames; same op-disjointness invariant
as the machine side (see `THeap`). -/

/-- Project a kernel `EvalCtx` to the txn-heap store it mirrors: the `handleF (transaction ℓ Θ)` frames. -/
def ctxTxns : Bang.EvalCtx → THeap
  | []                                    => []
  | Frame.handleF (.transaction ℓ Θ) :: K => (ℓ, Θ) :: ctxTxns K
  | _ :: K                                => ctxTxns K

/-- The D4 invariant on the kernel side: `evalD`'s threaded τ IS the context's active txn frames. -/
def CtxTxnCorr (τ : THeap) (K : Bang.EvalCtx) : Prop := τ = ctxTxns K

/-- Overwrite each `transaction` frame's heap in `K` with τ (consumed in order). The `Config.run`-side
analog of `updateTxns`. -/
def updateCtxTxns : Bang.EvalCtx → THeap → Bang.EvalCtx
  | [],                                       _ => []
  | Frame.handleF (.transaction ℓ0 _) :: K, τ =>
      match τ with
      | (_, Θ) :: τ' => Frame.handleF (.transaction ℓ0 Θ) :: updateCtxTxns K τ'
      | []           => Frame.handleF (.transaction ℓ0 default) :: updateCtxTxns K []
  | fr :: K,                                  τ => fr :: updateCtxTxns K τ

/-- The combined kernel-side net-effect: state values from σ, then txn heaps from τ. -/
def ctxNetEffect (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) : Bang.EvalCtx :=
  updateCtxTxns (updateCtxStates K σ) τ

/-- `updateCtxTxns` SKIPS a state-frame head; `updateCtxStates` SKIPS a txn-frame head — the two
EvalCtx passes are independent (frame kinds disjoint). -/
theorem updateCtxTxns_cons_state {ℓ : Bang.EffectRow.Label} {s : Val} {K : Bang.EvalCtx} (τ : THeap) :
    updateCtxTxns (Frame.handleF (.state ℓ s) :: K) τ = Frame.handleF (.state ℓ s) :: updateCtxTxns K τ := by
  simp only [updateCtxTxns]

theorem updateCtxStates_cons_txn {ℓ : Bang.EffectRow.Label} {Θ : List Val} {K : Bang.EvalCtx} (σ : SStore) :
    updateCtxStates (Frame.handleF (.transaction ℓ Θ) :: K) σ
      = Frame.handleF (.transaction ℓ Θ) :: updateCtxStates K σ := by simp only [updateCtxStates]

/-- A non-frame (letF/appF/throws) head is transparent to BOTH passes. -/
theorem ctxNetEffect_cons_nonframe {fr : Bang.Frame} {K : Bang.EvalCtx} (σ : SStore) (τ : THeap)
    (hns : ∀ ℓ s, fr ≠ Frame.handleF (.state ℓ s)) (hnt : ∀ ℓ Θ, fr ≠ Frame.handleF (.transaction ℓ Θ)) :
    ctxNetEffect (fr :: K) σ τ = fr :: ctxNetEffect K σ τ := by
  unfold ctxNetEffect
  cases fr with
  | handleF h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt ℓ Θ)
      | throws ℓ => simp only [updateCtxStates, updateCtxTxns]
  | letF N => simp only [updateCtxStates, updateCtxTxns]
  | appF v => simp only [updateCtxStates, updateCtxTxns]

/-- The reconstruction: a context `K'` agreeing on state (`CtxCorr σ'`) and txn (`CtxTxnCorr τ'`)
projections IS `ctxNetEffect K σ' τ'` when `K'` is `K` net-updated. We use the structural form via
`updateCtx*_self`. Combined identity under both corrs. -/
theorem ctxNetEffect_self {σ : SStore} {τ : THeap} {K : Bang.EvalCtx}
    (hC : CtxCorr σ K) (hT : CtxTxnCorr τ K) : ctxNetEffect K σ τ = K := by
  unfold ctxNetEffect CtxCorr CtxTxnCorr at *; subst hC; subst hT
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF h =>
        cases h with
        | state ℓ s =>
            simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns_cons_state]; rw [ih]
        | throws ℓ => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]
        | transaction ℓ Θ =>
            simp only [ctxStates, ctxTxns, updateCtxStates_cons_txn, updateCtxTxns]; rw [ih]
    | letF N => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]
    | appF v => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]

/-- A non-txn frame carries no heap entry ⇒ `CtxTxnCorr` passes through its install. -/
theorem CtxTxnCorr_cons_nontxn {τ : THeap} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hnt : ∀ ℓ Θ, fr ≠ Frame.handleF (.transaction ℓ Θ)) (hT : CtxTxnCorr τ K) :
    CtxTxnCorr τ (fr :: K) := by
  unfold CtxTxnCorr at hT ⊢; rw [hT]
  cases fr with
  | handleF h =>
      cases h with
      | transaction ℓ Θ => exact absurd rfl (hnt ℓ Θ)
      | state ℓ s => simp only [ctxTxns]
      | throws ℓ => simp only [ctxTxns]
  | letF N => simp only [ctxTxns]
  | appF v => simp only [ctxTxns]

/-- `updateCtxStates` preserves the state/txn FRAME STRUCTURE, so it commutes through `updateCtxTxns`'s
view; and both are idempotent in the K-slot. We need only: `ctxNetEffect (ctxNetEffect K σ1 τ1) σ τ =
ctxNetEffect K σ τ`. Proved by frame-structure induction. -/
theorem ctxNetEffect_ctxNetEffect : ∀ (K : Bang.EvalCtx) (σ1 : SStore) (τ1 : THeap) (σ : SStore) (τ : THeap),
    ctxNetEffect (ctxNetEffect K σ1 τ1) σ τ = ctxNetEffect K σ τ := by
  have key : ∀ (K : Bang.EvalCtx) (σ1 : SStore) (τ1 : THeap) (σ : SStore) (τ : THeap),
      updateCtxTxns (updateCtxStates (updateCtxTxns (updateCtxStates K σ1) τ1) σ) τ
        = updateCtxTxns (updateCtxStates K σ) τ := by
    intro K
    induction K with
    | nil => intro σ1 τ1 σ τ; rfl
    | cons fr K ih =>
      intro σ1 τ1 σ τ
      cases fr with
      | handleF h =>
          cases h with
          | state ℓ s =>
              cases σ1 with
              | nil =>
                  simp only [updateCtxStates, updateCtxTxns_cons_state]
                  cases σ with
                  | nil => simp only [updateCtxStates, updateCtxTxns_cons_state, ih]
                  | cons p σ' => simp only [updateCtxStates, updateCtxTxns_cons_state, ih]
              | cons p1 σ1' =>
                  simp only [updateCtxStates, updateCtxTxns_cons_state]
                  cases σ with
                  | nil => simp only [updateCtxStates, updateCtxTxns_cons_state, ih]
                  | cons p σ' => simp only [updateCtxStates, updateCtxTxns_cons_state, ih]
          | throws ℓ => simp only [updateCtxStates, updateCtxTxns, ih]
          | transaction ℓ Θ =>
              cases τ1 with
              | nil =>
                  simp only [updateCtxStates_cons_txn, updateCtxTxns]
                  cases τ with
                  | nil => simp only [updateCtxStates_cons_txn, updateCtxTxns, ih]
                  | cons p τ' => simp only [updateCtxStates_cons_txn, updateCtxTxns, ih]
              | cons p1 τ1' =>
                  simp only [updateCtxStates_cons_txn, updateCtxTxns]
                  cases τ with
                  | nil => simp only [updateCtxStates_cons_txn, updateCtxTxns, ih]
                  | cons p τ' => simp only [updateCtxStates_cons_txn, updateCtxTxns, ih]
      | letF N => simp only [updateCtxStates, updateCtxTxns, ih]
      | appF v => simp only [updateCtxStates, updateCtxTxns, ih]
  intro K σ1 τ1 σ τ; unfold ctxNetEffect; exact key K σ1 τ1 σ τ

/-- After a non-frame install, `CtxCorr` over `ctxNetEffect (fr::K)` passes to `ctxNetEffect K`. -/
theorem CtxCorr_ctxNetEffect_nonframe {σ' : SStore} {τ' : THeap} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ ℓ s, fr ≠ Frame.handleF (.state ℓ s)) (hnt : ∀ ℓ Θ, fr ≠ Frame.handleF (.transaction ℓ Θ))
    (hC : CtxCorr σ' (ctxNetEffect (fr :: K) σ' τ')) : CtxCorr σ' (ctxNetEffect K σ' τ') := by
  rw [ctxNetEffect_cons_nonframe σ' τ' hns hnt] at hC
  unfold CtxCorr at hC ⊢
  cases fr with
  | handleF h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt ℓ Θ)
      | throws ℓ => simpa only [ctxStates] using hC
  | letF N => simpa only [ctxStates] using hC
  | appF v => simpa only [ctxStates] using hC

/-- After a non-frame install, `CtxTxnCorr` over `ctxNetEffect (fr::K)` passes to `ctxNetEffect K`. -/
theorem CtxTxnCorr_ctxNetEffect_nonframe {σ' : SStore} {τ' : THeap} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ ℓ s, fr ≠ Frame.handleF (.state ℓ s)) (hnt : ∀ ℓ Θ, fr ≠ Frame.handleF (.transaction ℓ Θ))
    (hT : CtxTxnCorr τ' (ctxNetEffect (fr :: K) σ' τ')) : CtxTxnCorr τ' (ctxNetEffect K σ' τ') := by
  rw [ctxNetEffect_cons_nonframe σ' τ' hns hnt] at hT
  unfold CtxTxnCorr at hT ⊢
  cases fr with
  | handleF h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt ℓ Θ)
      | throws ℓ => simpa only [ctxTxns] using hT
  | letF N => simpa only [ctxTxns] using hT
  | appF v => simpa only [ctxTxns] using hT

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

/-- `CtxTxnCorr` preserved by a `handle (transaction ℓ Θ)` install (PUSH `(ℓ↦Θ)` on τ). -/
theorem CtxTxnCorr_install {τ : THeap} {ℓ : Bang.EffectRow.Label} {Θ : List Val} {K : Bang.EvalCtx}
    (hT : CtxTxnCorr τ K) : CtxTxnCorr (τ.push ℓ Θ) (Frame.handleF (.transaction ℓ Θ) :: K) := by
  unfold CtxTxnCorr at hT ⊢; rw [hT]; simp only [ctxTxns, THeap.push]

/-- Combined-pop for a `state` install in the kernel context: pops σ1.tail (state side), τ1 unchanged.
Yields the combined `ctxNetEffect K σ1.tail τ1` correspondence + the at-return context equation. -/
theorem CtxCorr_ctxNetEffect_pop_state {σ1 : SStore} {τ1 : THeap} {ℓ0 : Bang.EffectRow.Label}
    {s0 : Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF (.state ℓ0 s0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF (.state ℓ0 s0) :: K) σ1 τ1)) :
    (CtxCorr σ1.tail (ctxNetEffect K σ1.tail τ1) ∧ CtxTxnCorr τ1 (ctxNetEffect K σ1.tail τ1)) ∧
      ctxNetEffect (Frame.handleF (.state ℓ0 s0) :: K) σ1 τ1
        = Frame.handleF (.state ℓ0 (σ1.headD (default, default)).2) :: ctxNetEffect K σ1.tail τ1 := by
  cases σ1 with
  | nil =>
      exfalso; unfold CtxCorr ctxNetEffect at hC
      simp only [updateCtxStates, updateCtxTxns_cons_state, ctxStates] at hC
      exact (List.cons_ne_nil _ _ hC.symm)
  | cons p σ1' =>
      obtain ⟨ℓa, wa⟩ := p
      have hupd : ctxNetEffect (Frame.handleF (.state ℓ0 s0) :: K) ((ℓa, wa) :: σ1') τ1
          = Frame.handleF (.state ℓ0 wa) :: ctxNetEffect K σ1' τ1 := by
        unfold ctxNetEffect; simp only [updateCtxStates, updateCtxTxns_cons_state]
      rw [hupd] at hC hT
      refine ⟨⟨?_, ?_⟩, by simp only [List.headD, List.tail]; exact hupd⟩
      · unfold CtxCorr at hC ⊢; simp only [ctxStates, List.tail] at hC ⊢
        exact (List.cons.injEq _ _ _ _).mp hC |>.2
      · unfold CtxTxnCorr at hT ⊢; simp only [List.tail]; simpa only [ctxTxns] using hT

/-- Combined-pop for a NON-state (throws/txn) install: σ1/τ adjust per kind; this is the throws case
(non-state, non-txn) — both stores pass through to the tail. -/
theorem CtxCorr_ctxNetEffect_pop_throws {σ1 : SStore} {τ1 : THeap} {ℓ0 : Bang.EffectRow.Label}
    {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF (.throws ℓ0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF (.throws ℓ0) :: K) σ1 τ1)) :
    (CtxCorr σ1 (ctxNetEffect K σ1 τ1) ∧ CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1)) ∧
      ctxNetEffect (Frame.handleF (.throws ℓ0) :: K) σ1 τ1
        = Frame.handleF (.throws ℓ0) :: ctxNetEffect K σ1 τ1 := by
  have hupd : ctxNetEffect (Frame.handleF (.throws ℓ0) :: K) σ1 τ1
      = Frame.handleF (.throws ℓ0) :: ctxNetEffect K σ1 τ1 :=
    ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp)
  rw [hupd] at hC hT
  refine ⟨⟨?_, ?_⟩, hupd⟩
  · unfold CtxCorr at hC ⊢; simpa only [ctxStates] using hC
  · unfold CtxTxnCorr at hT ⊢; simpa only [ctxTxns] using hT

/-- Combined-pop for a `transaction` install: pops τ1.tail (txn side), σ1 unchanged. Free rollback —
the popped heap is discarded with the frame. -/
theorem CtxCorr_ctxNetEffect_pop_txn {σ1 : SStore} {τ1 : THeap} {ℓ0 : Bang.EffectRow.Label}
    {Θ0 : List Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF (.transaction ℓ0 Θ0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF (.transaction ℓ0 Θ0) :: K) σ1 τ1)) :
    (CtxCorr σ1 (ctxNetEffect K σ1 τ1.tail) ∧ CtxTxnCorr τ1.tail (ctxNetEffect K σ1 τ1.tail)) ∧
      ctxNetEffect (Frame.handleF (.transaction ℓ0 Θ0) :: K) σ1 τ1
        = Frame.handleF (.transaction ℓ0 (τ1.headD (default, default)).2) :: ctxNetEffect K σ1 τ1.tail := by
  cases τ1 with
  | nil =>
      exfalso; unfold CtxTxnCorr ctxNetEffect at hT
      simp only [updateCtxStates_cons_txn, updateCtxTxns, ctxTxns] at hT
      exact (List.cons_ne_nil _ _ hT.symm)
  | cons p τ1' =>
      obtain ⟨ℓa, Θa⟩ := p
      have hupd : ctxNetEffect (Frame.handleF (.transaction ℓ0 Θ0) :: K) σ1 ((ℓa, Θa) :: τ1')
          = Frame.handleF (.transaction ℓ0 Θa) :: ctxNetEffect K σ1 τ1' := by
        unfold ctxNetEffect; simp only [updateCtxStates_cons_txn, updateCtxTxns]
      rw [hupd] at hC hT
      refine ⟨⟨?_, ?_⟩, by simp only [List.headD, List.tail]; exact hupd⟩
      · unfold CtxCorr at hC ⊢; simp only [List.tail]; simpa only [ctxStates] using hC
      · unfold CtxTxnCorr at hT ⊢; simp only [ctxTxns, List.tail] at hT ⊢
        exact (List.cons.injEq _ _ _ _).mp hT |>.2

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

/-! ### Transaction kernel-dispatch lemmas (ADR-0031 D4): mirror of the `dispatch_state_*` set. -/

/-- `splitAt` for a txn op on `ℓ` SUCCEEDS at a `transaction ℓ Θ` frame whenever `ℓ` has an active txn
frame (`(ctxTxns K).get? ℓ = some Θ`). Mirror of `splitAt_state_some`. Induction on `K`. -/
theorem splitAt_txn_some {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} (hop : isTxnOp op = true) :
    ∀ {K : Bang.EvalCtx} {Θ : List Val}, (ctxTxns K).get? ℓ = some Θ →
      ∃ Kᵢ Kₒ, Bang.splitAt K ℓ op = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ) := by
  intro K
  induction K with
  | nil => intro Θ hg; simp [ctxTxns, THeap.get?] at hg
  | cons fr K ih =>
    intro Θ hg
    cases fr with
    | handleF h0 =>
        cases h0 with
        | transaction ℓ0 Θ0 =>
            by_cases hc : ℓ0 = ℓ
            · subst hc
              simp only [ctxTxns, THeap.get?, List.find?, decide_true, Option.map_some,
                Option.some.injEq] at hg
              subst hg
              have hcatch : Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ0 op = true := by
                simp only [Bang.handlesOp, beq_self_eq_true, true_and]
                simp only [isTxnOp] at hop; exact hop
              exact ⟨[], K, by simp only [Bang.splitAt, if_pos hcatch]⟩
            · have hg' : (ctxTxns K).get? ℓ = some Θ := by
                simp only [ctxTxns, THeap.get?, List.find?, hc, decide_false,
                  Bool.false_eq_true, if_false] at hg; simpa [THeap.get?] using hg
              obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
              have hnc : ¬ Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ op = true := by
                simp [Bang.handlesOp, hc]
              exact ⟨Frame.handleF (Handler.transaction ℓ0 Θ0) :: Kᵢ, Kₒ, by
                simp only [Bang.splitAt, if_neg hnc, hsp, Option.map_some]⟩
        | state ℓ0 s0 =>
            have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
            obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
            have hnc : ¬ Bang.handlesOp (Handler.state ℓ0 s0) ℓ op = true := by
              rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp [Bang.handlesOp]
            exact ⟨Frame.handleF (Handler.state ℓ0 s0) :: Kᵢ, Kₒ, by
              simp only [Bang.splitAt, if_neg hnc, hsp, Option.map_some]⟩
        | throws ℓ0 =>
            have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
            obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
            have hnc : ¬ Bang.handlesOp (Handler.throws ℓ0) ℓ op = true := by
              rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp [Bang.handlesOp]
            exact ⟨Frame.handleF (Handler.throws ℓ0) :: Kᵢ, Kₒ, by
              simp only [Bang.splitAt, if_neg hnc, hsp, Option.map_some]⟩
    | letF N =>
        have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
        obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
        exact ⟨Frame.letF N :: Kᵢ, Kₒ, by simp only [Bang.splitAt, hsp, Option.map_some]⟩
    | appF w =>
        have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
        obtain ⟨Kᵢ, Kₒ, hsp⟩ := ih hg'
        exact ⟨Frame.appF w :: Kᵢ, Kₒ, by simp only [Bang.splitAt, hsp, Option.map_some]⟩

/-- `updateCtxStates K (ctxStates K) = K` (the `rfl`-CtxCorr corollary of `updateCtxStates_self`). -/
theorem updateCtxStates_self_aux {K : Bang.EvalCtx} : updateCtxStates K (ctxStates K) = K :=
  updateCtxStates_self (rfl : CtxCorr (ctxStates K) K)

/-- `updateCtxTxns K (ctxTxns K) = K` (the txn analog of `updateCtxStates_self`, structural). -/
theorem updateCtxTxns_self_aux : ∀ {K : Bang.EvalCtx}, updateCtxTxns K (ctxTxns K) = K := by
  intro K
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF h =>
        cases h with
        | transaction ℓ Θ => simp only [ctxTxns, updateCtxTxns]; rw [ih]
        | state ℓ s => simp only [ctxTxns, updateCtxTxns]; rw [ih]
        | throws ℓ => simp only [ctxTxns, updateCtxTxns]; rw [ih]
    | letF N => simp only [ctxTxns, updateCtxTxns]; rw [ih]
    | appF v => simp only [ctxTxns, updateCtxTxns]; rw [ih]

/-- A txn dispatch reinstalls the serviced heap: `splitAt K ℓ op = (Kᵢ, transaction ℓ Θ, Kₒ)` ⇒
`updateCtxTxns K ((ctxTxns K).put ℓ Θ') = Kᵢ ++ handleF (transaction ℓ Θ') :: Kₒ`. Mirror of
`updateCtxStates_put_split`. Induction on `K`. -/
theorem updateCtxTxns_service_split {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {Θ' : List Val}
    (hop : isTxnOp op = true) :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {Θ : List Val},
      Bang.splitAt K ℓ op = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ) →
        updateCtxTxns K ((ctxTxns K).put ℓ Θ') = Kᵢ ++ Frame.handleF (Handler.transaction ℓ Θ') :: Kₒ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ Θ hsp; simp [Bang.splitAt] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ Θ hsp
    cases fr with
    | handleF h0 =>
        cases h0 with
        | transaction ℓ0 Θ0 =>
            by_cases hc : ℓ0 = ℓ
            · subst hc
              have hco : Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ0 op = true := by
                simp only [Bang.handlesOp, beq_self_eq_true, true_and]
                rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp
              simp only [Bang.splitAt, if_pos hco, Option.some.injEq, Prod.mk.injEq] at hsp
              obtain ⟨rfl, hh, rfl⟩ := hsp
              simp only [Handler.transaction.injEq] at hh; obtain ⟨_, rfl⟩ := hh
              simp only [ctxTxns, THeap.put, if_true, updateCtxTxns, List.nil_append]
              rw [updateCtxTxns_self_aux]
            · have hnc : ¬ Bang.handlesOp (Handler.transaction ℓ0 Θ0) ℓ op = true := by
                simp [Bang.handlesOp, hc]
              simp only [Bang.splitAt, if_neg hnc] at hsp
              cases hsp2 : Bang.splitAt K ℓ op with
              | none => rw [hsp2] at hsp; simp at hsp
              | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                          obtain ⟨rfl, rfl, rfl⟩ := hsp
                          simp only [ctxTxns, THeap.put, hc, if_false, updateCtxTxns, List.cons_append]
                          rw [ih hsp2]
        | state ℓ0 s0 =>
            have hnc : ¬ Bang.handlesOp (Handler.state ℓ0 s0) ℓ op = true := by
              rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp [Bang.handlesOp]
            simp only [Bang.splitAt, if_neg hnc] at hsp
            cases hsp2 : Bang.splitAt K ℓ op with
            | none => rw [hsp2] at hsp; simp at hsp
            | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                        obtain ⟨rfl, rfl, rfl⟩ := hsp
                        simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]
        | throws ℓ0 =>
            have hnc : ¬ Bang.handlesOp (Handler.throws ℓ0) ℓ op = true := by
              rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp [Bang.handlesOp]
            simp only [Bang.splitAt, if_neg hnc] at hsp
            cases hsp2 : Bang.splitAt K ℓ op with
            | none => rw [hsp2] at hsp; simp at hsp
            | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                        obtain ⟨rfl, rfl, rfl⟩ := hsp
                        simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]
    | letF N =>
        simp only [Bang.splitAt] at hsp
        cases hsp2 : Bang.splitAt K ℓ op with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := hsp
                    simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]
    | appF w0 =>
        simp only [Bang.splitAt] at hsp
        cases hsp2 : Bang.splitAt K ℓ op with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := hsp
                    simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]

/-- A txn dispatch RESUMES with the heap serviced: finds `transaction ℓ Θ`, services via `txnService`,
reinstalls `transaction ℓ Θ'`, resumes `(updateCtxTxns K ((ctxTxns K).put ℓ Θ'), .ret r)`. The kernel
`dispatchOn` transaction arm, packaged against the EvalCtx projection. Mirror of `dispatch_state_put`. -/
theorem dispatch_txn_service {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val} {K : Bang.EvalCtx}
    {Θ : List Val} (hop : isTxnOp op = true) (hg : (ctxTxns K).get? ℓ = some Θ) :
    Bang.dispatch K ℓ op v
      = some (updateCtxTxns K ((ctxTxns K).put ℓ (txnService op v Θ).2), .ret (txnService op v Θ).1) := by
  obtain ⟨Kᵢ, Kₒ, hsp⟩ := splitAt_txn_some hop hg
  rw [updateCtxTxns_service_split hop hsp]
  -- unfold the kernel dispatchOn transaction arm and match txnService's (r, Θ').
  rcases isTxnOp_iff.mp hop with rfl | rfl | rfl
  · -- newTVar: (vint Θ.length, Θ ++ [v])
    simp only [Bang.dispatch, hsp, Option.bind_some, Bang.dispatchOn, txnService,
      beq_self_eq_true, if_true, if_pos rfl]
  · -- readTVar: (Θ.getD i (vint 0), Θ)
    simp only [Bang.dispatch, hsp, Option.bind_some, Bang.dispatchOn, txnService,
      (by decide : ("readTVar" == "newTVar") = false), beq_self_eq_true, Bool.false_eq_true,
      if_false, if_true, if_neg (by decide : ¬ ("readTVar" = "newTVar")), if_pos rfl]
  · -- writeTVar: (vunit, storeSet Θ i w) on a pair payload; vunit/Θ otherwise
    simp only [Bang.dispatch, hsp, Option.bind_some, Bang.dispatchOn, txnService,
      (by decide : ("writeTVar" == "newTVar") = false), (by decide : ("writeTVar" == "readTVar") = false),
      Bool.false_eq_true, if_false, if_neg (by decide : ¬ ("writeTVar" = "newTVar")),
      if_neg (by decide : ¬ ("writeTVar" = "readTVar"))]
    cases v with
    | pair iv w => simp
    | _ => simp

/-- A txn service leaves the STATE projection unchanged (a txn frame carries no state value). The
cross-projection-stability fact on the kernel side — used to thread `CtxCorr` through a txn resume. -/
theorem ctxStates_updateCtxTxns : ∀ (K : Bang.EvalCtx) (τ : THeap),
    ctxStates (updateCtxTxns K τ) = ctxStates K := by
  intro K
  induction K with
  | nil => intro τ; rfl
  | cons fr K ih =>
    intro τ
    cases fr with
    | handleF h =>
        cases h with
        | transaction ℓ Θ =>
            cases τ with
            | nil => simp only [updateCtxTxns, ctxStates]; exact ih []
            | cons p τ' => simp only [updateCtxTxns, ctxStates]; exact ih τ'
        | state ℓ s => simp only [updateCtxTxns, ctxStates]; rw [ih τ]
        | throws ℓ => simp only [updateCtxTxns, ctxStates]; exact ih τ
    | letF N => simp only [updateCtxTxns, ctxStates]; exact ih τ
    | appF v => simp only [updateCtxTxns, ctxStates]; exact ih τ

/-- After a txn service, the resume context's `ctxTxns` IS the put-updated heap-store: `ctxTxns
(updateCtxTxns K (τ.put ℓ Θ')) = τ.put ℓ Θ'` where τ = ctxTxns K. The `CtxTxnCorr`-preservation of a
txn resume. Mirror of `ctxStates_updateCtxStates_put`. Induction on `K`. -/
theorem ctxTxns_updateCtxTxns_service {ℓ : Bang.EffectRow.Label} {Θ' : List Val} :
    ∀ {K : Bang.EvalCtx} {Θ : List Val}, (ctxTxns K).get? ℓ = some Θ →
      ctxTxns (updateCtxTxns K ((ctxTxns K).put ℓ Θ')) = (ctxTxns K).put ℓ Θ' := by
  intro K
  induction K with
  | nil => intro Θ hg; simp [ctxTxns, THeap.get?] at hg
  | cons fr K ih =>
    intro Θ hg
    cases fr with
    | handleF h0 =>
        cases h0 with
        | transaction ℓ0 Θ0 =>
            by_cases hc : ℓ0 = ℓ
            · subst hc
              simp only [ctxTxns, THeap.put, if_true, updateCtxTxns]
              rw [updateCtxTxns_self_aux]
            · have hg' : (ctxTxns K).get? ℓ = some Θ := by
                simp only [ctxTxns, THeap.get?, List.find?, hc, decide_false,
                  Bool.false_eq_true, if_false] at hg; simpa [THeap.get?] using hg
              simp only [ctxTxns, THeap.put, hc, if_false, updateCtxTxns]; rw [ih hg']
        | state ℓ0 s0 =>
            have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
            simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
        | throws ℓ0 =>
            have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
            simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
    | letF N =>
        have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
        simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
    | appF v0 =>
        have hg' : (ctxTxns K).get? ℓ = some Θ := by simpa only [ctxTxns] using hg
        simp only [ctxTxns, updateCtxTxns]; rw [ih hg']

/-- A state service leaves the TXN projection unchanged (the mirror of `ctxStates_updateCtxTxns`). -/
theorem ctxTxns_updateCtxStates : ∀ (K : Bang.EvalCtx) (σ : SStore),
    ctxTxns (updateCtxStates K σ) = ctxTxns K := by
  intro K
  induction K with
  | nil => intro σ; rfl
  | cons fr K ih =>
    intro σ
    cases fr with
    | handleF h =>
        cases h with
        | state ℓ s =>
            cases σ with
            | nil => simp only [updateCtxStates, ctxTxns]; exact ih []
            | cons p σ' => simp only [updateCtxStates, ctxTxns]; exact ih σ'
        | transaction ℓ Θ => simp only [updateCtxStates, ctxTxns]; rw [ih σ]
        | throws ℓ => simp only [updateCtxStates, ctxTxns]; exact ih σ
    | letF N => simp only [updateCtxStates, ctxTxns]; exact ih σ
    | appF v => simp only [updateCtxStates, ctxTxns]; exact ih σ

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
    (∀ M σ τ t σ' τ', evalD fe σ τ M = some (.term t, σ', τ') →
      ∀ (K : Bang.EvalCtx), CtxCorr σ K → CtxTxnCorr τ K →
        (CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ')) ∧
        ∀ (n : Nat) (r : Bang.Result Val),
          Bang.Config.run n (ctxNetEffect K σ' τ', t) = r → ∃ F, Bang.Config.run F (K, M) = r)
    ∧ (∀ M σ τ ℓ v σ' τ', evalD fe σ τ M = some (.raised ℓ "raise" v, σ', τ') →
      ∀ (K : Bang.EvalCtx), CtxCorr σ K → CtxTxnCorr τ K →
        (CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ')) ∧
        ∀ (n : Nat) (r : Bang.Result Val),
          dispatchRun n (ctxNetEffect K σ' τ') ℓ "raise" v = r → ∃ F, Bang.Config.run F (K, M) = r) := by
  intro fe
  induction fe with
  | zero => exact ⟨fun M σ τ t σ' τ' h => by simp [evalD] at h,
                   fun M σ τ ℓ v σ' τ' h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M σ τ t σ' τ' h K hCtx hTtx
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
          rw [ctxNetEffect_self hCtx hTtx]
          exact ⟨⟨hCtx, hTtx⟩, fun n r hr => ⟨n, hr⟩⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
          rw [ctxNetEffect_self hCtx hTtx]
          exact ⟨⟨hCtx, hTtx⟩, fun n r hr => ⟨n, hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.ret v), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTletF : CtxTxnCorr τ (Frame.letF N :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M σ τ (.ret v) σ1 τ1 hM (Frame.letF N :: K) hCletF hTletF
                have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                  CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCM
                have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTM
                obtain ⟨⟨hCf, hTf⟩, kN⟩ := ihT (Comp.subst v N) σ1 τ1 t σ' τ' h (ctxNetEffect K σ1 τ1) hCM' hTM'
                rw [ctxNetEffect_ctxNetEffect] at hCf hTf
                refine ⟨⟨hCf, hTf⟩, fun n r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kN n r (by rw [ctxNetEffect_ctxNetEffect]; exact hr)
                have hstep : Bang.Config.run (F2+1) (Frame.letF N :: ctxNetEffect K σ1 τ1, .ret v) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                rw [← ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp)] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.lam a), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _, _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hCf, kf⟩ := ihT M σ τ t σ' τ' h K hCtx hTtx
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
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.lam N), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                have hCappF : CtxCorr σ (Frame.appF v :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTappF : CtxTxnCorr τ (Frame.appF v :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M σ τ (.lam N) σ1 τ1 hM (Frame.appF v :: K) hCappF hTappF
                have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                  CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCM
                have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTM
                obtain ⟨⟨hCf, hTf⟩, kN⟩ := ihT (Comp.subst v N) σ1 τ1 t σ' τ' h (ctxNetEffect K σ1 τ1) hCM' hTM'
                rw [ctxNetEffect_ctxNetEffect] at hCf hTf
                refine ⟨⟨hCf, hTf⟩, fun n r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kN n r (by rw [ctxNetEffect_ctxNetEffect]; exact hr)
                have hstep : Bang.Config.run (F2+1) (Frame.appF v :: ctxNetEffect K σ1 τ1, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                rw [← ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp)] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.ret w), _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
            | (.raised ℓ op w, _, _), h => simp [Option.bind] at h
      | perform _ ℓ2 op2 v2 =>
          -- OP-FIRST (mirrors evalD's up-arm + the kernel's handlesOp): get/put→σ, txnops→τ, else raise.
          simp only [evalD] at h
          by_cases hop : op2 = "get"
          · subst hop
            simp only [if_pos rfl] at h
            cases hg : σ.get? ℓ2 with
            | none => rw [hg] at h; simp at h
            | some sv =>
                rw [hg] at h
                simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                rw [ctxNetEffect_self hCtx hTtx]
                refine ⟨⟨hCtx, hTtx⟩, fun n r hr => ?_⟩
                have hgc : (ctxStates K).get? ℓ2 = some sv := by rw [← hCtx]; exact hg
                refine ⟨n+1, ?_⟩
                simp only [Bang.Config.run, Source.step, dispatch_state_get hgc]; exact hr
          · by_cases hop2 : op2 = "put"
            · subst hop2
              simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl] at h
              cases hg : σ.get? ℓ2 with
              | none => rw [hg] at h; simp at h
              | some sv =>
                  rw [hg] at h
                  simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  -- σ = ctxStates K; the put-resume context mirrors the put-updated store. τ unchanged
                  -- (state put doesn't touch txn frames), so ctxNetEffect threads it through.
                  have hgc : (ctxStates K).get? ℓ2 = some sv := by rw [← hCtx]; exact hg
                  subst hCtx; subst hTtx
                  -- `ctxNetEffect K ((ctxStates K).put ℓ2 v2) (ctxTxns K)`: the state pass produces the
                  -- put-resume context; the txn pass is the identity (its store mirrors K's txn frames,
                  -- whose projection state-put leaves fixed).
                  have hC' : ctxStates (ctxNetEffect K ((ctxStates K).put ℓ2 v2) (ctxTxns K))
                      = (ctxStates K).put ℓ2 v2 := by
                    unfold ctxNetEffect; rw [ctxStates_updateCtxTxns]
                    exact ctxStates_updateCtxStates_put hgc
                  have hT' : ctxTxns (ctxNetEffect K ((ctxStates K).put ℓ2 v2) (ctxTxns K)) = ctxTxns K := by
                    unfold ctxNetEffect
                    rw [show ctxTxns K = ctxTxns (updateCtxStates K ((ctxStates K).put ℓ2 v2)) from
                      (ctxTxns_updateCtxStates K _).symm, updateCtxTxns_self_aux,
                      ctxTxns_updateCtxStates]
                  refine ⟨⟨hC'.symm, hT'.symm⟩, fun n r hr => ?_⟩
                  refine ⟨n+1, ?_⟩
                  -- the kernel put-resume runs on `updateCtxStates K (put)`; `ctxNetEffect` agrees because
                  -- the txn pass is the identity on K's txn projection (state put untouched it).
                  have hctxeq : ctxNetEffect K ((ctxStates K).put ℓ2 v2) (ctxTxns K)
                      = updateCtxStates K ((ctxStates K).put ℓ2 v2) := by
                    unfold ctxNetEffect
                    rw [show ctxTxns K = ctxTxns (updateCtxStates K ((ctxStates K).put ℓ2 v2)) from
                      (ctxTxns_updateCtxStates K _).symm, updateCtxTxns_self_aux]
                  rw [hctxeq] at hr
                  simp only [Bang.Config.run, Source.step, dispatch_state_put (w := v2) hgc]; exact hr
            · by_cases hopt : isTxnOp op2 = true
              · -- txn op: serviced against τ via the kernel's dispatchOn transaction arm (`dispatch_txn_service`).
                simp only [if_neg hop, if_neg hop2, hopt, if_true] at h
                cases hgt : τ.get? ℓ2 with
                | none => rw [hgt] at h; simp at h
                | some Θ =>
                    rw [hgt] at h
                    simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    subst hCtx; subst hTtx
                    have hgt' : (ctxTxns K).get? ℓ2 = some Θ := hgt
                    -- σ unchanged; τ threaded to (ctxTxns K).put ℓ2 Θ'. The resume context is the kernel's
                    -- txn-service context, which ctxNetEffect reproduces (state pass identity, txn pass = put).
                    have hC' : ctxStates (ctxNetEffect K (ctxStates K) ((ctxTxns K).put ℓ2 (txnService op2 v2 Θ).2))
                        = ctxStates K := by
                      unfold ctxNetEffect; rw [ctxStates_updateCtxTxns, updateCtxStates_self_aux]
                    have hT' : ctxTxns (ctxNetEffect K (ctxStates K) ((ctxTxns K).put ℓ2 (txnService op2 v2 Θ).2))
                        = (ctxTxns K).put ℓ2 (txnService op2 v2 Θ).2 := by
                      unfold ctxNetEffect
                      rw [show updateCtxStates K (ctxStates K) = K from updateCtxStates_self_aux]
                      exact ctxTxns_updateCtxTxns_service hgt'
                    refine ⟨⟨hC'.symm, hT'.symm⟩, fun n r hr => ?_⟩
                    refine ⟨n+1, ?_⟩
                    have hctxeq : ctxNetEffect K (ctxStates K) ((ctxTxns K).put ℓ2 (txnService op2 v2 Θ).2)
                        = updateCtxTxns K ((ctxTxns K).put ℓ2 (txnService op2 v2 Θ).2) := by
                      unfold ctxNetEffect; rw [updateCtxStates_self_aux]
                    rw [hctxeq] at hr
                    simp only [Bang.Config.run, Source.step, dispatch_txn_service hopt hgt']; exact hr
              · rw [Bool.not_eq_true] at hopt
                simp only [if_neg hop, if_neg hop2, hopt, if_false, Option.some.injEq, Prod.mk.injEq,
                  reduceCtorEq, false_and] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                    have hCins : CtxCorr (σ.push ℓ0 s0) (Frame.handleF (.state ℓ0 s0) :: K) :=
                      CtxCorr_install hCtx
                    have hTins : CtxTxnCorr τ (Frame.handleF (.state ℓ0 s0) :: K) :=
                      CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                    obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M (σ.push ℓ0 s0) τ (.ret v) σ1 τ1 hM
                      (Frame.handleF (.state ℓ0 s0) :: K) hCins hTins
                    obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_state hCM hTM
                    refine ⟨hpop, fun n r hr => ?_⟩
                    have hstep : Bang.Config.run (n+1)
                        (ctxNetEffect (Frame.handleF (.state ℓ0 s0) :: K) σ1 τ1, .ret v) = r := by
                      rw [hupd]; simp only [Bang.Config.run, Source.step]; exact hr
                    obtain ⟨F1, hF1⟩ := kM (n+1) r hstep
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                    have hCins : CtxCorr σ (Frame.handleF (.throws ℓ0) :: K) :=
                      CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                    have hTins : CtxTxnCorr τ (Frame.handleF (.throws ℓ0) :: K) :=
                      CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                    obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M σ τ (.ret v) σ1 τ1 hM (Frame.handleF (.throws ℓ0) :: K) hCins hTins
                    obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_throws hCM hTM
                    refine ⟨hpop, fun n r hr => ?_⟩
                    have hstep : Bang.Config.run (n+1)
                        (ctxNetEffect (Frame.handleF (.throws ℓ0) :: K) σ1 τ1, .ret v) = r := by
                      rw [hupd]; simp only [Bang.Config.run, Source.step]; exact hr
                    obtain ⟨F1, hF1⟩ := kM (n+1) r hstep
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp only [if_pos hk, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                      obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                      obtain ⟨rfl, rfl⟩ := hk
                      have hCins : CtxCorr σ (Frame.handleF (.throws ℓ0) :: K) :=
                        CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                      have hTins : CtxTxnCorr τ (Frame.handleF (.throws ℓ0) :: K) :=
                        CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                      obtain ⟨⟨hCM, hTM⟩, kR⟩ := ihR M σ τ ℓ0 w σ1 τ1 hM (Frame.handleF (.throws ℓ0) :: K) hCins hTins
                      obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_throws hCM hTM
                      refine ⟨hpop, fun n r hr => ?_⟩
                      have hd : dispatchRun n
                          (Frame.handleF (.throws ℓ0) :: ctxNetEffect K σ1 τ1) ℓ0 "raise" w = r := by
                        simp only [dispatchRun, Bang.Config.run, Source.step, Bang.dispatch,
                          Bang.splitAt, Bang.handlesOp, beq_self_eq_true, Bool.and_true, decide_true,
                          if_true, Option.bind_some, Bang.dispatchOn]
                        simpa using hr
                      rw [← hupd] at hd
                      obtain ⟨F1, hF1⟩ := kR n r hd
                      exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                    · simp [if_neg hk] at h
          | transaction ℓ0 Θ =>
              simp only at h
              cases hM : evalD fe σ (τ.push ℓ0 Θ) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
                    have hCins : CtxCorr σ (Frame.handleF (.transaction ℓ0 Θ) :: K) :=
                      CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                    have hTins : CtxTxnCorr (τ.push ℓ0 Θ) (Frame.handleF (.transaction ℓ0 Θ) :: K) :=
                      CtxTxnCorr_install hTtx
                    obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M σ (τ.push ℓ0 Θ) (.ret v) σ1 τ1 hM
                      (Frame.handleF (.transaction ℓ0 Θ) :: K) hCins hTins
                    obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_txn hCM hTM
                    refine ⟨hpop, fun n r hr => ?_⟩
                    have hstep : Bang.Config.run (n+1)
                        (ctxNetEffect (Frame.handleF (.transaction ℓ0 Θ) :: K) σ1 τ1, .ret v) = r := by
                      rw [hupd]; simp only [Bang.Config.run, Source.step]; exact hr
                    obtain ⟨F1, hF1⟩ := kM (n+1) r hstep
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
      | case a b d =>
          -- ADT sum elim (Unit 6): the kernel `Source.step` reduces in place (Operational.lean 260-261).
          -- Mirror `force`: recurse via `ihT` on the reduced branch, then one `Source.step` bridges.
          cases a with
          | inl v =>
              simp only [evalD] at h
              obtain ⟨hCf, kf⟩ := ihT (Comp.subst v b) σ τ t σ' τ' h K hCtx hTtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kf n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | inr v =>
              simp only [evalD] at h
              obtain ⟨hCf, kf⟩ := ihT (Comp.subst v d) σ τ t σ' τ' h K hCtx hTtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kf n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | split a b =>
          -- ADT product elim (Unit 6): DOUBLE subst (Operational.lean 262).
          cases a with
          | pair v w =>
              simp only [evalD] at h
              obtain ⟨hCf, kf⟩ := ihT (Comp.subst v (Comp.subst (Val.shift w) b)) σ τ t σ' τ' h K hCtx hTtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kf n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | fold w => simp [evalD] at h
      | unfold a =>
          -- ADT μ elim (Unit 6): erases to `ret v` (Operational.lean 263). Terminal — no IH; bridge the
          -- one `Source.step` (fold/unfold) over the `ret`-terminal close, stores unchanged.
          cases a with
          | fold v =>
              simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
              obtain ⟨ht, hσ, hτ⟩ := h; subst ht; subst hσ; subst hτ
              rw [ctxNetEffect_self hCtx hTtx]
              exact ⟨⟨hCtx, hTtx⟩, fun n r hr => ⟨n+1, by simp only [Bang.Config.run, Source.step]; exact hr⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
    · -- RAISED PART
      intro M σ τ ℓ v σ' τ' h K hCtx hTtx
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | perform _ ℓ2 op2 v2 =>
          -- OP-FIRST: the obligation fixes op = "raise", which is NOT get/put/txnop ⇒ evalD's up-arm
          -- falls to the final `raised ℓ2 "raise" v2` branch unconditionally; σ/τ unchanged.
          simp only [evalD] at h
          by_cases hop : op2 = "get"
          · subst hop; simp only [if_pos rfl] at h
            cases hg : σ.get? ℓ2 with
            | none => rw [hg] at h; simp at h
            | some sv => rw [hg] at h; simp at h
          · by_cases hop2 : op2 = "put"
            · subst hop2; simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl] at h
              cases hg : σ.get? ℓ2 with
              | none => rw [hg] at h; simp at h
              | some sv => rw [hg] at h; simp at h
            · by_cases hopt : isTxnOp op2 = true
              · simp only [if_neg hop, if_neg hop2, hopt, if_true] at h
                cases hgt : τ.get? ℓ2 with
                | none =>
                    rw [hgt] at h
                    simp only [Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                    obtain ⟨⟨_, hopeq, _⟩, _, _⟩ := h
                    subst hopeq; simp [isTxnOp] at hopt
                | some Θ => rw [hgt] at h; simp at h
              · rw [Bool.not_eq_true] at hopt
                simp only [if_neg hop, if_neg hop2, hopt, if_false, Option.some.injEq, Prod.mk.injEq,
                  Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                rw [ctxNetEffect_self hCtx hTtx]
                refine ⟨⟨hCtx, hTtx⟩, fun n r hr => ⟨n+1, ?_⟩⟩
                rw [dispatchRun_perform]; exact hr
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1, τ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTletF : CtxTxnCorr τ (Frame.letF N :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                obtain ⟨⟨hCM, hTM⟩, kR⟩ := ihR M σ τ ℓ' w σ1 τ1 hM (Frame.letF N :: K) hCletF hTletF
                refine ⟨⟨CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCM,
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTM⟩,
                  fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by
                  rw [ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp),
                    dispatchRun_letF]; exact hr)
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.ret v0), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTletF : CtxTxnCorr τ (Frame.letF N :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M σ τ (.ret v0) σ1 τ1 hM (Frame.letF N :: K) hCletF hTletF
                have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                  CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCM
                have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTM
                obtain ⟨⟨hCf, hTf⟩, kR⟩ := ihR (Comp.subst v0 N) σ1 τ1 ℓ v σ' τ' h (ctxNetEffect K σ1 τ1) hCM' hTM'
                rw [ctxNetEffect_ctxNetEffect] at hCf hTf
                refine ⟨⟨hCf, hTf⟩, fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by rw [ctxNetEffect_ctxNetEffect]; exact hr)
                have hstep : Bang.Config.run (F1+1) (Frame.letF N :: ctxNetEffect K σ1 τ1, .ret v0) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF1
                rw [← ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp)] at hstep
                obtain ⟨F2, hF2⟩ := kM (F1+1) r hstep
                exact ⟨F2+1, by simp only [Bang.Config.run, Source.step]; exact hF2⟩
            | (.term (.lam a), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hCf, kR⟩ := ihR M σ τ ℓ v σ' τ' h K hCtx hTtx
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
          cases hM : evalD fe σ τ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, σ1, τ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                have hCappF : CtxCorr σ (Frame.appF v0 :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTappF : CtxTxnCorr τ (Frame.appF v0 :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                obtain ⟨⟨hCM, hTM⟩, kR⟩ := ihR M σ τ ℓ' w σ1 τ1 hM (Frame.appF v0 :: K) hCappF hTappF
                refine ⟨⟨CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCM,
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTM⟩,
                  fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by
                  rw [ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp),
                    dispatchRun_appF]; exact hr)
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.lam N), σ1, τ1), h =>
                simp only [Option.bind_some] at h
                have hCappF : CtxCorr σ (Frame.appF v0 :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTappF : CtxTxnCorr τ (Frame.appF v0 :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                obtain ⟨⟨hCM, hTM⟩, kM⟩ := ihT M σ τ (.lam N) σ1 τ1 hM (Frame.appF v0 :: K) hCappF hTappF
                have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                  CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCM
                have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTM
                obtain ⟨⟨hCf, hTf⟩, kR⟩ := ihR (Comp.subst v0 N) σ1 τ1 ℓ v σ' τ' h (ctxNetEffect K σ1 τ1) hCM' hTM'
                rw [ctxNetEffect_ctxNetEffect] at hCf hTf
                refine ⟨⟨hCf, hTf⟩, fun n r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR n r (by rw [ctxNetEffect_ctxNetEffect]; exact hr)
                have hstep : Bang.Config.run (F1+1) (Frame.appF v0 :: ctxNetEffect K σ1 τ1, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF1
                rw [← ctxNetEffect_cons_nonframe σ1 τ1 (by intro ℓ s; simp) (by intro ℓ Θ; simp)] at hstep
                obtain ⟨F2, hF2⟩ := kM (F1+1) r hstep
                exact ⟨F2+1, by simp only [Bang.Config.run, Source.step]; exact hF2⟩
            | (.term (.ret w), _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _), h => simp [Option.bind] at h
            | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | state ℓ0 s0 =>
              simp only at h
              cases hM : evalD fe (σ.push ℓ0 s0) τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    -- evalD forwards `raised ℓ' op' w (σ1.tail, τ1)` (pops the pushed σ entry).
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                    have hCins : CtxCorr (σ.push ℓ0 s0) (Frame.handleF (.state ℓ0 s0) :: K) :=
                      CtxCorr_install hCtx
                    have hTins : CtxTxnCorr τ (Frame.handleF (.state ℓ0 s0) :: K) :=
                      CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                    obtain ⟨⟨hCM, hTM⟩, kR⟩ := ihR M (σ.push ℓ0 s0) τ ℓ' w σ1 τ1 hM
                      (Frame.handleF (.state ℓ0 s0) :: K) hCins hTins
                    obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_state hCM hTM
                    refine ⟨hpop, fun n r hr => ?_⟩
                    have hnc : Bang.handlesOp (Handler.state ℓ0 (σ1.headD (default, default)).2) ℓ' "raise"
                        = false := by simp [Bang.handlesOp]
                    have hd : dispatchRun n (ctxNetEffect (Frame.handleF (.state ℓ0 s0) :: K) σ1 τ1)
                        ℓ' "raise" w = r := by
                      rw [hupd, dispatchRun_handleF_skip n _ _ ℓ' w hnc]; exact hr
                    obtain ⟨F1, hF1⟩ := kR n r hd
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.ret v0), _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
          | throws ℓ0 =>
              simp only at h
              cases hM : evalD fe σ τ M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ0 = ℓ' ∧ op' = "raise"
                    · simp [if_pos hk] at h   -- caught ⇒ term, but h says raised: absurd
                    · simp only [if_neg hk, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                      have hne : ℓ0 ≠ ℓ' := fun he => hk ⟨he, rfl⟩
                      have hnc : Bang.handlesOp (Handler.throws ℓ0) ℓ' "raise" = false := by
                        simp [Bang.handlesOp, hne]
                      have hCins : CtxCorr σ (Frame.handleF (.throws ℓ0) :: K) :=
                        CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                      have hTins : CtxTxnCorr τ (Frame.handleF (.throws ℓ0) :: K) :=
                        CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                      obtain ⟨⟨hCM, hTM⟩, kR⟩ := ihR M σ τ ℓ' w σ1 τ1 hM (Frame.handleF (.throws ℓ0) :: K) hCins hTins
                      obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_throws hCM hTM
                      refine ⟨hpop, fun n r hr => ?_⟩
                      obtain ⟨F1, hF1⟩ := kR n r (by
                        rw [hupd, dispatchRun_handleF_skip n (Handler.throws ℓ0) _ ℓ' w hnc]; exact hr)
                      exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.ret v0), _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
          | transaction ℓ0 Θ =>
              simp only at h
              cases hM : evalD fe σ (τ.push ℓ0 Θ) M with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, σ1, τ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    -- raise FORWARDS past the txn frame (ℓ' ≠ ℓ0 or op' = raise on a different label);
                    -- evalD pops the pushed heap (τ1.tail) — FREE ROLLBACK (the heap never commits).
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
                    have hnc : Bang.handlesOp (Handler.transaction ℓ0 (τ1.headD (default, default)).2) ℓ' "raise" = false := by
                      simp [Bang.handlesOp]
                    have hCins : CtxCorr σ (Frame.handleF (.transaction ℓ0 Θ) :: K) :=
                      CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                    have hTins : CtxTxnCorr (τ.push ℓ0 Θ) (Frame.handleF (.transaction ℓ0 Θ) :: K) :=
                      CtxTxnCorr_install hTtx
                    obtain ⟨⟨hCM, hTM⟩, kR⟩ := ihR M σ (τ.push ℓ0 Θ) ℓ' w σ1 τ1 hM
                      (Frame.handleF (.transaction ℓ0 Θ) :: K) hCins hTins
                    obtain ⟨hpop, hupd⟩ := CtxCorr_ctxNetEffect_pop_txn hCM hTM
                    refine ⟨hpop, fun n r hr => ?_⟩
                    obtain ⟨F1, hF1⟩ := kR n r (by
                      rw [hupd, dispatchRun_handleF_skip n _ _ ℓ' w hnc]
                      exact hr)
                    exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
                | (.term (.ret v0), _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _), h => simp [Option.bind] at h
                | (.term (.perform _ a b d), _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _), h => simp [Option.bind] at h
      | case a b d =>
          -- ADT sum elim (Unit 6) raising: branch raises; recurse via `ihR`, bridge one `Source.step`.
          cases a with
          | inl sv =>
              simp only [evalD] at h
              obtain ⟨hCf, kR⟩ := ihR (Comp.subst sv b) σ τ ℓ v σ' τ' h K hCtx hTtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kR n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | inr sv =>
              simp only [evalD] at h
              obtain ⟨hCf, kR⟩ := ihR (Comp.subst sv d) σ τ ℓ v σ' τ' h K hCtx hTtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kR n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | split a b =>
          -- ADT product elim (Unit 6) raising: DOUBLE subst, then the branch raises.
          cases a with
          | pair sv sw =>
              simp only [evalD] at h
              obtain ⟨hCf, kR⟩ := ihR (Comp.subst sv (Comp.subst (Val.shift sw) b)) σ τ ℓ v σ' τ' h K hCtx hTtx
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kR n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | fold w => simp [evalD] at h
      | unfold a =>
          -- ADT μ elim (Unit 6): always `term (ret v)` — never `raised`, vacuous here.
          cases a with
          | fold v => simp [evalD] at h
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h

/-- **The D1-A bridge** (headline): when `evalD` says a closed computation returns
`v`, the kernel's verified `Source.eval` agrees (`.done v`). Ties the calculated
machine to the type-safety reference (invariant #1) — `Source.eval`'s `type_safety`
now backs `evalD`'s `ret`-results. Pure spine; handlers/ADT elim later. -/
theorem evalD_agrees_source (f : Nat) (M : Comp) (v : Val) (σ' : SStore) (τ' : THeap)
    (h : evalD f [] [] M = some (.term (.ret v), σ', τ')) :
    ∃ F, Source.eval F M = Result.done v := by
  -- the empty stores mirror the empty kernel context (`CtxCorr [] []`/`CtxTxnCorr [] []` by `rfl`); a
  -- closed program has no resumptive frames ⇒ `ctxNetEffect [] σ' τ' = []`, continuation at `([], ret v)`.
  obtain ⟨_, k⟩ := (run_evalD f).1 M [] [] (.ret v) σ' τ' h [] rfl rfl
  have hbase : Config.run 1 (ctxNetEffect [] σ' τ', .ret v) = Result.done v := by
    simp only [ctxNetEffect, updateCtxStates, updateCtxTxns, Config.run]
  obtain ⟨F, hF⟩ := k 1 (Result.done v) hbase
  exact ⟨F, hF⟩

/-- `handle`-install over a non-raising body: `handle (throws ℓ) (ret 7)` ⇒ `7`
(handler-return = identity — `MARK`/`UNMARK` are identity on a normal return). A distinct
shape from the battery's *catching* throws cases; the full three-rep bridge witnessed at once. -/
example :
    let M := Comp.handle (.throws 0) (.ret (.vint 7))
    evalD 5 [] [] M = some (.term (.ret (.vint 7)), [], []) ∧ Agree 10 M (.vint 7) := by
  refine ⟨by rfl, by rfl, by rfl⟩

end Bang.CalcVM
