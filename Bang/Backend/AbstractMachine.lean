module

public import Bang.Core.Semantics
public import Bang.Core.CapCoh

/-!
# AbstractMachine — the ◊3 graded-CBPV calculated machine (pure CBPV spine)

INVARIANT #4 (pinned here): this is the **CALCULATED machine (Bahr–Hutton) — an
OUTPUT of the derivation, NOT hand-designed**. The `(compile, Code, exec)` triple is
*derived* from `evalD` by equational reasoning; we never hand-design the VM and then
justify a compiler against it. `compile_correct` is the calculation's discharge.

NOTE (Phase-2 rename seam): the FILE/module is `Bang.AbstractMachine`, but the
`namespace` stays `Bang.CalcVM` — the four gated headlines (`compile_correct`,
`evalD_agrees_source`, `sim`, `run_evalD`) keep their `Bang.CalcVM.*` qualified names
so the Audit census stays byte-identical (the rename is module-only by design).

The Bahr–Hutton calculation (ADR-0016, ADR-0017; invariant #4) ported ONCE to
the new graded-CBPV `Comp`/`Val` (`Bang.IR`), replacing the K2 `Calc*.lean`
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
open Bang.CapCoh (WeakCoh CapLabelCoh capLabelCoh_step capLabelCoh_initial capLabelCoh_perform_label)
open Bang.Model (FreshCfg freshCfg_step)

-- Module reveal (Phase 1a). `@[expose] public section`: CalcVM's machine defs (compile/exec/
-- evalD/Code) and bridge lemmas are unfolded by downstream Compile + the Audit headlines
-- (compile_correct/evalD_agrees_source/sim/run_evalD), so bodies cross the boundary.
@[expose] public section

/-! ## The state store (ADR-0031 D1): a 1:1 mirror of the active `state ℓ s` frames

`SStore` is the resumptive mechanism `evalD` threads (ADR-0031 D1). It is a **stack** of
`(label ↦ value)` bindings that mirrors the machine's active `state ℓ s` frames **1:1, in order**
(D3): `handle (state ℓ s) M` PUSHES `(ℓ, s)` for the dynamic extent of `M` and POPS it on exit;
`get` reads the nearest binding for `ℓ`; `put` UPDATES the nearest binding **in place** (NOT a
prepend — this exactly mirrors the machine's in-place `stateUpdate` on the HStack, so the store and
the HStack-state-projection stay structurally identical, which is what makes the bridge invariant a
direct correspondence rather than a representation translation). `∉ store` ⟺ no active `state`
frame for `ℓ` ⟹ the op propagates as a throws-path `raised`. -/
/-- The state store `evalD` threads (ADR-0031): a stack of `(label ↦ value)` bindings
mirroring the machine's active `state ℓ s` frames 1:1, in order. -/
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
/-- The transaction heap store `evalD` threads (ADR-0031): `SStore` generalized from a
single cell to a list-heap, mirroring the machine's active `transaction ℓ Θ` frames. -/
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

/-! ## The custom store (ADR-0085 #44 Stage 4): the user-defined-effect analog of `SStore`/`THeap`

`CStore` is the resumptive mechanism `evalD` threads for **custom** (`Handler.custom`) frames — the
third **per-kind** store, a structural sibling of `SStore` (state) and `THeap` (transaction) under the
KIND-FIRST-STORES idiom (route-B, build-arbitrated): stores are per-handler-kind, matching `evalD`'s
per-kind dispatch — skip a non-matching kind, then check id. A custom frame carries a `(param, clauses)`
payload, so the cell type is `Val × List (ClauseKey × Comp)` (vs `SStore`'s `Val` and `THeap`'s `List Val`).

`handle (custom ℓ p cls) M` PUSHES `(id ↦ (p, cls))` for the dynamic extent of `M` and POPS on exit;
a `perform (vcap n ℓ) op v` at a live custom frame `n` looks up the frame's clauses, finds the op's
clause, and INLINE-SERVICES it. Plain clauses run `subst p (subst (shift v) clause.2)` against the
live store. ADR-0114 updating clauses instead consume a direct `(resumeValue, nextParam)` envelope
and replace the matching store cell before resumption.

**INVARIANT (op-disjointness — same load-bearing argument as `THeap`).** This is a SEPARATE parallel
store, NOT a unified one, because custom ops (a user `effect` decl's fresh op names) are op-disjoint
from the built-in op sets `{get,put}` / `{newTVar,readTVar,writeTVar}`. A label shared across kinds
resolves unambiguously by op-id; the three projections never cross.

**DEFERRED (per ADR-0085 D3, operator ruling 2026-07-09).** This is a per-kind store (kind-first
idiom). The ADR-0085 D3 SINGLE-param-store generalization (one store subsuming state/txn/custom) is a
DEFERRED census-preserving refactor — the SAME status as the handler-COLLAPSE (ADR-0085 D5, Option-A
instances): a later beautification, not taken mid-derivation on taste (which would invert invariant #4). -/
/-- The custom-effect store `evalD` threads (ADR-0085): keyed by handler identity to a
`(param, clauses)` payload, mirroring the machine's active `custom ℓ p cls` frames. -/
abbrev CStore := List (Nat × (Val × List (Bang.ClauseKey × Comp)))

/-- The nearest stored `(param, clauses)` for identity `n` (innermost custom frame wins — shadowing;
identities are globally fresh, so at most one matches). -/
def CStore.get? (κ : CStore) (n : Nat) : Option (Val × List (Bang.ClauseKey × Comp)) :=
  (κ.find? (fun p => p.1 = n)).map (·.2)

/-- PUSH a fresh custom binding (a `handle (custom ℓ p cls)` install). -/
def CStore.push (κ : CStore) (n : Nat) (p : Val) (cls : List (Bang.ClauseKey × Comp)) : CStore :=
  (n, (p, cls)) :: κ

/-- Update the private parameter of the custom frame identified by `n`, preserving
its finite clause table (ADR-0114). -/
def CStore.put : CStore → Nat → Val → CStore
  | [], _, _ => []
  | (m, (old, cls)) :: κ, n, next =>
      if m = n then (m, (next, cls)) :: κ else (m, (old, cls)) :: CStore.put κ n next

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
  -- route-B (ADR-0052): a `raised` propagates to its handler by IDENTITY `n` (the capability's
  -- generative name), NOT by label — mirroring the kernel's `idDispatch`. The `handle` whose minted
  -- id equals `n` catches it (throws abort); state/transaction frames forward it.
  | raised : Nat → Bang.OpId → Val → Outcome      -- a throws-`up` en route to handler IDENTITY n
  deriving Inhabited

-- route-B (ADR-0052): `evalD` is the big-step denotation of the IDENTITY kernel. It threads the
-- fresh-id counter `g` (in and out), MINTS+SUBSTITUTES `vcap g h.label` at `handle` (mirroring the
-- kernel's `Source.step` handle-arm, Operational.lean:471), and keys both stores by the capability
-- IDENTITY `n` (not the label). A `perform (vcap n …)` dispatches by `n` (mirroring `idDispatch`/
-- `splitAtId`, :284/374); a `raised n …` propagates to the `handle` whose minted id equals `n`.
-- The store key type is `Nat` (= `Label`), so `SStore`/`THeap`/`CStore` are keyed by the capability
-- IDENTITY; identities are globally fresh (unique), so `get?`/`put` find the unique entry. ADR-0085
-- Stage 4: the THIRD store `κ : CStore` threads custom (`Handler.custom`) frames — a per-kind sibling
-- of σ/τ (kind-first idiom), carrying `(param, clauses)` and INLINE-SERVICING a custom op by running
-- the clause body as a sub-eval against the live frame.
/-- The CalcVM reference (route-B, ADR-0052): the big-step denotation of the identity
kernel, threading the fresh-id counter and the per-kind stores (state/heap/custom) and
dispatching by capability identity. Must agree with `Source.eval`. -/
def evalD : Nat → Nat → SStore → THeap → CStore → Comp → Option (Outcome × Nat × SStore × THeap × CStore)
  | 0,          _, _, _, _, _      => none
  | Nat.succ _, g, σ, τ, κ, .ret v    => some (.term (.ret v), g, σ, τ, κ)
  | Nat.succ _, g, σ, τ, κ, .lam M    => some (.term (.lam M), g, σ, τ, κ)
  | Nat.succ f, g, σ, τ, κ, .letC M N =>
      (evalD f g σ τ κ M).bind (fun p => match p with
        | (.term (.ret v), g', σ', τ', κ') => evalD f g' σ' τ' κ' (Comp.subst v N) -- M : F _ ⇒ terminal `ret v`
        | (.term _, _, _, _, _)            => none                              -- ill-typed (letC of a lam)
        | (.raised n op w, g', σ', τ', κ') => some (.raised n op w, g', σ', τ', κ')) -- propagate the raise
  | Nat.succ f, g, σ, τ, κ, .force (.vthunk M) => evalD f g σ τ κ M   -- force∘thunk = run the closed body
  | Nat.succ f, g, σ, τ, κ, .app M v  =>
      (evalD f g σ τ κ M).bind (fun p => match p with
        | (.term (.lam N), g', σ', τ', κ') => evalD f g' σ' τ' κ' (Comp.subst v N) -- β: M ⇒ lam N, then N[v]
        | (.term _, _, _, _, _)            => none                              -- ill-typed (app of a non-lam)
        | (.raised n op w, g', σ', τ', κ') => some (.raised n op w, g', σ', τ', κ')) -- propagate the raise
  -- perform (vcap n ℓ) op v: dispatch BY IDENTITY n (route-B, id-first). The IDENTITY n — NOT the op
  -- name — picks the arm: whichever per-kind store HOLDS n services the op. The three stores are
  -- DISJOINT by generative freshness (each `handle` mints a globally-fresh g and pushes onto EXACTLY
  -- ONE of σ/τ/κ — the store image of the kernel's single-stack `splitAtId`), so n lives in at most
  -- one. This mirrors the kernel `idDispatch` (Dispatch.lean): `splitAtId K n` resolves the frame by
  -- identity, THEN `handlesOp h ℓ op` is a FAIL-LOUD op-legality guard — the op only selects the
  -- operation WITHIN the resolved frame's kind, and an op the resolved kind does not handle RAISES
  -- (never falls through to another store / another kind). The op name NEVER disambiguates the store
  -- (operator ruling 2026-07-09, issue #62): a custom frame keyed with a built-in-like name "get" IS
  -- serviced by its clause; a built-in `get` reaches the state store only because its cap's identity
  -- lives there. No frame for n (n in no store) ⇒ raise. Order of the store checks is irrelevant to
  -- the result (disjointness); the σ→τ→κ order matches the store-declaration order.
  | Nat.succ f, g, σ, τ, κ, .perform (.vcap n _ℓ) op v   =>
      match σ.get? n with
      -- n resolves to a STATE frame (handlesOp image: state handles get/put on ℓ; any other op raises).
      | some s =>
          if op = "get" then some (.term (.ret s), g, σ, τ, κ)               -- get: return stored s, σ unchanged
          else if op = "put" then some (.term (.ret .vunit), g, σ.put n v, τ, κ) -- put: thread s := v at key n
          else some (.raised n op v, g, σ, τ, κ)                             -- op the state frame can't handle ⇒ raise (fail-loud)
      | none =>
      match τ.get? n with
      -- n resolves to a TRANSACTION frame (handlesOp image: txn handles the three stm ops; else raises).
      | some Θ =>
          if isTxnOp op then
            -- serviced against the heap: thread Θ := Θ' in place (mirrors the machine's txnUpdate).
            let (r, Θ') := txnService op v Θ
            some (.term (.ret r), g, σ, τ.put n Θ', κ)
          else some (.raised n op v, g, σ, τ, κ)                             -- op the txn frame can't handle ⇒ raise (fail-loud)
      | none =>
      match κ.get? n with
      -- n resolves to a CUSTOM frame (handlesOp image: custom handles op iff its clause list has it).
      -- INLINE-SERVICE: plain clauses run against the live store; updating clauses atomically install
      -- their explicit next parameter before resumption. No matching clause raises to identity n.
      | some (p, cls) =>
          match cls.find? (fun clause => clause.1.op == op) with
          | some clause =>
              let body := Comp.subst p (Comp.subst (Val.shift v) clause.2)
              if clause.1.updates then
                match body with
                | .ret (.pair resumeValue nextParam) =>
                    some (.term (.ret resumeValue), g, σ, τ, κ.put n nextParam)
                | _ => none
              else
                evalD f g σ τ κ body
          | none        => some (.raised n op v, g, σ, τ, κ)                 -- op unserviced by this custom frame ⇒ raise
      | none => some (.raised n op v, g, σ, τ, κ)                            -- n in no store ⇒ raise / non-resumptive op
  -- handle h M: MINT id := g, SUBSTITUTE `vcap id h.label` for the handle-bound var 0, recurse with g+1.
  --  · state s : push (id ↦ s) on σ for M's extent; POP on exit; a raise FORWARDS (pop entry).
  --  · transaction Θ : the list-heap analog (ADR-0031 D4); push (id ↦ Θ) on τ; POP on exit.
  --  · custom (ℓ p cls) : the user-effect analog (ADR-0085 Stage 4); push (id ↦ (p, cls)) on κ; POP on exit.
  --  · throws : CATCH a `raised n` with n = id ∧ op = "raise" ⇒ yield `term (ret w)` (zero-shot abort,
  --    ADR-0023). The at-raise stores σ'/τ'/κ' are KEPT (outer effects persist; inner frames already popped).
  | Nat.succ f, g, σ, τ, κ, .handle h M  =>
      let id := g
      let M' := Comp.subst (.vcap id h.label) M
      match h with
      | .state _ s =>
          (evalD f (g+1) (σ.push id s) τ κ M').bind (fun p => match p with
            | (.term (.ret v), g', σ', τ', κ') => some (.term (.ret v), g', σ'.tail, τ', κ')  -- POP the pushed id entry
            | (.term _, _, _, _, _)            => none
            | (.raised n op' w, g', σ', τ', κ') => some (.raised n op' w, g', σ'.tail, τ', κ')) -- forward; pop entry
      | .transaction _ Θ =>
          (evalD f (g+1) σ (τ.push id Θ) κ M').bind (fun p => match p with
            | (.term (.ret v), g', σ', τ', κ') => some (.term (.ret v), g', σ', τ'.tail, κ')  -- POP the pushed id heap
            | (.term _, _, _, _, _)            => none
            | (.raised n op' w, g', σ', τ', κ') => some (.raised n op' w, g', σ', τ'.tail, κ')) -- forward; pop heap
      -- custom (ADR-0085 #44 STAGE 4 — DERIVED): the user-effect analog of the state arm. PUSH (id ↦ (p, cls))
      -- on κ for M's extent; POP on exit; a raise FORWARDS (pop entry). Structural sibling of `state`, with the
      -- clause-service happening at the `perform` arm (κ.get? + find? + inline sub-eval), exactly `state`'s
      -- get/put-at-perform shape with USER clause logic in the resume focus (ADR-0085 D3, probe-confirmed).
      | .custom _ p cls =>
          (evalD f (g+1) σ τ (κ.push id p cls) M').bind (fun q => match q with
            | (.term (.ret v), g', σ', τ', κ') => some (.term (.ret v), g', σ', τ', κ'.tail)  -- POP the pushed id entry
            | (.term _, _, _, _, _)            => none
            | (.raised n op' w, g', σ', τ', κ') => some (.raised n op' w, g', σ', τ', κ'.tail)) -- forward; pop entry
      | .throws _ =>
          (evalD f (g+1) σ τ κ M').bind (fun p => match p with
            | (.term (.ret v), g', σ', τ', κ') => some (.term (.ret v), g', σ', τ', κ')
            | (.term _, _, _, _, _)            => none
            | (.raised n op' w, g', σ', τ', κ') =>
                -- CAUGHT (zero-shot abort) iff the raise targets THIS handler's identity. Discard the
                -- captured continuation; KEEP the at-raise stores σ'/τ'/κ' (outer put/writeTVar persists —
                -- inner frames already popped on the way out). Else forward outward.
                if n = id ∧ op' = "raise" then some (.term (.ret w), g', σ', τ', κ')
                else some (.raised n op' w, g', σ', τ', κ'))
  -- ADT eliminators (Unit 6): PURE reductions — closed-value scrutinee, no store/counter change.
  | Nat.succ f, g, σ, τ, κ, .case (.inl v) N₁ _  => evalD f g σ τ κ (Comp.subst v N₁)
  | Nat.succ f, g, σ, τ, κ, .case (.inr v) _  N₂ => evalD f g σ τ κ (Comp.subst v N₂)
  | Nat.succ f, g, σ, τ, κ, .split (.pair v w) N => evalD f g σ τ κ (Comp.subst v (Comp.subst (Val.shift w) N))
  | Nat.succ _, g, σ, τ, κ, .unfold (.fold v)    => some (.term (.ret v), g, σ, τ, κ)
  -- δ-rule (ADR-0065, #40): mirrors `Source.step` (`binop op (vint a) (vint b) ⇒ ret (op.eval a b)`).
  -- PURE — no store/counter change; non-`vint` operands fall to the catch-all (stuck, like Source.step).
  | Nat.succ _, g, σ, τ, κ, .binop op (.vint a) (.vint b) => some (.term (.ret (op.eval a b)), g, σ, τ, κ)
  | _,          _, _, _, _, _      => none                -- out of scope (ill-formed scrutinee)

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

/-- The calculated VM's instruction set (route-B, ADR-0052): the `{RET, LAMI, SUBST,
APP}` core derived from `evalD` plus the handler/dispatch/ADT-eliminator instructions. -/
inductive Instr where
  | RET   : Val → Instr      -- push the terminal `ret v`
  | LAMI  : Comp → Instr     -- push the terminal `lam M`
  | SUBST : Comp → Instr     -- pop `ret v`; compile+run `N[v]` before continuing
  | APP   : Val → Instr      -- pop `lam N`; compile+run `N[v]` before continuing
  -- handler frames (route-B, ADR-0052). `HANDLE h M` DEFERS: it carries the RAW handler + RAW body so
  -- that `exec`, at runtime, mints the fresh identity `g`, pushes the frame keyed by `g`, and RE-COMPILES
  -- `subst (vcap g h.label) M` (the residual-recompile pattern of `SUBST`/`APP`/`CASE`). The body cannot
  -- be pre-compiled because its `perform` caps are unresolved `vvar`s until the mint substitutes them —
  -- the U1 finding. `UNMARK` pops the frame on a normal return (handler-return = identity, Q6). `THROW n
  -- op v` unwinds to the frame with IDENTITY `n`, discarding the inner continuation (zero-shot abort).
  | HANDLE : Handler → Comp → Instr  -- DEFER: exec mints id, pushes the frame, recompiles the subst body
  | UNMARK : Instr
  | THROW  : Nat → Bang.OpId → Val → Instr   -- unwind to handler IDENTITY n (route-B)
  -- OP (route-B): the dispatch instruction, keyed by capability IDENTITY `n`. `compile (perform (vcap n ℓ)
  -- op v) c` emits `OP n op v :: c`; the inner continuation `c` IS Kᵢ and is KEPT for a resume. On
  -- execution: resolve the state/txn frame with id `n` (`stateUpdate`/`txnUpdate`), service IN PLACE,
  -- CONTINUE `c`; if `n` is not a resumptive frame, fall through to the `unwindFind`/abort path.
  | OP     : Nat → Bang.OpId → Val → Instr
  -- ADT eliminators (Unit 6): same residual-`Comp`-in-instruction pattern as `SUBST`/`APP`. `compile`
  -- emits the instruction WITHOUT recursing into the branches (keeping `compile` structural); `exec`
  -- inspects the closed-value scrutinee and re-`compile`s the chosen branch at runtime (fuel-bounded).
  | CASE   : Val → Comp → Comp → Instr  -- sum elim: inl/inr ⇒ compile+run the matching branch[v]
  | SPLIT  : Val → Comp → Instr         -- product elim: pair ⇒ compile+run N[v][shift w] (DOUBLE subst)
  -- (no UNFOLD: `unfold (fold v)` erases to `RET v` at compile time — see `compile`.)
  deriving Inhabited

/-- A compiled program: a list of `Instr`. -/
abbrev Code  := List Instr
/-- The machine stack holds *terminal computations* (`ret v` / `lam M`) — the
shared value representation both `evalD` and `exec` produce, keeping correctness a
plain equality (no logical relation; k2-playbook §2). -/
abbrev Stack := List Comp

/-- A saved handler frame: the minted IDENTITY `id` + the handler + the OUTER continuation
(`Code` × `Stack`) to resume on a zero-shot abort (= the kernel's `Kₒ`). route-B: `id` is the
frame's generative name — `unwindFind`/`stateUpdate`/`txnUpdate` resolve by it (mirroring
`splitAtId`). The inner continuation is DISCARDED on abort (throws are zero-shot), so it is NOT saved. -/
structure HFrame where
  /-- The frame's minted generative identity; dispatch resolves by it. -/
  id         : Nat
  /-- The installed handler. -/
  handler    : Handler
  /-- The outer continuation code to resume on a zero-shot abort (`Kₒ`). -/
  savedCode  : Code
  /-- The outer continuation stack to resume on a zero-shot abort. -/
  savedStack : Stack

/-- The machine's handler stack: a list of saved `HFrame`s. -/
abbrev HStack := List HFrame

/-- Compile a computation into bytecode prepended onto continuation code `c`
(derived from `evalD` by Bahr–Hutton reasoning). -/
def compile : Comp → Code → Code
  | .ret v,             c => Instr.RET v :: c
  | .lam M,             c => Instr.LAMI M :: c
  | .letC M N,          c => compile M (Instr.SUBST N :: c)
  | .force (.vthunk M), c => compile M c
  | .app M v,           c => compile M (Instr.APP v :: c)
  -- route-B: DEFER. The body's caps are unresolved `vvar`s until exec mints the id + substitutes, so
  -- `HANDLE` carries the raw `h`+`M` and exec re-compiles `subst (vcap g h.label) M` (the SUBST/APP pattern).
  | .handle h M,        c => Instr.HANDLE h M :: c
  -- route-B: the cap is RESOLVED here (`vcap n ℓ`) because `compile` runs on the post-mint substituted
  -- body (exec's HANDLE recompile), so `compile` reads the IDENTITY `n` and emits an identity-keyed `OP`.
  | .perform (.vcap n _ℓ) op v,  c => Instr.OP n op v :: c     -- RESUMPTIVE: `c` IS Kᵢ, KEPT; dispatch by identity n
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
  -- δ-rule (#40): binop COLLAPSES onto `RET`, exactly like `unfold (fold v)`. The operands are CLOSED
  -- vints whenever `compile` reaches a binop (the SUBST/APP/HANDLE/CASE residual-recompile discipline
  -- substitutes every enclosing binder first), so `op.eval a b` is computable here — no dedicated
  -- instruction (invariant #4: the calculation collapses a structural terminal-reduction onto RET).
  | .binop op (.vint a) (.vint b), c => Instr.RET (op.eval a b) :: c
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
def unwindFind : Nat → Bang.OpId → HStack → Option (Code × Stack × HStack)
  | _, _, []        => none
  | n, op, fr :: hs =>
      match fr.handler with
      | .throws _ => if fr.id = n ∧ op = "raise" then some (fr.savedCode, fr.savedStack, hs)  -- abort to Kₒ
                     else unwindFind n op hs
      | _         => unwindFind n op hs   -- non-throws frame ⇒ skip (state/txn resume, handled elsewhere)

/-- Find the nearest **state** frame for `ℓ` and service `get`/`put` IN PLACE (ADR-0031 D2,
the resume analog of `unwindFind`). `get` returns the stored `s`, leaving `hs` unchanged; `put`
returns `unit` and UPDATES that frame's stored state to `v` **in `hs`** — the frames ABOVE it
(Kᵢ's handlers) are KEPT (deep handler). Returns `(resultValue, hs')`. `none` = no `state ℓ` frame
(a throws label) ⇒ the caller falls through to `unwindFind`. PURE (no `exec` arg), mirroring the
kernel's `dispatchOn` state arm (KEEP `Kᵢ`, reinstall a deep `state ℓ s'` frame). -/
def stateUpdate : Nat → Bang.OpId → Val → HStack → Option (Val × HStack)
  | _, _, _, []       => none
  | n, op, v, fr :: hs =>
      match fr.handler with
      | .state ℓ0 s =>
          if fr.id = n then
            if op = "get" then some (s, fr :: hs)                                  -- get: return s, frame kept
            else if op = "put" then some (.vunit, { fr with handler := .state ℓ0 v } :: hs)  -- put: store v in place
            else none                                                             -- non-get/put on n ⇒ throws path
          else (stateUpdate n op v hs).map (fun p => (p.1, fr :: p.2))            -- different id ⇒ keep, recurse
      | _ => (stateUpdate n op v hs).map (fun p => (p.1, fr :: p.2))              -- non-state frame ⇒ keep, recurse

/-- Find the nearest **transaction** frame for `ℓ` and service `newTVar`/`readTVar`/`writeTVar` IN
PLACE (ADR-0031 D4, the list-heap analog of `stateUpdate`). Returns `(resultValue, hs')` where `hs'`
has that frame's heap updated to `txnService`'s threaded `Θ'`; the frames ABOVE it (Kᵢ's handlers)
are KEPT (deep handler). `none` = no `transaction ℓ` frame OR a non-txn op on a txn label ⇒ the caller
falls through to `unwindFind` (throws path). Mirrors `dispatchOn`'s transaction arm. -/
def txnUpdate : Nat → Bang.OpId → Val → HStack → Option (Val × HStack)
  | _, _, _, []       => none
  | n, op, v, fr :: hs =>
      match fr.handler with
      | .transaction ℓ0 Θ =>
          if fr.id = n then
            if isTxnOp op then
              let (r, Θ') := txnService op v Θ
              some (r, { fr with handler := .transaction ℓ0 Θ' } :: hs)            -- service: store Θ' in place
            else none                                                             -- non-txn op on n ⇒ throws path
          else (txnUpdate n op v hs).map (fun p => (p.1, fr :: p.2))              -- different id ⇒ keep, recurse
      | _ => (txnUpdate n op v hs).map (fun p => (p.1, fr :: p.2))                -- non-txn frame ⇒ keep, recurse

/-- Find the nearest **custom** frame with identity `n` and inline-service a user op. Plain clauses
return their instantiated body with the live frame unchanged. ADR-0114 updating clauses consume a
direct result/next-parameter pair, return the result body, and replace that frame's parameter.
`none` means no matching custom service, so the caller falls through to the throws path. -/
def customUpdate : Nat → Bang.OpId → Val → HStack → Option (Comp × HStack)
  | _, _, _, []       => none
  | n, op, v, fr :: hs =>
      match fr.handler with
      | .custom _ p cls =>
          if fr.id = n then
            match cls.find? (fun clause => clause.1.op == op) with
            | some clause =>
                let body := Comp.subst p (Comp.subst (Val.shift v) clause.2)
                if clause.1.updates then
                  match body with
                  | .ret (.pair resumeValue nextParam) =>
                      some (.ret resumeValue,
                        { fr with handler := .custom fr.handler.label nextParam cls } :: hs)
                  | _ => some (.wrong "custom update clause must return (result, next param)", fr :: hs)
                else
                  some (body, fr :: hs)
            | none        => none                                                              -- op unserviced ⇒ throws path
          else (customUpdate n op v hs).map (fun q => (q.1, fr :: q.2))          -- different id ⇒ keep, recurse
      | _ => (customUpdate n op v hs).map (fun q => (q.1, fr :: q.2))            -- non-custom frame ⇒ keep, recurse

/-- Is `op` a BUILT-IN op (state get/put or a transaction op)? `evalD`'s perform arm dispatches
OP-PRIORITY — `if get / elif put / elif isTxnOp / else custom` — so a built-in op NEVER reaches the
custom arm. The machine's OP arm mirrors this: it only consults `customUpdate` when `op` is NOT built-in,
so a built-in op that misses its store raises (never accidentally served by a custom clause keyed with a
built-in name). This is the DERIVATION-FAITHFUL guard (invariant #4: the machine falls out of evalD's
control flow), NOT a threaded op-disjointness premise (ADR-0087 §op-priority). -/
def isBuiltinOp (op : Bang.OpId) : Bool := op = "get" || op = "put" || isTxnOp op

/-- `evalD`'s custom perform arm is reached exactly when `op` is not a built-in (`isBuiltinOp op = false`);
this ties the machine guard to evalD's `else`-branch condition. -/
theorem isBuiltinOp_iff {op : Bang.OpId} :
    isBuiltinOp op = false ↔ (op ≠ "get" ∧ op ≠ "put" ∧ isTxnOp op = false) := by
  simp only [isBuiltinOp, Bool.or_eq_false_iff, decide_eq_false_iff_not, and_assoc]

/-! ### Store ↔ HStack correspondence (ADR-0031 D3): the invariant the resume proof rides

`hsState hs ℓ` reads the nearest `state ℓ` frame's stored value out of the machine's
HStack — the machine-side mirror of `evalD`'s `SStore.get?`. `Corr σ hs` is the
bridge invariant: the denotational store agrees with the machine's active state
frames at every label. The two lemmas below relate `stateUpdate` (the machine's
in-place service) to `SStore.get?`/`SStore.put` (the store's), so the `sim` `up`/
`handle (state)` cases close by a direct correspondence (D3), not a representation
translation. -/

/-- The state value of the `state` frame with IDENTITY `n` in `hs` (route-B: machine-side `SStore.get?`,
keyed by identity). KIND-FIRST (mirrors `stateUpdate` + `evalD`'s state-only `σ.get?`): skip non-state
frames, and at a state frame return its value if `id = n`. No id-uniqueness invariant needed. -/
def hsState : HStack → Nat → Option Val
  | [],       _ => none
  | fr :: hs, n =>
      match fr.handler with
      | .state _ s => if fr.id = n then some s else hsState hs n
      | _          => hsState hs n

/-- Project the machine's HStack to the store it mirrors: the `state` frames, in order, as
`(id, s)` entries keyed by IDENTITY (throws/transaction frames carry no state ⇒ skipped). `Corr`
says `evalD`'s threaded store IS exactly this projection. -/
def hsStates : HStack → SStore
  | []        => []
  | fr :: hs  =>
      match fr.handler with
      | .state _ s => (fr.id, s) :: hsStates hs
      | _          => hsStates hs

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

/-- The txn heap of the `transaction` frame with IDENTITY `n` in `hs` (route-B machine-side `THeap.get?`).
KIND-FIRST (mirrors `txnUpdate`): skip non-txn frames, at a txn frame return its heap if `id = n`. -/
def hsTxn : HStack → Nat → Option (List Val)
  | [],       _ => none
  | fr :: hs, n =>
      match fr.handler with
      | .transaction _ Θ => if fr.id = n then some Θ else hsTxn hs n
      | _                => hsTxn hs n

/-- Project the HStack to the txn-heap store it mirrors: the `transaction` frames, in order, as
`(id, Θ)` entries keyed by IDENTITY (state/throws frames carry no heap ⇒ skipped). `TCorr` says
`evalD`'s threaded τ IS this projection. -/
def hsTxns : HStack → THeap
  | []        => []
  | fr :: hs  =>
      match fr.handler with
      | .transaction _ Θ => (fr.id, Θ) :: hsTxns hs
      | _                => hsTxns hs

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

/-! ### Custom ↔ HStack correspondence (ADR-0085 Stage 4): the user-effect analog of the state/txn bridge

`hsCustom`/`hsCustoms`/`updateCustoms`/`CCorr` are the EXACT mirror of `hsState`/`hsStates`/
`updateStates`/`Corr`, projecting `custom ℓ p cls` frames into a `CStore` instead of `state ℓ s`
frames into an `SStore`. A SEPARATE projection (op-disjointness — see `CStore`): the state/txn
projections skip custom frames, the custom projection skips state/txn frames, and no op crosses.
`updateCustoms` mirrors the state/transaction rebuild and overwrites a frame's private parameter
from the final `CStore` while preserving its label and finite clause table. -/

/-- The `(param, clauses)` of the `custom` frame with IDENTITY `n` in `hs` (machine-side `CStore.get?`).
KIND-FIRST (mirrors `customUpdate`): skip non-custom frames, at a custom frame return its payload if
`id = n`. -/
def hsCustom : HStack → Nat → Option (Val × List (Bang.ClauseKey × Comp))
  | [],       _ => none
  | fr :: hs, n =>
      match fr.handler with
      | .custom _ p cls => if fr.id = n then some (p, cls) else hsCustom hs n
      | _               => hsCustom hs n

/-- Project the HStack to the custom store it mirrors: the `custom` frames, in order, as
`(id, (p, cls))` entries keyed by IDENTITY (state/throws/txn frames carry no clause payload ⇒ skipped).
`CCorr` says `evalD`'s threaded κ IS this projection. -/
def hsCustoms : HStack → CStore
  | []        => []
  | fr :: hs  =>
      match fr.handler with
      | .custom _ p cls => (fr.id, (p, cls)) :: hsCustoms hs
      | _               => hsCustoms hs

/-- The bridge invariant (Stage 4), STRUCTURAL form: `evalD`'s threaded κ IS the projection of the
machine's active custom frames. The user-effect analog of `Corr`/`TCorr`. -/
def CCorr (κ : CStore) (hs : HStack) : Prop := κ = hsCustoms hs

/-! ### Store-disjointness (`StoresDisjoint`) — the ID-FIRST dispatch backbone.

Under the ID-FIRST perform arm (operator ruling 2026-07-09, issue #62), the IDENTITY `n` picks WHICH
per-kind store services (`σ.get? n` state → `τ.get? n` txn → `κ.get? n` custom); the op only selects the
operation within the resolved frame. For `evalD`↔machine agreement this REQUIRES that `n` resolves in at
most one store — else a perform whose op mismatches the first-resolved kind RAISES in `evalD` (fail-loud,
the `handlesOp` image) but the machine, walking PAST the mismatched frame via `stateUpdate`/`txnUpdate`/
`customUpdate`, could find a same-id shadow of another kind and RESUME (a real divergence, not a proof
gap). This disjointness is TRUE of every reachable configuration by generative freshness: each `handle`
mints a globally-fresh id and pushes onto exactly one store. It is the store-level image of the kernel's
`StratFresh`; the discharge is `storesDisjoint_of_freshCfg` (bundling the `ctxStates/ctxTxns/ctxCustoms
_get_none_of_capsBelow` triple), threaded from `FreshCfg` at the `sim` call site in `run_evalD`. -/
/-- No identity is bound in more than one of the three per-kind stores — the
id-first dispatch backbone (a key resolves to at most one store). -/
def StoresDisjoint (σ : SStore) (τ : THeap) (κ : CStore) : Prop :=
  ∀ n, (σ.get? n ≠ none → τ.get? n = none ∧ κ.get? n = none)
     ∧ (τ.get? n ≠ none → σ.get? n = none ∧ κ.get? n = none)
     ∧ (κ.get? n ≠ none → σ.get? n = none ∧ τ.get? n = none)

/-- Every stored key across all three per-kind stores is `< g` (the fresh-id counter). This is the
**machine-store twin of the kernel's `WellCounted`** (team-lead ruling 2026-07-09): the counter-bound
freshness invariant. It is a CORRESPONDENCE-SIDE bridge invariant (`Corr`/`StratFresh`/`WellCounted`
lineage — "uniqueness lives in the bridge via StratFresh/WellCounted"), NOT the rejected `WfCustomOps`
program premise. It is what makes `StoresDisjoint` PUSH-STABLE: a `handle` mints key `g` (≥ every existing
key ⇒ fresh ⇒ distinct from the other stores) then bumps `g→g+1`. **`StoresDisjoint` is never inductive
on its own under minting — the counter-bound is** (a disjointness fact isn't preserved by push without
knowing the pushed key is fresh); so the two ride together and `StoresBelow` supplies the freshness.
Both are TRIVIALLY true at the empty-store `compile_correct` entry, `StoresDisjoint` is DERIVED at the
fail-loud perform arms, and both stay INSIDE `sim` — the public headline `compile_forward_sim` remains
VcapFree-only. The `sim`-side (exec-direction, self-contained, entered at empty stores) analog of the
K-side `ctx*_get_none_of_ctx*_some` corollary; routing from `run_evalD`'s `FreshCfg` would INVERT the
dependency (`run_evalD` consumes `sim`). -/
def StoresBelow (g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) : Prop :=
  (∀ n, σ.get? n ≠ none → n < g) ∧ (∀ n, τ.get? n ≠ none → n < g) ∧ (∀ n, κ.get? n ≠ none → n < g)

/-! ### `StoresBelow`/`StoresDisjoint` preservation (push/put closure of the bridge invariant, (B')). -/

-- push = cons on the assoc list ⇒ `get? m` sees the new key `g` OR the original.
theorem SStore.get?_push_ne_none {σ : SStore} {g m : Nat} {v : Val} :
    (σ.push g v).get? m ≠ none ↔ (m = g ∨ σ.get? m ≠ none) := by
  simp only [SStore.push, SStore.get?, List.find?]
  by_cases hc : g = m
  · subst hc; simp
  · have hc' : ¬ (m = g) := fun he => hc he.symm
    simp only [hc, decide_false, Bool.false_eq_true, if_false, hc', false_or]
theorem THeap.get?_push_ne_none {τ : THeap} {g m : Nat} {Θ : List Val} :
    (τ.push g Θ).get? m ≠ none ↔ (m = g ∨ τ.get? m ≠ none) := by
  simp only [THeap.push, THeap.get?, List.find?]
  by_cases hc : g = m
  · subst hc; simp
  · have hc' : ¬ (m = g) := fun he => hc he.symm
    simp only [hc, decide_false, Bool.false_eq_true, if_false, hc', false_or]
theorem CStore.get?_push_ne_none {κ : CStore} {g m : Nat} {p : Val} {cls : List (Bang.ClauseKey × Comp)} :
    (κ.push g p cls).get? m ≠ none ↔ (m = g ∨ κ.get? m ≠ none) := by
  simp only [CStore.push, CStore.get?, List.find?]
  by_cases hc : g = m
  · subst hc; simp
  · have hc' : ¬ (m = g) := fun he => hc he.symm
    simp only [hc, decide_false, Bool.false_eq_true, if_false, hc', false_or]

-- `SStore.put` keeps the key SET (`= none` iff it was `= none`) — `put` never adds/removes a key,
-- only rewrites a present one. Single induction on σ (each cons: replace-head keeps the key, else recurse).
theorem SStore.put_get?_eq_none : ∀ (σ : SStore) {ℓ m : Bang.EffectRow.Label} {v : Val},
    ((σ.put ℓ v).get? m = none ↔ σ.get? m = none) := by
  intro σ
  induction σ with
  | nil => intro ℓ m v; rfl
  | cons p σ ih =>
    obtain ⟨ℓ0, w⟩ := p
    intro ℓ m v
    simp only [SStore.put]
    by_cases hlv : ℓ0 = ℓ
    · -- head replaced (ℓ0,w)→(ℓ0,v); `get? m` on both = check `ℓ0 = m` then recurse identically.
      simp only [if_pos hlv]
      by_cases hm : ℓ0 = m
      · simp [SStore.get?, List.find?, hm]
      · simp only [SStore.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]
    · simp only [if_neg hlv]
      by_cases hm : ℓ0 = m
      · simp [SStore.get?, List.find?, hm]
      · simp only [SStore.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]; exact ih
theorem THeap.put_get?_eq_none : ∀ (τ : THeap) {ℓ m : Bang.EffectRow.Label} {Θ : List Val},
    ((τ.put ℓ Θ).get? m = none ↔ τ.get? m = none) := by
  intro τ
  induction τ with
  | nil => intro ℓ m Θ; rfl
  | cons p τ ih =>
    obtain ⟨ℓ0, w⟩ := p
    intro ℓ m Θ
    simp only [THeap.put]
    by_cases hlv : ℓ0 = ℓ
    · simp only [if_pos hlv]
      by_cases hm : ℓ0 = m
      · simp [THeap.get?, List.find?, hm]
      · simp only [THeap.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]
    · simp only [if_neg hlv]
      by_cases hm : ℓ0 = m
      · simp [THeap.get?, List.find?, hm]
      · simp only [THeap.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]; exact ih
theorem CStore.put_get?_eq_none : ∀ (κ : CStore) {n m : Nat} {next : Val},
    ((κ.put n next).get? m = none ↔ κ.get? m = none) := by
  intro κ
  induction κ with
  | nil => intro n m next; rfl
  | cons entry κ ih =>
      obtain ⟨n0, payload⟩ := entry; obtain ⟨p, cls⟩ := payload
      intro n m next
      simp only [CStore.put]
      by_cases hn : n0 = n
      · simp only [if_pos hn]
        by_cases hm : n0 = m
        · simp [CStore.get?, List.find?, hm]
        · simp only [CStore.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]
      · simp only [if_neg hn]
        by_cases hm : n0 = m
        · simp [CStore.get?, List.find?, hm]
        · simp only [CStore.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]; exact ih

-- push `= none`: `m ≠ g` AND missed before.
private theorem sstore_push_eq_none {σ : SStore} {g m : Nat} {v : Val}
    (hne : m ≠ g) (h0 : σ.get? m = none) : (σ.push g v).get? m = none := by
  by_contra hc; rcases SStore.get?_push_ne_none.mp hc with rfl | hin; exacts [hne rfl, hin h0]
private theorem theap_push_eq_none {τ : THeap} {g m : Nat} {Θ : List Val}
    (hne : m ≠ g) (h0 : τ.get? m = none) : (τ.push g Θ).get? m = none := by
  by_contra hc; rcases THeap.get?_push_ne_none.mp hc with rfl | hin; exacts [hne rfl, hin h0]
private theorem cstore_push_eq_none {κ : CStore} {g m : Nat} {p : Val} {cls : List (Bang.ClauseKey × Comp)}
    (hne : m ≠ g) (h0 : κ.get? m = none) : (κ.push g p cls).get? m = none := by
  by_contra hc; rcases CStore.get?_push_ne_none.mp hc with rfl | hin; exacts [hne rfl, hin h0]

theorem StoresBelow.put_state {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {n : Nat} {v : Val}
    (h : StoresBelow g σ τ κ) : StoresBelow g (σ.put n v) τ κ :=
  ⟨fun m hm => h.1 m (fun heq => hm ((SStore.put_get?_eq_none σ).mpr heq)), h.2.1, h.2.2⟩
theorem StoresBelow.put_txn {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {n : Nat} {Θ : List Val}
    (h : StoresBelow g σ τ κ) : StoresBelow g σ (τ.put n Θ) κ :=
  ⟨h.1, fun m hm => h.2.1 m (fun heq => hm ((THeap.put_get?_eq_none τ).mpr heq)), h.2.2⟩
theorem StoresBelow.put_custom {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {n : Nat} {next : Val}
    (h : StoresBelow g σ τ κ) : StoresBelow g σ τ (κ.put n next) :=
  ⟨h.1, h.2.1, fun m hm => h.2.2 m (fun heq => hm ((CStore.put_get?_eq_none κ).mpr heq))⟩
theorem StoresBelow.push_state {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {s : Val}
    (h : StoresBelow g σ τ κ) : StoresBelow (g+1) (σ.push g s) τ κ := by
  refine ⟨fun m hm => ?_, fun m hm => Nat.lt_succ_of_lt (h.2.1 m hm), fun m hm => Nat.lt_succ_of_lt (h.2.2 m hm)⟩
  rcases SStore.get?_push_ne_none.mp hm with heq | hin
  · subst heq; exact Nat.lt_succ_self m
  · exact Nat.lt_succ_of_lt (h.1 m hin)
theorem StoresBelow.push_txn {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {Θ : List Val}
    (h : StoresBelow g σ τ κ) : StoresBelow (g+1) σ (τ.push g Θ) κ := by
  refine ⟨fun m hm => Nat.lt_succ_of_lt (h.1 m hm), fun m hm => ?_, fun m hm => Nat.lt_succ_of_lt (h.2.2 m hm)⟩
  rcases THeap.get?_push_ne_none.mp hm with heq | hin
  · subst heq; exact Nat.lt_succ_self m
  · exact Nat.lt_succ_of_lt (h.2.1 m hin)
theorem StoresBelow.push_custom {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {p : Val}
    {cls : List (Bang.ClauseKey × Comp)} (h : StoresBelow g σ τ κ) : StoresBelow (g+1) σ τ (κ.push g p cls) :=
  ⟨fun m hm => Nat.lt_succ_of_lt (h.1 m hm), fun m hm => Nat.lt_succ_of_lt (h.2.1 m hm),
   fun m hm => by rcases CStore.get?_push_ne_none.mp hm with rfl | hin
                  exacts [by omega, Nat.lt_succ_of_lt (h.2.2 m hin)]⟩

theorem StoresDisjoint.put_state {σ : SStore} {τ : THeap} {κ : CStore} {n : Nat} {v : Val}
    (h : StoresDisjoint σ τ κ) : StoresDisjoint (σ.put n v) τ κ := by
  intro m
  have keyb : (σ.put n v).get? m ≠ none → σ.get? m ≠ none :=
    fun hne heq => hne ((SStore.put_get?_eq_none σ).mpr heq)
  exact ⟨fun hne => (h m).1 (keyb hne),
    fun hne => ⟨(SStore.put_get?_eq_none σ).mpr ((h m).2.1 hne).1, ((h m).2.1 hne).2⟩,
    fun hne => ⟨(SStore.put_get?_eq_none σ).mpr ((h m).2.2 hne).1, ((h m).2.2 hne).2⟩⟩
theorem StoresDisjoint.put_txn {σ : SStore} {τ : THeap} {κ : CStore} {n : Nat} {Θ : List Val}
    (h : StoresDisjoint σ τ κ) : StoresDisjoint σ (τ.put n Θ) κ := by
  intro m
  have keyb : (τ.put n Θ).get? m ≠ none → τ.get? m ≠ none :=
    fun hne heq => hne ((THeap.put_get?_eq_none τ).mpr heq)
  exact ⟨fun hne => ⟨(THeap.put_get?_eq_none τ).mpr ((h m).1 hne).1, ((h m).1 hne).2⟩,
    fun hne => (h m).2.1 (keyb hne),
    fun hne => ⟨((h m).2.2 hne).1, (THeap.put_get?_eq_none τ).mpr ((h m).2.2 hne).2⟩⟩
theorem StoresDisjoint.put_custom {σ : SStore} {τ : THeap} {κ : CStore} {n : Nat} {next : Val}
    (h : StoresDisjoint σ τ κ) : StoresDisjoint σ τ (κ.put n next) := by
  intro m
  have keyb : (κ.put n next).get? m ≠ none → κ.get? m ≠ none :=
    fun hne heq => hne ((CStore.put_get?_eq_none κ).mpr heq)
  exact ⟨fun hne => ⟨((h m).1 hne).1, (CStore.put_get?_eq_none κ).mpr ((h m).1 hne).2⟩,
    fun hne => ⟨((h m).2.1 hne).1, (CStore.put_get?_eq_none κ).mpr ((h m).2.1 hne).2⟩,
    fun hne => (h m).2.2 (keyb hne)⟩
theorem StoresDisjoint.push_state {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {s : Val}
    (hd : StoresDisjoint σ τ κ) (hb : StoresBelow g σ τ κ) : StoresDisjoint (σ.push g s) τ κ := by
  intro m
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_⟩
  · rcases SStore.get?_push_ne_none.mp hne with rfl | hin
    · exact ⟨by by_contra hc; exact Nat.lt_irrefl _ (hb.2.1 m hc),
             by by_contra hc; exact Nat.lt_irrefl _ (hb.2.2 m hc)⟩
    · exact (hd m).1 hin
  · have hmg : m ≠ g := Nat.ne_of_lt (hb.2.1 m hne)
    exact ⟨sstore_push_eq_none hmg ((hd m).2.1 hne).1, ((hd m).2.1 hne).2⟩
  · have hmg : m ≠ g := Nat.ne_of_lt (hb.2.2 m hne)
    exact ⟨sstore_push_eq_none hmg ((hd m).2.2 hne).1, ((hd m).2.2 hne).2⟩
theorem StoresDisjoint.push_txn {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {Θ : List Val}
    (hd : StoresDisjoint σ τ κ) (hb : StoresBelow g σ τ κ) : StoresDisjoint σ (τ.push g Θ) κ := by
  intro m
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_⟩
  · have hmg : m ≠ g := Nat.ne_of_lt (hb.1 m hne)
    exact ⟨theap_push_eq_none hmg ((hd m).1 hne).1, ((hd m).1 hne).2⟩
  · rcases THeap.get?_push_ne_none.mp hne with rfl | hin
    · exact ⟨by by_contra hc; exact Nat.lt_irrefl _ (hb.1 m hc),
             by by_contra hc; exact Nat.lt_irrefl _ (hb.2.2 m hc)⟩
    · exact (hd m).2.1 hin
  · have hmg : m ≠ g := Nat.ne_of_lt (hb.2.2 m hne)
    exact ⟨((hd m).2.2 hne).1, theap_push_eq_none hmg ((hd m).2.2 hne).2⟩
theorem StoresDisjoint.push_custom {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {p : Val}
    {cls : List (Bang.ClauseKey × Comp)} (hd : StoresDisjoint σ τ κ) (hb : StoresBelow g σ τ κ) :
    StoresDisjoint σ τ (κ.push g p cls) := by
  intro m
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_⟩
  · have hmg : m ≠ g := Nat.ne_of_lt (hb.1 m hne)
    exact ⟨((hd m).1 hne).1, cstore_push_eq_none hmg ((hd m).1 hne).2⟩
  · have hmg : m ≠ g := Nat.ne_of_lt (hb.2.1 m hne)
    exact ⟨((hd m).2.1 hne).1, cstore_push_eq_none hmg ((hd m).2.1 hne).2⟩
  · rcases CStore.get?_push_ne_none.mp hne with rfl | hin
    · exact ⟨by by_contra hc; exact Nat.lt_irrefl _ (hb.1 m hc),
             by by_contra hc; exact Nat.lt_irrefl _ (hb.2.1 m hc)⟩
    · exact (hd m).2.2 hin

-- BUMP: a `throws` handle mints (g→g+1) but pushes NO store, so the bound only weakens.
theorem StoresBelow.bump {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresBelow g σ τ κ) : StoresBelow (g+1) σ τ κ :=
  ⟨fun m hm => Nat.lt_succ_of_lt (h.1 m hm), fun m hm => Nat.lt_succ_of_lt (h.2.1 m hm),
   fun m hm => Nat.lt_succ_of_lt (h.2.2 m hm)⟩

theorem StoresBelow.nil {g : Nat} : StoresBelow g [] [] [] :=
  ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩
theorem StoresDisjoint.nil : StoresDisjoint [] [] [] :=
  fun _ => ⟨fun h => absurd rfl h, fun h => absurd rfl h, fun h => absurd rfl h⟩

-- POP: a key present in `tail` is present in the whole list (tail keys ⊆ list keys). `get?` = `find?`,
-- so `tail.get? m ≠ none → list.get? m ≠ none` (a deeper match implies SOME match on the cons).
theorem SStore.tail_get?_ne_none {σ : SStore} {m : Nat} (h : SStore.get? σ.tail m ≠ none) :
    SStore.get? σ m ≠ none := by
  cases σ with
  | nil => exact h
  | cons p σ' =>
      obtain ⟨ℓ0, w⟩ := p
      simp only [List.tail] at h
      by_cases hm : ℓ0 = m
      · subst hm; simp [SStore.get?, List.find?]
      · simp only [SStore.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]; exact h
theorem THeap.tail_get?_ne_none {τ : THeap} {m : Nat} (h : THeap.get? τ.tail m ≠ none) :
    THeap.get? τ m ≠ none := by
  cases τ with
  | nil => exact h
  | cons p τ' =>
      obtain ⟨ℓ0, w⟩ := p
      simp only [List.tail] at h
      by_cases hm : ℓ0 = m
      · subst hm; simp [THeap.get?, List.find?]
      · simp only [THeap.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]; exact h
theorem CStore.tail_get?_ne_none {κ : CStore} {m : Nat} (h : CStore.get? κ.tail m ≠ none) :
    CStore.get? κ m ≠ none := by
  cases κ with
  | nil => exact h
  | cons p κ' =>
      obtain ⟨ℓ0, pc⟩ := p
      simp only [List.tail] at h
      by_cases hm : ℓ0 = m
      · subst hm; simp [CStore.get?, List.find?]
      · simp only [CStore.get?, List.find?, hm, decide_false, Bool.false_eq_true, if_false]; exact h

theorem StoresBelow.tail_state {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresBelow g σ τ κ) : StoresBelow g σ.tail τ κ :=
  ⟨fun m hm => h.1 m (SStore.tail_get?_ne_none hm), h.2.1, h.2.2⟩
theorem StoresBelow.tail_txn {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresBelow g σ τ κ) : StoresBelow g σ τ.tail κ :=
  ⟨h.1, fun m hm => h.2.1 m (THeap.tail_get?_ne_none hm), h.2.2⟩
theorem StoresBelow.tail_custom {g : Nat} {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresBelow g σ τ κ) : StoresBelow g σ τ κ.tail :=
  ⟨h.1, h.2.1, fun m hm => h.2.2 m (CStore.tail_get?_ne_none hm)⟩
theorem StoresDisjoint.tail_state {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresDisjoint σ τ κ) : StoresDisjoint σ.tail τ κ := by
  intro m
  refine ⟨fun hne => (h m).1 (SStore.tail_get?_ne_none hne), fun hne => ?_, fun hne => ?_⟩
  · exact ⟨by by_contra hc; exact (SStore.tail_get?_ne_none hc) ((h m).2.1 hne).1, ((h m).2.1 hne).2⟩
  · exact ⟨by by_contra hc; exact (SStore.tail_get?_ne_none hc) ((h m).2.2 hne).1, ((h m).2.2 hne).2⟩
theorem StoresDisjoint.tail_txn {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresDisjoint σ τ κ) : StoresDisjoint σ τ.tail κ := by
  intro m
  refine ⟨fun hne => ?_, fun hne => (h m).2.1 (THeap.tail_get?_ne_none hne), fun hne => ?_⟩
  · exact ⟨by by_contra hc; exact (THeap.tail_get?_ne_none hc) ((h m).1 hne).1, ((h m).1 hne).2⟩
  · exact ⟨((h m).2.2 hne).1, by by_contra hc; exact (THeap.tail_get?_ne_none hc) ((h m).2.2 hne).2⟩
theorem StoresDisjoint.tail_custom {σ : SStore} {τ : THeap} {κ : CStore}
    (h : StoresDisjoint σ τ κ) : StoresDisjoint σ τ κ.tail := by
  intro m
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => (h m).2.2 (CStore.tail_get?_ne_none hne)⟩
  · exact ⟨((h m).1 hne).1, by by_contra hc; exact (CStore.tail_get?_ne_none hc) ((h m).1 hne).2⟩
  · exact ⟨((h m).2.1 hne).1, by by_contra hc; exact (CStore.tail_get?_ne_none hc) ((h m).2.1 hne).2⟩

/-- Overwrite each `custom` frame's private parameter with the head parameter of `κ` (consumed in
order). Clause tables are structural code, not mutable state, so they remain those of the frame.
This is the custom-store pass of the uniform `netEffect` rebuild (ADR-0114). -/
def updateCustoms : HStack → CStore → HStack
  | [],       _ => []
  | fr :: hs, κ =>
      match fr.handler with
      | .custom ℓ0 _ cls0 =>
          match κ with
          | (_, (p, cls)) :: κ' => { fr with handler := .custom ℓ0 p cls } :: updateCustoms hs κ'
          | []                  => fr :: updateCustoms hs []     -- κ exhausted (unreachable under CCorr)
      | _ => fr :: updateCustoms hs κ

theorem hsStates_updateCustoms : ∀ (hs : HStack) (κ : CStore),
    hsStates (updateCustoms hs κ) = hsStates hs := by
  intro hs
  induction hs with
  | nil => intro κ; rfl
  | cons fr hs ih =>
      intro κ
      cases hh : fr.handler with
      | custom ℓ p cls =>
          cases κ with
          | nil => simp only [updateCustoms, hh, hsStates]; rw [ih]
          | cons entry κ' =>
              obtain ⟨n, pcls⟩ := entry; obtain ⟨p', cls'⟩ := pcls
              simp only [updateCustoms, hh, hsStates]; rw [ih]
      | state ℓ s => simp only [updateCustoms, hh, hsStates]; rw [ih]
      | throws ℓ => simp only [updateCustoms, hh, hsStates]; rw [ih]
      | transaction ℓ Θ => simp only [updateCustoms, hh, hsStates]; rw [ih]

theorem hsTxns_updateCustoms : ∀ (hs : HStack) (κ : CStore),
    hsTxns (updateCustoms hs κ) = hsTxns hs := by
  intro hs
  induction hs with
  | nil => intro κ; rfl
  | cons fr hs ih =>
      intro κ
      cases hh : fr.handler with
      | custom ℓ p cls =>
          cases κ with
          | nil => simp only [updateCustoms, hh, hsTxns]; rw [ih]
          | cons entry κ' =>
              obtain ⟨n, pcls⟩ := entry; obtain ⟨p', cls'⟩ := pcls
              simp only [updateCustoms, hh, hsTxns]; rw [ih]
      | state ℓ s => simp only [updateCustoms, hh, hsTxns]; rw [ih]
      | throws ℓ => simp only [updateCustoms, hh, hsTxns]; rw [ih]
      | transaction ℓ Θ => simp only [updateCustoms, hh, hsTxns]; rw [ih]

/-- `get?` of the projection reads the state frame with identity `n` (ties `hsStates` to `hsState`). -/
theorem get?_hsStates : ∀ (hs : HStack) (n : Nat),
    (hsStates hs).get? n = hsState hs n := by
  intro hs
  induction hs with
  | nil => intro n; rfl
  | cons fr hs ih =>
    intro n
    cases hh : fr.handler with
    | state ℓ0 s =>
        simp only [hsStates, hsState, hh]
        by_cases hc : fr.id = n
        · simp [SStore.get?, List.find?, hc]
        · simp only [if_neg hc, SStore.get?, List.find?, hc, decide_false, Bool.false_eq_true,
            if_false]; exact ih n
    | throws ℓ0 => simp only [hsStates, hsState, hh]; exact ih n
    | transaction ℓ0 Θ => simp only [hsStates, hsState, hh]; exact ih n
    | custom ℓ0 p cl => simp only [hsStates, hsState, hh]; exact ih n   -- custom = non-state frame, catch-all (ADR-0085 stage 1)

/-- Under `Corr`, the store read equals the machine read. -/
theorem Corr.get? {σ : SStore} {hs : HStack} (hC : Corr σ hs) (n : Nat) :
    σ.get? n = hsState hs n := by rw [hC]; exact get?_hsStates hs n

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
theorem stateUpdate_get {n : Nat} {v : Val} :
    ∀ {hs : HStack} {s : Val}, hsState hs n = some s → stateUpdate n "get" v hs = some (s, hs) := by
  intro hs
  induction hs with
  | nil => intro s hg; simp [hsState] at hg
  | cons fr hs ih =>
    intro s hg
    cases hh : fr.handler with
    | state ℓ0 s0 =>
        simp only [hsState, hh] at hg
        by_cases hc : fr.id = n
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
    | custom ℓ0 p cl =>   -- custom = non-state frame, catch-all (ADR-0085 stage 1)
        simp only [hsState, hh] at hg
        simp [stateUpdate, hh, ih hg]

/-- `put` correspondence: when `hsState hs ℓ = some s₀`, `stateUpdate ℓ "put" v hs` returns
`(vunit, hs')` whose state-projection is exactly the store after an in-place `put` —
`hsStates hs' = (hsStates hs).put ℓ v`. This is the structural `Corr`-preservation fact (D3): the
machine's in-place HStack update mirrors the store's in-place `put`. Induction on `hs`. -/
theorem stateUpdate_put {n : Nat} {v : Val} :
    ∀ {hs : HStack} {s0 : Val}, hsState hs n = some s0 →
      ∃ hs', stateUpdate n "put" v hs = some (.vunit, hs')
        ∧ hsStates hs' = (hsStates hs).put n v := by
  intro hs
  induction hs with
  | nil => intro s0 hg; simp [hsState] at hg
  | cons fr hs ih =>
    intro s0 hg
    cases hh : fr.handler with
    | state ℓ0 s0' =>
        by_cases hc : fr.id = n
        · -- found here: update this frame in place
          refine ⟨{ fr with handler := .state ℓ0 v } :: hs, ?_, ?_⟩
          · simp [stateUpdate, hh, hc]
          · simp [hsStates, hh, SStore.put, hc]
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
    | custom ℓ0 p cl =>   -- custom = non-state frame, catch-all (ADR-0085 stage 1)
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
  -- route-B: the body's net effect preserves the frame IDENTITY (minted once at HANDLE, never changed —
  -- `stateUpdate`/`txnUpdate` use `{fr with handler := …}`, keeping `id`). This is what lets the
  -- net-effect reconstruction (`updateStates_eq`) recover the exact HStack including its ids.
  a.id = b.id ∧ a.savedCode = b.savedCode ∧ a.savedStack = b.savedStack ∧
    (match a.handler, b.handler with
     | .state ℓ1 _, .state ℓ2 _ => ℓ1 = ℓ2
     | .throws ℓ1, .throws ℓ2 => ℓ1 = ℓ2
     | .transaction ℓ1 _, .transaction ℓ2 _ => ℓ1 = ℓ2
     -- A custom clause may replace its private parameter (ADR-0114). The custom store carries the
     -- full payload used by reconstruction; `HMut` records only the stable handler kind and label.
     | .custom ℓ1 _ _, .custom ℓ2 _ _ => ℓ1 = ℓ2
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
      refine ⟨rfl, rfl, rfl, ?_⟩
      cases fr.handler <;> simp, HMut.refl hs⟩

/-- If the body was installed under a NON-state top frame (throws/transaction) and `HMut` holds,
the resulting top is also non-state ⇒ the projection drops it ⇒ `Corr` passes to the tail. -/
theorem Corr_pop_nonstate {σ : SStore} {fr top : HFrame} {hs tail : HStack}
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) (hmut : HMut (fr :: hs) (top :: tail))
    (hC : Corr σ (top :: tail)) : Corr σ tail := by
  obtain ⟨⟨_, _, _, hsh⟩, _⟩ := hmut
  unfold Corr at hC ⊢; rw [hC]
  cases hfr : fr.handler with
  | state ℓ1 s1 => exact absurd hfr (hns ℓ1 s1)
  | throws ℓ1 =>
      cases hth : top.handler with
      | throws ℓ2 => simp [hsStates, hth]
      | state _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | transaction _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | custom _ _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)   -- FrameMut throws/custom = False (ADR-0085 stage 1)
  | transaction ℓ1 Θ1 =>
      cases hth : top.handler with
      | transaction ℓ2 Θ2 => simp [hsStates, hth]
      | state _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | throws _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | custom _ _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)   -- FrameMut txn/custom = False (ADR-0085 stage 1)
  | custom ℓ1 p1 cl1 =>   -- custom fr: FrameMut forces top = custom (same label); hsStates skips both (ADR-0085 stage 1)
      cases hth : top.handler with
      | custom ℓ2 p2 cl2 => simp [hsStates, hth]
      | state _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | throws _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)
      | transaction _ _ => rw [hfr, hth] at hsh; exact absurd hsh (by simp)

/-- `stateUpdate`-put preserves `HMut` (it mutates one state-frame value in place). -/
theorem HMut.of_stateUpdate_put {n : Nat} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, stateUpdate n "put" v hs = some (r, hs') → HMut hs hs' := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [stateUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | state ℓ0 s =>
        simp only [stateUpdate, hh] at hsu
        by_cases hc : fr.id = n
        · simp only [if_pos hc, if_neg (by decide : ¬ ("put" = "get")), Option.some.injEq,
            Prod.mk.injEq] at hsu
          obtain ⟨_, rfl⟩ := hsu
          exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, HMut.refl hs⟩
        · simp only [if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | throws ℓ0 =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | custom ℓ0 p cl =>   -- custom = non-state frame, catch-all (ADR-0085 stage 1)
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | transaction ℓ0 Θ =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩

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
          refine ⟨⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.1.trans hbc.2.2.1, ?_⟩, ih hxy hyz⟩
          obtain ⟨_, _, _, h1⟩ := hab; obtain ⟨_, _, _, h2⟩ := hbc
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

/-- The reconstruction lemma: a structure-preserving machine stack whose three projections are
`σ'`, `τ'`, and `κ'` is exactly the three-pass store reconstruction of the original stack. -/
theorem updateStates_eq : ∀ {hs k : HStack} {σ' : SStore} {τ' : THeap} {κ' : CStore},
    HMut hs k → Corr σ' k → TCorr τ' k → CCorr κ' k →
      k = updateCustoms (updateTxns (updateStates hs σ') τ') κ' := by
  intro hs
  induction hs with
  | nil =>
      intro k σ' τ' κ' hmut _ _ _
      cases k with
      | nil => rfl
      | cons => simp [HMut] at hmut
  | cons fr hs ih =>
      intro k σ' τ' κ' hmut hC hT hK
      cases k with
      | nil => simp [HMut] at hmut
      | cons fk k =>
        obtain ⟨hfm, hmut'⟩ := hmut
        obtain ⟨hid, hscode, hsstack, hsh⟩ := hfm
        unfold Corr at hC; unfold TCorr at hT; unfold CCorr at hK
        cases hfr : fr.handler with
        | state ℓ0 s0 =>
            cases hfk : fk.handler with
            | state ℓ1 s1 =>
                rw [hfr, hfk] at hsh; simp only at hsh; subst hsh
                rw [hsStates, hfk] at hC
                rw [hsTxns, hfk] at hT
                simp only [hsCustoms, hfk] at hK
                -- σ' covers `(ℓ0,s1) :: hsStates k`; updateStates overwrites fr's value to s1, then
                -- updateTxns SKIPS the resulting state frame. The tail closes by IH.
                obtain ⟨p, σ'', rfl⟩ : ∃ p σ'', σ' = p :: σ'' := by
                  rw [hC]; exact ⟨_, _, rfl⟩
                simp only [List.cons.injEq] at hC; obtain ⟨hp, hCtl⟩ := hC; subst hp
                simp only [hsTxns, hfk] at hT
                simp only [updateStates, hfr, updateTxns, updateCustoms]
                rw [← ih hmut' (hCtl ▸ rfl : Corr σ'' k) (hT : TCorr τ' k) (hK : CCorr κ' k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | custom _ _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)   -- FrameMut state/custom = False (ADR-0085 stage 1)
        | throws ℓ0 =>
            cases hfk : fk.handler with
            | throws ℓ1 =>
                simp only [hsStates, hfk] at hC
                simp only [hsTxns, hfk] at hT
                simp only [hsCustoms, hfk] at hK
                simp only [updateStates, hfr, updateTxns, updateCustoms]
                rw [← ih hmut' (hC : Corr σ' k) (hT : TCorr τ' k) (hK : CCorr κ' k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | custom _ _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)   -- FrameMut throws/custom = False (ADR-0085 stage 1)
        | transaction ℓ0 Θ0 =>
            cases hfk : fk.handler with
            | transaction ℓ1 Θ1 =>
                rw [hfr, hfk] at hsh; simp only at hsh; subst hsh
                simp only [hsStates, hfk] at hC
                rw [hsTxns, hfk] at hT
                simp only [hsCustoms, hfk] at hK
                -- τ' covers `(ℓ0,Θ1) :: hsTxns k`; updateStates SKIPS the txn frame (copies fr), then
                -- updateTxns overwrites fr's heap to Θ1. The tail closes by IH.
                obtain ⟨p, τ'', rfl⟩ : ∃ p τ'', τ' = p :: τ'' := by
                  rw [hT]; exact ⟨_, _, rfl⟩
                simp only [List.cons.injEq] at hT; obtain ⟨hp, hTtl⟩ := hT; subst hp
                simp only [updateStates, hfr, updateTxns, updateCustoms]
                rw [← ih hmut' (hC : Corr σ' k) (hTtl ▸ rfl : TCorr τ'' k) (hK : CCorr κ' k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | custom _ _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)   -- FrameMut txn/custom = False (ADR-0085 stage 1)
        | custom ℓ0 p0 cl0 =>
            cases hfk : fk.handler with
            | custom ℓ1 p1 cl1 =>
                rw [hfr, hfk] at hsh
                simp only [hsStates, hfk] at hC
                simp only [hsTxns, hfk] at hT
                rw [hsCustoms, hfk] at hK
                subst κ'
                simp only [updateStates, hfr, updateTxns, updateCustoms]
                rw [← ih hmut' (hC : Corr σ' k) (hT : TCorr τ' k) (rfl : CCorr (hsCustoms k) k)]
                obtain ⟨fkc, fks, fkh⟩ := fk; obtain ⟨frc, frs, frh⟩ := fr
                simp_all
            | state _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | throws _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)
            | transaction _ _ => rw [hfr, hfk] at hsh; exact absurd hsh (by simp)

/-- The combined net-HStack effect: overwrite state values, transaction heaps, and custom private
parameters from their three source stores. -/
def netEffect (hs : HStack) (σ : SStore) (τ : THeap) (κ : CStore) : HStack :=
  updateCustoms (updateTxns (updateStates hs σ) τ) κ

/-- `netEffect` with stores a HStack already mirrors (`Corr σ hs ∧ TCorr τ hs`) is the identity —
overwriting each value/heap with the one it already has. (`updateStates_eq` at `k = hs`, `HMut.refl`.) -/
theorem updateStates_self {σ : SStore} {τ : THeap} {κ : CStore} {hs : HStack}
    (hC : Corr σ hs) (hT : TCorr τ hs) (hK : CCorr κ hs) :
    netEffect hs σ τ κ = hs := (updateStates_eq (HMut.refl hs) hC hT hK).symm

/-- `updateStates` preserves the CUSTOM projection: rewriting state-frame values never touches custom
frames (op-disjointness), so `hsCustoms` is invariant. -/
theorem hsCustoms_updateStates : ∀ (hs : HStack) (σ : SStore),
    hsCustoms (updateStates hs σ) = hsCustoms hs := by
  intro hs
  induction hs with
  | nil => intro σ; rfl
  | cons fr hs ih =>
    intro σ
    cases hh : fr.handler with
    | state ℓ0 s =>
        cases σ with
        | nil => simp only [updateStates, hh, hsCustoms]; rw [ih]
        | cons p σ' => simp only [updateStates, hh, hsCustoms]; rw [ih]
    | throws ℓ0 => simp only [updateStates, hh, hsCustoms]; rw [ih]
    | transaction ℓ0 Θ => simp only [updateStates, hh, hsCustoms]; rw [ih]
    | custom ℓ0 p cl => simp only [updateStates, hh, hsCustoms]; rw [ih]

/-- `updateTxns` preserves the CUSTOM projection (op-disjointness — analog of `hsCustoms_updateStates`). -/
theorem hsCustoms_updateTxns : ∀ (hs : HStack) (τ : THeap),
    hsCustoms (updateTxns hs τ) = hsCustoms hs := by
  intro hs
  induction hs with
  | nil => intro τ; rfl
  | cons fr hs ih =>
    intro τ
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        cases τ with
        | nil => simp only [updateTxns, hh, hsCustoms]; rw [ih]
        | cons p τ' => simp only [updateTxns, hh, hsCustoms]; rw [ih]
    | state ℓ0 s => simp only [updateTxns, hh, hsCustoms]; rw [ih]
    | throws ℓ0 => simp only [updateTxns, hh, hsCustoms]; rw [ih]
    | custom ℓ0 p cl => simp only [updateTxns, hh, hsCustoms]; rw [ih]

/-- The first two reconstruction passes do not affect the custom pass's projection. -/
theorem hsCustoms_netEffect (hs : HStack) (σ : SStore) (τ : THeap) (κ : CStore) :
    hsCustoms (netEffect hs σ τ κ) = hsCustoms (updateCustoms hs κ) := by
  induction hs generalizing σ τ κ with
  | nil => rfl
  | cons fr hs ih =>
      cases hh : fr.handler with
      | state ℓ s =>
          cases σ with
          | nil =>
              simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
              simpa only [netEffect] using ih [] τ κ
          | cons entry σ' =>
              obtain ⟨n, v⟩ := entry
              simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
              simpa only [netEffect] using ih σ' τ κ
      | transaction ℓ Θ =>
          cases τ with
          | nil =>
              simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
              simpa only [netEffect] using ih σ [] κ
          | cons entry τ' =>
              obtain ⟨n, Θ'⟩ := entry
              simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
              simpa only [netEffect] using ih σ τ' κ
      | throws ℓ =>
          simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
          simpa only [netEffect] using ih σ τ κ
      | custom ℓ p cls =>
          cases κ with
          | nil =>
              simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
              exact congrArg (fun tail => (fr.id, (p, cls)) :: tail) (by
                simpa only [netEffect] using ih σ τ [])
          | cons entry κ' =>
              obtain ⟨n, pcls⟩ := entry; obtain ⟨p', cls'⟩ := pcls
              simp only [netEffect, updateStates, hh, updateTxns, updateCustoms, hsCustoms]
              exact congrArg (fun tail => (fr.id, (p', cls')) :: tail) (by
                simpa only [netEffect] using ih σ τ κ')


/-- `netEffect k σ τ κ` is `HMut`-related to `k`: net-update mutates state values / txn heaps in place,
preserving frame structure. -/
theorem HMut_netEffect : ∀ (hs : HStack) (σ : SStore) (τ : THeap) (κ : CStore),
    HMut hs (netEffect hs σ τ κ) := by
  intro hs
  induction hs with
  | nil => intro σ τ κ; exact HMut.refl []
  | cons fr hs ih =>
    intro σ τ κ
    cases hfr : fr.handler with
    | state ℓ0 s0 =>
        cases σ with
        | nil =>
            show HMut (fr :: hs) (updateCustoms (updateTxns (updateStates (fr :: hs) []) τ) κ)
            rw [show updateStates (fr :: hs) [] = fr :: updateStates hs [] from by simp only [updateStates, hfr]]
            rw [updateTxns_cons_state τ hfr]
            simp only [updateCustoms, hfr]
            exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih [] τ κ⟩
        | cons p σ' =>
            obtain ⟨ℓq, wq⟩ := p
            show HMut (fr :: hs) (updateCustoms (updateTxns (updateStates (fr :: hs) ((ℓq, wq) :: σ')) τ) κ)
            rw [show updateStates (fr :: hs) ((ℓq, wq) :: σ') = { fr with handler := .state ℓ0 wq } :: updateStates hs σ' from by simp only [updateStates, hfr]]
            rw [updateTxns_cons_state τ (show ({ fr with handler := .state ℓ0 wq } : HFrame).handler = .state ℓ0 wq from rfl)]
            simp only [updateCustoms]
            exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih σ' τ κ⟩
    | throws ℓ0 =>
        simp only [netEffect, updateStates, hfr, updateTxns_cons_throws τ hfr, updateCustoms]
        exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih σ τ κ⟩
    | custom ℓ0 p cl =>   -- custom = non-state, non-txn: both passes skip it (catch-all), like throws (ADR-0085 stage 1)
        cases κ with
        | nil =>
            simp only [netEffect, updateStates, hfr, updateTxns, updateCustoms]
            exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih σ τ []⟩
        | cons entry κ' =>
            obtain ⟨n, pcls⟩ := entry; obtain ⟨p', cls'⟩ := pcls
            simp only [netEffect, updateStates, hfr, updateTxns, updateCustoms]
            exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih σ τ κ'⟩
    | transaction ℓ0 Θ0 =>
        cases τ with
        | nil =>
            simp only [netEffect, updateStates_cons_txn σ hfr, updateTxns, hfr, updateCustoms]
            exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih σ [] κ⟩
        | cons p τ' =>
            obtain ⟨ℓq, Θq⟩ := p
            simp only [netEffect, updateStates_cons_txn σ hfr, updateTxns, hfr, updateCustoms]
            exact ⟨⟨rfl, rfl, rfl, by simp [hfr]⟩, ih σ τ' κ⟩

/-- `netEffect` depends only on a HStack's FRAME STRUCTURE, not its stored values/heaps: `HMut`-
related stacks net-update identically. The re-base that lets a `letC`/`app` raised chain restate the
at-raise HStack on the ORIGINAL `hs`. Because `netEffect` overwrites BOTH state values and txn heaps,
the relaxed-HMut txn frames (differing `Θ`) are erased to the common store head — so this holds where
the state-only `updateStates` version would not. Reduced to `updateStates_eq` (the unique HStack
pinned by `HMut hs ·`, `Corr σ ·`, `TCorr τ ·`). -/
theorem netEffect_congr_HMut {hs k : HStack} (σ : SStore) (τ : THeap) (κ : CStore)
    (hmut : HMut hs k) (hcovS : Corr σ (netEffect k σ τ κ))
    (hcovT : TCorr τ (netEffect k σ τ κ)) (hcovK : CCorr κ (netEffect k σ τ κ)) :
    netEffect k σ τ κ = netEffect hs σ τ κ := by
  have hmutNet : HMut hs (netEffect k σ τ κ) := HMut.trans hmut (HMut_netEffect k σ τ κ)
  exact updateStates_eq hmutNet hcovS hcovT hcovK

/-- A NON-state frame `fr` is transparent to `updateStates`: `updateStates (fr::hs) σ = fr ::
updateStates hs σ` (the σ-cursor is not advanced — only `state` frames consume an entry). -/
theorem updateStates_cons_nonstate {fr : HFrame} {hs : HStack} (σ : SStore)
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) :
    updateStates (fr :: hs) σ = fr :: updateStates hs σ := by
  cases hh : fr.handler with
  | state ℓ s => exact absurd hh (hns ℓ s)
  | throws ℓ => simp only [updateStates, hh]
  | transaction ℓ Θ => simp only [updateStates, hh]
  | custom ℓ p cl => simp only [updateStates, hh]   -- custom = non-state frame, catch-all (ADR-0085 stage 1)


/-- `netEffect` distributes over a `throws`-frame head (it carries neither a state value nor a heap,
so both passes skip it). Used to push the at-raise tail through the throws install in `sim`. -/
theorem netEffect_cons_throws {fr : HFrame} {hs : HStack} {σ : SStore} {τ : THeap} {κ : CStore}
    {ℓ0 : Bang.EffectRow.Label} (hfr : fr.handler = .throws ℓ0) :
    netEffect (fr :: hs) σ τ κ = fr :: netEffect hs σ τ κ := by
  unfold netEffect
  rw [updateStates_cons_nonstate σ (by rw [hfr]; intro ℓ s; simp)]
  rw [updateTxns_cons_throws τ hfr]
  simp only [updateCustoms, hfr]

/-- `netEffect` on a custom head consumes exactly the custom-store head. The resulting frame remains
custom (and therefore transparent to throw unwinding), while the tail uses `κ.tail`. -/
theorem netEffect_cons_custom {fr : HFrame} {hs : HStack} {σ : SStore} {τ : THeap} {κ : CStore}
    {ℓ0 : Bang.EffectRow.Label} {p0 : Val} {cls0 : List (Bang.ClauseKey × Comp)}
    (hfr : fr.handler = .custom ℓ0 p0 cls0) :
    ∃ top, netEffect (fr :: hs) σ τ κ = top :: netEffect hs σ τ κ.tail ∧
      ∃ p cls, top.handler = .custom ℓ0 p cls := by
  unfold netEffect
  rw [updateStates_cons_nonstate σ (by rw [hfr]; intro ℓ s; simp)]
  simp only [updateTxns, hfr]
  cases κ with
  | nil => exact ⟨fr, by simp [updateCustoms, hfr], p0, cls0, hfr⟩
  | cons entry κ' =>
      obtain ⟨n, pcls⟩ := entry; obtain ⟨p, cls⟩ := pcls
      refine ⟨{ fr with handler := .custom ℓ0 p cls }, ?_, p, cls, rfl⟩
      simp only [updateCustoms, hfr, List.tail]

/-- The raised-part at-raise correspondence pops a NON-state, NON-txn (throws) install frame from the
COMBINED net-effect triple: a throws frame carries neither store entry, so `Corr`/`TCorr`/`HMut` over
`netEffect (fr::hs) σ' τ'` pass to the tail. The `sim` raised handle(throws) escape case (triple form). -/
theorem raisedTriple_pop_nontxn {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap} {κ' : CStore}
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) (hnt : ∀ ℓ Θ, fr.handler ≠ .transaction ℓ Θ)
    (hnc : ∀ ℓ p cls, fr.handler ≠ .custom ℓ p cls)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ' κ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ' κ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ' κ')) :
    Corr σ' (netEffect hs σ' τ' κ') ∧ TCorr τ' (netEffect hs σ' τ' κ') ∧ HMut hs (netEffect hs σ' τ' κ') := by
  have hupd : netEffect (fr :: hs) σ' τ' κ' = fr :: netEffect hs σ' τ' κ' := by
    unfold netEffect
    rw [updateStates_cons_nonstate σ' hns]
    cases hh : fr.handler with
    | state ℓ s => exact absurd hh (hns ℓ s)
    | transaction ℓ Θ => exact absurd hh (hnt ℓ Θ)
    | throws ℓ =>
        rw [updateTxns_cons_throws τ' hh]
        simp only [updateCustoms, hh]
    | custom ℓ p cl => exact absurd hh (hnc ℓ p cl)
  rw [hupd] at hCr hTr hmutr
  refine ⟨?_, ?_, HMut.tail hmutr⟩
  · unfold Corr at hCr ⊢
    have hproj : hsStates (fr :: netEffect hs σ' τ' κ') = hsStates (netEffect hs σ' τ' κ') := by
      cases hh : fr.handler with
      | state ℓ s => exact absurd hh (hns ℓ s)
      | throws ℓ => simp only [hsStates, hh]
      | transaction ℓ Θ => exact absurd hh (hnt ℓ Θ)
      | custom ℓ p cl => simp only [hsStates, hh]   -- custom = non-state frame, hsStates catch-all (ADR-0085 stage 1)
    rw [hproj] at hCr; exact hCr
  · unfold TCorr at hTr ⊢
    have hproj : hsTxns (fr :: netEffect hs σ' τ' κ') = hsTxns (netEffect hs σ' τ' κ') := by
      cases hh : fr.handler with
      | transaction ℓ Θ => exact absurd hh (hnt ℓ Θ)
      | state ℓ s => simp only [hsTxns, hh]
      | throws ℓ => simp only [hsTxns, hh]
      | custom ℓ p cl => simp only [hsTxns, hh]   -- custom = non-txn frame, hsTxns catch-all (ADR-0085 stage 1)
    rw [hproj] at hTr; exact hTr

/-- Pop a custom install from a raised net effect. The custom-store cursor advances once. -/
theorem raisedTriple_pop_custom {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap} {κ' : CStore}
    {ℓ0 : Bang.EffectRow.Label} {p0 : Val} {cls0 : List (Bang.ClauseKey × Comp)}
    (hfr : fr.handler = .custom ℓ0 p0 cls0)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ' κ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ' κ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ' κ')) :
    Corr σ' (netEffect hs σ' τ' κ'.tail) ∧ TCorr τ' (netEffect hs σ' τ' κ'.tail) ∧
      HMut hs (netEffect hs σ' τ' κ'.tail) := by
  obtain ⟨top, heq, p, cls, htop⟩ := netEffect_cons_custom hfr
  rw [heq] at hCr hTr hmutr
  refine ⟨?_, ?_, HMut.tail hmutr⟩
  · unfold Corr at hCr ⊢; simpa only [hsStates, htop] using hCr
  · unfold TCorr at hTr ⊢; simpa only [hsTxns, htop] using hTr


/-- The COMBINED (triple) raised-pop for a `state` install frame: pops `σ'.tail` (state side), `τ'`
unchanged (a state frame carries no heap). The `sim` raised handle(state) escape case (triple form). -/
theorem raisedTriple_pop_state {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap} {κ' : CStore}
    {ℓ0 : Bang.EffectRow.Label} {s0 : Val} (hfr : fr.handler = .state ℓ0 s0)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ' κ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ' κ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ' κ')) :
    Corr σ'.tail (netEffect hs σ'.tail τ' κ') ∧ TCorr τ' (netEffect hs σ'.tail τ' κ')
      ∧ HMut hs (netEffect hs σ'.tail τ' κ') := by
  cases σ' with
  | nil =>
      exfalso; unfold Corr netEffect at hCr
      rw [hsStates_updateCustoms] at hCr
      rw [updateStates] at hCr; simp only [hfr] at hCr
      rw [updateTxns_cons_state τ' hfr] at hCr
      rw [hsStates] at hCr; simp only [hfr] at hCr
      exact (List.cons_ne_nil _ _ hCr.symm)
  | cons p σ1' =>
      obtain ⟨ℓa, wa⟩ := p
      have hupd : netEffect (fr :: hs) ((ℓa, wa) :: σ1') τ' κ' =
          { fr with handler := .state ℓ0 wa } :: netEffect hs σ1' τ' κ' := by
        unfold netEffect; rw [updateStates]; simp only [hfr]
        rw [updateTxns_cons_state τ' (show ({ fr with handler := .state ℓ0 wa } : HFrame).handler = .state ℓ0 wa from rfl)]
        simp only [updateCustoms]
      rw [hupd] at hCr hTr hmutr
      simp only [List.tail]
      refine ⟨?_, ?_, HMut.tail hmutr⟩
      · unfold Corr at hCr ⊢; simp only [hsStates] at hCr
        exact (List.cons.injEq _ _ _ _).mp hCr |>.2
      · unfold TCorr at hTr ⊢; simpa only [hsTxns] using hTr

/-- The COMBINED (triple) raised-pop for a `transaction` install frame: pops `τ'.tail` (txn side),
`σ'` unchanged (a txn frame carries no state). The `sim` raised handle(transaction) escape case. -/
theorem raisedTriple_pop_txn {fr : HFrame} {hs : HStack} {σ' : SStore} {τ' : THeap} {κ' : CStore}
    {ℓ0 : Bang.EffectRow.Label} {Θ0 : List Val} (hfr : fr.handler = .transaction ℓ0 Θ0)
    (hCr : Corr σ' (netEffect (fr :: hs) σ' τ' κ'))
    (hTr : TCorr τ' (netEffect (fr :: hs) σ' τ' κ'))
    (hmutr : HMut (fr :: hs) (netEffect (fr :: hs) σ' τ' κ')) :
    Corr σ' (netEffect hs σ' τ'.tail κ') ∧ TCorr τ'.tail (netEffect hs σ' τ'.tail κ')
      ∧ HMut hs (netEffect hs σ' τ'.tail κ') := by
  cases τ' with
  | nil =>
      exfalso; unfold TCorr netEffect at hTr
      rw [hsTxns_updateCustoms] at hTr
      rw [updateStates_cons_txn σ' hfr] at hTr
      rw [updateTxns] at hTr; simp only [hfr] at hTr
      rw [hsTxns] at hTr; simp only [hfr] at hTr
      exact (List.cons_ne_nil _ _ hTr.symm)
  | cons p τ1' =>
      obtain ⟨ℓa, Θa⟩ := p
      have hupd : netEffect (fr :: hs) σ' ((ℓa, Θa) :: τ1') κ' =
          { fr with handler := .transaction ℓ0 Θa } :: netEffect hs σ' τ1' κ' := by
        unfold netEffect; rw [updateStates_cons_txn σ' hfr, updateTxns]; simp only [hfr]
        simp only [updateCustoms]
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
        by_cases hc : fr.id = ℓ
        · simp [stateUpdate, hh, hc, hng, hnp]
        · simp [stateUpdate, hh, hc, ih hng hnp]
    | throws ℓ0 => simp [stateUpdate, hh, ih hng hnp]
    | transaction ℓ0 Θ => simp [stateUpdate, hh, ih hng hnp]
    | custom ℓ0 p cl => simp [stateUpdate, hh, ih hng hnp]   -- custom = non-state, catch-all (ADR-0085 stage 1)

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
        by_cases hc : fr.id = ℓ
        · simp [if_pos hc] at hns
        · simp only [if_neg hc] at hns
          simp [stateUpdate, hh, hc, ih hns]
    | throws ℓ0 => simp only [hsState, hh] at hns; simp [stateUpdate, hh, ih hns]
    | transaction ℓ0 Θ => simp only [hsState, hh] at hns; simp [stateUpdate, hh, ih hns]
    | custom ℓ0 p cl => simp only [hsState, hh] at hns; simp [stateUpdate, hh, ih hns]   -- custom = non-state, catch-all (ADR-0085 stage 1)

/-- `Corr` is preserved by a `handle (state ℓ s)` install: PUSHING `(ℓ ↦ s)` on the store
mirrors pushing a `state ℓ s` frame on the HStack. -/
theorem Corr_install {σ : SStore} {hs : HStack} (ℓ : Bang.EffectRow.Label) (s : Val) (fr : HFrame)
    (hfr : fr.handler = .state ℓ s) (hC : Corr σ hs) : Corr (σ.push fr.id s) (fr :: hs) := by
  unfold Corr at hC ⊢; rw [hC]; simp [hsStates, hfr, SStore.push]

/-- A NON-state frame (throws/transaction) carries no store entry: pushing it preserves `Corr`. -/
theorem Corr_install_nonstate {σ : SStore} {hs : HStack} (fr : HFrame)
    (hns : ∀ ℓ s, fr.handler ≠ .state ℓ s) (hC : Corr σ hs) : Corr σ (fr :: hs) := by
  unfold Corr at hC ⊢; rw [hC]
  cases hh : fr.handler with
  | state ℓ0 s => exact absurd hh (hns ℓ0 s)
  | throws ℓ0 => simp [hsStates, hh]
  | transaction ℓ0 Θ => simp [hsStates, hh]
  | custom ℓ0 p cl => simp [hsStates, hh]   -- custom = non-state, hsStates catch-all (ADR-0085 stage 1)

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
        by_cases hc : fr.id = ℓ
        · simp [THeap.get?, List.find?, hc]
        · simp only [if_neg hc, THeap.get?, List.find?, hc, decide_false, Bool.false_eq_true,
            if_false]; exact ih ℓ
    | state ℓ0 s => simp only [hsTxns, hsTxn, hh]; exact ih ℓ
    | throws ℓ0 => simp only [hsTxns, hsTxn, hh]; exact ih ℓ
    | custom ℓ0 p cl => simp only [hsTxns, hsTxn, hh]; exact ih ℓ   -- custom = non-txn, hsTxns catch-all (ADR-0085 stage 1)

/-- Under `TCorr`, the heap read equals the machine read. -/
theorem TCorr.get? {τ : THeap} {hs : HStack} (hT : TCorr τ hs) (ℓ : Bang.EffectRow.Label) :
    τ.get? ℓ = hsTxn hs ℓ := by rw [hT]; exact get?_hsTxns hs ℓ

/-- `get?` of the custom projection reads the custom frame with identity `n` (ties `hsCustoms` to
`hsCustom`). The user-effect analog of `get?_hsStates`/`get?_hsTxns`. -/
theorem get?_hsCustoms : ∀ (hs : HStack) (n : Nat),
    (hsCustoms hs).get? n = hsCustom hs n := by
  intro hs
  induction hs with
  | nil => intro n; rfl
  | cons fr hs ih =>
    intro n
    cases hh : fr.handler with
    | custom ℓ0 p cl =>
        simp only [hsCustoms, hsCustom, hh]
        by_cases hc : fr.id = n
        · simp [CStore.get?, List.find?, hc]
        · simp only [if_neg hc, CStore.get?, List.find?, hc, decide_false, Bool.false_eq_true,
            if_false]; exact ih n
    | state ℓ0 s => simp only [hsCustoms, hsCustom, hh]; exact ih n
    | throws ℓ0 => simp only [hsCustoms, hsCustom, hh]; exact ih n
    | transaction ℓ0 Θ => simp only [hsCustoms, hsCustom, hh]; exact ih n

/-- Under `CCorr`, the custom store read equals the machine read. -/
theorem CCorr.get? {κ : CStore} {hs : HStack} (hK : CCorr κ hs) (n : Nat) :
    κ.get? n = hsCustom hs n := by rw [hK]; exact get?_hsCustoms hs n

theorem CCorr_put {κ : CStore} {hs hs' : HStack} {n : Nat} {next : Val}
    (hK : CCorr κ hs) (heq : hsCustoms hs' = (hsCustoms hs).put n next) :
    CCorr (κ.put n next) hs' := by
  unfold CCorr at hK ⊢; rw [hK, heq]

/-- The custom-service correspondence (ADR-0085 Stage 4, the user-effect analog of `stateUpdate_get`):
when `hsCustom hs n = some (p, cls)` (a live custom frame `n`) and `op`'s clause is `clause`,
`customUpdate` returns the clause body to run and the SAME `hs` (frame kept live). This is what aligns
the machine's `OP`-arm custom dispatch with `evalD`'s inline clause-service. -/
theorem customUpdate_service {n : Nat} {op : Bang.OpId} {v : Val} {p : Val}
    {cls : List (Bang.ClauseKey × Comp)} {clause : Bang.ClauseKey × Comp} :
    ∀ {hs : HStack}, hsCustom hs n = some (p, cls) → cls.find? (fun clause => clause.1.op == op) = some clause →
      clause.1.updates = false →
      customUpdate n op v hs = some (Comp.subst p (Comp.subst (Val.shift v) clause.2), hs) := by
  intro hs
  induction hs with
  | nil => intro hc _ _; simp [hsCustom] at hc
  | cons fr hs ih =>
    intro hc hcl hupd
    cases hh : fr.handler with
    | custom ℓ0 p0 cls0 =>
        by_cases hid : fr.id = n
        · simp only [hsCustom, hh, hid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [customUpdate, hh, hid, ↓reduceIte, hcl, hupd, Bool.false_eq_true, if_false]
        · simp only [hsCustom, hh, if_neg hid] at hc
          simp only [customUpdate, hh, if_neg hid, ih hc hcl hupd, Option.map_some]
    | state ℓ0 s =>
        simp only [hsCustom, hh] at hc
        simp only [customUpdate, hh, ih hc hcl hupd, Option.map_some]
    | throws ℓ0 =>
        simp only [hsCustom, hh] at hc
        simp only [customUpdate, hh, ih hc hcl hupd, Option.map_some]
    | transaction ℓ0 Θ =>
        simp only [hsCustom, hh] at hc
        simp only [customUpdate, hh, ih hc hcl hupd, Option.map_some]

/-- An updating custom clause returns directly and mutates exactly the matching custom-frame
parameter, mirroring `CStore.put` (ADR-0114). -/
theorem customUpdate_service_updating {n : Nat} {op : Bang.OpId} {v p resume next : Val}
    {cls : List (Bang.ClauseKey × Comp)} {clause : Bang.ClauseKey × Comp} :
    ∀ {hs : HStack}, hsCustom hs n = some (p, cls) →
      cls.find? (fun clause => clause.1.op == op) = some clause → clause.1.updates = true →
      Comp.subst p (Comp.subst (Val.shift v) clause.2) = .ret (.pair resume next) →
      ∃ hs', customUpdate n op v hs = some (.ret resume, hs') ∧
        hsStates hs' = hsStates hs ∧ hsTxns hs' = hsTxns hs ∧
        hsCustoms hs' = (hsCustoms hs).put n next ∧ HMut hs hs' := by
  intro hs
  induction hs with
  | nil => intro hc _ _ _; simp [hsCustom] at hc
  | cons fr hs ih =>
      intro hc hcl hupd hbody
      cases hh : fr.handler with
      | custom ℓ0 p0 cls0 =>
          by_cases hid : fr.id = n
          · simp only [hsCustom, hh, hid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            let fr' : HFrame := { fr with handler := .custom ℓ0 next cls0 }
            refine ⟨fr' :: hs, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [customUpdate, hh, hid, ↓reduceIte, hcl, hupd, if_true, hbody,
                Handler.label, fr']
            · simp only [hsStates, hh, fr']
            · simp only [hsTxns, hh, fr']
            · simp only [hsCustoms, hh, CStore.put, hid, if_true, fr']
            · exact ⟨⟨rfl, rfl, rfl, by simp [hh, fr']⟩, HMut.refl hs⟩
          · simp only [hsCustom, hh, if_neg hid] at hc
            obtain ⟨hs', hcu, hS, hT, hK, hM⟩ := ih hc hcl hupd hbody
            refine ⟨fr :: hs', ?_, ?_, ?_, ?_, ?_⟩
            · simp only [customUpdate, hh, if_neg hid, hcu, Option.map_some]
            · simpa only [hsStates, hh] using hS
            · simpa only [hsTxns, hh] using hT
            · simp only [hsCustoms, hh, CStore.put, if_neg hid, hK]
            · exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, hM⟩
      | state ℓ0 s =>
          simp only [hsCustom, hh] at hc
          obtain ⟨hs', hcu, hS, hT, hK, hM⟩ := ih hc hcl hupd hbody
          refine ⟨fr :: hs', by simp only [customUpdate, hh, hcu, Option.map_some], ?_, ?_, ?_, ?_⟩
          · simpa only [hsStates, hh] using congrArg (fun x => (fr.id, s) :: x) hS
          · simpa only [hsTxns, hh] using hT
          · simpa only [hsCustoms, hh] using hK
          · exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, hM⟩
      | throws ℓ0 =>
          simp only [hsCustom, hh] at hc
          obtain ⟨hs', hcu, hS, hT, hK, hM⟩ := ih hc hcl hupd hbody
          refine ⟨fr :: hs', by simp only [customUpdate, hh, hcu, Option.map_some], ?_, ?_, ?_, ?_⟩
          · simpa only [hsStates, hh] using hS
          · simpa only [hsTxns, hh] using hT
          · simpa only [hsCustoms, hh] using hK
          · exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, hM⟩
      | transaction ℓ0 Θ =>
          simp only [hsCustom, hh] at hc
          obtain ⟨hs', hcu, hS, hT, hK, hM⟩ := ih hc hcl hupd hbody
          refine ⟨fr :: hs', by simp only [customUpdate, hh, hcu, Option.map_some], ?_, ?_, ?_, ?_⟩
          · simpa only [hsStates, hh] using hS
          · simpa only [hsTxns, hh] using congrArg (fun x => (fr.id, Θ) :: x) hT
          · simpa only [hsCustoms, hh] using hK
          · exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, hM⟩

/-- No custom frame for `n` ⇒ `customUpdate` misses (the machine falls to the throw path). Ties the
`evalD`-side `κ.get? n = none` to the machine `customUpdate = none` via `CCorr`. -/
theorem customUpdate_none_of_hsCustom_none {n : Nat} {op : Bang.OpId} {v : Val} :
    ∀ {hs : HStack}, hsCustom hs n = none → customUpdate n op v hs = none := by
  intro hs
  induction hs with
  | nil => intro _; rfl
  | cons fr hs ih =>
    intro hc
    cases hh : fr.handler with
    | custom ℓ0 p0 cls0 =>
        by_cases hid : fr.id = n
        · simp only [hsCustom, hh, hid, ↓reduceIte] at hc; exact absurd hc (by simp)
        · simp only [hsCustom, hh, if_neg hid] at hc
          simp only [customUpdate, hh, if_neg hid, ih hc, Option.map_none]
    | state ℓ0 s => simp only [hsCustom, hh] at hc; simp only [customUpdate, hh, ih hc, Option.map_none]
    | throws ℓ0 => simp only [hsCustom, hh] at hc; simp only [customUpdate, hh, ih hc, Option.map_none]
    | transaction ℓ0 Θ => simp only [hsCustom, hh] at hc; simp only [customUpdate, hh, ih hc, Option.map_none]

/-- Custom frame present but the op has no clause ⇒ `customUpdate` misses (throws path). Ties
`cls.find? op = none` to the machine miss. -/
theorem customUpdate_none_of_clause_miss {n : Nat} {op : Bang.OpId} {v : Val} {p : Val}
    {cls : List (Bang.ClauseKey × Comp)} :
    ∀ {hs : HStack}, hsCustom hs n = some (p, cls) → cls.find? (fun clause => clause.1.op == op) = none →
      customUpdate n op v hs = none := by
  intro hs
  induction hs with
  | nil => intro hc _; simp [hsCustom] at hc
  | cons fr hs ih =>
    intro hc hcl
    cases hh : fr.handler with
    | custom ℓ0 p0 cls0 =>
        by_cases hid : fr.id = n
        · simp only [hsCustom, hh, hid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [customUpdate, hh, hid, ↓reduceIte, hcl]
        · simp only [hsCustom, hh, if_neg hid] at hc
          simp only [customUpdate, hh, if_neg hid, ih hc hcl, Option.map_none]
    | state ℓ0 s => simp only [hsCustom, hh] at hc; simp only [customUpdate, hh, ih hc hcl, Option.map_none]
    | throws ℓ0 => simp only [hsCustom, hh] at hc; simp only [customUpdate, hh, ih hc hcl, Option.map_none]
    | transaction ℓ0 Θ => simp only [hsCustom, hh] at hc; simp only [customUpdate, hh, ih hc hcl, Option.map_none]

/-- Installing a `custom` frame pushes its `(p, cls)` onto the custom store (the `handle (custom)`
INSTALL — analog of `Corr_install`). -/
theorem CCorr_install {κ : CStore} {hs : HStack} (ℓ : Bang.EffectRow.Label) (p : Val)
    (cls : List (Bang.ClauseKey × Comp)) (fr : HFrame) (hfr : fr.handler = .custom ℓ p cls) (hK : CCorr κ hs) :
    CCorr (κ.push fr.id p cls) (fr :: hs) := by
  unfold CCorr at hK ⊢; rw [hK]; simp [hsCustoms, hfr, CStore.push]

/-- A NON-custom frame (state/throws/transaction) carries no clause entry: pushing it preserves `CCorr`. -/
theorem CCorr_install_noncustom {κ : CStore} {hs : HStack} (fr : HFrame)
    (hnc : ∀ ℓ p cls, fr.handler ≠ .custom ℓ p cls) (hK : CCorr κ hs) : CCorr κ (fr :: hs) := by
  unfold CCorr at hK ⊢; rw [hK]
  cases hh : fr.handler with
  | custom ℓ0 p cl => exact absurd hh (hnc ℓ0 p cl)
  | state ℓ0 s => simp [hsCustoms, hh]
  | throws ℓ0 => simp [hsCustoms, hh]
  | transaction ℓ0 Θ => simp [hsCustoms, hh]

/-- `CCorr` for the tail when the top is a `custom` frame (the `handle (custom)` POP): the store's
tail mirrors the HStack's tail. -/
theorem CCorr_pop_custom {κ : CStore} {fr : HFrame} {hs : HStack} {ℓ0 : Bang.EffectRow.Label}
    {p : Val} {cls : List (Bang.ClauseKey × Comp)} (hfr : fr.handler = .custom ℓ0 p cls)
    (hK : CCorr κ (fr :: hs)) : CCorr κ.tail hs := by
  unfold CCorr at hK ⊢; rw [hK]; simp [hsCustoms, hfr]

/-- `CCorr` rides the POP of a NON-custom top frame (state/throws/txn): the custom projection skips it,
so the store is unchanged (analog of `Corr_pop_nonstate`, but no `HMut` needed — CCorr projects the
top directly). -/
theorem CCorr_pop_noncustom {κ : CStore} {top : HFrame} {tail : HStack}
    (hnc : ∀ ℓ p cls, top.handler ≠ .custom ℓ p cls) (hK : CCorr κ (top :: tail)) : CCorr κ tail := by
  unfold CCorr at hK ⊢; rw [hK]
  cases hh : top.handler with
  | custom ℓ0 p cl => exact absurd hh (hnc ℓ0 p cl)
  | state ℓ0 s => simp [hsCustoms, hh]
  | throws ℓ0 => simp [hsCustoms, hh]
  | transaction ℓ0 Θ => simp [hsCustoms, hh]

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
        by_cases hc : fr.id = ℓ
        · simp only [hsTxn, hh, hc, ↓reduceIte, Option.some.injEq] at hg
          subst hg
          refine ⟨{ fr with handler := .transaction ℓ0 (txnService op v Θ0).2 } :: hs, ?_, ?_⟩
          · simp only [txnUpdate, hh, hc, ↓reduceIte, hop]
          · simp [hsTxns, hh, THeap.put, hc]
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
    | custom ℓ0 p cl =>   -- custom = non-txn, txnUpdate/hsTxns catch-all (ADR-0085 stage 1)
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
        by_cases hc : fr.id = ℓ
        · simp [if_pos hc] at hns
        · simp only [if_neg hc] at hns
          simp [txnUpdate, hh, hc, ih hns]
    | state ℓ0 s => simp only [hsTxn, hh] at hns; simp [txnUpdate, hh, ih hns]
    | throws ℓ0 => simp only [hsTxn, hh] at hns; simp [txnUpdate, hh, ih hns]
    | custom ℓ0 p cl => simp only [hsTxn, hh] at hns; simp [txnUpdate, hh, ih hns]   -- custom = non-txn, catch-all (ADR-0085 stage 1)

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
        by_cases hc : fr.id = ℓ
        · simp [txnUpdate, hh, hc, hop]
        · simp [txnUpdate, hh, hc, ih hop]
    | state ℓ0 s => simp [txnUpdate, hh, ih hop]
    | throws ℓ0 => simp [txnUpdate, hh, ih hop]
    | custom ℓ0 p cl => simp [txnUpdate, hh, ih hop]   -- custom = non-txn, catch-all (ADR-0085 stage 1)

/-- `TCorr` is preserved by a `handle (transaction ℓ Θ)` install: PUSHING `(ℓ ↦ Θ)` on the heap-store
mirrors pushing a `transaction ℓ Θ` frame. -/
theorem TCorr_install {τ : THeap} {hs : HStack} (ℓ : Bang.EffectRow.Label) (Θ : List Val) (fr : HFrame)
    (hfr : fr.handler = .transaction ℓ Θ) (hT : TCorr τ hs) : TCorr (τ.push fr.id Θ) (fr :: hs) := by
  unfold TCorr at hT ⊢; rw [hT]; simp [hsTxns, hfr, THeap.push]

/-- A NON-txn frame (state/throws) carries no heap entry: pushing it preserves `TCorr`. -/
theorem TCorr_install_nontxn {τ : THeap} {hs : HStack} (fr : HFrame)
    (hnt : ∀ ℓ Θ, fr.handler ≠ .transaction ℓ Θ) (hT : TCorr τ hs) : TCorr τ (fr :: hs) := by
  unfold TCorr at hT ⊢; rw [hT]
  cases hh : fr.handler with
  | transaction ℓ0 Θ => exact absurd hh (hnt ℓ0 Θ)
  | state ℓ0 s => simp [hsTxns, hh]
  | throws ℓ0 => simp [hsTxns, hh]
  | custom ℓ0 p cl => simp [hsTxns, hh]   -- custom = non-txn, hsTxns catch-all (ADR-0085 stage 1)

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
  | custom ℓ0 p cl => simp [hsTxns, hh]   -- custom = non-txn, hsTxns catch-all (ADR-0085 stage 1)

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
        by_cases hc : fr.id = ℓ
        · by_cases hop : isTxnOp op = true
          · simp only [txnUpdate, hh, hc, ↓reduceIte, hop, Option.some.injEq] at hsu
            obtain ⟨_, rfl⟩ := hsu; simp [hsStates, hh]
          · simp only [txnUpdate, hh, hc, ↓reduceIte, hop] at hsu; simp at hsu
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
    | custom ℓ0 p cl =>   -- custom = non-txn frame, txnUpdate/hsStates catch-all (ADR-0085 stage 1)
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
        by_cases hc : fr.id = ℓ
        · by_cases hop : isTxnOp op = true
          · simp only [txnUpdate, hh, hc, ↓reduceIte, hop, Option.some.injEq] at hsu
            obtain ⟨_, rfl⟩ := hsu
            exact ⟨⟨hc, rfl, rfl, by simp [hh]⟩, HMut.refl hs⟩
          · simp only [txnUpdate, hh, hc, ↓reduceIte, hop] at hsu; simp at hsu
        · simp only [txnUpdate, hh, if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | state ℓ0 s =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | throws ℓ0 =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩
    | custom ℓ0 p cl =>   -- custom = non-txn frame, txnUpdate catch-all; FrameMut custom/custom diagonal (ADR-0085 stage 1)
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        exact ⟨⟨rfl, rfl, rfl, by simp [hh]⟩, ih hsu1⟩

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
        by_cases hc : fr.id = ℓ
        · simp only [stateUpdate, hh, hc, ↓reduceIte, if_neg (by decide : ¬ ("put" = "get")),
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
    | custom ℓ0 p cl =>   -- custom = non-state frame: stateUpdate recurses; hsTxns skips custom (ADR-0085 stage 1)
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsTxns, hh]; exact ih hsu1

/-- `stateUpdate`'s `put` preserves the CUSTOM projection (op-disjointness — analog of
`hsTxns_stateUpdate_put`): a state-frame value rewrite never touches a custom frame's payload. -/
theorem hsCustoms_stateUpdate_put {ℓ : Bang.EffectRow.Label} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, stateUpdate ℓ "put" v hs = some (r, hs') → hsCustoms hs' = hsCustoms hs := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [stateUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | state ℓ0 s =>
        by_cases hc : fr.id = ℓ
        · simp only [stateUpdate, hh, hc, ↓reduceIte, if_neg (by decide : ¬ ("put" = "get")),
            Option.some.injEq] at hsu
          obtain ⟨_, rfl⟩ := hsu; simp [hsCustoms, hh]
        · simp only [stateUpdate, hh, if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          simp only [hsCustoms, hh]; exact ih hsu1
    | throws ℓ0 =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsCustoms, hh]; exact ih hsu1
    | transaction ℓ0 Θ =>
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsCustoms, hh]; exact ih hsu1
    | custom ℓ0 p cl =>   -- custom frame: stateUpdate recurses; hsCustoms KEEPS this frame's entry, rest by ih
        simp only [stateUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsCustoms, hh]; rw [ih hsu1]

/-- `txnUpdate`'s service preserves the CUSTOM projection (op-disjointness): a txn-heap rewrite never
touches a custom frame's payload. Analog of `hsCustoms_stateUpdate_put` for the txn side. -/
theorem hsCustoms_txnUpdate {n : Nat} {op : Bang.OpId} {v : Val} :
    ∀ {hs hs' : HStack} {r : Val}, txnUpdate n op v hs = some (r, hs') → hsCustoms hs' = hsCustoms hs := by
  intro hs
  induction hs with
  | nil => intro hs' r hsu; simp [txnUpdate] at hsu
  | cons fr hs ih =>
    intro hs' r hsu
    cases hh : fr.handler with
    | transaction ℓ0 Θ =>
        by_cases hc : fr.id = n
        · simp only [txnUpdate, hh, hc, ↓reduceIte] at hsu
          by_cases hto : isTxnOp op
          · simp only [hto, ↓reduceIte, Option.some.injEq] at hsu
            obtain ⟨_, rfl⟩ := hsu; simp [hsCustoms, hh]
          · simp only [hto, Bool.false_eq_true, ↓reduceIte] at hsu; exact absurd hsu (by simp)
        · simp only [txnUpdate, hh, if_neg hc, Option.map_eq_some_iff] at hsu
          obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
          simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
          simp only [hsCustoms, hh]; exact ih hsu1
    | state ℓ0 s =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsCustoms, hh]; exact ih hsu1
    | throws ℓ0 =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsCustoms, hh]; exact ih hsu1
    | custom ℓ0 p cl =>
        simp only [txnUpdate, hh, Option.map_eq_some_iff] at hsu
        obtain ⟨⟨r1, hs1⟩, hsu1, hpeq⟩ := hsu
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨_, rfl⟩ := hpeq
        simp only [hsCustoms, hh]; rw [ih hsu1]

/-- The machine. Structurally recursive on the fuel (k2-playbook §3); `SUBST`/`APP`
re-enter `compile` on the substituted body, `THROW` jumps via the pure `unwindFind`
(both direct recursive calls — structural). Carries an `HStack` of installed
handlers (deep dispatch). -/
def exec : Nat → Nat → Code → Stack → HStack → Option Stack
  | 0,          _, _,                  _, _  => none
  | Nat.succ _, _, [],                 s, _  => some s
  | Nat.succ f, g, Instr.RET v :: c,   s, hs => exec f g c (.ret v :: s) hs
  | Nat.succ f, g, Instr.LAMI M :: c,  s, hs => exec f g c (.lam M :: s) hs
  | Nat.succ f, g, Instr.SUBST N :: c, s, hs =>
      match s with
      | .ret v :: s' => exec f g (compile (Comp.subst v N) c) s' hs
      | _            => none
  | Nat.succ f, g, Instr.APP v :: c, s, hs =>
      match s with
      | .lam N :: s' => exec f g (compile (Comp.subst v N) c) s' hs
      | _            => none
  -- HANDLE (route-B): MINT id := g, push the frame (savedCode := this `c` = the abort target Kₒ), and
  -- RE-COMPILE the substituted body `subst (vcap id h.label) M` before `UNMARK :: c`. The counter advances
  -- to `g+1` (matching `evalD`'s handle-arm mint order). This is the SUBST/APP residual-recompile, now
  -- carrying the runtime-minted cap so the body's `perform`s resolve to identity-keyed `OP`s.
  | Nat.succ f, g, Instr.HANDLE h M :: c, s, hs =>
      let id := g
      exec f (g+1) (compile (Comp.subst (.vcap id h.label) M) (Instr.UNMARK :: c)) s
        ({ id := id, handler := h, savedCode := c, savedStack := s } :: hs)
  -- UNMARK pops on normal return (handler-return = identity, Q6).
  | Nat.succ f, g, Instr.UNMARK :: c, s, hs =>
      match hs with
      | _ :: hs' => exec f g c s hs'
      | []       => none
  -- THROW (route-B): unwind to the frame with IDENTITY n, DISCARDING the inner continuation; resume its
  -- saved OUTER continuation with `ret v` pushed (abort yields the payload).
  | Nat.succ f, g, Instr.THROW n op v :: _, _, hs =>
      match unwindFind n op hs with
      | some (c', s', hs') => exec f g c' (.ret v :: s') hs'   -- ABORT to (Kₒ, ret v), frame popped
      | none               => none                             -- uncaught = stuck
  -- OP (route-B, id-first): identity-keyed dispatch. Try `stateUpdate n` (state get/put, in-place
  -- resume), then `txnUpdate n` (txn resume), then `customUpdate n` (custom inline-service), then
  -- `unwindFind n` (throws abort, DISCARDING `c`). Each `*Update n` SKIPS non-matching frame KINDS and
  -- checks `fr.id = n` — so the IDENTITY n, not the op, picks which arm services (kind-first store idiom,
  -- the store image of `splitAtId`). n is in at most one frame-kind (generative freshness), so the
  -- try-order is irrelevant to the result. Mirrors the id-first `evalD` perform arm and `idDispatch`:
  -- the op only selects the operation WITHIN the resolved frame; an op the resolved frame can't handle
  -- (or n in no frame) falls through to the abort. The op name NEVER disambiguates the store, so there
  -- is no `isBuiltinOp` guard (operator ruling 2026-07-09, issue #62): a custom frame keyed "get" IS
  -- serviced by its clause; a built-in `get` reaches the state store only via its cap's identity.
  | Nat.succ f, g, Instr.OP n op v :: c, s, hs =>
      match stateUpdate n op v hs with
      | some (r, hs') => exec f g c (.ret r :: s) hs'          -- RESUME (state): continue c with ret r
      | none =>                                                -- not a state frame at n: try transaction
          match txnUpdate n op v hs with
          | some (r, hs') => exec f g c (.ret r :: s) hs'      -- RESUME (txn): continue c with ret r
          | none =>                                            -- not a txn frame at n: try custom
              match customUpdate n op v hs with
              -- RESUME (custom): re-compile the clause body and run it BEFORE `c` (the resume continuation),
              -- against the unchanged `hs` (frame kept live). Mirrors evalD's inline clause-service sub-eval:
              -- where evalD runs `evalD … κ clauseBody`, exec runs `compile clauseBody c` (invariant #4).
              | some (body, hs') => exec f g (compile body c) s hs'
              | none =>                                        -- no state/txn/custom frame at n ⇒ throws abort
                  match unwindFind n op hs with
                  | some (c', s', hs') => exec f g c' (.ret v :: s') hs'
                  | none               => none                 -- uncaught = stuck
  -- ADT eliminators (Unit 6): inspect the closed-value scrutinee in place, re-`compile` the chosen
  -- branch[v] (fuel-bounded ⇒ terminating), mirroring the `SUBST` exec arm. PURE — no `hs` change.
  | Nat.succ f, g, Instr.CASE w N₁ N₂ :: c, s, hs =>
      match w with
      | .inl v => exec f g (compile (Comp.subst v N₁) c) s hs
      | .inr v => exec f g (compile (Comp.subst v N₂) c) s hs
      | _      => none
  | Nat.succ f, g, Instr.SPLIT w N :: c, s, hs =>
      match w with
      | .pair v u => exec f g (compile (Comp.subst v (Comp.subst (Val.shift u) N)) c) s hs
      | _         => none

/-! ## The calculation is correct (proven) -/

/-- Fuel monotonicity, one step (k2-playbook §2 bedrock): more fuel never changes a
`some`. Induction on fuel, `cases` on the head instruction; `SUBST`/`APP`'s nested
stack-match resolves the same way. -/
theorem exec_succ : ∀ f g c s hs r, exec f g c s hs = some r → exec (f+1) g c s hs = some r := by
  intro f
  induction f with
  | zero => intro g c s hs r h; simp [exec] at h
  | succ f ih =>
    intro g c s hs r h
    cases c with
    | nil => simpa [exec] using h
    | cons i c =>
      cases i with
      | RET v => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | LAMI M => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | SUBST N =>
        simp only [exec] at h ⊢
        cases s with
        | nil => simp at h
        | cons hd s' => cases hd with
          | ret v => simp only [] at h ⊢; exact ih _ _ _ _ _ h
          | _ => simp at h
      | APP v =>
        simp only [exec] at h ⊢
        cases s with
        | nil => simp at h
        | cons hd s' => cases hd with
          | lam N => simp only [] at h ⊢; exact ih _ _ _ _ _ h
          | _ => simp at h
      | HANDLE hd M => simp only [exec] at h ⊢; exact ih _ _ _ _ _ h
      | UNMARK =>
        simp only [exec] at h ⊢
        cases hs with
        | nil => simp at h
        | cons hd hs' => simp only [] at h ⊢; exact ih _ _ _ _ _ h
      | THROW n op v =>
        simp only [exec] at h ⊢
        cases hu : unwindFind n op hs with
        | none => rw [hu] at h; simp at h
        | some cs => obtain ⟨c', s', hs'⟩ := cs; rw [hu] at h; exact ih _ _ _ _ _ h
      | OP n op v =>
        simp only [exec] at h ⊢
        cases hsu : stateUpdate n op v hs with
        | some ru =>
          obtain ⟨r, hs'⟩ := ru
          simp only [hsu] at h ⊢; exact ih _ _ _ _ _ h
        | none =>
          simp only [hsu] at h ⊢
          cases htu : txnUpdate n op v hs with
          | some ru =>
            obtain ⟨r, hs'⟩ := ru
            simp only [htu] at h ⊢; exact ih _ _ _ _ _ h
          | none =>
            simp only [htu] at h ⊢
            -- id-first exec OP arm: no isBuiltinOp branch — customUpdate then unwindFind.
            cases hcu : customUpdate n op v hs with
            | some ru =>
              obtain ⟨body, hs'⟩ := ru
              simp only [hcu] at h ⊢; exact ih _ _ _ _ _ h
            | none =>
              simp only [hcu] at h ⊢
              cases hu : unwindFind n op hs with
              | none => simp only [hu] at h; simp at h
              | some cs => obtain ⟨c', s', hs'⟩ := cs; simp only [hu] at h ⊢; exact ih _ _ _ _ _ h
      | CASE w N₁ N₂ =>
        simp only [exec] at h ⊢
        cases w with
        | inl v => simp only [] at h ⊢; exact ih _ _ _ _ _ h
        | inr v => simp only [] at h ⊢; exact ih _ _ _ _ _ h
        | _ => simp at h
      | SPLIT w N =>
        simp only [exec] at h ⊢
        cases w with
        | pair v u => simp only [] at h ⊢; exact ih _ _ _ _ _ h
        | _ => simp at h

/-- Fuel monotonicity, `≤` (k2-playbook §2): bump any sub-fuel to a common value. -/
theorem exec_mono : ∀ f f2 g c s hs r, f ≤ f2 → exec f g c s hs = some r → exec f2 g c s hs = some r := by
  intro f f2 g c s hs r hle h
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Nat.add_succ]; exact exec_succ _ _ _ _ _ _ ih

/-- The machine outcome of a `raised ℓ op v` hitting handler stack `hs`: unwind to
the nearest catching frame and resume its saved continuation with `ret v` pushed
(the abort), or `none` (uncaught). Factored out of `exec`'s THROW arm so the two-part
`sim` can target it (CalcEff §throwOutcome). -/
def throwOutcome (F g : Nat) (n : Nat) (op : Bang.OpId) (v : Val)
    (hs : HStack) : Option Stack :=
  match unwindFind n op hs with
  | some (c', s', hs') => exec F g c' (.ret v :: s') hs'
  | none               => none

/-- A non-throws top frame (state/transaction) is SKIPPED by the throws unwind ⇒ `throwOutcome`
is unchanged by prepending it (the abort target is found deeper). -/
theorem throwOutcome_cons_nonthrows (F g : Nat) (n : Nat) (op : Bang.OpId) (v : Val)
    (fr : HFrame) (hs : HStack) (hnt : ∀ ℓ0, fr.handler ≠ Handler.throws ℓ0) :
    throwOutcome F g n op v (fr :: hs) = throwOutcome F g n op v hs := by
  cases hh : fr.handler with
  | throws ℓ0 => exact absurd hh (hnt ℓ0)
  | state ℓ0 s => simp only [throwOutcome, unwindFind, hh]
  | transaction ℓ0 Θ => simp only [throwOutcome, unwindFind, hh]
  | custom ℓ0 p cl => simp only [throwOutcome, unwindFind, hh]   -- custom = non-throws: skipped by unwind (ADR-0085 stage 1)

/-- (★) the **two-part, store-threaded** simulation (k2-playbook §Effects + ADR-0031):
a `term` part AND a `raised` part. The store-thread is the resume mechanism — the
`term` part is now an EXISTENTIAL over the machine's resulting HStack `hsf` (M
transforms `hs ↝ hsf`, the continuation `c` runs from `hsf`), with `Corr σ' hsf`
(the store mirrors the machine's active state frames, D3). The `up`/`handle (state)`
cases use `stateUpdate_get`/`stateUpdate_put`/`Corr_install` to align the inline
store service with the in-place HStack update. The `handle (throws)` catch is the
zero-shot `THROW ↔ dispatch` correspondence (now σ-threaded).
Induction on the eval fuel `fe`. -/
theorem sim : ∀ fe,
    (∀ M g σ τ κ t g' σ' τ' κ', evalD fe g σ τ κ M = some (.term t, g', σ', τ', κ') →
      ∀ hs, Corr σ hs → TCorr τ hs → CCorr κ hs →
        -- correspondence-side bridge invariants (NOT program premises): stores keyed below `g` and
        -- pairwise-disjoint — every reachable config satisfies both by generative freshness. Threaded
        -- (with the POST-M output copies) so the id-first fail-loud raise sub-cases rule out a same-id
        -- cross-kind shadow; trivial at the empty-store entry.
        StoresBelow g σ τ κ → StoresDisjoint σ τ κ →
        ∃ hsf, Corr σ' hsf ∧ TCorr τ' hsf ∧ CCorr κ' hsf ∧ HMut hs hsf ∧
          StoresBelow g' σ' τ' κ' ∧ StoresDisjoint σ' τ' κ' ∧
          -- route-B: the continuation `c` runs from the POST-M counter `g'` (exec threaded g→g' through
          -- M's HANDLE mints), the whole body `compile M c` runs from the PRE-M counter `g`.
          ∀ c s F r, exec F g' c (t :: s) hsf = some r →
            ∃ F', exec F' g (compile M c) s hs = some r)
    ∧ (∀ M g σ τ κ n op v g' σ' τ' κ', evalD fe g σ τ κ M = some (.raised n op v, g', σ', τ', κ') →
      ∀ hs, Corr σ hs → TCorr τ hs → CCorr κ hs →
        StoresBelow g σ τ κ → StoresDisjoint σ τ κ →
        -- the at-raise HStack `netEffect hs σ' τ' κ'` mirrors the at-raise stores σ'/τ' (D3/D4) and is a
        -- value/heap-mutation of the at-handle `hs` — threaded so the throws-CAUGHT term subcase can
        -- name it as its existential witness (an outer put/writeTVar before a caught raise persists).
        -- κ' mirrors it too (`hsCustoms_netEffect`: netEffect leaves custom frames untouched).
        -- The post-raise store invariants ride out too, so the throws-CAUGHT subcase (which emits a
        -- TERM over the at-raise stores) can discharge its own term-output `StoresBelow`/`StoresDisjoint`.
        (Corr σ' (netEffect hs σ' τ' κ') ∧ TCorr τ' (netEffect hs σ' τ' κ') ∧ CCorr κ' (netEffect hs σ' τ' κ') ∧
          HMut hs (netEffect hs σ' τ' κ')) ∧ StoresBelow g' σ' τ' κ' ∧ StoresDisjoint σ' τ' κ' ∧
        ∀ c s F r, throwOutcome F g' n op v (netEffect hs σ' τ' κ') = some r →
        ∃ F', exec F' g (compile M c) s hs = some r) := by
  intro fe
  induction fe with
  | zero =>
      exact ⟨fun M g σ τ κ t g' σ' τ' κ' h => by simp [evalD] at h,
             fun M g σ τ κ n op v g' σ' τ' κ' h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M g σ τ κ t g' σ' τ' κ' h hs hC hT hK hSB hSD
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
          exact ⟨hs, hC, hT, hK, HMut.refl hs, hSB, hSD, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
          exact ⟨hs, hC, hT, hK, HMut.refl hs, hSB, hSD, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe g σ τ κ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hKM, hlenM, hSBM, hSDM, kM⟩ := ihT M g σ τ κ (.ret v) g1 σ1 τ1 κ1 hM hs hC hT hK hSB hSD
                obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, kN⟩ := ihT (Comp.subst v N) g1 σ1 τ1 κ1 t g' σ' τ' κ' h hsM hCM hTM hKM hSBM hSDM
                refine ⟨hsf, hCf, hTf, hKf, HMut.trans hlenM hlenf, hSBf, hSDf, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kN c s F r hr
                have hstep : exec (F1+1) g1 (Instr.SUBST N :: c) (.ret v :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.SUBST N :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
            | (.raised n op w, _, _, _), h =>
                -- letC propagates a raise: evalD (letC M N) = raised ⇒ h : raised = term, absurd
                simp [Option.bind] at h
      | force a =>
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, k⟩ := ihT M g σ τ κ t g' σ' τ' κ' h hs hC hT hK hSB hSD
              exact ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, fun c s F r hr => by
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
          cases hM : evalD fe g σ τ κ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.lam N), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hKM, hlenM, hSBM, hSDM, kM⟩ := ihT M g σ τ κ (.lam N) g1 σ1 τ1 κ1 hM hs hC hT hK hSB hSD
                obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, kN⟩ := ihT (Comp.subst v N) g1 σ1 τ1 κ1 t g' σ' τ' κ' h hsM hCM hTM hKM hSBM hSDM
                refine ⟨hsf, hCf, hTf, hKf, HMut.trans hlenM hlenf, hSBf, hSDf, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kN c s F r hr
                have hstep : exec (F1+1) g1 (Instr.APP v :: c) (.lam N :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.APP v :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.ret w), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
            | (.raised n op w, _, _, _, _), h => simp [Option.bind] at h
      | perform cap op v =>
          -- route-B, ID-FIRST: dispatch BY IDENTITY n — WHICH per-kind store holds n picks the arm
          -- (σ→state, τ→txn, κ→custom, disjoint by freshness), then the op selects the operation within
          -- the resolved frame. Mirrored by stateUpdate/txnUpdate/customUpdate (each id-keyed, kind-first)
          -- on hs. The cap is a value `vcap n ℓ` (a non-vcap cap can't reduce in `evalD`, vacuous via `h`).
          obtain ⟨n, ℓ, rfl⟩ : ∃ n ℓ, cap = Val.vcap n ℓ := by
            cases cap <;> first | exact ⟨_, _, rfl⟩ | simp [evalD] at h
          simp only [evalD] at h
          -- n resolves to the STATE store first (evalD's `match σ.get? n`); the machine's OP arm hits
          -- `stateUpdate n` first. Corr aligns the two reads (`Corr.get?`).
          cases hg : σ.get? n with
          | some sv =>
              rw [hg] at h
              -- state frame at n: op ∈ {get, put} services; any other op RAISES (⇒ term absurd).
              by_cases hop : op = "get"
              · subst hop
                simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                have hgState : hsState hs n = some sv := by rw [← Corr.get? hC n]; exact hg
                refine ⟨hs, hC, hT, hK, HMut.refl hs, hSB, hSD, fun c s F r hr => ⟨F+1, ?_⟩⟩
                simp only [compile, exec, stateUpdate_get hgState]; exact hr
              · by_cases hop2 : op = "put"
                · subst hop2
                  simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl,
                    Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                  have hgState : hsState hs n = some sv := by rw [← Corr.get? hC n]; exact hg
                  obtain ⟨hs', hsu, heq⟩ := stateUpdate_put (v := v) hgState
                  refine ⟨hs', Corr_put hC heq, ?_, ?_, HMut.of_stateUpdate_put hsu,
                    hSB.put_state, hSD.put_state, fun c s F r hr => ⟨F+1, ?_⟩⟩
                  · unfold TCorr; rw [hsTxns_stateUpdate_put hsu, ← hT]
                  · -- CCorr rides: stateUpdate_put rewrites a state-frame value, never a custom frame.
                    unfold CCorr; rw [hsCustoms_stateUpdate_put hsu, ← hK]
                  · simp only [compile, exec, hsu]; exact hr
                · -- op the state frame can't handle ⇒ evalD RAISES ⇒ term absurd.
                  simp only [if_neg hop, if_neg hop2] at h; simp at h
          | none =>
          rw [hg] at h
          cases hgt : τ.get? n with
          | some Θ =>
              rw [hgt] at h
              -- txn frame at n: an stm op services; any other op RAISES (⇒ term absurd).
              by_cases hopt : isTxnOp op = true
              · simp only [hopt, if_true, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                have hgTxn : hsTxn hs n = some Θ := by rw [← TCorr.get? hT n]; exact hgt
                -- op is a txn op, so it is NOT get/put (isTxnOp/get/put disjoint) ⇒ stateUpdate misses.
                have hop : op ≠ "get" := by intro he; rw [he] at hopt; simp [isTxnOp] at hopt
                have hop2 : op ≠ "put" := by intro he; rw [he] at hopt; simp [isTxnOp] at hopt
                obtain ⟨hs', hsu, heq⟩ := txnUpdate_service (v := v) hopt hgTxn
                refine ⟨hs', Corr_txnUpdate_eq hsu hC, ?_, ?_, HMut_of_txnUpdate hsu,
                  hSB.put_txn, hSD.put_txn, fun c s F r hr => ⟨F+1, ?_⟩⟩
                · unfold TCorr; rw [heq, ← hT]
                · -- CCorr rides: txnUpdate rewrites a txn-frame heap, never a custom frame.
                  unfold CCorr; rw [hsCustoms_txnUpdate hsu, ← hK]
                · have hns : stateUpdate n op v hs = none :=
                    stateUpdate_none_of_non_getput n v hs hop hop2
                  simp only [compile, exec, hns, hsu]; exact hr
              · -- op the txn frame can't handle ⇒ evalD RAISES ⇒ term absurd.
                rw [Bool.not_eq_true] at hopt; simp only [hopt, Bool.false_eq_true, if_false] at h; simp at h
          | none =>
          rw [hgt] at h
          -- n resolves to the CUSTOM store (ADR-0085 Stage 4): INLINE-SERVICE the clause, OR raise if
          -- no matching clause. evalD's `match κ.get? n`; the machine's OP arm falls through
          -- stateUpdate/txnUpdate (both none here) to customUpdate.
          cases hck : κ.get? n with
          | none => rw [hck] at h; simp at h   -- no custom frame for n ⇒ evalD raises ⇒ term absurd
          | some pcls =>
              obtain ⟨p, cls⟩ := pcls
              rw [hck] at h
              cases hcl : cls.find? (fun clause => clause.1.op == op) with
              | none => simp only [hcl] at h; simp at h   -- op unserviced ⇒ raise ⇒ term absurd
              | some clause =>
                  simp only [hcl] at h
                  have hgCustom : hsCustom hs n = some (p, cls) := by rw [← CCorr.get? hK n]; exact hck
                  have hns : stateUpdate n op v hs = none :=
                    stateUpdate_none_of_get?_none (by rw [← Corr.get? hC n]; exact hg)
                  have hnt : txnUpdate n op v hs = none :=
                    txnUpdate_none_of_hsTxn_none (by rw [← TCorr.get? hT n]; exact hgt)
                  by_cases hupd : clause.1.updates = true
                  · simp only [hupd, if_true] at h
                    split at h
                    · rename_i resume next hbody
                      simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                      obtain ⟨hs', hcu, hS, hTx, hCp, hMut⟩ :=
                        customUpdate_service_updating hgCustom hcl hupd hbody
                      refine ⟨hs', ?_, ?_, CCorr_put hK hCp, hMut, hSB.put_custom,
                        hSD.put_custom, fun c s F r hr => ⟨F+2, ?_⟩⟩
                      · unfold Corr at hC ⊢; rw [hS, ← hC]
                      · unfold TCorr at hT ⊢; rw [hTx, ← hT]
                      · simp only [compile, exec, hns, hnt, hcu]; exact hr
                    · simp_all
                  · have hupd0 : clause.1.updates = false := Bool.eq_false_of_not_eq_true hupd
                    simp only [hupd0, Bool.false_eq_true, if_false] at h
                    obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, kBody⟩ :=
                      ihT (Comp.subst p (Comp.subst (Val.shift v) clause.2)) g σ τ κ t g' σ' τ' κ' h hs hC hT hK hSB hSD
                    refine ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, fun c s F r hr => ?_⟩
                    obtain ⟨F', hF'⟩ := kBody c s F r hr
                    have hcu : customUpdate n op v hs
                        = some (Comp.subst p (Comp.subst (Val.shift v) clause.2), hs) :=
                      customUpdate_service hgCustom hcl hupd0
                    exact ⟨F'+1, by simp only [compile, exec, hns, hnt, hcu]; exact hF'⟩
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | custom ℓ0 p0 cls0 =>
              -- route-B INSTALL a custom frame (ADR-0085 Stage 4): MINT id := g, push (id ↦ (p0,cls0)) on κ,
              -- run the SUBSTITUTED body M' = subst (vcap g ℓ0) M at g+1. The machine's HANDLE recompiles the
              -- SAME M' at g+1 under an `id:=g` custom frame. Custom carries NO state/txn payload ⇒ Corr/TCorr
              -- pass through (like throws); CCorr installs/pops the κ entry (like state does for σ). The
              -- clause-service happens at the perform arm (already proven), not here — this is pure install/pop.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ τ (κ.push g p0 cls0) (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    -- The installed custom frame is popped, so reconstruction consumes `κ1.head`.
                    -- The custom frame is popped; κ1.tail mirrors it.
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 g1 cc (.ret v :: ss) (netEffect hs σ1 τ1 κ1.tail) = some r2 →
                        (∃ F', exec F' (g+1) (compile (Comp.subst (Val.vcap g ℓ0) M) (Instr.UNMARK :: cc)) ss
                          ({ id := g, handler := Handler.custom ℓ0 p0 cls0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (netEffect hs σ1 τ1 κ1.tail) ∧ TCorr τ1 (netEffect hs σ1 τ1 κ1.tail)
                        ∧ CCorr κ1.tail (netEffect hs σ1 τ1 κ1.tail) ∧ HMut hs (netEffect hs σ1 τ1 κ1.tail)
                        ∧ StoresBelow g1 σ1 τ1 κ1.tail ∧ StoresDisjoint σ1 τ1 κ1.tail := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { id := g, handler := Handler.custom ℓ0 p0 cls0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hCinstall : Corr σ (fr :: hs) :=
                        Corr_install_nonstate fr (by rw [hfrdef]; intro ℓ s; simp) hC
                      have hTinstall : TCorr τ (fr :: hs) :=
                        TCorr_install_nontxn fr (by rw [hfrdef]; intro ℓ Θ; simp) hT
                      have hKinstall : CCorr (κ.push g p0 cls0) (fr :: hs) :=
                        CCorr_install ℓ0 p0 cls0 fr (by rw [hfrdef]) hK
                      obtain ⟨hsM, hCM, hTM, hKM, hmutM, hSBM, hSDM, kM⟩ :=
                        ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ (κ.push g p0 cls0) (.ret v) g1 σ1 τ1 κ1 hM (fr :: hs) hCinstall hTinstall hKinstall
                          hSB.push_custom (hSD.push_custom hSB)
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have htop : ∃ p' cls', top.handler = .custom ℓ0 p' cls' := by
                        have hh := hmutM.1.2.2.2
                        cases hth : top.handler with
                        | custom ℓ1 p1 cls1 =>
                            rw [hfrdef, hth] at hh; simp only at hh; subst ℓ1; exact ⟨p1, cls1, rfl⟩
                        | state _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | throws _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | transaction _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                      obtain ⟨p', cls', hts⟩ := htop
                      have hCtail : Corr σ1 tail :=
                        Corr_pop_nonstate (fr := fr) (by rw [hfrdef]; intro ℓ s; simp) hmutM hCM
                      have hTtail : TCorr τ1 tail :=
                        TCorr_pop_nontxn (by rw [hts]; intro ℓ Θ; simp) hTM
                      have hKtail : CCorr κ1.tail tail := CCorr_pop_custom hts hKM
                      have htaileq : tail = netEffect hs σ1 τ1 κ1.tail :=
                        updateStates_eq (HMut.tail hmutM) hCtail hTtail hKtail
                      have hstep : exec (F2+1) g1 (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ hKtail, htaileq ▸ (HMut.tail hmutM),
                        hSBM.tail_custom, hSDM.tail_custom⟩
                    obtain ⟨_, hCf, hTf, hKf, hmutf, hSBf, hSDf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1 τ1 κ1.tail, hCf, hTf, hKf, hmutf, hSBf, hSDf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised n' op' w, _, _, _, _), h =>
                    -- body raises past the custom frame (custom never catches a throws-raise) ⇒ forwards ⇒
                    -- raised, contradicting the term part.
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | state ℓ0 s0 =>
              -- route-B INSTALL a state frame: MINT id := g, push (id ↦ s0) keyed by g, run the SUBSTITUTED
              -- body `M' = subst (vcap g ℓ0) M` at g+1. The machine's HANDLE recompiles the SAME M' at g+1
              -- under an `id:=g` frame — the HANDLE-defer-recompile lining up with the IH (the refute-watch).
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    -- The existential = `netEffect hs σ1.tail τ1 κ1`. `body cc ss` runs M' under the REAL frame
                    -- `{id:=g, state ℓ0 s0, cc, ss}` (g+1) and shows its popped tail IS the net effect.
                    -- κ threads UNCHANGED (state install doesn't touch custom frames; CCorr rides).
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 g1 cc (.ret v :: ss) (netEffect hs σ1.tail τ1 κ1) = some r2 →
                        (∃ F', exec F' (g+1) (compile (Comp.subst (Val.vcap g ℓ0) M) (Instr.UNMARK :: cc)) ss
                          ({ id := g, handler := Handler.state ℓ0 s0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1.tail (netEffect hs σ1.tail τ1 κ1) ∧ TCorr τ1 (netEffect hs σ1.tail τ1 κ1)
                        ∧ CCorr κ1 (netEffect hs σ1.tail τ1 κ1) ∧ HMut hs (netEffect hs σ1.tail τ1 κ1)
                        ∧ StoresBelow g1 σ1.tail τ1 κ1 ∧ StoresDisjoint σ1.tail τ1 κ1 := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { id := g, handler := Handler.state ℓ0 s0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hCinstall : Corr (σ.push g s0) (fr :: hs) :=
                        Corr_install ℓ0 s0 fr (by rw [hfrdef]) hC
                      have hTinstall : TCorr τ (fr :: hs) :=
                        TCorr_install_nontxn fr (by rw [hfrdef]; intro ℓ Θ; simp) hT
                      have hKinstall : CCorr κ (fr :: hs) :=
                        CCorr_install_noncustom fr (by rw [hfrdef]; intro ℓ p cls; simp) hK
                      obtain ⟨hsM, hCM, hTM, hKM, hmutM, hSBM, hSDM, kM⟩ :=
                        ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) (σ.push g s0) τ κ (.ret v) g1 σ1 τ1 κ1 hM (fr :: hs) hCinstall hTinstall hKinstall
                          hSB.push_state (hSD.push_state hSB)
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have htop : ∃ s', top.handler = .state ℓ0 s' := by
                        have hh := hmutM.1.2.2.2
                        cases hth : top.handler with
                        | state ℓ1 s1 => rw [hfrdef, hth] at hh; simp only at hh; subst hh; exact ⟨s1, rfl⟩
                        | throws _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | transaction _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | custom _ _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)   -- FrameMut state/custom = False
                      obtain ⟨s', hts⟩ := htop
                      have hCtail := Corr_pop_state hts hCM
                      have hTtail : TCorr τ1 tail :=
                        TCorr_pop_nontxn (by rw [hts]; intro ℓ Θ; simp) hTM
                      have hKtail : CCorr κ1 tail :=
                        CCorr_pop_noncustom (by rw [hts]; intro ℓ p cls; simp) hKM
                      have htaileq : tail = netEffect hs σ1.tail τ1 κ1 :=
                        updateStates_eq (HMut.tail hmutM) hCtail hTtail hKtail
                      -- the body's terminal config `top :: tail`; UNMARK pops `top` ⇒ run `cc` from `tail` at g1.
                      have hstep : exec (F2+1) g1 (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ hKtail, htaileq ▸ (HMut.tail hmutM),
                        hSBM.tail_state, hSDM.tail_state⟩
                    obtain ⟨_, hCf, hTf, hKf, hmutf, hSBf, hSDf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1.tail τ1 κ1, hCf, hTf, hKf, hmutf, hSBf, hSDf,
                      fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised n' op' w, _, _, _, _), h =>
                    -- body raises past the state frame (state never catches) ⇒ handle forwards ⇒ raised,
                    -- contradicting the term part.
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | throws ℓ0 =>
              -- route-B INSTALL a throws frame: MINT id := g, run the SUBSTITUTED body `M' = subst (vcap g
              -- ℓ0) M` at g+1 (no store push — throws carries neither state nor heap). The machine's HANDLE
              -- recompiles the SAME M' at g+1 under an `id:=g` throws frame; the IH on M' closes (refute-watch).
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    -- throws-install + normal return: existential = `netEffect hs σ1 τ1 κ1` (throws carries
                    -- no state/heap/clauses ⇒ all three stores pass through). Pop the throws frame.
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 g1 cc (.ret v :: ss) (netEffect hs σ1 τ1 κ1) = some r2 →
                        (∃ F', exec F' (g+1) (compile (Comp.subst (Val.vcap g ℓ0) M) (Instr.UNMARK :: cc)) ss
                          ({ id := g, handler := Handler.throws ℓ0, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (netEffect hs σ1 τ1 κ1) ∧ TCorr τ1 (netEffect hs σ1 τ1 κ1)
                        ∧ CCorr κ1 (netEffect hs σ1 τ1 κ1) ∧ HMut hs (netEffect hs σ1 τ1 κ1)
                        ∧ StoresBelow g1 σ1 τ1 κ1 ∧ StoresDisjoint σ1 τ1 κ1 := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { id := g, handler := Handler.throws ℓ0, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hns : ∀ ℓ s, fr.handler ≠ Handler.state ℓ s := by rw [hfrdef]; intro ℓ s; simp
                      have hnt : ∀ ℓ Θ, fr.handler ≠ Handler.transaction ℓ Θ := by rw [hfrdef]; intro ℓ Θ; simp
                      have hnc : ∀ ℓ p cls, fr.handler ≠ Handler.custom ℓ p cls := by rw [hfrdef]; intro ℓ p cls; simp
                      have hCinstall : Corr σ (fr :: hs) := Corr_install_nonstate fr hns hC
                      have hTinstall : TCorr τ (fr :: hs) := TCorr_install_nontxn fr hnt hT
                      have hKinstall : CCorr κ (fr :: hs) := CCorr_install_noncustom fr hnc hK
                      obtain ⟨hsM, hCM, hTM, hKM, hmutM, hSBM, hSDM, kM⟩ :=
                        ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ (.ret v) g1 σ1 τ1 κ1 hM (fr :: hs) hCinstall hTinstall hKinstall
                          hSB.bump hSD
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have hCtail := Corr_pop_nonstate hns hmutM hCM
                      have htopnc : ∀ ℓ p cls, top.handler ≠ Handler.custom ℓ p cls := by
                        obtain ⟨⟨_, _, _, hsh⟩, _⟩ := hmutM
                        intro ℓ p cls
                        cases hth : top.handler with
                        | custom _ _ _ => rw [hfrdef, hth] at hsh; exact absurd hsh (by simp)
                        | state _ _ => simp [hth]
                        | throws _ => simp [hth]
                        | transaction _ _ => simp [hth]
                      have hTtail : TCorr τ1 tail := TCorr_pop_nontxn (by
                        obtain ⟨⟨_, _, _, hsh⟩, _⟩ := hmutM
                        intro ℓ Θ
                        cases hth : top.handler with
                        | transaction _ _ => rw [hfrdef, hth] at hsh; exact absurd hsh (by simp)
                        | state _ _ => simp [hth]
                        | throws _ => simp [hth]
                        | custom _ _ _ => simp [hth]) hTM
                      have hKtail : CCorr κ1 tail := CCorr_pop_noncustom htopnc hKM
                      have htaileq : tail = netEffect hs σ1 τ1 κ1 :=
                        updateStates_eq (HMut.tail hmutM) hCtail hTtail hKtail
                      have hstep : exec (F2+1) g1 (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ hKtail, htaileq ▸ (HMut.tail hmutM),
                        hSBM, hSDM⟩
                    obtain ⟨_, hCf, hTf, hKf, hmutf, hSBf, hSDf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1 τ1 κ1, hCf, hTf, hKf, hmutf, hSBf, hSDf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    by_cases hc : ℓ' = g ∧ op' = "raise"
                    · simp only [Option.bind_some, if_pos hc, Option.some.injEq, Prod.mk.injEq,
                        Outcome.term.injEq] at h
                      obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                      obtain ⟨hcn, rfl⟩ := hc; subst ℓ'
                      -- caught: M' raises `(g,raise)` ⇒ machine OP catches the throws frame (id g), aborts to
                      -- the HANDLE's saved (c2,s2) with `ret w`. The abort unwinds only the CONTINUATION; the
                      -- stores stay at the at-raise `σ1`/`τ1`/`κ1` (caught = at-raise, keeping outer puts/writes),
                      -- so the existential HStack is `netEffect hs σ1 τ1 κ1`. The outer 4-tuple over `hs` comes
                      -- from popping the throws install frame (non-state, non-txn, non-custom) off the raised IH.
                      have hns0 : ∀ ℓ s, (Handler.throws ℓ0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                      have hnt0 : ∀ ℓ Θ, (Handler.throws ℓ0) ≠ Handler.transaction ℓ Θ := by intro ℓ Θ; simp
                      have hnc0 : ∀ ℓ p cls, (Handler.throws ℓ0) ≠ Handler.custom ℓ p cls := by intro ℓ p cls; simp
                      have htriple : (Corr σ1 (netEffect hs σ1 τ1 κ1) ∧ TCorr τ1 (netEffect hs σ1 τ1 κ1)
                          ∧ CCorr κ1 (netEffect hs σ1 τ1 κ1) ∧ HMut hs (netEffect hs σ1 τ1 κ1))
                          ∧ StoresBelow g1 σ1 τ1 κ1 ∧ StoresDisjoint σ1 τ1 κ1 := by
                        set fr0 : HFrame := { id := g, handler := Handler.throws ℓ0, savedCode := [], savedStack := [] }
                        have hns : ∀ ℓ s, fr0.handler ≠ Handler.state ℓ s := hns0
                        have hnt : ∀ ℓ Θ, fr0.handler ≠ Handler.transaction ℓ Θ := hnt0
                        have hnc : ∀ ℓ p cls, fr0.handler ≠ Handler.custom ℓ p cls := hnc0
                        obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, _⟩ :=
                          ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ g "raise" w g1 σ1 τ1 κ1 hM (fr0 :: hs)
                            (Corr_install_nonstate fr0 hns hC) (TCorr_install_nontxn fr0 hnt hT)
                            (CCorr_install_noncustom fr0 hnc hK) hSB.bump hSD
                        -- pop the non-{state,txn} throws frame off the raised IH's net-effect 4-tuple.
                        refine ⟨⟨raisedTriple_pop_nontxn hns hnt hnc hCr hTr hmutr |>.1,
                          raisedTriple_pop_nontxn hns hnt hnc hCr hTr hmutr |>.2.1, ?_,
                          raisedTriple_pop_nontxn hns hnt hnc hCr hTr hmutr |>.2.2⟩, hSBr, hSDr⟩
                        -- κ1 mirrors netEffect (fr0::hs) = throws-frame :: netEffect hs; CCorr projects the tail.
                        have := hKr
                        rw [netEffect_cons_throws (show fr0.handler = .throws ℓ0 from rfl)] at this
                        exact CCorr_pop_noncustom (by intro ℓ p cls; simp) this
                      refine ⟨netEffect hs σ1 τ1 κ1, htriple.1.1, htriple.1.2.1, htriple.1.2.2.1, htriple.1.2.2.2,
                        htriple.2.1, htriple.2.2, fun c2 s2 F2 r2 hr2 => ?_⟩
                      set fr2 : HFrame := { id := g, handler := Handler.throws ℓ0, savedCode := c2, savedStack := s2 }
                        with hfrdef
                      have hCinstall2 : Corr σ (fr2 :: hs) := Corr_install_nonstate fr2 hns0 hC
                      have hTinstall2 : TCorr τ (fr2 :: hs) := TCorr_install_nontxn fr2 hnt0 hT
                      have hKinstall2 : CCorr κ (fr2 :: hs) := CCorr_install_noncustom fr2 hnc0 hK
                      obtain ⟨_, _, _, kR2⟩ :=
                        ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ g "raise" w g1 σ1 τ1 κ1 hM (fr2 :: hs) hCinstall2 hTinstall2 hKinstall2 hSB.bump hSD
                      have hthrow : throwOutcome F2 g1 g "raise" w (netEffect (fr2 :: hs) σ1 τ1 κ1) = some r2 := by
                        rw [netEffect_cons_throws (show fr2.handler = .throws ℓ0 from by rw [hfrdef])]
                        simp only [throwOutcome, unwindFind, hfrdef, and_self, if_true]; exact hr2
                      obtain ⟨F1, hF1⟩ := kR2 (Instr.UNMARK :: c2) s2 F2 r2 hthrow
                      exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                    · simp [Option.bind_some, if_neg hc] at h
          | transaction ℓ0 Θ =>
              -- route-B INSTALL a transaction frame: MINT id := g, push (id ↦ Θ) on τ keyed by g, run the
              -- SUBSTITUTED body `M' = subst (vcap g ℓ0) M` at g+1; on a normal return POP the heap (τ1.tail).
              -- A MIRROR of the proven handle-state case, on the τ side (no σ push).
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    have body : ∀ (cc : Code) (ss : Stack) (F2 r2 : _),
                        exec F2 g1 cc (.ret v :: ss) (netEffect hs σ1 τ1.tail κ1) = some r2 →
                        (∃ F', exec F' (g+1) (compile (Comp.subst (Val.vcap g ℓ0) M) (Instr.UNMARK :: cc)) ss
                          ({ id := g, handler := Handler.transaction ℓ0 Θ, savedCode := cc, savedStack := ss } :: hs) = some r2)
                        ∧ Corr σ1 (netEffect hs σ1 τ1.tail κ1) ∧ TCorr τ1.tail (netEffect hs σ1 τ1.tail κ1)
                        ∧ CCorr κ1 (netEffect hs σ1 τ1.tail κ1) ∧ HMut hs (netEffect hs σ1 τ1.tail κ1)
                        ∧ StoresBelow g1 σ1 τ1.tail κ1 ∧ StoresDisjoint σ1 τ1.tail κ1 := by
                      intro cc ss F2 r2 hr2
                      set fr : HFrame := { id := g, handler := Handler.transaction ℓ0 Θ, savedCode := cc, savedStack := ss }
                        with hfrdef
                      have hCinstall : Corr σ (fr :: hs) :=
                        Corr_install_nonstate fr (by rw [hfrdef]; intro ℓ s; simp) hC
                      have hTinstall : TCorr (τ.push g Θ) (fr :: hs) :=
                        TCorr_install ℓ0 Θ fr (by rw [hfrdef]) hT
                      have hKinstall : CCorr κ (fr :: hs) :=
                        CCorr_install_noncustom fr (by rw [hfrdef]; intro ℓ p cls; simp) hK
                      obtain ⟨hsM, hCM, hTM, hKM, hmutM, hSBM, hSDM, kM⟩ :=
                        ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ (τ.push g Θ) κ (.ret v) g1 σ1 τ1 κ1 hM (fr :: hs) hCinstall hTinstall hKinstall
                          hSB.push_txn (hSD.push_txn hSB)
                      obtain ⟨top, tail, rfl⟩ : ∃ top tail, hsM = top :: tail := by
                        cases hsM with | nil => simp [HMut, hfrdef] at hmutM | cons a b => exact ⟨a, b, rfl⟩
                      have htop : ∃ Θ', top.handler = .transaction ℓ0 Θ' := by
                        have hh := hmutM.1.2.2.2
                        cases hth : top.handler with
                        | transaction ℓ1 Θ1 => rw [hfrdef, hth] at hh; simp only at hh; subst hh; exact ⟨Θ1, rfl⟩
                        | state _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | throws _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)
                        | custom _ _ _ => rw [hfrdef, hth] at hh; exact absurd hh (by simp)   -- FrameMut txn/custom = False
                      obtain ⟨Θ', hts⟩ := htop
                      have hTtail := TCorr_pop_txn hts hTM
                      have hCtail : Corr σ1 tail :=
                        Corr_pop_nonstate (by rw [hfrdef]; intro ℓ s; simp) hmutM hCM
                      have hKtail : CCorr κ1 tail :=
                        CCorr_pop_noncustom (by rw [hts]; intro ℓ p cls; simp) hKM
                      have htaileq : tail = netEffect hs σ1 τ1.tail κ1 :=
                        updateStates_eq (HMut.tail hmutM) hCtail hTtail hKtail
                      have hstep : exec (F2+1) g1 (Instr.UNMARK :: cc) (.ret v :: ss) (top :: tail) = some r2 := by
                        simp only [exec]; rw [htaileq]; exact hr2
                      exact ⟨kM (Instr.UNMARK :: cc) ss (F2+1) r2 hstep,
                        htaileq ▸ hCtail, htaileq ▸ hTtail, htaileq ▸ hKtail, htaileq ▸ (HMut.tail hmutM),
                        hSBM.tail_txn, hSDM.tail_txn⟩
                    obtain ⟨_, hCf, hTf, hKf, hmutf, hSBf, hSDf⟩ := body [] [] 1 [.ret v] (by simp only [exec])
                    refine ⟨netEffect hs σ1 τ1.tail κ1, hCf, hTf, hKf, hmutf, hSBf, hSDf, fun c2 s2 F2 r2 hr2 => ?_⟩
                    obtain ⟨⟨F1, hF1⟩, _, _⟩ := body c2 s2 F2 r2 hr2
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, _, _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
      | case a b d =>
          -- ADT sum elim (Unit 6): closed-value scrutinee, PURE reduction. evalD reduces into a branch;
          -- the IH on `subst v branch` carries it; `CASE` exec re-compiles that branch (mirrors SUBST).
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | inl v =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, k⟩ := ihT (Comp.subst v b) g σ τ κ t g' σ' τ' κ' h hs hC hT hK hSB hSD
              refine ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, fun c s F r hr => ?_⟩
              obtain ⟨F', hF'⟩ := k c s F r hr
              exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩
          | inr v =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, k⟩ := ihT (Comp.subst v d) g σ τ κ t g' σ' τ' κ' h hs hC hT hK hSB hSD
              refine ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, fun c s F r hr => ?_⟩
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
          | vcap n ℓ => simp [evalD] at h
          | pair v w =>
              simp only [evalD] at h
              obtain ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, k⟩ :=
                ihT (Comp.subst v (Comp.subst (Val.shift w) b)) g σ τ κ t g' σ' τ' κ' h hs hC hT hK hSB hSD
              refine ⟨hsf, hCf, hTf, hKf, hlenf, hSBf, hSDf, fun c s F r hr => ?_⟩
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
          | vcap n ℓ => simp [evalD] at h
          | fold v =>
              simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
              obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
              exact ⟨hs, hC, hT, hK, HMut.refl hs, hSB, hSD, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩
          | vunit => simp [evalD] at h
          | vint n => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
      | binop op v w =>
          -- δ-rule (#40): on closed vints binop reduces to `term (ret (op.eval a b))` and collapses onto
          -- `RET`, exactly like `unfold (fold v)` above; non-vint operands are `none` (false-by-contradiction).
          cases v <;> cases w <;>
            first
            | (simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
               obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
               exact ⟨hs, hC, hT, hK, HMut.refl hs, hSB, hSD, fun c s F r hr => ⟨F+1, by simp only [compile, exec]; exact hr⟩⟩)
            | simp [evalD] at h
    · -- RAISED PART
      intro M g σ τ κ ℓ op v g' σ' τ' κ' h hs hC hT hK hSB hSD
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | perform cap op2 v2 =>
          -- ID-FIRST raise (route-B, identity-keyed): a `raised` from `perform (vcap n2 ℓ2) op2 v2` means
          -- IDENTITY n2 resolved to NO resumptive frame OR to a frame whose kind can't handle op2 — a
          -- state frame with op ∉ {get,put}, a txn frame with a non-stm op, a custom frame with no matching
          -- clause, or n2 in no store. In ALL of these the machine's stateUpdate/txnUpdate/customUpdate
          -- (each keyed by n2) return none and the OP falls to the throw path. The net-effect is the
          -- identity (no store changed), so the existential HStack is `hs`; evalD's perform arm does not
          -- advance the counter ⇒ g' = g. Unwrap the cap value (non-vcap caps are vacuous via `h`).
          obtain ⟨n2, ℓ2, rfl⟩ : ∃ n ℓ, cap = Val.vcap n ℓ := by
            cases cap <;> first | exact ⟨_, _, rfl⟩ | simp [evalD] at h
          simp only [evalD] at h
          -- A single helper closing every raise-subcase: stores unchanged ⇒ netEffect = hs, machine OP
          -- (dispatch identity n2) misses stateUpdate/txnUpdate/customUpdate (id-first, no isBuiltinOp)
          -- and falls to unwindFind = throwOutcome.
          have close : ∀ (hns : stateUpdate n2 op2 v2 hs = none) (hnt : txnUpdate n2 op2 v2 hs = none)
              (hnc : customUpdate n2 op2 v2 hs = none),
              (Corr σ (netEffect hs σ τ κ) ∧ TCorr τ (netEffect hs σ τ κ) ∧ CCorr κ (netEffect hs σ τ κ) ∧
                HMut hs (netEffect hs σ τ κ)) ∧ StoresBelow g σ τ κ ∧ StoresDisjoint σ τ κ ∧
              ∀ c s F r, throwOutcome F g n2 op2 v2 (netEffect hs σ τ κ) = some r →
                ∃ F', exec F' g (compile (.perform (.vcap n2 ℓ2) op2 v2) c) s hs = some r := by
            intro hns hnt hnc
            have hus : netEffect hs σ τ κ = hs := updateStates_self hC hT hK
            refine ⟨⟨by rw [hus]; exact hC, by rw [hus]; exact hT, by rw [hus]; exact hK,
              by rw [hus]; exact HMut.refl hs⟩, hSB, hSD, fun c s F r hr => ?_⟩
            rw [hus] at hr
            refine ⟨F+1, ?_⟩
            simp only [compile, exec, hns, hnt, hnc]; simpa only [throwOutcome] using hr
          -- n2 resolves against σ first (evalD's `match σ.get? n2`).
          cases hg : σ.get? n2 with
          | some sv =>
              rw [hg] at h
              -- state frame at n2: get/put would SERVICE (term), so a raise needs op ∉ {get,put} (fail-loud).
              by_cases hop : op2 = "get"
              · subst hop; simp only [if_pos rfl] at h; simp at h
              · by_cases hop2 : op2 = "put"
                · subst hop2; simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl] at h; simp at h
                · -- op2 the state frame can't handle ⇒ raise. Machine: stateUpdate hits n2 (state frame)
                  -- but op ∉ {get,put} ⇒ stateUpdate = none (fail-loud mirror); txn/custom miss (n2 in σ).
                  simp only [if_neg hop, if_neg hop2, Option.some.injEq, Prod.mk.injEq,
                    Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                  -- state frame at n2 ⇒ StoresDisjoint rules out a txn/custom frame at n2 (id-uniqueness);
                  -- transport via TCorr/CCorr.get? to the hs side.
                  have hne : σ.get? n2 ≠ none := by rw [hg]; exact Option.some_ne_none _
                  exact close (stateUpdate_none_of_non_getput n2 v2 hs hop hop2)
                    (txnUpdate_none_of_hsTxn_none (TCorr.get? hT n2 ▸ ((hSD n2).1 hne).1))
                    (customUpdate_none_of_hsCustom_none (CCorr.get? hK n2 ▸ ((hSD n2).1 hne).2))
          | none =>
          rw [hg] at h
          cases hgt : τ.get? n2 with
          | some Θ =>
              rw [hgt] at h
              -- txn frame at n2: an stm op services (term), so a raise needs a non-stm op (fail-loud).
              by_cases hopt : isTxnOp op2 = true
              · simp only [hopt, if_true] at h; simp at h
              · rw [Bool.not_eq_true] at hopt
                simp only [hopt, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq,
                  Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                -- non-stm op is not get/put either (they're not stm ops but the state store missed n2, so
                -- stateUpdate misses via hsState = none). txnUpdate: n2 IS a txn frame but op non-stm ⇒ none.
                -- txn frame at n2 ⇒ StoresDisjoint rules out a custom frame at n2 (id-uniqueness).
                have hne : τ.get? n2 ≠ none := by rw [hgt]; exact Option.some_ne_none _
                exact close
                  (stateUpdate_none_of_get?_none (Corr.get? hC n2 ▸ hg))
                  (txnUpdate_none_of_non_txnop n2 v2 hs hopt)
                  (customUpdate_none_of_hsCustom_none (CCorr.get? hK n2 ▸ ((hSD n2).2.1 hne).2))
          | none =>
          rw [hgt] at h
          -- n2 resolves against κ (custom), or n2 in no store: raise if no matching clause / no frame.
          cases hck : κ.get? n2 with
          | none =>
              simp only [hck, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
              obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
              exact close (stateUpdate_none_of_get?_none (Corr.get? hC n2 ▸ hg))
                (txnUpdate_none_of_hsTxn_none (TCorr.get? hT n2 ▸ hgt))
                (customUpdate_none_of_hsCustom_none (CCorr.get? hK n2 ▸ hck))
          | some pcls =>
              obtain ⟨p, cls⟩ := pcls
              rw [hck] at h
              cases hcl : cls.find? (fun clause => clause.1.op == op2) with
              | some clause =>
                  -- clause HIT but the raise propagates: the custom CLAUSE BODY itself raises (deep-handler
                  -- recursion at the residual row). evalD ran `evalD … κ clauseBody = raised`; the machine's
                  -- OP arm serviced via customUpdate ⇒ `exec (compile clauseBody) c`, which raises. Recurse
                  -- via ihR on the clause body against the LIVE stores (κ unchanged, frame kept).
                  simp only [hcl] at h
                  have hgCustom : hsCustom hs n2 = some (p, cls) := by rw [← CCorr.get? hK n2]; exact hck
                  have hns : stateUpdate n2 op2 v2 hs = none :=
                    stateUpdate_none_of_get?_none (Corr.get? hC n2 ▸ hg)
                  have hnt : txnUpdate n2 op2 v2 hs = none :=
                    txnUpdate_none_of_hsTxn_none (TCorr.get? hT n2 ▸ hgt)
                  by_cases hupd : clause.1.updates = true
                  · simp only [hupd, if_true] at h
                    split at h <;> simp_all
                  · have hupd0 : clause.1.updates = false := Bool.eq_false_of_not_eq_true hupd
                    simp only [hupd0, Bool.false_eq_true, if_false] at h
                    have hcu : customUpdate n2 op2 v2 hs
                        = some (Comp.subst p (Comp.subst (Val.shift v2) clause.2), hs) :=
                      customUpdate_service hgCustom hcl hupd0
                    obtain ⟨hpair, hSBr, hSDr, kR⟩ :=
                      ihR (Comp.subst p (Comp.subst (Val.shift v2) clause.2)) g σ τ κ ℓ op v g' σ' τ' κ' h hs hC hT hK hSB hSD
                    exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
                      obtain ⟨F1, hF1⟩ := kR c s F r hr
                      exact ⟨F1+1, by
                        simp only [compile, exec, hns, hnt, hcu]
                        exact hF1⟩⟩
              | none =>
                  simp only [hcl, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                  exact close (stateUpdate_none_of_get?_none (Corr.get? hC n2 ▸ hg))
                    (txnUpdate_none_of_hsTxn_none (TCorr.get? hT n2 ▸ hgt))
                    (customUpdate_none_of_clause_miss (CCorr.get? hK n2 ▸ hck) hcl)
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe g σ τ κ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                obtain ⟨hpair, hSBr, hSDr, kR⟩ := ihR M g σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM hs hC hT hK hSB hSD
                exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
                  obtain ⟨F1, hF1⟩ := kR (Instr.SUBST N :: c) s F r hr
                  exact ⟨F1, by simpa [compile] using hF1⟩⟩
            | (.term (.ret v0), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hKM, hmutM, hSBM, hSDM, kM⟩ := ihT M g σ τ κ (.ret v0) g1 σ1 τ1 κ1 hM hs hC hT hK hSB hSD
                -- the inner raise is over hsM (HMut hs); re-base via `netEffect_congr_HMut` so the inner
                -- `ihR` over `netEffect hsM σ' τ' κ'` reuses the outer `hr` over `netEffect hs σ' τ' κ'`.
                obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, kR⟩ := ihR (Comp.subst v0 N) g1 σ1 τ1 κ1 ℓ op v g' σ' τ' κ' h hsM hCM hTM hKM hSBM hSDM
                have hreb : netEffect hsM σ' τ' κ' = netEffect hs σ' τ' κ' :=
                  netEffect_congr_HMut σ' τ' κ' hmutM hCr hTr hKr
                refine ⟨⟨hreb ▸ hCr, hreb ▸ hTr, hreb ▸ hKr, HMut.trans hmutM (hreb ▸ hmutr)⟩, hSBr, hSDr, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR c s F r (by rw [hreb]; exact hr)
                have hstep : exec (F1+1) g1 (Instr.SUBST N :: c) (.ret v0 :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.SUBST N :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | vthunk M =>
              simp only [evalD] at h
              obtain ⟨hpair, hSBr, hSDr, kR⟩ := ihR M g σ τ κ ℓ op v g' σ' τ' κ' h hs hC hT hK hSB hSD
              exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
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
          cases hM : evalD fe g σ τ κ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                obtain ⟨hpair, hSBr, hSDr, kR⟩ := ihR M g σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM hs hC hT hK hSB hSD
                exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
                  obtain ⟨F1, hF1⟩ := kR (Instr.APP v0 :: c) s F r hr
                  exact ⟨F1, by simpa [compile] using hF1⟩⟩
            | (.term (.lam N), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨hsM, hCM, hTM, hKM, hmutM, hSBM, hSDM, kM⟩ := ihT M g σ τ κ (.lam N) g1 σ1 τ1 κ1 hM hs hC hT hK hSB hSD
                obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, kR⟩ := ihR (Comp.subst v0 N) g1 σ1 τ1 κ1 ℓ op v g' σ' τ' κ' h hsM hCM hTM hKM hSBM hSDM
                have hreb : netEffect hsM σ' τ' κ' = netEffect hs σ' τ' κ' :=
                  netEffect_congr_HMut σ' τ' κ' hmutM hCr hTr hKr
                refine ⟨⟨hreb ▸ hCr, hreb ▸ hTr, hreb ▸ hKr, HMut.trans hmutM (hreb ▸ hmutr)⟩, hSBr, hSDr, fun c s F r hr => ?_⟩
                obtain ⟨F1, hF1⟩ := kR c s F r (by rw [hreb]; exact hr)
                have hstep : exec (F1+1) g1 (Instr.APP v0 :: c) (.lam N :: s) hsM = some r := by
                  simp only [exec]; exact hF1
                obtain ⟨F2, hF2⟩ := kM (Instr.APP v0 :: c) s (F1+1) r hstep
                exact ⟨F2, by simpa [compile] using hF2⟩
            | (.term (.ret w), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
      | handle h0 M =>
          simp only [evalD] at h
          cases h0 with
          | custom ℓ0 p0 cls0 =>
              -- route-B INSTALL (raised, FORWARD): MINT id := g, push (id↦(p0,cls0)) on κ, run M' at g+1;
              -- a raise FORWARDS past the custom frame (custom never catches a throws-raise), popping the
              -- pushed κ entry (κ1.tail). Custom carries no state/heap ⇒ σ/τ pass through. Mirrors the throws
              -- FORWARD case with a κ push/pop.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ τ (κ.push g p0 cls0) (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                    have hns0 : ∀ ℓ s, (Handler.custom ℓ0 p0 cls0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                    have hnt0 : ∀ ℓ Θ, (Handler.custom ℓ0 p0 cls0) ≠ Handler.transaction ℓ Θ := by intro ℓ Θ; simp
                    have htriple : (Corr σ1 (netEffect hs σ1 τ1 κ1.tail) ∧ TCorr τ1 (netEffect hs σ1 τ1 κ1.tail)
                        ∧ CCorr κ1.tail (netEffect hs σ1 τ1 κ1.tail) ∧ HMut hs (netEffect hs σ1 τ1 κ1.tail))
                        ∧ StoresBelow g1 σ1 τ1 κ1.tail ∧ StoresDisjoint σ1 τ1 κ1.tail := by
                      set fr0 : HFrame := { id := g, handler := Handler.custom ℓ0 p0 cls0, savedCode := [], savedStack := [] }
                        with hfr0
                      obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, _⟩ :=
                        ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ (κ.push g p0 cls0) ℓ' op' w g1 σ1 τ1 κ1 hM (fr0 :: hs)
                          (Corr_install_nonstate fr0 (by rw [hfr0]; exact hns0) hC)
                          (TCorr_install_nontxn fr0 (by rw [hfr0]; exact hnt0) hT)
                          (CCorr_install ℓ0 p0 cls0 fr0 (by rw [hfr0]) hK)
                          hSB.push_custom (hSD.push_custom hSB)
                      obtain ⟨hCt, hTt, hMt⟩ := raisedTriple_pop_custom
                        (show fr0.handler = .custom ℓ0 p0 cls0 from by rw [hfr0]) hCr hTr hmutr
                      refine ⟨⟨hCt, hTt, ?_, hMt⟩, hSBr.tail_custom, hSDr.tail_custom⟩
                      obtain ⟨top, heq, p', cls', htop⟩ :=
                        netEffect_cons_custom (show fr0.handler = .custom ℓ0 p0 cls0 from rfl)
                      rw [heq] at hKr
                      exact CCorr_pop_custom htop hKr
                    refine ⟨htriple.1, htriple.2.1, htriple.2.2, fun c s F r hr => ?_⟩
                    set fr : HFrame := { id := g, handler := Handler.custom ℓ0 p0 cls0, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, _, _, kR⟩ := ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ (κ.push g p0 cls0) ℓ' op' w g1 σ1 τ1 κ1 hM (fr :: hs)
                      (Corr_install_nonstate fr (by rw [hfrdef]; exact hns0) hC)
                      (TCorr_install_nontxn fr (by rw [hfrdef]; exact hnt0) hT)
                      (CCorr_install ℓ0 p0 cls0 fr (by rw [hfrdef]) hK)
                      hSB.push_custom (hSD.push_custom hSB)
                    have hfwd : throwOutcome F g1 ℓ' op' w (netEffect (fr :: hs) σ1 τ1 κ1) = some r := by
                      obtain ⟨top, heq, p', cls', htop⟩ :=
                        netEffect_cons_custom (show fr.handler = .custom ℓ0 p0 cls0 from by rw [hfrdef])
                      rw [heq]
                      rw [throwOutcome_cons_nonthrows _ _ _ _ _ _ _ (by rw [htop]; intro ℓ; simp)]
                      exact hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.ret v0), _, _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
          | state ℓ0 s0 =>
              -- route-B INSTALL (raised): MINT id := g, run M' = subst (vcap g ℓ0) M at g+1 under σ.push g s0;
              -- a raise FORWARDS, popping the pushed σ entry (σ1.tail). The frame's id is g.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                    -- at-raise 4-TUPLE: one IH over a dummy install frame, popped through the state frame.
                    -- κ passes unchanged (state install doesn't touch custom frames); CCorr pops noncustom.
                    have htriple : (Corr σ1.tail (netEffect hs σ1.tail τ1 κ1) ∧ TCorr τ1 (netEffect hs σ1.tail τ1 κ1)
                        ∧ CCorr κ1 (netEffect hs σ1.tail τ1 κ1) ∧ HMut hs (netEffect hs σ1.tail τ1 κ1))
                        ∧ StoresBelow g1 σ1.tail τ1 κ1 ∧ StoresDisjoint σ1.tail τ1 κ1 := by
                      set fr0 : HFrame := { id := g, handler := Handler.state ℓ0 s0, savedCode := [], savedStack := [] }
                        with hfr0
                      obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, _⟩ :=
                        ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) (σ.push g s0) τ κ ℓ' op' w g1 σ1 τ1 κ1 hM (fr0 :: hs)
                          (Corr_install ℓ0 s0 fr0 (by rw [hfr0]) hC)
                          (TCorr_install_nontxn fr0 (by rw [hfr0]; intro ℓ Θ; simp) hT)
                          (CCorr_install_noncustom fr0 (by rw [hfr0]; intro ℓ p cls; simp) hK)
                          hSB.push_state (hSD.push_state hSB)
                      obtain ⟨hCt, hTt, hMt⟩ := raisedTriple_pop_state (by rw [hfr0]) hCr hTr hmutr
                      refine ⟨⟨hCt, hTt, ?_, hMt⟩, hSBr.tail_state, hSDr.tail_state⟩
                      -- κ1 mirrors netEffect (state-frame :: hs); state install/net-effect keeps custom frames.
                      have hproj : hsCustoms (netEffect (fr0 :: hs) σ1 τ1 κ1) = hsCustoms (netEffect hs σ1.tail τ1 κ1) := by
                        rw [hsCustoms_netEffect, hsCustoms_netEffect]
                        simp only [updateCustoms, hfr0, hsCustoms]
                      unfold CCorr at hKr ⊢; exact hKr.trans hproj
                    refine ⟨htriple.1, htriple.2.1, htriple.2.2, fun c s F r hr => ?_⟩
                    set fr : HFrame := { id := g, handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, _, _, kR⟩ := ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) (σ.push g s0) τ κ ℓ' op' w g1 σ1 τ1 κ1 hM (fr :: hs)
                      (Corr_install ℓ0 s0 fr (by rw [hfrdef]) hC)
                      (TCorr_install_nontxn fr (by rw [hfrdef]; intro ℓ Θ; simp) hT)
                      (CCorr_install_noncustom fr (by rw [hfrdef]; intro ℓ p cls; simp) hK)
                      hSB.push_state (hSD.push_state hSB)
                    have hfwd : throwOutcome F g1 ℓ' op' w (netEffect (fr :: hs) σ1 τ1 κ1) = some r := by
                      have hskip : throwOutcome F g1 ℓ' op' w (netEffect (fr :: hs) σ1 τ1 κ1)
                          = throwOutcome F g1 ℓ' op' w (netEffect hs σ1.tail τ1 κ1) := by
                        cases σ1 with
                        | nil =>
                            unfold netEffect; rw [updateStates]; simp only [hfrdef, List.tail]
                            rw [updateTxns_cons_state τ1 (show ({ id := g, handler := Handler.state ℓ0 s0, savedCode := c, savedStack := s : HFrame } : HFrame).handler = .state ℓ0 s0 from rfl)]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ _ (by simp)
                        | cons p σ1' =>
                            obtain ⟨ℓa, wa⟩ := p
                            unfold netEffect; rw [updateStates]; simp only [hfrdef, List.tail]
                            rw [updateTxns_cons_state τ1 (show ({ id := g, handler := Handler.state ℓ0 wa, savedCode := c, savedStack := s : HFrame } : HFrame).handler = .state ℓ0 wa from rfl)]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ _ (by simp)
                      rw [hskip]; exact hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.ret v0), _, _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
          | throws ℓ0 =>
              -- route-B INSTALL (raised, FORWARD): MINT id := g, run M' at g+1; the throws frame CATCHES
              -- only its own identity g (id-keyed) — a raise with ℓ' ≠ g (or op' ≠ "raise") FORWARDS past it.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ' = g ∧ op' = "raise"
                    · simp [if_pos hk] at h
                    · simp only [if_neg hk, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                      have hns0 : ∀ ℓ s, (Handler.throws ℓ0) ≠ Handler.state ℓ s := by intro ℓ s; simp
                      have hnt0 : ∀ ℓ Θ, (Handler.throws ℓ0) ≠ Handler.transaction ℓ Θ := by intro ℓ Θ; simp
                      have hnc0 : ∀ ℓ p cls, (Handler.throws ℓ0) ≠ Handler.custom ℓ p cls := by intro ℓ p cls; simp
                      have htriple : (Corr σ1 (netEffect hs σ1 τ1 κ1) ∧ TCorr τ1 (netEffect hs σ1 τ1 κ1)
                          ∧ CCorr κ1 (netEffect hs σ1 τ1 κ1) ∧ HMut hs (netEffect hs σ1 τ1 κ1))
                          ∧ StoresBelow g1 σ1 τ1 κ1 ∧ StoresDisjoint σ1 τ1 κ1 := by
                        set fr0 : HFrame := { id := g, handler := Handler.throws ℓ0, savedCode := [], savedStack := [] } with hfr0
                        obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, _⟩ :=
                          ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM (fr0 :: hs)
                            (Corr_install_nonstate fr0 hns0 hC) (TCorr_install_nontxn fr0 hnt0 hT)
                            (CCorr_install_noncustom fr0 hnc0 hK) hSB.bump hSD
                        obtain ⟨hCt, hTt, hMt⟩ := raisedTriple_pop_nontxn hns0 hnt0 hnc0 hCr hTr hmutr
                        refine ⟨⟨hCt, hTt, ?_, hMt⟩, hSBr, hSDr⟩
                        rw [netEffect_cons_throws (show fr0.handler = .throws ℓ0 from by rw [hfr0])] at hKr
                        exact CCorr_pop_noncustom (by intro ℓ p cls; simp) hKr
                      refine ⟨htriple.1, htriple.2.1, htriple.2.2, fun c s F r hr => ?_⟩
                      set fr : HFrame := { id := g, handler := Handler.throws ℓ0, savedCode := c, savedStack := s }
                        with hfrdef
                      obtain ⟨_, _, _, kR⟩ := ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM (fr :: hs)
                        (Corr_install_nonstate fr hns0 hC) (TCorr_install_nontxn fr hnt0 hT)
                        (CCorr_install_noncustom fr hnc0 hK) hSB.bump hSD
                      have hfwd : throwOutcome F g1 ℓ' op' w (netEffect (fr :: hs) σ1 τ1 κ1) = some r := by
                        rw [netEffect_cons_throws (show fr.handler = .throws ℓ0 from by rw [hfrdef])]
                        have hknf : ¬ (g = ℓ' ∧ op' = "raise") := fun h' => hk ⟨h'.1.symm, h'.2⟩
                        simp only [throwOutcome, unwindFind, hfrdef, if_neg hknf]; exact hr
                      obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                      exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.ret v0), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
          | transaction ℓ0 Θ =>
              -- route-B INSTALL (raised, FORWARD): MINT id := g, push τ.push g Θ, run M' at g+1; a raise
              -- FORWARDS, popping the pushed heap (τ1.tail) — ROLLBACK IS FREE (ADR-0031 D4). Mirror of state.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                    -- transaction-install + raise FORWARD: pop the pushed heap (τ1.tail). The txn frame
                    -- does NOT catch a foreign raise (its identity g is not the target), so the heap is
                    -- discarded with the frame — ROLLBACK IS FREE (ADR-0031 D4). Mirror of the state forward.
                    -- κ passes unchanged (txn install doesn't touch custom frames); CCorr pops noncustom.
                    have htriple : (Corr σ1 (netEffect hs σ1 τ1.tail κ1) ∧ TCorr τ1.tail (netEffect hs σ1 τ1.tail κ1)
                        ∧ CCorr κ1 (netEffect hs σ1 τ1.tail κ1) ∧ HMut hs (netEffect hs σ1 τ1.tail κ1))
                        ∧ StoresBelow g1 σ1 τ1.tail κ1 ∧ StoresDisjoint σ1 τ1.tail κ1 := by
                      set fr0 : HFrame := { id := g, handler := Handler.transaction ℓ0 Θ, savedCode := [], savedStack := [] }
                        with hfr0
                      obtain ⟨⟨hCr, hTr, hKr, hmutr⟩, hSBr, hSDr, _⟩ :=
                        ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ (τ.push g Θ) κ ℓ' op' w g1 σ1 τ1 κ1 hM (fr0 :: hs)
                          (Corr_install_nonstate fr0 (by rw [hfr0]; intro ℓ s; simp) hC)
                          (TCorr_install ℓ0 Θ fr0 (by rw [hfr0]) hT)
                          (CCorr_install_noncustom fr0 (by rw [hfr0]; intro ℓ p cls; simp) hK)
                          hSB.push_txn (hSD.push_txn hSB)
                      obtain ⟨hCt, hTt, hMt⟩ := raisedTriple_pop_txn (by rw [hfr0]) hCr hTr hmutr
                      refine ⟨⟨hCt, hTt, ?_, hMt⟩, hSBr.tail_txn, hSDr.tail_txn⟩
                      have hproj : hsCustoms (netEffect (fr0 :: hs) σ1 τ1 κ1) = hsCustoms (netEffect hs σ1 τ1.tail κ1) := by
                        rw [hsCustoms_netEffect, hsCustoms_netEffect]
                        simp only [updateCustoms, hfr0, hsCustoms]
                      unfold CCorr at hKr ⊢; exact hKr.trans hproj
                    refine ⟨htriple.1, htriple.2.1, htriple.2.2, fun c s F r hr => ?_⟩
                    set fr : HFrame := { id := g, handler := Handler.transaction ℓ0 Θ, savedCode := c, savedStack := s }
                      with hfrdef
                    obtain ⟨_, _, _, kR⟩ := ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ (τ.push g Θ) κ ℓ' op' w g1 σ1 τ1 κ1 hM (fr :: hs)
                      (Corr_install_nonstate fr (by rw [hfrdef]; intro ℓ s; simp) hC)
                      (TCorr_install ℓ0 Θ fr (by rw [hfrdef]) hT)
                      (CCorr_install_noncustom fr (by rw [hfrdef]; intro ℓ p cls; simp) hK)
                      hSB.push_txn (hSD.push_txn hSB)
                    have hfwd : throwOutcome F g1 ℓ' op' w (netEffect (fr :: hs) σ1 τ1 κ1) = some r := by
                      -- the txn install frame is skipped by the throws-unwind; the heap τ1.tail is what
                      -- the popped triple sees, and netEffect over the txn frame copies it through.
                      have hskip : throwOutcome F g1 ℓ' op' w (netEffect (fr :: hs) σ1 τ1 κ1)
                          = throwOutcome F g1 ℓ' op' w (netEffect hs σ1 τ1.tail κ1) := by
                        cases τ1 with
                        | nil =>
                            unfold netEffect; rw [updateStates_cons_txn σ1 (show fr.handler = .transaction ℓ0 Θ from by rw [hfrdef])]
                            simp only [updateTxns, hfrdef, List.tail]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ _ (by simp)
                        | cons p τ1' =>
                            obtain ⟨ℓa, Θa⟩ := p
                            unfold netEffect; rw [updateStates_cons_txn σ1 (show fr.handler = .transaction ℓ0 Θ from by rw [hfrdef])]
                            simp only [updateTxns, hfrdef, List.tail]
                            exact throwOutcome_cons_nonthrows _ _ _ _ _ _ _ (by simp)
                      rw [hskip]; exact hr
                    obtain ⟨F1, hF1⟩ := kR (Instr.UNMARK :: c) s F r hfwd
                    exact ⟨F1+1, by simp only [compile, exec, Handler.label]; exact hF1⟩
                | (.term (.ret v0), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
      | case a b d =>
          -- ADT sum elim (Unit 6) raising: the chosen branch raises. `ihR` on `subst v branch` carries
          -- the at-raise triple + throwOutcome; the `CASE` exec bumps one fuel to re-compile the branch.
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | inl sv =>
              simp only [evalD] at h
              obtain ⟨hpair, hSBr, hSDr, kR⟩ := ihR (Comp.subst sv b) g σ τ κ ℓ op v g' σ' τ' κ' h hs hC hT hK hSB hSD
              exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
                obtain ⟨F', hF'⟩ := kR c s F r hr; exact ⟨F'+1, by simp only [compile, exec]; exact hF'⟩⟩
          | inr sv =>
              simp only [evalD] at h
              obtain ⟨hpair, hSBr, hSDr, kR⟩ := ihR (Comp.subst sv d) g σ τ κ ℓ op v g' σ' τ' κ' h hs hC hT hK hSB hSD
              exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
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
          | vcap n ℓ => simp [evalD] at h
          | pair sv sw =>
              simp only [evalD] at h
              obtain ⟨hpair, hSBr, hSDr, kR⟩ :=
                ihR (Comp.subst sv (Comp.subst (Val.shift sw) b)) g σ τ κ ℓ op v g' σ' τ' κ' h hs hC hT hK hSB hSD
              exact ⟨hpair, hSBr, hSDr, fun c s F r hr => by
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
          | vcap n ℓ => simp [evalD] at h
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
      | binop op v w =>
          -- δ-rule (#40): binop reduces to `term (ret (op.eval a b))` on closed vints, `none` otherwise —
          -- NEVER `raised`, so every operand shape is false-by-contradiction here.
          cases v <;> cases w <;> simp [evalD] at h


/-- Headline: compiling a closed computation and running it on the empty stack/store yields exactly
`[t]` where `evalD n [] M = some (.term t, σ')` (the convergent spine, now over the resumptive-state
store-thread). `compile_correct` analogue of `Bang.Calc`; the `c=[]`, `s=[]`, `hs=[]` corollary of
`sim` (`Corr [] []` holds by `rfl`, the empty store mirrors the empty HStack). -/
theorem compile_correct (n : Nat) (M : Comp) (t : Comp) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (h : evalD n 0 [] [] [] M = some (.term t, g', σ', τ', κ')) :
    ∃ F, exec F 0 (compile M []) [] [] = some [t] := by
  have hbase : exec 1 g' [] (t :: []) [] = some [t] := by simp [exec]
  obtain ⟨hsf, _, _, _, hmutf, _, _, k⟩ := (sim n).1 M 0 [] [] [] t g' σ' τ' κ' h [] rfl rfl rfl StoresBelow.nil StoresDisjoint.nil
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
  exec fuel 0 (compile M []) [] [] = some [.ret v] ∧ Source.eval fuel M = .done v

-- ─── PURE axis (let / app / force) ───────────────────────────────────────────

/-- `(λ. ret #0) 5` ⇒ `5` — β through `LAMI`/`APP`. -/
example : Agree 12 (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.vint 5) := ⟨by rfl, by rfl⟩

/-- `let x = (λ.ret #0) 5 in ret x` ⇒ `5` — `SUBST` over an applied lambda. -/
example : Agree 16 (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0))) (.vint 5) :=
  ⟨by rfl, by rfl⟩

/-- `force (thunk (ret 9))` ⇒ `9` — `force`∘`vthunk` collapses to the body. -/
example : Agree 12 (.force (.vthunk (.ret (.vint 9)))) (.vint 9) := ⟨by rfl, by rfl⟩

-- ─── THROWS axis (caught + uncaught) ─────────────────────────────────────────

/-- `handle (throws ℓ) (raise 7)` ⇒ `7` — the deep handler catches and aborts with the payload.
route-B: the cap is the handle-bound `vvar 0` (resolved to `vcap g ℓ` at the mint). -/
example : Agree 20 (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 7))) (.vint 7) := ⟨by rfl, by rfl⟩

/-- DEEP throws: `handle (throws ℓ) (let _ = raise 7 in 99)` ⇒ `7` — the handler reaches PAST a
`letF` frame and DISCARDS the captured continuation (`99` is never returned). -/
example : Agree 24 (.handle (.throws 0) (.letC (.perform (.vvar 0) "raise" (.vint 7)) (.ret (.vint 99)))) (.vint 7) :=
  ⟨by rfl, by rfl⟩

/-- UNCAUGHT `raise` (no handler in scope) yields NO observable value — so it falls OUTSIDE
`Agree`. Both reps signal it: the machine gets STUCK (`exec = none`), the kernel routes the
free-`vcap` perform to the DEFINED terminal `.escapedCap` (ADR-0063 — a `perform (vcap …)` with
no installed frame is a defined fail-loud escape, not genuine stuck). The axis is covered by
asserting that shared non-value outcome. route-B: a FREE `vcap 0 0` (no frame with identity 0). -/
example : exec 20 0 (compile (.perform (.vcap 0 0) "raise" (.vint 7)) []) [] [] = none := by rfl
example : Source.eval 20 (Comp.perform (.vcap 0 0) "raise" (.vint 7)) = .escapedCap := by rfl

-- ─── STATE axis (get-default / put-then-get / persist-past-caught-throw) ──────

/-- `handle (state ℓ 5) (get ())` ⇒ `5` — read the initial state. -/
example : Agree 40 (.handle (.state 1 (.vint 5)) (.perform (.vvar 0) "get" .vunit)) (.vint 5) := ⟨by rfl, by rfl⟩

/-- **OP-PRIORITY regression (ADR-0085 Stage 4, resolution A — pins the fork, not just the prose).**
A custom handler keyed with the BUILT-IN op `"get"` sits INSIDE a `state` frame; `get` performed on the
STATE cap is serviced by the STATE frame (⇒ `7`), and the inner custom `"get"` clause is BYPASSED. This
witnesses that `evalD`'s op-priority (`if get / elif put / elif isTxnOp / else custom`) and the machine's
`isBuiltinOp` guard AGREE: a built-in op is NEVER served by a like-named custom clause. Were the guard
absent (frame-priority), the machine's OP arm could hit the custom `"get"` clause and diverge from
`evalD`. Both sides yield `7` — the raise/builtin path wins, exactly as the calculation demands. -/
example : Agree 200
    (.handle (.state 5 (.vint 7))
      (.handle (.custom 1 (.vint 100) [(.plain "get", .binop .add (.vvar 0) (.vvar 1))])
        (.perform (.vvar 1) "get" .vunit))) (.vint 7) := ⟨by rfl, by rfl⟩

/-- `handle (state ℓ 0) (let _ = put 7 in get ())` ⇒ `7` — the RESUMPTIVE handler KEEPS the captured
`letF` continuation and threads the store; `get` reads the `put`. The `get` is under the `letC`
binder, so the handle-bound cap is `vvar 1` there (the `put` in the `letC` head is `vvar 0`). -/
example : Agree 80
    (.handle (.state 1 (.vint 0)) (.letC (.perform (.vvar 0) "put" (.vint 7)) (.perform (.vvar 1) "get" .vunit)))
    (.vint 7) := ⟨by rfl, by rfl⟩

/-- OUTER STATE PERSISTS PAST A CAUGHT THROW: `handle (state ℓ 0) (put 7; handle (throws) (raise);
get)` ⇒ `7`. The inner zero-shot throw is caught and discarded, but the outer resumptive store
survives — `get` still sees the `put 7`. The interaction the resumptive/zero-shot split must get right.
de Bruijn: outer state cap is `vvar 0` at `put`, `vvar 2` at `get` (two `letC` binders deep); the inner
throws cap is its own handle's `vvar 0`. -/
example : Agree 100
    (.handle (.state 1 (.vint 0))
      (.letC (.perform (.vvar 0) "put" (.vint 7))
        (.letC (.handle (.throws 0) (.perform (.vvar 0) "raise" .vunit))
          (.perform (.vvar 2) "get" .vunit))))
    (.vint 7) := ⟨by rfl, by rfl⟩

-- ─── TRANSACTION axis (new+read heap-thread / abort-rollback) ─────────────────

/-- `handle (transaction ℓ []) (newTVar 9; readTVar 0)` ⇒ `9` — allocate then read back; the heap
threads through both ops (ADR-0031 D4). -/
example : Agree 40
    (.handle (.transaction 2 []) (.letC (.perform (.vvar 0) "newTVar" (.vint 9)) (.perform (.vvar 1) "readTVar" (.vvar 0))))
    (.vint 9) := ⟨by rfl, by rfl⟩

/-- ABORT-ROLLBACK: an outer `throws` wraps `transaction (newTVar 100; writeTVar 0:=70; raise 100)`.
The `raise` is FOREIGN to the transaction frame, so it escapes it (zero-shot) — the threaded heap with
the `writeTVar 70` is DISCARDED with the frame (never commits). The abort payload `100` is the ORIGINAL
balance, the observable proof the write rolled back. -/
example : Agree 80
    (.handle (.throws 0)
      (.handle (.transaction 2 [])
        (.letC (.perform (.vvar 0) "newTVar" (.vint 100))
          (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 70)))
            (.perform (.vvar 3) "raise" (.vint 100))))))
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
example : evalD 12 0 [] [] [] (.case (.inl (.vint 5)) (.ret (.vvar 0)) (.ret (.vint 99)))
    = some (.term (.ret (.vint 5)), 0, [], [], []) := by rfl
example : evalD 14 0 [] [] [] (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1)))
    = some (.term (.ret (.vint 3)), 0, [], [], []) := by rfl
example : evalD 12 0 [] [] [] (.unfold (.fold (.vint 8)))
    = some (.term (.ret (.vint 8)), 0, [], [], []) := by rfl

/-! ## The D1-A bridge: `evalD ≡ Source.eval` (two-part, with handlers)

`run_evalD` is the **two-part** big/small-step simulation: a `term` part (M runs to
its terminal under context `K`) AND a `raised` part (M raises an op the kernel
`dispatch`es — the `THROW ↔ dispatch` correspondence). Subst-vs-subst ⇒ a plain
simulation, no cross-rep logical relation (the (b) payoff). `evalD_agrees_source`
(`K = []`, `ret v`) is the headline tying the calculated machine to the kernel's
type-safety-verified `Source.eval`.

### `splitAtId`/`idDispatch` commutation (throws-only, D2)  — route-B (ADR-0052)

A throws-abort resumes the OUTER continuation `Kₒ` and DISCARDS the inner prefix
`Kᵢ`; prepending a non-handler frame (`letF`/`appF`) — or a non-matching `handleF`
(identity `m ≠ n`) — only grows that discarded `Kᵢ`, and `dispatchOn` on a `throws`
handler discards it, so the dispatch result is unchanged. ROUTE-B: dispatch is by
the capability's IDENTITY `n` (`splitAtId`/`idDispatch`), not by label. Conditioned
on `splitAtId K n` finding a `throws` handler (the only catching kind in D2). The
state/txn RESUME arms KEEP `Kᵢ` (`dispatchOn` returns `Kᵢ ++ handleF n :: Kₒ`), so
these letF/appF-prepend lemmas are FALSE there and stay throws-conditioned. -/

theorem dispatch_letF (N : Comp) (K : Bang.EvalCtx) (n : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId)
    (v : Val) {Kᵢ Kₒ : Bang.EvalCtx} {ℓ0 : Bang.EffectRow.Label}
    (hs : Bang.splitAtId K n = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    Bang.idDispatch (Frame.letF N :: K) n ℓ op v = Bang.idDispatch K n ℓ op v := by
  simp only [Bang.idDispatch, Bang.splitAtId, hs, Option.map_some, Option.bind_some, Bang.dispatchOn]

theorem dispatch_appF (w : Val) (K : Bang.EvalCtx) (n : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId)
    (v : Val) {Kᵢ Kₒ : Bang.EvalCtx} {ℓ0 : Bang.EffectRow.Label}
    (hs : Bang.splitAtId K n = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    Bang.idDispatch (Frame.appF w :: K) n ℓ op v = Bang.idDispatch K n ℓ op v := by
  simp only [Bang.idDispatch, Bang.splitAtId, hs, Option.map_some, Option.bind_some, Bang.dispatchOn]

/-- A `raise` propagating PAST a NON-matching `handleF m h0` frame (identity `m ≠ n`): same
`idDispatch` outcome. `splitAtId` skips the frame (the `m = n` test fails), only prepending
`handleF m h0` to the discarded inner prefix `Kᵢ` — and `dispatchOn` on a `throws` handler
DISCARDS `Kᵢ`, so the `Kₒ`-resume is unchanged. ROUTE-B: the skip criterion is IDENTITY
mismatch `m ≠ n`, not a label/op `handlesOp` test. -/
theorem dispatch_handleF_skip (m : Nat) (h0 : Handler) (K : Bang.EvalCtx) (n : Nat)
    (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Val) {Kᵢ Kₒ : Bang.EvalCtx}
    {ℓ0 : Bang.EffectRow.Label} (hmn : m ≠ n)
    (hs : Bang.splitAtId K n = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    Bang.idDispatch (Frame.handleF m h0 :: K) n ℓ op v = Bang.idDispatch K n ℓ op v := by
  simp only [Bang.idDispatch, Bang.splitAtId, if_neg hmn, hs, Option.map_some,
    Option.bind_some, Bang.dispatchOn]

/-- The kernel-side outcome of a `raised n op v` reaching context `K`: running the machine from
the perform config that re-dispatches to handler IDENTITY `n` (route-B; `Source.step` on a
`perform (vcap n ℓ) op v` focus is `(idDispatch K n ℓ op v).map …`). The `Config.run` analog of
the machine's `throwOutcome` — the two-part bridge's raised target. The counter `g` threads
through unchanged (a re-dispatch never mints). NOTE: the consumer wiring (`run_evalD`'s raised
arm, the `dispatchRun_*` prepend lemmas) is the route-B cluster-3 re-derivation — TODO. -/
def dispatchRun (fuel g n : Nat) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId)
    (v : Val) : Bang.Result Val := Bang.Config.run fuel (g, K, .perform (.vcap n ℓ) op v)

/-- The LABEL the capability identity `n` resolves to in `K` — the label of the frame `splitAtId K n`
finds, or `default` if `n` doesn't resolve (escaped). Route-B U3: the bridge re-dispatches a `raised n`
by IDENTITY, but the kernel's `idDispatch` fail-loud guard gates on `handlesOp h ℓ op` (the LABEL).
`evalD`'s identity-only `raised` dropped the cap's label, so the bridge RECONSTRUCTS it here — a thin
total projection over the existing `splitAtId` (NOT a new parallel store). The cap's real label IS the
resolved frame's label (the mint pairs them), so `labelOf` recovers exactly what makes the gate fire at
the catch; on escape both sides are `escapedCap` regardless of label, so the `default` is immaterial. -/
def labelOf (K : Bang.EvalCtx) (n : Nat) : Bang.EffectRow.Label :=
  ((Bang.splitAtId K n).map (fun t => t.2.1.label)).getD default

/-! ### D3 store ↔ kernel-`EvalCtx` correspondence (state)

The kernel resumes state in its `EvalCtx`: a `handleF (state ℓ s)` frame stores `s`, and `dispatch`
threads it on `get`/`put` (KEEP `Kᵢ`, reinstall `handleF (state ℓ s')` — `Operational.lean`
`dispatchOn`). `evalD`'s store σ is the kernel side's `state` frames projected, exactly mirroring the
machine-side `Corr σ hs`/`hsStates`/`updateStates` triad but over `EvalCtx`. -/

/-- Project a kernel `EvalCtx` to the store it mirrors: the `handleF n (state ℓ s)` frames, innermost
first, as `(n, s)` entries keyed by IDENTITY (route-B). The `Config.run`-side analog of `hsStates`. -/
def ctxStates : Bang.EvalCtx → SStore
  | []                                => []
  | Frame.handleF n (.state _ s) :: K => (n, s) :: ctxStates K
  | _ :: K                            => ctxStates K

/-- The bridge's D3 invariant: `evalD`'s threaded store IS the kernel context's active state frames. -/
def CtxCorr (σ : SStore) (K : Bang.EvalCtx) : Prop := σ = ctxStates K

/-- Overwrite each `state` frame's stored value in `K` with the store `σ` (consumed in order) — the
kernel context AFTER M's state ops have fired (the at-term/at-raise context the continuation runs on).
The `Config.run`-side analog of `updateStates`; non-state frames pass through. -/
def updateCtxStates : Bang.EvalCtx → SStore → Bang.EvalCtx
  | [],                                    _ => []
  | Frame.handleF n (.state ℓ0 _) :: K, σ =>
      match σ with
      | (_, v) :: σ' => Frame.handleF n (.state ℓ0 v) :: updateCtxStates K σ'
      | []           => Frame.handleF n (.state ℓ0 default) :: updateCtxStates K []  -- σ-exhausted (∉ Corr)
  | fr :: K,                               σ => fr :: updateCtxStates K σ

/-! ### Transaction EvalCtx-bridge (ADR-0031 D4): the `Config.run`-side mirror of the txn HStack bridge.
Parallel `THeap` projection of the kernel context's `transaction` frames; same op-disjointness invariant
as the machine side (see `THeap`). -/

/-- Project a kernel `EvalCtx` to the txn-heap store it mirrors: the `handleF n (transaction ℓ Θ)`
frames, as `(n, Θ)` entries keyed by IDENTITY (route-B). -/
def ctxTxns : Bang.EvalCtx → THeap
  | []                                      => []
  | Frame.handleF n (.transaction _ Θ) :: K => (n, Θ) :: ctxTxns K
  | _ :: K                                  => ctxTxns K

/-- The D4 invariant on the kernel side: `evalD`'s threaded τ IS the context's active txn frames. -/
def CtxTxnCorr (τ : THeap) (K : Bang.EvalCtx) : Prop := τ = ctxTxns K

/-- Overwrite each `transaction` frame's heap in `K` with τ (consumed in order). The `Config.run`-side
analog of `updateTxns`. -/
def updateCtxTxns : Bang.EvalCtx → THeap → Bang.EvalCtx
  | [],                                         _ => []
  | Frame.handleF n (.transaction ℓ0 _) :: K, τ =>
      match τ with
      | (_, Θ) :: τ' => Frame.handleF n (.transaction ℓ0 Θ) :: updateCtxTxns K τ'
      | []           => Frame.handleF n (.transaction ℓ0 default) :: updateCtxTxns K []
  | fr :: K,                                    τ => fr :: updateCtxTxns K τ

/-- Project and rebuild custom handler payloads on the kernel-context side (ADR-0114). -/
def ctxCustoms : Bang.EvalCtx → CStore
  | []                                     => []
  | Frame.handleF n (.custom _ p cls) :: K => (n, (p, cls)) :: ctxCustoms K
  | _ :: K                                 => ctxCustoms K

def updateCtxCustoms : Bang.EvalCtx → CStore → Bang.EvalCtx
  | [], _ => []
  | Frame.handleF n (.custom ℓ _ _) :: K, κ =>
      match κ with
      | (_, (p, cls)) :: κ' => Frame.handleF n (.custom ℓ p cls) :: updateCtxCustoms K κ'
      | [] => Frame.handleF n (.custom ℓ default []) :: updateCtxCustoms K []
  | fr :: K, κ => fr :: updateCtxCustoms K κ

def customCtxPut : Nat → Val → Bang.EvalCtx → Bang.EvalCtx
  | _, _, [] => []
  | n, next, Frame.handleF m (.custom ℓ p cls) :: K =>
      if m = n then Frame.handleF m (.custom ℓ next cls) :: K
      else Frame.handleF m (.custom ℓ p cls) :: customCtxPut n next K
  | n, next, fr :: K => fr :: customCtxPut n next K

theorem updateCtxCustoms_self : ∀ (K : Bang.EvalCtx), updateCtxCustoms K (ctxCustoms K) = K := by
  intro K
  induction K with
  | nil => rfl
  | cons fr K ih =>
      cases fr with
      | handleF n h =>
          cases h with
          | custom ℓ p cls => simp only [ctxCustoms, updateCtxCustoms]; rw [ih]
          | state ℓ s => simp only [ctxCustoms, updateCtxCustoms]; rw [ih]
          | throws ℓ => simp only [ctxCustoms, updateCtxCustoms]; rw [ih]
          | transaction ℓ Θ => simp only [ctxCustoms, updateCtxCustoms]; rw [ih]
      | letF N => simp only [ctxCustoms, updateCtxCustoms]; rw [ih]
      | appF v => simp only [ctxCustoms, updateCtxCustoms]; rw [ih]

theorem updateCtxCustoms_put : ∀ (K : Bang.EvalCtx) (n : Nat) (next : Val),
    updateCtxCustoms K ((ctxCustoms K).put n next) = customCtxPut n next K := by
  intro K
  induction K with
  | nil => intro n next; rfl
  | cons fr K ih =>
      intro n next
      cases fr with
      | handleF m h =>
          cases h with
          | custom ℓ p cls =>
              by_cases hmn : m = n
              · simp only [ctxCustoms, CStore.put, hmn, if_true, updateCtxCustoms, customCtxPut]
                rw [updateCtxCustoms_self]
              · simp only [ctxCustoms, CStore.put, hmn, if_false, updateCtxCustoms, customCtxPut]
                rw [ih]
          | state ℓ s => simp only [ctxCustoms, updateCtxCustoms, customCtxPut]; rw [ih]
          | throws ℓ => simp only [ctxCustoms, updateCtxCustoms, customCtxPut]; rw [ih]
          | transaction ℓ Θ => simp only [ctxCustoms, updateCtxCustoms, customCtxPut]; rw [ih]
      | letF N => simp only [ctxCustoms, updateCtxCustoms, customCtxPut]; rw [ih]
      | appF v => simp only [ctxCustoms, updateCtxCustoms, customCtxPut]; rw [ih]

theorem ctxCustoms_customCtxPut : ∀ (K : Bang.EvalCtx) (n : Nat) (next : Val),
    ctxCustoms (customCtxPut n next K) = (ctxCustoms K).put n next := by
  intro K
  induction K with
  | nil => intro n next; rfl
  | cons fr K ih =>
      intro n next
      cases fr with
      | handleF m h =>
          cases h with
          | custom ℓ p cls =>
              by_cases hmn : m = n
              · simp only [customCtxPut, hmn, if_true, ctxCustoms, CStore.put]
              · simp only [customCtxPut, hmn, if_false, ctxCustoms, CStore.put]; rw [ih]
          | state ℓ s => simp only [customCtxPut, ctxCustoms]; rw [ih]
          | throws ℓ => simp only [customCtxPut, ctxCustoms]; rw [ih]
          | transaction ℓ Θ => simp only [customCtxPut, ctxCustoms]; rw [ih]
      | letF N => simp only [customCtxPut, ctxCustoms]; rw [ih]
      | appF v => simp only [customCtxPut, ctxCustoms]; rw [ih]

theorem customCtxPut_split {K Kᵢ Kₒ : Bang.EvalCtx} {n : Nat} {ℓ : Bang.EffectRow.Label}
    {p next : Val} {cls : List (Bang.ClauseKey × Comp)}
    (hsp : Bang.splitAtId K n = some (Kᵢ, .custom ℓ p cls, Kₒ)) :
    customCtxPut n next K = Kᵢ ++ Frame.handleF n (.custom ℓ next cls) :: Kₒ := by
  induction K generalizing Kᵢ with
  | nil => simp [Bang.splitAtId] at hsp
  | cons fr K ih =>
      cases fr with
      | handleF m h =>
          simp only [Bang.splitAtId] at hsp
          by_cases hmn : m = n
          · subst m; simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp; simp [customCtxPut]
          · rw [if_neg hmn] at hsp
            cases htail : Bang.splitAtId K n with
            | none => rw [htail] at hsp; simp at hsp
            | some triple =>
                obtain ⟨Jᵢ, h', Jₒ⟩ := triple
                rw [htail] at hsp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := hsp
                cases h with
                | custom ℓ0 p0 cls0 => simp only [customCtxPut, if_neg hmn, List.cons_append]; rw [ih htail]
                | state ℓ0 s => simp only [customCtxPut, List.cons_append]; rw [ih htail]
                | throws ℓ0 => simp only [customCtxPut, List.cons_append]; rw [ih htail]
                | transaction ℓ0 Θ => simp only [customCtxPut, List.cons_append]; rw [ih htail]
      | letF N =>
          simp only [Bang.splitAtId] at hsp
          cases htail : Bang.splitAtId K n with
          | none => rw [htail] at hsp; simp at hsp
          | some triple =>
              obtain ⟨Jᵢ, h', Jₒ⟩ := triple
              rw [htail] at hsp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := hsp
              simp only [customCtxPut, List.cons_append]; rw [ih htail]
      | appF v =>
          simp only [Bang.splitAtId] at hsp
          cases htail : Bang.splitAtId K n with
          | none => rw [htail] at hsp; simp at hsp
          | some triple =>
              obtain ⟨Jᵢ, h', Jₒ⟩ := triple
              rw [htail] at hsp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := hsp
              simp only [customCtxPut, List.cons_append]; rw [ih htail]

/-- The combined kernel-side net-effect: state values from σ, then txn heaps from τ. -/
def ctxNetEffect (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) : Bang.EvalCtx :=
  updateCtxTxns (updateCtxStates K σ) τ

/-- Full kernel-side reconstruction including mutable custom-handler parameters. -/
def ctxFullEffect (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) (κ : CStore) : Bang.EvalCtx :=
  updateCtxCustoms (ctxNetEffect K σ τ) κ

@[simp] theorem ctxFullEffect_cons_state (n : Nat) (ℓ : Bang.EffectRow.Label) (s : Val)
    (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) (κ : CStore) :
    ctxFullEffect (Frame.handleF n (.state ℓ s) :: K) σ τ κ =
      Frame.handleF n (.state ℓ (σ.headD (default, default)).2) ::
        ctxFullEffect K σ.tail τ κ := by
  cases σ <;> rfl

@[simp] theorem ctxFullEffect_cons_txn (n : Nat) (ℓ : Bang.EffectRow.Label) (Θ : List Val)
    (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) (κ : CStore) :
    ctxFullEffect (Frame.handleF n (.transaction ℓ Θ) :: K) σ τ κ =
      Frame.handleF n (.transaction ℓ (τ.headD (default, default)).2) ::
        ctxFullEffect K σ τ.tail κ := by
  cases τ <;> rfl

@[simp] theorem ctxFullEffect_cons_custom (n : Nat) (ℓ : Bang.EffectRow.Label) (p : Val)
    (cls : List (Bang.ClauseKey × Comp)) (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) (κ : CStore) :
    ctxFullEffect (Frame.handleF n (.custom ℓ p cls) :: K) σ τ κ =
      Frame.handleF n (.custom ℓ (κ.headD (default, (default, []))).2.1
        (κ.headD (default, (default, []))).2.2) :: ctxFullEffect K σ τ κ.tail := by
  cases κ <;> rfl

@[simp] theorem ctxFullEffect_cons_throws (n : Nat) (ℓ : Bang.EffectRow.Label)
    (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) (κ : CStore) :
    ctxFullEffect (Frame.handleF n (.throws ℓ) :: K) σ τ κ =
      Frame.handleF n (.throws ℓ) :: ctxFullEffect K σ τ κ := rfl

@[simp] theorem ctxFullEffect_cons_let (N : Comp) (K : Bang.EvalCtx)
    (σ : SStore) (τ : THeap) (κ : CStore) :
    ctxFullEffect (Frame.letF N :: K) σ τ κ = Frame.letF N :: ctxFullEffect K σ τ κ := rfl

@[simp] theorem ctxFullEffect_cons_app (v : Val) (K : Bang.EvalCtx)
    (σ : SStore) (τ : THeap) (κ : CStore) :
    ctxFullEffect (Frame.appF v :: K) σ τ κ = Frame.appF v :: ctxFullEffect K σ τ κ := rfl

theorem ctxFullEffect_ctxFullEffect : ∀ (K : Bang.EvalCtx)
    (σ1 : SStore) (τ1 : THeap) (κ1 : CStore) (σ : SStore) (τ : THeap) (κ : CStore),
    ctxFullEffect (ctxFullEffect K σ1 τ1 κ1) σ τ κ = ctxFullEffect K σ τ κ := by
  intro K
  induction K with
  | nil => intro σ1 τ1 κ1 σ τ κ; rfl
  | cons fr K ih =>
      intro σ1 τ1 κ1 σ τ κ
      cases fr with
      | handleF n h =>
          cases h with
          | state ℓ s =>
              simp only [ctxFullEffect_cons_state, List.tail, List.headD, ih]
          | transaction ℓ Θ =>
              simp only [ctxFullEffect_cons_txn, List.tail, List.headD, ih]
          | custom ℓ p cls =>
              simp only [ctxFullEffect_cons_custom, List.tail, List.headD, ih]
          | throws ℓ =>
              simp only [ctxFullEffect_cons_throws, ih]
      | letF N =>
          simp only [ctxFullEffect_cons_let, ih]
      | appF v =>
          simp only [ctxFullEffect_cons_app, ih]

/-- `updateCtxTxns` SKIPS a state-frame head; `updateCtxStates` SKIPS a txn-frame head — the two
EvalCtx passes are independent (frame kinds disjoint). -/
theorem updateCtxTxns_cons_state {n : Nat} {ℓ : Bang.EffectRow.Label} {s : Val} {K : Bang.EvalCtx} (τ : THeap) :
    updateCtxTxns (Frame.handleF n (.state ℓ s) :: K) τ = Frame.handleF n (.state ℓ s) :: updateCtxTxns K τ := by
  simp only [updateCtxTxns]

theorem updateCtxStates_cons_txn {n : Nat} {ℓ : Bang.EffectRow.Label} {Θ : List Val} {K : Bang.EvalCtx} (σ : SStore) :
    updateCtxStates (Frame.handleF n (.transaction ℓ Θ) :: K) σ
      = Frame.handleF n (.transaction ℓ Θ) :: updateCtxStates K σ := by simp only [updateCtxStates]

/-- A non-frame (letF/appF/throws) head is transparent to BOTH passes. -/
theorem ctxNetEffect_cons_nonframe {fr : Bang.Frame} {K : Bang.EvalCtx} (σ : SStore) (τ : THeap)
    (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s)) (hnt : ∀ n ℓ Θ, fr ≠ Frame.handleF n (.transaction ℓ Θ)) :
    ctxNetEffect (fr :: K) σ τ = fr :: ctxNetEffect K σ τ := by
  unfold ctxNetEffect
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt n ℓ Θ)
      | throws ℓ => simp only [updateCtxStates, updateCtxTxns]
      | custom ℓ p cl => simp only [updateCtxStates, updateCtxTxns]   -- custom = non-state/txn, both passes skip (ADR-0085 stage 1)
  | letF N => simp only [updateCtxStates, updateCtxTxns]
  | appF v => simp only [updateCtxStates, updateCtxTxns]

theorem ctxFullEffect_cons_nonframe {fr : Bang.Frame} {K : Bang.EvalCtx} (σ : SStore) (τ : THeap)
    (κ : CStore) (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s))
    (hnt : ∀ n ℓ Θ, fr ≠ Frame.handleF n (.transaction ℓ Θ))
    (hnc : ∀ n ℓ p cls, fr ≠ Frame.handleF n (.custom ℓ p cls)) :
    ctxFullEffect (fr :: K) σ τ κ = fr :: ctxFullEffect K σ τ κ := by
  unfold ctxFullEffect
  rw [ctxNetEffect_cons_nonframe σ τ hns hnt]
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt n ℓ Θ)
      | custom ℓ p cls => exact absurd rfl (hnc n ℓ p cls)
      | throws ℓ => simp only [updateCtxCustoms]
  | letF N => simp only [updateCtxCustoms]
  | appF v => simp only [updateCtxCustoms]

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
    | handleF n h =>
        cases h with
        | state ℓ s =>
            simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns_cons_state]; rw [ih]
        | throws ℓ => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]
        | custom ℓ p cl => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]   -- custom = non-state/txn (ADR-0085 stage 1)
        | transaction ℓ Θ =>
            simp only [ctxStates, ctxTxns, updateCtxStates_cons_txn, updateCtxTxns]; rw [ih]
    | letF N => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]
    | appF v => simp only [ctxStates, ctxTxns, updateCtxStates, updateCtxTxns]; rw [ih]

/-- A non-txn frame carries no heap entry ⇒ `CtxTxnCorr` passes through its install. -/
theorem CtxTxnCorr_cons_nontxn {τ : THeap} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hnt : ∀ n ℓ Θ, fr ≠ Frame.handleF n (.transaction ℓ Θ)) (hT : CtxTxnCorr τ K) :
    CtxTxnCorr τ (fr :: K) := by
  unfold CtxTxnCorr at hT ⊢; rw [hT]
  cases fr with
  | handleF n h =>
      cases h with
      | transaction ℓ Θ => exact absurd rfl (hnt n ℓ Θ)
      | state ℓ s => simp only [ctxTxns]
      | throws ℓ => simp only [ctxTxns]
      | custom ℓ p cl => simp only [ctxTxns]   -- custom = non-txn, ctxTxns catch-all (ADR-0085 stage 1)
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
      | handleF n h =>
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
          | custom ℓ p cl => simp only [updateCtxStates, updateCtxTxns, ih]   -- custom = non-state/txn (ADR-0085 stage 1)
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
    (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s)) (hnt : ∀ n ℓ Θ, fr ≠ Frame.handleF n (.transaction ℓ Θ))
    (hC : CtxCorr σ' (ctxNetEffect (fr :: K) σ' τ')) : CtxCorr σ' (ctxNetEffect K σ' τ') := by
  rw [ctxNetEffect_cons_nonframe σ' τ' hns hnt] at hC
  unfold CtxCorr at hC ⊢
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt n ℓ Θ)
      | throws ℓ => simpa only [ctxStates] using hC
      | custom ℓ p cl => simpa only [ctxStates] using hC   -- custom = non-state, ctxStates catch-all (ADR-0085 stage 1)
  | letF N => simpa only [ctxStates] using hC
  | appF v => simpa only [ctxStates] using hC

/-- After a non-frame install, `CtxTxnCorr` over `ctxNetEffect (fr::K)` passes to `ctxNetEffect K`. -/
theorem CtxTxnCorr_ctxNetEffect_nonframe {σ' : SStore} {τ' : THeap} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s)) (hnt : ∀ n ℓ Θ, fr ≠ Frame.handleF n (.transaction ℓ Θ))
    (hT : CtxTxnCorr τ' (ctxNetEffect (fr :: K) σ' τ')) : CtxTxnCorr τ' (ctxNetEffect K σ' τ') := by
  rw [ctxNetEffect_cons_nonframe σ' τ' hns hnt] at hT
  unfold CtxTxnCorr at hT ⊢
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | transaction ℓ Θ => exact absurd rfl (hnt n ℓ Θ)
      | throws ℓ => simpa only [ctxTxns] using hT
      | custom ℓ p cl => simpa only [ctxTxns] using hT   -- custom = non-txn, ctxTxns catch-all (ADR-0085 stage 1)
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
    | handleF n h =>
        cases h with
        | state ℓ s => simp only [ctxStates, updateCtxStates]; rw [ih]
        | throws ℓ => simp only [ctxStates, updateCtxStates]; rw [ih]
        | transaction ℓ Θ => simp only [ctxStates, updateCtxStates]; rw [ih]
        | custom ℓ p cl => simp only [ctxStates, updateCtxStates]; rw [ih]   -- custom = non-state (ADR-0085 stage 1)
    | letF N => simp only [ctxStates, updateCtxStates]; rw [ih]
    | appF v => simp only [ctxStates, updateCtxStates]; rw [ih]

/-- A NON-state frame is transparent to `updateCtxStates`. -/
theorem updateCtxStates_cons_nonstate {fr : Bang.Frame} {K : Bang.EvalCtx} (σ : SStore)
    (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s)) :
    updateCtxStates (fr :: K) σ = fr :: updateCtxStates K σ := by
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | throws ℓ => simp only [updateCtxStates]
      | transaction ℓ Θ => simp only [updateCtxStates]
      | custom ℓ p cl => simp only [updateCtxStates]   -- custom = non-state, updateCtxStates catch-all (ADR-0085 stage 1)
  | letF N => simp only [updateCtxStates]
  | appF v => simp only [updateCtxStates]


/-- A NON-state frame carries no store entry ⇒ `CtxCorr` passes through its install (and pop). -/
theorem CtxCorr_cons_nonstate {σ : SStore} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s)) (hC : CtxCorr σ K) :
    CtxCorr σ (fr :: K) := by
  unfold CtxCorr at hC ⊢; rw [hC]
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | throws ℓ => simp only [ctxStates]
      | transaction ℓ Θ => simp only [ctxStates]
      | custom ℓ p cl => simp only [ctxStates]   -- custom = non-state, ctxStates catch-all (ADR-0085 stage 1)
  | letF N => simp only [ctxStates]
  | appF v => simp only [ctxStates]

theorem CtxCorr_pop_nonstate {σ : SStore} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hns : ∀ n ℓ s, fr ≠ Frame.handleF n (.state ℓ s))
    (hC : CtxCorr σ (fr :: K)) : CtxCorr σ K := by
  unfold CtxCorr at hC ⊢
  cases fr with
  | handleF n h =>
      cases h with
      | state ℓ s => exact absurd rfl (hns n ℓ s)
      | throws ℓ => simpa only [ctxStates] using hC
      | transaction ℓ Θ => simpa only [ctxStates] using hC
      | custom ℓ p cls => simpa only [ctxStates] using hC
  | letF N => simpa only [ctxStates] using hC
  | appF v => simpa only [ctxStates] using hC

theorem CtxTxnCorr_pop_nontxn {τ : THeap} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hnt : ∀ n ℓ Θ, fr ≠ Frame.handleF n (.transaction ℓ Θ))
    (hT : CtxTxnCorr τ (fr :: K)) : CtxTxnCorr τ K := by
  unfold CtxTxnCorr at hT ⊢
  cases fr with
  | handleF n h =>
      cases h with
      | transaction ℓ Θ => exact absurd rfl (hnt n ℓ Θ)
      | state ℓ s => simpa only [ctxTxns] using hT
      | throws ℓ => simpa only [ctxTxns] using hT
      | custom ℓ p cls => simpa only [ctxTxns] using hT
  | letF N => simpa only [ctxTxns] using hT
  | appF v => simpa only [ctxTxns] using hT

/-- A `state ℓ s` install PUSHES `(ℓ ↦ s)` on the store, preserving `CtxCorr`. -/
theorem CtxCorr_install {σ : SStore} {n : Nat} {ℓ : Bang.EffectRow.Label} {s : Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ K) : CtxCorr (σ.push n s) (Frame.handleF n (.state ℓ s) :: K) := by
  unfold CtxCorr at hC ⊢; rw [hC]; simp only [ctxStates, SStore.push]



/-- `CtxTxnCorr` preserved by a `handle (transaction ℓ Θ)` install (PUSH `(ℓ↦Θ)` on τ). -/
theorem CtxTxnCorr_install {τ : THeap} {n : Nat} {ℓ : Bang.EffectRow.Label} {Θ : List Val} {K : Bang.EvalCtx}
    (hT : CtxTxnCorr τ K) : CtxTxnCorr (τ.push n Θ) (Frame.handleF n (.transaction ℓ Θ) :: K) := by
  unfold CtxTxnCorr at hT ⊢; rw [hT]; simp only [ctxTxns, THeap.push]

/-- Combined-pop for a `state` install in the kernel context: pops σ1.tail (state side), τ1 unchanged.
Yields the combined `ctxNetEffect K σ1.tail τ1` correspondence + the at-return context equation. -/
theorem CtxCorr_ctxNetEffect_pop_state {σ1 : SStore} {τ1 : THeap} {n : Nat} {ℓ0 : Bang.EffectRow.Label}
    {s0 : Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF n (.state ℓ0 s0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF n (.state ℓ0 s0) :: K) σ1 τ1)) :
    (CtxCorr σ1.tail (ctxNetEffect K σ1.tail τ1) ∧ CtxTxnCorr τ1 (ctxNetEffect K σ1.tail τ1)) ∧
      ctxNetEffect (Frame.handleF n (.state ℓ0 s0) :: K) σ1 τ1
        = Frame.handleF n (.state ℓ0 (σ1.headD (default, default)).2) :: ctxNetEffect K σ1.tail τ1 := by
  cases σ1 with
  | nil =>
      exfalso; unfold CtxCorr ctxNetEffect at hC
      simp only [updateCtxStates, updateCtxTxns_cons_state, ctxStates] at hC
      exact (List.cons_ne_nil _ _ hC.symm)
  | cons p σ1' =>
      obtain ⟨ℓa, wa⟩ := p
      have hupd : ctxNetEffect (Frame.handleF n (.state ℓ0 s0) :: K) ((ℓa, wa) :: σ1') τ1
          = Frame.handleF n (.state ℓ0 wa) :: ctxNetEffect K σ1' τ1 := by
        unfold ctxNetEffect; simp only [updateCtxStates, updateCtxTxns_cons_state]
      rw [hupd] at hC hT
      refine ⟨⟨?_, ?_⟩, by simp only [List.headD, List.tail]; exact hupd⟩
      · unfold CtxCorr at hC ⊢; simp only [ctxStates, List.tail] at hC ⊢
        exact (List.cons.injEq _ _ _ _).mp hC |>.2
      · unfold CtxTxnCorr at hT ⊢; simp only [List.tail]; simpa only [ctxTxns] using hT

/-- Combined-pop for a NON-state (throws/txn) install: σ1/τ adjust per kind; this is the throws case
(non-state, non-txn) — both stores pass through to the tail. -/
theorem CtxCorr_ctxNetEffect_pop_throws {σ1 : SStore} {τ1 : THeap} {n : Nat} {ℓ0 : Bang.EffectRow.Label}
    {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1)) :
    (CtxCorr σ1 (ctxNetEffect K σ1 τ1) ∧ CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1)) ∧
      ctxNetEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1
        = Frame.handleF n (.throws ℓ0) :: ctxNetEffect K σ1 τ1 := by
  have hupd : ctxNetEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1
      = Frame.handleF n (.throws ℓ0) :: ctxNetEffect K σ1 τ1 :=
    ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
  rw [hupd] at hC hT
  refine ⟨⟨?_, ?_⟩, hupd⟩
  · unfold CtxCorr at hC ⊢; simpa only [ctxStates] using hC
  · unfold CtxTxnCorr at hT ⊢; simpa only [ctxTxns] using hT

/-- Combined-pop for a `custom` install (ADR-0085 Stage 4): a custom frame carries NEITHER state NOR
heap (op-disjoint), so σ1/τ1 both pass through unchanged — the exact `throws` shape on the σ/τ side (the
κ side pops via `CCtxCorr_pop_custom`). -/
theorem CtxCorr_ctxNetEffect_pop_custom {σ1 : SStore} {τ1 : THeap} {n : Nat} {ℓ0 : Bang.EffectRow.Label}
    {p0 : Val} {cls0 : List (Bang.ClauseKey × Comp)} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1)) :
    (CtxCorr σ1 (ctxNetEffect K σ1 τ1) ∧ CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1)) ∧
      ctxNetEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1
        = Frame.handleF n (.custom ℓ0 p0 cls0) :: ctxNetEffect K σ1 τ1 := by
  have hupd : ctxNetEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1
      = Frame.handleF n (.custom ℓ0 p0 cls0) :: ctxNetEffect K σ1 τ1 :=
    ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
  rw [hupd] at hC hT
  refine ⟨⟨?_, ?_⟩, hupd⟩
  · unfold CtxCorr at hC ⊢; simpa only [ctxStates] using hC
  · unfold CtxTxnCorr at hT ⊢; simpa only [ctxTxns] using hT

/-- Combined-pop for a `transaction` install: pops τ1.tail (txn side), σ1 unchanged. Free rollback —
the popped heap is discarded with the frame. -/
theorem CtxCorr_ctxNetEffect_pop_txn {σ1 : SStore} {τ1 : THeap} {n : Nat} {ℓ0 : Bang.EffectRow.Label}
    {Θ0 : List Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxNetEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 τ1))
    (hT : CtxTxnCorr τ1 (ctxNetEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 τ1)) :
    (CtxCorr σ1 (ctxNetEffect K σ1 τ1.tail) ∧ CtxTxnCorr τ1.tail (ctxNetEffect K σ1 τ1.tail)) ∧
      ctxNetEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 τ1
        = Frame.handleF n (.transaction ℓ0 (τ1.headD (default, default)).2) :: ctxNetEffect K σ1 τ1.tail := by
  cases τ1 with
  | nil =>
      exfalso; unfold CtxTxnCorr ctxNetEffect at hT
      simp only [updateCtxStates_cons_txn, updateCtxTxns, ctxTxns] at hT
      exact (List.cons_ne_nil _ _ hT.symm)
  | cons p τ1' =>
      obtain ⟨ℓa, Θa⟩ := p
      have hupd : ctxNetEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 ((ℓa, Θa) :: τ1')
          = Frame.handleF n (.transaction ℓ0 Θa) :: ctxNetEffect K σ1 τ1' := by
        unfold ctxNetEffect; simp only [updateCtxStates_cons_txn, updateCtxTxns]
      rw [hupd] at hC hT
      refine ⟨⟨?_, ?_⟩, by simp only [List.headD, List.tail]; exact hupd⟩
      · unfold CtxCorr at hC ⊢; simp only [List.tail]; simpa only [ctxStates] using hC
      · unfold CtxTxnCorr at hT ⊢; simp only [ctxTxns, List.tail] at hT ⊢
        exact (List.cons.injEq _ _ _ _).mp hT |>.2

theorem CtxCorr_ctxFullEffect_pop_state {σ1 : SStore} {τ1 : THeap} {κ1 : CStore}
    {n : Nat} {ℓ0 : Bang.EffectRow.Label} {s0 : Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxFullEffect (Frame.handleF n (.state ℓ0 s0) :: K) σ1 τ1 κ1))
    (hT : CtxTxnCorr τ1 (ctxFullEffect (Frame.handleF n (.state ℓ0 s0) :: K) σ1 τ1 κ1)) :
    (CtxCorr σ1.tail (ctxFullEffect K σ1.tail τ1 κ1) ∧
      CtxTxnCorr τ1 (ctxFullEffect K σ1.tail τ1 κ1)) ∧
      ctxFullEffect (Frame.handleF n (.state ℓ0 s0) :: K) σ1 τ1 κ1 =
        Frame.handleF n (.state ℓ0 (σ1.headD (default, default)).2) ::
          ctxFullEffect K σ1.tail τ1 κ1 := by
  have heq := ctxFullEffect_cons_state n ℓ0 s0 K σ1 τ1 κ1
  rw [heq] at hC hT
  refine ⟨⟨?_, ?_⟩, heq⟩
  · cases σ1 with
    | nil => simp [CtxCorr, ctxStates] at hC
    | cons entry σ' =>
        unfold CtxCorr at hC ⊢; simp only [List.tail, ctxStates] at hC
        exact (List.cons.injEq _ _ _ _).mp hC |>.2
  · unfold CtxTxnCorr at hT ⊢; simpa only [ctxTxns] using hT

theorem CtxCorr_ctxFullEffect_pop_throws {σ1 : SStore} {τ1 : THeap} {κ1 : CStore}
    {n : Nat} {ℓ0 : Bang.EffectRow.Label} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxFullEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1 κ1))
    (hT : CtxTxnCorr τ1 (ctxFullEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1 κ1)) :
    (CtxCorr σ1 (ctxFullEffect K σ1 τ1 κ1) ∧ CtxTxnCorr τ1 (ctxFullEffect K σ1 τ1 κ1)) ∧
      ctxFullEffect (Frame.handleF n (.throws ℓ0) :: K) σ1 τ1 κ1 =
        Frame.handleF n (.throws ℓ0) :: ctxFullEffect K σ1 τ1 κ1 := by
  have heq := ctxFullEffect_cons_throws n ℓ0 K σ1 τ1 κ1
  rw [heq] at hC hT
  exact ⟨⟨CtxCorr_pop_nonstate (by intro n ℓ s; simp) hC,
    CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hT⟩, heq⟩

theorem CtxCorr_ctxFullEffect_pop_custom {σ1 : SStore} {τ1 : THeap} {κ1 : CStore}
    {n : Nat} {ℓ0 : Bang.EffectRow.Label} {p0 : Val} {cls0 : List (Bang.ClauseKey × Comp)}
    {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxFullEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1 κ1))
    (hT : CtxTxnCorr τ1 (ctxFullEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1 κ1)) :
    (CtxCorr σ1 (ctxFullEffect K σ1 τ1 κ1.tail) ∧
      CtxTxnCorr τ1 (ctxFullEffect K σ1 τ1 κ1.tail)) ∧
      ∃ p cls, ctxFullEffect (Frame.handleF n (.custom ℓ0 p0 cls0) :: K) σ1 τ1 κ1 =
        Frame.handleF n (.custom ℓ0 p cls) :: ctxFullEffect K σ1 τ1 κ1.tail := by
  have heq := ctxFullEffect_cons_custom n ℓ0 p0 cls0 K σ1 τ1 κ1
  rw [heq] at hC hT
  refine ⟨⟨CtxCorr_pop_nonstate (by intro n ℓ s; simp) hC,
    CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hT⟩, ?_⟩
  exact ⟨_, _, heq⟩

theorem CtxCorr_ctxFullEffect_pop_txn {σ1 : SStore} {τ1 : THeap} {κ1 : CStore}
    {n : Nat} {ℓ0 : Bang.EffectRow.Label} {Θ0 : List Val} {K : Bang.EvalCtx}
    (hC : CtxCorr σ1 (ctxFullEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 τ1 κ1))
    (hT : CtxTxnCorr τ1 (ctxFullEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 τ1 κ1)) :
    (CtxCorr σ1 (ctxFullEffect K σ1 τ1.tail κ1) ∧
      CtxTxnCorr τ1.tail (ctxFullEffect K σ1 τ1.tail κ1)) ∧
      ctxFullEffect (Frame.handleF n (.transaction ℓ0 Θ0) :: K) σ1 τ1 κ1 =
        Frame.handleF n (.transaction ℓ0 (τ1.headD (default, default)).2) ::
          ctxFullEffect K σ1 τ1.tail κ1 := by
  have heq := ctxFullEffect_cons_txn n ℓ0 Θ0 K σ1 τ1 κ1
  rw [heq] at hC hT
  refine ⟨⟨?_, ?_⟩, heq⟩
  · unfold CtxCorr at hC ⊢; simpa only [ctxStates] using hC
  · cases τ1 with
    | nil => simp [CtxTxnCorr, ctxTxns] at hT
    | cons entry τ' =>
        unfold CtxTxnCorr at hT ⊢; simp only [List.tail, ctxTxns] at hT
        exact (List.cons.injEq _ _ _ _).mp hT |>.2

/-- `splitAtId` RECONSTRUCTS its input: `K = Kᵢ ++ handleF n h :: Kₒ` (route-B: the matched frame's
IDENTITY `n` is preserved in the reconstruction — `splitAtId` matches `m = n`, so the re-installed frame
carries `n`). The decomposition is lossless. Induction on `K`. -/
theorem splitAtId_reconstruct {n : Nat} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {h : Handler},
      Bang.splitAtId K n = some (Kᵢ, h, Kₒ) → Kᵢ ++ Frame.handleF n h :: Kₒ = K := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hs; simp [Bang.splitAtId] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ h hs
    cases fr with
    | handleF m h0 =>
        simp only [Bang.splitAtId] at hs
        by_cases hc : m = n
        · subst hc; rw [if_pos rfl] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs; simp
        · rw [if_neg hc] at hs
          cases hsp : Bang.splitAtId K n with
          | none => rw [hsp] at hs; simp at hs
          | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                      obtain ⟨rfl, rfl, rfl⟩ := hs; simp only [List.cons_append]; rw [ih hsp]
    | letF N =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                    obtain ⟨rfl, rfl, rfl⟩ := hs; simp only [List.cons_append]; rw [ih hsp]
    | appF w =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                    obtain ⟨rfl, rfl, rfl⟩ := hs; simp only [List.cons_append]; rw [ih hsp]

/-- `splitAtId K n` landing on a `state ℓ' s` frame ⟹ the IDENTITY-keyed store has `s` at `n`:
`(ctxStates K).get? n = some s`. Route-B: the value lookup is by identity `n`; the frame's label `ℓ'`
is immaterial to the store projection. Induction on `K`. -/
theorem splitAtId_state_value {n : Nat} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {ℓ' : Bang.EffectRow.Label} {s : Val},
      Bang.splitAtId K n = some (Kᵢ, Handler.state ℓ' s, Kₒ) →
        (ctxStates K).get? n = some s := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ ℓ' s hs; simp [Bang.splitAtId] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ ℓ' s hs
    cases fr with
    | handleF m h0 =>
        simp only [Bang.splitAtId] at hs
        by_cases hc : m = n
        · subst hc
          rw [if_pos rfl] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨_, rfl, _⟩ := hs
          simp [ctxStates, SStore.get?, List.find?]
        · rw [if_neg hc] at hs
          cases hsp : Bang.splitAtId K n with
          | none => rw [hsp] at hs; simp at hs
          | some t =>
              obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨_, rfl, _⟩ := hs
              have hv := ih hsp
              cases h0 with
              | state ℓ0 s0 => simpa [ctxStates, SStore.get?, List.find?, hc] using hv
              | throws ℓ0 => simpa [ctxStates] using hv
              | transaction ℓ0 Θ0 => simpa [ctxStates] using hv
              | custom ℓ0 p cl => simpa [ctxStates] using hv   -- custom = non-state, ctxStates skip (ADR-0085 stage 1)
    | letF N =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxStates] using ih hsp
    | appF w =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxStates] using ih hsp

/-- No state cell at a key the stack keeps strictly below it: `CapsBelow n K ⟹ (ctxStates K).get? n = none`.
The `ctxStates` keys are exactly the `handleF`-state ids, all `< n` under `CapsBelow`, so the lookup misses.
(Used by the inverse `splitAtId_of_ctxStates_get` to refute a same-id non-state frame shadowing the cell.) -/
theorem ctxStates_get_none_of_capsBelow {n : Nat} : ∀ {K : Bang.EvalCtx},
    Bang.Model.CapsBelow n K → (ctxStates K).get? n = none := by
  intro K
  induction K with
  | nil => intro _; rfl
  | cons fr K ih =>
    intro hcb
    cases fr with
    | handleF m h0 =>
        simp only [Bang.Model.CapsBelow] at hcb
        cases h0 with
        | state ℓ0 s0 =>
            have hmn : ¬ (m = n) := by omega
            have he : (ctxStates (Frame.handleF m (Handler.state ℓ0 s0) :: K)).get? n = (ctxStates K).get? n := by
              simp only [ctxStates, SStore.get?, List.find?, hmn, decide_false, Bool.false_eq_true, if_false]
            rw [he]; exact ih hcb.2
        | throws ℓ0 => simp only [ctxStates]; exact ih hcb.2
        | transaction ℓ0 Θ0 => simp only [ctxStates]; exact ih hcb.2
        | custom ℓ0 p cl => simp only [ctxStates]; exact ih hcb.2   -- custom = non-state (ADR-0085 stage 1)
    | letF N => simp only [Bang.Model.CapsBelow] at hcb; simp only [ctxStates]; exact ih hcb.2
    | appF w => simp only [Bang.Model.CapsBelow] at hcb; simp only [ctxStates]; exact ih hcb.2

/-- **The existence factor of `CapResolves`** (route-B, the U3 perform-arm bridge): a live state value at
identity `n` in the store reflects a live `state` frame at `n` on the stack. `StratFresh` (id-uniqueness)
is load-bearing — without it a shallower `throws`/`transaction` frame at the same id could shadow the
cell (`ctxStates` skips non-state frames, but `splitAtId` would match the shadow); the freshness contra
(`ctxStates_get_none_of_capsBelow`) rules that out. Inverse of `splitAtId_state_value`. -/
theorem splitAtId_of_ctxStates_get {n : Nat} {s : Val} : ∀ {K : Bang.EvalCtx},
    Bang.Model.StratFresh K → (ctxStates K).get? n = some s →
      ∃ Kᵢ ℓ' Kₒ, Bang.splitAtId K n = some (Kᵢ, Handler.state ℓ' s, Kₒ) := by
  intro K
  induction K with
  | nil => intro _ hg; simp [ctxStates, SStore.get?] at hg
  | cons fr K ih =>
    intro hsf hg
    cases fr with
    | handleF m h0 =>
        cases h0 with
        | state ℓ0 s0 =>
            by_cases hc : m = n
            · subst hc
              have hhead : (ctxStates (Frame.handleF m (Handler.state ℓ0 s0) :: K)).get? m = some s0 := by
                simp [ctxStates, SStore.get?]
              rw [hhead] at hg
              obtain rfl : s = s0 := (Option.some.inj hg).symm
              exact ⟨[], ℓ0, K, by simp [Bang.splitAtId]⟩
            · have he : (ctxStates (Frame.handleF m (Handler.state ℓ0 s0) :: K)).get? n = (ctxStates K).get? n := by
                simp only [ctxStates, SStore.get?, List.find?, hc, decide_false, Bool.false_eq_true, if_false]
              rw [he] at hg
              simp only [Bang.Model.StratFresh] at hsf
              obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg
              exact ⟨Frame.handleF m (Handler.state ℓ0 s0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | throws ℓ0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxStates_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.throws ℓ0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | transaction ℓ0 Θ0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxStates_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.transaction ℓ0 Θ0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | custom ℓ0 p cl =>   -- custom = non-state frame: same shadow-refute shape as throws/txn (ADR-0085 stage 1)
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxStates_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.custom ℓ0 p cl) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
    | letF N =>
        simp only [Bang.Model.StratFresh] at hsf
        have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
        obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf hg'
        exact ⟨Frame.letF N :: Ki, ℓ', Ko, by simp only [Bang.splitAtId, hsp, Option.map_some]⟩
    | appF w =>
        simp only [Bang.Model.StratFresh] at hsf
        have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
        obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf hg'
        exact ⟨Frame.appF w :: Ki, ℓ', Ko, by simp only [Bang.splitAtId, hsp, Option.map_some]⟩

/-- Txn mirror of `ctxStates_get_none_of_capsBelow`: `CapsBelow n K ⟹ (ctxTxns K).get? n = none`. -/
theorem ctxTxns_get_none_of_capsBelow {n : Nat} : ∀ {K : Bang.EvalCtx},
    Bang.Model.CapsBelow n K → (ctxTxns K).get? n = none := by
  intro K
  induction K with
  | nil => intro _; rfl
  | cons fr K ih =>
    intro hcb
    cases fr with
    | handleF m h0 =>
        simp only [Bang.Model.CapsBelow] at hcb
        cases h0 with
        | transaction ℓ0 Θ0 =>
            have hmn : ¬ (m = n) := by omega
            have he : (ctxTxns (Frame.handleF m (Handler.transaction ℓ0 Θ0) :: K)).get? n = (ctxTxns K).get? n := by
              simp only [ctxTxns, THeap.get?, List.find?, hmn, decide_false, Bool.false_eq_true, if_false]
            rw [he]; exact ih hcb.2
        | state ℓ0 s0 => simp only [ctxTxns]; exact ih hcb.2
        | throws ℓ0 => simp only [ctxTxns]; exact ih hcb.2
        | custom ℓ0 p cl => simp only [ctxTxns]; exact ih hcb.2   -- custom = non-txn (ADR-0085 stage 1)
    | letF N => simp only [Bang.Model.CapsBelow] at hcb; simp only [ctxTxns]; exact ih hcb.2
    | appF w => simp only [Bang.Model.CapsBelow] at hcb; simp only [ctxTxns]; exact ih hcb.2

/-- Txn mirror of `splitAtId_of_ctxStates_get` (the existence factor for txn ops): a live txn heap at id
`n` reflects a live `transaction` frame at `n`; `StratFresh` rules out a same-id state/throws shadow. -/
theorem splitAtId_of_ctxTxns_get {n : Nat} {Θ : List Val} : ∀ {K : Bang.EvalCtx},
    Bang.Model.StratFresh K → (ctxTxns K).get? n = some Θ →
      ∃ Kᵢ ℓ' Kₒ, Bang.splitAtId K n = some (Kᵢ, Handler.transaction ℓ' Θ, Kₒ) := by
  intro K
  induction K with
  | nil => intro _ hg; simp [ctxTxns, THeap.get?] at hg
  | cons fr K ih =>
    intro hsf hg
    cases fr with
    | handleF m h0 =>
        cases h0 with
        | transaction ℓ0 Θ0 =>
            by_cases hc : m = n
            · subst hc
              have hhead : (ctxTxns (Frame.handleF m (Handler.transaction ℓ0 Θ0) :: K)).get? m = some Θ0 := by
                simp [ctxTxns, THeap.get?]
              rw [hhead] at hg
              obtain rfl : Θ = Θ0 := (Option.some.inj hg).symm
              exact ⟨[], ℓ0, K, by simp [Bang.splitAtId]⟩
            · have he : (ctxTxns (Frame.handleF m (Handler.transaction ℓ0 Θ0) :: K)).get? n = (ctxTxns K).get? n := by
                simp only [ctxTxns, THeap.get?, List.find?, hc, decide_false, Bool.false_eq_true, if_false]
              rw [he] at hg
              simp only [Bang.Model.StratFresh] at hsf
              obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg
              exact ⟨Frame.handleF m (Handler.transaction ℓ0 Θ0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | state ℓ0 s0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxTxns_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.state ℓ0 s0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | throws ℓ0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxTxns_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.throws ℓ0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | custom ℓ0 p cl =>   -- custom = non-txn frame: same shadow-refute shape as state/throws (ADR-0085 stage 1)
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxTxns_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.custom ℓ0 p cl) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
    | letF N =>
        simp only [Bang.Model.StratFresh] at hsf
        have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
        obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf hg'
        exact ⟨Frame.letF N :: Ki, ℓ', Ko, by simp only [Bang.splitAtId, hsp, Option.map_some]⟩
    | appF w =>
        simp only [Bang.Model.StratFresh] at hsf
        have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
        obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf hg'
        exact ⟨Frame.appF w :: Ki, ℓ', Ko, by simp only [Bang.splitAtId, hsp, Option.map_some]⟩

/-- A `state`-`get` dispatch RESUMES in place (route-B). The cap resolves by IDENTITY
(`CapResolves K n ℓ "get"` — holds by-mint: the cap `vcap n ℓ` names the handler `n`, whose label IS
`ℓ`), and the identity-keyed store has `s` at `n`. `idDispatch` finds the `state ℓ s` frame and resumes
`(K, .ret s)` — context structurally unchanged (`get` re-installs the same frame, does not mutate). The
`handlesOp` label-guard is discharged by the resolution witness — NO `state_some`/`WellCounted` needed
(the coherence comes IN via `CapResolves`, not derived from the store). Via `splitAtId_state_value` +
`splitAtId_reconstruct`. -/
theorem dispatch_state_get {n : Nat} {ℓ : Bang.EffectRow.Label} {v s : Val} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K)
    (hcr : Bang.CapResolves K n ℓ "get") (hg : (ctxStates K).get? n = some s) :
    Bang.idDispatch K n ℓ "get" v = some (K, .ret s) := by
  obtain ⟨Kᵢ, h, Kₒ, hsp, hho⟩ := hcr
  -- a handler of `(ℓ, "get")` is a `state ℓ _` frame. throws/txn fail `handlesOp`; custom (now REAL,
  -- ADR-0087) could resolve a `"get"`-named clause, so it is excluded by ID-UNIQUENESS instead: the store
  -- read `hg` reflects a live STATE frame at `n` (`splitAtId_of_ctxStates_get`), and `splitAtId` is
  -- deterministic, so that state frame IS the resolved frame `h` — a custom `h` contradicts it.
  obtain ⟨ℓ', s', rfl⟩ : ∃ ℓ' s', h = Handler.state ℓ' s' := by
    cases h with
    | state ℓ' s' => exact ⟨ℓ', s', rfl⟩
    | throws _ => simp [Bang.handlesOp] at hho
    | transaction _ _ => simp [Bang.handlesOp] at hho
    | custom _ _ _ =>
        obtain ⟨Kᵢ2, ℓ2, Kₒ2, hsp2⟩ := splitAtId_of_ctxStates_get hsf hg
        rw [hsp] at hsp2
        simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at hsp2
  -- the store value at `n` is the frame's `s'`; with `hg`, `s' = s`.
  have hsv : (ctxStates K).get? n = some s' := splitAtId_state_value hsp
  rw [hg] at hsv
  obtain rfl : s = s' := Option.some.inj hsv
  have hrec : Kᵢ ++ Frame.handleF n (Handler.state ℓ' s) :: Kₒ = K := splitAtId_reconstruct hsp
  simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn,
    beq_self_eq_true, if_true]
  rw [hrec]

/-- A `state`-`put` dispatch RESUMES with the value updated (route-B, IDENTITY-keyed): `splitAtId K n`
finds `handleF n (state ℓ' s)`, reinstalls `handleF n (state ℓ' w)`, resumes with the context `K` whose
`n`-keyed state value is set to `w` — i.e. `updateCtxStates K ((ctxStates K).put n w)`. The identity
`n` selects the frame; the frame's own label `ℓ'` is immaterial to the store projection. Induction on
`K`, mirroring `splitAtId_state_value`'s walk + `dispatchOn`'s put. -/
theorem updateCtxStates_put_split {n : Nat} {w : Val} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {ℓ' : Bang.EffectRow.Label} {s : Val},
      Bang.splitAtId K n = some (Kᵢ, Handler.state ℓ' s, Kₒ) →
        updateCtxStates K ((ctxStates K).put n w) = Kᵢ ++ Frame.handleF n (Handler.state ℓ' w) :: Kₒ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ ℓ' s hsp; simp [Bang.splitAtId] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ ℓ' s hsp
    cases fr with
    | handleF m h0 =>
        simp only [Bang.splitAtId] at hsp
        by_cases hc : m = n
        · subst hc
          -- `subst hc` (hc : m = n) eliminated `n`; the head frame's identity is now `m`.
          rw [if_pos rfl] at hsp
          simp only [Option.some.injEq, Prod.mk.injEq] at hsp
          obtain ⟨rfl, rfl, rfl⟩ := hsp
          have e1 : (ctxStates (Frame.handleF m (Handler.state ℓ' s) :: K)).put m w
                    = (m, w) :: ctxStates K := by simp [ctxStates, SStore.put]
          rw [e1]
          show Frame.handleF m (Handler.state ℓ' w) :: updateCtxStates K (ctxStates K)
                = [] ++ Frame.handleF m (Handler.state ℓ' w) :: K
          rw [updateCtxStates_self (rfl : CtxCorr (ctxStates K) K), List.nil_append]
        · -- head identity ≠ `n` ⇒ splitAtId recurses; put updates a DEEPER frame.
          rw [if_neg hc] at hsp
          cases hsp2 : Bang.splitAtId K n with
          | none => rw [hsp2] at hsp; simp at hsp
          | some t =>
              obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := hsp
              cases h0 with
              | state ℓ0 s0 =>
                  simp only [ctxStates, SStore.put, if_neg hc, updateCtxStates, List.cons_append]
                  rw [ih hsp2]
              | throws ℓ0 =>
                  simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]
              | transaction ℓ0 Θ0 =>
                  simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]
              | custom ℓ0 p cl =>
                  simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]   -- custom = non-state (ADR-0085 stage 1)
    | letF N =>
        simp only [Bang.splitAtId] at hsp
        cases hsp2 : Bang.splitAtId K n with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp
            simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]
    | appF w0 =>
        simp only [Bang.splitAtId] at hsp
        cases hsp2 : Bang.splitAtId K n with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp
            simp only [ctxStates, updateCtxStates, List.cons_append]; rw [ih hsp2]

/-- A `state`-`put` dispatch RESUMES with the value updated (route-B): the cap resolves by IDENTITY
(`CapResolves K n ℓ "put"`), `idDispatch` finds the `state ℓ' s'` frame, reinstalls `state ℓ' w`, and
resumes `(updateCtxStates K ((ctxStates K).put n w), .ret unit)`. The `handlesOp` label-guard is
discharged off the resolution witness (mirror of `dispatch_state_get`; via `updateCtxStates_put_split`). -/
theorem dispatch_state_put {n : Nat} {ℓ : Bang.EffectRow.Label} {w s : Val} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K)
    (hcr : Bang.CapResolves K n ℓ "put") (hg : (ctxStates K).get? n = some s) :
    Bang.idDispatch K n ℓ "put" w
      = some (updateCtxStates K ((ctxStates K).put n w), .ret .vunit) := by
  obtain ⟨Kᵢ, h, Kₒ, hsp, hho⟩ := hcr
  -- state frame by ID-UNIQUENESS (mirror of `dispatch_state_get`): the store read reflects a live state
  -- frame at `n`, deterministically the resolved `h`, so a custom (now-REAL, ADR-0087) `h` is absurd.
  obtain ⟨ℓ', s', rfl⟩ : ∃ ℓ' s', h = Handler.state ℓ' s' := by
    cases h with
    | state ℓ' s' => exact ⟨ℓ', s', rfl⟩
    | throws _ => simp [Bang.handlesOp] at hho
    | transaction _ _ => simp [Bang.handlesOp] at hho
    | custom _ _ _ =>
        obtain ⟨Kᵢ2, ℓ2, Kₒ2, hsp2⟩ := splitAtId_of_ctxStates_get hsf hg
        rw [hsp] at hsp2
        simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at hsp2
  rw [updateCtxStates_put_split hsp]
  simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn, beq_iff_eq,
    if_neg (by decide : ¬ ("put" = "get"))]

/-- After a `put`, the resume context's `ctxStates` IS the put-updated store: `ctxStates
(updateCtxStates K (σ.put ℓ w)) = (ctxStates K).put ℓ w` where σ = ctxStates K. The `CtxCorr`-
preservation of a state `put` (the kernel `dispatchOn`-put restores the D3 correspondence). Via
`updateCtxStates_put_split` + `ctxStates` of the split reconstruction. Induction on `K`. -/
theorem ctxStates_updateCtxStates_put {n : Nat} {w : Val} :
    ∀ {K : Bang.EvalCtx} {s : Val}, (ctxStates K).get? n = some s →
      ctxStates (updateCtxStates K ((ctxStates K).put n w)) = (ctxStates K).put n w := by
  intro K
  induction K with
  | nil => intro s hg; simp [ctxStates, SStore.get?] at hg
  | cons fr K ih =>
    intro s hg
    cases fr with
    | handleF m h0 =>
        cases h0 with
        | state ℓ0 s0 =>
            by_cases hc : m = n
            · subst hc
              simp only [ctxStates, SStore.put, if_true, updateCtxStates]
              rw [updateCtxStates_self rfl]
            · have hg' : (ctxStates K).get? n = some s := by
                simp only [ctxStates, SStore.get?, List.find?, hc, decide_false,
                  Bool.false_eq_true, if_false] at hg; simpa [SStore.get?] using hg
              simp only [ctxStates, SStore.put, if_neg hc, updateCtxStates]; rw [ih hg']
        | throws ℓ0 =>
            have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
            simp only [ctxStates, updateCtxStates]; rw [ih hg']
        | transaction ℓ0 Θ0 =>
            have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
            simp only [ctxStates, updateCtxStates]; rw [ih hg']
        | custom ℓ0 p cl =>   -- custom = non-state, ctxStates/updateCtxStates skip (ADR-0085 stage 1)
            have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
            simp only [ctxStates, updateCtxStates]; rw [ih hg']
    | letF N =>
        have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
        simp only [ctxStates, updateCtxStates]; rw [ih hg']
    | appF v0 =>
        have hg' : (ctxStates K).get? n = some s := by simpa only [ctxStates] using hg
        simp only [ctxStates, updateCtxStates]; rw [ih hg']

/-! ### Transaction kernel-dispatch lemmas (ADR-0031 D4): mirror of the `dispatch_state_*` set. -/

/-- `splitAtId K n` landing on a `transaction ℓ' Θ` frame ⟹ the IDENTITY-keyed txn-heap has `Θ` at
`n`: `(ctxTxns K).get? n = some Θ`. Route-B txn mirror of `splitAtId_state_value` — the value lookup is
by identity `n`; the frame's label `ℓ'` is immaterial to the heap projection. Induction on `K`. -/
theorem splitAtId_txn_value {n : Nat} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {ℓ' : Bang.EffectRow.Label} {Θ : List Val},
      Bang.splitAtId K n = some (Kᵢ, Handler.transaction ℓ' Θ, Kₒ) →
        (ctxTxns K).get? n = some Θ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ ℓ' Θ hs; simp [Bang.splitAtId] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ ℓ' Θ hs
    cases fr with
    | handleF m h0 =>
        simp only [Bang.splitAtId] at hs
        by_cases hc : m = n
        · subst hc
          rw [if_pos rfl] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨_, rfl, _⟩ := hs
          simp [ctxTxns, THeap.get?, List.find?]
        · rw [if_neg hc] at hs
          cases hsp : Bang.splitAtId K n with
          | none => rw [hsp] at hs; simp at hs
          | some t =>
              obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨_, rfl, _⟩ := hs
              have hv := ih hsp
              cases h0 with
              | transaction ℓ0 Θ0 => simpa [ctxTxns, THeap.get?, List.find?, hc] using hv
              | state ℓ0 s0 => simpa [ctxTxns] using hv
              | throws ℓ0 => simpa [ctxTxns] using hv
              | custom ℓ0 p cl => simpa [ctxTxns] using hv   -- custom = non-txn, ctxTxns skip (ADR-0085 stage 1)
    | letF N =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxTxns] using ih hsp
    | appF w =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxTxns] using ih hsp

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
    | handleF m h =>
        cases h with
        | transaction ℓ Θ => simp only [ctxTxns, updateCtxTxns]; rw [ih]
        | state ℓ s => simp only [ctxTxns, updateCtxTxns]; rw [ih]
        | throws ℓ => simp only [ctxTxns, updateCtxTxns]; rw [ih]
        | custom ℓ p cl => simp only [ctxTxns, updateCtxTxns]; rw [ih]   -- custom = non-txn (ADR-0085 stage 1)
    | letF N => simp only [ctxTxns, updateCtxTxns]; rw [ih]
    | appF v => simp only [ctxTxns, updateCtxTxns]; rw [ih]

/-- A txn dispatch reinstalls the serviced heap (route-B, IDENTITY-keyed): `splitAtId K n =
(Kᵢ, transaction ℓ' Θ, Kₒ)` ⇒ `updateCtxTxns K ((ctxTxns K).put n Θ') = Kᵢ ++ handleF n
(transaction ℓ' Θ') :: Kₒ`. Mirror of `updateCtxStates_put_split`. Induction on `K`. -/
theorem updateCtxTxns_service_split {n : Nat} {Θ' : List Val} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {ℓ' : Bang.EffectRow.Label} {Θ : List Val},
      Bang.splitAtId K n = some (Kᵢ, Handler.transaction ℓ' Θ, Kₒ) →
        updateCtxTxns K ((ctxTxns K).put n Θ') = Kᵢ ++ Frame.handleF n (Handler.transaction ℓ' Θ') :: Kₒ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ ℓ' Θ hsp; simp [Bang.splitAtId] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ ℓ' Θ hsp
    cases fr with
    | handleF m h0 =>
        simp only [Bang.splitAtId] at hsp
        by_cases hc : m = n
        · subst hc
          rw [if_pos rfl] at hsp
          simp only [Option.some.injEq, Prod.mk.injEq] at hsp
          obtain ⟨rfl, rfl, rfl⟩ := hsp
          -- `subst hc` (hc : m = n) eliminated `n`, so the head frame's identity is now `m`.
          have e1 : (ctxTxns (Frame.handleF m (Handler.transaction ℓ' Θ) :: K)).put m Θ'
                    = (m, Θ') :: ctxTxns K := by simp [ctxTxns, THeap.put]
          rw [e1]
          show Frame.handleF m (Handler.transaction ℓ' Θ') :: updateCtxTxns K (ctxTxns K)
                = [] ++ Frame.handleF m (Handler.transaction ℓ' Θ') :: K
          rw [updateCtxTxns_self_aux, List.nil_append]
        · rw [if_neg hc] at hsp
          cases hsp2 : Bang.splitAtId K n with
          | none => rw [hsp2] at hsp; simp at hsp
          | some t =>
              obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := hsp
              cases h0 with
              | transaction ℓ0 Θ0 =>
                  simp only [ctxTxns, THeap.put, if_neg hc, updateCtxTxns, List.cons_append]
                  rw [ih hsp2]
              | state ℓ0 s0 =>
                  simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]
              | throws ℓ0 =>
                  simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]
              | custom ℓ0 p cl =>
                  simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]   -- custom = non-txn (ADR-0085 stage 1)
    | letF N =>
        simp only [Bang.splitAtId] at hsp
        cases hsp2 : Bang.splitAtId K n with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp
            simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]
    | appF w0 =>
        simp only [Bang.splitAtId] at hsp
        cases hsp2 : Bang.splitAtId K n with
        | none => rw [hsp2] at hsp; simp at hsp
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp2] at hsp
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := hsp
            simp only [ctxTxns, updateCtxTxns, List.cons_append]; rw [ih hsp2]

/-- A txn dispatch RESUMES with the heap serviced: finds `transaction ℓ Θ`, services via `txnService`,
reinstalls `transaction ℓ Θ'`, resumes `(updateCtxTxns K ((ctxTxns K).put ℓ Θ'), .ret r)`. The kernel
`dispatchOn` transaction arm, packaged against the EvalCtx projection. Mirror of `dispatch_state_put`. -/
theorem dispatch_txn_service {n : Nat} {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val}
    {K : Bang.EvalCtx} {Θ : List Val} (hsf : Bang.Model.StratFresh K)
    (hop : isTxnOp op = true) (hcr : Bang.CapResolves K n ℓ op)
    (hg : (ctxTxns K).get? n = some Θ) :
    Bang.idDispatch K n ℓ op v
      = some (updateCtxTxns K ((ctxTxns K).put n (txnService op v Θ).2), .ret (txnService op v Θ).1) := by
  obtain ⟨Kᵢ, h, Kₒ, hsp, hho⟩ := hcr
  -- a handler catching a txn op is a `transaction` frame. state/throws fail `handlesOp`; custom (now REAL,
  -- ADR-0087) is excluded by ID-UNIQUENESS: the heap read reflects a live transaction frame at `n`
  -- (`splitAtId_of_ctxTxns_get`), deterministically the resolved `h`, so a custom `h` is absurd.
  obtain ⟨ℓ', Θ', rfl⟩ : ∃ ℓ' Θ', h = Handler.transaction ℓ' Θ' := by
    cases h with
    | transaction ℓ' Θ' => exact ⟨ℓ', Θ', rfl⟩
    | state _ _ => rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp [Bang.handlesOp] at hho
    | throws _ => rcases isTxnOp_iff.mp hop with rfl | rfl | rfl <;> simp [Bang.handlesOp] at hho
    | custom _ _ _ =>
        obtain ⟨Kᵢ2, ℓ2, Kₒ2, hsp2⟩ := splitAtId_of_ctxTxns_get hsf hg
        rw [hsp] at hsp2
        simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at hsp2
  -- the heap value at `n` is the frame's `Θ'`; with `hg`, `Θ' = Θ`.
  have hhv : (ctxTxns K).get? n = some Θ' := splitAtId_txn_value hsp
  rw [hg] at hhv
  obtain rfl : Θ = Θ' := Option.some.inj hhv
  rw [updateCtxTxns_service_split hsp]
  -- unfold the kernel dispatchOn transaction arm and match txnService's (r, Θ').
  rcases isTxnOp_iff.mp hop with rfl | rfl | rfl
  · -- newTVar: (vint Θ.length, Θ ++ [v])
    simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn, txnService,
      beq_self_eq_true, if_true, if_pos rfl]
  · -- readTVar: (Θ.getD i (vint 0), Θ)
    simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn, txnService,
      (by decide : ("readTVar" == "newTVar") = false), beq_self_eq_true, Bool.false_eq_true,
      if_false, if_true, if_neg (by decide : ¬ ("readTVar" = "newTVar")), if_pos rfl]
  · -- writeTVar: (vunit, storeSet Θ i w) on a pair payload; vunit/Θ otherwise
    simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn, txnService,
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
    | handleF m h =>
        cases h with
        | transaction ℓ Θ =>
            cases τ with
            | nil => simp only [updateCtxTxns, ctxStates]; exact ih []
            | cons p τ' => simp only [updateCtxTxns, ctxStates]; exact ih τ'
        | state ℓ s => simp only [updateCtxTxns, ctxStates]; rw [ih τ]
        | throws ℓ => simp only [updateCtxTxns, ctxStates]; exact ih τ
        | custom ℓ p cl => simp only [updateCtxTxns, ctxStates]; exact ih τ   -- custom = non-txn (ADR-0085 stage 1)
    | letF N => simp only [updateCtxTxns, ctxStates]; exact ih τ
    | appF v => simp only [updateCtxTxns, ctxStates]; exact ih τ

/-- After a txn service, the resume context's `ctxTxns` IS the put-updated heap-store: `ctxTxns
(updateCtxTxns K (τ.put ℓ Θ')) = τ.put ℓ Θ'` where τ = ctxTxns K. The `CtxTxnCorr`-preservation of a
txn resume. Mirror of `ctxStates_updateCtxStates_put`. Induction on `K`. -/
theorem ctxTxns_updateCtxTxns_service {n : Nat} {Θ' : List Val} :
    ∀ {K : Bang.EvalCtx} {Θ : List Val}, (ctxTxns K).get? n = some Θ →
      ctxTxns (updateCtxTxns K ((ctxTxns K).put n Θ')) = (ctxTxns K).put n Θ' := by
  intro K
  induction K with
  | nil => intro Θ hg; simp [ctxTxns, THeap.get?] at hg
  | cons fr K ih =>
    intro Θ hg
    cases fr with
    | handleF m h0 =>
        cases h0 with
        | transaction ℓ0 Θ0 =>
            by_cases hc : m = n
            · subst hc
              simp only [ctxTxns, THeap.put, if_true, updateCtxTxns]
              rw [updateCtxTxns_self_aux]
            · have hg' : (ctxTxns K).get? n = some Θ := by
                simp only [ctxTxns, THeap.get?, List.find?, hc, decide_false,
                  Bool.false_eq_true, if_false] at hg; simpa [THeap.get?] using hg
              simp only [ctxTxns, THeap.put, if_neg hc, updateCtxTxns]; rw [ih hg']
        | state ℓ0 s0 =>
            have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
            simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
        | throws ℓ0 =>
            have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
            simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
        | custom ℓ0 p cl =>   -- custom = non-txn, ctxTxns/updateCtxTxns skip (ADR-0085 stage 1)
            have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
            simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
    | letF N =>
        have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
        simp only [ctxTxns, updateCtxTxns]; rw [ih hg']
    | appF v0 =>
        have hg' : (ctxTxns K).get? n = some Θ := by simpa only [ctxTxns] using hg
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
    | handleF m h =>
        cases h with
        | state ℓ s =>
            cases σ with
            | nil => simp only [updateCtxStates, ctxTxns]; exact ih []
            | cons p σ' => simp only [updateCtxStates, ctxTxns]; exact ih σ'
        | transaction ℓ Θ => simp only [updateCtxStates, ctxTxns]; rw [ih σ]
        | throws ℓ => simp only [updateCtxStates, ctxTxns]; exact ih σ
        | custom ℓ p cl => simp only [updateCtxStates, ctxTxns]; exact ih σ   -- custom = non-state (ADR-0085 stage 1)
    | letF N => simp only [updateCtxStates, ctxTxns]; exact ih σ
    | appF v => simp only [updateCtxStates, ctxTxns]; exact ih σ

/-! ### Custom EvalCtx-bridge (ADR-0085 Stage 4): the `Config.run`-side mirror of the custom HStack bridge.

`ctxCustoms`/`CCtxCorr` are the EvalCtx analogs of `hsCustoms`/`CCorr` — projecting the kernel context's
`custom` frames into the `CStore` `evalD` threads. ADR-0114 adds `updateCtxCustoms`; `ctxFullEffect`
composes it after the state/transaction net effect so all three final stores are reflected in the
kernel context. This makes `CCtxCorr` the exact custom sibling of the state/transaction families. -/

/-- The Stage-4 invariant on the kernel side: `evalD`'s threaded κ IS the context's active custom frames.
The `Config.run`-side analog of `CCorr`. -/
def CCtxCorr (κ : CStore) (K : Bang.EvalCtx) : Prop := κ = ctxCustoms K

theorem ctxStates_updateCtxCustoms : ∀ (K : Bang.EvalCtx) (κ : CStore),
    ctxStates (updateCtxCustoms K κ) = ctxStates K := by
  intro K
  induction K with
  | nil => intro κ; rfl
  | cons fr K ih =>
      intro κ
      cases fr with
      | handleF n h =>
          cases h with
          | custom ℓ p cls =>
              cases κ with
              | nil => simp only [updateCtxCustoms, ctxStates]; rw [ih]
              | cons entry κ' =>
                  obtain ⟨m, pcls⟩ := entry; obtain ⟨p', cls'⟩ := pcls
                  simp only [updateCtxCustoms, ctxStates]; rw [ih]
          | state ℓ s => simp only [updateCtxCustoms, ctxStates]; rw [ih]
          | throws ℓ => simp only [updateCtxCustoms, ctxStates]; rw [ih]
          | transaction ℓ Θ => simp only [updateCtxCustoms, ctxStates]; rw [ih]
      | letF N => simp only [updateCtxCustoms, ctxStates]; rw [ih]
      | appF v => simp only [updateCtxCustoms, ctxStates]; rw [ih]

theorem ctxTxns_updateCtxCustoms : ∀ (K : Bang.EvalCtx) (κ : CStore),
    ctxTxns (updateCtxCustoms K κ) = ctxTxns K := by
  intro K
  induction K with
  | nil => intro κ; rfl
  | cons fr K ih =>
      intro κ
      cases fr with
      | handleF n h =>
          cases h with
          | custom ℓ p cls =>
              cases κ with
              | nil => simp only [updateCtxCustoms, ctxTxns]; rw [ih]
              | cons entry κ' =>
                  obtain ⟨m, pcls⟩ := entry; obtain ⟨p', cls'⟩ := pcls
                  simp only [updateCtxCustoms, ctxTxns]; rw [ih]
          | state ℓ s => simp only [updateCtxCustoms, ctxTxns]; rw [ih]
          | throws ℓ => simp only [updateCtxCustoms, ctxTxns]; rw [ih]
          | transaction ℓ Θ => simp only [updateCtxCustoms, ctxTxns]; rw [ih]
      | letF N => simp only [updateCtxCustoms, ctxTxns]; rw [ih]
      | appF v => simp only [updateCtxCustoms, ctxTxns]; rw [ih]

theorem ctxFullEffect_eq_ctxNetEffect {K : Bang.EvalCtx} {σ : SStore} {τ : THeap} {κ : CStore}
    (hK : CCtxCorr κ (ctxNetEffect K σ τ)) : ctxFullEffect K σ τ κ = ctxNetEffect K σ τ := by
  unfold CCtxCorr at hK
  unfold ctxFullEffect
  rw [hK, updateCtxCustoms_self]

theorem ctxFullEffect_self {K : Bang.EvalCtx} {σ : SStore} {τ : THeap} {κ : CStore}
    (hC : CtxCorr σ K) (hT : CtxTxnCorr τ K) (hK : CCtxCorr κ K) :
    ctxFullEffect K σ τ κ = K := by
  unfold ctxFullEffect
  rw [ctxNetEffect_self hC hT]
  unfold CCtxCorr at hK; rw [hK, updateCtxCustoms_self]

theorem ctxFullEffect_put_custom {K Kᵢ Kₒ : Bang.EvalCtx} {σ : SStore} {τ : THeap}
    {κ : CStore} {n : Nat} {ℓ : Bang.EffectRow.Label} {p next : Val}
    {cls : List (Bang.ClauseKey × Comp)}
    (hC : CtxCorr σ K) (hT : CtxTxnCorr τ K) (hK : CCtxCorr κ K)
    (hsp : Bang.splitAtId K n = some (Kᵢ, .custom ℓ p cls, Kₒ)) :
    ctxFullEffect K σ τ (κ.put n next) =
      Kᵢ ++ Frame.handleF n (.custom ℓ next cls) :: Kₒ := by
  unfold ctxFullEffect
  rw [ctxNetEffect_self hC hT]
  unfold CCtxCorr at hK; rw [hK, updateCtxCustoms_put, customCtxPut_split hsp]

/-- `updateCtxStates` only rewrites STATE-frame values ⇒ the custom projection is invariant. -/
theorem ctxCustoms_updateCtxStates : ∀ (K : Bang.EvalCtx) (σ : SStore),
    ctxCustoms (updateCtxStates K σ) = ctxCustoms K := by
  intro K
  induction K with
  | nil => intro σ; rfl
  | cons fr K ih =>
    intro σ
    cases fr with
    | handleF m h =>
        cases h with
        | state ℓ s =>
            cases σ with
            | nil => simp only [updateCtxStates, ctxCustoms]; exact ih []
            | cons p σ' => simp only [updateCtxStates, ctxCustoms]; exact ih σ'
        | transaction ℓ Θ => simp only [updateCtxStates, ctxCustoms]; rw [ih σ]
        | throws ℓ => simp only [updateCtxStates, ctxCustoms]; exact ih σ
        | custom ℓ p cl => simp only [updateCtxStates, ctxCustoms]; rw [ih σ]
    | letF N => simp only [updateCtxStates, ctxCustoms]; exact ih σ
    | appF v => simp only [updateCtxStates, ctxCustoms]; exact ih σ

/-- `updateCtxTxns` only rewrites TXN-frame heaps ⇒ the custom projection is invariant. -/
theorem ctxCustoms_updateCtxTxns : ∀ (K : Bang.EvalCtx) (τ : THeap),
    ctxCustoms (updateCtxTxns K τ) = ctxCustoms K := by
  intro K
  induction K with
  | nil => intro τ; rfl
  | cons fr K ih =>
    intro τ
    cases fr with
    | handleF m h =>
        cases h with
        | transaction ℓ Θ =>
            cases τ with
            | nil => simp only [updateCtxTxns, ctxCustoms]; exact ih []
            | cons p τ' => simp only [updateCtxTxns, ctxCustoms]; exact ih τ'
        | state ℓ s => simp only [updateCtxTxns, ctxCustoms]; rw [ih τ]
        | throws ℓ => simp only [updateCtxTxns, ctxCustoms]; exact ih τ
        | custom ℓ p cl => simp only [updateCtxTxns, ctxCustoms]; rw [ih τ]
    | letF N => simp only [updateCtxTxns, ctxCustoms]; exact ih τ
    | appF v => simp only [updateCtxTxns, ctxCustoms]; exact ih τ

/-- The custom projection is INVARIANT under the full net-effect rebuild (both value passes touch only
state/txn frames). The `Config.run`-side analog of `hsCustoms_netEffect`. -/
theorem ctxCustoms_ctxNetEffect (K : Bang.EvalCtx) (σ : SStore) (τ : THeap) :
    ctxCustoms (ctxNetEffect K σ τ) = ctxCustoms K := by
  unfold ctxNetEffect
  rw [ctxCustoms_updateCtxTxns, ctxCustoms_updateCtxStates]

/-- `CCtxCorr` rides the net-effect rebuild (custom projection invariant). -/
theorem CCtxCorr_ctxNetEffect {κ : CStore} {K : Bang.EvalCtx} (σ : SStore) (τ : THeap)
    (hK : CCtxCorr κ K) : CCtxCorr κ (ctxNetEffect K σ τ) := by
  unfold CCtxCorr at hK ⊢; rw [hK, ctxCustoms_ctxNetEffect]

/-- Installing a `custom` frame PUSHES its `(p, cls)` onto the custom store — `CCtxCorr` preserved. The
`Config.run`-side analog of `CCorr_install`. -/
theorem CCtxCorr_install {κ : CStore} {n : Nat} {ℓ : Bang.EffectRow.Label} {p : Val}
    {cls : List (Bang.ClauseKey × Comp)} {K : Bang.EvalCtx} (hK : CCtxCorr κ K) :
    CCtxCorr (κ.push n p cls) (Frame.handleF n (.custom ℓ p cls) :: K) := by
  unfold CCtxCorr at hK ⊢; rw [hK]; simp only [ctxCustoms, CStore.push]

/-- A NON-custom handler/non-frame head carries no clause entry: pushing it preserves `CCtxCorr`. -/
theorem CCtxCorr_cons_noncustom {κ : CStore} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hnc : ∀ n ℓ p cls, fr ≠ Frame.handleF n (.custom ℓ p cls)) (hK : CCtxCorr κ K) :
    CCtxCorr κ (fr :: K) := by
  unfold CCtxCorr at hK ⊢; rw [hK]
  cases fr with
  | handleF m h =>
      cases h with
      | state ℓ0 s => simp only [ctxCustoms]
      | throws ℓ0 => simp only [ctxCustoms]
      | transaction ℓ0 Θ => simp only [ctxCustoms]
      | custom ℓ0 p cl => exact absurd rfl (hnc m ℓ0 p cl)
  | letF N => simp only [ctxCustoms]
  | appF w => simp only [ctxCustoms]

/-- `CCtxCorr` for the tail when the top is a `custom` frame (the `handle (custom)` POP): the store's
head entry pops with the frame. The `Config.run`-side analog of `CCorr_pop_custom`. -/
theorem CCtxCorr_pop_custom {κ : CStore} {n : Nat} {ℓ0 : Bang.EffectRow.Label} {p : Val}
    {cls : List (Bang.ClauseKey × Comp)} {K : Bang.EvalCtx}
    (hK : CCtxCorr κ (Frame.handleF n (.custom ℓ0 p cls) :: K)) : CCtxCorr κ.tail K := by
  unfold CCtxCorr at hK ⊢; rw [hK]; simp only [ctxCustoms, List.tail]

/-- `CCtxCorr` rides the POP of a NON-custom top frame: the custom projection skips it. -/
theorem CCtxCorr_pop_noncustom {κ : CStore} {fr : Bang.Frame} {K : Bang.EvalCtx}
    (hnc : ∀ n ℓ p cls, fr ≠ Frame.handleF n (.custom ℓ p cls))
    (hK : CCtxCorr κ (fr :: K)) : CCtxCorr κ K := by
  unfold CCtxCorr at hK ⊢; rw [hK]
  cases fr with
  | handleF m h =>
      cases h with
      | state ℓ0 s => simp only [ctxCustoms]
      | throws ℓ0 => simp only [ctxCustoms]
      | transaction ℓ0 Θ => simp only [ctxCustoms]
      | custom ℓ0 p cl => exact absurd rfl (hnc m ℓ0 p cl)
  | letF N => simp only [ctxCustoms]
  | appF w => simp only [ctxCustoms]

/-- No custom cell at a key the stack keeps strictly below it: `CapsBelow n K ⟹ (ctxCustoms K).get? n =
none`. Mirror of `ctxStates_get_none_of_capsBelow` — the ids of custom frames are all `< n`, so the lookup
misses. Used by `splitAtId_of_ctxCustoms_get` to refute a same-id non-custom shadow. -/
theorem ctxCustoms_get_none_of_capsBelow {n : Nat} : ∀ {K : Bang.EvalCtx},
    Bang.Model.CapsBelow n K → (ctxCustoms K).get? n = none := by
  intro K
  induction K with
  | nil => intro _; rfl
  | cons fr K ih =>
    intro hcb
    cases fr with
    | handleF m h0 =>
        simp only [Bang.Model.CapsBelow] at hcb
        cases h0 with
        | custom ℓ0 p cl =>
            have hmn : ¬ (m = n) := by omega
            have he : (ctxCustoms (Frame.handleF m (Handler.custom ℓ0 p cl) :: K)).get? n
                = (ctxCustoms K).get? n := by
              simp only [ctxCustoms, CStore.get?, List.find?, hmn, decide_false, Bool.false_eq_true, if_false]
            rw [he]; exact ih hcb.2
        | state ℓ0 s0 => simp only [ctxCustoms]; exact ih hcb.2
        | throws ℓ0 => simp only [ctxCustoms]; exact ih hcb.2
        | transaction ℓ0 Θ0 => simp only [ctxCustoms]; exact ih hcb.2
    | letF N => simp only [Bang.Model.CapsBelow] at hcb; simp only [ctxCustoms]; exact ih hcb.2
    | appF w => simp only [Bang.Model.CapsBelow] at hcb; simp only [ctxCustoms]; exact ih hcb.2

/-- **The existence factor for custom ops** (route-B, the Stage-4 perform-arm bridge): a live custom
`(p, cls)` at identity `n` in the store reflects a live `custom` frame at `n` on the stack. `StratFresh`
(id-uniqueness) rules out a same-id state/throws/txn shadow. Mirror of `splitAtId_of_ctxStates_get`. -/
theorem splitAtId_of_ctxCustoms_get {n : Nat} {p : Val} {cls : List (Bang.ClauseKey × Comp)} :
    ∀ {K : Bang.EvalCtx}, Bang.Model.StratFresh K → (ctxCustoms K).get? n = some (p, cls) →
      ∃ Kᵢ ℓ' Kₒ, Bang.splitAtId K n = some (Kᵢ, Handler.custom ℓ' p cls, Kₒ) := by
  intro K
  induction K with
  | nil => intro _ hg; simp [ctxCustoms, CStore.get?] at hg
  | cons fr K ih =>
    intro hsf hg
    cases fr with
    | handleF m h0 =>
        cases h0 with
        | custom ℓ0 p0 cl0 =>
            by_cases hc : m = n
            · subst hc
              have hhead : (ctxCustoms (Frame.handleF m (Handler.custom ℓ0 p0 cl0) :: K)).get? m
                  = some (p0, cl0) := by simp [ctxCustoms, CStore.get?]
              rw [hhead] at hg
              obtain ⟨rfl, rfl⟩ : p = p0 ∧ cls = cl0 := by
                have := Option.some.inj hg; simp only [Prod.mk.injEq] at this; exact ⟨this.1.symm, this.2.symm⟩
              exact ⟨[], ℓ0, K, by simp [Bang.splitAtId]⟩
            · have he : (ctxCustoms (Frame.handleF m (Handler.custom ℓ0 p0 cl0) :: K)).get? n
                  = (ctxCustoms K).get? n := by
                simp only [ctxCustoms, CStore.get?, List.find?, hc, decide_false, Bool.false_eq_true, if_false]
              rw [he] at hg
              simp only [Bang.Model.StratFresh] at hsf
              obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg
              exact ⟨Frame.handleF m (Handler.custom ℓ0 p0 cl0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | state ℓ0 s0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxCustoms K).get? n = some (p, cls) := by simpa only [ctxCustoms] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxCustoms_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.state ℓ0 s0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | throws ℓ0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxCustoms K).get? n = some (p, cls) := by simpa only [ctxCustoms] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxCustoms_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.throws ℓ0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
        | transaction ℓ0 Θ0 =>
            simp only [Bang.Model.StratFresh] at hsf
            have hg' : (ctxCustoms K).get? n = some (p, cls) := by simpa only [ctxCustoms] using hg
            by_cases hc : m = n
            · subst hc; rw [ctxCustoms_get_none_of_capsBelow hsf.1] at hg'; simp at hg'
            · obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf.2 hg'
              exact ⟨Frame.handleF m (Handler.transaction ℓ0 Θ0) :: Ki, ℓ', Ko, by
                simp only [Bang.splitAtId, if_neg hc, hsp, Option.map_some]⟩
    | letF N =>
        simp only [Bang.Model.StratFresh] at hsf
        have hg' : (ctxCustoms K).get? n = some (p, cls) := by simpa only [ctxCustoms] using hg
        obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf hg'
        exact ⟨Frame.letF N :: Ki, ℓ', Ko, by simp only [Bang.splitAtId, hsp, Option.map_some]⟩
    | appF w =>
        simp only [Bang.Model.StratFresh] at hsf
        have hg' : (ctxCustoms K).get? n = some (p, cls) := by simpa only [ctxCustoms] using hg
        obtain ⟨Ki, ℓ', Ko, hsp⟩ := ih hsf hg'
        exact ⟨Frame.appF w :: Ki, ℓ', Ko, by simp only [Bang.splitAtId, hsp, Option.map_some]⟩

/-- If `splitAtId K n` resolves to a `custom ℓ' p cl` frame, the custom store has that entry at key
`n`: `(ctxCustoms K).get? n = some (p, cl)`. Route-B custom mirror of `splitAtId_state_value`/
`splitAtId_txn_value` — the value lookup is by identity `n`; the frame's label `ℓ'` is immaterial to
the custom projection. Induction on `K`. -/
theorem splitAtId_custom_value {n : Nat} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {ℓ' : Bang.EffectRow.Label} {p : Val} {cl : List (Bang.ClauseKey × Comp)},
      Bang.splitAtId K n = some (Kᵢ, Handler.custom ℓ' p cl, Kₒ) →
        (ctxCustoms K).get? n = some (p, cl) := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ ℓ' p cl hs; simp [Bang.splitAtId] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ ℓ' p cl hs
    cases fr with
    | handleF m h0 =>
        simp only [Bang.splitAtId] at hs
        by_cases hc : m = n
        · subst hc
          rw [if_pos rfl] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨_, rfl, _⟩ := hs
          simp [ctxCustoms, CStore.get?, List.find?]
        · rw [if_neg hc] at hs
          cases hsp : Bang.splitAtId K n with
          | none => rw [hsp] at hs; simp at hs
          | some t =>
              obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨_, rfl, _⟩ := hs
              have hv := ih hsp
              cases h0 with
              | custom ℓ0 p0 cl0 => simpa [ctxCustoms, CStore.get?, List.find?, hc] using hv
              | state ℓ0 s0 => simpa [ctxCustoms] using hv
              | throws ℓ0 => simpa [ctxCustoms] using hv
              | transaction ℓ0 Θ0 => simpa [ctxCustoms] using hv
    | letF N =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxCustoms] using ih hsp
    | appF w =>
        simp only [Bang.splitAtId] at hs
        cases hsp : Bang.splitAtId K n with
        | none => rw [hsp] at hs; simp at hs
        | some t =>
            obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨_, rfl, _⟩ := hs
            simpa [ctxCustoms] using ih hsp

/-! ### K-side store-DISJOINTNESS corollary of `StratFresh` (the id-first raise-arm ground).

Under id-first dispatch, a `perform (vcap n2 _)` whose identity resolves in ONE per-kind store must be
absent from the OTHERS — else the fail-loud raise (`evalD`) and the machine could diverge. On the `K`
side (`run_evalD`, which carries `StratFresh`) this is the store-level corollary the run threads directly:
a state cell at `n` ⇒ `splitAtId` finds a STATE frame there (`splitAtId_of_ctxStates_get`); a same-id txn
cell would make `splitAtId` ALSO return a TXN frame (`splitAtId_of_ctxTxns_get`) — but `splitAtId` is a
function, so the two results coincide, and a state frame is not a txn frame. `StratFresh` supplies the
id-uniqueness the existence lemmas need. (K-side twin of the machine-hs disjointness.) -/
theorem ctxTxns_get_none_of_ctxStates_some {n : Nat} {s : Val} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K) (hs : (ctxStates K).get? n = some s) : (ctxTxns K).get? n = none := by
  cases hgt : (ctxTxns K).get? n with
  | none => rfl
  | some Θ =>
      exfalso
      obtain ⟨Kᵢ, ℓs, Kₒ, hsps⟩ := splitAtId_of_ctxStates_get hsf hs
      obtain ⟨Kᵢ', ℓt, Kₒ', hspt⟩ := splitAtId_of_ctxTxns_get hsf hgt
      rw [hsps] at hspt; simp at hspt

theorem ctxCustoms_get_none_of_ctxStates_some {n : Nat} {s : Val} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K) (hs : (ctxStates K).get? n = some s) :
    (ctxCustoms K).get? n = none := by
  cases hgc : (ctxCustoms K).get? n with
  | none => rfl
  | some pcl =>
      exfalso
      obtain ⟨p, cl⟩ := pcl
      obtain ⟨Kᵢ, ℓs, Kₒ, hsps⟩ := splitAtId_of_ctxStates_get hsf hs
      obtain ⟨Kᵢ', ℓc, Kₒ', hspc⟩ := splitAtId_of_ctxCustoms_get hsf hgc
      rw [hsps] at hspc; simp at hspc

theorem ctxCustoms_get_none_of_ctxTxns_some {n : Nat} {Θ : List Val} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K) (ht : (ctxTxns K).get? n = some Θ) :
    (ctxCustoms K).get? n = none := by
  cases hgc : (ctxCustoms K).get? n with
  | none => rfl
  | some pcl =>
      exfalso
      obtain ⟨p, cl⟩ := pcl
      obtain ⟨Kᵢ, ℓt, Kₒ, hspt⟩ := splitAtId_of_ctxTxns_get hsf ht
      obtain ⟨Kᵢ', ℓc, Kₒ', hspc⟩ := splitAtId_of_ctxCustoms_get hsf hgc
      rw [hspt] at hspc; simp at hspc

/-- **The custom-dispatch bridge** (route-B, Stage-4 perform-arm): a custom op serviced by `evalD`'s inline
clause-service corresponds to the kernel `idDispatch` running the clause body against the SAME context `K`
(the custom frame is REINSTALLED in place — `dispatchOn`'s custom arm keeps it live). The store read
`(ctxCustoms K).get? n = some (p, cls)` + `cls.find? op = some clause` witness a live custom frame at `n`
(`splitAtId_of_ctxCustoms_get`), which is deterministically the resolved frame; `capLabelCoh_perform_label`
(supplied by the caller via `CapResolves`) gives the label match. Mirror of `dispatch_state_get`, but the
resume FOCUS is the clause body (not `ret s`). -/
theorem dispatch_custom {n : Nat} {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v p : Val}
    {cls : List (Bang.ClauseKey × Comp)} {clause : Bang.ClauseKey × Comp} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K) (hcr : Bang.CapResolves K n ℓ op)
    (hg : (ctxCustoms K).get? n = some (p, cls))
    (hcl : cls.find? (fun clause => clause.1.op == op) = some clause)
    (hupd : clause.1.updates = false) :
    Bang.idDispatch K n ℓ op v = some (K, Comp.subst p (Comp.subst (Val.shift v) clause.2)) := by
  obtain ⟨Kᵢ, h, Kₒ, hsp, hho⟩ := hcr
  -- the resolved frame is the live custom frame (id-uniqueness): the store read reflects a custom frame at
  -- `n` (`splitAtId_of_ctxCustoms_get`), `splitAtId` deterministic ⇒ it IS `h`; a non-custom `h` is absurd.
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', h = Handler.custom ℓ' p cls := by
    obtain ⟨Kᵢ2, ℓ2, Kₒ2, hsp2⟩ := splitAtId_of_ctxCustoms_get hsf hg
    rw [hsp] at hsp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hsp2
    obtain ⟨_, rfl, _⟩ := hsp2; exact ⟨ℓ2, rfl⟩
  have hrec : Kᵢ ++ Frame.handleF n (Handler.custom ℓ' p cls) :: Kₒ = K := splitAtId_reconstruct hsp
  simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn, hcl,
    hupd, Bool.false_eq_true, if_false]
  rw [hrec]

theorem dispatch_custom_updating {n : Nat} {ℓ : Bang.EffectRow.Label} {op : Bang.OpId}
    {v p resume next : Val} {cls : List (Bang.ClauseKey × Comp)}
    {clause : Bang.ClauseKey × Comp} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K) (hcr : Bang.CapResolves K n ℓ op)
    (hg : (ctxCustoms K).get? n = some (p, cls))
    (hcl : cls.find? (fun clause => clause.1.op == op) = some clause)
    (hupd : clause.1.updates = true)
    (hbody : Comp.subst p (Comp.subst (Val.shift v) clause.2) = .ret (.pair resume next)) :
    ∃ Kᵢ ℓ' Kₒ, Bang.splitAtId K n = some (Kᵢ, .custom ℓ' p cls, Kₒ) ∧
      Bang.idDispatch K n ℓ op v =
        some (Kᵢ ++ Bang.Frame.handleF n (.custom ℓ' next cls) :: Kₒ, .ret resume) := by
  obtain ⟨Kᵢ, h, Kₒ, hsp, hho⟩ := hcr
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', h = Handler.custom ℓ' p cls := by
    obtain ⟨Kᵢ2, ℓ2, Kₒ2, hsp2⟩ := splitAtId_of_ctxCustoms_get hsf hg
    rw [hsp] at hsp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hsp2
    obtain ⟨_, rfl, _⟩ := hsp2; exact ⟨ℓ2, rfl⟩
  refine ⟨Kᵢ, ℓ', Kₒ, hsp, ?_⟩
  simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn, hcl,
    hupd, if_true, hbody]

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
    | handleF m h0 =>
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


/-- A `raise` propagating under a `letF` frame: same `Config.run` outcome (the abort discards the
inner prefix the frame grows). Route-B: identity-keyed + THROWS-conditioned (`splitAtId K n` finds a
`throws` frame — the only kind for which the prepended `letF` is discarded; state/txn KEEP `Kᵢ`). The
single perform-step result is `idDispatch (letF N :: K) = idDispatch K` (`dispatch_letF`). -/
theorem dispatchRun_letF (f g n : Nat) (N : Comp) (K : Bang.EvalCtx) (ℓ : Bang.EffectRow.Label)
    (v : Val) {Kᵢ Kₒ : Bang.EvalCtx} {ℓ0 : Bang.EffectRow.Label}
    (hs : Bang.splitAtId K n = some (Kᵢ, Handler.throws ℓ0, Kₒ)) :
    dispatchRun f g n (Frame.letF N :: K) ℓ "raise" v = dispatchRun f g n K ℓ "raise" v := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [dispatchRun]
    rw [Bang.Config.run_step f _ (by intro g' v' h; simp at h),
        Bang.Config.run_step f _ (by intro g' v' h; simp at h)]
    simp only [Source.step, dispatch_letF N K n ℓ "raise" v hs]




/-- **No `custom` frame is installed in the context** (ADR-0087 rung-2 SCAFFOLDING premise; DROPS at
ADR-0085 Stage 4 when `evalD`'s custom arm is DERIVED and the machine speaks custom — a consumer-safe
strengthening). During Stages 2-3 the calculated machine legitimately does not speak custom (its `evalD`
custom-handle arm is `none`, the machine-side witness), so its correspondence headlines honestly carry
"no custom frame reaches me". VACUOUS for every elaborator-emitted program: custom is UNTYPED (no typing
rule), so no `handle (custom …)` is ever emitted, so no custom frame is reachable in any run. Mirrors the
ADR-0086 `CustomFree` premise-lifecycle pattern (grep-adjacent so the Stage-4 expiry finds both). -/
def NoCustomFrame : Bang.EvalCtx → Prop
  | [] => True
  | Frame.handleF _ (.custom _ _ _) :: _ => False
  | _ :: K => NoCustomFrame K

/-- `NoCustomFrame` passes to the tail (every recursive `run_evalD` case strips or keeps the head). -/
theorem NoCustomFrame.tail {fr : Bang.Frame} {K : Bang.EvalCtx} (h : NoCustomFrame (fr :: K)) :
    NoCustomFrame K := by
  cases fr with
  | handleF m hd => cases hd <;> first | exact h | exact absurd h (by simp [NoCustomFrame])
  | letF N => exact h
  | appF w => exact h

/-- Pushing a NON-custom handler frame preserves `NoCustomFrame`. -/
theorem NoCustomFrame.cons_handleF {n : Nat} {hd : Handler} {K : Bang.EvalCtx}
    (hne : ∀ ℓ p cl, hd ≠ Handler.custom ℓ p cl) (h : NoCustomFrame K) :
    NoCustomFrame (Frame.handleF n hd :: K) := by
  cases hd with
  | custom ℓ p cl => exact absurd rfl (hne ℓ p cl)
  | _ => exact h

theorem NoCustomFrame.cons_letF {N : Comp} {K : Bang.EvalCtx} (h : NoCustomFrame K) :
    NoCustomFrame (Frame.letF N :: K) := h
theorem NoCustomFrame.cons_appF {w : Val} {K : Bang.EvalCtx} (h : NoCustomFrame K) :
    NoCustomFrame (Frame.appF w :: K) := h

/-- `updateCtxStates` only rewrites state-frame VALUES, never frame kinds — so `NoCustomFrame` rides. -/
theorem NoCustomFrame.updateCtxStates {K : Bang.EvalCtx} (σ : SStore) (h : NoCustomFrame K) :
    NoCustomFrame (updateCtxStates K σ) := by
  induction K generalizing σ with
  | nil => exact h
  | cons fr K ih =>
    cases fr with
    | handleF m hd =>
        cases hd with
        | state ℓ0 s0 =>
            cases σ with
            | nil => exact ih [] h.tail
            | cons hd σ' => obtain ⟨_, v⟩ := hd; exact ih σ' h.tail
        | throws ℓ0 => exact ih σ h.tail
        | transaction ℓ0 Θ0 => exact ih σ h.tail
        | custom ℓ0 p cl => exact absurd h (by simp [NoCustomFrame])
    | letF N => exact ih σ h
    | appF w => exact ih σ h

/-- `updateCtxTxns` only rewrites txn-frame VALUES, never frame kinds — so `NoCustomFrame` rides. -/
theorem NoCustomFrame.updateCtxTxns {K : Bang.EvalCtx} (τ : THeap) (h : NoCustomFrame K) :
    NoCustomFrame (updateCtxTxns K τ) := by
  induction K generalizing τ with
  | nil => exact h
  | cons fr K ih =>
    cases fr with
    | handleF m hd =>
        cases hd with
        | transaction ℓ0 Θ0 =>
            cases τ with
            | nil => exact ih [] h.tail
            | cons hd τ' => obtain ⟨_, Θv⟩ := hd; exact ih τ' h.tail
        | state ℓ0 s0 => exact ih τ h.tail
        | throws ℓ0 => exact ih τ h.tail
        | custom ℓ0 p cl => exact absurd h (by simp [NoCustomFrame])
    | letF N => exact ih τ h
    | appF w => exact ih τ h

/-- `NoCustomFrame` rides the full net-effect context rebuild (both value passes). -/
theorem NoCustomFrame.ctxNetEffect {K : Bang.EvalCtx} (σ : SStore) (τ : THeap) (h : NoCustomFrame K) :
    NoCustomFrame (ctxNetEffect K σ τ) :=
  (h.updateCtxStates σ).updateCtxTxns τ

/-- A resolved custom frame contradicts `NoCustomFrame` — the discharge for the now-REAL custom
`NoResume`/`dispatchRun` arms (ADR-0087 rung-2): `splitAtId` returns a frame FROM `K`, so a custom
result witnesses a custom frame `NoCustomFrame` forbids. -/
theorem NoCustomFrame.not_custom {K : Bang.EvalCtx} (h : NoCustomFrame K)
    {n : Nat} {Kᵢ : Bang.EvalCtx} {ℓ' : Bang.EffectRow.Label} {p : Val} {cl : List (ClauseKey × Comp)}
    {Kₒ : Bang.EvalCtx} (hsp : Bang.splitAtId K n = some (Kᵢ, Handler.custom ℓ' p cl, Kₒ)) : False := by
  induction K generalizing Kᵢ Kₒ with
  | nil => simp [Bang.splitAtId] at hsp
  | cons fr K ih =>
    cases fr with
    | handleF m hd =>
        simp only [Bang.splitAtId] at hsp
        by_cases hmn : m = n
        · rw [if_pos hmn] at hsp
          simp only [Option.some.injEq, Prod.mk.injEq] at hsp
          obtain ⟨_, rfl, _⟩ := hsp
          exact absurd h (by simp [NoCustomFrame])
        · rw [if_neg hmn, Option.map_eq_some_iff] at hsp
          obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
          simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
          exact ih h.tail hsp'
    | letF N =>
        simp only [Bang.splitAtId, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
        exact ih h.tail hsp'
    | appF w =>
        simp only [Bang.splitAtId, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
        exact ih h.tail hsp'

/-- **The non-resume invariant** (route-B, U3 raised). At identity `n`, op `op`, the context `K` does NOT
RESUME: any frame `n` resolves to either fails the op (`handlesOp = false`, fail-loud) or is a `throws`
(zero-shot abort). NEVER a resuming `state`/`txn` — which is exactly the shape `evalD` returns `raised`
for (a resumptive op would be serviced inline → `term`). The `Handler.label h` argument is sound for ANY
dispatched `ℓ`: `handlesOp h ℓ op = true` forces `ℓ = h.label` (`handlesOp_label`), so a resuming dispatch
is ruled out regardless. This is what makes `idDispatch`/`Config.run` INVARIANT under prepending a frame
to a raise's context (abort/fail discard the inner prefix; only a resume would keep it). -/
def NoResume (K : Bang.EvalCtx) (n : Nat) (op : Bang.OpId) : Prop :=
  ∀ Kᵢ h Kₒ, Bang.splitAtId K n = some (Kᵢ, h, Kₒ) →
    Bang.handlesOp h (Handler.label h) op = false ∨ ∃ ℓh, h = Handler.throws ℓh

/-- A successful split through a NON-matching head frame prepends that frame to the inner prefix. -/
theorem splitAtId_cons_lift {fr : Bang.Frame} {K : Bang.EvalCtx} {n : Nat}
    {Kᵢ : Bang.EvalCtx} {h : Handler} {Kₒ : Bang.EvalCtx}
    (hfr : ∀ h0, fr ≠ Frame.handleF n h0)
    (hsp : Bang.splitAtId K n = some (Kᵢ, h, Kₒ)) :
    Bang.splitAtId (fr :: K) n = some (fr :: Kᵢ, h, Kₒ) := by
  cases fr with
  | handleF m h0 =>
      have hmn : m ≠ n := fun he => hfr h0 (he ▸ rfl)
      simp only [Bang.splitAtId, if_neg hmn, hsp, Option.map_some]
  | letF N => simp only [Bang.splitAtId, hsp, Option.map_some]
  | appF w => simp only [Bang.splitAtId, hsp, Option.map_some]

/-- `NoResume` strips a NON-matching head frame (the matched handler `h` is unchanged, so its disjunct
transfers). The propagation engine of `evalD_raised_noResume`. -/
theorem noResume_strip_cons {fr : Bang.Frame} {K : Bang.EvalCtx} {n : Nat} {op : Bang.OpId}
    (hfr : ∀ h0, fr ≠ Frame.handleF n h0) (hnr : NoResume (fr :: K) n op) : NoResume K n op := by
  intro Kᵢ h Kₒ hsp; exact hnr (fr :: Kᵢ) h Kₒ (splitAtId_cons_lift hfr hsp)

/-- `CapsBelow` survives the state-value overwrite (the frame IDS — all `CapsBelow` reads — are kept). -/
theorem CapsBelow_updateCtxStates {g : Nat} : ∀ {K : Bang.EvalCtx} (σ : SStore),
    Bang.Model.CapsBelow g K → Bang.Model.CapsBelow g (updateCtxStates K σ) := by
  intro K
  induction K with
  | nil => intro σ _; exact trivial
  | cons fr K ih =>
      intro σ hcb
      cases fr with
      | handleF m h0 =>
          cases h0 with
          | state ℓ0 s0 =>
              simp only [Bang.Model.CapsBelow] at hcb
              cases σ with
              | nil => exact ⟨hcb.1, ih [] hcb.2⟩
              | cons p σ' => obtain ⟨_, w⟩ := p; exact ⟨hcb.1, ih σ' hcb.2⟩
          | throws ℓ0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxStates]
              exact ⟨hcb.1, ih σ hcb.2⟩
          | transaction ℓ0 Θ0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxStates]
              exact ⟨hcb.1, ih σ hcb.2⟩
          | custom ℓ0 p cl =>   -- custom = non-state, updateCtxStates skip (ADR-0085 stage 1)
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxStates]
              exact ⟨hcb.1, ih σ hcb.2⟩
      | letF N =>
          simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxStates]
          exact ⟨hcb.1, ih σ hcb.2⟩
      | appF w =>
          simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxStates]
          exact ⟨hcb.1, ih σ hcb.2⟩

/-- `CapsBelow` survives the txn-heap overwrite (mirror of `CapsBelow_updateCtxStates`). -/
theorem CapsBelow_updateCtxTxns {g : Nat} : ∀ {K : Bang.EvalCtx} (τ : THeap),
    Bang.Model.CapsBelow g K → Bang.Model.CapsBelow g (updateCtxTxns K τ) := by
  intro K
  induction K with
  | nil => intro τ _; exact trivial
  | cons fr K ih =>
      intro τ hcb
      cases fr with
      | handleF m h0 =>
          cases h0 with
          | transaction ℓ0 Θ0 =>
              simp only [Bang.Model.CapsBelow] at hcb
              cases τ with
              | nil => exact ⟨hcb.1, ih [] hcb.2⟩
              | cons p τ' => obtain ⟨_, Θ⟩ := p; exact ⟨hcb.1, ih τ' hcb.2⟩
          | state ℓ0 s0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxTxns]
              exact ⟨hcb.1, ih τ hcb.2⟩
          | throws ℓ0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxTxns]
              exact ⟨hcb.1, ih τ hcb.2⟩
          | custom ℓ0 p cl =>   -- custom = non-txn, updateCtxTxns skip (ADR-0085 stage 1)
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxTxns]
              exact ⟨hcb.1, ih τ hcb.2⟩
      | letF N =>
          simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxTxns]
          exact ⟨hcb.1, ih τ hcb.2⟩
      | appF w =>
          simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxTxns]
          exact ⟨hcb.1, ih τ hcb.2⟩

/-- `CapsBelow` survives the combined net-effect (only stored values change; frame ids are kept). -/
theorem CapsBelow_ctxNetEffect {g : Nat} {K : Bang.EvalCtx} (σ : SStore) (τ : THeap)
    (h : Bang.Model.CapsBelow g K) : Bang.Model.CapsBelow g (ctxNetEffect K σ τ) := by
  unfold ctxNetEffect; exact CapsBelow_updateCtxTxns τ (CapsBelow_updateCtxStates σ h)

/-- `CapsBelow` also survives custom-parameter overwrite. -/
theorem CapsBelow_updateCtxCustoms {g : Nat} : ∀ {K : Bang.EvalCtx} (κ : CStore),
    Bang.Model.CapsBelow g K → Bang.Model.CapsBelow g (updateCtxCustoms K κ) := by
  intro K
  induction K with
  | nil => intro κ _; exact trivial
  | cons fr K ih =>
      intro κ hcb
      cases fr with
      | handleF m h0 =>
          cases h0 with
          | custom ℓ0 p cls =>
              simp only [Bang.Model.CapsBelow] at hcb
              cases κ with
              | nil => exact ⟨hcb.1, ih [] hcb.2⟩
              | cons entry κ' =>
                  obtain ⟨_, pcls⟩ := entry
                  obtain ⟨p', cls'⟩ := pcls
                  exact ⟨hcb.1, ih κ' hcb.2⟩
          | state ℓ0 s0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxCustoms]
              exact ⟨hcb.1, ih κ hcb.2⟩
          | throws ℓ0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxCustoms]
              exact ⟨hcb.1, ih κ hcb.2⟩
          | transaction ℓ0 Θ0 =>
              simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxCustoms]
              exact ⟨hcb.1, ih κ hcb.2⟩
      | letF N =>
          simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxCustoms]
          exact ⟨hcb.1, ih κ hcb.2⟩
      | appF w =>
          simp only [Bang.Model.CapsBelow] at hcb; simp only [updateCtxCustoms]
          exact ⟨hcb.1, ih κ hcb.2⟩

theorem CapsBelow_ctxFullEffect {g : Nat} {K : Bang.EvalCtx}
    (σ : SStore) (τ : THeap) (κ : CStore) (h : Bang.Model.CapsBelow g K) :
    Bang.Model.CapsBelow g (ctxFullEffect K σ τ κ) := by
  unfold ctxFullEffect
  exact CapsBelow_updateCtxCustoms κ (CapsBelow_ctxNetEffect σ τ h)

/-- An ESCAPED capability's label is immaterial to `Config.run`: when `splitAtId K n = none` the
`idDispatch` short-circuits BEFORE reading the label, so `Source.step` is `none` for ANY label and the
run lands on the same `escapedCap`/`outOfFuel` terminal. Used by `run_evalD`'s raised `perform` base case to
discharge the escape sub-case (where `labelOf K n = default ≠` the cap's stored `ℓ`). -/
theorem run_perform_label_irrel {g : Nat} {K : Bang.EvalCtx} {n : Nat} {op : Bang.OpId} {v : Val}
    (ℓ1 ℓ2 : Bang.EffectRow.Label) (hsplit : Bang.splitAtId K n = none) (fuel : Nat) :
    Bang.Config.run fuel (g, K, Comp.perform (Val.vcap n ℓ1) op v)
      = Bang.Config.run fuel (g, K, Comp.perform (Val.vcap n ℓ2) op v) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    have h1 : Bang.Source.step (g, K, Comp.perform (Val.vcap n ℓ1) op v) = none := by
      simp [Bang.Source.step, Bang.idDispatch, hsplit]
    have h2 : Bang.Source.step (g, K, Comp.perform (Val.vcap n ℓ2) op v) = none := by
      simp [Bang.Source.step, Bang.idDispatch, hsplit]
    rw [Bang.Config.run_step f _ (by intro gg u; simp), Bang.Config.run_step f _ (by intro gg u; simp),
        h1, h2]

/-- The dispatch core of the frame-strip: a split matched in `K` (prepended frame `fr`) dispatches
identically — `handlesOp = false` ⇒ both `none`; a `throws` discards the inner prefix so the abort target
is frame-invariant. RESUME is exactly what `NoResume` forbids. -/
theorem idDispatch_prepend_eq {fr : Bang.Frame} {K : Bang.EvalCtx} {n : Nat} {ℓ : Bang.EffectRow.Label}
    {op : Bang.OpId} {v : Val} {Kᵢ Kₒ : Bang.EvalCtx} {h : Handler}
    (hspK : Bang.splitAtId K n = some (Kᵢ, h, Kₒ))
    (hsplit : Bang.splitAtId (fr :: K) n = some (fr :: Kᵢ, h, Kₒ))
    (hnr : NoResume K n op) :
    Bang.idDispatch (fr :: K) n ℓ op v = Bang.idDispatch K n ℓ op v := by
  simp only [Bang.idDispatch, hsplit, hspK, Option.bind_some]
  rcases hnr Kᵢ h Kₒ hspK with hf | ⟨ℓh, rfl⟩
  · by_cases hho : Bang.handlesOp h ℓ op = true
    · exfalso; rw [Bang.handlesOp_label hho] at hf; rw [hf] at hho; exact absurd hho (by simp)
    · rw [Bool.not_eq_true] at hho; rw [hho]; simp
  · simp only [Bang.dispatchOn]

/-- **The frame-strip for a raise** (route-B). `idDispatch` is INVARIANT under prepending a frame to a
non-resuming context: a non-matching head (letF/appF/handleF m≠n) keeps the matched handler (`NoResume`
makes the dispatch abort/fail, frame-blind); a matching head (`handleF n`, the n=g handle case) escapes on
BOTH sides (the op fails the just-installed handler; `n` is fresh-absent below it). -/
theorem idDispatch_cons_noResume {fr : Bang.Frame} {K : Bang.EvalCtx} {n : Nat}
    {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val}
    (hhead : ∀ h0, fr = Frame.handleF n h0 → Bang.handlesOp h0 ℓ op = false ∧ Bang.splitAtId K n = none)
    (hnr : NoResume K n op) :
    Bang.idDispatch (fr :: K) n ℓ op v = Bang.idDispatch K n ℓ op v := by
  by_cases hfr : ∀ h0, fr ≠ Frame.handleF n h0
  · cases hsp : Bang.splitAtId K n with
    | none =>
        have hnone : Bang.splitAtId (fr :: K) n = none := by
          cases fr with
          | handleF m h0 =>
              have hmn : m ≠ n := fun he => (hfr h0) (he ▸ rfl)
              simp only [Bang.splitAtId, if_neg hmn, hsp, Option.map_none]
          | letF N => simp only [Bang.splitAtId, hsp, Option.map_none]
          | appF w => simp only [Bang.splitAtId, hsp, Option.map_none]
        simp only [Bang.idDispatch, hnone, hsp, Option.bind_none]
    | some t =>
        obtain ⟨Kᵢ, h, Kₒ⟩ := t
        exact idDispatch_prepend_eq hsp (splitAtId_cons_lift hfr hsp) hnr
  · push Not at hfr
    obtain ⟨h0, rfl⟩ := hfr
    obtain ⟨hhof, hKnone⟩ := hhead h0 rfl
    rw [show Bang.idDispatch K n ℓ op v = none from by simp [Bang.idDispatch, hKnone]]
    simp [Bang.idDispatch, Bang.splitAtId, hhof]

/-- `Config.run` lifts the `idDispatch` frame-strip to the whole run (same step ⇒ same successor / same
fail-loud terminal). -/
theorem run_perform_cons_eq {g : Nat} {fr : Bang.Frame} {K : Bang.EvalCtx} {n : Nat}
    {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} {v : Val}
    (hid : Bang.idDispatch (fr :: K) n ℓ op v = Bang.idDispatch K n ℓ op v) (fuel : Nat) :
    Bang.Config.run fuel (g, fr :: K, Comp.perform (Val.vcap n ℓ) op v)
      = Bang.Config.run fuel (g, K, Comp.perform (Val.vcap n ℓ) op v) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    rw [Bang.Config.run_step f _ (by intro gg u; simp), Bang.Config.run_step f _ (by intro gg u; simp)]
    have hs1 : Bang.Source.step (g, fr :: K, Comp.perform (Val.vcap n ℓ) op v)
        = (Bang.idDispatch (fr :: K) n ℓ op v).map (fun Kc => (g, Kc.1, Kc.2)) := rfl
    have hs2 : Bang.Source.step (g, K, Comp.perform (Val.vcap n ℓ) op v)
        = (Bang.idDispatch K n ℓ op v).map (fun Kc => (g, Kc.1, Kc.2)) := rfl
    rw [hs1, hs2, hid]

/-- `labelOf` skips a non-matching head frame (the resolved handler — hence its label — is unchanged). -/
theorem labelOf_cons_ne {fr : Bang.Frame} {K : Bang.EvalCtx} {n : Nat}
    (hfr : ∀ h0, fr ≠ Frame.handleF n h0) : labelOf (fr :: K) n = labelOf K n := by
  cases hsp : Bang.splitAtId K n with
  | none =>
      have hnone : Bang.splitAtId (fr :: K) n = none := by
        cases fr with
        | handleF m h0 =>
            have hmn : m ≠ n := fun he => (hfr h0) (he ▸ rfl)
            simp only [Bang.splitAtId, if_neg hmn, hsp, Option.map_none]
        | letF N => simp only [Bang.splitAtId, hsp, Option.map_none]
        | appF w => simp only [Bang.splitAtId, hsp, Option.map_none]
      simp only [labelOf, hnone, hsp]
  | some t =>
      obtain ⟨Kᵢ, h, Kₒ⟩ := t
      simp only [labelOf, splitAtId_cons_lift hfr hsp, hsp, Option.map_some, Option.getD_some]

/-- A fresh id `g` (strictly above every frame, `CapsBelow g K`) does not resolve in `K`. -/
theorem splitAtId_none_of_capsBelow {g : Nat} {K : Bang.EvalCtx} (hcb : Bang.Model.CapsBelow g K) :
    Bang.splitAtId K g = none := by
  cases hsp : Bang.splitAtId K g with
  | none => rfl
  | some t => obtain ⟨Kᵢ, h, Kₒ⟩ := t; exact absurd (Bang.CapCoh.splitAtId_id_lt hcb hsp) (by omega)

/-- **The handle-forward continuation bridge.** `Config.run` of the raise's `perform` is invariant under
prepending the just-popped `handleF g`: if the raise target `ℓ' ≠ g`, the frame-strip applies (NoResume
makes the matched handler abort/fail, frame-blind); if `ℓ' = g`, BOTH escape (the op fails the installed
handler `hhof`, and `g` is fresh-absent below it). The two perform foci carry their OWN `labelOf`. -/
theorem run_perform_pop_handleF {g1 g : Nat} {hd : Handler} {K' : Bang.EvalCtx} {ℓ' : Nat}
    {op' : Bang.OpId} {w : Val} (hcb : Bang.Model.CapsBelow g K') (hnr : NoResume K' ℓ' op')
    (hhof : ℓ' = g → Bang.handlesOp hd (Handler.label hd) op' = false) (fuel : Nat) :
    Bang.Config.run fuel (g1, Frame.handleF g hd :: K',
        Comp.perform (Val.vcap ℓ' (labelOf (Frame.handleF g hd :: K') ℓ')) op' w)
      = Bang.Config.run fuel (g1, K', Comp.perform (Val.vcap ℓ' (labelOf K' ℓ')) op' w) := by
  by_cases hℓg : ℓ' = g
  · subst hℓg
    have hspL : Bang.splitAtId (Frame.handleF ℓ' hd :: K') ℓ' = some ([], hd, K') := by simp [Bang.splitAtId]
    have hlblL : labelOf (Frame.handleF ℓ' hd :: K') ℓ' = Handler.label hd := by
      simp only [labelOf, hspL, Option.map_some, Option.getD_some]
    have hidL : Bang.idDispatch (Frame.handleF ℓ' hd :: K') ℓ' (labelOf (Frame.handleF ℓ' hd :: K') ℓ') op' w = none := by
      rw [hlblL]; simp only [Bang.idDispatch, hspL, Option.bind_some, hhof rfl, Bool.false_eq_true, if_false]
    have hidR : Bang.idDispatch K' ℓ' (labelOf K' ℓ') op' w = none := by
      simp only [Bang.idDispatch, splitAtId_none_of_capsBelow hcb, Option.bind_none]
    cases fuel with
    | zero => rfl
    | succ f =>
      rw [Bang.Config.run_step f _ (by intro gg u; simp), Bang.Config.run_step f _ (by intro gg u; simp)]
      have hsL : Bang.Source.step (g1, Frame.handleF ℓ' hd :: K',
          Comp.perform (Val.vcap ℓ' (labelOf (Frame.handleF ℓ' hd :: K') ℓ')) op' w) = none := by
        show (Bang.idDispatch (Frame.handleF ℓ' hd :: K') ℓ' (labelOf (Frame.handleF ℓ' hd :: K') ℓ') op' w).map _ = none
        rw [hidL]; rfl
      have hsR : Bang.Source.step (g1, K', Comp.perform (Val.vcap ℓ' (labelOf K' ℓ')) op' w) = none := by
        show (Bang.idDispatch K' ℓ' (labelOf K' ℓ') op' w).map _ = none
        rw [hidR]; rfl
      rw [hsL, hsR]
  · have hns : ∀ h0, Frame.handleF g hd ≠ Frame.handleF ℓ' h0 := by
      intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)
    rw [labelOf_cons_ne hns]
    exact run_perform_cons_eq (idDispatch_cons_noResume
      (by intro h0 he; exact absurd ((Frame.handleF.inj he).1.symm) hℓg) hnr) fuel

/-- Strip a `letF` frame from `CapLabelCoh` of a `ret` focus (the raised-propagation pop). -/
theorem capLabelCoh_pop_letF {g1 : Nat} {N : Comp} {K : Bang.EvalCtx} {w : Val}
    (h : CapLabelCoh (g1, Frame.letF N :: K, Comp.ret w)) : CapLabelCoh (g1, K, Comp.ret w) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun p hp => Bang.CapCoh.weakCoh_letF_inv (h1 p hp),
    fun p hp => Bang.CapCoh.weakCoh_letF_inv (h2 p (by simp only [Bang.Model.capsK]; exact List.mem_append_right _ hp))⟩

/-- Strip an `appF` frame from `CapLabelCoh` of a `ret` focus. -/
theorem capLabelCoh_pop_appF {g1 : Nat} {u : Val} {K : Bang.EvalCtx} {w : Val}
    (h : CapLabelCoh (g1, Frame.appF u :: K, Comp.ret w)) : CapLabelCoh (g1, K, Comp.ret w) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun p hp => Bang.CapCoh.weakCoh_appF_inv (h1 p hp),
    fun p hp => Bang.CapCoh.weakCoh_appF_inv (h2 p (by simp only [Bang.Model.capsK]; exact List.mem_append_right _ hp))⟩

/-- Strip a `handleF g` frame from `CapLabelCoh` of a `ret` focus (the handle-forward pop). -/
theorem capLabelCoh_pop_handleF {g1 g : Nat} {hd : Handler} {K : Bang.EvalCtx} {w : Val}
    (hcb : Bang.Model.CapsBelow g K)
    (h : CapLabelCoh (g1, Frame.handleF g hd :: K, Comp.ret w)) : CapLabelCoh (g1, K, Comp.ret w) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun p hp => Bang.CapCoh.weakCoh_handleF_inv hcb (h1 p hp),
    fun p hp => Bang.CapCoh.weakCoh_handleF_inv hcb (h2 p (by simp only [Bang.Model.capsK]; exact List.mem_append_right _ hp))⟩

/-- Strip a `letF` frame from `FreshCfg` of a `ret` focus. -/
theorem freshCfg_pop_letF {g1 : Nat} {N : Comp} {K : Bang.EvalCtx} {w : Val}
    (h : FreshCfg (g1, Frame.letF N :: K, Comp.ret w)) : FreshCfg (g1, K, Comp.ret w) := by
  obtain ⟨hcb, hfoc, hsf, hsk⟩ := h
  exact ⟨hcb.2, hfoc, hsf, fun p hp => hsk p (by simp only [Bang.Model.capsK]; exact List.mem_append_right _ hp)⟩

/-- Strip an `appF` frame from `FreshCfg` of a `ret` focus. -/
theorem freshCfg_pop_appF {g1 : Nat} {u : Val} {K : Bang.EvalCtx} {w : Val}
    (h : FreshCfg (g1, Frame.appF u :: K, Comp.ret w)) : FreshCfg (g1, K, Comp.ret w) := by
  obtain ⟨hcb, hfoc, hsf, hsk⟩ := h
  exact ⟨hcb.2, hfoc, hsf, fun p hp => hsk p (by simp only [Bang.Model.capsK]; exact List.mem_append_right _ hp)⟩

/-- Strip a `handleF g` frame from `FreshCfg` of a `ret` focus. -/
theorem freshCfg_pop_handleF {g1 g : Nat} {hd : Handler} {K : Bang.EvalCtx} {w : Val}
    (h : FreshCfg (g1, Frame.handleF g hd :: K, Comp.ret w)) : FreshCfg (g1, K, Comp.ret w) := by
  obtain ⟨hcb, hfoc, hsf, hsk⟩ := h
  exact ⟨hcb.2, hfoc, hsf.2, fun p hp => hsk p (by simp only [Bang.Model.capsK]; exact List.mem_append_right _ hp)⟩

/-- (★bridge) the **two-part** `evalD ≡ Source.eval` simulation: a `term` part (M
runs to its terminal under K) AND a `raised` part (M raises, dispatched by the
kernel — the `THROW ↔ dispatch` correspondence). Subst-vs-subst, no cross-rep LR.
Induction on the eval fuel `fe`. -/
theorem run_evalD : ∀ fe,
    (∀ M g σ τ κ t g' σ' τ' κ', evalD fe g σ τ κ M = some (.term t, g', σ', τ', κ') →
      ∀ (K : Bang.EvalCtx), CtxCorr σ K → CtxTxnCorr τ K → CCtxCorr κ K →
        CapLabelCoh (g, K, M) → FreshCfg (g, K, M) →
        (CtxCorr σ' (ctxFullEffect K σ' τ' κ') ∧ CtxTxnCorr τ' (ctxFullEffect K σ' τ' κ') ∧
          CCtxCorr κ' (ctxFullEffect K σ' τ' κ') ∧
          CapLabelCoh (g', ctxFullEffect K σ' τ' κ', t) ∧ FreshCfg (g', ctxFullEffect K σ' τ' κ', t)) ∧
        ∀ (fuel : Nat) (r : Bang.Result Val),
          Bang.Config.run fuel (g', ctxFullEffect K σ' τ' κ', t) = r → ∃ F, Bang.Config.run F (g, K, M) = r)
    ∧ (∀ M g σ τ κ n op v g' σ' τ' κ', evalD fe g σ τ κ M = some (.raised n op v, g', σ', τ', κ') →
      ∀ (K : Bang.EvalCtx), CtxCorr σ K → CtxTxnCorr τ K → CCtxCorr κ K →
        CapLabelCoh (g, K, M) → FreshCfg (g, K, M) →
        -- route-A 5th conjunct (build-proven necessary, route-B disproven): a raise NEVER RESUMES — the
        -- target `n` resolves only to none/throws/non-handling in the net-effect context. This is what makes
        -- the continuation's `Config.run` frame-INVARIANT under the letF/appF/handleF the propagation cases push.
        (CtxCorr σ' (ctxFullEffect K σ' τ' κ') ∧ CtxTxnCorr τ' (ctxFullEffect K σ' τ' κ') ∧
          CCtxCorr κ' (ctxFullEffect K σ' τ' κ') ∧
          CapLabelCoh (g', ctxFullEffect K σ' τ' κ', Comp.ret v) ∧ FreshCfg (g', ctxFullEffect K σ' τ' κ', Comp.ret v) ∧
          NoResume (ctxFullEffect K σ' τ' κ') n op) ∧
        ∀ (fuel : Nat) (r : Bang.Result Val),
          dispatchRun fuel g' n (ctxFullEffect K σ' τ' κ') (labelOf (ctxFullEffect K σ' τ' κ') n) op v = r →
            ∃ F, Bang.Config.run F (g, K, M) = r) := by
  intro fe
  induction fe with
  | zero => exact ⟨fun M g σ τ κ t g' σ' τ' κ' h => by simp [evalD] at h,
                   fun M g σ τ κ n op v g' σ' τ' κ' h => by simp [evalD] at h⟩
  | succ fe ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · -- TERM PART
      intro M g σ τ κ t g' σ' τ' κ' h K hCtx hTtx hCK hCoh hFresh
      cases M with
      | ret v =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
          rw [ctxFullEffect_self hCtx hTtx hCK]
          exact ⟨⟨hCtx, hTtx, hCK, hCoh, hFresh⟩,
            fun fuel r hr => ⟨fuel, hr⟩⟩
      | lam M =>
          simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
          obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
          rw [ctxFullEffect_self hCtx hTtx hCK]
          exact ⟨⟨hCtx, hTtx, hCK, hCoh, hFresh⟩,
            fun fuel r hr => ⟨fuel, hr⟩⟩
      | letC M N =>
          simp only [evalD] at h
          cases hM : evalD fe g σ τ κ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                have hCletF : CtxCorr σ (Frame.letF N :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTletF : CtxTxnCorr τ (Frame.letF N :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                have hKletF : CCtxCorr κ (Frame.letF N :: K) :=
                  CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
                -- PUSH the coherence/freshness through `Source.step (g,K,letC M N) → (g, letF N :: K, M)`.
                have hpush : Source.step (g, K, Comp.letC M N) = some (g, Frame.letF N :: K, M) := rfl
                have hFletF := freshCfg_step _ _ hFresh hpush
                have hCletFcoh := capLabelCoh_step _ _ hFresh hCoh hpush
                obtain ⟨⟨hCM, hTM, hKM, hCohR, hFR⟩, kM⟩ :=
                  ihT M g σ τ κ (.ret v) g1 σ1 τ1 κ1 hM (Frame.letF N :: K) hCletF hTletF hKletF hCletFcoh hFletF
                have hcne := ctxFullEffect_cons_nonframe σ1 τ1 κ1
                  (K := K) (fr := Frame.letF N) (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
                  (by intro n ℓ p cls; simp)
                rw [hcne] at hCM hTM hKM hCohR hFR
                have hCM' := CtxCorr_pop_nonstate (by intro n ℓ s; simp) hCM
                have hTM' := CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hTM
                have hKM' := CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                -- POP: rewrite ret v's coherence to `letF N :: ctxFullEffect K σ1 τ1 κ1`, then step to `subst v N`.
                have hpop : Source.step (g1, Frame.letF N :: ctxFullEffect K σ1 τ1 κ1, Comp.ret v)
                    = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.subst v N) := rfl
                have hFsub := freshCfg_step _ _ hFR hpop
                have hCsub := capLabelCoh_step _ _ hFR hCohR hpop
                obtain ⟨⟨hCf, hTf, hKf, hCohF, hFF⟩, kN⟩ :=
                  ihT (Comp.subst v N) g1 σ1 τ1 κ1 t g' σ' τ' κ' h (ctxFullEffect K σ1 τ1 κ1) hCM' hTM' hKM' hCsub hFsub
                rw [ctxFullEffect_ctxFullEffect] at hCf hTf hKf hCohF hFF
                refine ⟨⟨hCf, hTf, hKf, hCohF, hFF⟩, fun fuel r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kN fuel r (by rw [ctxFullEffect_ctxFullEffect]; exact hr)
                have hstep : Bang.Config.run (F2+1) (g1, Frame.letF N :: ctxFullEffect K σ1 τ1 κ1, .ret v) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                rw [← hcne] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
            | (.raised n op w, _, _, _, _), h => simp [Option.bind] at h
      | force a =>
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | vthunk M =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.force (Val.vthunk M)) = some (g, K, M) := rfl
              obtain ⟨hCf, kf⟩ := ihT M g σ τ κ t g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
              exact ⟨hCf, fun fuel r hr => by
                obtain ⟨F', hF'⟩ := kf fuel r hr
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
          cases hM : evalD fe g σ τ κ M with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.term (.lam N), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                have hCappF : CtxCorr σ (Frame.appF v :: K) :=
                  CtxCorr_cons_nonstate (by intro ℓ s; simp) hCtx
                have hTappF : CtxTxnCorr τ (Frame.appF v :: K) :=
                  CtxTxnCorr_cons_nontxn (by intro ℓ Θ; simp) hTtx
                have hKappF : CCtxCorr κ (Frame.appF v :: K) :=
                  CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
                have hpush : Source.step (g, K, Comp.app M v) = some (g, Frame.appF v :: K, M) := rfl
                have hFappF := freshCfg_step _ _ hFresh hpush
                have hCappFcoh := capLabelCoh_step _ _ hFresh hCoh hpush
                obtain ⟨⟨hCM, hTM, hKM, hCohR, hFR⟩, kM⟩ :=
                  ihT M g σ τ κ (.lam N) g1 σ1 τ1 κ1 hM (Frame.appF v :: K) hCappF hTappF hKappF hCappFcoh hFappF
                have hcne := ctxFullEffect_cons_nonframe σ1 τ1 κ1
                  (K := K) (fr := Frame.appF v) (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
                  (by intro n ℓ p cls; simp)
                rw [hcne] at hCM hTM hKM hCohR hFR
                have hCM' := CtxCorr_pop_nonstate (by intro n ℓ s; simp) hCM
                have hTM' := CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hTM
                have hKM' := CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                have hpop : Source.step (g1, Frame.appF v :: ctxFullEffect K σ1 τ1 κ1, Comp.lam N)
                    = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.subst v N) := rfl
                have hFsub := freshCfg_step _ _ hFR hpop
                have hCsub := capLabelCoh_step _ _ hFR hCohR hpop
                obtain ⟨⟨hCf, hTf, hKf, hCohF, hFF⟩, kN⟩ :=
                  ihT (Comp.subst v N) g1 σ1 τ1 κ1 t g' σ' τ' κ' h (ctxFullEffect K σ1 τ1 κ1) hCM' hTM' hKM' hCsub hFsub
                rw [ctxFullEffect_ctxFullEffect] at hCf hTf hKf hCohF hFF
                refine ⟨⟨hCf, hTf, hKf, hCohF, hFF⟩, fun fuel r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kN fuel r (by rw [ctxFullEffect_ctxFullEffect]; exact hr)
                have hstep : Bang.Config.run (F2+1) (g1, Frame.appF v :: ctxFullEffect K σ1 τ1 κ1, .lam N) = r := by
                  simp only [Bang.Config.run, Source.step]; exact hF2
                rw [← hcne] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.ret w), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
            | (.raised n op w, _, _, _, _), h => simp [Option.bind] at h
      | perform cap op2 v2 =>
          -- ID-FIRST (route-B, IDENTITY-keyed). The IDENTITY n2 — which per-kind store holds it (σ/τ/κ,
          -- disjoint by FreshCfg/StratFresh) — picks the arm; the op selects the operation within the
          -- resolved frame; an op the resolved kind can't handle RAISES (fail-loud, the handlesOp image).
          -- The coherence premise (CapLabelCoh) + freshness (FreshCfg) reassemble `CapResolves` at the
          -- perform seam: the store-read supplies the live frame (`splitAtId_of_ctx*_get`),
          -- `capLabelCoh_perform_label` supplies the label match; the kernel step is
          -- `dispatch_state_{get,put}` / `dispatch_txn_service` / `dispatch_custom`; `capLabelCoh_step`/
          -- `freshCfg_step` carry the folded coherence onto the resumed focus. (The store-disjointness is
          -- discharged LOCALLY via the ctx*_get_none_of_capsBelow triple where needed — no cross-store
          -- shadow can arise under StratFresh.)
          obtain ⟨n2, ℓ2, rfl⟩ : ∃ n ℓ, cap = Val.vcap n ℓ := by
            cases cap <;> first | exact ⟨_, _, rfl⟩ | simp [evalD] at h
          simp only [evalD] at h
          -- n2 resolves against σ first (evalD's `match σ.get? n2`).
          cases hg : σ.get? n2 with
          | some sv =>
              rw [hg] at h
              -- state frame at n2: op ∈ {get, put} services; any other op RAISES (⇒ term absurd).
              by_cases hop : op2 = "get"
              · subst hop
                simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                have hgc : (ctxStates K).get? n2 = some sv := by rw [← hCtx]; exact hg
                obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxStates_get hFresh.2.2.1 hgc
                have hlab : ℓ' = ℓ2 := by
                  have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                have hcr : Bang.CapResolves K n2 ℓ2 "get" :=
                  ⟨Kᵢ, Handler.state ℓ' sv, Kₒ, hsp, by subst hlab; simp [Bang.handlesOp]⟩
                have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) "get" v2)
                    = some (g, K, Comp.ret sv) := by
                  simp only [Source.step, dispatch_state_get hFresh.2.2.1 hcr hgc, Option.map_some]
                rw [ctxFullEffect_self hCtx hTtx hCK]
                refine ⟨⟨hCtx, hTtx, hCK, capLabelCoh_step _ _ hFresh hCoh hstep,
                  freshCfg_step _ _ hFresh hstep⟩, fun fuel r hr => ⟨fuel+1, ?_⟩⟩
                simp only [Bang.Config.run, hstep]; exact hr
              · by_cases hop2 : op2 = "put"
                · subst hop2
                  simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl,
                    Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                  have hgc : (ctxStates K).get? n2 = some sv := by rw [← hCtx]; exact hg
                  obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxStates_get hFresh.2.2.1 hgc
                  have hlab : ℓ' = ℓ2 := by
                    have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                  have hcr : Bang.CapResolves K n2 ℓ2 "put" :=
                    ⟨Kᵢ, Handler.state ℓ' sv, Kₒ, hsp, by subst hlab; simp [Bang.handlesOp]⟩
                  have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) "put" v2)
                      = some (g, updateCtxStates K ((ctxStates K).put n2 v2), Comp.ret .vunit) := by
                    simp only [Source.step, dispatch_state_put (w := v2) hFresh.2.2.1 hcr hgc, Option.map_some]
                  have hcoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                  have hfr' := freshCfg_step _ _ hFresh hstep
                  have hK' : CCtxCorr κ (ctxNetEffect K ((ctxStates K).put n2 v2) (ctxTxns K)) := by
                    unfold CCtxCorr at hCK ⊢; rw [hCK, ctxCustoms_ctxNetEffect]
                  subst hCtx; subst hTtx
                  have hC' : ctxStates (ctxNetEffect K ((ctxStates K).put n2 v2) (ctxTxns K))
                      = (ctxStates K).put n2 v2 := by
                    unfold ctxNetEffect; rw [ctxStates_updateCtxTxns]
                    exact ctxStates_updateCtxStates_put hgc
                  have hT' : ctxTxns (ctxNetEffect K ((ctxStates K).put n2 v2) (ctxTxns K)) = ctxTxns K := by
                    unfold ctxNetEffect
                    rw [show ctxTxns K = ctxTxns (updateCtxStates K ((ctxStates K).put n2 v2)) from
                      (ctxTxns_updateCtxStates K _).symm, updateCtxTxns_self_aux, ctxTxns_updateCtxStates]
                  have hctxeq : ctxNetEffect K ((ctxStates K).put n2 v2) (ctxTxns K)
                      = updateCtxStates K ((ctxStates K).put n2 v2) := by
                    unfold ctxNetEffect
                    rw [show ctxTxns K = ctxTxns (updateCtxStates K ((ctxStates K).put n2 v2)) from
                      (ctxTxns_updateCtxStates K _).symm, updateCtxTxns_self_aux]
                  rw [← hctxeq] at hcoh' hfr'
                  rw [ctxFullEffect_eq_ctxNetEffect hK']
                  refine ⟨⟨hC'.symm, hT'.symm, hK', hcoh', hfr'⟩, fun n r hr => ⟨n+1, ?_⟩⟩
                  rw [hctxeq] at hr
                  simp only [Bang.Config.run, hstep]; exact hr
                · -- op the state frame can't handle ⇒ evalD RAISES ⇒ term absurd.
                  simp only [if_neg hop, if_neg hop2] at h; simp at h
          | none =>
          rw [hg] at h
          cases hgt : τ.get? n2 with
          | some Θ =>
              rw [hgt] at h
              -- txn frame at n2: an stm op services; any other op RAISES (⇒ term absurd).
              by_cases hopt : isTxnOp op2 = true
              · simp only [hopt, if_true, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                have hgt' : (ctxTxns K).get? n2 = some Θ := by rw [← hTtx]; exact hgt
                obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxTxns_get hFresh.2.2.1 hgt'
                have hlab : ℓ' = ℓ2 := by
                  have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                have hcr : Bang.CapResolves K n2 ℓ2 op2 :=
                  ⟨Kᵢ, Handler.transaction ℓ' Θ, Kₒ, hsp, by
                    subst hlab; rcases isTxnOp_iff.mp hopt with rfl | rfl | rfl <;> simp [Bang.handlesOp]⟩
                have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op2 v2)
                    = some (g, updateCtxTxns K ((ctxTxns K).put n2 (txnService op2 v2 Θ).2),
                        Comp.ret (txnService op2 v2 Θ).1) := by
                  simp only [Source.step, dispatch_txn_service hFresh.2.2.1 hopt hcr hgt', Option.map_some]
                have hcoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                have hfr' := freshCfg_step _ _ hFresh hstep
                have hK' : CCtxCorr κ (ctxNetEffect K (ctxStates K) ((ctxTxns K).put n2 (txnService op2 v2 Θ).2)) := by
                  unfold CCtxCorr at hCK ⊢; rw [hCK, ctxCustoms_ctxNetEffect]
                subst hCtx; subst hTtx
                have hC' : ctxStates (ctxNetEffect K (ctxStates K) ((ctxTxns K).put n2 (txnService op2 v2 Θ).2))
                    = ctxStates K := by
                  unfold ctxNetEffect; rw [ctxStates_updateCtxTxns, updateCtxStates_self_aux]
                have hT' : ctxTxns (ctxNetEffect K (ctxStates K) ((ctxTxns K).put n2 (txnService op2 v2 Θ).2))
                    = (ctxTxns K).put n2 (txnService op2 v2 Θ).2 := by
                  unfold ctxNetEffect
                  rw [show updateCtxStates K (ctxStates K) = K from updateCtxStates_self_aux]
                  exact ctxTxns_updateCtxTxns_service hgt'
                have hctxeq : ctxNetEffect K (ctxStates K) ((ctxTxns K).put n2 (txnService op2 v2 Θ).2)
                    = updateCtxTxns K ((ctxTxns K).put n2 (txnService op2 v2 Θ).2) := by
                  unfold ctxNetEffect; rw [updateCtxStates_self_aux]
                rw [← hctxeq] at hcoh' hfr'
                rw [ctxFullEffect_eq_ctxNetEffect hK']
                refine ⟨⟨hC'.symm, hT'.symm, hK', hcoh', hfr'⟩, fun n r hr => ⟨n+1, ?_⟩⟩
                rw [hctxeq] at hr
                simp only [Bang.Config.run, hstep]; exact hr
              · -- op the txn frame can't handle ⇒ evalD RAISES ⇒ term absurd.
                rw [Bool.not_eq_true] at hopt; simp only [hopt, Bool.false_eq_true, if_false] at h; simp at h
          | none =>
          rw [hgt] at h
          -- CUSTOM op (ADR-0085 Stage 4): evalD INLINE-SERVICES the clause body against the SAME store (κ
          -- unchanged, frame stays live). Route-B: the store read `κ.get? n2 = some (p,cls)` + `cls.find? op`
          -- witness a live custom frame at `n2` in K (`splitAtId_of_ctxCustoms_get`); the kernel
          -- `dispatch_custom` runs the SAME clause body against K. Recurse via `ihT` on the clause body
          -- (K/σ/τ/κ unchanged), then one perform-step bridges. Mirror of the sim custom perform-service arm.
          cases hck : κ.get? n2 with
          | none => rw [hck] at h; simp at h   -- n2 in no store ⇒ evalD raises ⇒ term absurd
          | some pcls =>
              obtain ⟨p, cls⟩ := pcls
              rw [hck] at h
              cases hcl : cls.find? (fun clause => clause.1.op == op2) with
              | none => simp only [hcl] at h; simp at h   -- op unserviced ⇒ raise ⇒ term absurd
              | some clause =>
                  simp only [hcl] at h
                  have hgc : (ctxCustoms K).get? n2 = some (p, cls) := by rw [← hCK]; exact hck
                  obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxCustoms_get hFresh.2.2.1 hgc
                  have hlab : ℓ' = ℓ2 := by
                    have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                  have hho : Bang.handlesOp (Handler.custom ℓ' p cls) ℓ2 op2 = true := by
                    subst hlab
                    -- the clause exists ⇒ handlesOp fires (op ∈ the clause keys, label matches)
                    have hsome : ((cls.find? (fun clause => clause.1.op == op2)).isSome) = true := by rw [hcl]; rfl
                    simp only [Bang.handlesOp, hsome, Bool.and_true, decide_true]
                  have hcr : Bang.CapResolves K n2 ℓ2 op2 := ⟨Kᵢ, Handler.custom ℓ' p cls, Kₒ, hsp, hho⟩
                  by_cases hupd : clause.1.updates = true
                  · simp only [hupd, if_true] at h
                    split at h
                    · rename_i resume next hbody
                      simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                      obtain ⟨Jᵢ, ℓj, Jₒ, hspj, hid⟩ :=
                        dispatch_custom_updating hFresh.2.2.1 hcr hgc hcl hupd hbody
                      have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op2 v2) =
                          some (g, Jᵢ ++ Frame.handleF n2 (.custom ℓj next cls) :: Jₒ, .ret resume) := by
                        simp only [Source.step, hid, Option.map_some]
                      have hfull := ctxFullEffect_put_custom hCtx hTtx hCK hspj (next := next)
                      have hCfull : CtxCorr σ (ctxFullEffect K σ τ (κ.put n2 next)) := by
                        unfold CtxCorr ctxFullEffect
                        rw [ctxStates_updateCtxCustoms, ctxNetEffect_self hCtx hTtx]
                        exact hCtx
                      have hTfull : CtxTxnCorr τ (ctxFullEffect K σ τ (κ.put n2 next)) := by
                        unfold CtxTxnCorr ctxFullEffect
                        rw [ctxTxns_updateCtxCustoms, ctxNetEffect_self hCtx hTtx]
                        exact hTtx
                      have hKfull : CCtxCorr (κ.put n2 next) (ctxFullEffect K σ τ (κ.put n2 next)) := by
                        unfold CCtxCorr ctxFullEffect
                        rw [ctxNetEffect_self hCtx hTtx, hCK, updateCtxCustoms_put,
                          ctxCustoms_customCtxPut]
                      have hCoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                      have hFresh' := freshCfg_step _ _ hFresh hstep
                      rw [← hfull] at hCoh' hFresh'
                      refine ⟨⟨hCfull, hTfull, hKfull, hCoh', hFresh'⟩, fun fuel r hr => ⟨fuel+1, ?_⟩⟩
                      rw [hfull] at hr
                      simp only [Bang.Config.run, hstep]; exact hr
                    · simp_all
                  · have hupd0 : clause.1.updates = false := Bool.eq_false_of_not_eq_true hupd
                    simp only [hupd0, Bool.false_eq_true, if_false] at h
                    have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op2 v2)
                        = some (g, K, Comp.subst p (Comp.subst (Val.shift v2) clause.2)) := by
                      simp only [Source.step, dispatch_custom hFresh.2.2.1 hcr hgc hcl hupd0, Option.map_some]
                    have hCsub := capLabelCoh_step _ _ hFresh hCoh hstep
                    have hFsub := freshCfg_step _ _ hFresh hstep
                    obtain ⟨⟨hCf, hTf, hKf, hCohF, hFF⟩, kBody⟩ :=
                      ihT (Comp.subst p (Comp.subst (Val.shift v2) clause.2)) g σ τ κ t g' σ' τ' κ' h
                        K hCtx hTtx hCK hCsub hFsub
                    refine ⟨⟨hCf, hTf, hKf, hCohF, hFF⟩, fun fuel r hr => ?_⟩
                    obtain ⟨F, hF⟩ := kBody fuel r hr
                    exact ⟨F+1, by simp only [Bang.Config.run, hstep]; exact hF⟩
      | handle h0 M =>
          -- U3 seam-2: handle-term route-B re-key. MINT id := g, push the identity-keyed frame
          -- `handleF g h0 :: K`, run the substituted body `M' = subst (vcap g h0.label) M` at g+1 (the
          -- kernel MINT step). The body's at-term coherence pops to the outer net-effect context (the
          -- `CtxCorr_ctxNetEffect_pop_*` lemmas) and the UNMARK step (handler-return = identity) transports
          -- coherence/freshness down. Mirrors the proven U2 `sim` handle arm (1723) on the Config.run side.
          simp only [evalD] at h
          cases h0 with
          | custom ℓ0 p0 cls0 =>
              -- route-B INSTALL a custom frame (ADR-0085 Stage 4): MINT id := g, push (id ↦ (p0,cls0)) on
              -- κ, run the SUBSTITUTED body M' = subst (vcap g ℓ0) M at g+1 (kernel MINT). σ/τ pass through
              -- (custom carries no state/heap); κ pops on return (CCtxCorr_pop_custom). A raise FORWARDS
              -- (custom never catches a throws-raise) ⇒ the raised-sub-case is term-absurd. The clause-
              -- service happens at the perform arm (already proven) — this is pure install/pop.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ τ (κ.push g p0 cls0) (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    have hmint : Source.step (g, K, Comp.handle (Handler.custom ℓ0 p0 cls0) M)
                        = some (g+1, Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K,
                            Comp.subst (Val.vcap g ℓ0) M) := rfl
                    have hCinstall : CtxCorr σ (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                      CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
                    have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                      CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
                    have hKinstall : CCtxCorr (κ.push g p0 cls0) (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                      CCtxCorr_install hCK
                    have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
                    have hFreshInstall := freshCfg_step _ _ hFresh hmint
                    obtain ⟨⟨hCM, hTM, hKM, hCohM, hFreshM⟩, kM⟩ :=
                      ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ (κ.push g p0 cls0) (.ret v) g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, p1, cls1, hnetEq⟩ :=
                      CtxCorr_ctxFullEffect_pop_custom hCM hTM
                    have hKpop : CCtxCorr κ1.tail (ctxFullEffect K σ1 τ1 κ1.tail) := by
                      rw [hnetEq] at hKM; exact CCtxCorr_pop_custom hKM
                    rw [hnetEq] at hCohM hFreshM
                    have hunmark : Source.step (g1, Frame.handleF g (Handler.custom ℓ0 p1 cls1) ::
                        ctxFullEffect K σ1 τ1 κ1.tail, Comp.ret v) =
                        some (g1, ctxFullEffect K σ1 τ1 κ1.tail, Comp.ret v) := rfl
                    have hCohPop := capLabelCoh_step _ _ hFreshM hCohM hunmark
                    have hFreshPop := freshCfg_step _ _ hFreshM hunmark
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohPop, hFreshPop⟩, fun fuel r hr => ?_⟩
                    have hstepRun : Config.run (fuel+1)
                        (g1, ctxFullEffect (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) σ1 τ1 κ1,
                          Comp.ret v) = r := by
                      rw [hnetEq]; simp only [Bang.Config.run, hunmark]; exact hr
                    obtain ⟨F, hF⟩ := kM (fuel+1) r hstepRun
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised n' op' w, _, _, _, _), h =>
                    -- custom never catches a throws-raise ⇒ forwards ⇒ raised, contradicting the term part.
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | state ℓ0 s0 =>
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    have hmint : Source.step (g, K, Comp.handle (Handler.state ℓ0 s0) M)
                        = some (g+1, Frame.handleF g (Handler.state ℓ0 s0) :: K,
                            Comp.subst (Val.vcap g ℓ0) M) := rfl
                    have hCinstall : CtxCorr (σ.push g s0) (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                      CtxCorr_install hCtx
                    have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                      CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
                    have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                      CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
                    have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
                    have hFreshInstall := freshCfg_step _ _ hFresh hmint
                    obtain ⟨⟨hCM, hTM, hKM, hCohM, hFreshM⟩, kM⟩ :=
                      ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) (σ.push g s0) τ κ (.ret v) g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.state ℓ0 s0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_state hCM hTM
                    have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1.tail τ1 κ1) := by
                      rw [hnetEq] at hKM
                      exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                    rw [hnetEq] at hCohM hFreshM
                    have hunmark : Source.step (g1, Frame.handleF g
                        (Handler.state ℓ0 (σ1.headD (default, default)).2) :: ctxFullEffect K σ1.tail τ1 κ1,
                        Comp.ret v) = some (g1, ctxFullEffect K σ1.tail τ1 κ1, Comp.ret v) := rfl
                    have hCohPop := capLabelCoh_step _ _ hFreshM hCohM hunmark
                    have hFreshPop := freshCfg_step _ _ hFreshM hunmark
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohPop, hFreshPop⟩, fun fuel r hr => ?_⟩
                    have hstepRun : Config.run (fuel+1)
                        (g1, ctxFullEffect (Frame.handleF g (Handler.state ℓ0 s0) :: K) σ1 τ1 κ1,
                          Comp.ret v) = r := by
                      rw [hnetEq]; simp only [Bang.Config.run, hunmark]; exact hr
                    obtain ⟨F, hF⟩ := kM (fuel+1) r hstepRun
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised n' op' w, _, _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | throws ℓ0 =>
              -- throws install: no store push. A normal return pops the throws frame (UNMARK, like state
              -- but stores pass through). A raise CAUGHT by THIS handler's identity g (op = "raise") aborts
              -- to a `ret w` term — consumes the raised IH (`ihR`), the FIRST consumer of it in run_evalD.
              simp only [Handler.label] at h
              have hmint : Source.step (g, K, Comp.handle (Handler.throws ℓ0) M)
                  = some (g+1, Frame.handleF g (Handler.throws ℓ0) :: K, Comp.subst (Val.vcap g ℓ0) M) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              cases hM : evalD fe (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    obtain ⟨⟨hCM, hTM, hKM, hCohM, hFreshM⟩, kM⟩ :=
                      ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ (.ret v) g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.throws ℓ0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_throws hCM hTM
                    have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                      rw [hnetEq] at hKM
                      exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                    rw [hnetEq] at hCohM hFreshM
                    have hunmark : Source.step (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxFullEffect K σ1 τ1 κ1,
                        Comp.ret v) = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.ret v) := rfl
                    have hCohPop := capLabelCoh_step _ _ hFreshM hCohM hunmark
                    have hFreshPop := freshCfg_step _ _ hFreshM hunmark
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohPop, hFreshPop⟩, fun fuel r hr => ?_⟩
                    have hstepRun : Config.run (fuel+1)
                        (g1, ctxFullEffect (Frame.handleF g (Handler.throws ℓ0) :: K) σ1 τ1 κ1, Comp.ret v) = r := by
                      rw [hnetEq]; simp only [Bang.Config.run, hunmark]; exact hr
                    obtain ⟨F, hF⟩ := kM (fuel+1) r hstepRun
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    by_cases hc : ℓ' = g ∧ op' = "raise"
                    · -- CAUGHT: M' raises to identity g (this handler), op "raise" ⇒ abort to `ret w`.
                      simp only [Option.bind_some, if_pos hc, Option.some.injEq, Prod.mk.injEq,
                        Outcome.term.injEq] at h
                      obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                      obtain ⟨hcn, rfl⟩ := hc; subst ℓ'
                      obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, _⟩, kR⟩ :=
                        ihR (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ τ κ g "raise" w g1 σ1 τ1 κ1 hM
                          (Frame.handleF g (Handler.throws ℓ0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                      obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_throws hCr hTr
                      have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                        rw [hnetEq] at hKr
                        exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKr
                      rw [hnetEq] at hCohr hFreshr
                      have hunmark : Source.step (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxFullEffect K σ1 τ1 κ1,
                          Comp.ret w) = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.ret w) := rfl
                      have hCohPop := capLabelCoh_step _ _ hFreshr hCohr hunmark
                      have hFreshPop := freshCfg_step _ _ hFreshr hunmark
                      refine ⟨⟨hCpop, hTpop, hKpop, hCohPop, hFreshPop⟩, fun fuel r hr => ?_⟩
                      -- the kernel ABORT step: `perform (vcap g ℓ0) "raise" w` over the throws frame at id g
                      -- resolves it (label ℓ0) and aborts to the outer context with `ret w`.
                      have hsp : Bang.splitAtId (Frame.handleF g (Handler.throws ℓ0) :: ctxFullEffect K σ1 τ1 κ1) g
                          = some ([], Handler.throws ℓ0, ctxFullEffect K σ1 τ1 κ1) := by simp [Bang.splitAtId]
                      have hho : Bang.handlesOp (Handler.throws ℓ0) ℓ0 "raise" = true := by simp [Bang.handlesOp]
                      have hid : Bang.idDispatch (Frame.handleF g (Handler.throws ℓ0) :: ctxFullEffect K σ1 τ1 κ1)
                          g ℓ0 "raise" w = some (ctxFullEffect K σ1 τ1 κ1, Comp.ret w) := by
                        simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn]
                      have hstep_perf : Source.step (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxFullEffect K σ1 τ1 κ1,
                          Comp.perform (Val.vcap g ℓ0) "raise" w) = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.ret w) := by
                        simp only [Source.step, hid, Option.map_some]
                      have hlabel : labelOf (ctxFullEffect (Frame.handleF g (Handler.throws ℓ0) :: K) σ1 τ1 κ1) g = ℓ0 := by
                        rw [hnetEq]; simp only [labelOf, hsp, Option.map_some, Option.getD_some, Handler.label]
                      have hdr : dispatchRun (fuel+1) g1 g
                          (ctxFullEffect (Frame.handleF g (Handler.throws ℓ0) :: K) σ1 τ1 κ1)
                          (labelOf (ctxFullEffect (Frame.handleF g (Handler.throws ℓ0) :: K) σ1 τ1 κ1) g) "raise" w = r := by
                        rw [hlabel, hnetEq]
                        simp only [dispatchRun]
                        rw [Bang.Config.run_step fuel _ (by intro gg vv hcontra; simp at hcontra)]
                        simp only [hstep_perf]; exact hr
                      obtain ⟨F, hF⟩ := kR (fuel+1) r hdr
                      exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                    · simp only [Option.bind_some, if_neg hc, Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
          | transaction ℓ0 Θ =>
              -- MIRROR of the state arm on the τ side: install `handleF g (transaction ℓ0 Θ) :: K`,
              -- push the heap `τ.push g Θ`, run M' at g+1; a normal return POPs the heap (τ1.tail). Free
              -- rollback — the popped heap is discarded with the frame.
              simp only [Handler.label] at h
              cases hM : evalD fe (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.term (.ret v), g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                      Outcome.term.injEq] at h
                    obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
                    have hmint : Source.step (g, K, Comp.handle (Handler.transaction ℓ0 Θ) M)
                        = some (g+1, Frame.handleF g (Handler.transaction ℓ0 Θ) :: K,
                            Comp.subst (Val.vcap g ℓ0) M) := rfl
                    have hCinstall : CtxCorr σ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                      CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
                    have hTinstall : CtxTxnCorr (τ.push g Θ) (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                      CtxTxnCorr_install hTtx
                    have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                      CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
                    have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
                    have hFreshInstall := freshCfg_step _ _ hFresh hmint
                    obtain ⟨⟨hCM, hTM, hKM, hCohM, hFreshM⟩, kM⟩ :=
                      ihT (Comp.subst (Val.vcap g ℓ0) M) (g+1) σ (τ.push g Θ) κ (.ret v) g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_txn hCM hTM
                    have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1 τ1.tail κ1) := by
                      rw [hnetEq] at hKM
                      exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                    rw [hnetEq] at hCohM hFreshM
                    have hunmark : Source.step (g1, Frame.handleF g
                        (Handler.transaction ℓ0 (τ1.headD (default, default)).2) :: ctxFullEffect K σ1 τ1.tail κ1,
                        Comp.ret v) = some (g1, ctxFullEffect K σ1 τ1.tail κ1, Comp.ret v) := rfl
                    have hCohPop := capLabelCoh_step _ _ hFreshM hCohM hunmark
                    have hFreshPop := freshCfg_step _ _ hFreshM hunmark
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohPop, hFreshPop⟩, fun fuel r hr => ?_⟩
                    have hstepRun : Config.run (fuel+1)
                        (g1, ctxFullEffect (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) σ1 τ1 κ1,
                          Comp.ret v) = r := by
                      rw [hnetEq]; simp only [Bang.Config.run, hunmark]; exact hr
                    obtain ⟨F, hF⟩ := kM (fuel+1) r hstepRun
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.lam M2), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
                | (.raised n' op' w, _, _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
      | case a b d =>
          -- ADT sum elim (Unit 6): the kernel `Source.step` reduces in place (Operational.lean 260-261).
          -- Mirror `force`: recurse via `ihT` on the reduced branch, then one `Source.step` bridges.
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | inl v =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.case (Val.inl v) b d) = some (g, K, Comp.subst v b) := rfl
              obtain ⟨hCf, kf⟩ := ihT (Comp.subst v b) g σ τ κ t g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
              exact ⟨hCf, fun n r hr => by
                obtain ⟨F', hF'⟩ := kf n r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | inr v =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.case (Val.inr v) b d) = some (g, K, Comp.subst v d) := rfl
              obtain ⟨hCf, kf⟩ := ihT (Comp.subst v d) g σ τ κ t g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
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
          | vcap n ℓ => simp [evalD] at h
          | pair v w =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.split (Val.pair v w) b)
                  = some (g, K, Comp.subst v (Comp.subst (Val.shift w) b)) := rfl
              obtain ⟨hCf, kf⟩ := ihT (Comp.subst v (Comp.subst (Val.shift w) b)) g σ τ κ t g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
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
          | vcap n ℓ => simp [evalD] at h
          | fold v =>
              simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
              obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
              have hstep : Source.step (g, K, Comp.unfold (Val.fold v)) = some (g, K, Comp.ret v) := rfl
              rw [ctxFullEffect_self hCtx hTtx hCK]
              exact ⟨⟨hCtx, hTtx, hCK, capLabelCoh_step _ _ hFresh hCoh hstep, freshCfg_step _ _ hFresh hstep⟩,
                fun n r hr => ⟨n+1, by simp only [Bang.Config.run, Source.step]; exact hr⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
      | oom => simp [evalD] at h
      | wrong a => simp [evalD] at h
      | binop op v w =>
          -- δ-rule (#40): on closed vints binop erases to `ret (op.eval a b)`, one `Source.step` over the
          -- `ret`-terminal close (stores unchanged), exactly like `unfold (fold v)`; non-vint operands `none`.
          cases v <;> cases w <;>
            first
            | (rename_i a b
               simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
               obtain ⟨ht, hg, hσ, hτ, hκ⟩ := h; subst ht; subst hg; subst hσ; subst hτ; subst hκ
               have hstep : Source.step (g, K, Comp.binop op (Val.vint a) (Val.vint b))
                   = some (g, K, Comp.ret (op.eval a b)) := rfl
               rw [ctxFullEffect_self hCtx hTtx hCK]
               exact ⟨⟨hCtx, hTtx, hCK, capLabelCoh_step _ _ hFresh hCoh hstep, freshCfg_step _ _ hFresh hstep⟩,
                 fun n r hr => ⟨n+1, by simp only [Bang.Config.run, Source.step]; exact hr⟩⟩)
            | simp [evalD] at h
    · -- RAISED PART (U3 seam-3). Mirrors the U2 `sim` raised arm on the `Config.run`/`dispatchRun` side.
      -- The conclusion folds `CapLabelCoh (g', ctxFullEffect K σ' τ' κ', ret v)` (REFUTE-WATCH: CONFIRMED —
      -- `capsV v ⊆ capsC` of the focus in every case, so the raised value's coherence is a sub-multiset of
      -- the focus coherence the premise already carries). The continuation re-performs the op at the outer
      -- context; the BASE (`perform`) case is the only place a raise originates, the rest propagate via `ihR`.
      intro M g σ τ κ n op v g' σ' τ' κ' h K hCtx hTtx hCK hCoh hFresh
      cases M with
      | ret w => simp [evalD] at h
      | lam M => simp [evalD] at h
      | perform cap op2 v2 =>
          -- OP-FIRST raise (route-B, identity-keyed): the op matched NO resumptive frame at IDENTITY n2
          -- (get/put with no state cell, txn op with no txn cell, or a non-resumptive op). The stores are
          -- unchanged (g'=g, σ'=σ, τ'=τ ⇒ `ctxFullEffect K σ τ κ = K`), so the continuation's `dispatchRun`
          -- RE-PERFORMS exactly the kernel's own `perform` — they agree up to the cap label, which `labelOf`
          -- reconstructs (`= ℓ2` when the cap resolves, by `WeakCoh`; immaterial on escape, `run_perform_label_irrel`).
          obtain ⟨n2, ℓ2, rfl⟩ : ∃ n ℓ, cap = Val.vcap n ℓ := by
            cases cap <;> first | exact ⟨_, _, rfl⟩ | simp [evalD] at h
          simp only [evalD] at h
          -- one helper closing every raise sub-case: conclusion (focus-cap-shrink + NoResume from store-miss)
          -- + continuation (label match/escape). The store-miss hyps rule out the resuming-kind frame. ID-FIRST:
          -- a THIRD custom disjunct (no custom cell OR the op misses the clause list) — the now-REAL custom
          -- dispatch, no longer excluded by NoCustomFrame; `splitAtId_custom_value` mirrors state/txn.
          have close : ∀ (o : Bang.OpId),
              ((ctxStates K).get? n2 = none ∨ (o ≠ "get" ∧ o ≠ "put")) →
              ((ctxTxns K).get? n2 = none ∨ isTxnOp o = false) →
              (∀ p cl, (ctxCustoms K).get? n2 = some (p, cl) → (cl.find? (fun clause => clause.1.op == o)).isNone) →
              (CtxCorr σ (ctxFullEffect K σ τ κ) ∧ CtxTxnCorr τ (ctxFullEffect K σ τ κ) ∧
                CCtxCorr κ (ctxFullEffect K σ τ κ) ∧
                CapLabelCoh (g, ctxFullEffect K σ τ κ, Comp.ret v2) ∧ FreshCfg (g, ctxFullEffect K σ τ κ, Comp.ret v2) ∧
                NoResume (ctxFullEffect K σ τ κ) n2 o) ∧
              ∀ (fuel : Nat) (r : Bang.Result Val),
                dispatchRun fuel g n2 (ctxFullEffect K σ τ κ) (labelOf (ctxFullEffect K σ τ κ) n2) o v2 = r →
                  ∃ F, Bang.Config.run F (g, K, Comp.perform (Val.vcap n2 ℓ2) o v2) = r := by
            intro o hst htx hcus
            rw [ctxFullEffect_self hCtx hTtx hCK]
            refine ⟨⟨hCtx, hTtx, hCK,
              ⟨fun p hp => hCoh.1 p (by simp only [Bang.Model.capsC] at hp ⊢; exact List.mem_append_right _ hp), hCoh.2⟩,
              ⟨hFresh.1, fun p hp => hFresh.2.1 p (by simp only [Bang.Model.capsC] at hp ⊢; exact List.mem_append_right _ hp),
                hFresh.2.2.1, hFresh.2.2.2⟩, ?_⟩, fun fuel r hr => ?_⟩
            · -- NoResume K n2 o: a resolved frame is throws (abort), or fails the op (the resuming kind is
              -- ruled out by the store-miss it would imply).
              intro Kᵢ h Kₒ hsp
              cases h with
              | throws ℓ' => exact Or.inr ⟨ℓ', rfl⟩
              | state ℓ' s =>
                  rcases hst with hmiss | ⟨hng, hnp⟩
                  · exfalso; rw [splitAtId_state_value hsp] at hmiss; exact absurd hmiss (by simp)
                  · left
                    have e1 : (o == "get") = false := by simpa using hng
                    have e2 : (o == "put") = false := by simpa using hnp
                    simp [Handler.label, Bang.handlesOp, e1, e2]
              | transaction ℓ' Θ =>
                  rcases htx with hmiss | hnt
                  · exfalso; rw [splitAtId_txn_value hsp] at hmiss; exact absurd hmiss (by simp)
                  · left
                    simp only [isTxnOp, Bool.or_eq_false_iff] at hnt
                    obtain ⟨⟨ea, eb⟩, ec⟩ := hnt
                    simp only [Handler.label, Bang.handlesOp]
                    simp [show (o == "newTVar") = false from by simpa using ea,
                      show (o == "readTVar") = false from by simpa using eb,
                      show (o == "writeTVar") = false from by simpa using ec]
              | custom ℓ' p cl =>
                  -- id-first: a custom frame CAN sit in K now. It fails to handle `o` — the clause list misses
                  -- (`hcus` at the resolved custom cell `splitAtId_custom_value`) ⇒ handlesOp = false ⇒ no resume.
                  left
                  have hmiss := hcus p cl (splitAtId_custom_value hsp)
                  simp only [Handler.label, Bang.handlesOp, Option.isNone_iff_eq_none.mp hmiss,
                    Option.isSome_none, Bool.and_false]
            · simp only [dispatchRun] at hr
              cases hsp : Bang.splitAtId K n2 with
              | none =>
                  exact ⟨fuel, by rw [run_perform_label_irrel ℓ2 (labelOf K n2) hsp fuel]; exact hr⟩
              | some t =>
                  obtain ⟨Kᵢ, hh, Kₒ⟩ := t
                  have hwk : Bang.CapCoh.WeakCoh K (n2, ℓ2) := hCoh.1 (n2, ℓ2) (by simp [Bang.Model.capsC, Bang.Model.capsV])
                  have hlab : labelOf K n2 = ℓ2 := by
                    simp only [labelOf, hsp, Option.map_some, Option.getD_some]; exact hwk Kᵢ hh Kₒ hsp
                  rw [hlab] at hr; exact ⟨fuel, hr⟩
          -- ID-FIRST raise (route-B): n2 resolves in NO store, or its resolved-kind frame fails op2 (fail-loud).
          -- Case-split on the store the identity resolves in (σ→τ→κ), mirroring the id-first evalD raise arm.
          cases hg : σ.get? n2 with
          | some sv =>
              rw [hg] at h
              -- state frame at n2: get/put SERVICE (term), so a raise needs op ∉ {get,put}.
              by_cases hop : op2 = "get"
              · subst hop; simp only [if_pos rfl] at h; simp at h
              · by_cases hop2 : op2 = "put"
                · subst hop2; simp only [if_neg (by decide : ¬ ("put" = "get")), if_pos rfl] at h; simp at h
                · simp only [if_neg hop, if_neg hop2, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                  -- n2 resolves in σ (state frame) ⇒ absent from τ/κ by StratFresh id-uniqueness
                  -- (ctxStates_some_ctxTxns_none / _ctxCustoms_none — the K-side store-disjointness corollary).
                  have hsc := hCtx ▸ hg
                  exact close _ (Or.inr ⟨hop, hop2⟩)
                    (Or.inl (ctxTxns_get_none_of_ctxStates_some hFresh.2.2.1 hsc))
                    (by intro p cl hc; exact absurd hc (by rw [ctxCustoms_get_none_of_ctxStates_some hFresh.2.2.1 hsc]; simp))
          | none =>
          rw [hg] at h
          cases hgt : τ.get? n2 with
          | some Θ =>
              rw [hgt] at h
              by_cases hopt : isTxnOp op2 = true
              · simp only [hopt, if_true] at h; simp at h
              · rw [Bool.not_eq_true] at hopt
                simp only [hopt, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq,
                  Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                -- n2 resolves in τ (txn frame) ⇒ absent from σ (hg) and κ (StratFresh id-uniqueness).
                have htc := hTtx ▸ hgt
                exact close _ (Or.inl (by rw [← hCtx]; exact hg)) (Or.inr hopt)
                  (by intro p cl hc; exact absurd hc (by rw [ctxCustoms_get_none_of_ctxTxns_some hFresh.2.2.1 htc]; simp))
          | none =>
          rw [hgt] at h
          cases hck : κ.get? n2 with
          | none =>
              simp only [hck, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
              obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
              exact close _ (Or.inl (by rw [← hCtx]; exact hg)) (Or.inl (by rw [← hTtx]; exact hgt))
                (by intro p cl hc; rw [← hCK] at hc; rw [hck] at hc; exact absurd hc (by simp))
          | some pcls =>
              obtain ⟨p, cls⟩ := pcls
              rw [hck] at h
              cases hcl : cls.find? (fun clause => clause.1.op == op2) with
              | some clause =>
                  -- clause HIT ⇒ evalD SERVICES (recurses) ⇒ raise came from the clause body; recurse via ihR.
                  simp only [hcl] at h
                  have hgc : (ctxCustoms K).get? n2 = some (p, cls) := by rw [← hCK]; exact hck
                  obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxCustoms_get hFresh.2.2.1 hgc
                  have hlab : ℓ' = ℓ2 := by
                    have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                  have hho : Bang.handlesOp (Handler.custom ℓ' p cls) ℓ2 op2 = true := by
                    subst hlab
                    have hsome : ((cls.find? (fun clause => clause.1.op == op2)).isSome) = true := by rw [hcl]; rfl
                    simp only [Bang.handlesOp, hsome, Bool.and_true, decide_true]
                  have hcr : Bang.CapResolves K n2 ℓ2 op2 := ⟨Kᵢ, Handler.custom ℓ' p cls, Kₒ, hsp, hho⟩
                  by_cases hupd : clause.1.updates = true
                  · simp only [hupd, if_true] at h
                    split at h <;> simp_all
                  · have hupd0 : clause.1.updates = false := Bool.eq_false_of_not_eq_true hupd
                    simp only [hupd0, Bool.false_eq_true, if_false] at h
                    have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op2 v2)
                        = some (g, K, Comp.subst p (Comp.subst (Val.shift v2) clause.2)) := by
                      simp only [Source.step,
                        dispatch_custom hFresh.2.2.1 hcr hgc hcl hupd0, Option.map_some]
                    have hCsub := capLabelCoh_step _ _ hFresh hCoh hstep
                    have hFsub := freshCfg_step _ _ hFresh hstep
                    obtain ⟨hpair, kR⟩ :=
                      ihR (Comp.subst p (Comp.subst (Val.shift v2) clause.2)) g σ τ κ n op v g' σ' τ' κ' h
                        K hCtx hTtx hCK hCsub hFsub
                    exact ⟨hpair, fun fuel r hr => by
                      obtain ⟨F1, hF1⟩ := kR fuel r hr
                      exact ⟨F1+1, by simp only [Bang.Config.run, hstep]; exact hF1⟩⟩
              | none =>
                  simp only [hcl, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                  exact close _ (Or.inl (by rw [← hCtx]; exact hg)) (Or.inl (by rw [← hTtx]; exact hgt))
                    (by intro p' cl' hc'; rw [← hCK] at hc'; rw [hck] at hc'
                        simp only [Option.some.injEq, Prod.mk.injEq] at hc'
                        obtain ⟨rfl, rfl⟩ := hc'; rw [Option.isNone_iff_eq_none]; exact hcl)
      | force a =>
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | vthunk M =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.force (Val.vthunk M)) = some (g, K, M) := rfl
              obtain ⟨hpair, kR⟩ := ihR M g σ τ κ n op v g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
              exact ⟨hpair, fun fuel r hr => by
                obtain ⟨F', hF'⟩ := kR fuel r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | case a b d =>
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | inl sv =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.case (Val.inl sv) b d) = some (g, K, Comp.subst sv b) := rfl
              obtain ⟨hpair, kR⟩ := ihR (Comp.subst sv b) g σ τ κ n op v g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
              exact ⟨hpair, fun fuel r hr => by
                obtain ⟨F', hF'⟩ := kR fuel r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | inr sv =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.case (Val.inr sv) b d) = some (g, K, Comp.subst sv d) := rfl
              obtain ⟨hpair, kR⟩ := ihR (Comp.subst sv d) g σ τ κ n op v g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
              exact ⟨hpair, fun fuel r hr => by
                obtain ⟨F', hF'⟩ := kR fuel r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | pair w1 w2 => simp [evalD] at h
          | fold w => simp [evalD] at h
      | split a b =>
          cases a with
          | vcap n ℓ => simp [evalD] at h
          | pair sv sw =>
              simp only [evalD] at h
              have hstep : Source.step (g, K, Comp.split (Val.pair sv sw) b)
                  = some (g, K, Comp.subst sv (Comp.subst (Val.shift sw) b)) := rfl
              obtain ⟨hpair, kR⟩ := ihR (Comp.subst sv (Comp.subst (Val.shift sw) b)) g σ τ κ n op v g' σ' τ' κ' h K hCtx hTtx hCK
                (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep)
              exact ⟨hpair, fun fuel r hr => by
                obtain ⟨F', hF'⟩ := kR fuel r hr
                exact ⟨F'+1, by simp only [Bang.Config.run, Source.step]; exact hF'⟩⟩
          | vunit => simp [evalD] at h
          | vint x => simp [evalD] at h
          | vvar i => simp [evalD] at h
          | vthunk M => simp [evalD] at h
          | inl w => simp [evalD] at h
          | inr w => simp [evalD] at h
          | fold w => simp [evalD] at h
      | unfold a =>
          -- `unfold` always yields `term (ret v)` — never `raised`, so vacuous.
          cases a with
          | vcap n ℓ => simp [evalD] at h
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
      | binop op v w =>
          -- δ-rule (#40): binop reduces to `term (ret (op.eval a b))` on closed vints, `none` otherwise —
          -- NEVER `raised`, so every operand shape is false-by-contradiction here.
          cases v <;> cases w <;> simp [evalD] at h
      | letC M0 N =>
          -- TWO live sub-cases: (a) M0 raises → propagate; (b) M0 returns `ret v0`, then `subst v0 N` raises
          -- (needs `ihT` for the M0-store-alignment — the reason this MUST be co-induced with the term part).
          simp only [evalD] at h
          have hCletF : CtxCorr σ (Frame.letF N :: K) := CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
          have hTletF : CtxTxnCorr τ (Frame.letF N :: K) := CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
          have hKletF : CCtxCorr κ (Frame.letF N :: K) := CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
          have hpush : Source.step (g, K, Comp.letC M0 N) = some (g, Frame.letF N :: K, M0) := rfl
          have hCletFcoh := capLabelCoh_step _ _ hFresh hCoh hpush
          have hFletF := freshCfg_step _ _ hFresh hpush
          have hns : ∀ h0 : Handler, Frame.letF N ≠ Frame.handleF n h0 := by intro h0; simp
          cases hM : evalD fe g σ τ κ M0 with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                  ihR M0 g σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM (Frame.letF N :: K) hCletF hTletF hKletF hCletFcoh hFletF
                have hcne : ctxFullEffect (Frame.letF N :: K) σ1 τ1 κ1 = Frame.letF N :: ctxFullEffect K σ1 τ1 κ1 :=
                  ctxFullEffect_cons_let N K σ1 τ1 κ1
                rw [hcne] at hCr hTr
                have hCr' := CtxCorr_pop_nonstate (by intro n ℓ s; simp) hCr
                have hTr' := CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hTr
                have hKr' : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                  rw [hcne] at hKr
                  exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKr
                rw [hcne] at hCohr hFreshr hNRr
                have hCohr' := capLabelCoh_pop_letF hCohr
                have hFreshr' := freshCfg_pop_letF hFreshr
                have hNRr' := noResume_strip_cons hns hNRr
                refine ⟨⟨hCr', hTr', hKr', hCohr', hFreshr', hNRr'⟩, fun fuel r hr => ?_⟩
                have hidEq := idDispatch_cons_noResume (fr := Frame.letF N) (K := ctxFullEffect K σ1 τ1 κ1)
                  (ℓ := labelOf (ctxFullEffect K σ1 τ1 κ1) ℓ') (op := op') (v := w) (by intro h0; simp) hNRr'
                have hlbl := labelOf_cons_ne (fr := Frame.letF N) (K := ctxFullEffect K σ1 τ1 κ1) (n := ℓ') hns
                have hkr : dispatchRun fuel g1 ℓ' (ctxFullEffect (Frame.letF N :: K) σ1 τ1 κ1)
                    (labelOf (ctxFullEffect (Frame.letF N :: K) σ1 τ1 κ1) ℓ') op' w = r := by
                  rw [hcne, hlbl]; simp only [dispatchRun]
                  rw [run_perform_cons_eq hidEq fuel]
                  simp only [dispatchRun] at hr; exact hr
                obtain ⟨F, hF⟩ := kR fuel r hkr
                exact ⟨F+1, by simp only [Bang.Config.run, Source.step]; exact hF⟩
            | (.term (.ret v0), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨⟨hCM, hTM, hKM, hCohR, hFR⟩, kM⟩ :=
                  ihT M0 g σ τ κ (.ret v0) g1 σ1 τ1 κ1 hM (Frame.letF N :: K) hCletF hTletF hKletF hCletFcoh hFletF
                have hcne : ctxFullEffect (Frame.letF N :: K) σ1 τ1 κ1 = Frame.letF N :: ctxFullEffect K σ1 τ1 κ1 :=
                  ctxFullEffect_cons_let N K σ1 τ1 κ1
                rw [hcne] at hCM hTM
                have hCM' := CtxCorr_pop_nonstate (by intro n ℓ s; simp) hCM
                have hTM' := CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hTM
                have hKM' : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                  rw [hcne] at hKM
                  exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                rw [hcne] at hCohR hFR
                have hpop : Source.step (g1, Frame.letF N :: ctxFullEffect K σ1 τ1 κ1, Comp.ret v0)
                    = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.subst v0 N) := rfl
                have hCsub := capLabelCoh_step _ _ hFR hCohR hpop
                have hFsub := freshCfg_step _ _ hFR hpop
                obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                  ihR (Comp.subst v0 N) g1 σ1 τ1 κ1 n op v g' σ' τ' κ' h (ctxFullEffect K σ1 τ1 κ1) hCM' hTM' hKM' hCsub hFsub
                rw [ctxFullEffect_ctxFullEffect] at hCr hTr hKr hCohr hFreshr hNRr
                refine ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, fun fuel r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kR fuel r (by rw [ctxFullEffect_ctxFullEffect]; exact hr)
                have hstep : Bang.Config.run (F2+1) (g1, Frame.letF N :: ctxFullEffect K σ1 τ1 κ1, Comp.ret v0) = r := by
                  simp only [Bang.Config.run, hpop]; exact hF2
                rw [← hcne] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
      | app M0 v0 =>
          -- MIRROR of letC over the `appF v0` frame: (a) M0 raises; (b) M0 returns `.lam N`, the beta
          -- `subst v0 N` raises (needs `ihT`).
          simp only [evalD] at h
          have hCappF : CtxCorr σ (Frame.appF v0 :: K) := CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
          have hTappF : CtxTxnCorr τ (Frame.appF v0 :: K) := CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
          have hKappF : CCtxCorr κ (Frame.appF v0 :: K) := CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
          have hpush : Source.step (g, K, Comp.app M0 v0) = some (g, Frame.appF v0 :: K, M0) := rfl
          have hCappFcoh := capLabelCoh_step _ _ hFresh hCoh hpush
          have hFappF := freshCfg_step _ _ hFresh hpush
          have hns : ∀ h0 : Handler, Frame.appF v0 ≠ Frame.handleF n h0 := by intro h0; simp
          cases hM : evalD fe g σ τ κ M0 with
          | none => rw [hM] at h; simp at h
          | some oM =>
            rw [hM] at h
            match oM, h with
            | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                  ihR M0 g σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM (Frame.appF v0 :: K) hCappF hTappF hKappF hCappFcoh hFappF
                have hcne : ctxFullEffect (Frame.appF v0 :: K) σ1 τ1 κ1 = Frame.appF v0 :: ctxFullEffect K σ1 τ1 κ1 :=
                  ctxFullEffect_cons_app v0 K σ1 τ1 κ1
                rw [hcne] at hCr hTr
                have hCr' := CtxCorr_pop_nonstate (by intro n ℓ s; simp) hCr
                have hTr' := CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hTr
                have hKr' : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                  rw [hcne] at hKr
                  exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKr
                rw [hcne] at hCohr hFreshr hNRr
                have hCohr' := capLabelCoh_pop_appF hCohr
                have hFreshr' := freshCfg_pop_appF hFreshr
                have hNRr' := noResume_strip_cons hns hNRr
                refine ⟨⟨hCr', hTr', hKr', hCohr', hFreshr', hNRr'⟩, fun fuel r hr => ?_⟩
                have hidEq := idDispatch_cons_noResume (fr := Frame.appF v0) (K := ctxFullEffect K σ1 τ1 κ1)
                  (ℓ := labelOf (ctxFullEffect K σ1 τ1 κ1) ℓ') (op := op') (v := w) (by intro h0; simp) hNRr'
                have hlbl := labelOf_cons_ne (fr := Frame.appF v0) (K := ctxFullEffect K σ1 τ1 κ1) (n := ℓ') hns
                have hkr : dispatchRun fuel g1 ℓ' (ctxFullEffect (Frame.appF v0 :: K) σ1 τ1 κ1)
                    (labelOf (ctxFullEffect (Frame.appF v0 :: K) σ1 τ1 κ1) ℓ') op' w = r := by
                  rw [hcne, hlbl]; simp only [dispatchRun]
                  rw [run_perform_cons_eq hidEq fuel]
                  simp only [dispatchRun] at hr; exact hr
                obtain ⟨F, hF⟩ := kR fuel r hkr
                exact ⟨F+1, by simp only [Bang.Config.run, Source.step]; exact hF⟩
            | (.term (.lam N), g1, σ1, τ1, κ1), h =>
                simp only [Option.bind_some] at h
                obtain ⟨⟨hCM, hTM, hKM, hCohR, hFR⟩, kM⟩ :=
                  ihT M0 g σ τ κ (.lam N) g1 σ1 τ1 κ1 hM (Frame.appF v0 :: K) hCappF hTappF hKappF hCappFcoh hFappF
                have hcne : ctxFullEffect (Frame.appF v0 :: K) σ1 τ1 κ1 = Frame.appF v0 :: ctxFullEffect K σ1 τ1 κ1 :=
                  ctxFullEffect_cons_app v0 K σ1 τ1 κ1
                rw [hcne] at hCM hTM
                have hCM' := CtxCorr_pop_nonstate (by intro n ℓ s; simp) hCM
                have hTM' := CtxTxnCorr_pop_nontxn (by intro n ℓ Θ; simp) hTM
                have hKM' : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                  rw [hcne] at hKM
                  exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKM
                rw [hcne] at hCohR hFR
                have hpop : Source.step (g1, Frame.appF v0 :: ctxFullEffect K σ1 τ1 κ1, Comp.lam N)
                    = some (g1, ctxFullEffect K σ1 τ1 κ1, Comp.subst v0 N) := rfl
                have hCsub := capLabelCoh_step _ _ hFR hCohR hpop
                have hFsub := freshCfg_step _ _ hFR hpop
                obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                  ihR (Comp.subst v0 N) g1 σ1 τ1 κ1 n op v g' σ' τ' κ' h (ctxFullEffect K σ1 τ1 κ1) hCM' hTM' hKM' hCsub hFsub
                rw [ctxFullEffect_ctxFullEffect] at hCr hTr hKr hCohr hFreshr hNRr
                refine ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, fun fuel r hr => ?_⟩
                obtain ⟨F2, hF2⟩ := kR fuel r (by rw [ctxFullEffect_ctxFullEffect]; exact hr)
                have hstep : Bang.Config.run (F2+1) (g1, Frame.appF v0 :: ctxFullEffect K σ1 τ1 κ1, Comp.lam N) = r := by
                  simp only [Bang.Config.run, hpop]; exact hF2
                rw [← hcne] at hstep
                obtain ⟨F1, hF1⟩ := kM (F2+1) r hstep
                exact ⟨F1+1, by simp only [Bang.Config.run, Source.step]; exact hF1⟩
            | (.term (.ret w), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
            | (.term (.split a b), _, _, _), h => simp [Option.bind] at h
            | (.term (.unfold a), _, _, _), h => simp [Option.bind] at h
            | (.term .oom, _, _, _), h => simp [Option.bind] at h
            | (.term (.wrong a), _, _, _), h => simp [Option.bind] at h
      | handle h0 M0 =>
          -- FORWARD (all 3 kinds): MINT `handleF g h0`, run M' = subst (vcap g ℓ0) M0 at g+1; the body raises
          -- and is NOT caught (state/txn never catch; throws catches only its own id+"raise" — that's a TERM,
          -- excluded here). Pop the frame off the conclusion (`CtxCorr_ctxNetEffect_pop_*` + `*_pop_handleF`);
          -- bridge the continuation across the popped frame (`run_perform_pop_handleF`: strip if ℓ'≠g, escape if
          -- ℓ'=g); then the MINT step. `hcbpop` (freshness) supplies the `ℓ'=g` escape.
          simp only [evalD] at h
          cases h0 with
          | custom ℓ0 p0 cls0 =>
              -- FORWARD a raise past a custom frame (ADR-0085 Stage 4): custom NEVER catches a throws-raise,
              -- so the body's raise propagates out. MINT `handleF g (custom ℓ0 p0 cls0)`, run M' at g+1; on a
              -- raise POP the κ entry (CCtxCorr_pop_custom) + the σ/τ pass-through pop; bridge the continuation
              -- across the popped frame (run_perform_pop_handleF); then MINT. Mirror of the state FORWARD arm.
              simp only [Handler.label] at h
              have hmint : Source.step (g, K, Comp.handle (Handler.custom ℓ0 p0 cls0) M0)
                  = some (g+1, Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr (κ.push g p0 cls0) (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                CCtxCorr_install hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              cases hM : evalD fe (g+1) σ τ (κ.push g p0 cls0) (Comp.subst (Val.vcap g ℓ0) M0) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                    obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                      ihR (Comp.subst (Val.vcap g ℓ0) M0) (g+1) σ τ (κ.push g p0 cls0) ℓ' op' w g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, p1, cls1, hnetEq⟩ :=
                      CtxCorr_ctxFullEffect_pop_custom hCr hTr
                    have hKpop : CCtxCorr κ1.tail (ctxFullEffect K σ1 τ1 κ1.tail) := by
                      rw [hnetEq] at hKr; exact CCtxCorr_pop_custom hKr
                    rw [hnetEq] at hCohr hFreshr hNRr
                    have hcbpop : Bang.Model.CapsBelow g (ctxFullEffect K σ1 τ1 κ1.tail) :=
                      CapsBelow_ctxFullEffect _ _ _ hFresh.1
                    have hCohr' := capLabelCoh_pop_handleF hcbpop hCohr
                    have hFreshr' := freshCfg_pop_handleF hFreshr
                    have hNRr' : NoResume (ctxFullEffect K σ1 τ1 κ1.tail) ℓ' op' := by
                      by_cases hℓg : ℓ' = g
                      · subst hℓg; intro Kᵢ h Kₒ hsp
                        exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                      · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNRr
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr'⟩, fun fuel r hr => ?_⟩
                    have hhof : ℓ' = g → Bang.handlesOp (Handler.custom ℓ0 p1 cls1)
                        (Handler.label (Handler.custom ℓ0 p1 cls1)) op' = false := by
                      intro hgl; subst hgl
                      rcases hNRr [] (Handler.custom ℓ0 p1 cls1) (ctxFullEffect K σ1 τ1 κ1.tail)
                        (by simp [Bang.splitAtId]) with hf | ⟨_, he⟩
                      · exact hf
                      · exact absurd he (by simp)
                    have hkr : dispatchRun fuel g1 ℓ' (ctxFullEffect (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) σ1 τ1 κ1)
                        (labelOf (ctxFullEffect (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) σ1 τ1 κ1) ℓ') op' w = r := by
                      rw [hnetEq]; simp only [dispatchRun]
                      rw [run_perform_pop_handleF hcbpop hNRr' hhof fuel]
                      simp only [dispatchRun] at hr; exact hr
                    obtain ⟨F, hF⟩ := kR fuel r hkr
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.ret v0), _, _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _, _), h => simp [Option.bind] at h
          | state ℓ0 s0 =>
              simp only [Handler.label] at h
              have hmint : Source.step (g, K, Comp.handle (Handler.state ℓ0 s0) M0)
                  = some (g+1, Frame.handleF g (Handler.state ℓ0 s0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr (σ.push g s0) (Frame.handleF g (Handler.state ℓ0 s0) :: K) := CtxCorr_install hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              cases hM : evalD fe (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M0) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                    obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                      ihR (Comp.subst (Val.vcap g ℓ0) M0) (g+1) (σ.push g s0) τ κ ℓ' op' w g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.state ℓ0 s0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_state hCr hTr
                    have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1.tail τ1 κ1) := by
                      rw [hnetEq] at hKr
                      exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKr
                    rw [hnetEq] at hCohr hFreshr hNRr
                    have hcbpop : Bang.Model.CapsBelow g (ctxFullEffect K σ1.tail τ1 κ1) :=
                      CapsBelow_ctxFullEffect _ _ _ hFresh.1
                    have hCohr' := capLabelCoh_pop_handleF hcbpop hCohr
                    have hFreshr' := freshCfg_pop_handleF hFreshr
                    have hNRr' : NoResume (ctxFullEffect K σ1.tail τ1 κ1) ℓ' op' := by
                      by_cases hℓg : ℓ' = g
                      · subst hℓg; intro Kᵢ h Kₒ hsp
                        exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                      · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNRr
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr'⟩, fun fuel r hr => ?_⟩
                    have hhof : ℓ' = g → Bang.handlesOp (Handler.state ℓ0 (σ1.headD (default, default)).2)
                        (Handler.label (Handler.state ℓ0 (σ1.headD (default, default)).2)) op' = false := by
                      intro hgl; subst hgl
                      rcases hNRr [] (Handler.state ℓ0 (σ1.headD (default, default)).2) (ctxFullEffect K σ1.tail τ1 κ1)
                        (by simp [Bang.splitAtId]) with hf | ⟨_, he⟩
                      · exact hf
                      · exact absurd he (by simp)
                    have hkr : dispatchRun fuel g1 ℓ' (ctxFullEffect (Frame.handleF g (Handler.state ℓ0 s0) :: K) σ1 τ1 κ1)
                        (labelOf (ctxFullEffect (Frame.handleF g (Handler.state ℓ0 s0) :: K) σ1 τ1 κ1) ℓ') op' w = r := by
                      rw [hnetEq]; simp only [dispatchRun]
                      rw [run_perform_pop_handleF hcbpop hNRr' hhof fuel]
                      simp only [dispatchRun] at hr; exact hr
                    obtain ⟨F, hF⟩ := kR fuel r hkr
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.ret v0), _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _), h => simp [Option.bind] at h
          | throws ℓ0 =>
              simp only [Handler.label] at h
              have hmint : Source.step (g, K, Comp.handle (Handler.throws ℓ0) M0)
                  = some (g+1, Frame.handleF g (Handler.throws ℓ0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              cases hM : evalD fe (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M0) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some] at h
                    by_cases hk : ℓ' = g ∧ op' = "raise"
                    · simp [if_pos hk] at h
                    · simp only [if_neg hk, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                      obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                        ihR (Comp.subst (Val.vcap g ℓ0) M0) (g+1) σ τ κ ℓ' op' w g1 σ1 τ1 κ1 hM
                          (Frame.handleF g (Handler.throws ℓ0) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                      obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_throws hCr hTr
                      have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1 τ1 κ1) := by
                        rw [hnetEq] at hKr
                        exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKr
                      rw [hnetEq] at hCohr hFreshr hNRr
                      have hcbpop : Bang.Model.CapsBelow g (ctxFullEffect K σ1 τ1 κ1) :=
                        CapsBelow_ctxFullEffect _ _ _ hFresh.1
                      have hCohr' := capLabelCoh_pop_handleF hcbpop hCohr
                      have hFreshr' := freshCfg_pop_handleF hFreshr
                      have hNRr' : NoResume (ctxFullEffect K σ1 τ1 κ1) ℓ' op' := by
                        by_cases hℓg : ℓ' = g
                        · subst hℓg; intro Kᵢ h Kₒ hsp
                          exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                        · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNRr
                      refine ⟨⟨hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr'⟩, fun fuel r hr => ?_⟩
                      have hhof : ℓ' = g → Bang.handlesOp (Handler.throws ℓ0)
                          (Handler.label (Handler.throws ℓ0)) op' = false := by
                        intro hgl
                        have hnr : op' ≠ "raise" := fun he => hk ⟨hgl, he⟩
                        simp [Handler.label, Bang.handlesOp, hnr]
                      have hkr : dispatchRun fuel g1 ℓ' (ctxFullEffect (Frame.handleF g (Handler.throws ℓ0) :: K) σ1 τ1 κ1)
                          (labelOf (ctxFullEffect (Frame.handleF g (Handler.throws ℓ0) :: K) σ1 τ1 κ1) ℓ') op' w = r := by
                        rw [hnetEq]; simp only [dispatchRun]
                        rw [run_perform_pop_handleF hcbpop hNRr' hhof fuel]
                        simp only [dispatchRun] at hr; exact hr
                      obtain ⟨F, hF⟩ := kR fuel r hkr
                      exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.ret v0), _, _, _), h => simp [Option.bind] at h
                | (.term (.lam a), _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _), h => simp [Option.bind] at h
          | transaction ℓ0 Θ =>
              simp only [Handler.label] at h
              have hmint : Source.step (g, K, Comp.handle (Handler.transaction ℓ0 Θ) M0)
                  = some (g+1, Frame.handleF g (Handler.transaction ℓ0 Θ) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr (τ.push g Θ) (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                CtxTxnCorr_install hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              cases hM : evalD fe (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M0) with
              | none => rw [hM] at h; simp at h
              | some oM =>
                rw [hM] at h
                match oM, h with
                | (.raised ℓ' op' w, g1, σ1, τ1, κ1), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Outcome.raised.injEq] at h
                    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
                    obtain ⟨⟨hCr, hTr, hKr, hCohr, hFreshr, hNRr⟩, kR⟩ :=
                      ihR (Comp.subst (Val.vcap g ℓ0) M0) (g+1) σ (τ.push g Θ) κ ℓ' op' w g1 σ1 τ1 κ1 hM
                        (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) hCinstall hTinstall hKinstall hCohInstall hFreshInstall
                    obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxFullEffect_pop_txn hCr hTr
                    have hKpop : CCtxCorr κ1 (ctxFullEffect K σ1 τ1.tail κ1) := by
                      rw [hnetEq] at hKr
                      exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hKr
                    rw [hnetEq] at hCohr hFreshr hNRr
                    have hcbpop : Bang.Model.CapsBelow g (ctxFullEffect K σ1 τ1.tail κ1) :=
                      CapsBelow_ctxFullEffect _ _ _ hFresh.1
                    have hCohr' := capLabelCoh_pop_handleF hcbpop hCohr
                    have hFreshr' := freshCfg_pop_handleF hFreshr
                    have hNRr' : NoResume (ctxFullEffect K σ1 τ1.tail κ1) ℓ' op' := by
                      by_cases hℓg : ℓ' = g
                      · subst hℓg; intro Kᵢ h Kₒ hsp
                        exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                      · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNRr
                    refine ⟨⟨hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr'⟩, fun fuel r hr => ?_⟩
                    have hhof : ℓ' = g → Bang.handlesOp (Handler.transaction ℓ0 (τ1.headD (default, default)).2)
                        (Handler.label (Handler.transaction ℓ0 (τ1.headD (default, default)).2)) op' = false := by
                      intro hgl; subst hgl
                      rcases hNRr [] (Handler.transaction ℓ0 (τ1.headD (default, default)).2) (ctxFullEffect K σ1 τ1.tail κ1)
                        (by simp [Bang.splitAtId]) with hf | ⟨_, he⟩
                      · exact hf
                      · exact absurd he (by simp)
                    have hkr : dispatchRun fuel g1 ℓ' (ctxFullEffect (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) σ1 τ1 κ1)
                        (labelOf (ctxFullEffect (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) σ1 τ1 κ1) ℓ') op' w = r := by
                      rw [hnetEq]; simp only [dispatchRun]
                      rw [run_perform_pop_handleF hcbpop hNRr' hhof fuel]
                      simp only [dispatchRun] at hr; exact hr
                    obtain ⟨F, hF⟩ := kR fuel r hkr
                    exact ⟨F+1, by simp only [Bang.Config.run, hmint]; exact hF⟩
                | (.term (.ret v0), _, _, _), h =>
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hr', _⟩ := h; exact absurd hr' (by simp)
                | (.term (.lam a), _, _, _), h => simp [Option.bind] at h
                | (.term (.letC a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.force a), _, _, _), h => simp [Option.bind] at h
                | (.term (.app a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.perform a b d), _, _, _), h => simp [Option.bind] at h
                | (.term (.handle a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.case a b d), _, _, _), h => simp [Option.bind] at h
                | (.term (.split a b), _, _, _), h => simp [Option.bind] at h
                | (.term (.unfold a), _, _, _), h => simp [Option.bind] at h
                | (.term .oom, _, _, _), h => simp [Option.bind] at h
                | (.term (.wrong a), _, _, _), h => simp [Option.bind] at h

/-- **The D1-A bridge** (headline): when `evalD` says a closed computation returns
`v`, the kernel's verified `Source.eval` agrees (`.done v`). Ties the calculated
machine to the type-safety reference (invariant #1) — `Source.eval`'s `type_safety`
now backs `evalD`'s `ret`-results. -/
theorem evalD_agrees_source (f : Nat) (M : Comp) (v : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hvf : Bang.Model.VcapFree M)
    (h : evalD f 0 [] [] [] M = some (.term (.ret v), g', σ', τ', κ')) :
    ∃ F, Source.eval F M = Result.done v := by
  -- the empty stores mirror the empty kernel context (`CtxCorr [] []`/`CtxTxnCorr [] []`/`CCtxCorr [] []`
  -- by `rfl`); a closed program has no resumptive frames ⇒ `ctxNetEffect [] σ' τ' = []`, continuation at
  -- `(g', [], ret v)`. `VcapFree` (closed source, route-B) seeds label-coherence + freshness vacuously.
  have hFresh : FreshCfg (0, [], M) := by
    refine ⟨trivial, fun p hp => ?_, trivial, fun p hp => ?_⟩
    · rw [Bang.Model.VcapFree] at hvf; rw [hvf] at hp; exact absurd hp (by simp)
    · simp [Bang.Model.capsK] at hp
  obtain ⟨_, k⟩ := (run_evalD f).1 M 0 [] [] [] (.ret v) g' σ' τ' κ' h [] rfl rfl rfl
    (capLabelCoh_initial hvf) hFresh
  have hbase : Config.run 1 (g', ctxNetEffect [] σ' τ', .ret v) = Result.done v := by
    simp only [ctxNetEffect, updateCtxStates, updateCtxTxns, Config.run]
  obtain ⟨F, hF⟩ := k 1 (Result.done v) hbase
  exact ⟨F, hF⟩

/-- `handle`-install over a non-raising body: `handle (throws ℓ) (ret 7)` ⇒ `7`
(handler-return = identity — `MARK`/`UNMARK` are identity on a normal return). A distinct
shape from the battery's *catching* throws cases; the full three-rep bridge witnessed at once. -/
example :
    let M := Comp.handle (.throws 0) (.ret (.vint 7))
    evalD 5 0 [] [] [] M = some (.term (.ret (.vint 7)), 1, [], [], []) ∧ Agree 10 M (.vint 7) := by
  refine ⟨by rfl, by rfl, by rfl⟩

end -- public section
end Bang.CalcVM
