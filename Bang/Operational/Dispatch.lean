/-
  Bang/Operational/Dispatch.lean — effect dispatch (ADR-0054 identity dispatch).
  ─────────────────────────────────────────────────────────────────────────
    handlesOp · splitAt · splitAtId · dispatchOn · idDispatch
    handler-skeleton utilities (handlerCount / handlersOf)
    CapResolves / FocusResolves — the cap-resolution predicates

  The dispatch concern of the operational hub. Imports Subst (handlesOp is
  invariant under substFrom). Split out of Bang/Operational.lean per
  core-overview.md §6; behavior-preserving MOVE.
-/

module

public import Bang.Operational.Subst

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]

@[expose] public section

/-- The label a handler discharges (its first field). `handlesOp h ℓ op = true → h.label = ℓ`. -/
def Handler.label : Handler → Label
  | .throws ℓ => ℓ
  | .state ℓ _ => ℓ
  | .transaction ℓ _ => ℓ

/-- Does handler `h` catch operation `(ℓ, op)`? -/
def handlesOp : Handler → Label → OpId → Bool
  | .throws ℓ',   ℓ, op => (ℓ' = ℓ) && (op == "raise")
  | .state  ℓ' _, ℓ, op => (ℓ' = ℓ) && (op == "get" || op == "put")
  -- transaction (ADR-0030): catches the three stm ops on its own label.
  | .transaction ℓ' _, ℓ, op =>
      (ℓ' = ℓ) && (op == "newTVar" || op == "readTVar" || op == "writeTVar")

/-- `handlesOp` forces the label match: a catching handler's `label` IS the dispatched `ℓ`. -/
theorem handlesOp_label {h : Handler} {ℓ : Label} {op : OpId} (hc : handlesOp h ℓ op = true) :
    h.label = ℓ := by
  cases h <;> simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hc <;>
    simp only [Handler.label] <;> exact hc.1

/-- Split a stack at the nearest frame catching `(ℓ, op)`: returns `(Kᵢ, h, Kₒ)` with
`K = Kᵢ ++ handleF h :: Kₒ`, `Kᵢ` containing no catching frame (the inner captured continuation),
and `h` the catching handler. `none` = no handler in `K` (unhandled). The recursion is the SAME walk
ADR-0023's `dispatch` did; it now also RETURNS the inner prefix `Kᵢ` (kept by `state`, discarded by
`throws`).

ADR-0054: `splitAt` (label search) is LEGACY for `Source.step` (which now dispatches by IDENTITY via
`idDispatch`/`splitAtId`). It STAYS only because the not-yet-ported LR (`krelS_splitAt_decomp`) +
`NoWrapMiss` still reference its shape; the inc-5 LR port re-keys them onto `splitAtId`. -/
def splitAt : EvalCtx → Label → OpId → Option (EvalCtx × Handler × EvalCtx)
  | [], _, _ => none
  | (.handleF m h :: K), ℓ, op =>
      if handlesOp h ℓ op then some ([], h, K)
      else (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF m h :: Kᵢ, h', Kₒ))
  | (fr :: K), ℓ, op =>
      (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-- ADR-0054 IDENTITY dispatch: split the stack at the `handleF` whose IDENTITY is `n` (the capability's
generative name). Unlike `splitAt`'s label search, this MATCHES the unique identity — migration-invariant
(a match never re-counts, so it never shifts). Mirror of `scratch/IdentityKernelProbe.splitAtId`. -/
def splitAtId : EvalCtx → Nat → Option (EvalCtx × Handler × EvalCtx)
  | [], _ => none
  | (.handleF m h :: K), n =>
      if m = n then some ([], h, K)
      else (splitAtId K n).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF m h :: Kᵢ, h', Kₒ))
  | (fr :: K), n => (splitAtId K n).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-- ◊4.5b-answertrack SCOPED-SEAM (ADR-0043): `(ℓ, op)` does NOT "pass through" a non-catching handler
before reaching its catcher — the captured continuation up to the catching handler contains NO handler
frame. Mirrors `splitAt`'s recursion: a `handleF h` frame must either CATCH `(ℓ, op)` (split point,
`Kᵢ = []`) or have NO catcher below it (`splitAt K = none`, op unhandled = stuck). The EXCLUDED edge
(`splitAt`-wrap-MISS) is exactly `¬ NoWrapMiss`: a non-catching `handleF` with a deeper catcher — the
captured continuation then wraps that handler, the inverse-strip case `krelS_splitAt_decomp` cannot
certify (answer-determinism FALSE). COVERED: every op caught by the NEAREST enclosing handler. -/
private def NoWrapMiss : EvalCtx → Label → OpId → Prop
  | [], _, _ => True
  | (.handleF _ h :: K), ℓ, op =>
      handlesOp h ℓ op = true ∨ splitAt K ℓ op = none
  | (_ :: K), ℓ, op => NoWrapMiss K ℓ op

/-- Read TVar index `i` (a payload `vint i`) out of a value; `none` if the payload is malformed. -/
def tvarIdx : Val → Option Nat
  | .vint n => if n ≥ 0 then some n.toNat else none
  | _       => none

/-- Update heap cell `i` to `w` (out-of-range = unchanged; the type system guarantees in-range). -/
def storeSet (Θ : Store) (i : Nat) (w : Val) : Store := List.set Θ i w

/-- Deep-handler dispatch (ADR-0025 generalizes ADR-0023 to KEEP the captured continuation for
resumptive handlers). Split the stack at the nearest catching frame, then:

  - `throws ℓ`: ZERO-SHOT abort. Discard `Kᵢ` and the handler frame; the payload `v` becomes the
    focus over the outer stack `Kₒ`. (ADR-0023, unchanged behaviour.)
  - `state ℓ s`: ONE-SHOT RESUME (ADR-0025). KEEP `Kᵢ` and reinstall a (deep) `state ℓ s'` frame so
    the next operation is handled too:
      · `get`: return the stored `s` to `Kᵢ`, state unchanged (`s' = s`, focus `ret s`);
      · `put w`: store the payload `w`, return `unit` to `Kᵢ` (`s' = w`, focus `ret unit`).
    The resumed stack is `Kᵢ ++ handleF (state ℓ s') :: Kₒ`.
  - `transaction ℓ Θ`: ONE-SHOT RESUME threading the list-heap (ADR-0030) — `state` generalized to a
    list. `newTVar`/`readTVar`/`writeTVar` reinstall a deep `transaction ℓ Θ'` frame with the heap
    grown/read/updated. Rollback is FREE: abort is a foreign `throws` escaping this frame, so `Θ'`
    is discarded with the frame (never commits). A malformed/out-of-range TVar payload yields `oom`.

Reaching `[]` (no catching frame) = unhandled = stuck (`none`). The CK focus stays CLOSED: the stored
`s`/payload `w`/heap cells are closed values (the focus is always closed), so resumption threads no
open term and no variable budget — the grade vectors stay `[]` (ADR-0025 §grade discipline). -/
-- ADR-0055: dispatch is COUNTER-FREE — it produces a `(stack, focus)` pair (the old Config shape),
-- and `Source.step`'s perform arm threads the carried counter `g` back in via `.map`. A resume reuses
-- the matched id, so dispatch never mints; keeping it counter-free is what lets the `splitAtId`/
-- `dispatchOn`/`idDispatch` helpers stay byte-identical under the reshape.
def dispatchOn (n : Nat) (op : OpId) (v : Val) :
    EvalCtx × Handler × EvalCtx → Option (EvalCtx × Comp)
  | (Kᵢ, h, Kₒ) =>
      match h with
      | .throws _   => some (Kₒ, .ret v)                                        -- ABORT
      | .state ℓ' s =>
          if op == "get" then
            some (Kᵢ ++ Frame.handleF n (.state ℓ' s) :: Kₒ, .ret s)             -- RESUME with s
          else
            some (Kᵢ ++ Frame.handleF n (.state ℓ' v) :: Kₒ, .ret .vunit)        -- RESUME with unit
      -- transaction (ADR-0030): the multi-cell generalization of `state`. RESUME threading the
      -- updated heap (KEEP `Kᵢ`, reinstall a deep `transaction ℓ' Θ'` frame), exactly the ADR-0025
      -- state-resume pattern with a list-heap. Rollback is FREE: an abort is a zero-shot `throws`
      -- that escapes this frame (handled by the throws arm above over a DIFFERENT label), so the
      -- threaded `Θ'` is discarded with the frame and never commits.
      | .transaction ℓ' Θ =>
          if op == "newTVar" then
            -- allocate: append the initial value `v`; the new TVar's index is the old length.
            some (Kᵢ ++ Frame.handleF n (.transaction ℓ' (Θ ++ [v])) :: Kₒ, .ret (.vint Θ.length))
          else if op == "readTVar" then
            -- read (ADR-0030 amendment, TVarRef = int, TOTAL store): payload `vint i`; return cell `i`,
            -- or the DEFAULT `vint 0` if out of range. NEVER ooms — `oom` is the fuel sentinel, so a
            -- bad read producing it would be untypable (preservation gap). The store is conceptually a
            -- total `Loc → Val` map (`getD` with `vint 0`); source refs come only from `newTVar`, so
            -- the default path is source-unreachable but kernel-total. Heap unchanged on read.
            some (Kᵢ ++ Frame.handleF n (.transaction ℓ' Θ) :: Kₒ,
                  .ret (Θ.getD ((tvarIdx v).getD 0) (.vint 0)))
          else
            -- writeTVar (ADR-0030, total store): payload `pair (vint i) w`; store `w` at cell `i`, return
            -- unit. `storeSet`/`List.set` is a no-op out of range, so this is TOTAL and never ooms. A
            -- malformed payload (not `pair (vint _) _`) is a type-safe no-op resume (source-unreachable
            -- since the payload type is `prod int S`).
            match v with
            | .pair iv w =>
                some (Kᵢ ++ Frame.handleF n (.transaction ℓ' (storeSet Θ ((tvarIdx iv).getD 0) w)) :: Kₒ,
                      .ret .vunit)
            | _ => some (Kᵢ ++ Frame.handleF n (.transaction ℓ' Θ) :: Kₒ, .ret .vunit)

/-- ADR-0054: the kernel's effect dispatch — resolve the capability's IDENTITY `n`, then route the
matched `(Kᵢ, h, Kₒ)` through `dispatchOn n` (which reinstalls `handleF n` on a resumptive RESUME). -/
def idDispatch (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) (v : Val) : Option (EvalCtx × Comp) :=
  (splitAtId K n).bind fun (Kᵢ, h, Kₒ) =>
    -- FAIL-LOUD (ADR-0054 inc 4): identity match alone does NOT check the handler KIND, so a
    -- mis-identified / escaped capability could land on a wrong-kind frame and be read
    -- silently-wrong (`op = "get"` on a `.throws` frame hits the abort arm → a wrong value, not
    -- `none`). Gate on the capability's OWN label `ℓ`: a cap whose resolved handler does not
    -- handle `(ℓ, op)` is STUCK (fail-loud), never wrong-valued. Well-typed programs are
    -- unaffected — typing (`c : Cap ℓ`) + `NonEscape` guarantee the match handles `(ℓ, op)`,
    -- so the migration #guards still pass. This makes the `dispatchOn` kind-check redundant on
    -- the verified core while keeping the tested superset honest at the escape boundary.
    if handlesOp h ℓ op then dispatchOn n op v (Kᵢ, h, Kₒ) else none

/-! ### Handler-skeleton utilities (`handlerCount` / `handlersOf`).

`handlerCount K` is also the fresh-identity source for `Source.step`'s `handle` arm (ADR-0054: the
new handler's identity is the count of handlers below it, Fork ii). -/

/-- Number of `handleF` frames in a context. Equal to `(handlersOf K).length`
(`handlerCount_eq_handlersOf_length`). The `handle` step mints the new identity as `handlerCount K`. -/
def handlerCount : EvalCtx → Nat
  | [] => 0
  | .handleF _ _ :: K => handlerCount K + 1
  | .letF _ :: K => handlerCount K
  | .appF _ :: K => handlerCount K

@[simp] private theorem handlerCount_letF (N : Comp) (K : EvalCtx) :
    handlerCount (Frame.letF N :: K) = handlerCount K := rfl
@[simp] private theorem handlerCount_appF (v : Val) (K : EvalCtx) :
    handlerCount (Frame.appF v :: K) = handlerCount K := rfl
@[simp] private theorem handlerCount_handleF (n : Nat) (h : Handler) (K : EvalCtx) :
    handlerCount (Frame.handleF n h :: K) = handlerCount K + 1 := rfl

/-- The handler skeleton of a context: keep `handleF` frames (identity + handler), drop the
cap-transparent `letF`/`appF` plumbing. -/
private def handlersOf : EvalCtx → EvalCtx
  | [] => []
  | .handleF n h :: K => Frame.handleF n h :: handlersOf K
  | .letF _ :: K => handlersOf K
  | .appF _ :: K => handlersOf K

/-- `handlersOf` distributes over append. -/
private theorem handlersOf_append (K K' : EvalCtx) : handlersOf (K ++ K') = handlersOf K ++ handlersOf K' := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp only [handlersOf, List.cons_append, ih]

/-- `handlersOf` preserves the handler count (it drops only `letF`/`appF`, keeps every `handleF`). -/
private theorem handlerCount_handlersOf (K : EvalCtx) : handlerCount (handlersOf K) = handlerCount K := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp [handlersOf, handlerCount, ih]

private theorem handlerCount_eq_handlersOf_length (K : EvalCtx) :
    handlerCount K = (handlersOf K).length := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp [handlerCount, handlersOf, ih]



/-- **`CapResolves K n ℓ op`** — the capability named `n` (label `ℓ`) resolves in stack `K` to a frame
that HANDLES `(ℓ, op)`. This is precisely the precondition `idDispatch`/`Source.step` need to fire on a
`perform (vcap n ℓ) op v` focus: `splitAtId` finds the frame and the fail-loud guard `handlesOp` passes.
The existential mirrors `idDispatch`'s `bind`. shape: scratch/NonEscapeProbe.lean §1. -/
def CapResolves (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) : Prop :=
  ∃ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) ∧ handlesOp h ℓ op = true

/-- The focus-level non-escape obligation: a `perform (vcap …)` focus must RESOLVE; every other focus is
inert (`int`/`unit`/cap-free thunks impose nothing — this is the TYPE-directedness). `NonEscape` (defined
after `Source.step`, which its reachability closure needs) is the forward closure of this over reachable
configs. shape: scratch/NonEscapeProbe.lean §3. -/
def FocusResolves : Config → Prop
  | (_, K, .perform (.vcap n ℓ) op _) => CapResolves K n ℓ op
  | _                                 => True


/-- `handlesOp` is invariant under `substFrom` (subst changes only handler payloads, never the label
or op-kind it reads). -/

@[simp] theorem handlesOp_substFrom (k : Nat) (v : Val) (h : Handler) (ℓ : Label) (op : OpId) :
    handlesOp (Handler.substFrom k v h) ℓ op = handlesOp h ℓ op := by cases h <;> rfl



end -- public section

end Bang
