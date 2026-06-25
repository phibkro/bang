/-
NonEscape de-risk probe (ADR-0054 inc-4b) — arbitrate "Shape B" CHEAPLY, WITHOUT porting the LR.

GOAL (de-risk, not implement): pin the exact `NonEscape` statement that `progress`/`preservation`
need, validate it is (1) strong enough to close progress's perform case, (2) preserved by
construction, (3) DISCRIMINATING — accepts the safe migration witnesses, rejects a genuine escape.

Shape B = `NonEscape` is the unary projection of the typed LR config relation (`LR.KrelS`/`CrelK`):
non-escape is EXACTLY what the LR proves (a related config never gets stuck mid-dispatch), so we do
NOT hand-maintain a parallel structural invariant — single source of truth. The carried obligation
(inc 5) is the one direction `KrelS-diagonal → NonEscape`; this probe states it as a `sorry`-stub
with a precise signature and does NOT port KrelS.

NO frozen-def edits. Scratch-only. Run: `lake env lean scratch/NonEscapeProbe.lean`.
-/
import Bang.Operational
import Bang.Syntax

namespace Bang.NonEscapeProbe
open Bang Frame
open Bang.EffectRow (Label)

/-! ## 1. The cap-scope property `progress`'s perform case needs -/

/-- **`CapResolves K n ℓ op`** — the cap named `n` (label `ℓ`) resolves in stack `K` to a frame that
HANDLES `(ℓ, op)`. This is precisely the precondition `idDispatch`/`Source.step` need to fire on a
`perform (vcap n ℓ) op v` focus (`splitAtId` finds the frame, the fail-loud guard `handlesOp` passes).
The existential mirrors `idDispatch`'s `bind`; its computational content is `capResolvesB` below. -/
def CapResolves (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) : Prop :=
  ∃ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) ∧ handlesOp h ℓ op = true

/-- Decidable Bool reflection of `CapResolves` — the actual computation `idDispatch` runs. -/
def capResolvesB (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) : Bool :=
  match splitAtId K n with
  | some (_, h, _) => handlesOp h ℓ op
  | none           => false

theorem capResolvesB_iff (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) :
    capResolvesB K n ℓ op = true ↔ CapResolves K n ℓ op := by
  unfold capResolvesB CapResolves
  cases hs : splitAtId K n with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    simp only []
    constructor
    · intro hh; exact ⟨Kᵢ, h, Kₒ, rfl, hh⟩
    · rintro ⟨Kᵢ', h', Kₒ', heq, hh⟩
      simp only [Option.some.injEq] at heq
      obtain ⟨_, rfl, _⟩ := heq; exact hh

/-! ## 2. Progress's perform case closes from `CapResolves` alone (NO LR needed) -/

/-- `dispatchOn` is TOTAL — every handler kind / op branch returns `some`. So once `splitAtId` finds a
HANDLING frame, the transition always exists. (This is the only thing the perform case needs beyond
`CapResolves`; it holds for any triple, with NO typing hypothesis.) -/
theorem dispatchOn_isSome (n : Nat) (op : OpId) (v : Val) (X : EvalCtx × Handler × EvalCtx) :
    ∃ cfg', dispatchOn n op v X = some cfg' := by
  obtain ⟨Kᵢ, h, Kₒ⟩ := X
  cases h <;>
    simp only [dispatchOn] <;>
    (first
      | exact ⟨_, rfl⟩
      | (split <;> exact ⟨_, rfl⟩)
      | (repeat' first | split | exact ⟨_, rfl⟩))

/-- **PROGRESS'S PERFORM CASE.** Given a `perform (vcap n ℓ) op v` focus over `K` and `CapResolves K n ℓ
op`, the config steps. Goes through purely from `splitAtId`/`handlesOp`/`dispatchOn` + the fail-loud
guard — no LR, no typing. This is the obligation `NonEscape` must DELIVER at the head of a config. -/
theorem progress_perform_from_capResolves
    (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) (v : Val)
    (hr : CapResolves K n ℓ op) :
    ∃ cfg', Source.step (K, Comp.perform (Val.vcap n ℓ) op v) = some cfg' := by
  obtain ⟨Kᵢ, h, Kₒ, hsplit, hhandles⟩ := hr
  simp only [Source.step, idDispatch, hsplit, Option.bind_some, hhandles, if_true]
  exact dispatchOn_isSome n op v (Kᵢ, h, Kₒ)

/-! ## 3. Candidate `NonEscape` (Shape B) — config-wide closure of `CapResolves`, TYPE-DIRECTED

`FocusResolves` constrains ONLY a `perform (vcap …)` focus (every other focus is inert: `int`/`unit`/
cap-free thunks impose nothing — this is the type-directedness). `NonEscapeCand` is its closure over
reachable configs: every `perform` the program ever reaches resolves. -/

/-- The focus-level obligation: if (and only if) the focus is a cap-dispatch, the cap must resolve. -/
def FocusResolves : Config → Prop
  | (K, .perform (.vcap n ℓ) op _) => CapResolves K n ℓ op
  | _                              => True

/-- Reflexive-transitive closure of `Source.step` (snoc form). -/
inductive StepStar : Config → Config → Prop where
  | refl : StepStar cfg cfg
  | tail : StepStar cfg cfg' → Source.step cfg' = some cfg'' → StepStar cfg cfg''

/-- **CANDIDATE `NonEscape` (Shape B).** A capability never outlives its handler's dynamic extent,
expressed as: every config reachable from `cfg` whose focus is a cap-dispatch RESOLVES. This is the
projection the ported `KrelS` will supply (a related config is never stuck at a `perform`). -/
def NonEscapeCand (cfg : Config) : Prop :=
  ∀ cfg', StepStar cfg cfg' → FocusResolves cfg'

/-- Prepend a step (the cons lemma `StepStar` needs to show preservation by construction). -/
theorem StepStar.head {cfg cfg₁ cfg' : Config}
    (h0 : Source.step cfg = some cfg₁) (h : StepStar cfg₁ cfg') : StepStar cfg cfg' := by
  induction h with
  | refl => exact StepStar.tail StepStar.refl h0
  | tail _ hstep ih => exact StepStar.tail ih hstep

/-- **PRESERVATION of `NonEscapeCand` — TRIVIAL by construction** (the closure is forward-closed).
This is why Shape B costs no parallel-invariant proof: preservation is structural, not earned. -/
theorem nonEscapeCand_preserved {cfg cfg₁ : Config}
    (hstep : Source.step cfg = some cfg₁) (hne : NonEscapeCand cfg) : NonEscapeCand cfg₁ :=
  fun cfg' hreach => hne cfg' (StepStar.head hstep hreach)

/-- **PROGRESS uses `NonEscapeCand`**: at a cap-dispatch head, the head itself is reachable
(`refl`), so `FocusResolves` gives `CapResolves`, and §2 closes the step. -/
theorem progress_perform_from_nonEscape
    (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) (v : Val)
    (hne : NonEscapeCand (K, Comp.perform (Val.vcap n ℓ) op v)) :
    ∃ cfg', Source.step (K, Comp.perform (Val.vcap n ℓ) op v) = some cfg' := by
  have hfr : FocusResolves (K, Comp.perform (Val.vcap n ℓ) op v) := hne _ StepStar.refl
  exact progress_perform_from_capResolves K n ℓ op v hfr

/-! ## 4. The single CARRIED obligation (inc 5 discharges via the ported LR)

`LRDiag` is the placeholder for the diagonal of inc-5's ported `LR.KrelS`/`CrelK` (the unary shadow
of the binary config relation). The probe stays LR-free, so `LRDiag` is opaque and the obligation is
a `sorry`-stub with the PRECISE signature inc 5 must close: the LR relation's diagonal projects to
`NonEscapeCand`. Note: this is NOT derivable from `HasConfigTy` alone — `HasVTy.vcap` types ANY `vcap
n ℓ` unconditionally, so an ESCAPED cap is HasCTy-typeable (see §5); the LR's two-context discipline
(`LWT`, = `preservation_returnEscape_TODO`) is what rules escape out. That is exactly the work the
LR port carries — hence the obligation is keyed on `LRDiag`, not on typing. -/

/-- Opaque stand-in for inc-5's `fun cfg => LR.KrelS n Co Co eo cfg.1 cfg.1 ∧ HasConfigTy cfg eo Co`
diagonal (the binary LR relation restricted to the diagonal + its typing side-conditions). -/
opaque LRDiag : Config → Prop

/-- **CARRIED OBLIGATION (Shape B, the only direction inc 5 owes).** The diagonal of the ported LR
config relation projects to `NonEscapeCand`. Closing this = re-establishing `lr_sound`/`lr_fundamental`
on the identity representation and reading off the non-stuck-at-perform property. Stated; NOT proved. -/
theorem lrDiag_supplies_nonEscape (cfg : Config) (_h : LRDiag cfg) : NonEscapeCand cfg := by
  sorry

/-! ## 5. Discrimination (anti-vacuity) — migration RESOLVES, escape does NOT

A decidable probe: step until the focus is a cap-dispatch, then report `capResolvesB` at THAT site
(`none` = never reached a perform within fuel). For a full non-stuck run the machine necessarily
passed every perform → every site resolved; a `stuck` run on these witnesses IS a resolution failure.
-/

/-- Run to the first cap-dispatch focus; report whether it resolves (`capResolvesB`). -/
def firstPerformResolves : Nat → Config → Option Bool
  | 0, _ => none
  | _+1, (K, .perform (.vcap n ℓ) op _) => some (capResolvesB K n ℓ op)
  | f+1, cfg => match Source.step cfg with
                | some cfg' => firstPerformResolves f cfg'
                | none      => none

/-- SAFE — the insert-below-target witness (= `capMigrateInternal`, transcribed): the thunk handles
its OWN `state` (handle INSIDE the thunk), forced under an unrelated outer `throws`. The cap travels
WITH the thunk → resolves to the thunk's own handler. -/
def migrateWitness : Comp :=
  .app (.lam (.handle (.throws 2) (.force (.vvar 1))))
    (.vthunk (.handle (.state 1 (.vint 7)) (.perform (.vvar 0) "get" .vunit)))

/-- SAFE — 1-deep migration (= `capMigrate1`): a `{get}` thunk targeting the OUTER `state`, forced
under a fresh `throws`. -/
def migrateWitness1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 1))))

/-- ESCAPE — distinct from the safe witnesses by ONE move: the `state` handle is OUTSIDE the thunk
(wraps the `ret`), so when the returned thunk is forced past the popped `handleF`, its `vcap` names a
handler no longer on the stack. `splitAtId K n = none` → STUCK. -/
def escapeWitness : Comp :=
  .letC (.handle (.state 1 (.vint 7)) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))

-- migration witnesses: reach a perform that RESOLVES (some true), and run to a value (not stuck).
#guard firstPerformResolves 200 ([], migrateWitness)  == some true
#guard firstPerformResolves 200 ([], migrateWitness1) == some true
#guard (match Source.eval 200 migrateWitness  with | .done (.vint 7) => true | _ => false)
#guard (match Source.eval 200 migrateWitness1 with | .done (.vint 5) => true | _ => false)

-- escape witness: reaches a perform that does NOT resolve (some false), and the run is STUCK.
#guard firstPerformResolves 200 ([], escapeWitness) == some false
#guard (match Source.eval 200 escapeWitness with | .stuck => true | _ => false)

-- the reached escape site, pinned: `splitAtId [] 0 = none`, so `capResolvesB` is false there.
#guard capResolvesB [] 0 1 "get" == false

/-- The escape site `([], perform (vcap 0 1) "get" unit)` does NOT step — concretely, `CapResolves`
fails there (the Prop-level statement, matching the Bool `#guard`). -/
example : ¬ CapResolves [] 0 1 "get" := by
  rw [← capResolvesB_iff]; decide

/-- …and therefore `NonEscapeCand` REJECTS the escape program: the reachable escape config violates
`FocusResolves`. (Concrete witness that the candidate is not vacuously true.) -/
example : ¬ NonEscapeCand ([], escapeWitness) := by
  intro hne
  -- the escape config is reachable; its focus is a non-resolving perform.
  have hreach : StepStar ([], escapeWitness) ([], Comp.perform (Val.vcap 0 1) "get" .vunit) := by
    apply StepStar.tail (cfg' := ([], Comp.force (.vthunk (Comp.perform (Val.vcap 0 1) "get" .vunit))))
    · apply StepStar.tail (cfg' := ([Frame.letF (Comp.force (.vvar 0))], Comp.ret (.vthunk (Comp.perform (Val.vcap 0 1) "get" .vunit))))
      · apply StepStar.tail (cfg' := ([Frame.handleF 0 (Handler.state 1 (.vint 7)), Frame.letF (Comp.force (.vvar 0))], Comp.ret (.vthunk (Comp.perform (Val.vcap 0 1) "get" .vunit))))
        · apply StepStar.tail (cfg' := ([Frame.letF (Comp.force (.vvar 0))], Comp.handle (Handler.state 1 (.vint 7)) (Comp.ret (.vthunk (Comp.perform (Val.vvar 0) "get" .vunit)))))
          · exact StepStar.tail StepStar.refl rfl
          · rfl
        · rfl
      · rfl
    · rfl
  have : FocusResolves ([], Comp.perform (Val.vcap 0 1) "get" (Val.vunit)) := hne _ hreach
  exact (by rw [← capResolvesB_iff]; decide : ¬ CapResolves [] 0 1 "get") this

end Bang.NonEscapeProbe
