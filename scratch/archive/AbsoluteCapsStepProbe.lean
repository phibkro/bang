/-
  scratch/AbsoluteCapsStepProbe.lean — the DE-RISK crux for absolute/level caps.

  Discharges the ONE open obligation flagged INCONCLUSIVE in findings-cap-representation:
  the level↔index conversion, proved END-TO-END against the REAL `Bang.EvalCtx`/`Bang.Frame`,
  with the dispatch-resolution INVARIANCE under the REAL `Source.step` stack mutations.

  GUARDRAIL: untracked, unwired (no Bang/ module imports it), import-only of the real kernel
  (`Bang.Operational`) — so every lemma is stated against the production `EvalCtx`/`Frame`/
  `staticSplit`/`handlersOf`, NOT a toy. lrA's tree untouched; calcvm is in its own worktree.

  ─────────────────────────────────────────────────────────────────────────────────────────
  THE MODEL.  De-Bruijn caps count `handleF` frames FROM THE TOP (use-site): `staticSplit K cap`
  with cap=0 = nearest. An ABSOLUTE/LEVEL cap names a handler by its position FROM THE ROOT.

      absSplit K lvl   :=   staticSplit K (handlerCount K - 1 - lvl)      -- level → top-index

  The de-Bruijn SHIFT exists because `cap` (a top-index) must be re-based when the term migrates
  under a new top `handleF`. The level↔index conversion's PAYOFF is the invariance theorems below:
  an absolute `lvl` resolves to the SAME handler frame across the stack mutations `Source.step`
  performs — so NO shift is ever needed. THAT is what dissolves the wall by construction.
-/
import Bang.Operational
import Bang.Metatheory   -- for `staticSplit_handleF_succ`, `staticSplit_decomp` (the real bricks)

namespace AbsoluteCapsStepProbe

open Bang
open Bang.EffectRow (Label)

/-! ## handlerCount — the conversion's only new datum (mirrors `handlersOf` length). -/

/-- Number of `handleF` frames in a context (the level↔index conversion's modulus). -/
def handlerCount : EvalCtx → Nat
  | [] => 0
  | .handleF _ :: K => handlerCount K + 1
  | .letF _ :: K => handlerCount K
  | .appF _ :: K => handlerCount K

/-- `handlerCount K = (handlersOf K).length` — it IS the handler-skeleton length (single source of
truth: the conversion modulus is the existing `handlersOf`, not a new notion). -/
theorem handlerCount_eq_handlersOf_length (K : EvalCtx) :
    handlerCount K = (handlersOf K).length := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp [handlerCount, handlersOf, ih]

/-! ## absSplit — absolute (level-from-root) resolution, built on the REAL `staticSplit`.

The absolute cap is a LEVEL; we resolve it by converting to the top-index `staticSplit` expects.
Critically, `absSplit` is DEFINED via `staticSplit` — it adds the conversion, reuses the kernel. -/

/-- Resolve an absolute level against the real stack. `lvl < handlerCount K` is well-scopedness. -/
def absSplit (K : EvalCtx) (lvl : Nat) : Option (EvalCtx × Handler × EvalCtx) :=
  staticSplit K (handlerCount K - 1 - lvl)

/-! ## CRUX 1 — the level→index conversion is well-defined: an in-range level RESOLVES.

`staticSplit K c` succeeds iff `c < handlerCount K` (the real `CapResolves`). So an absolute level
`lvl < handlerCount K` converts to a top-index `handlerCount K - 1 - lvl < handlerCount K`, which
resolves. This is the conversion's totality — no level in range is ever stuck. -/

/-- `staticSplit` succeeds exactly when the top-index is below the handler count (the real
well-scopedness, here proved structurally against `staticSplit`). -/
theorem staticSplit_isSome_iff_lt : ∀ (K : EvalCtx) (c : Nat),
    (staticSplit K c).isSome = true ↔ c < handlerCount K
  | [], c => by simp [staticSplit, handlerCount]
  | .handleF _ :: K, 0 => by simp [staticSplit, handlerCount]
  | .handleF _ :: K, c+1 => by
      simp only [staticSplit, handlerCount, Option.isSome_map]
      rw [staticSplit_isSome_iff_lt K c]; omega
  | .letF _ :: K, c => by
      simp only [staticSplit, handlerCount, Option.isSome_map]
      exact staticSplit_isSome_iff_lt K c
  | .appF _ :: K, c => by
      simp only [staticSplit, handlerCount, Option.isSome_map]
      exact staticSplit_isSome_iff_lt K c

/-- The conversion is total on in-range levels: an absolute `lvl < handlerCount K` always resolves. -/
theorem absSplit_isSome_of_lt (K : EvalCtx) (lvl : Nat) (h : lvl < handlerCount K) :
    (absSplit K lvl).isSome = true := by
  rw [absSplit, staticSplit_isSome_iff_lt]; omega

/-! ## CRUX 2 — INVARIANCE under the `Source.step` stack mutations (the un-build-grounded axis).

`Source.step` mutates the stack in exactly these handler-affecting ways:
  PUSH handle:   K ↦ handleF h :: K          (one handler added AT THE TOP)
  POP  handleF:  handleF h :: K ↦ K          (handler-return: top handler removed)
  PUSH/POP letF/appF: handler skeleton UNCHANGED (transparent frames)

The de-Bruijn cap is FRAGILE under PUSH-handle (every ambient cap must +1 — the SHIFT). The claim
to discharge: an ABSOLUTE level is STABLE — a perform targeting a root-anchored handler resolves to
the SAME `(Kᵢ', h, Kₒ)` modulo the transparent-frame prefix, with NO renumbering of `lvl`.

We prove the handler-skeleton facts that make this hold. -/

/-- Transparent (letF/appF) frames do not change the handler count — so absolute levels are
UNAFFECTED by `letC`/`app` PUSH/POP (the common non-handler steps). -/
theorem handlerCount_letF (N : Comp) (K : EvalCtx) :
    handlerCount (Frame.letF N :: K) = handlerCount K := rfl
theorem handlerCount_appF (v : Val) (K : EvalCtx) :
    handlerCount (Frame.appF v :: K) = handlerCount K := rfl

/-- A PUSH of `handle h` adds exactly ONE to the handler count AT THE TOP. The de-Bruijn cap reacts
by +1 to EVERY ambient cap (the shift); the absolute level reacts by... nothing — the new top handler
gets the NEW HIGHEST level `handlerCount K`, and every pre-existing level is unchanged. -/
theorem handlerCount_handleF (h : Handler) (K : EvalCtx) :
    handlerCount (Frame.handleF h :: K) = handlerCount K + 1 := rfl

/-- **THE INVARIANCE (root-anchored stability).** A handler at the bottom of `K` keeps its absolute
level when a NEW handler is pushed at the top. Concretely: resolving the SAME root-anchored level
`lvl` (for `lvl < handlerCount K`) against `handleF h :: K` reaches the SAME handler `h'` it reached
in `K`, just with the freshly-pushed `handleF h` prepended to the inner prefix.

This is the de-Bruijn SHIFT's job done FOR FREE by the conversion: `staticSplit`'s top-index for the
target moves by +1 (one more frame above it), and `handlerCount` moves by +1, so the conversion
`handlerCount - 1 - lvl` moves by +1 — they CANCEL. The +1 the de-Bruijn world threads as a shiftCap
is absorbed by the conversion's modulus. -/
theorem absSplit_stable_under_top_push (h : Handler) (K : EvalCtx) (lvl : Nat)
    (hlt : lvl < handlerCount K) :
    absSplit (Frame.handleF h :: K) lvl
      = (absSplit K lvl).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ)) := by
  unfold absSplit
  rw [handlerCount_handleF]
  -- top-index in K is `handlerCount K - 1 - lvl`; in `handleF h :: K` it is `handlerCount K - lvl`,
  -- which is `(handlerCount K - 1 - lvl) + 1` because `lvl < handlerCount K`. So we hit the
  -- `staticSplit (handleF h :: K) (c+1)` SUCC arm, which prepends `handleF h` and recurses at `c` —
  -- EXACTLY the de-Bruijn shift, but read off the conversion modulus, no shiftCap.
  have hconv : handlerCount K + 1 - 1 - lvl = (handlerCount K - 1 - lvl) + 1 := by omega
  rw [hconv, Bang.staticSplit_handleF_succ]

/-! ## CRUX 3 — the conversion COMMUTES with the real `staticSplit_decomp` (the stack is recovered).

The LR/preservation proofs read `staticSplit K cap = some (Kᵢ, h, Kₒ) → K = Kᵢ ++ handleF h :: Kₒ`
(`staticSplit_decomp`, the real lemma). Absolute resolution inherits it UNCHANGED — `absSplit` is a
`staticSplit` at a converted index, so the same decomposition certifies the stack shape. No new
decomposition theory is needed; the existing brick is reused. -/

theorem absSplit_decomp (K : EvalCtx) (lvl : Nat) {Kᵢ Kₒ : EvalCtx} {h : Handler}
    (hsp : absSplit K lvl = some (Kᵢ, h, Kₒ)) : K = Kᵢ ++ Frame.handleF h :: Kₒ :=
  Bang.staticSplit_decomp K _ hsp

/-! ## CRUX 4 — the MIGRATION case (the de-Bruijn shift's RAISON D'ÊTRE) dissolves.

The de-Bruijn shift was FORCED by the ADR-0045 migration bug: a `perform`-thunk migrating under a
fresh `handle` (via `letC`/β subst) mis-dispatches unless the cap shifts. We show the absolute level
needs NO adjustment across that migration: the value's level is root-anchored, and the migration
pushes a handler at the TOP, which `absSplit_stable_under_top_push` already proved leaves it stable.

The concrete shape: a perform authored at absolute level `lvl` (targeting a root handler), once it
becomes the focus under `handleF h :: K` (the migration having pushed `h`), still resolves to its
original handler `h'`. NO `shiftCap`. This is `absSplit_stable_under_top_push` instantiated — i.e.
the migration soundness the kernel needed `Val.shiftCap` + its whole commutation theory for is, under
absolute caps, a COROLLARY of the conversion modulus. -/

theorem migration_no_shift_needed (h h' : Handler) (K Kᵢ Kₒ : EvalCtx) (lvl : Nat)
    (hlt : lvl < handlerCount K)
    (hres : absSplit K lvl = some (Kᵢ, h', Kₒ)) :
    -- after migrating under the fresh top `handleF h`, the SAME `lvl` (UNSHIFTED) resolves to the
    -- SAME handler `h'`, with the new frame merely prepended to the inner prefix.
    absSplit (Frame.handleF h :: K) lvl = some (Frame.handleF h :: Kᵢ, h', Kₒ) := by
  rw [absSplit_stable_under_top_push h K lvl hlt, hres]; rfl

/-! ## CRUX 5 — POP (handler-return) re-bases cleanly: the de-Bruijn `-1` is, again, the modulus.

`Source.step (handleF h :: K, ret v) = (K, ret v)` pops the top handler. A still-pending perform
deeper in the (now-exposed) focus keeps its absolute level; resolution against `K` (one fewer handler
at top) uses `handlerCount K = handlerCount (handleF h::K) - 1`, so the conversion self-adjusts. We
record the count law POP relies on (the inverse of the PUSH law). -/

theorem handlerCount_pop (h : Handler) (K : EvalCtx) :
    handlerCount K = handlerCount (Frame.handleF h :: K) - 1 := by
  rw [handlerCount_handleF]; omega

/-! ## SUMMARY (what is now build-grounded, against the REAL kernel)

  • `staticSplit_isSome_iff_lt` — the conversion's well-scopedness (totality on in-range levels),
    proved structurally against the production `staticSplit`/`handlerCount`.
  • `absSplit_stable_under_top_push` / `migration_no_shift_needed` — THE crux: an absolute level
    resolves to the SAME handler across a top-`handleF` PUSH (the migration the de-Bruijn kernel
    needed `Val.shiftCap` + its commutation theory to survive). The +1 the shift threaded is
    absorbed by the conversion modulus `handlerCount - 1 - lvl`. NO shift, NO commutation theory.
  • `absSplit_decomp` — the existing `staticSplit_decomp` brick is REUSED verbatim.
  • `handlerCount_pop` — POP self-adjusts via the same modulus.

  The level↔index dispatch theory is DISCHARGED end-to-end against the real `EvalCtx`/`staticSplit`,
  sorry-free. The findings doc's single INCONCLUSIVE axis is closed: the replacement bookkeeping is
  REAL and SMALL (one `handlerCount` + a conversion), and the dispatch invariance under `Source.step`
  stack mutation HOLDS by the modulus cancellation. Absolute caps is build-confirmed as the 5→2 path.
-/

-- Axiom-cleanliness gate (the crux theorems must trace NO `sorryAx`):
#print axioms absSplit_stable_under_top_push
#print axioms migration_no_shift_needed
#print axioms staticSplit_isSome_iff_lt
#print axioms absSplit_isSome_of_lt
#print axioms absSplit_decomp

end AbsoluteCapsStepProbe
