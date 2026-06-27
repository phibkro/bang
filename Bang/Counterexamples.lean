/-
  Bang/Counterexamples.lean — the REFUTATION / COUNTEREXAMPLE registry (manifest + axiom report).
  ─────────────────────────────────────────────────────────────────────────────────
  A cohesive collection of machine-checked witnesses that a tempting-but-false statement is FALSE
  (or that a term breaks a claim). Modelled on Mathlib's `Counterexamples/` collection: one manifest
  imports every witness, so the whole registry builds as ONE target and `#print axioms` over it is
  ONE place.

  THE DO-NOT-WEAKEN DISCIPLINE. Each witness is a kept regression guard: it pins WHY a live
  statement carries the exact hypothesis/premise it does, by exhibiting the `False` you derive if you
  drop it. Reverting the guarded statement to the weaker form re-admits the counterexample — so these
  files must NOT be weakened or deleted. Each carries a `/-! … -/` (or `/- … -/`) header stating what
  it guards; the generated index `docs/notes/counterexamples.md` is a DERIVATION of those headers +
  the `-- cex: guards=…` annotations below (regen `just counterexamples`, gate `just cex-check`).

  THE BUILD SPLIT (fail-loud, not hidden). Two witnesses are PRE-EXISTING RED on the current branch's
  base — they re-key onto the ADR-0055 `Config` reshape (`NonEscape`/`CapResolves`), which is still
  in flight on the parent branch. They are listed below as COMMENTED imports (so this manifest stays
  the single membership SoT for the WHOLE registry) but are excluded from the build target, and the
  index flags them RED. Do NOT fix them here — that collides with the live Operational regrade.

  Axiom gate: `just cex-axioms` (= `lake env lean Bang/Counterexamples.lean`) reports `#print axioms`
  per headline theorem below; the lake build (this manifest as a target) re-verifies every green
  witness is sorry-free. PASS ⟺ each axiom set ⊆ { propext, Classical.choice, Quot.sound }.
-/

-- GREEN witnesses (built + axiom-gated here). `-- cex: guards=<live statement the witness pins>`.
import Bang.CohSubstRefute      -- cex: guards=`lwscg_subst` (the ∀γ'b' reshape of the subst hyp)
import Bang.LwscgLengthRefute   -- cex: guards=`lwscg_subst` (the `hlen_v` length hypothesis)
import Bang.LwscgOfTypedRefute  -- cex: guards=`lwscg_of_typed` (caps-resolve is a SEPARATE hyp)
import Bang.BoccRegress         -- cex: guards=`HasCTy` (the handle B-occ premise, ADR-0057)
import Bang.WsCfgInterfaceProbe -- cex: guards=`wsCfg_step` (records `lwscg_subst` off the critical path)

-- RED witnesses (PRE-EXISTING build break on this branch — excluded from the build target).
-- They re-key onto the ADR-0055 `Config` reshape (`NonEscape`/`CapResolves`), live on the parent
-- branch. Listed here so the registry membership has ONE home; the index renders them RED.
-- import Bang.LWRegress         -- cex: guards=`NonEscape` red=pre-existing ADR-0055 Config reshape
-- import Bang.CapEscapeWitness  -- cex: guards=`NonEscape` red=transitive (imports Bang.LWRegress)

/-! ### Axiom report — `#print axioms` per headline witness theorem (run via `just cex-axioms`). -/

-- CohSubstRefute: the single-grade subst hyp is unsound (wbad); the ∀-reshape excludes it.
#print axioms Bang.Model.lwscg_subst_refuted
#print axioms Bang.Model.wbad_not_reshaped
#print axioms Bang.Model.vgood_anyGrade
-- LwscgLengthRefute: without `hlen_v`, the truncating grade `zipWith` makes the statement FALSE.
#print axioms Bang.Model.lwscg_subst_length_refuted
-- LwscgOfTypedRefute: the HasCTy∧LWSC→LWSCg lift is unprovable; caps-resolve must be a separate hyp.
#print axioms Bang.Model.lwscg_of_typed_refuted
-- BoccRegress: the B-occ premise makes the arrow-guarded cap-escape witnesses untypeable.
#print axioms Bang.BoccRegress.escapeB_not_typeable
#print axioms Bang.BoccRegress.escapeB_app_typeable
#print axioms Bang.BoccRegress.safe_handle_typeable
-- WsCfgInterfaceProbe: REDUCE/MINT LWSC-preservation; locks where cap-resolution enters assembly.
#print axioms Bang.Model.reduce_live_preserves_lwsc
#print axioms Bang.Model.mint_preserves_lwsc
