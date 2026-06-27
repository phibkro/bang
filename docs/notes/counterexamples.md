# Counterexample registry

Machine-checked **refutation / counterexample witnesses**: each proves that a
tempting-but-false statement is FALSE (derives `False` from the weaker form), or
exhibits a term that breaks a claim. Modelled on Mathlib's `Counterexamples/`
collection — one manifest (`Bang/Counterexamples.lean`) imports every witness, so
the registry builds as ONE target and `#print axioms` over it is ONE place.

**Do-not-weaken discipline.** Every witness is a kept regression guard: it pins WHY
a live statement carries the exact hypothesis/premise it does. Reverting that
statement to the weaker form re-admits the counterexample — so these files must NOT
be weakened or deleted. The table below is GENERATED from the manifest's membership +
`-- cex: guards=…` annotations and each witness's own doc-comment header; never edit
it by hand. Regenerate with `just counterexamples`; `just cex-check` gates currency.

**Gates.** `just cex-axioms` (= `lake env lean Bang/Counterexamples.lean`) reports
`#print axioms` per headline theorem; the lake build of the manifest re-verifies every
green witness is sorry-free. Two witnesses are pre-existing RED on the current branch
(they re-key onto the in-flight ADR-0055 `Config` reshape) — excluded from the build
target, flagged below, and NOT to be fixed here (that collides with the live regrade).

<!-- BEGIN GENERATED CEX INDEX — do not edit; run `just counterexamples` -->

| Witness | What it refutes / witnesses | Live statement it guards | Axiom standing |
|---|---|---|---|
| [`Bang.CohSubstRefute`](../../Bang/CohSubstRefute.lean) | REGRESSION WITNESS — keep; do NOT revert `lwscg_subst` to the single-grade hypothesis. | `lwscg_subst` (the ∀γ'b' reshape of the subst hyp) | clean — gate `just cex-axioms` |
| [`Bang.LwscgLengthRefute`](../../Bang/LwscgLengthRefute.lean) | REGRESSION WITNESS — keep; do NOT remove the `(hlen_v : γ_v.length = γ.length)` hypothesis from `lwscg_subst`. | `lwscg_subst` (the `hlen_v` length hypothesis) | clean — gate `just cex-axioms` |
| [`Bang.LwscgOfTypedRefute`](../../Bang/LwscgOfTypedRefute.lean) | REGRESSION WITNESS — keep; the existence-lift `lwscg_of_typed` (Bang/Model.lean) takes cap-resolution as a SEPARATE hypothesis (`∀ p ∈ capsC c, ResolvesLabel K …`), NOT from `LWSC`. | `lwscg_of_typed` (caps-resolve is a SEPARATE hyp) | clean — gate `just cex-axioms` |
| [`Bang.BoccRegress`](../../Bang/BoccRegress.lean) | B-occ regression oracle (ADR-0057). | `HasCTy` (the handle B-occ premise, ADR-0057) | clean — gate `just cex-axioms` |
| [`Bang.WsCfgInterfaceProbe`](../../Bang/WsCfgInterfaceProbe.lean) | INTERFACE RECORD for the `wsCfg_step` LWSC-preservation half (#44/#46). | `wsCfg_step` (records `lwscg_subst` off the critical path) | clean — gate `just cex-axioms` |
| [`Bang.LWRegress`](../../Bang/LWRegress.lean) | ADR-0054 behavioral regression suite (NonEscape's operational oracle). | `NonEscape` | RED — does not compile (pre-existing ADR-0055 Config reshape) |
| [`Bang.CapEscapeWitness`](../../Bang/CapEscapeWitness.lean) | ADR-0054 escape witness (finding artifact, re-keyed to identity dispatch). | `NonEscape` | RED — does not compile (transitive (imports Bang.LWRegress)) |

_5 green (built + axiom-gated via `Bang/Counterexamples.lean`; axiom sets ⊆ {propext, Classical.choice, Quot.sound}), 2 pre-existing-red (excluded from the build target). Generated from the manifest + witness headers — `just counterexamples`._

<!-- END GENERATED CEX INDEX -->
