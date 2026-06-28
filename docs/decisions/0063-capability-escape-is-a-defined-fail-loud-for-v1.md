# 0063 — Capability escape is a defined fail-loud for v1; scoped-cap types deferred post-v1

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The inc-5 diagonal `HasConfigTy ([],c) → NonEscape ([],c)` — the derivation that makes
  `type_safety` mean "well-typed ⟹ safe" rather than "well-typed ∧ (undischargeable premise) ⟹ safe" — is
  **build-refuted**. A typeable, VcapFree program (`progComp`, `Bang/ReturnEscapeReach.lean`, axiom-clean +
  `#guard Source.eval = .stuck`) launders a **state** handler's capability into a returned **thunk** via an
  inner re-handle of the same label: the re-handle discharges the label from the thunk's external type **by
  label** (identity-blind), so the handler's answer-type B-occ (ADR-0057) is satisfied, while a live
  `cap ℓ` rides inside. Forced after the handler pops, the cap dispatches **by identity** to the dead handler
  ⟹ STUCK. B-occ guards the *direct-perform* escape; it does **not** guard the *laundered-via-re-handle*
  escape (the `liveCapsResolveC_returnEscape` POP-preservation lemma is build-FALSE as stated —
  `Bang/ReturnEscapeRefute.lean`). DECISION (operator, 2026-06-28): for **v1**, reclassify the
  capability-escape as a **DEFINED fail-loud outcome** — add `Result.escapedCap` (a defined terminal,
  distinct from `.stuck`); `Source.eval` routes the `perform (vcap n ℓ)`-with-`idDispatch = none` case there;
  `FocusResolves'`/`NonEscape'` accept the defined-escape config as terminal (so the diagonal becomes
  typing-derivable again); `returnEscape` is restated (the POP re-homes **OR** the focus is a defined
  escape). `type_safety`'s **text is unchanged** (`∀ fuel, Source.eval fuel c ≠ Result.stuck`) — the escape
  simply moves out of `.stuck`, so the theorem now reads "well-typed ⊥ programs never reach **genuine**
  stuck; they return, diverge, or hit a defined capability-escape fail-loud" (OCaml-effects' `Effect.Unhandled`
  as a defined result). The **structural** fix — scoped/region capability types making the escape *untypeable*
  — is the **post-v1** goal. Reopens **#50**; amends **ADR-0057**.
- **Refines**: 0057, 0054, 0023
- **Depends-on**: 0016, 0001, 0055
- **See-also**: 0061, 0035, 0058, 0062

## Status

Accepted (2026-06-28). Records a **frozen-statement reshape** (the `Result` type gains a constructor;
`Source.eval`'s classification of the escaped-cap case changes; `NonEscape`/`FocusResolves`/`returnEscape`
are restated). Operator-ratified after a build-arbitrated, manager-gated soundness investigation. The
witnesses are committed as regression tests (`inc5-comp-grind`: `68c44e0`, `bce2093`).

## Context

`type_safety` (`Bang/Spec.lean`) is `HasConfig (0,[],c) ⊥ (F q A) → ∀ fuel, Source.eval fuel c ≠
Result.stuck`, where `HasConfig = HasConfigTy ∧ NonEscape` and `NonEscape cfg = ∀ cfg', StepStar cfg cfg' →
FocusResolves cfg'`. The inc-5 deliverable (the **diagonal**) is to *discharge* `NonEscape` for the initial
config **from typing** — `HasConfigTy ([],c) → NonEscape ([],c)` — so that `type_safety` is a real
"well-typed ⟹ safe" theorem rather than one with an undischargeable hypothesis.

Closing the diagonal's POP arm required `liveCapsResolveC_returnEscape`: a focus carrier resolving in
`handleF g' hd :: K'` re-homes to the popped `K'` when no carrier-live cap references the popped handler.
The grade-sensitive carrier (ADR-0061) closes the **dead** intermediate (q=0 ⇒ gate-dormant); the **live**
intermediate reduced to a pure-typing capability-containment claim — `var0 live in N ⟹ ℓ≤φ ∨ labelOccurs ℓ B`
— which a build-arbitrated refute-test showed is **FALSE**: an inner `handle ℓ` (re-handle) launders ℓ out of
both the row and the result type by label, while the cap dispatches by identity to the *outer* handler. The
witness was then **sealed**: `progComp` typechecks (`HasCTy [] [] progComp ⊥ (F 1 unit)`, axiom-clean) **and**
`Source.eval progComp = .stuck` (a closed, pure, well-typed program that gets stuck = the `NonEscape`/progress
content the diagonal cannot establish).

Discrimination (build-found): the escape is specific to **state/transaction** handlers, whose answer type is
**free**. `throws` is *untypeable* here — `handleThrows` pins its answer to the raise payload — so the throws
form is already excluded. So this is ADR-0057's family (`#50`, "B-occ guards A, not S") **one level deeper**:
the answer-type B-occ is defeated precisely where the answer type is unconstrained and a re-handle can launder
the label.

A capability is a first-class value (the bang thesis). First-class values can be captured into thunks and
escape their dynamic extent — that is the nature of first-class values, not a kernel bug. The kernel already
**fails loud** here (global-fresh minting ⟹ the escaped cap finds no handler ⟹ `idDispatch = none` ⟹ a
detected terminal, never silent corruption). The only question is how the *type system* accounts for it.

## Decision

Reclassify the escape as **defined behavior** for v1 (the kernel already produces it; we name it):

```
1. Kernel — Result gains a defined terminal:
     inductive Result α | done (v) | escapedCap | stuck | …
   Source.eval: the `perform (vcap n ℓ) op v`-with-`idDispatch K n ℓ op v = none` case
   (the only step=none-non-terminal a WELL-TYPED ⊥ program can reach) ↦ .escapedCap  (was .stuck).

2. FocusResolves' / NonEscape' — accept the defined-escape config as terminal:
     FocusResolves' cfg := (focus caps resolve) ∨ (cfg is a defined-escape config)
   ⟹ NonEscape' IS derivable from typing ⟹ the inc-5 diagonal completes.

3. returnEscape RESTATED — the POP arm re-homes OR the focus is a defined escape
   (the build-refuted `liveCapsResolveC_returnEscape` becomes a true disjunction; the
   sealed witness is the defined branch, not a counterexample).

4. progress — RESTATED (the SIBLING frozen statement; under-specified in the first draft of
   this ADR). `progress` (`isReturnConfig ∨ steps`) must gain a third `∨ is-defined-escape`
   disjunct: the escape config neither returns NOR steps (`step = none`), so once `NonEscape'`
   replaces `NonEscape` in `HasConfig`, the safety content RELOCATES here — it does not dissolve.
   This is the real remaining obligation, and it is PROVABLE (the reclassification ALLOWS the
   escape), unlike the false `returnEscape` it replaces.

5. type_safety — TEXT UNCHANGED (`∀ fuel, Source.eval fuel c ≠ Result.stuck`).
   The escape lands in `.escapedCap`, so `.stuck` is unreachable for well-typed ⊥ programs ⟹
   the theorem is provable AND meaningful (via the restated `progress` + `HasConfig`→`NonEscape'`).
```

**Implementation status (2026-06-28).** Landed + manager-gated on `inc5-comp-grind`: the kernel
`Result.escapedCap` (`d745253`) and the Model-side `NonEscape'`/`FocusResolves'`/`diagonal'` (`7d7ebf9`,
sorry-free `[propext, Quot.sound]`, green set 716 jobs). `NonEscape'` came out STRONGER than "derivable
from typing": `FocusResolves'` (`focus resolves ∨ idDispatch = none`) is a **tautology**, so `diagonal'`
(`HasConfigTy ⟹ NonEscape'`) closes unconditionally. That makes it a correct **building block**, NOT
`type_safety` closure — `Spec.lean` is untouched (`HasConfig` still uses the old `NonEscape`; `progress`
still `returns ∨ steps`). The remaining **wiring** — `HasConfig`→`NonEscape'`, the `progress`
escape-disjunct restatement (step 4), the `type_safety` re-proof, and the CalcVM `.escapedCap` accounting
(invariant #1) — is **inc-6** (Spec/Compile/CalcVM are pre-red there). The vestigial
`WScfg`/`returnEscape` machinery is parked, not deleted, until that wiring lands.

The resulting v1 guarantee: **a well-typed ⊥ program never reaches genuine `.stuck` — it returns, diverges,
or hits a defined capability-escape fail-loud.** This is the standard "unhandled effect is a defined runtime
outcome" guarantee (OCaml 5 `Effect.Unhandled`, Koka's `final`).

## Consequences

- `type_safety` closes for v1 with its frozen text intact; the guarantee is honestly stated (no
  undischargeable `NonEscape` premise, no hidden hollow theorem).
- The two regression witnesses are **permanent tests** pinning the v1 semantics: `ReturnEscapeReach.lean`
  (typeable ∧ `.escapedCap`) and `ReturnEscapeRefute.lean` (the as-stated POP lemma is false). When the kernel
  reshape lands, `ReturnEscapeReach`'s `#guard` flips from `.stuck` to `.escapedCap`.
- **#50 is REOPENED** as the post-v1 structural item; **ADR-0057** is amended (its B-occ is sound but
  *incomplete* — it guards direct-perform, not laundered-re-handle escape).
- **Post-v1 goal:** scoped/region capability types that make the escape *untypeable* (`progComp` would then
  fail to typecheck, and the witnesses get re-proven UNtypeable). That is the correctness-by-construction
  endpoint; v1 ships the defined-fail-loud as the honest intermediate.
- A small deferred follow-up: the q=0 vacuous branch in `ReturnEscapeRefute.lean` (line 81) needs a Model
  budget-preservation lemma to be fully sorry-free; the **seal** (`ReturnEscapeReach`, axiom-clean) carries
  the verdict independently, so this is cosmetic.

## Alternatives considered and rejected

- **Proof-invariant "the cap doesn't escape"** (strengthen `NonEscape`/B-occ to *prove* no escape) — REJECTED,
  **build-impossible**: the sealed witness proves the cap **does** escape operationally, so any such invariant
  is false. The bad program must become *untypeable* or *defined-behavior*, never "proven-not-to-escape".
- **Scoped/region capability types now** (make `progComp` untypeable in `HasCTy`) — REJECTED for v1 on cost:
  a research-grade type-system extension (rank-2 / region polymorphism, the `runST` move). It is the **right
  post-v1 answer** and is recorded as the deferred structural goal, not discarded.
- **Second-class capabilities** (forbid storing caps in thunks/data at the surface) — REJECTED: it would
  restore safety but **sacrifices the "paradigm and capabilities are first-class values" thesis**, the core
  of the language.
- **Fold into #35 with no defined semantics** (just defer) — REJECTED: leaves `type_safety` hollow (the
  `NonEscape` premise stays undischargeable) and ships v1 with an *undefined* stuck rather than a *defined*
  outcome. Reclassifying gives the same deferral of the structural fix **plus** a provable, meaningful v1
  theorem.
