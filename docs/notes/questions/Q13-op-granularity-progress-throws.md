---
type: design-question
title: "Operation-granularity: `progress` for `throws` needs op-aware signatures"
description: "label-granular rows vs op-granular handlers — op-partial EffSig signatures close progress"
status: decided
area: effects
resolved-by: ["ADR-0023"]
ties: ["ADR-0022", "ADR-0023"]
see-also: ["Bang/Core/Soundness.lean"]
---
**Resolution (2026-06-22, ADR-0023)**: Co-resolved with the CK machine. The Unit-2 `sorry` had TWO
facets, not one: (a) the wrong-op-same-label case this entry names (`up ℓ "get"` under `throws ℓ`),
and (b) a DEEPER one this entry MISSED — an operation nested under `letC`/`app` inside the handle is
stuck under the shallow step *even with the right op* (machine-checked: `handle (throws ℓ)(letC (up ℓ
"raise" v) N)`). (b) needs the **CK machine** (ADR-0023); (a) needs **op-partial `EffSig`
signatures** (recommended option 1 below) — `opArg`/`opRes : Label → OpId → Option VTy`, `up`
requires `some`, `handleThrows` requires the interface `= {raise}`. Both landed in ADR-0023 (D6 + the
machine); `progress`/`type_safety` are axiom-clean over the machine. The `labelEff_sep` law (sub-gap
b of this entry) also landed as an `EffSig` law. Original deliberation preserved below.

**Question (historical)**: effect rows are **label**-granular (`labelEff ℓ : Eff`), but the `throws`
handler reduces only the `"raise"` **operation**. So `handle (throws ℓ) (up ℓ "get" v)` is
well-typed (label `ℓ` is in the row) yet **stuck** (`Source.step`'s throws arm matches only
`"raise"`), and `progress` cannot exclude it. This is the single `sorry` left in Unit 2
(`Bang/Core/Soundness.lean` `progress_gen` handleThrows case); `preservation` + `up` + `handleThrows`
are axiom-clean.

**Why it matters**: `progress`/`type_safety` (now stated at `⊥`, ADR-0022 D3) are headline ◊2
theorems; they regressed from axiom-clean to `sorry` when effects were added. The root is that
`EffSig.opArg`/`opRes : Label → OpId → VTy` are **total** over op-strings — the kernel "declares"
every operation for every label, so it out-permits the source language (where `effect Exn { raise }`
has no `get`).

**Two sub-gaps** (the proof-engineer named both):
1. **label separation** — `labelEff ℓ' ≤ labelEff ℓ ⊔ φ → ℓ' ≠ ℓ → labelEff ℓ' ≤ φ`. Easy:
   add as an `EffSig` law (holds for `Finset` singletons; needs a distributive lattice +
   atom-ness). This closes the `ℓ' = ℓ` half.
2. **throws-op restriction** — under `handle (throws ℓ)`, the body's `ℓ`-operations are only
   `"raise"`. The hard half; not expressible with label-granular effects.

**Options**:
1. **Op-aware signatures** *(recommended)*: `EffSig.opArg/opRes : Label → OpId → Option (VTy)`
   (`none` = not in the effect's interface); `up` requires `opArg ℓ op = some _`; `handleThrows`
   requires `ℓ`'s only defined op is `"raise"`. Closes the gap; re-touches the `up` rule + every
   `up` proof case.
2. **Op-granular effect rows**: track `(Label, OpId)` in `Eff`, not just `Label`. Bigger; changes
   ADR-0001's row carrier.
3. **Specialize `progress`/`type_safety` to `Eff = EffRow`** (Finset Label) with the separation
   lemma decidable — but there is currently **no `EffSig EffRow QTT` instance** in the tree, and
   it doesn't fix the op restriction.

**Blocked on**: the (1)-vs-(2) design choice. (1) is the lighter, recommended path.

**Revisit signal**: closing the `progress`/`type_safety` `sorry` (next Unit-2 follow-up).
