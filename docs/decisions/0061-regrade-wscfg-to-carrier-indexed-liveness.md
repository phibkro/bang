# 0061 — Regrade `WScfg` to a carrier-indexed liveness invariant (`LiveCapsResolveV/C/K`), derived coherent from typing

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The diagonal's preservation obligation `wsCfg_step` was carried by a **typeless**
  well-scoping invariant (`LWSC`/`LWSK`, a `Bool`/flag-liveness over the term structure). Its POP arm was
  machine-**WALLED**: `escapeB_app` refuted the ⊥-row/B-occ shaping (an arrow-guarded cap survives
  `app`-elimination into a `¬labelOccurs` answer type), proving **escape is grade-`q=0`-dead, NOT
  row-absent** — so a flag that reads liveness off the *term* cannot distinguish a spurious-live cap that
  only the *grade* catches. DECISION: **REGRADE** the invariant from typeless flags to a **carrier**
  (`LiveCapsResolveV/C/K`, an inductive `Prop` indexed by the *typing derivation* `HasVTy/HasCTy`). The
  carrier sees vcap **literals** only (a var-0 thunk materialises a cap only at REDUCE, so var-0 is *no
  carrier obligation* — exactly the `U {ℓ} Int` dormant-thunk position where the two prior refutations
  lived). `WScfg` then carries `LiveCapsResolveC` **+** the typing derivation and **DERIVES a coherent
  `LWSCg` by construction** (the `of_typed_live` engine: liveness grades = typing grades; dead values route
  to `vcap_dormant`, no resolution obligation), with the symmetric stack carrier `LiveCapsResolveK`. This
  makes the spurious-live-cap state **unrepresentable** rather than flag-detected, and is what lets the
  POP/REDUCE binder arms close where typeless flag-liveness choked. ENGINE + RESHAPE landed axiom-clean
  (`798f04e`); the carrier-subst **keystone** (`liveCapsResolve{V,C}_subst_gen` + `…_weaken`) closed
  axiom-clean at `da67c2d` (`inc5-lr-reindex`). The remaining consumer machinery
  (`liveCapsResolve{V,C}_returnEscape` + `lwsg_step_nonperform`) is tracked by **task #54**; the keystone
  is *not* one consumer-step from `type_safety` (build-refuted twice — the POP cross-term needs a combined
  carrier+grade-live-var invariant the subst lemma does not supply).
- **Refines**: 0060, 0057, 0056
- **Depends-on**: 0054, 0001, 0018, 0016
- **See-also**: 0055, 0058, 0062

## Status

Accepted (2026-06-27); filed 2026-06-28 as a decided-ledger backfill — the decision was referenced as
authoritative in `CONTEXT.md` + `paths/PATH-inc5-lr-reindex.md` and implemented on `inc5-lr-reindex`
before its ADR existed; this record closes that phantom-ADR gap, the same hygiene as task #49's backfill of
0056/0057/0060).

## Context

`type_safety` is closed by the diagonal `WScfg ⇒ FocusResolves ⇒ NonEscape`, whose preservation step is
`wsCfg_step` (the `WScfg`-is-preserved-under-`Source.step` lemma). Through ADR-0060 the well-scoping carried
in `WScfg` was **typeless**: `LWSV/LWSC/LWSK`, a structural flag-liveness that marks a storage position
live/dormant by term shape. ADR-0060 already committed the grade rig (`NoZeroDivisors`, `ZeroSumFree`,
`Nontrivial`) so that a discarded binding forces its grade to `0` — but the *invariant itself* still read
liveness off the term, not the grade.

The POP arm is where this breaks. A live binder of type `U {ℓ} Int` is **sound** — a dormant thunk-cap,
guarded from escape by B-occ on the *answer* type — yet `labelOccurs ℓ (U {ℓ} Int) = true`, so any
type-occurrence Γ-premise (`γ[i] ≠ 0 → ¬labelOccurs ℓ Γ[i]`) is **refuted** by it. Two machine-checked
refutations pinned the wall:

1. `escapeB_app` — an arrow-guarded cap survives `app`-elimination into a `¬labelOccurs` answer type.
   The cap is operationally dead (grade `q = 0`), so the invariant was *too strong*, not the language
   unsound: **escape is grade-dead, not row-absent.**
2. `lwsvg_closed_regrade_refute` — scale-gates couple grade ↔ liveness even for *closed* values, so a
   `∀ γ' b'` regrade of the typeless flag is FALSE.

The lesson: liveness is a fact about **which caps the grades keep**, and the invariant must be indexed by
the object that carries the grades — the **typing derivation** — not by the bare term.

## Decision

Replace the typeless flags with a **carrier**:

```
LWSV / LWSC / LWSK        (typeless flag-liveness, term-indexed)      ── DELETED as the WScfg carrier
        ▼  REGRADE
LiveCapsResolveV/C/K      inductive Prop, indexed by HasVTy/HasCTy    ── the new carrier
```

- The carrier resolves only **vcap literals** against the live evaluation context. A var-0 (a `vvar`)
  carries no obligation — its thunk-cap materialises only at REDUCE — so the `U {ℓ} Int` dormant-thunk
  position that refuted the type-occurrence approach is handled *for free*.
- `WScfg` carries `LiveCapsResolveC` **together with** the typing derivation, and derives a **coherent**
  `LWSCg` by construction via the `of_typed_live` engine (liveness grades ≡ typing grades; a dead value
  routes to `vcap_dormant` with no resolution obligation). The stack mirror is `LiveCapsResolveK`.
- Grade-coupling (ADR-0060's rig) does the dormancy work *inside* the carrier: a discarding binder forces
  `q1 * q_or_1 q2 = 0`, and with `q_or_1 q2 ≠ 0` + `[NoZeroDivisors]` this gives `q1 = 0`, switching the
  carrier's `ret`-gate `q1 ≠ 0` OFF — the cap is dormant, no obligation.

This is the **stratification / correctness-by-construction** move (CLAUDE.md): the spurious-live-cap state
that a flag could only *detect* becomes *unrepresentable* in the carrier.

## Consequences

- **Closed under this regrade:** `freshCfg_step` (#1), `lwskg_pop_fresh` (#2), the POP-tail building blocks
  `liveCapsResolve{V,C}_pop` + `liveCapsResolveK_rehome` (PIECE 1, `0acfd6b`), and the carrier-subst
  **keystone** `liveCapsResolve{V,C}_subst_gen` + `…_weaken` (#51, `da67c2d`, axiom-clean).
- **Open (task #54):** `liveCapsResolve{V,C}_returnEscape` (the POP-focus cross-term — a *combined*
  carrier + grade-live-var invariant, NOT the subst lemma) → `liveCapsResolveK_restack`/`_pop` → the
  `Source.step` case analysis → `lwsg_step_nonperform` → `type_safety` = sorryAx-on-`lwsg_step_dispatch`
  (#35 / ADR-0062)-only.
- The carrier rides **existing** `Bang/Metatheory.lean` substitution infra (`HasCTy.subst_gen` et al.) — no
  kernel primitive, no frozen-statement change, so no further ADR gate for the grind itself.
- `LiveCapsResolveV/C/K` live in `Bang.Model` (an inc5-only module); the eventual reconciliation promotes
  the shared `HasVTy.subst_gen` prereq to `Bang.Metatheory` (task #53).

## Alternatives considered and rejected

- **Keep the typeless flag-liveness, strengthen the POP lever** (the pre-regrade path) — REJECTED, machine-
  refuted: `escapeB_app` + a three-way build survey (ADR-0060's opt-1 later-modality / opt-2 reachability /
  opt-3 single-position grade-gate) closed off every first-order term-indexed fix.
- **Type-occurrence Γ-premise** (`γ[i] ≠ 0 → ¬labelOccurs ℓ Γ[i]`) — REJECTED: refuted by the sound
  `U {ℓ} Int` dormant-thunk binder (`labelOccurs` is true on a binder that is nonetheless safe).
- **`∀ γ' b'` regrade of the closed-value flag** — REJECTED, machine-refuted (`lwsvg_closed_regrade_refute`):
  scale-gates couple grade ↔ liveness even for closed values.
