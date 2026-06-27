# Calculating the type system — a post-v1 research frontier

> Banked 2026-06-27. Relationship of **Sound-By-Construction Type Systems** (Bahr/Garby/Hutton) and
> **The Calculated Typer** (Garby/Bahr/Hutton, Haskell'25) to bang-lang, and the genuinely-novel frontier
> they point at. **Post-v1; OFF the keystone/inc-6 critical path.** SoT for the "calculate the type system"
> idea. refs.bib: `bahr-pearl25-sound-by-construction`, `garby-haskell25-calculated-typer` (+ the compiler sibling
> `garby-haskell24-calculating-effectively`).

## The two papers (same Nottingham/ITU calculational lineage as our CalcVM)
- **Sound-By-Construction Type Systems** (Bahr, Garby, Hutton — functional pearl, Agda): derives the TYPING
  RELATION `⊢ e : t` by **solving the soundness property** (`⊨ e : t  ≡  ∃v. e ⇓ v ∧ v ∈ ⟦t⟧`) algebraically —
  the rules come out sound-by-construction, no separate soundness proof. Scope limit: deterministic big-step +
  **strong normalisation**.
- **The Calculated Typer** (Haskell'25, Agda+Haskell): derives the **checker** (executable decision procedure)
  by fold fusion, given a typing discipline. **Checking, NOT inference** (inference flagged for follow-up).
  Scope: semantics expressible as a fold.
- They compose (SbC gives the relation, TCT the program deciding it) and are the **typing-side analogue of the
  Bahr–Hutton calculated-compiler method** bang already uses for CalcVM (invariant #4).

## The asymmetry (the lens — and why it's a feature)
bang **calculates** the machine (CalcVM) but **hand-ports** the type system (`HasVTy`/`HasCTy` from Torczon).
This is a deliberate **build-vs-reuse** call, NOT a gap: no off-the-shelf verified CBPV→WasmFX compiler exists
(must derive); Torczon's graded-CBPV type system **is** the validated off-the-shelf artifact (reuse, don't
reinvent). The *novel* typing content — **capability safety** (`vcap` escape, the diagonal, B-occ, the
grade-gate) — was already derived via a *loose* sound-by-construction: **refute-first + build-arbitration
forced the rules** (`escapeB_app` killed the ⊥-row approach; the grade-gate was forced by dormancy). The
method isn't absent — it's done operationally (Lean + the build arbitrating) rather than via Agda calculation.

## Why SbC doesn't plug in (the honest blockers)
- **Strong normalisation is load-bearing** in SbC's calculation; bang threw it away by design (Div fragment,
  `mu`, thunks). SbC's `∃v. e ⇓ v` is vacuously false on divergence.
- No resource axis (grades); no resumption (zero-shot only).
- BUT the **method survives** the move from SbC's SN-total `⊨` to bang's **step-indexed `Crel`** (`Vrel`/`Crel`/
  `Krel`, `Bang/LR.lean`) — which IS the `⊨ᵏ` generalisation SbC lists as future work. SN's substitute is the
  strict `j < n` ▷-guard at `U φ B` / `mu` (base types stay flat, matching SbC's flat `⟦Int⟧`); divergence rides
  the vacuous `CoApproxC_le 0 = ⊤` floor; determinism is **free** (`Source.step`/`run n` are functions).

## CRITICAL caveat — which soundness route (structural, easy to get wrong)
bang has **two** soundness routes; the SbC-over-`Crel` idea maps onto the *deferred* one:
```
DIAGONAL  (unary NonEscape, Bang.Model)        → type_safety · preservation · progress
                                                  NEARLY CLOSED (the keystone). NOT Crel-based.
BINARY LR (Crel / lr_fundamental / lr_sound)   → contextual equivalence · effect_sound · grade erasure
                                                  DEFERRED to inc-6 (Canonical wall, ADR-0058). Crel-based.
```
So calculating rules over `Crel` would target **`effect_sound` / grade-erasure** (genuinely open, Crel-shaped) —
**NOT** `type_safety`/`preservation` (diagonal-routed, already proven). It does **not** help close v1 soundness.

## The frontier (the genuinely-novel part — worth a paper)
SbC solves for type **shapes**. bang's rules carry **grade arithmetic** (the `let`-rule's
`γ₁ + (q1 · q_or_1 q2) • γ₂`). **Nobody has calculated a quantitative/graded type system from a step-indexed
soundness relation.** If the grade coefficients **fall out** of the `Crel` calculation (rather than being fed in
as a QTT axiom), that is the contribution — the graded, non-terminating, resumptive extension SbC defers,
adjacent to the categorical/Trinity framing (the algebraic structure *determining* the rule).

## The decisive probe (when pursued — do THIS first, not the obvious thing)
NOT the zero-shot `handleThrows` transcription. That carries over `Crel` now (`krelS_handleF`'s throws case;
the resume conjunct is vacuous because zero-shot discards `Kᵢ`), BUT the rule is already ported + settled, so it
demos the *method* and produces no new rule — and the resumptive case (`handleState`/`transaction`) is blocked on
**#35** anyway (each resume re-entry consumes index ⟹ the `∀n` budget must stay positive until termination = the
▷-metering / `krelS_append` crux). The one question that decides **paper vs. elegant re-description**:
> **Does a single grade coefficient fall out of the `Crel` calculation of one rule (the `let`-rule), or must it
> be asserted?** `Crel` constrains *behaviour*; the multiplicity coefficients are *resource* accounting. Whether
> `Crel` has the resource-sensitivity to *force* the coefficients is **unshown** — and is the hard part.

Falls out → the paper. Must be fed in → an elegant re-description (learned cheaply). Put that probe first.

## Gordon's effect-quantale framing (arXiv:2606.19686) — refines the grade-derivation question
Gordon (`gordon-arxiv2606-effect-systems-as-abstract-interpretations`) embeds effect systems as abstract
interpretations over an **effect quantale** (join `⊔` for branching + partial monoid `▷` for sequencing,
Def 2.1). bang is the **degenerate, commutative, total** corner: `▷ = ⊔` — effects track *which* labels,
never *order* (you give up protocols/locks/sessions; commutativity is a real simplification, not free).
The strongest point, and it holds: **effect idempotence (`φ ⊔ φ = φ`) DECOUPLES the effect and grade axes.**
Running a computation N times gives effect `φ ⊔ … ⊔ φ = φ` (no growth) but grade `q × N` (growth), so the two
transfer functions never feed each other — the `letC` product is **direct (independent), not reduced**. That
is *why* `φ₁ ⊔ φ₂` and the grade arithmetic compute side-by-side at `letC` without coupling, and what keeps a
graded sound-by-construction calculation tractable.

**This refines the decisive probe above.** The grade axis is an *independent semiring* (decoupled by
idempotence), so "do the grade coefficients fall out of the `Crel` calculation?" partly resolves: the
coefficients are the QTT *semiring's own* structure (an independent axis), not derived from the
behavioural/effect calculation. The genuinely-novel thing to *verify/derive* is then the **decoupling
itself** (that the product is direct, not reduced) + the type-shape rules — not the grade coefficients per
se. Gordon does **soundness, not derivation** (the SbC complement); composing the two for the *graded* case
is what nobody has done.

**Caveats on the synthesis (assessed, not all of it survives):** (a) "time/order lives in the grade `×`" is
loose — QTT `×` is commutative, so it doesn't track order either; the directionality is in the *asymmetric
`letC` scaling* (`γ₁ + (q1·q_or_1 q2)•γ₂`), not the operation. (b) Gordon flagging continuation
answer-type/effect mutual-dependency as hard is *adjacent* corroboration for #35, not an exact match (#35 is
resumption *multiplicity*; Gordon's is effect/type *mutual-definition*). (c) the warning IS solid: ordered
effects (`▷ ≠ ⊔`) re-couple the axes (Gordon §6 iteration, non-unique fixed points), so bang's
idempotent-effects choice is **load-bearing for the graded calculation's feasibility**, not a free simplification.

## Status / gating
Post-v1. The resumptive fragment gates on **#35** (grade-the-resumption); the binary LR it builds on is itself
deferred (inc-6). **Not a reason to turn the wheel off the keystone.** Captured here so it's not lost.
