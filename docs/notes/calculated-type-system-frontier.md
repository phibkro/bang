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

## Cousot's calculational logic design (`cousot-calculational-incorrectness-logics`) — the SN-free template (the methodological keystone)
This RE-FRAMES the whole frontier. Cousot derives PROGRAM LOGICS (Hoare, incorrectness, …) as Galois
**abstractions of the relational semantics** `⟦S⟧`, and reads the proof rules off — sound+complete *by
construction*, no separate soundness proof; "healthiness conditions" become consequences of `α` **preserving
joins**. The recipe (§II.6): semantics → fixpoint form (fixpoint abstraction) → invariant/variant (fixpoint
induction) → deductive rules (Aczel's lfp-of-rules correspondence).

**Why it supersedes the SbC framing above:** Cousot assumes NO strong normalisation — `lfp`/`gfp`/bi-induction
handle nontermination directly. So **SbC is the SN-restricted special case of Cousot's method**; bang threw
away SN, so *Cousot* is the actual template, and step-indexed `Crel` is its operational realization (the
correspondence step-index ≈ ordinal/guarded fixpoint approximation is established — Appel–McAllester, Birkedal's
topos of trees). Two further correspondences: **over/under-approximation = may/MUST effects** (bang's rows are
the may/over half; the must/under dual exists by construction — the unexplored direction Gordon's
over-only AI doesn't give); and the **sets-vs-formulas gap** (Cousot uses sets-of-states, clean+complete; a
*decidable syntactic* type system is the "formula" level with "no best abstraction") **names why bang's eventual
decidable graded checker (inc-7) cannot be complete w.r.t. the semantic `Crel`** — a structural inevitability,
not a design failure.

**Calibrations (the synthesis reaches in three places):** (a) "Aczel = the SbC fixpoint, *same theorem*"
overstates — it's the same *machinery* (typing relation = lfp of a rule functor + derive-by-abstraction),
generic to inductive definitions, not literally one theorem. (b) the step-index ≈ ordinal-iterate correspondence
is real but *already known*, and it's a *template/analogy* for #35 (resumption metering), NOT a derivation of
the grade. (c) Cousot is FIRST-ORDER imperative (no higher-order, effects, or grades) — the port to graded CBPV
is the unproven work, and the **reduced product** (§I.3.15.3) is the named machinery for the *coupled* effect×grade
case (only needed if effects go ordered; idempotence keeps them decoupled today — see the Gordon section).

**The decisive port-or-break test (sharpens the probe above):** Cousot's method rests on `α` **preserving joins**.
The effect axis preserves them trivially (`α = ⊔`, idempotent). The **grade axis (QTT `+`/`×`) is the open
question** — three roads (does-the-grade-fall-out · is-the-product-reduced · is-`α`-join-preserving) are one toll
booth. **This experiment is now DEPLOYED** (run the §II.6 recipe on a grade-bearing bang rule, check join-preservation
of the grade `α`); findings → `docs/notes/calc-typer-experiment-findings.md` when it lands.

## The full triangulation (6-paper close, 2026-06-27) — bang's position is now defensible, not accidental
Ivašković–Mycroft–Orchard (`ivaskovic-fscd20-dataflow-effects-graded-monads`, FSCD'20) welds the two halves:
data-flow analysis = effect system = graded monad, with **transfer functions as the shared substrate** (the
Cousot fixpoint-iteration *is* the Katsumata graded bind). Its punchline — **effect quantales are too
restrictive** (distributivity excludes non-distributive analyses like constant propagation); the right general
structure is a pomonoid `(D,⊑,▷)`, not Gordon's quantale — *doesn't bite bang* (bang sits BELOW the quantale at
`▷=⊔`), but it **catalogs what the commutative corner costs**: flow-sensitive expressivity (liveness,
reaching-defs) — which is *orthogonal to bang's purpose* (handler-effects, not data-flow analyses), so it's a
named non-loss, not a gap.

**The verified correction this closes (my check, not the synthesis's):** the synthesis claims bang's grades have
**no order**. Confirmed against source — `Bang.Mult` is a bare `CommSemiring` (the `q_or_1` floor is a function,
not an order; the kernel's only `≤` is on *effects*, `labelEff ℓ ≤ φ`). This **reconciles** the apparent
contradiction with the AI experiment: that experiment's `{0,1,ω}` diamond order was a **constructed abstract
domain**, NOT bang's native grades. Consequence (the synthesis's sharpest point, now grounded): with no grade
`⊑` to least-fixpoint over, **bang's grades must be CHECKED, never INFERRED, at loops** — structurally, by
construction, mirroring the declarative-type-system / no-executable-checker stance. To even run Cousot's method
on grades you would first have to *equip* `Mult` with the diamond order (an added construction).

bang's full position, every clause a deliberate stance you can defend against the literature:
> **Calculate a graded effect-and-coeffect system by construction, over a step-indexed logical relation, in the
> commutative `▷=⊔` corner, with a non-idempotent grade semiring whose order is absent (so grades are checked,
> not inferred).**

| paper | gives bang | bang's deliberate departure |
|---|---|---|
| Cousot '24 | calculate rules by AI | idempotent lattices only; bang's grade `+` is non-idempotent |
| Gordon (quantale) | effects-as-AI structure | bang sits *below* it (`▷=⊔`, decoupled axes) |
| Ivašković '20 | dataflow=effects=graded; trivial→refined grades | bang grades trivial/erased + **no order** |
| Katsumata '14 | the `▷`-monoid under `U_φ` | — (adopted) |
| Gaboardi '16 | effect × coeffect | bang's exact two axes |
| Timany '24 | logical soundness (`Crel`) | — (adopted) |

**The two genuine frontiers** (where, across all six papers, the field is thinnest, and where bang does novel
work): (1) **non-idempotent quantitative grading across fixpoints** (the `ω`-collapse / #35); (2)
**checked-not-inferred at fixpoints** (no grade order). The one actionable near-term thread the data-flow paper
surfaces: **trivial→refined grades** (its §4.3.2) is a useful *lens* for ADR-0059 (grades go from runtime-erased
to compile-load-bearing) — a framing, not literally its store-passing construction; verify against ADR-0059.

## Status / gating
Post-v1. The resumptive fragment gates on **#35** (grade-the-resumption); the binary LR it builds on is itself
deferred (inc-6). **Not a reason to turn the wheel off the keystone.** Captured here so it's not lost.
