# Experiment: does Cousot's calculate-the-rules method port to bang's graded CBPV?

> Run 2026-06-27 (the join-preservation experiment deployed from
> `calculated-type-system-frontier.md`). Ran Cousot's §II.6 recipe on `perform` (+ `handleThrows` at the
> seam): semantics → abstract by `α` → fixpoint form → rule via Aczel. Question: does the GRADE abstraction
> preserve joins / does the method port to graded CBPV? **Caveat:** the rule shapes were reconstructed from
> the calculus algebra + memory — the *derivation structure* is the result, not the exact side-conditions
> (check those against `Bang/Syntax.lean`).

## The headline result — the join-preservation question is answered, and the real break is elsewhere

**Both axes preserve joins. The grade axis is NOT disqualified by "semiring ≠ lattice."**
- `αE = support : M(Label) → Finset Label` — join-semilattice `⊔`, join-preserving ✓.
- `αG = count-collapse : ℕ → {0,1,ω}` (n≥2 ↦ ω) — the standard QTT quotient, a **semiring homomorphism**
  `(ℕ,+,·) → ({0,1,ω},+,•)`, over the diamond `0,1 ⊑ ω`. Join-preserving ✓ (`αG{0,1} = 0⊔1 = ω`).

So my predicted crux ("does the grade `α` preserve joins?") resolves **YES** — and the real obstruction is a
*different, sharper* one (below). The single-step recipe then ports **verbatim on both axes**:

**`perform` derived (single step):** the concrete usage transfer `#_z = q·#_z(V) + #_z(M_k)` and occurrence
transfer `{op} ⊎ occ(M_k)` are both join-preserving, so each has a best abstract transformer. Pushing `α`
through (αcount a semiring hom) gives `(q•γ_v) + γ_c` (grade) and `{op} ⊔ φ` (effect) — **each the best abstract
transformer ⟹ the rule is sound AND complete by construction.** The grade arithmetic `(q•γ_v)+γ_c` **falls out**
(answering the earlier "fall out or fed in?" — it falls out *at single steps*). One `perform` rule already
exhibits all three operations: `•` (Gaboardi coeffect action), `+` (resource-semiring add), `⊔` (effect monad).

## Where it actually breaks: the FIXPOINT, via non-idempotence (not join-preservation)

| recipe stage | effect axis (`⊔`) | grade axis (`+`) |
|---|---|---|
| single-step best transformer | exact | exact |
| **iteration combinator** | `⊔` idempotent | `+` **non-idempotent** |
| Kleene iterates stabilize | `φ ⊔ φ = φ` (exact) | only at `⊤`: `1+1+… = ω` |
| `α(lfp F) = lfp F̄` (Th II.2.1, `=`) | ✓ complete | ✗ **collapses to `ω`** |
| `α(lfp F) ⊑ lfp F̄` (sound) | ✓ | ✓ |

**Root cause: Cousot's exactness at loops rides on idempotency of the lattice join.** The effect `⊔` is
idempotent → the least fixpoint is reached and exact. The grade `+` is not → the only value stable under
`γ ↦ γ+γ` is the absorbing `ω`, so **every iterated/resumed resource collapses to `ω`** — all multiplicity
precision is lost across any fixpoint. This is `1+1=ω ≠ 1=1⊔1` made consequential. It is the *same*
non-idempotence Gordon flagged as decoupling the two axes — here it's what makes the grade *fixpoint*
sound-but-not-complete.

## #35 located precisely: it's Cousot's §II.3 variant, not a local `sorry`

Reclaiming finite grades across a fixpoint is a fixpoint **under-approximation** problem — Cousot's §II.3, not
§II.2: Th II.3.6 (transfinite iterates) + Th II.3.8 (**least-fixpoint under-approximation with a VARIANT
function** on a well-founded set). The variant you need = a well-founded bound on the **number of
resumptions** — which is exactly **ADR #35 (grade the resumption)**: the resumption count is itself a grade,
`krelS_append` is the metering lemma, and the step-index drop `n → n-1` is the zero-shot base case where the
variant decreases trivially. So #35 is **not a local sorry to discharge — it is the exact coordinate where
"quantitative AI is thin" meets bang's calculus.**

`handleThrows` cleaves along the same seam: *discharge* (effect `(φ\{ℓ})⊔φ_h` — join-preserving, derives
exactly; the subeffecting side-condition `e ≤ labelEff ℓ ⊔ φ` **is Cousot's consequence rule** = the
over-approximation `α`, derivable not postulated) + *resumption* (zero-shot `r=0` exact; one-shot `r=1`
precise; multi-shot `r=ω` hits the collapse).

## Verdict on porting

- **Effect half:** calculable for free, sound AND complete — it sits in Gordon's idempotent `▷=⊔` corner. (A
  theoretical fact; little practical pull, since the effect soundness is already done + easy — calculating it
  would reinvent a settled wheel.)
- **Grade half:** derives exactly at single steps (best transformers); its *fixpoint* rules are
  sound-not-complete under the powerset machinery. Completeness needs two things Cousot doesn't supply: (1)
  the graded analogue of Th II.2.1 (Katsumata's parametric effect monad as the algebra of `F̄`, so iteration
  composes by `•`/`+` not `⊔`), and (2) §II.3 variant-bounded under-approximation on resumption counts.
- That combination — **calculate a graded effect-and-coeffect system, complete across resumption, over a
  step-indexed relation** — is done by **none** of the five papers (Cousot calculates on idempotent lattices;
  Katsumata/Gaboardi give the graded algebra with no calculation; Timany gives step-indexed soundness with no
  calculation). **#35 is the single load-bearing piece of the whole synthesis.**

## My assessment (calibrations — the result is sound + rigorous)
- The derivation is solid and the locus is correct: the obstruction is **fixpoint-completeness under
  non-idempotent `+`**, NOT join-preservation (which holds). That's a *sharper and different* answer than the
  experiment was set up to find — a good outcome (it refutes the cheap "semiring ≠ lattice" objection and
  finds the real one).
- **Load-bearing assumption to keep visible:** the whole analysis rides on bang's `Mult` being the `{0,1,ω}`
  QTT collapse (`1+1=ω`). It is. If bang ever adopted a richer multiplicity semiring (`ℕ`, or an explicit
  affine `0..1`), the `ω`-collapse story changes. Relatedly, the diamond already loses **affine** precision at
  joins (`0⊔1 = ω` — "used at most once" rounds to `ω`); a definite `r=1` stays precise, which is why the
  one-shot fragment is the recoverable one.
- The `#35 = §II.3 variant` localization is the deepest, most useful finding — it reframes #35 from "an
  implementation sorry" to "the precise coordinate of an open quantitative-AI-across-fixpoints problem," which
  is motivating (it's a contribution, not a gap) and correct.

## Next probe (BANKED, not run — post-v1, gated on the deferred binary LR)
The most actionable experiment yet, because it touches real code: take the **one-shot resumptive handler**
(`r ⊑ 1`), state the variant as the **step-index itself**, and check whether **`krelS_append` discharges Th
II.3.8's hypothesis (4)** (the strictly-decreasing variant on re-entry). If it does → a **completeness proof
for the affine-resumption fragment by construction**, and multi-shot `r=ω` is then *honestly* the only place
precision is provably unrecoverable. Blocked on: the binary LR (`krelS_append`/`crelK_fund`) is deferred to
inc-6 (ADR-0058). Do it when that resumes, not before — the keystone is the live priority.
