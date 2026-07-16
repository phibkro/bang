# ADR-0094 · Environment semantics in the machine layer; the substitution spec stays

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: #61's measured cliff (per-step `Comp.subst` at ~1 ms/step — O(knot-body-size) per unfold; `docs/notes/hang-61-diagnosis.md`) is a reduction-STRATEGY cost, not an encoding bug, so the fix is representational: **introduce an environment/closure representation in the calculated-machine layer (`evalD` → `exec`), leaving `Source.eval` unchanged as the substitution SPEC** (option A1 of `docs/notes/envsem-survey.md`). `evalD_agrees_source` is re-proven as the substitution↔environment correspondence (the PLFA `γ≈ₑσ` pattern — mechanized prior art, not an invention); the machine gains one variable environment `ρ` + closure values alongside the untouched effect stores (`SStore`/`THeap` are effect-state, not var-env); `bang run`'s default flips to the compiled engine so real programs hit the fast path while the oracle stays the slow, simple reference. The whole ~1900-occurrence substitution proof spine (Soundness 427 · both LRs 453 · Freshness 103) is **preserved, not rebased** — that asymmetry is the argument. Predicted gain: ~10⁴–10⁵× on the per-step constant (survey §5); the cliff dissolves, it isn't softened. **Rejected**: (B) env semantics in the spec — discards the paid-for substitution metatheory bang already owns (CakeML never paid it, so its day-one envs prove nothing for us) and blurs invariant #4's spec/machine split; (C) explicit-substitution calculus λσ — imports a known SN-failure hazard to solve a perf problem envs solve cleanly; (E) hash-consing — shares subterms but the reducer still walks O(body) per step. **(D) thunk-sharing at the knot is DEFERRED as the fallback stopgap**, not rejected — named cost: memoized force breaks step-monotonicity, owing backward simulation (PureCake §5.4), so it is small–medium, not small; if A lands, skip D entirely.
- **Depends-on**: 0016 (the two-hop split this exploits), 0035 (annotated forward simulation — the bridge shape that absorbs the re-proof)
- **Relates-to**: #61 (the motivating measurement), 0073 §5 (refined: the perf hazard is per-step O(body), not deep-recursion fuel exhaustion; the fix is env-in-the-machine, not TCO), `docs/notes/envsem-survey.md` (the full design-space analysis this ADR lifts from), `docs/notes/hang-61-diagnosis.md` (the evidence)

## Status

Accepted (2026-07-10, operator ruling — "let's rule it out", the day after Stage-4 landed and
unblocked the same files). Implementation is the next verification-spine unit: env/closure
representation in `evalD` → re-derived machine → `evalD_agrees_source` as the substitution↔
environment correspondence (the PLFA `γ≈ₑσ` pattern) → Agree battery → flip `bang run`'s
default to the compiled engine (A1). Originally Proposed 2026-07-09.

- **Layer:** CalcVM machine layer (`evalD`, `AbstractMachine.lean`) + one bridge lemma
  (`evalD_agrees_source` re-based across the representation gap) + CLI default flip
  (`Main.lean`). The kernel `Source.eval`, `Spec.lean`, Soundness, both LRs, and Freshness
  are untouched by construction.

## Context

`bang run` on the dogfood JSON parser takes 16.85 s to parse `[1]`; both engines hang-shaped
on sibling nested `let rec` (#61). The diagnosis (`hang-61-diagnosis.md`) refuted term blowup
(elaboration is linear) and located the cost precisely: every reduction step rebuilds the whole
knot body via `Comp.subst` (~1 ms/step, ~10⁵–10⁶ nodes traversed per step). The literature is
unambiguous that environments+closures are the standard fix; the only genuine fork is **which
layer pays** — the spec or the derived machine. The survey (`envsem-survey.md`) prices five
options against bang's actual proof spine and finds the decisive parallel in PureCake: its
verified backend introduces environments as ONE IL-local pass below an unchanged substitution
spec, exactly the shape bang's two-hop architecture (ADR-0016) already provides. CompCert's
machine contrast confirms the same: bang's CalcVM already has the continuation stack and the
effect-state stores — it is missing only the variable environment.

## Decision

Option **A1** of the survey:

1. `evalD` (and the machine derived from it) gains a variable environment `ρ` and closure
   values; reduction becomes lookup instead of whole-body substitution. The effect stores are
   additively untouched.
2. `Source.eval` stays the substitution spec — slow, simple, verified, the oracle. It is
   allowed to be slow; it is a reference, not the hot path (invariant #7).
3. `evalD_agrees_source` becomes the substitution↔environment correspondence lemma, carrying
   the one new invariant: env/closure well-formedness + `γ≈ₑσ` agreement (PLFA `BigStep` is
   the mechanized template, incl. its warning that the statement must generalize from the
   empty env for the induction to fire).
4. `bang run` defaults to the compiled engine; the substitution oracle remains reachable
   (differential testing rides on it, unchanged).

**Residual, named honestly:** the oracle path stays O(body)-per-step. Acceptable under (2);
if dogfooding later needs a fast oracle too, option D's memoization can be added to
`Source.eval` (A2) — a separate, deferrable decision.

## Rejected alternatives

- **(B) Environments in the spec** (`Source.eval` becomes CEK/CESK): re-bases every
  `subst`-indexed proof (~1900 occurrences across 16 files). CakeML chose env-from-day-one
  and paid nothing — bang is not greenfield, so B *discards* a tax already paid. Also erodes
  invariant #4 (the machine is calculated FROM the spec; B makes the spec machine-shaped).
- **(C) Explicit-substitution calculus (λσ)**: first-class lazy substitutions defer the copy
  but import λσ's known failure of preservation-of-strong-normalization — a new metatheory
  hazard purchased to solve a problem environments solve without one.
- **(E) Term-graph / hash-consing**: shares identical subterms but the reducer still walks the
  body every step; fixes duplication, not the O(body) traversal that #61 measured.
- **(D) Thunk-sharing at the knot** — deferred fallback, not rejected: collapses the
  per-unfold re-copy at a narrower blast radius, but memoized force breaks step-count
  monotonicity, so the pass owes forward AND backward simulation (PureCake §5.4) on top of a
  reduction-relation change. If A proceeds, D buys nothing extra.

## Consequences

- #61 closes for real programs via the compiled default; the JSON dogfood's 16.85 s run is
  predicted to land in tens of ms (survey §5 — per-step constant drops from ~1 ms to
  ~10–40 ns lookup; step count is unchanged and was never the bug).
- The proof cost concentrates in one known-pattern bridge lemma instead of a spec-wide
  re-base; the substitution metatheory keeps earning.
- The Bahr–Hutton derivation gets re-run over the env-shaped `evalD` — the machine stays a
  calculated output (invariant #4), now landing on the CESK point the derivation literature
  already maps (Van Horn–Might, Ager et al.).
- Sequencing: implementation queues behind the #44 Stage-4 landing (same files:
  `AbstractMachine.lean`, the sim spine); ruling can precede it.
