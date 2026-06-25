# 0051 — The CalcReify → Bahr–Hutton 2022 monadic recast is NO-GO (renames, does not dissolve)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Recasting CalcReify's fuel-indexed forward bisimulation into the Bahr–Hutton 2022 *Monadic Compiler Calculation* frame (partiality/`Delay` monad + step-indexed strong bisimilarity) does NOT dissolve the open `perf_outcome_mono` gate — it RENAMES it. The 2022 frame gets its key monotonicity (`~idown`) FREE from coinduction; bang's index is EAGER fuel, so the matching obligation is the *opposite* direction (upward, `f ≤ f' ⇒ outcome preserved`), must be EARNED, and the deep case (a performing resumed body under `handleC`, deep re-handling) is a genuine bisimulation knot the single-monad paper never confronts. The shallow leg is already `bind_mono` (the paper's `bind-cong` specialised to the `ret` leg — bang has it). No usable coinductive `Delay`/`Partial` exists in Mathlib (only propositional `Part`/`PFun`); a faithful port is prohibitive infra for zero buy on the gate. **Keep bang's eager `Comp` + `Nat` fuel + `RelV`.** Re-open ONLY if genuine divergence (the Div fragment) enters CalcReify. Bonus: `perf_outcome_mono` was never a Lean statement (only a doc-name in 0015 / k2-playbook / a `CalcReifySim` comment); formalized for the first time in the spike (`scratch/MonadicRecast.lean`, `PerfOutcomeMono`).
- **Amends**: 0015
- **Depends-on**: 0015, 0016

## Status
Accepted (2026-06-25, feasibility spike + operator ruling "yes keep"). This closes the question
"should CalcReify adopt the BH2022 monadic frame to discharge `perf_outcome_mono`?" — for the v1
**total** fragment. It is a decided NO-GO with an explicit, narrow re-open condition, not a
permanent ban.

## Context

The CalcReify track (ADR-0015) verifies the calculated machine against a reference `eval` via a
**fuel-indexed forward bisimulation** (`RelV : Nat → Value → Entry → Prop`). Its one named-but-open
gate, `perf_outcome_mono` ("reference perf-outcome fuel-monotonicity", k2-playbook 523–526), is a
*fuel-monotone logical relation on `Comp`, not a simple equality*. It was only ever a **doc-name** —
never a Lean `theorem`/`sorry` (verified by grep: `0015:191`, `k2-calculation-playbook.md:523`,
`CalcReifySim.lean:1358` comment).

Hypothesis (the spike): bang's source is effectful (algebraic effect rows) while its calculation
method is Bahr–Hutton **2015** (pure, stack-based, converging-only); the **2022** *Monadic Compiler
Calculation* paper formalizes divergence + bisimulation with a partiality (`Delay`) monad + strong
bisimilarity, and might make `perf_outcome_mono` an instance of a free monadic property
(monotonicity-in-index / `bind-cong`).

## Decision

**NO-GO.** Build-grounded, elaborated in `scratch/MonadicRecast.lean` (against the real, green
`CalcReifyRef`/`CalcReifySim` deps — not stubs):

- **Shallow half is already free.** `shallow_is_bind_mono` proves the `ret` leg of upward
  monotonicity is *literally* `bind_mono` (the paper's `bind-cong` specialised). Axiom-clean.
- **Deep half is a recursive knot, not a `bind-cong` instance.** `deep_step_recurses` makes the
  circularity elaborate: a performing resumed body under `handleC fuel (k w) clause cEnv` (deep
  re-handling) lands back on `perf_outcome_mono` one handler-depth down. `bind-cong` congruences
  over a *given* bisimilarity; here the bisimilarity at depth `n` is exactly what is being
  established, so it cannot discharge it.

Root cause: the 2022 frame's free `~idown` comes from **coinduction** (`later` is productive; fuel
is not a resource you exhaust). bang's `Comp` is **eager + fuel-exhausting** (`eval 0 _ _ = .stuck`),
so raising fuel genuinely changes outcomes and you must *prove* it preserves real ones. The
coinductive frame **defines the obligation away rather than proving it** — net buy on the gate: zero.

**Keep bang's eager `Comp` + `Nat` fuel + `RelV`.** Prove `perf_outcome_mono` by fuel induction
when ◊5 needs it (`handleC fuel (k w)` is structurally decreasing on fuel — earned, not free, not
blocking).

## Rejected alternatives

- **Adopt the BH2022 monadic frame for CalcReify (the spike's hypothesis).** Rejected: renames, does
  not dissolve (above).
- **Build a coinductive `Delay`/`Partial` substrate in Lean** to get `~idown` for free. Rejected for
  v1: Mathlib has only *propositional* `Part`/`PFun` (no step index, no strong bisim). A faithful
  port = building coinductive `Partial` + sized/step-indexed strong bisimilarity + `~idown`/`bind-cong`
  — substantial infra, prohibitive for zero gate-buy. This is the *larger, separate* question, parked.
- **Adopt the Pickard–Hutton 2021 dependently-typed calculation style.** Orthogonal to the gate
  (`perf_outcome_mono` is *semantic* fuel-monotonicity, not a typing invariant). Mild yes as
  *ergonomics* later if the typed surface stabilizes; NOT a route to the gate.
- **The graded-monad generalization** (single monad → bang's graded effect lattice). Out of scope —
  genuinely unbounded research; the 2022 paper uses a single monad with effects inline.

## Re-open trigger (narrow, explicit)

Re-open this spike **iff genuine divergence (general recursion / loops — the Div fragment) enters
the CalcReify track.** Then fuel exhaustion stops being a bookkeeping artifact and becomes real
non-termination the coinductive `Partial` models natively; `~idown` + productivity would replace the
fuel-monotonicity bookkeeping wholesale, and the frame may then dissolve what it currently can't.
bang's v1 fragment is **total** (skeleton-bounded firing), so this does not apply now.

## Evidence

- `docs/notes/monadic-recast-spike-findings.md` — the full spike findings (mapping table, build state,
  per-section detail).
- `scratch/MonadicRecast.lean` — the elaborated spike: `PerfOutcomeMono` (first formalization),
  `shallow_is_bind_mono` (axiom-clean), `deep_step_recurses` (the visible circularity, one deliberate
  `sorry`). Unwired (no module imports it) → inert to the build.
