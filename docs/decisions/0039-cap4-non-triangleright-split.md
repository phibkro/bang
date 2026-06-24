# 0039 — ◊4 split: LR foundation lands for the non-▷ fragment; the ▷-subsystem (μ + resumptive handlers) → ◊4.5

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: ◊4 split — the LR foundation lands sorry-free for the non-▷ fragment; the cohesive ▷-subsystem (μ · `up` · resumptive handlers) defers to ◊4.5.
- **Depends-on**: 0038, 0036, 0034, 0033, 0035, 0030, 0016

- **Layer:** P (LR / proof-architecture)
- **Status:** Accepted (user-authorized scope decision, 2026-06-24)
- **Depends on:** 0038, 0036, 0034, 0033, 0035, 0030, 0016

## Context

The ◊4 LR is proven sorry-free and gate-clean for the **non-▷ fragment** — pure CBPV + functions
(the arrow clause, ADR-0038) + non-recursive ADTs (sum/product) + **throws** effects. The remaining
cases of `lr_fundamental` form a **cohesive ▷-subsystem** that all need the *later*-modality (▷)
step-index machinery:

- **μ recursion observation** — `fold`/`unfold` (`Vrel (n+1) (mu A)` drops the payload to index `n`;
  the reduct must be observed at the dropped index).
- **`up`** (performing an operation) — under a handling stack, observed via the resume clause's
  Crel-at-the-next-index.
- **resumptive handlers** — `handleState` / `handleTransaction` (RESUME = reinstall the frame +
  continue at the next index).

(Only `throws` — zero-shot abort, no resume — is ▷-free, and it closed via the same-M angle: the
caught op is consumed *inside* the body's biorthogonal run, needing no `Krel` handled-op clause.)

## The build-confirmed root cause (the keeper)

Our `Vrel`/`Crel`/`Krel`/`Srel` are plain `Nat → Prop`. Biernacki's μ + resume soundness relies on the
**IxFree `∀k≤n` Kripke-monotone reading** (the relations monotone in *both* directions by
construction). Our phrasing structurally lacks it, and **no uniform monotonicity can be retrofitted**:

- `Krel`'s return-half has `Vrel` **covariant** (needs `Vrel`-down), but `Srel`'s resume clause
  (`∀u, Vrel n u → Crel n`) has `Vrel` **contravariant** (needs `Vrel`-up). Same relations, opposite
  required directions ⇒ no uniform monotonicity (build-confirmed: the `*_mono` block reverts as false).
- The ▷-anti-reduction `crel_unfold` needs (Biernacki Lemma 1(3)) requires `Krel`-**down**, but ours is
  `Krel`-**up**.
- `crel_unfold` *spending the index* (option a, `Vrel (n+1) (mu A) → Crel n`) **closes as a lemma**
  (`7f1bb24`) but **does not compose** into `crel_fund`: the IH supplies `Vrel n`, the lemma needs
  `Vrel (n+1)` — bridging is `Vrel`-up / `EnvRel`-up, false at μ.

Cross-checked against `ahmed-esop06` Fig 3: Ahmed's relations are `∀i≤j` downward-closed AND his
computation relation is *direct step-counting* (not biorthogonal) — which is what makes the μ step-cost
compose. To have **both** biorthogonal-effects (Biernacki) **and** iso-recursive-μ, the relations need
the IxFree `∀k≤n` wrapping we omitted in Phase A.

## Decision

**Split ◊4.**

- **◊4 (lands now) — LR foundation, non-▷ fragment.** `lr_fundamental` proven for all value cases +
  `ret`/`letC`/`force`/`case`/`split`/`lam`/`app`/`handleThrows`; `lr_sound`/`zero_usage` for the
  non-▷ fragment. `Audit.lean`: `sorryAx` on these comes **only** from the documented ▷-subsystem; ◊2
  (`no_accidental_handling` 0-axiom, STD block trusted-three) and ◊3 (CalcVM trusted-three) held
  throughout. The deferred cases are documented sorrys pointing here.
- **◊4.5 (focused follow-up PATH) — the ▷-subsystem.** Re-phrase `Crel`/`Krel`/`Srel` with the IxFree
  `∀k≤n` Kripke-monotone reading (designed in from the start, not retrofitted), then close `fold`/
  `unfold` + `up` + `handleState`/`handleTransaction`. `crel_unfold` (option a), `krel_appF_intro`, and
  all the frame/closedness infra carry over unchanged.

## Why (over the alternative)

Re-phrasing all four relations Kripke-style *this late* re-ripples the **entire** proven-green spine
(`crel_ret`/`force`/`letC`/`case`/`split`/`lam`/`app`, `krel_letF`/`krel_appF_intro`, eff-mono) — high
regression risk for a milestone that is otherwise done. The ▷-subsystem is **cohesive** (one
relation-design pass), so it warrants its own focused unit with the Kripke phrasing built in, rather
than a retrofit. The non-▷ spine is the bulk of ◊4 and is gate-clean. This also matches v1 reality:
`throws` is the primary v1 handler; resumptive STM is ADR-0030 (concurrency-deferred) territory.

## Honest scope note

The deferred fragment is **not a corner case** — it is the resumptive-effects + recursive-data
subsystem (state, STM, reactive, recursive ADTs), which the v1 product rungs 1/3/4 and the μ-using
rung-2 Stack exercise. ◊4.5 is therefore the **next unit**, not a someday-maybe. The honest ◊4 claim
is: *the LR foundation is proven for the pure-CBPV + functions + non-recursive-ADT + exceptions core;
the resumptive/recursive half is a build-confirmed, well-scoped ◊4.5.*

## Rejected alternatives

1. **Global Kripke re-ripple now (option a).** Why not: re-verifies every proven core under the new
   relation shape this late — high regression risk; a retrofit rather than a clean design. Reserved as
   the ◊4.5 *method* (done properly, designed-in).
2. **Localized bespoke `crel_unfold` anti-reduction (option b).** Why not: **build-confirmed it does not
   compose** (`crel_fund`'s unfold case needs `Vrel`-up / `Krel`-down, which the localized form cannot
   phrase around without the Kripke wrapping).

## Revisit if

- ◊4.5 begins (the IxFree `∀k≤n` re-phrase) — this ADR is its problem statement.
- A cleaner non-Kripke construction is found that closes μ + resume without re-rippling the spine.

_Both pure forms and option (a)/(b) were build-confirmed, not assumed — `crel_unfold(a)` banked at
`7f1bb24`, `handleThrows` closed ▷-free at `7b1e7dd`. The ▷-free boundary is where the source draws the
honest line._
