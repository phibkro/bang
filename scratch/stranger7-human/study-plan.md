# Study plan — repaired BANG resource-contract journey

- **Claim boundary**: moderated formative usability test with actual unfamiliar developers.
- **Decision this study may change**: whether the repaired resource-contract journey is ready to hand
  off to the spreadsheet/reactivity project, or which smallest correction must land first.
- **Owner**: operator recruits/moderates; Codex prepares artifacts and adjudicates reproducible product
  findings.
- **Frozen target**: commit `fe01ad60`, built from a clean checkout with its own `.lake/build/bin/bang`.
- **Target user/context**: first a competent developer unfamiliar with BANG and preferably Lean; then,
  when available, a Lean/proof developer unfamiliar with BANG as a distinct route.
- **Research questions**: can they discover the semantic-description model, establish evidence, recover
  from B018, transfer the model across realizations, inspect grade-0 output, and identify invalidity from
  the machine card without internal knowledge or hints?
- **Explicit non-claims**: one or two sessions do not estimate population usability, satisfaction,
  adoption, accessibility, or issue prevalence; agentic round 6 is comparison data, not a human sample.

## Source boundary

- **May use**: `README.md`, `ONBOARDING.md`, `docs/reference/language.md`, `examples/**`, and public CLI
  help/explain output from the pinned build.
- **Must not use**: implementation, `CLAUDE.md`, `CONTEXT.md`, `ROADMAP.md`, `paths/**`, `docs/notes/**`,
  `docs/decisions/**`, `.claude/**`, `scratch/**`, git history, score key, known findings, or prior traces.
- **Starting state**: clean/disposable pinned checkout, dependencies already built, terminal at repository
  root, and no command history or generated participant artifacts.
- **Isolation/reset**: participant edits only a fresh disposable copy; restore from the pinned checkout
  before every session.

## Session matrix

| Session | Task-relevant profile | Strategy/constraint | Status |
|---|---|---|---|
| H01 | non-Lean developer unfamiliar with BANG | natural strategy; no route hints | recruitment needed |
| H02 | Lean/proof developer unfamiliar with BANG | natural strategy; no route hints | optional second route |

## Intervention and stopping policy

- Ask the participant to narrate short expectations, actions, and observations—not private reasoning.
- The moderator may clarify task wording or resolve infrastructure failures, but may not name a command,
  syntax, document, expected result, concept, or solution route.
- A product hint makes the task assisted; record it and continue only if the participant wishes. The
  session then cannot satisfy the unassisted gate.
- Stop a task after 10 minutes or 20 product-facing actions without progress. Stop the whole session on
  request, consent withdrawal, unsafe/sensitive output, or an unrecoverable infrastructure failure.
- Infrastructure-only blockage is `blocked`, not product failure; rebuild/reset and schedule a successor
  session without relabelling the blocked run.

## Outcomes and analysis

- Outcomes: `success`, `partial`, `failure`, `blocked`, or `excluded`; also record first attempt,
  actions, errors, detours, interventions, recovery, and real elapsed time.
- Adjudicate every finding against the pinned product and an accepted alternate route before severity.
- Prioritize deterministic false success/blockage, independently reproduced friction, or an observation
  with high prospective regret. Keep human-only context and agent-only false positives visible.
- Commit only sanitized observation, interpretation, alternative explanation, disposition, and replay
  evidence; do not commit participant identity or unconsented recordings.
