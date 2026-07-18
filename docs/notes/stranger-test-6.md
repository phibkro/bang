<!-- note-status: active -->
<!-- describes: none -->
# Stranger test — round 6: agentic resource-contract inspection (2026-07-18)

> The first explicit agentic-usability round: one contaminated pilot designs the instrument, then three
> fresh-context participants receive the same neutral task packet, public-source boundary, disposable
> workspace, and objective score key. It tests the completed resource-contract tracer without pretending
> that model output is human validation.

## Claim boundary

This is an **agentic usability inspection** for claims about human newcomers. It is also direct but
single-provider evidence about one real audience BANG cares about—coding agents. It does not measure
human satisfaction, preference, adoption, lived context, accessibility, or population behavior.

There is deliberately no synthetic usability score. The useful evidence is task-level behavior,
machine-state oracles, route differences, and reproducible defects.

The reusable procedure is `.claude/skills/agentic-user-testing/`. The exact frozen instrument, private
score key, structured session data, and raw traces are in `scratch/stranger6-agentic/`.

## Study design

- **Target**: `d48b7d33`, including resource-contract feature commit `4fef991e`, using the warm built
  binary from that revision.
- **Permitted surface**: `README.md`, `ONBOARDING.md`, `docs/reference/language.md`, `examples/**`, and
  CLI help/explain output.
- **Forbidden surface**: implementation, internal notes/ADRs/paths, git history, prior findings, score
  key, and other participant artifacts.
- **Profiles**: documentation-first functional programmer; help-first CLI automation engineer;
  example-first language practitioner.
- **Isolation**: fresh agent context plus a distinct `/tmp` workspace for each participant; product tree
  read-only.
- **Roles**: lead designed and piloted; participant agents acted through the real CLI; raw reports
  recorded their traces; lead adjudicated every product finding against the binary.
- **Exclusion**: the pilot inherited answer-bearing project context and is recorded as contaminated.
  It shaped the packet but contributes no session counts.
- **Limitation**: all three included participants came from one provider/model family. The profiles vary
  strategy, not independent human populations or model families.

The six tasks tested orientation, baseline evidence, B018 refusal/recovery, realization transfer,
concrete grade-0 emission, and invalid-card interpretation. Tasks stated goals rather than commands;
the private key fixed success before the fresh sessions began.

## Result

All three fresh participants completed all six tasks with no moderator interventions.

| Task | Success | Actions | Errors | Detours | What the task established |
|---|---:|---:|---:|---:|---|
| orient from public surface | 3/3 | 9 | 0 | 0 | every route found the example and explained descriptions before realizations |
| establish baseline evidence | 3/3 | 15 | 0 | 0 | result `7`, laws `2/2`, and the joined card were independently recovered |
| duplicate and recover | 3/3 | 17 | 5 | 1 | all reached `[omega]`; JSON help was shorter than the human-output route |
| swap realization | 3/3 | 15 | 0 | 0 | all predicted/observed `-7`, retained laws, and noticed identifier churn |
| inspect grade-0 emission | 3/3 | 8 | 1 | 2 | all found construct+drop of `99` and no retained environment cell |
| judge invalid card | 3/3 | 3 | 0 | 0 | all independently rejected top-level `ok` as a validity gate |

Raw denominators matter: this is three fresh runs, not “three representative users.”

## Follow-through (2026-07-18)

The evidence-integrity slice prompted by this study has repaired F1–F4 without rewriting the
historical observations below:

- contract cards now separate operation success (`ok`) from program validity (`subjectValid`);
- resolver provenance supplies stable contract, realization, and law-instance IDs while local
  display labels remain concise;
- resolved human and JSON B018 diagnostics retain the code and locate an entry-file quantity
  annotation when available, while imported-only failures remain honestly unlocated;
- the example now uses the already-built binary for quiet repeated runs.

F5 remains an explicit option-preserving follow-up: the law renderer does not currently receive an
observed result, so enriching it here would widen the witness pipeline rather than repair a local
presentation seam. The frozen tasks and new regression gates are replayed before this path closes.

## Findings

### F1 — The contract card can report `ok:true` for an invalid program. **[high · A · 3/3]**

Every participant queried the twice-used `[1]` program and observed process exit `0` plus top-level
`"ok":true`, while only nested `evidence.typeChecked:false` established invalidity. The reference
documents that `ok` means the query operation ran, so this is not a hidden implementation mismatch.
It is still a hazardous schema default: ordinary automation commonly gates on exit success and a
top-level `ok` field.

**Next slice**: add an unambiguous top-level subject-validity field to the contract card (preserving
operation success separately), gate it on both accepted and refused programs, and document the machine
consumer rule beside the schema.

### F2 — Realization identities churn when only the installed realization changes. **[medium · A · 3/3]**

The Identity card serializes `Identity` and `Permit_Negate`; the Negate card serializes
`Permit_Identity` and `Negate`. The underlying module declarations are unchanged, yet both realization
names and law-instance names move because the selected import receives the short resolver alias.

This matters precisely because `query contract` is the machine-readable seam for interchangeable
realizations. A consumer should not have to infer declaration identity from selection-dependent display
names.

**Next slice**: retain stable fully qualified IDs for contracts, realizations, and law instances, then
represent local/selected display names separately. Add a swap test asserting stable ID sets.

### F3 — B018 recovery quality depends on output mode and loses location. **[medium · A]**

The help-first and docs-first routes used `check --json`, retained `explainCode:"B018"`, and recovered
directly with `bang explain B018`. The example-first route used human-readable `check` on the same
resolved multi-file shape; it received the useful quantity mismatch but no `error[B018]`, so it had to
search the long reference. Direct adjudication confirmed the split: the single-file refusal fixture
prints `error[B018]`, resolved multi-file human output drops the code, and resolved JSON retains it.

Both structured sessions also received `span:null`. The CLI documents missing resolved multi-file spans,
but the public diagnostic table says stable codes appear in `bang check` output; that claim is false for
this route.

**Next slice**: preserve `B018` through resolved human formatting first; then carry the `use [q]` source
location through resolver-aware checking so both human and structured diagnostics can navigate to it.

### F4 — The example's literal `lake exe bang` commands replay 1,633 warning lines. **[medium · A · pilot/adjudicator]**

The excluded pilot followed `examples/resource-contract/README.md` literally and received 1,633 lines
(about 20k output tokens) before `ok` or `7`. The lead reproduced the exact count. The three frozen
sessions avoided it because the root README and task packet directed them to the already-built binary,
so this is an objective documented-route finding, not a replicated participant signal.

**Next slice**: make example commands use a quiet built-binary or wrapper path after the build step, or
stop Lake from replaying the library's warning backlog for routine CLI use.

### F5 — A zero-parameter law failure reports only `counterexample []`. **[low · A · pilot/adjudicator]**

Adding an `Offset` realization (`spend(n) => n + 1`) correctly fails `preserves_zero`, but the witness is
only `counterexample []`; it does not show the observed result or failed expression. The failure is sound
but thin to debug.

**Next slice**: include the evaluated law outcome (or expected/observed values where available) when a law
has no sampled parameters.

## What worked and should be preserved

- The public surface teaches the central semantic-description story well enough that all three routes
  reconstructed it without internal context.
- B018's structured code, wording, and explanation form a strong one-step recovery loop.
- The tiny example supports one coherent evidence chain: check, run, cross-realization law test, joined
  query, handler swap, refusal, recovery, and concrete WAT.
- Every participant predicted the Negate behavior correctly before running it. The contract/realization
  distinction transferred beyond rote command execution.
- Grade-0 erasure is not merely asserted: the emitted artifact let every participant verify preserved RHS
  evaluation and omitted environment retention.

## Method verdict

The effective agentic analogue is not a synthetic interview panel. It is a blinded, task-based usability
inspection with fresh contexts, frozen tasks, real interfaces, objective oracles, raw traces, and separate
adjudication. It is strongest for documentation discovery, CLI/API workflows, error recovery, semantic
prediction, machine-readable contracts, and regression replay. It is weakest for preference, emotion,
accessibility, adoption, real-world context, and population inference.

Convergence identified the query-schema and identity seams. Divergence identified the B018 presentation
split. A single score—or one agent asked to imagine three personas—would have hidden both.

## Human handoff remains the outer-loop gate

This round improves the instrument; it does not close the loop-audit's organic-user row. The next external
round should recruit at least one developer unfamiliar with Lean and one Lean/proof developer unfamiliar
with BANG, use the same goals without solution leakage, and compare human-only issues, agent-only false
positives, route differences, recovery, and time to first evidence. A coding-agent round from another
provider/model family would separately calibrate the agent-user audience.

The immediate implementation order is F1 → F2 → F3, replay this frozen packet, then put the repaired
slice in front of real outsiders. F4/F5 are bounded polish slices that can ride the same usability batch.

## Method sources

- ISO 9241-11 usability concepts: <https://www.iso.org/standard/63500.html>
- GOV.UK moderated task-testing procedure: <https://www.gov.uk/service-manual/user-research/using-moderated-usability-testing>
- UXAgent's human-study-pretesting framing: <https://arxiv.org/abs/2504.09407>
- Synthetic-participant systematic review (182 studies):
  <https://www.researchsquare.com/article/rs-9057643/v1>
- Task-dependent simulator calibration in SimulatorArena:
  <https://aclanthology.org/2025.emnlp-main.1786/>
