---
name: agentic-user-testing
description: Plan, run, and analyse blinded task-based usability inspections with LLM agents, preserving reproducible traces and calibrated claim boundaries. Use when Codex needs to pretest a user study, inspect a CLI/API/developer workflow, probe documentation findability or error recovery, compare product revisions, or prepare high-value hypotheses for later human research.
---

# Agentic User Testing

Use LLM agents as reproducible usability inspectors and study-rehearsal participants. Do not present
their output as human validation unless the target users are themselves agents.

Read `references/method-selection.md` before choosing the method. Read
`references/protocol.md` before writing a study packet or scoring sessions.

## Set the claim boundary

State one of these labels at the top of every study:

- **Agent usability test** — agents are an actual target population.
- **Agentic usability inspection** — agents exercise a real interface and surface issue hypotheses.
- **Synthetic study rehearsal** — agents test the research tasks, scoring, and environment before humans.

Never use synthetic ease, confidence, preference, emotion, adoption, demographic, or satisfaction
responses as evidence about humans. Never treat repeated samples from one model as independent people.

## Separate the roles

Keep four roles logically separate. Use separate contexts when tools permit it.

1. **Designer**: define the decision, research questions, participants, neutral tasks, stopping rules,
   source boundary, and score key before sessions.
2. **Participant**: receive only a profile, starting state, permitted public surface, and task packet.
   Do not reveal design intent, expected route, internal implementation, success criteria, or known bugs.
3. **Moderator/recorder**: give the same neutral prompts, enforce intervention rules, and retain the full
   chronological trace. Do not teach unless the predeclared assistance threshold is reached.
4. **Adjudicator**: score from the trace and machine state, not participant self-report. Separate
   observation, interpretation, and recommendation.

Do not allow the designer's pilot session to count as evidence. Mark any session with leaked context as
contaminated and use it only to improve the packet.

## Run the workflow

### 1. Frame the study

Write the product decision the study may change. Turn assumptions into research questions. Define the
target user and context narrowly enough that tasks can be realistic. Copy `assets/study-plan.md` and
complete it before launching participants.

Freeze and record:

- repository revision, build, configuration, and starting data;
- participant source boundary and forbidden sources;
- model/provider/version when available;
- success, partial success, failure, abandonment, intervention, and stopping rules;
- objective output or machine-state oracle for each task.

Rebuild the tested artifact from the frozen revision. A stale binary invalidates the session.

### 2. Design neutral tasks

Copy `assets/task-packet.md`. Give a believable goal, not a sequence of interface actions. Avoid product
terms that reveal where to click, which command to run, or which syntax to type. Include at least:

- one orientation or discovery task;
- one representative end-to-end task;
- one mistake-and-recovery task;
- one transfer task that changes a detail beyond the example.

Keep the score key outside the participant packet. Pilot the packet once and revise ambiguous wording.

### 3. Launch independent sessions

Use fresh contexts and isolated workspaces. Prefer several expertise profiles and more than one model or
provider when available. Change only one study variable when comparing revisions.

Give each participant the same frozen packet plus its assigned profile. Instruct it to act through the
real interface, keep a chronological action/output trace, avoid internal sources, and stop according to
the packet. Ask for concise expectations and observations, not hidden chain-of-thought. Do not ask it to
imagine what a user might do when it can actually perform the task.

Treat model/provider diversity as triangulation, not population sampling. Record failures and successful
detours as carefully as direct success.

### 4. Preserve evidence

Copy `assets/session-report.json` for each session. Preserve commands, relevant output, files consulted,
edits, errors, recoveries, assistance, final state, and contamination notes. Redact secrets and personal
data, but do not clean up the behavioral trace.

Store participant self-report separately from observed behavior. Self-report can suggest a follow-up
question; it cannot override the trace.

### 5. Score and adjudicate

Score task outcomes against the frozen oracle. Measure effectiveness and efficiency using observable
fields: completion, correctness, false success, errors, actions, detours, interventions, and recovery.
Do not calculate SUS or interpret an LLM's ease rating as satisfaction.

Run `scripts/summarize_sessions.py <session-dir>` to validate session JSON and aggregate task outcomes
and repeated finding keys. Have an adjudicator inspect the raw trace for every high-severity result.

Prioritise a finding when it is:

- mechanically confirmed and severe, even in one session;
- independently reproduced across sessions; or
- an ambiguity in the study instrument that would invalidate human sessions.

Keep one-off, persona-dependent, or introspective claims labelled as hypotheses.

Assign an evidence grade separately from severity: deterministic replay (`A`), cross-session or
cross-provider replication (`B`), single-instrument hypothesis (`C`), or a claim that requires humans
(`D`).

### 6. Hand off to humans and iterate

Turn surviving findings into product changes or human-research questions. For human usability claims,
recruit actual or likely users and use the corresponding traditional method in
`references/method-selection.md`. Compare agent and human issue detection over time to learn where the
instrument is calibrated and where it is blind.

After a product change, replay the frozen tasks, then add a transfer task so success does not merely
reflect memorising the original path.

## Report the result

Include:

1. claim boundary and decision;
2. frozen target and participant source boundary;
3. task and profile matrix;
4. per-task observed outcomes;
5. findings with raw evidence, replication count, severity, and alternative explanation;
6. contaminated or excluded sessions;
7. changes recommended now;
8. questions reserved for human research;
9. exact prompts, model metadata, and artifact locations needed to reproduce the study.

Avoid a single synthetic “usability score.” It hides which tasks failed and falsely resembles a human
population estimate.

## Use the bundled resources

- `references/method-selection.md` — traditional methods, agent-fit matrix, and validity limits.
- `references/protocol.md` — task design, metrics, severity, contamination, and adjudication details.
- `assets/study-plan.md` — reusable study plan and score-key template.
- `assets/task-packet.md` — participant-safe packet template.
- `assets/session-report.json` — trace and outcome schema.
- `scripts/summarize_sessions.py` — deterministic validator and aggregate report generator.
