# Protocol and scoring reference

## Study unit

Define a study as one frozen product revision, task packet, source boundary, score key, and intervention
policy. A session is one participant agent in one fresh context and isolated workspace.

Do not silently change tasks between sessions. Version the packet when a pilot reveals ambiguity and
exclude earlier sessions from the new study.

## Participant profiles

Vary task-relevant knowledge and behavior, not demographic stereotypes. Useful dimensions include:

- domain expertise: novice, adjacent expert, expert;
- tool familiarity: first-time CLI user, experienced terminal user, automation author;
- strategy: documentation-first, example-first, help-first, experiment-first;
- constraints: time pressure, minimal dependencies, machine-readable output requirement;
- recovery tendency: persistent debugger, quick abandoner, asks for help at a fixed threshold.

Do not infer that a profile represents people who share a demographic label.

For a small exploratory pass, use at least three fresh sessions with meaningfully different strategies.
For a stronger synthetic replication, cross three relevant profiles with two model/provider families and
two fresh runs, then report the clustering rather than calling the twelve runs twelve users. Counterbalance
task order when tasks are independent; retain a fixed logical order when one task creates another's state.

## Task construction

For each task, keep two separate blocks:

**Participant block**

- realistic context and goal;
- starting state and permitted interface;
- deliverable;
- stop condition.

**Score-key block**

- observable success state;
- accepted alternate routes;
- partial and false-success conditions;
- allowed assistance and timeout/action threshold;
- cleanup or state-reset procedure.

Avoid naming commands, navigation labels, syntax, files, or concepts whose discovery is under test.

When simulator reliability itself matters, include a known-solvable control, a known-failing control, and
an impossible or underspecified task. These expose hallucinated success, excessive cooperation, and
unearned confidence. Keep controls out of ordinary product scoring.

## Recorded evidence

Capture every action in order:

- command or interface action;
- relevant output and exit status;
- public document or help surface consulted;
- file change or state transition;
- participant prediction before action when semantic comprehension matters;
- error, detour, recovery, intervention, and abandonment;
- final artifact and machine-state oracle.

Record model/provider/version, prompt hash or exact prompt, revision, build identity, timestamps, and
contamination notes when available. Unknown metadata is `null`, never guessed.

Request short predictions and observable explanations. Do not request or retain private chain-of-thought.

## Task outcomes

Use these categorical outcomes:

- `success`: oracle satisfied without prohibited help;
- `partial`: a declared subset of the goal is correct;
- `failure`: attempt ends without satisfying the oracle;
- `blocked`: environment or infrastructure, rather than product interaction, prevents a fair attempt;
- `excluded`: contamination or protocol deviation invalidates the session.

Record `first_attempt`, `actions`, `errors`, `detours`, `interventions`, and `recovered`. Counts describe
the trace; they are not human time or cognitive-load measures.

## Finding severity

Rate impact before ease of fixing:

- `critical`: safety/data loss or the primary journey is impossible with no recovery;
- `high`: representative journey blocked, false success, or documentation teaches a broken path;
- `medium`: substantial detour, opaque recovery, or important concept misunderstanding;
- `low`: local friction or cosmetic ambiguity with an obvious recovery;
- `instrument`: task wording, environment, or scoring flaw rather than a product issue.

For each finding, preserve:

1. observation: what happened in the trace;
2. evidence: command/output/action references;
3. interpretation: why it may have happened;
4. alternative explanation;
5. replication count and involved model families;
6. recommended next test or product change.

An objective single-session blocker may outrank a repeated papercut. Repetition increases confidence,
not necessarily severity.

Assign an independent evidence grade:

- `A`: deterministic defect confirmed by replay and a machine oracle;
- `B`: synthetic signal reproduced across independent sessions or provider families;
- `C`: one model/session's friction hypothesis;
- `D`: preference, emotion, identity, lived experience, prevalence, or adoption claim reserved for humans.

## Contamination rules

Exclude a session from evidence when the participant saw:

- expected commands or solution path;
- score key or machine oracle;
- implementation notes or internal architecture outside the source boundary;
- known findings or prior session reports;
- artifacts left by another participant;
- a context summary containing the design intent or answer.

Use contaminated sessions as pilots. Record the leak instead of pretending independence.

## Adjudication

Have a separate agent or human review raw traces without participant conclusions. Re-run every claimed
product defect directly. Search for an accepted alternate route before rating a failure. Distinguish:

- product failure;
- documentation/findability failure;
- participant strategy or model failure;
- infrastructure failure;
- study-instrument failure.

Report both convergence and divergence. Convergence across independent sessions strengthens a finding;
divergence often reveals strategy sensitivity, hidden context, or an ambiguous task.

## Human calibration

For claims about humans, run corresponding sessions with actual or likely users. Keep the task goal and
oracle comparable while using human-appropriate consent and facilitation. Track:

- issues found by both agents and humans;
- agent-only hypotheses rejected by humans;
- human-only issues missed by agents;
- severity agreement;
- route and recovery differences.

Use that calibration history to narrow future agent claims. Do not use it to claim that a model has become
a representative population sample.
