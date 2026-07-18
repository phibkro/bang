# Moderator guide — stranger test 7

## Before recruitment/session

1. Recruit for task-relevant experience, not demographic stereotypes. Confirm the participant is
   unfamiliar with BANG and record only the minimum relevant background they consent to share.
2. Explain purpose, duration (about 45–60 minutes), voluntary participation, what will be observed, how
   notes/recordings will be stored, retention/deletion, anonymization, and any compensation.
3. Obtain explicit consent separately for screen/terminal recording, audio, quotation, and publication
   of a sanitized trace. Default each optional item to **no**. The participant may pause or withdraw.
4. Do not place identity, contact details, unredacted recordings, or unrelated personal context in git.
5. Prepare a clean checkout at `fe01ad60`; build once; verify the exact binary; prepare a separate
   disposable workspace with empty history; keep `score-key.md` inaccessible to the participant.

Suggested opening:

> We are testing BANG and its documentation, not you. Please work naturally and briefly narrate what you
> expect, do, and observe. I will mostly stay quiet. You can stop or withdraw at any time. Some tasks may
> expose unfinished or confusing behavior; that is useful product evidence.

## During the session

- Give only `participant-packet.md` and the allowed source boundary.
- Record chronological actions and product output. Ask neutral prompts such as “What are you looking for?”
  or “What tells you that worked?” Avoid “Did you see…?”, syntax, command, document, or expected-result hints.
- If the participant asks for product help, first ask what they would normally try. If you later provide a
  hint, record its exact content and mark the task/session assisted.
- Separate infrastructure remediation from product assistance. Preserve errors, detours, recovery, and
  abandonment rather than cleaning the trace.
- Do not request hidden chain-of-thought. Short expectations, decisions, and observable explanations are
  sufficient.

## After the session

1. Confirm whether the participant still consents to the agreed retained artifacts and quotations.
2. Copy observations into `session-notes-template.md`; keep self-report separate from observed behavior.
3. Redact secrets and personal data without rewriting product behavior. Mark contamination/intervention.
4. An adjudicator scores against `score-key.md`, replays every claimed defect, and searches for accepted
   alternate routes.
5. Compare with round 6: issues found by both, agent-only hypotheses, human-only issues, severity/route/
   recovery differences. Report denominators literally.
