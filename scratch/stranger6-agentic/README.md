# Stranger test 6 — agentic resource-contract study

This directory preserves the frozen instrument and raw session reports behind
`docs/notes/stranger-test-6.md`.

- `participant-packet.md` is the exact prompt-visible task packet.
- `score-key.md` was private from participants.
- `sessions/S00-pilot.json` records the excluded, context-contaminated pilot.
- `sessions/S01`–`S03` are independent fresh-context reports and structured summaries.

All sessions exercised commit `d48b7d33` (feature commit `4fef991e`) through the public CLI and user
documentation. They edited only disposable directories under `/tmp`. The study is an agentic usability
inspection for human-facing claims and a direct test of one coding-agent audience; it is not evidence of
human satisfaction, preference, adoption, or population behavior.

Validate and aggregate the structured reports with:

```sh
nix shell nixpkgs#python3 -c python3 \
  .claude/skills/agentic-user-testing/scripts/summarize_sessions.py \
  scratch/stranger6-agentic/sessions
```
