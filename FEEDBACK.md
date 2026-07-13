# Contributor feedback

**Summary:** Open, actionable bugs, DX friction, and improvement opportunities discovered while executing Plan 014.

| ID | Finding | Evidence | Impact |
|---|---|---|---|
| F-010 | Plan 014 duplicated volatile integration state in its plan-level and Phase 1 status lines; the copies drifted (“not yet committed” after commit, and F-009 omitted from the closed-fix range). | `plans/014-developer-reference-onboarding-system.md:3`, `:63`; `git show 65e53ed4^:FEEDBACK.md`; branch head `65e53ed4`. | A contributor resuming the plan can misread banked work as local-only and rediscover an already-closed public-link fix. |
| F-011 | `check-refs.py` resolved references against any path present in the working tree, so untracked research files and ephemeral `/tmp` outputs made local `just verify` pass while the clean CI checkout failed five references. | `git show 65e53ed4:tools/check-refs.py`; Verify run `29262315569`; deliberately untracked `research/`; `/tmp/lint-out.txt`. | A dirty developer tree can certify committed content that fails in CI, violating the gate-on-clean-commit contract. |
| F-012 | Reference classification ran before stripping anchors and line suffixes, so stale targets such as `docs/<missing>.md#section` and `tools/<missing>.py:42` were silently ignored; the first fix also skipped every absolute path rather than only ephemeral `/tmp` artifacts. | `tools/check-refs.py:is_pathish`, `normalize`; adversarial review poles. | The checker can report green while path-shaped references are broken. |
| F-013 | The first tracked-only projection mixed index membership with worktree existence, admitting intent-to-add files and omitting unstaged-deleted Markdown. | `git add -N` and `git ls-files --deleted` review fixtures; `tools/check-refs.py:tracked_paths`. | Local fitness can still disagree with the next clean checkout in two ordinary dirty-tree states. |
| F-014 | The new self-test exercised only synthetic sets and was invoked as a second indistinguishable fitness leg. | `tools/check-refs.py:self_test`; duplicate `check-refs.py` entries in generated `.claude/codebase-maintenance.md`. | The exact Git/source-scan regression was untested while gate documentation became misleading. |
| F-015 | Adding argparse replaced the checker's positional repository-root interface with `--root`. | `python3 tools/check-refs.py /tmp/lang-bang-doc-research` exits 2 on the first draft. | Existing wrappers or contributors using the prior interface break unnecessarily. |

## Lifecycle

1. Record a finding when it is observed, with a concrete failure scenario and source evidence.
2. Convert it into a bounded fix between documentation phases; do not carry known friction into the next phase silently.
3. Bind the fix to the strongest available gate—test, generated check, type, or CI rule.
4. Delete the finding once the real journey and relevant gates verify the fix. Git and the PR retain the history.
