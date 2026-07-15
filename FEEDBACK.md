# Contributor feedback

**Summary:** Open, actionable bugs, DX friction, and improvement opportunities discovered while executing Plan 014.

## Open findings

| ID | Finding | Failure scenario | Evidence | Graduation gate |
|---|---|---|---|---|
| F1 | The P2.2 sibling fact schema duplicates the evidence vocabulary and inspects `example.schema.json` internals. | Integrating PR #156 after the shared `common.schema.json` migration can leave language facts on a parallel vocabulary or break their compatibility check despite both sibling PRs being green alone. | PR #156: [language schema](https://github.com/phibkro/bang/blob/6ed2e3159dfe4ead692fc00d8fde57972ebcf32a/docfacts/schema/language.schema.json) and [generator](https://github.com/phibkro/bang/blob/6ed2e3159dfe4ead692fc00d8fde57972ebcf32a/tools/docfacts_language.py); this branch: `docfacts/schema/common.schema.json`. | During sibling integration, migrate the language schema/tool to the shared common definition and run both P2.2 and P2.3 fact batteries. |

## Lifecycle

1. Record a finding when it is observed, with a concrete failure scenario and source evidence.
2. Convert it into a bounded fix between documentation phases; do not carry known friction into the next phase silently.
3. Bind the fix to the strongest available gate—test, generated check, type, or CI rule.
4. Delete the finding once the real journey and relevant gates verify the fix. Git and the PR retain the history.
