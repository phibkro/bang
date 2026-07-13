# Contributor feedback

**Summary:** Open, actionable bugs, DX friction, and improvement opportunities discovered while executing Plan 014.

## Open findings

### F-020 — Example facts omit structured engine and concept metadata

- **Evidence:** `docfacts/schema/example.schema.json` and `docfacts/examples/logger-counting.json` represent prose, source text, output, and evidence, but do not encode the engines that support the example, the concepts it teaches, or whether it belongs to a refusal class.
- **Impact:** Retrieval and future consumers must infer stable classification data from prose, so facts cannot reliably drive engine filters, concept indexes, or refusal documentation.

### F-021 — Markdown bypasses the committed serialized fact

- **Evidence:** `tools/docfacts_logger.py` builds one in-memory dictionary and renders both JSON and Markdown from that sibling value; no generation or check path reloads `docfacts/examples/logger-counting.json` before rendering the page.
- **Impact:** The public consumer can stay green without exercising the serialization boundary, allowing parser/schema/committed-fact integration defects to remain invisible.

### F-022 — Generated public source pointers resolve outside the repository

- **Evidence:** `docs/reference/examples/logger-counting.md` renders `../../../examples/...`, `../../../tools/...`, and `../../../docfacts/...` links from a page published under the Vocs documentation tree.
- **Impact:** Vocs publishes those as site-relative paths where the repository files do not exist, turning canonical-source and evidence pointers into dead links for readers.

### F-023 — CI does not observe the default-shell jsonschema boundary directly

- **Evidence:** `flake.nix` adds Python with `jsonschema` to `devShells.default`, but `.github/workflows/verify.yml` proceeds directly to broad `just verify` without first importing the module through `nix develop --command python3`.
- **Impact:** A dev-shell packaging regression is reported late and indirectly inside the broad gate rather than at the dependency boundary that caused it.

### F-024 — Docfact self-tests are duplicated across gate recipes

- **Evidence:** `justfile` invokes `tools/docfacts_logger.py --check` and then `--self-test` separately in both `fitness` and `docs-check`, while drift checking and semantic poles belong to one docfact gate leg.
- **Impact:** The same poles run multiple times and the apparent gate composition can drift if one recipe later keeps only one half.

### F-025 — The tools index captures a closing docstring delimiter

- **Evidence:** `tools/docfacts_logger.py` uses a one-line module docstring after its tool header, so `tools/gen-tools-index.py` records a purpose ending in `"""` in `tools/README.md`.
- **Impact:** The generated tool map exposes parser punctuation as documentation and obscures the generator's actual purpose.

## Lifecycle

1. Record a finding when it is observed, with a concrete failure scenario and source evidence.
2. Convert it into a bounded fix between documentation phases; do not carry known friction into the next phase silently.
3. Bind the fix to the strongest available gate—test, generated check, type, or CI rule.
4. Delete the finding once the real journey and relevant gates verify the fix. Git and the PR retain the history.
