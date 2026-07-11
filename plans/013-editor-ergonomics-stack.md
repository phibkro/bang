# Plan 013: The ergonomics stack — generated grammars, LSP, tree-sitter, VS Code + the agent-loop verbs (explain · fixits · new · --update · watch)

> **Executor instructions**: Follow this plan slice by slice; every slice is independently
> bankable — commit each separately, land what fits, report the rest untouched. Run every
> verification command. STOP conditions binding. The reviewer maintains the index. Reply in
> the standard report format.
>
> **Drift check (run first)**: `git log --oneline -2 -- Bang/Frontend/Surface.lean Bang/Frontend/Query.lean web/docs/ tools/gen-reference.py`
> and compare "Current state" below.

## Status

- **Priority**: P3 for slices 1–4 (◊5.75 / public-early, human-facing); P2 for slices 5–9
  (agent-loop verbs — they move the agent-coding yardstick directly)
- **Effort**: XL total, but NINE independently bankable slices (S/M each) — this plan is a
  MENU across multiple dispatches, not one lane's session. **Reorder slices 5–9 by the N5
  dogfood findings note when it lands** (evidence beats the menu order below).
- **Risk**: LOW (all additive; nothing enters the verify gate's Lean legs)
- **Depends on**: none hard; slice 2 benefits from N3's verbs being merged (holes/impact landed)
- **Category**: dx / direction
- **Planned at**: 2026-07-10 (stamp the sha at dispatch — the wave was mid-merge at writing)

## Why this matters

The public-early policy puts outsiders in front of bang during ◊5.5. Today an outsider gets: a
site that renders bang code as plain text (the sync-seam alias), a GitHub repo that highlights
nothing, and no editor support. The engine half of the fix already exists — the parser is a
REIFIED rule table (`opInfo`, `keywordRule` in `Bang/Frontend/Surface.lean`) and the LSP's guts
are the landed `bang query`/`check --json`/`holes` verbs (#80/#82, deliberately "the agent LSP
as CLI"). What's missing is projections: grammars generated from the tables (so they cannot
drift from the parser — the same move `gen-reference.py` already makes for the grammar DOCS)
and a thin JSON-RPC transport over the Query API.

## Current state

- `tools/gen-reference.py` extracts `opInfo` (operators + precedences) and `keywordRule`
  (keyword forms) from `Bang/Frontend/Surface.lean` — reuse its extraction functions.
- Reserved words (parser-enforced): `get put raise new read write resume with param` — extract
  from source, don't hand-list (grep `pIdent`'s reserved list; a hand-copy is drift).
- The site aliases `bang`→`text` fences at the sync seam (`web/docs/sync-docs.mjs` — the comment
  block there names THIS plan's slice 1 as the deletion trigger).
- `Bang/Frontend/Query.lean` — Tier-1 public API: check/holes/impact/refs/dump JSON functions.
  `Main.lean` — the CLI verb arms (the exemplar for wiring).
- Repo conventions: new tools carry `# tool:` frontmatter + the telemetry line (see any
  `tools/*.sh` post-plan-012); new batteries enroll in `tools/run-batteries.sh`'s array;
  generated artifacts get a `--check` staleness leg chained into `fitness`.

## Slices

### Slice 1 (S–M): the GENERATED TextMate grammar — one artifact, three surfaces

A generator (suggest extending the gen-tools family: a new python tool under `tools/`) that
derives a `bang.tmLanguage.json` from the reified tables: keywords (from `keywordRule`),
operators (from `opInfo`), reserved binders, plus the small hand-written residue (line comments
`--`, strings, number literals, effect/handler block punctuation) kept INSIDE the generator as
explicit constants. Output committed (a generated artifact with a `--check` fitness leg, like
the reference). Then consume it in all three surfaces:
1. **the site**: register the grammar with Shiki via the vocs config's markdown/code options
   (vocs passes shiki options through; verify empirically) and DELETE the `bang`→`text` alias
   in the sync seam (leave the `wat`→`text` case only if wat fences reappear un-bundled).
2. **GitHub**: a `.gitattributes` `*.bang linguist-language=` override needs a registered
   language — instead document in the grammar's header comment that real linguist registration
   is post-adoption; GitHub rendering via the grammar is NOT achievable per-repo — say so
   honestly in the report rather than claiming it.
3. **VS Code**: the grammar file is slice-4's input; nothing to do here yet.
**Verify**: site builds with highlighted bang fences (`bun run build` exit 0 AND a grep of one
generated HTML page shows token spans inside a known bang snippet, not a plain `text` block);
the fitness `--check` leg is green, then demonstrated RED on a hand-edit to the generated
grammar, then restored.

### Slice 2 (M): the LSP wrapper — a thin stdio JSON-RPC transport over Query

A new leaf executable (the `bang` exe pattern: a root-level .lean file registered in
`lakefile.toml`, importing Frontend only) speaking LSP over stdio: `initialize`,
`textDocument/didOpen`/`didChange` (re-check the buffer via the SAME `checkProg` pipeline),
`publishDiagnostics` (from `check --json`'s data), `textDocument/hover` (the display-type of
the enclosing decl — POSITION mapping is line-level only until the #52 span tier lands: hover
returns the DECL's type for the line, honestly coarse, documented as such), and
`textDocument/definition` for module-qualified names via the refs graph. NO completions, NO
semantic tokens in this slice. Battery: a `tools/` test script driving the server over stdio
with 6-8 canned request/response cases (the repl battery is the shape exemplar), enrolled in
the batteries array.
**Verify**: the battery green standalone + under run-batteries; a manual smoke transcript in
the report (initialize → didOpen a broken file → diagnostics arrive with the right span).

### Slice 3 (M): tree-sitter grammar (#9)

Check the stale `lang-bang-tree-sitter` branch first (`git log lang-bang-tree-sitter -3`) —
salvage if useful, else fresh. Generate what's generable (keywords/operators from the same
extraction the TextMate generator uses — share the extraction module), hand-write the grammar.js
structure. The corpus test: tree-sitter's own test format seeded from a SAMPLE of the
`parsesTo` corpus + every `examples/*/main.bang` must parse without ERROR nodes.
**Verify**: `tree-sitter test` green; `tree-sitter parse examples/*/main.bang` zero ERROR
nodes (script the sweep; count asserted). Nix note: `nix shell nixpkgs#tree-sitter`.

### Slice 4 (S): the VS Code extension package

`editors/vscode/` (new dir): package.json contributing the language id + the slice-1 grammar +
an LSP client pointed at the slice-2 server binary. Build with `nix shell nixpkgs#vsce` or
plain `npm pack` — DO NOT publish to the marketplace (outward action, operator's button).
**Verify**: `vsce package` (or equivalent) produces a `.vsix`; the report includes the
install-and-open smoke result ONLY if a VS Code is available headlessly — otherwise state the
packaging succeeded and the smoke is deferred to the operator.

### Slice 5 (M): stable diagnostic codes + `bang explain` (the rustc pattern)

A diagnostic-code REGISTRY as the SSoT (a table in code — code · one-line summary · the
teaching text · a minimal triggering example), starting with the existing teaching-diagnostic
family (the ADR-0095 D4 text, the reserved-word rejections, the row-mismatch and escape
diagnostics) — the long tail retrofits incrementally, slice-bounded at ~10 codes. Diagnostics
gain their code in output (`error[B012]: …`); `bang explain B012` prints the registry entry;
`gen-reference.py` derives a diagnostics section from the registry (drift-unrepresentable).
**Verify**: battery cases per code (trigger → the code appears; explain → the teaching text);
reference regen includes the section; `--check` green.

### Slice 6 (M): lint FIXITS riding the rewrite preservation gate

Extend lint findings with an optional machine-applicable edit; `bang lint --fix` applies it and
then runs THE SAME differential preservation gate `bang rewrite` uses — a fixit that provably
preserves semantics, which is the bang-distinctive claim (Roslyn/rust-analyzer can't make it).
Start with 1–2 mechanical lints only (whichever existing findings have obvious rewrites — read
`Bang/Frontend/Lint.lean` for candidates); the mechanism is the deliverable, not coverage.
**Verify**: fix applied → preservation gate green → re-lint shows the finding gone; a
deliberately WRONG fixit (planted in a test) is REJECTED by the gate (the red-path test).

### Slice 7 (S): `bang new NAME` scaffolding

Scaffolds a directory per the examples convention (a runnable starter `main.bang`, an
`expected.txt` produced by actually running it, a README stub) with a `--module` variant for
the import/use multi-file shape. **Verify**: scaffold → `bang run` works out of the box →
the directory passes the check-examples loop shape.

### Slice 8 (S): `bang test --update` (deliberate snapshot acceptance)

An update mode for the expected.txt oracle: re-runs a NAMED example and rewrites its
expected.txt from actual output. Deliberate-only by design: requires naming the example (no
bulk-silent mode), prints the old→new diff loudly, and relies on git for review (the oracle
change is a visible diff, never an invisible mutation). **Verify**: update flow shown; the
diff appears in `git status`; check-examples green after.

### Slice 9 (S): watch mode

`just watch [FILE]` — re-runs `just check FILE` (or check-examples for a named example) on
file change via inotifywait (`nix shell nixpkgs#inotify-tools`), the Vite-lesson loop-speed
item. **Verify**: a manual transcript (edit → automatic re-check output) in the report.

## Done criteria (per slice — land what fits)

- [ ] S1: grammar generated + fitness-gated; site highlights bang; alias deleted
- [ ] S2: LSP battery in the gate; smoke transcript in the report
- [ ] S3: tree-sitter corpus green over all examples
- [ ] S4: a .vsix artifact, unpublished
- [ ] S5: ≥10 coded diagnostics + explain verb + the generated reference section
- [ ] S6: the fixit mechanism with the preservation gate REJECTING a planted wrong fixit
- [ ] S7: scaffold runs out of the box
- [ ] S8: oracle updates are loud, named, git-visible
- [ ] S9: the watch transcript
- [ ] `just verify` + `just fitness` exit 0 after each slice

## STOP conditions

- vocs does NOT pass shiki lang options through (slice 1.1) — report the config wall; the
  grammar still lands (fitness-gated) and the site keeps the alias until vocs allows it.
- The LSP slice needs real per-node spans to be useful at all (hover unusable at line
  granularity) — report; #52's span tier becomes the dependency and slice 2 parks.
- tree-sitter's grammar.js needs parser behaviors the rule table can't express (significant
  lookahead) — hand-write those productions and SAY which ones; if >half the grammar ends up
  hand-written, report the generation premise as weakened.
- Anything wants to publish (marketplace, linguist PR) — operator's button, always.

## Maintenance notes

- The generated-grammar `--check` leg makes syntax changes self-announcing: a parser-table
  edit that forgets to regen fails fitness — that's the "stable ergonomics while the surface
  is liquid" property this plan exists for.
- Slices 5–9 were merged in from the ecosystem-inspiration survey (operator, 2026-07-10);
  the N5 dogfood findings note is the standing re-prioritizer for them. Doctests were
  surveyed and found ALREADY WON in inverted form (gen-reference derives examples FROM
  compiled #guards — the docs gate the build rather than decorate it).
