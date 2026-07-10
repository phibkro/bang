# Plan 013: The editor-ergonomics stack — generated grammars, the LSP wrapper, tree-sitter, VS Code

> **Executor instructions**: Follow this plan slice by slice; every slice is independently
> bankable — commit each separately, land what fits, report the rest untouched. Run every
> verification command. STOP conditions binding. The reviewer maintains the index. Reply in
> the standard report format.
>
> **Drift check (run first)**: `git log --oneline -2 -- Bang/Frontend/Surface.lean Bang/Frontend/Query.lean site/ tools/gen-reference.py`
> and compare "Current state" below.

## Status

- **Priority**: P3 (◊5.75 / public-early — human-facing; agents already have the JSON verbs)
- **Effort**: L total, but sliced S/M/M/S
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
- The site aliases `bang`→`text` fences at the sync seam (`site/sync-docs.mjs` — the comment
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

## Done criteria (per slice — land what fits)

- [ ] S1: grammar generated + fitness-gated; site highlights bang; alias deleted
- [ ] S2: LSP battery in the gate; smoke transcript in the report
- [ ] S3: tree-sitter corpus green over all examples
- [ ] S4: a .vsix artifact, unpublished
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
- Follow-ups (separate plans, fed by the N5 dogfood findings): `bang explain <diag-code>` +
  stable diagnostic codes (the rustc pattern), lint FIXITS riding the rewrite preservation
  gate, `bang new` scaffolding, `bang test --update` snapshot acceptance, watch mode.
