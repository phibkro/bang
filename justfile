# bang-lang task runner. `just` is more ergonomic than make (no .PHONY,
# parameters via {{...}}, listing recipes via `just --list`).
#
# Common usage:
#   just              # list recipes
#   just verify       # selfcheck + build + audit (default gate)
#   just check FILE   # fast per-file error check
#   just burndown     # per-module sorry/axiom count
#
# Real guarantee for Phase B is `lake env lean Bang/Audit.lean` (#print
# axioms per theorem); audit.sh is the cheap static guard.

# Default: list recipes.
default:
    @just --list --unsorted

# First-time setup (idempotent): install hooks + fetch Mathlib oleans + verify.
setup:
    bash tools/setup.sh

# Read-only readiness report for the bounded newcomer journey.
onboarding-preflight *ARGS:
    bash tools/onboarding-preflight.sh {{ARGS}}

# Known-good/known-bad poles for preflight states and non-mutation.
test-onboarding-preflight:
    bash tools/test-onboarding-preflight.sh

# Executable env/oracle/compiled agreement for the common newcomer route.
test-onboarding-journey *ARGS:
    bash tools/test-onboarding-journey.sh {{ARGS}}

# Content-owned frontend role-lab fixture through fmt/check/query/impact/rewrite/run.
test-role-lab-frontend:
    bash tools/test-role-lab-frontend.sh

# One pinned formatter/linter entry point. The PostToolUse hook calls the same
# underlying script with one safely quoted changed-file path.
autoquality:
    bash tools/autoquality.sh

# One-shot orient — position, active path, burndown, recent commits, next steps.
orient:
    bash tools/orient.sh

# Default verify gate — selfcheck + build + the independent test batteries (run
# concurrently by run-batteries, plan 004) + audit. `audit` now runs the full
# `just fitness` bundle (#114), which already includes the ADR-ledger `--check`,
# so a separate `adr-check` dep is redundant.
verify: selfcheck build run-batteries audit

# All independent test batteries, concurrently (single up-front binary build).
# Same set as verify's former serial leg list — check-examples, test-repl,
# test-fmt, test-check-json, test-query, test-rewrite, test-annotate, test-lint,
# test-82-verbs, test-cli, test-law, test-modules — driven by tools/run-batteries.sh (plan 004).
run-batteries:
    bash tools/run-batteries.sh

# Run every examples/<project>/main.bang and diff stdout against expected.txt —
# the end-to-end run oracle for whole bang programs (supersedes per-example
# #guards). Depends on `build` for the `bang` runner (verify runs build first).
check-examples:
    bash tools/check-examples.sh

# Same corpus as check-examples, run through `bang run --engine=env` (the ADR-0094
# environment machine) and diffed against the SAME expected.txt — the empirical
# companion to `evalE_agrees_evalD`. Part of the default `verify` chain (run-batteries).
check-examples-env:
    bash tools/check-examples-env.sh

# Non-interactive gate for `bang repl` (issue #7): pipes scripted transcripts
# through the binary and asserts stdout/stderr/exit-code, mirroring
# check-examples.sh's shape. Part of the default `verify` chain.
test-repl:
    bash tools/test-repl.sh

# Gate for `bang fmt` (#58 CLI half): pinned canonical output · file/stdin
# agreement · idempotency sweep over examples/ · parse-error path. Part of
# the default `verify` chain.
test-fmt:
    bash tools/test-fmt.sh

# Gate for `bang check [--json]` (#59, agent-facing structured diagnostics):
# ok:true/false via file+stdin · human vs --json rendering · the 0/1/2 exit
# contract (ok / diagnostics / tool-error) · jq-parseability. The schema's
# byte-exactness is gated separately by Bang/Frontend/Diagnostics.lean's
# #guards; this gates the CLI surface. Part of the default `verify` chain.
test-check-json:
    bash tools/test-check-json.sh

# Gate for `bang query <op>` (#80, the agent LSP as stateless CLI subcommands): symbols/type/
# effects/laws/def/refs — file-arg vs stdin, resolver-aware multi-file (import qualification),
# and the 0/1/2 exit-code contract observed through the binary. Part of the default `verify` chain.
test-query:
    bash tools/test-query.sh

# Gate for `bang rewrite <verb>` (#81, the CQS command side over #80's query/read-model side):
# fmt-as-rewrite-#0 parity with `bang fmt`, the rename happy path + its three diagnostics, the
# diff-vs--w output contract (immutable by default, `-w` writes), and the differential
# PRESERVATION GATE falsified (a local-binding-capture case the gate must catch, then shown
# restored). Part of the default `verify` chain.
test-rewrite:
    bash tools/test-rewrite.sh

# Gate for `bang rewrite annotate` (#82 item 1): infers types AND effect rows for top-level `let`
# decls lacking an ascription, diff-by-default/-w, the already-annotated no-op case, and a
# genuinely non-empty builtin row (Div, via ordinary recursion) made diff-visible end to end.
# Part of the default `verify` chain.
test-annotate:
    bash tools/test-annotate.sh

# Gate for `bang lint` (#82 item 2): the three rules (dead-private/unused-pub/fmt-divergence) as
# queries over the fact base, human table vs --json, the exit contract, and --quiet-clean.
# Part of the default `verify` chain.
test-lint:
    bash tools/test-lint.sh

# Gate for the #82 agent-tooling verbs over the landed Query rails (analysis/ergonomics commands
# past query/rewrite/lint/annotate): `bang holes` (residual/underdetermined positions), `bang
# impact` (transitive dependents = pre-edit blast radius), `bang semver-diff` (public-surface diff
# → version bump). File/stdin, resolver-aware, the 0/1/2 exit contract, one falsify-once
# discrimination case per verb. Part of `verify` (enrolled in tools/run-batteries.sh's array).
test-82-verbs:
    bash tools/test-82-verbs.sh

# Gate for the TOP-LEVEL CLI hygiene (#66/#67): `--help`/`--version` exit 0
# with text on stdout, and every non-zero RUNTIME outcome (oom/escapedCap/
# stuck/compiled-collapse) prints a human-readable stderr message alongside
# its exit code. Part of the default `verify` chain.
test-cli:
    bash tools/test-cli.sh

# Exact release tag ↔ binary provenance poles: accepts only byte-exact `bang X.Y.Z`,
# rejects stale/suffixed/noisy/nonzero binaries and malformed tags. Part of verify.
test-release-version:
    bash tools/test-release-version.sh

# Network-free release-integrity poles: deterministic all-platform SHA256SUMS,
# one-tag installer resolution, exact manifest parsing, checksum verification, and
# atomic preservation of an existing install across every fetch/validation failure.
test-release-integrity:
    bash tools/test-release-integrity.sh

# Gate for `bang test` (#60's CLI wiring over the landed LawTest/lawInstancesOf
# seam): a real true trait law (PASS), a deliberately false one (FAIL +
# counterexample), no-laws-found (vacuous success), and the decls-only-input
# footgun this slice's own manual testing found (a trailing expression
# silently corrupts every discovered law's report — caught before it does).
# Part of the default `verify` chain.
test-law:
    bash tools/test-law.sh

# Rank duplicated code windows in Bang/ (extraction candidates; triage lives in
# docs/notes/clone-triage.md). ARGS pass through, e.g. `just clones --window 8`.
clones *ARGS:
    python3 tools/clone-report.py {{ARGS}}

# Regenerate docs/notes/proof-assets.md (the reusable-proof-assets inventory).
proof-assets:
    python3 tools/gen-proof-assets.py

# Doc-staleness over git pins: every note declares `<!-- describes: <paths> @ <sha> -->`
# or opts out (`describes: none`). Warn-tier in fitness; `just doc-pins --strict`
# (stale = fail) belongs in the release ritual.
doc-pins *ARGS:
    python3 tools/check-doc-pins.py {{ARGS}}

# Regenerate EVERY derived artifact in one shot — the write-side twin of the fitness
# checks. Run before committing anything that touches generators' inputs; kills the
# one-stale-leg-per-hook-cycle onion at landings.
regen-all:
    python3 tools/gen-adr-index.py
    python3 tools/gen-notes-index.py
    python3 tools/gen-tools-index.py
    python3 tools/gen-questions-index.py
    python3 tools/gen-llms-txt.py
    python3 tools/refs.py build
    python3 tools/gen-gate-index.py
    python3 tools/docfacts_architecture.py
    # proof docfacts EXCLUDED: live-Audit/build-dependent, like proof-state below.
    # Use `just proof-docfacts` when proof inputs move.
    python3 tools/gen-import-graph.py
    python3 tools/check-architecture-assertions.py
    python3 tools/gen-proof-assets.py
    python3 tools/gen-changelog.py
    python3 tools/docfacts_language.py
    python3 tools/gen-reference.py
    python3 tools/docfacts_logger.py
    python3 tools/gen-tmgrammar.py
    # gen-proof-state EXCLUDED: build-dependent — in a build-less clone it emits a FALSE
    # census block into CONTEXT.md (toolmap finding 2026-07-09). Use `just proof-state` after a build.

# Gate for ADR-0093 (file-modules, `import`/`use`/`pub`): real multi-FILE
# resolution through the compiled CLI — happy-path import + use, the existing
# examples/ corpus unchanged through the resolver, missing-import/cycle/
# private-access error transcripts, and same-dir-shadows-root search order.
# Part of the default `verify` chain (plan 004) — the module-merge CORE's own
# laws are already #guard-gated in Bang/Frontend/TypeCheck.lean; this gates
# only what #guard cannot (real filesystem IO).
test-modules:
    bash tools/test-modules.sh

# Gate for stable diagnostic codes + `bang explain` (plan 013 slice 5): each example-carrying
# registry code fires end-to-end (`explainCode` in --json, `error[Bxxx]` in the human path),
# `explain CODE` prints the teaching entry, `explain BOGUS` is a loud unknown-code error. The
# registry byte-exactness is #guard-gated in Bang/Frontend/DiagCodes.lean; this gates the CLI
# surface. Part of the default `verify` chain (enrolled in tools/run-batteries.sh's array).
test-explain:
    bash tools/test-explain.sh

# The --compiled differential gate for the dogfood programs (#135): calc + json run on the compiled
# engine (exec∘compile) byte-identically to their expected.txt AND to `--engine=env` (the
# differential). Makes the diagnosis's "both pass compiled" a STANDING gate, so a compiled-path
# regression (the #95-class re-entrant-parser slowdown, a lowering drift) fails verify instead of
# rotting into a stale finding. Enrolled in tools/run-batteries.sh's array.
test-compiled-dogfood:
    bash tools/test-compiled-dogfood.sh

# Regenerate the ADR decided-ledger (the index + resolved-questions tables in
# docs/decisions/README.md) from each ADR's frontmatter. Drift = unrepresentable.
adr-index:
    python3 tools/gen-adr-index.py

# Gate the ADR ledger: README generated region is current; every Q marked
# RESOLVED(ADR-n) in OPEN_QUESTIONS ⟺ ADR-n declares `Resolves: Qn`; and each
# ADR's sentinel-frontmatter Status agrees with its prose Status bullet.
adr-check:
    python3 tools/gen-adr-index.py --check

# Build the Lean library. First time: pulls Mathlib oleans (multi-GB).
build:
    #!/usr/bin/env bash
    set -euo pipefail
    # Cache-get is the legit first-setup path ONLY on the MAIN checkout with oleans genuinely
    # absent. In a LINKED worktree we NEVER cache-get (#40b: it re-clones Mathlib and corrupts the
    # shared .git/objects, 2026-06-27/-29) — oleans come from the nix dev-shell (LEAN_PATH) or the
    # reflink-seeded .lake (tools/new-worktree.sh), so we go straight to `lake build`. If oleans were
    # truly missing it fails loud on its own, and the PreToolUse guard independently blocks any
    # cache-get. The old `-e <local mathlib stub>` precondition FALSE-NEGATIVED in the nix setup
    # (oleans are on LEAN_PATH, not the local dir) → it aborted worktree builds spuriously and forced
    # --no-verify on IC commits (#43).
    if [ "$(git rev-parse --git-dir)" = "$(git rev-parse --git-common-dir)" ] \
       && [ ! -e .lake/packages/mathlib/.lake/build ]; then
      lake exe cache get   # main checkout, first setup only
    fi
    lake build

# Static + dynamic audit gate: the live proof fact comparison is the fail-closed
# axiom policy; tools/audit.sh adds the static/fitness belt and suspenders.
audit:
    python3 tools/docfacts_proof.py --live-check
    bash tools/test-gates.sh
    bash tools/audit.sh

# ◊5 engine probe (OPEN_QUESTIONS Q9): run a stack-switching suspend/resume
# generator on real Wasmtime — leg #2's oracle foundation. Expects `49`.
wasmfx-probe:
    bash tools/wasmfx-probe.sh

# Architecture fitness functions — CLAUDE.md Invariants #3/#5 (five primitives,
# STM-only) + ADR link integrity + ADR decided-ledger currency (gen-adr-index
# --check: README ≡ frontmatter, Status copies agree, Q⟺ADR) + the
# import-direction V (ADR-0046/0047: Core imports neither edge). Fast: no Lean
# build on docs/tooling commits — the proof-state leg elaborates Audit.lean ONLY
# when `Bang/` actually moved (sha short-circuit). Also run by `just audit`.
# adr-check is HERE (not just in `just verify`)
# so docs-only ADR commits — the normal case — get ledger-gated by the hook too.
fitness:
    just autoquality
    bash tools/check-primitives.sh
    bash tools/check-git-hygiene.sh
    bash tools/check-sha-reachable.sh
    bash tools/check-paths.sh
    bash tools/check-loop-audit.sh
    bash tools/check-adr-links.sh
    python3 tools/gen-adr-index.py --check
    python3 tools/import_facts.py --self-test
    python3 tools/arch-check.py
    bash tools/check-audit-sync.sh
    bash tools/check-all-modules.sh
    python3 tools/check-refs.py
    python3 tools/check-onboarding-refs.py
    bash tools/test-onboarding-preflight.sh
    python3 tools/check-runs-in.py
    python3 tools/check-doc-hygiene.py --check
    python3 tools/check-context-claims.py
    python3 tools/gen-notes-index.py --check
    python3 tools/gen-agent-pack.py --check
    python3 tools/gen-tools-index.py --check
    python3 tools/gen-questions-index.py --check
    python3 tools/gen-llms-txt.py --check
    python3 tools/refs.py check
    python3 tools/gen-gate-index.py --check
    python3 tools/gen-proof-state.py --check
    python3 tools/gen-import-graph.py --check
    python3 tools/check-architecture-assertions.py --check
    python3 tools/gen-proof-assets.py --check
    python3 tools/check-doc-pins.py
    python3 tools/gen-changelog.py --check
    python3 tools/docfacts_language.py --check
    python3 tools/gen-reference.py --check
    python3 tools/docfacts_logger.py --check
    bash tools/test-docfacts-architecture-proof.sh
    BANG_SITE_SCHEMA_ADAPTER=python node web/docs/test-site-model.mjs
    BANG_SITE_SCHEMA_ADAPTER=python node web/docs/site-model.mjs --check
    python3 tools/gen-tmgrammar.py --check

# Orientation-doc SHA reachability: every backtick SHA cited as a waypoint in
# CONTEXT.md/ROADMAP.md resolves to a real commit (a rebase/drop makes the prose
# silently false). Foreign hex (other repos, package revs) → tools/sha-allow.txt.
check-sha:
    bash tools/check-sha-reachable.sh

# PATH lifecycle: every active paths/PATH-*.md is reachable from CONTEXT/ROADMAP (done → archive). Also run by fitness.
check-paths:
    bash tools/check-paths.sh

# runs-in validation: every `runs-in=verify` script is reachable from the verify chain or the
# batteries array; every battery is runs-in=verify; every runs-in=hook script is hook-referenced.
# Makes the header's `runs-in=` claim a check, not a reading task. Also run by fitness.
check-runs-in:
    python3 tools/check-runs-in.py

# Reference library (refs.bib = single source of truth; index.json + the README block are derived).
refs-index:
    python3 tools/refs.py build

# Regenerate the gate-composition block in .claude/codebase-maintenance.md from the justfile recipes.
gate-index:
    python3 tools/gen-gate-index.py

# Regenerate the module dependency graph (mermaid + fan-in) in docs/architecture/core-overview.md §2 from the import edges.
import-graph:
    python3 tools/gen-import-graph.py

# Regenerate the current architecture assertion snapshot from code and accepted ADRs.
architecture-assertions:
    python3 tools/check-architecture-assertions.py

# Regenerate docs/notes/README.md (the design-notes map) from each note's `note-status` frontmatter.
notes-index:
    python3 tools/gen-notes-index.py

# Splice the lane-discipline pack (from .claude/lane-discipline.md) into each .claude/agents/*.md.
# The generate-rung fallback: the harness doesn't expand @-injection in agent bodies, so the pack
# is a marked GENERATED block, drift-gated by `just fitness`. Also run by fitness (`--check`).
agent-pack:
    python3 tools/gen-agent-pack.py

# Regenerate tools/README.md (the flat-tools map) from each script's `# tool:` header.
# `just tools-index --with-log` prints a status + last-invoked view (from the telemetry
# log) to stdout WITHOUT touching README.md — the deprecation-candidate view (plan 012).
tools-index *ARGS:
    python3 tools/gen-tools-index.py {{ARGS}}

# Regenerate docs/notes/OPEN_QUESTIONS.md (multi-view ledger + validated tie-graph) from the OKF question files.
questions-index:
    python3 tools/gen-questions-index.py

# Regenerate llms.txt (the LLM-doc-index, llmstxt.org) from CLAUDE.md's reference index.
llms-txt:
    python3 tools/gen-llms-txt.py

# Regenerate CHANGELOG.md (product MVP increments) from conventional commits since the MVP baseline.
changelog:
    python3 tools/gen-changelog.py

# Regenerate the schema-validated language/diagnostic/prelude/CLI fact bundle.
docfacts-language:
    python3 tools/docfacts_language.py

# Regenerate the schema-validated logger-counting docfact and its standalone Markdown consumer.
docfacts-logger:
    python3 tools/docfacts_logger.py

# Regenerate source-derived architecture facts (no Lean build).
architecture-docfacts:
    python3 tools/docfacts_architecture.py

# Regenerate proof facts from a fresh authoritative Audit build/elaboration.
proof-docfacts:
    python3 tools/docfacts_proof.py

# Static schema/source/fingerprint checks, cross-fact checks, consumer boundary,
# and the 36 architecture/proof falsification poles. Part of `just fitness`.
test-docfacts-architecture-proof:
    bash tools/test-docfacts-architecture-proof.sh

# Focused static architecture/proof documentation-fact gate.
docfacts-architecture-proof-check:
    bash tools/test-docfacts-architecture-proof.sh
    python3 tools/check-architecture-assertions.py --check
    python3 tools/gen-import-graph.py --check

# Cheap documentation-fact + page-manifest schema/semantic poles. Part of `just fitness`.
docs-check:
    python3 tools/docfacts_language.py --check
    python3 tools/docfacts_logger.py --check
    just docfacts-architecture-proof-check
    BANG_SITE_SCHEMA_ADAPTER=python node web/docs/test-site-model.mjs
    BANG_SITE_SCHEMA_ADAPTER=python node web/docs/site-model.mjs --check

# Focused executable agreement for the serialized language docfact seam.
test-docfacts-language:
    bash tools/test-docfacts-language.sh

# Executable logger-counting evidence: env/oracle/compiled output + check/query. Part of verify.
test-docfacts-logger:
    bash tools/test-docfacts-logger.sh

# Regenerate docs/reference/language.md from the Surf/Ty constructor comments + the verified #guard corpus.
reference: docfacts-language
    python3 tools/gen-reference.py

# Regenerate web/docs/bang.tmLanguage.json — the TextMate grammar derived from the reified parser
# tables (opInfo/keywordRule/pIdent) in Bang/Frontend/Surface.lean. `--check` gates it in fitness.
tmgrammar: docfacts-language
    python3 tools/gen-tmgrammar.py

# Regenerate _site/index.html — the glanceable progress dashboard (milestones + ◊-map + proof-state + pulse).
dashboard:
    python3 tools/gen-dashboard.py

# Validate the generated module-graph mermaid actually COMPILES (mmdc render). On-demand; the
# build (`just import-graph`) also auto-compiles before writing, so a broken graph never lands.
check-mermaid:
    python3 tools/gen-import-graph.py --validate

# Regenerate CONTEXT.md's proof-state block from the live axiom gate (Bang/Audit.lean
# #print axioms + burndown + git). `--build` forces a fresh olean read (authoritative).
# Tree-aware: reads the proof tree, writes the docs tree's CONTEXT.md.
proof-state:
    python3 tools/gen-proof-state.py --build

# Faceted retrieval over the library: `just refs capability-safety` (matches key/title/topic/grounds).
refs QUERY:
    @python3 tools/refs.py query "{{QUERY}}"

# Bibliography fitness (also run by `just fitness`): PDF↔key · grounds:ADR↔ADR · Lean cite↔key · sha256.
check-bib:
    python3 tools/refs.py check

# Zero-dep Node sanity check on the row-unifier algorithm.
selfcheck:
    bash tools/tool-log.sh selfcheck.mjs
    node tools/selfcheck.mjs

# Fast per-file Lean error check (no full library rebuild).
#   just check                        # full build
#   just check Bang/Spec.lean         # just that file
check FILE="":
    bash tools/check.sh {{FILE}}

# Generated Lean symbol index (the navigation gap-fill — tilth/stacklit don't do Lean).
# ON-DEMAND: regenerates fresh in <1s, so it never drifts (a file:line index would churn
# every edit, so it is NOT committed/gated). Optional name filter.
#   just symbols                      # all declarations, sorted by name
#   just symbols HasCTy               # only names containing "HasCTy"
#   just symbols --by-file            # per-module structural outline
symbols PATTERN="":
    python3 tools/symbols.py {{PATTERN}}

# Phase B burndown chart — sorry + axiom count per Bang/*.lean.
burndown:
    bash tools/burndown.sh

# Submit a Lean snippet via stdin; get elaborator output.
#   echo '#check @Bang.Comp.handle' | just eval
eval:
    bash tools/eval.sh

# Install git pre-commit hook (symlink into .git/hooks/). One-time per clone.
install-hooks:
    bash tools/install-hooks.sh

# Run loogle Mathlib type-signature search (via the web service, not a build dep — see lakefile.toml).
#   just loogle "?n + 0 = ?n"     ·     agents: prefer the lean_loogle MCP tool
loogle QUERY:
    @curl -sG "https://loogle.lean-lang.org/json" --data-urlencode "q={{QUERY}}" | jq -r 'if .error then "loogle: \(.error)" else (.hits[]? | "\(.name) : \(.type)") end'

# Remove .lake build artifacts (forces full rebuild next time).
clean:
    -rm -rf .lake

# Run the headline-theorem gate once: fresh Audit build/elaboration, readable
# normalized census, and exact comparison with committed proof documentation facts.
axioms:
    bash tools/tool-log.sh axioms
    python3 tools/docfacts_proof.py --live-check

# Advisory dead-code scan: Bang.* decls unreachable from the Audit headlines +
# the `bang` CLI entry. NEVER a gate — output curates via tools/deadcode-allow.txt.
# Regenerates the tool's full-module import block first (drift-free coverage).
dead-code:
    bash tools/tool-log.sh dead-code
    python3 tools/gen-deadcode-imports.py
    lake env lean tools/DeadCode.lean

# Batteries environment linters over every Bang module (plan 007; NOT in verify yet —
# first-run backlog is triaged in plans/007-lint-triage.md, wiring is an operator call).
# ROOT-MODULE enumeration, not full-file enumeration: `lake lint -- A B` scopes to the
# LAST arg's import closure only (verified, see plans/007-lint-triage.md) — passing every
# `.lean` file as its own scope would massively duplicate findings. The 19 modules below
# are every file nothing else in Bang/ imports; their closures cover all of Bang/ (BFS-verified).
# No Bang.lean barrel exists (retired, #81) so `lake lint` alone (bare) does not work.
lint-lean:
    #!/usr/bin/env bash
    set -euo pipefail
    bash tools/tool-log.sh lint-lean
    for mod in Bang.Audit Bang.Backend.EnvMachine Bang.Distribution Bang.Examples \
      Bang.Frontend.Lint Bang.Frontend.NamedCore Bang.Frontend.Rewrite \
      Bang.Frontend.Surface.PropTest Bang.Frontend.Surface.Trait Bang.Reify.CalcReifySim \
      Bang.Witness.BinopTyping Bang.Witness.BoccRegress Bang.Witness.CapEscapeWitness \
      Bang.Witness.CustomStage1Refute Bang.Witness.ElabFuzz Bang.Witness.ProofExport \
      Bang.Witness.ReturnEscapeReach Bang.Witness.StateEscapeWitness Bang.Witness.VcapFreeRefute; do
      echo "=== $mod ==="
      lake lint -- "$mod" || true
    done

# Build critical path — NOTE: `lake exe pole` does not exist in this importGraph pin
# (only `graph` + `unused_transitive_imports` are registered; see plans/007-lint-triage.md).
# `graph` gives the import SHAPE (fan-in/fan-out), not per-file build timing; real timing
# needs either a newer importGraph pin or parsing `lake build`'s own `Built <mod> (Xs)` lines.
pole:
    bash tools/tool-log.sh pole
    lake exe graph --to Bang.Audit import-graph.dot

# Focused page-manifest gate with the lockfile-installed Ajv adapter.
site-manifest-check:
    nix develop .#site --command bash -lc 'cd web/docs && bun install --frozen-lockfile && bun run manifest:check'

# Production-equivalent Vocs build: enter the opt-in flake-pinned Bun/Chromium shell,
# install the locked JS graph, require every Mermaid SVG, build, repair Vocs's
# generated skip-link base path, and smoke every maintained navigation route.
site-build:
    nix develop .#site --command bash tools/site-build.sh

# The release battery (plan 011) — clean+main+verify gates, extracts notes since the
# previous tag (reuses gen-changelog.py's own derivation, re-windowed — CHANGELOG.md has
# no per-version sections to slice), creates a LOCAL annotated tag, and PRINTS the publish
# commands without running them. The operator's finger stays on the publish button:
#   just release v0.2.0                # normal
#   just release v0.2.0 --skip-verify  # skips only the broad suite; release gates remain
release VERSION *ARGS:
    bash tools/release.sh {{VERSION}} {{ARGS}}

# Advisory unused-import scan (report mode, no --fix — plan 011 rider). ONE combined
# invocation over the same 19 root modules as lint-lean — unlike `lake lint`, `shake`
# genuinely unions multiple modules' closures in a single call (plans/007-lint-triage.md
# "Command note"; 26 files had removable imports at the last run). `lake exe shake` exits
# nonzero when findings exist — advisory here, not a gate: tolerate it (`|| true`) but
# assert the report is non-empty, so a masked tool failure doesn't read as "zero findings".
shake:
    #!/usr/bin/env bash
    set -euo pipefail
    out="$(lake exe shake -- Bang.Audit Bang.Backend.EnvMachine Bang.Distribution Bang.Examples \
      Bang.Frontend.Lint Bang.Frontend.NamedCore Bang.Frontend.Rewrite \
      Bang.Frontend.Surface.PropTest Bang.Frontend.Surface.Trait Bang.Reify.CalcReifySim \
      Bang.Witness.BinopTyping Bang.Witness.BoccRegress Bang.Witness.CapEscapeWitness \
      Bang.Witness.CustomStage1Refute Bang.Witness.ElabFuzz Bang.Witness.ProofExport \
      Bang.Witness.ReturnEscapeReach Bang.Witness.StateEscapeWitness Bang.Witness.VcapFreeRefute 2>&1)" || true
    echo "$out"
    if [[ -z "$out" ]]; then
      echo "shake: EMPTY output — the tool likely failed silently rather than found zero" >&2
      echo "       issues; investigate before trusting a clean report." >&2
      exit 1
    fi

# Generated API docs (doc-gen4) from the `/--`/`/-!` docstring convention. Builds
# in the `docbuild/` SUBPROJECT (its own lake workspace — see docbuild/lakefile.toml)
# so the root manifest stays untouched. NOT in `just verify`: doc-gen4 + the
# KNOWN-BLOCKED upstream (2026-07-10): UnicodeBasic (doc-gen4 transitive dep) gates its
# extern_lib behind isWindows, so its precompiled .so lacks the C symbol on Linux —
# lake build Bang:docs fails at UnicodeBasic.TableLookup. No requirer-side override exists
# (traced vs Lake 5.0.0 source; plans/010 report). Fix = one-line upstream PR to
# fgdorais/lean4-unicode-basic — SUPERSEDED: upstream issue #81 is the canonical thread;
# maintainer holds until a LAKE fix (Lake maintainer concurs it is a Lake bug); the un-gate
# diff was already posted there and not merged. Our repro+nm evidence added to #81. Local
# unblock option = docbuild-root direct-require of a patched FORK (shadows the transitive
# dep) — operator call, since forking is outward. NixOS nuance: symbol missing everywhere,
# faults only under eager binding (bindnow).
# import-closure page render is slow by design. First run resolves doc-gen4's deps
# (network) and compiles it (tens of minutes cold).
docs:
    bash tools/tool-log.sh docs
    # BangDocs.lean is a GENERATED doc-only barrel (regenerated every run — no
    # staleness possible): the parent `Bang` lib is a rootless glob (the barrel
    # was retired), and doc-gen4 renders root modules + transitive imports —
    # a rootless lib renders "(0 root modules)", i.e. NOTHING (false-green).
    find Bang -name '*.lean' | sort | sed 's|/|.|g; s|\.lean$||; s|^|import |' > docbuild/BangDocs.lean
    cd docbuild && lake build BangDocs:docs && echo "→ docbuild/.lake/build/doc/index.html"

# Deliberate snapshot acceptance for ONE example (plan 013 s8): re-run examples/<NAME>/main.bang
# and rewrite its expected.txt from actual output, printing the old→new diff loudly. NAME is
# required (no bulk mode by design — the oracle change stays a small, reviewable git diff); an
# unknown NAME is a loud error. Review the result with `git diff examples/<NAME>/expected.txt`.
#   just update-example caesar
update-example NAME:
    bash tools/check-examples.sh --update {{NAME}}

# Watch a Lean FILE and re-run `just check FILE` on every save (plan 013 s9, the Vite loop-speed
# lesson). Self-provisions inotifywait via `nix shell nixpkgs#inotify-tools` (no repo dep added).
# Runs one check up front, then blocks re-running on each close_write event until Ctrl-C. Editors
# that write-via-rename (vim/emacs) fire close_write on the temp then move it over the target, so
# we watch the DIRECTORY and filter to the file's basename rather than the inode (which the rename
# would orphan). FILE is required — a bare `just watch` has no target and would busy-loop.
#   just watch Bang/Spec.lean
watch FILE:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -f "{{FILE}}" ]; then echo "watch: no such file '{{FILE}}'" >&2; exit 1; fi
    dir="$(dirname "{{FILE}}")"; base="$(basename "{{FILE}}")"
    echo "watching {{FILE}} — Ctrl-C to stop"
    just check "{{FILE}}" || true
    nix shell nixpkgs#inotify-tools -c \
      inotifywait -m -q -e close_write --format '%f' "$dir" | while read -r changed; do
        if [ "$changed" = "$base" ]; then
          echo "── {{FILE}} changed — re-checking ──"
          just check "{{FILE}}" || true
        fi
      done
