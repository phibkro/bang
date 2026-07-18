<!-- note-status: active -->
# docs/outreach — the v0.2 launch kit (#70)

The content deliverables for the v0.2 public announcement (issue #70). The operator
posts; these are drafts. **The binding rule is the claims constraint: every
load-bearing sentence traces to a source in the repo, and every command shown was
actually run** (`copy-kit.md` §5, the anti-hype rules — this audience of proof people
*will* catch a green-stub claim).

## The files

| file | what it is | shape |
|---|---|---|
| `announcement-v0.2.md` | the post | HN "Show HN" + lobste.rs, ~750 words |
| `hn-first-comment.md` | the author's own first reply | ~150 words, pre-empts the skeptic thread |
| `asciinema-script.md` | the ~90-second terminal demo | exact commands + REAL captured frames |
| `README.md` | this — posting checklist + claims-trace | — |

## Grounding (the sources these derive from)

- `docs/notes/copy-kit.md` — the ruled wedge (candidate A: "the docs can't lie"), the
  2-min pitch, the skeptic FAQ, and the binding anti-hype rules. **Read this first.**
- `docs/notes/traction-survey.md` — why the wedge is "docs-that-cannot-lie" and why
  design-deep-dives (not release notes) travel on HN.
- issue #70 — the original scope (announcement + asciinema, after a tagged release).
- `CONTEXT.md` + `CHANGELOG.md` — what v0.2 actually contains.

## Posting checklist (the buttons that precede the post)

Ordered. **The post links things that must exist first** — nothing to link before the
tag and the site are live.

1. **Tag the release.** `just release <VERSION>` (drives the 3-row build matrix:
   x86_64-linux, aarch64-linux, aarch64-darwin — `tools/install.sh` reads the same
   triples). The post's `curl … | sh` one-liner pulls a release asset; it 404s without
   a tag.
2. **Deploy the docs site.** `cd web/docs && bun run build` → publish to
   `phibkro.github.io/bang/`. The post's "reference that can't lie" CTA links there.
   The `/tour` route (`web/docs/vocs.config.ts`) should render.
3. **Smoke the install one-liner on a clean machine** — actually run
   `curl -fsSL …/tools/install.sh | sh` and confirm `bang --version` works. The demo
   *shows* it; verify it before inviting the crowd.
4. **Re-run the asciinema commands and record.** Every frame in `asciinema-script.md`
   was captured off `draft-announcement @ 0425b925`; re-run against the tagged sha so
   the recording matches what a viewer installs. A drifted frame = the demo is wrong.
5. **Post + immediately drop the first comment** (`hn-first-comment.md`, author
   convention).

## Claims-trace table (every load-bearing claim → its source)

Each row: the claim as it appears in the copy · the source that makes it true ·
verified-how (claims re-audited 2026-07-18 against the current release worktree;
`wasmtime 45.0.0`).

| claim in the copy | source | verified |
|---|---|---|
| "the reference is generated from the verified source; every example is build-gated" | `docs/reference/language.md` header; `tools/gen-reference.py` (`--check` is a `just fitness` leg, justfile:229) | read the header + the fitness leg |
| "195 verified examples in the 1,331-line generated reference" | `docs/reference/language.md`; `tools/gen-reference.py` | generator reports `195 verified examples`; `wc -l` → `1331` |
| "1,118 `#guard`s across the source" | `Bang/**` | `rg -n '^#guard' Bang -g '*.lean' \| wc -l` → `1118` |
| the `#guard runYieldsInt 30 "…x*x+y*y" 25` line (verbatim) | `Bang/Examples.lean:129` | quoted verbatim from source |
| "drift → `lake build` goes red" | `tools/gen-reference.py --check` exits 1 if committed ≠ regenerated (fitness leg) | read the generator + fitness recipe |
| "verified kernel; 22 clean audited headlines within trusted-three, 5 explicitly flagged" | CLAUDE.md invariants #1/#3/#5; `CONTEXT.md` generated proof-state | read CLAUDE.md + CONTEXT proof-state block; `lake build` replays `Bang.Audit` |
| "tested superset: parser, elaborator, Turing-complete Div fragment, differential-tested; seam is type-visible" | CLAUDE.md the stratification principle; `copy-kit.md` §4 | read CLAUDE.md |
| "v0.2, not production-ready; latest published cold audit 7/10 and not yet rerun after fixes" | `stranger-test-5.md`; `CONTEXT.md` (round-5 fixes landed afterward) | read both; wording distinguishes the measured score from current inference |
| "paradigms are values you swap — one `logic`, two handlers → 30005" | `examples/stage-swap/main.bang` + `README.md` | `bang run examples/stage-swap/main.bang` → `30005` |
| "trait laws are checked; `bang test` reports PASS / a counterexample" | `tools/test-law.sh` (issue #60 seam) | ran `bang test` on the true+bogus fixtures → `✓ … PASS (30 samples)` / `✗ … FAIL — counterexample [(0 - 10), 0]` |
| "`deriving (Eq, Ord)` generates impl + laws" | ADR-0097 (Accepted); `CONTEXT.md` mega-session wave | read ADR + CONTEXT |
| "whole programs compile to WebAssembly — `bang build` nqueens → WasmGC → Wasmtime → 21004" | `Main.lean`; `tools/test-bang-build.sh`; `examples/nqueens/` | built and ran `/tmp/bang-nqueens-v02.wasm` on Wasmtime → `21004` |
| "one command reproduces 45 emitted programs, 23 effectful, real engine vs kernel oracle" | `tools/emit-rung5-effects-diff.sh` | ran it → all 45 emitted programs matched; ADR-0114 `stateful-quota` included |
| "that agreement is the point / proof rides the reference" | CLAUDE.md invariant #1 | read CLAUDE.md |
| "safe to generate into; illegal states structurally unrepresentable; built by agent teams" | `docs/PRD.md` §3; the moat §2 | read PRD |
| "`bang query hover` — LSP-class op, JSON, agent-facing; `{Div}` row in the type" | `Bang/Frontend/Query.lean`; issue #52 slice 5; `bang --help` | `bang query hover examples/nqueens/main.bang 12 9` → `{"ok":true,…"row":"{Div}"…}` |
| "install: prebuilt for x86_64-linux, aarch64-linux, aarch64-darwin; curl one-liner" | `tools/install.sh`; `README.md:52` | read install.sh platform table + README |
| the reference site URL `phibkro.github.io/bang/` | `web/docs/vocs.config.ts:5` | read the config |
| "concurrency = scheduler-as-handler (direction ratified, impl post-v1)" — NOT claimed as shipped | ADR-0101 (Accepted; implementation post-v1, spike-gated) | read ADR-0101 header; deliberately NOT in the post as a shipped feature |

## What the anti-hype rules kept OUT (deliberate cuts)

Per `copy-kit.md` §5 — recorded so a future editor doesn't "helpfully" add them back:

- **No "try the full language in your browser."** Only rung-1 pure arithmetic is
  honestly browser-runnable; a playground stubbing the hard part is the green-stub lie.
  The post ships a `curl` install, not a playground claim.
- **No "deterministic concurrency, today."** ADR-0101 is *direction*, post-v1. The
  replay claim (copy-kit candidate C) is real but gated — held until the sim-scheduler
  is a runnable demo, when it becomes a headline. Not in this post.
- **No closed contextual-equivalence claim.** The binary LR (◊4) is parked; the live
  theorem is forward-simulation (compile correctness). The post claims neither by name —
  it claims the *observable* fact (wasmtime == kernel oracle) instead.
- **No "production-ready / stable / 1.0."** It's v0.2; the latest published stranger-test is
  7/10 and has not been rerun after the pre-release fixes, said plainly.
- **No "proof-by-construction for your data structures, today."** The user-facing
  law-language is the north star, least-built. The post leads with docs-that-can't-lie
  (shipped) and shows checked *trait laws* (real today), not proof-by-construction.
