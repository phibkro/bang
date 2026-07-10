# bang-lang

A small effect-typed language whose **paradigm and runtime are values, not
language features**. The kernel is thunks + effects + STM; everything else
(mutability, IO, async, actors, signals) is ordinary library code over it.

> **AI agents / Claude Code**: read [`CLAUDE.md`](CLAUDE.md) first — invariants,
> glossary, current playhead, what not to do. Then [`CONTEXT.md`](CONTEXT.md)
> and [`ROADMAP.md`](ROADMAP.md). This README is the human-facing intro.

## Architecture

Two-hop verified compilation (ADR-0016):

```
  source  ─►  graded-CBPV semantics  ─Bahr-Hutton calc─►  CalcVM
                                                              │
                                                              └─Benton-Hur LR─►  WasmFX
```

The **graded-CBPV reference** (`Bang/Core/Semantics.lean`'s `Source.eval` +
`Bang/Spec.lean`) is the specification. The **CalcVM** is the executable interpreter — canonical
operational meaning, derived by calculation, not designed. The **WasmFX
backend** is the optimized compiler output, proven to preserve contextual
equivalence (CakeML / Benton-Hur model). See `docs/notes/spec-handover.md`
for why this is engineer-ready, not still-in-design.

## Layout

```
Bang/                    Lean library — semantics, calc machines, spec, LR
tools/                   audit.sh (axiom gate) + selfcheck.mjs (Node smoke)
docs/
  decisions/             ADRs (governance) — see docs/decisions/README.md
  spec/                  language design notes
  roadmap/               K-keyframe research roadmap (research-grade)
  notes/                 spec-proof-discipline, spec-handover, calc-playbook
references/              cited papers (organized by topic) + refs.bib
paths/                   per-path working docs (PATH-<slug>.md)
.claude/agents/          domain-specific subagent definitions
CLAUDE.md                read-first orientation for agents
ROADMAP.md               long-term map of checkpoints (◊1 → ◊6)
CONTEXT.md               volatile current position on the map
```

## Install

**Download a prebuilt binary** (x86_64 Linux — no Nix, no Lean, no build):

```bash
curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh
bang eval "1 + 2"
# → 3
```

This grabs the latest [GitHub Release](https://github.com/phibkro/bang/releases)
binary and drops it in `~/.local/bin`. The binary is native and links only glibc
+ libgcc_s, so any mainstream glibc-based Linux runs it (no runtime dependencies to
install).

> **Releases start at the first version tag.** Until one is cut there is nothing to
> download — use the build-from-source path below. Only x86_64 Linux has a prebuilt
> binary today (a darwin build is a planned follow-up); on any other platform the
> installer errors out and points you here.

## Run a bang program

To build from source (contributors, other platforms, or before the first release),
you need [Nix](https://nixos.org/download) with flakes enabled — nothing else
(no Lean, no elan; the dev shell brings the exact toolchain). Copy-paste, from a
fresh checkout:

```bash
git clone https://github.com/phibkro/bang.git
cd bang
nix develop -c lake exe cache get   # fetch Mathlib oleans (~2 GB, one-time)
nix develop -c lake build bang      # compile the `bang` runner
./.lake/build/bin/bang eval "1 + 2"
# → 3
```

Run a program from a file (there are ready examples in `examples/`):

```bash
./.lake/build/bin/bang run examples/state/main.bang
# → 5
```

Other subcommands: `bang repl` (interactive), `bang fmt <file>` (canonical
form), `bang check <file>` (type-check only, `--json` for structured
diagnostics), `bang test <file>` (law runner). `bang --help` lists flags and
exit codes.

**Engines (v0.1.0).** The default engine is the *proven environment machine*
(ADR-0094): its agreement with the kernel semantics is a machine-checked
theorem (`evalE_agrees_evalD`, axiom-clean) and it eliminates the per-step
substitution cost — the `examples/json` parse runs in ~50 ms where the
substitution reference takes ~16 s. `--engine=oracle` runs that reference
(`Source.eval`) — slower, but its failures carry the specific outcome
(out-of-fuel / escaped capability / stuck); it remains the arbiter in every
differential gate. `--engine=compiled` runs the *verified calculated machine*
(`exec ∘ compile`, ADR-0016) — same program, same value.

**Cold-start cost.** Measured from a fresh clone: `cache get` ~2 min (decompresses
Mathlib's prebuilt `.olean` files; **add several minutes to download ~2 GB from the
Lean community CDN if your nix store doesn't already have them**), then `lake build
bang` ~4 min (compiles the bang library + runner). Budget **~10–15 min** on a cold
machine (network-bound for the fetch, CPU-bound for the build); a warm rebuild of
just the runner is ~2 min. Mathlib is a *build-time* dependency only — the resulting
`bang` binary is native and links nothing but glibc.

### Zero-clone: `nix run` (x86_64-linux)

No clone, no dev shell — one command runs bang from the flake:

```bash
nix run github:phibkro/bang -- eval "1 + 2"
# → 3
nix run github:phibkro/bang -- run examples/caesar/main.bang
```

`nix build github:phibkro/bang#bang` produces the native binary at
`result/bin/bang`. See [Packaging](#packaging) for how this stays reproducible.
(x86_64-linux only — the packaging fetches the linux Lean release; other systems
use the `nix develop` path above.)

## Verify the proofs (contributors)

```bash
nix develop          # dev shell with Lean via elan
just verify          # selfcheck + lake build + tools/audit.sh
```

Piecemeal:
```bash
just selfcheck       # zero-dep Node check on the row unifier algorithm
just build           # lake build the Bang library
just audit           # static cheat-grep + lake build clean
lake env lean Bang/Audit.lean   # the real gate — #print axioms
```

## Where things stand

- **K1 unifier** proven (`Bang/Core/EffectRow.lean`)
- **K2 reference `eval`** — ported to the graded-CBPV kernel
  (`Bang/Core/Semantics.lean`'s `Source.eval`) at ◊2; the K2 free-monad form is in git history
- **K3 calculated machines** (eight) — collapsed into one graded-CBPV machine
  `Bang/Backend/AbstractMachine.lean` at ◊3 (see ADR-0017); the eight are in git history
- **Wasmfx spec** in place (`Bang/Spec.lean`, `Bang/Meta/BinaryLR.lean`,
  `Bang/Audit.lean`) — theorem statements frozen; proof bodies awaiting Phase A
  + Phase B per `docs/notes/spec-proof-discipline.md`

Current checkpoint: **◊1 (Reconciliation landed)**. Next: **◊2 (Kernel frozen v1)**.

See `CONTEXT.md` for live state, blockers, and active paths.

## Contributing as a builder

1. Read `CLAUDE.md`, `CONTEXT.md`, `ROADMAP.md`, then skim
   `docs/decisions/README.md`.
2. Read the ADR most relevant to what you're touching (ADRs document the
   *why*, not just the *what*).
3. For kernel work: invoke the `kernel-engineer` subagent. For proofs:
   invoke `proof-engineer`. Both are at `.claude/agents/`.
4. When you make a decision a future session could reasonably reverse, write
   an ADR (copy the format of an existing one; tag layer K / C / S).

## Packaging

The flake packages `bang` as a pure, reproducible `nix build .#bang` / `nix run`
app (issue #63), so a stranger runs it with no clone. All logic lives in
[`nix/bang.nix`](nix/bang.nix); the flake wires it to `packages.{default,bang}`
and `apps.default` on x86_64-linux.

**Why it takes three derivations.** The `bang` exe transitively imports four
`Bang/Core/*` modules that `import Mathlib`, so Mathlib `.olean`s must exist
*before* `lake build bang`. Building Mathlib from source is multi-GB / hours;
instead we fetch the prebuilt oleans the way the dev shell does (`lake exe cache
get`, Lean's CDN). Network is forbidden in a pure derivation, so that fetch lives
in a **fixed-output derivation** (network allowed, output pinned by hash); a
second **pure** derivation runs `lake build bang` offline against it. The exe's
runtime closure is trivial (glibc + libgcc_s; Lean statically links its runtime).

| derivation | what it does |
|---|---|
| `toolchain` | official Lean release, autoPatchelf'd to run on Nix |
| `deps` (FOD) | `lake exe cache get` → the resolved `.lake/packages` tree, network-gated, hash-pinned; a determinism scrub drops the cache-tool metadata + `scripts/` (whose patched shebangs would otherwise make the FOD reference store paths) |
| `bang` (pure) | offline `lake build bang` against toolchain + deps |

### Re-pinning the FOD hash

The `deps` FOD is pinned by `depsHash` in `nix/bang.nix`. It goes stale whenever
the resolved dependency set changes — a Mathlib rev bump in `lake-manifest.json`,
or a `lean-toolchain` bump (which also moves `toolchainHash`). A stale hash fails
**loud** with nix's `hash mismatch … got: <new>`; that error line *is* the re-pin
instruction:

```bash
# 1. set the stale hash to fakeHash in nix/bang.nix:
#      depsHash ? pkgs.lib.fakeHash;
# 2. build once; nix prints the real hash:
nix build .#deps 2>&1 | grep got:
#      got:    sha256-…
# 3. paste that value back as depsHash and rebuild:
nix build .#bang
```

For a `lean-toolchain` bump, do the same for `toolchainHash` first (bump
`leanVersion`/url, set `toolchainHash = lib.fakeHash`, build, copy `got:`), then
re-pin `depsHash` (the toolchain change moves the resolved deps).

> **Reproducibility guard.** `lake exe cache get` compiles Mathlib's own `cache`
> tool locally, which leaves a few non-deterministic artifacts (link-time hash-map
> order). The FOD scrubs them — critically `bin/cache.hash`, the sole leak that
> made two independent builds disagree. It also drops the `scripts/` trees, whose
> nixpkgs-patched `#!/nix/store/…-bash` shebangs are the only store references
> cache-get leaves (illegal in an FOD). A fail-loud guard aborts the build, naming
> the offending files, if any store reference survives — so a future Mathlib rev
> that adds one fails visibly instead of with nix's opaque late rejection.
