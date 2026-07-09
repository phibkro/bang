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

## Run a bang program

You need [Nix](https://nixos.org/download) with flakes enabled — nothing else
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
diagnostics). `bang --help` lists flags and exit codes. Pass `--compiled` to run
the *verified calculated machine* instead of the kernel oracle — same program,
same value (ADR-0016).

**Cold-start cost.** Measured from a fresh clone: `cache get` ~2 min (decompresses
Mathlib's prebuilt `.olean` files; **add several minutes to download ~2 GB from the
Lean community CDN if your nix store doesn't already have them**), then `lake build
bang` ~4 min (compiles the bang library + runner). Budget **~10–15 min** on a cold
machine (network-bound for the fetch, CPU-bound for the build); a warm rebuild of
just the runner is ~2 min. Mathlib is a *build-time* dependency only — the resulting
`bang` binary is native and links nothing but glibc.

> A pure `nix build .#bang` / `nix run github:phibkro/bang` is **not yet
> available**: it would require Mathlib present as oleans inside the nix build
> sandbox (a multi-GB source build, or a fixed-output cache fetch), which isn't
> wired up. Tracked as a follow-up — see [issue below](#packaging-follow-up).
> Until then, the `nix develop` path above is the supported install.

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

## Packaging follow-up

`nix run github:phibkro/bang -- eval "1 + 2"` (a pure flake `package`/`app`
output) is the target that would let a stranger run bang with a single command,
no clone. It is **not yet wired up**. What blocks it, for whoever picks it up:

- The `bang` exe imports `Bang.Frontend.Surface`, which transitively pulls in
  four `Bang/Core/*` modules that `import Mathlib` (Finset semilattice for effect
  rows). So **Mathlib is a build-time dependency** — its `.olean` files must be
  present before `lake build bang` runs.
- The exe's *runtime* closure is tiny (native binary, links only glibc +
  libgcc_s — Lean statically links its runtime; no gmp, no oleans). So the only
  hard part is the build.
- Two candidate pure paths, both non-trivial:
  1. **Build Mathlib from source** in the derivation — correct but multi-GB
     closure and hours of compile; needs `lean4-nix`
     (`github:lenianiva/lean4-nix`) to express lake deps as derivations.
  2. **Fixed-output derivation that runs `lake exe cache get`** — fetches the
     prebuilt oleans from the Lean CDN (network is allowed in an FOD), then a
     second derivation runs `lake build bang`. Lighter, but fragile: the FOD hash
     must be pinned and re-pinned when the cache changes.
- Wrapping a *pre-built* binary in a `nix run` app is **not** acceptable (there
  is no binary hosting, and it wouldn't be reproducible).

Until one of those lands, the `nix develop -c lake build bang` path in
[Run a bang program](#run-a-bang-program) is the supported install.
