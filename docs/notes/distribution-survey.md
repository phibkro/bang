<!-- note-status: active -->
# Distribution survey — a more accessible install story than "ride Nix"

> Research survey (operator-posed 2026-07-11): "a more accessible distribution story than
> riding on Nix." Census claims are web-sourced (citations §7); bang-state claims are
> repo-cited. Docs-only. **Headline: the rung-0 ladder is already BUILT** (`release.yml` +
> `tools/install.sh` + `tools/release-artifact.sh`) — this survey grades it, names the
> two-line change that widens it, and draws the honest ceiling.

## 0. The ground truth (measured, not assumed)

The `bang` binary is a self-contained native ELF — Mathlib is a **build-time-only** dep
(the `.olean`s never ship; `Prelude.bang` is `include_str`-embedded, ADR-0098).

| fact | value | source |
|---|---|---|
| runtime links | `libc, libm, libdl, libpthread, libgcc_s` — **all glibc + libgcc_s**, nothing exotic | `ldd` on the built exe |
| size (unstripped / stripped) | **116 MB / 78 MB** | `stat` on `.lake/build/bin/bang` + `strip` |
| ELF interp (as-built) | `/nix/store/…/ld-linux` — **NOT portable**; `release-artifact.sh` patchelf-rewrites it to `/lib64/ld-linux-x86-64.so.2` | `file` + the script |
| static-linkable? | **No** (glibc dynamic). Lean statically links only *its own runtime*; libc stays dynamic | Lean platform docs (§7) — no musl distribution |

The 78 MB stripped size is the real cost line: Lean folds its runtime + a large slice of
compiled library code into the exe. It is ~1.5× a Zig tarball, but it is **one file with
zero runtime deps to install** — the property that matters for a `curl | sh`.

## 1. The census — how comparable projects ship (2026)

| project | producer | channels shipped | version mgr | one lesson for bang |
|---|---|---|---|---|
| **Lean itself** | CI per Tier-1 platform | **elan** (rustup-style) + GitHub Releases | elan | elan is *toolchain* mgmt — overkill for a single end-user exe |
| **Zig** | self-hosted cross-compile | **fully-static tarballs** per platform (~50 MiB) + brew + scoop + winget + nix | none (tarball IS the truth) | static-tarball is the gold standard bang **can't reach** (glibc) |
| **Gleam** | CI (Rust exe) | GitHub Releases + **brew bottles (6 platforms)** + nixpkgs + scoop + winget + apk/pacman/zypper | none | **one small binary → every package mgr took it**; solo-author, community-packaged |
| **Rust** | project CI | **rustup** + distro packages + GitHub Releases | rustup | rustup earns its keep only once you have multiple toolchains/targets |
| **Elixir** | — | needs the **BEAM installed first** (asdf/brew/…) | asdf-ish | *cautionary*: a runtime-dependency install story is the friction bang **avoids by being native** |
| **esbuild / biome / bun** | CI matrix | **npm** (`optionalDependencies` + `os`/`cpu` fields) + brew + curl | none | the npm-wrapped-binary pattern — reach, but supply-chain + flag-conflict controversy (§7) |

**Table-stakes in 2026** (what a language is expected to have): (1) a `curl \| sh` installer,
(2) GitHub Releases with a per-platform binary matrix, (3) a **brew tap**, (4) scoop/winget
for Windows, (5) *optionally* an npm-wrapped binary, (6) a container image. Nix is a
**contributor/power-user** channel, never the front door.

## 2. bang feasibility per channel — the FOD build is the producer

The `nix build .#bang` FOD (issue #63, `nix/bang.nix`) is a **reproducible binary factory**:
`toolchain` (Lean release, autoPatchelf'd) → `deps` (FOD: `lake exe cache get`, hash-pinned)
→ `bang` (pure `lake build`). CI already drives the *non-FOD* path (`nix develop -c lake build
bang`) in `release.yml`. Per channel:

| channel | feasible? | the work | blocker / note |
|---|---|---|---|
| **curl installer** | ✅ **SHIPPED (3 triples)** | `tools/install.sh` (platform-detect → GH Release asset → `~/.local/bin`) | covers x86_64-linux, aarch64-linux, aarch64-darwin; errors loud + names alternatives elsewhere |
| **GH Release x86_64-linux** | ✅ **SHIPPED** | `release.yml` matrix row + `release-artifact.sh` (strip + **de-nix the ELF interp** + smoke) | none — live; smoke-verified locally |
| **GH Release aarch64-linux** | ✅ **SHIPPED** | `release.yml` matrix row (`ubuntu-24.04-arm`); Lean Tier-1 (glibc 2.27+); same ELF de-nix path | untested-until-first-run (no arm64 runner in this lane); build path identical to x86_64 |
| **GH Release aarch64-darwin** | 🟡 **SHIPPED, one honest gap** | `release.yml` matrix row (`macos-latest`, Apple Silicon); Lean Tier-1; `nix develop -c lake build` path (not the x86_64-gated FOD) | strip + smoke only — Mach-O dylib de-nixing (`install_name_tool`) is UNVERIFIED until the first darwin run; the run prints `otool -L` so a /nix/store leak shows. Loudly flagged |
| **brew tap** | 🟡 rung 1 | a `homebrew-bang` tap repo w/ a formula pointing at the GH Release asset | trivial once ≥1 platform ships; Gleam's exact path |
| **scoop / winget** | 🔴 rung 2 | Windows binary first | Lean *is* Tier-1 on Windows, but see §4 |
| **npm-wrapped** | 🟡 rung 2 (assess) | wrapper pkg + per-platform `@bang/<triple>` optionalDeps | **78 MB × N platforms** on npm is heavy; supply-chain optics; defer |
| **container image** | 🟢 cheap anytime | `FROM debian-slim` + COPY the de-nixed binary | near-free; good for CI-of-CI users |
| **nix run / nix build** | ✅ **SHIPPED** | the FOD | stays the **contributor** path, unchanged |

## 3. THE RECOMMENDED LADDER

```
rung 0  (v0.2, DONE — 3-row matrix landed)   curl installer + GH Release binary
        ├── x86_64-linux ....... ✅ ships + smoke-verified locally (release.yml + install.sh)
        ├── aarch64-linux ...... ✅ matrix row (ubuntu-24.04-arm; Lean Tier-1) — untested until first run
        └── aarch64-darwin ..... ✅ matrix row (macos-latest; Lean Tier-1) — strip+smoke only,
                                  dylib de-nix UNVERIFIED until first darwin run (loud gap)
                                  install.sh's platform `case` widened to all three
rung 1  (fast-follow)         brew tap  (homebrew-bang, formula → GH Release asset)
rung 2  (later / on-demand)   container image · npm-wrapped · Windows+scoop/winget
never  (contributor lane)     nix develop  — the build-from-source path, unchanged
```

**Verification path (operator):** the matrix is testable WITHOUT cutting a tag — a
`workflow_dispatch` run (Actions → Release → Run workflow on `feat-release-matrix`)
builds + smoke-tests + uploads all three as CI artifacts but does NOT publish a Release
(the create step is tag-gated). Use that to prove the arm64 + darwin rows green before
the first real tag. A cachix/magic-nix-cache layer would cut per-row cold-build cost but
needs an auth secret — the operator's config step, not added here.

**Rung-0 verdict:** the curl-installer + x86_64-linux binary is **already the front door**
and correctly de-nixed. The single highest-leverage move is **widening the release matrix
to aarch64-linux + aarch64-darwin** — both are Lean Tier-1, and the `release.yml` header
already sketches the matrix promotion. That turns "one binary" into "the three platforms
that cover ~all bang users," which is what makes the story genuinely "more accessible than
Nix."

## 4. The three requested verdicts

- **Rung-0 verdict** — Done across all three Tier-1 platforms (the matrix landed on
  `feat-release-matrix`). It is NOT Nix-gated for the end user (the binary is native; Nix is
  only the *build* substrate in CI). x86_64-linux is smoke-verified locally; the arm64 and
  darwin rows are wired but untested until the first `workflow_dispatch`/tag run (the darwin
  dylib-de-nix gap is the one loud caveat, see §5).
- **Static-linking verdict** — **Not available.** Lean ships no musl/static-glibc target;
  the runtime dynamically links glibc. bang therefore **cannot** match Zig's "static tarball
  runs on every distro." The mitigation is already in place and sufficient: `release-artifact.sh`
  de-nixes the ELF interpreter to the distro-standard loader, and glibc-2.26+ (Lean's Tier-1
  floor) covers every mainstream distro from ~2018 on. Ship glibc-dynamic, document the floor.
- **Windows verdict** — **Not worth v0.x effort.** Lean *is* Tier-1 on Windows, so it is
  *possible*, but: (a) the whole toolchain/FOD path is Linux-shaped, (b) scoop/winget are
  downstream of a Windows binary that doesn't exist yet, (c) bang's audience (Lean/PL/agent
  users) skews non-Windows. Defer to post-1.0; revisit only if a concrete user asks.

## 5. CI shape (LANDED on `feat-release-matrix`)

`release.yml` now runs the 3-row matrix. The shape:

```
on: push tags v*  (+ workflow_dispatch for dry-run — builds+uploads CI artifacts,
                     does NOT publish a Release; the create step is tag-gated)
strategy: fail-fast:false  (independent artifacts — one row's failure ≠ cancel the rest)
matrix.include:
  - { os: ubuntu-latest,    triple: x86_64-linux  }   # ← live, smoke-verified locally
  - { os: ubuntu-24.04-arm, triple: aarch64-linux }   # ← GH arm64 runner
  - { os: macos-latest,     triple: aarch64-darwin}   # ← Apple Silicon
per row:
  nix-installer → cache(elan+.lake, keyed per-triple) → `lake exe cache get`
  → `lake build bang` → release-artifact.sh <ver> <triple>
  → upload CI artifact  →  (tag only) create-Release-if-absent + upload asset
```

`release-artifact.sh` guards the de-nix by `case "$TRIPLE"`: on `*-linux` it strips +
patchelf-rewrites the ELF interpreter (the portability move); on `*-darwin` it strips +
prints `otool -L` linkage (Mach-O has no ELF interp). **The one honest gap:** Mach-O
dylib de-nixing (`install_name_tool` to rewrite any hardcoded `/nix/store/…*.dylib`) is
NOT done — the exact dylib set a `bang` Mach-O carries is unverifiable without a darwin
machine. The smoke set proves the binary is self-consistent ON the runner; the residual
risk is a /nix/store dylib that resolves on the CI Mac but not on a stranger's — the
`otool -L` dump in the build log exposes it, and both the release note and this section
name it. If the first darwin run shows a leak, add the `install_name_tool` arm then.
The tag-shared Release is created once (create-if-absent guard) and each row uploads
its own asset with `--clobber`. `install.sh`'s platform `case` matches all three triples.

## 6. Proposed issues (do not file)

1. ~~**Widen the release matrix to aarch64-linux + aarch64-darwin**~~ — ✅ **LANDED** on
   `feat-release-matrix`: 3-row matrix, `patchelf` guarded for Mach-O, `install.sh` case
   extended. Remaining: the operator dry-runs `workflow_dispatch` to prove the arm64 +
   darwin rows, and closes the darwin dylib-de-nix gap if the first run shows a leak.
2. **Homebrew tap (`phibkro/homebrew-bang`)** — formula pulling the GH Release asset; the
   Gleam pattern. Gated on issue 1 landing ≥1 asset. *Rung 1.*
3. **Publish a container image** — `FROM debian:stable-slim` + the de-nixed binary; near-free
   CI step, good for agent/CI users. *Rung 2, cheap.*
4. **(assess-only) npm-wrapped binary** — `optionalDependencies` matrix; weigh the 78 MB × N
   payload + supply-chain optics before committing. *Rung 2, contested.*

## 7. Citations

- Lean supported platforms (Tier-1/2; glibc mins; no musl/static story):
  <https://lean-lang.org/doc/reference/latest/platforms/>
- elan (Lean toolchain mgr): <https://github.com/leanprover/elan>
- Zig static tarballs (~50 MiB, "tarball is the source of truth"):
  <https://ziglang.org/download/> · <https://ziglang.org/learn/overview/>
- Gleam install matrix (brew bottles ×6, nixpkgs, scoop/winget/apk/…):
  <https://gleam.run/getting-started/installing/> · <https://formulae.brew.sh/formula/gleam>
- npm binary-distribution pattern (esbuild `optionalDependencies` + controversy):
  <https://deepwiki.com/evanw/esbuild/6.2-platform-specific-binaries> ·
  <https://github.com/evanw/esbuild/issues/789>
- Repo-cited: `nix/bang.nix`, `.github/workflows/release.yml`, `tools/install.sh`,
  `tools/release-artifact.sh`, README §Install/§Packaging, issue #63.
