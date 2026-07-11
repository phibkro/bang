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
| **curl installer** | ✅ **SHIPPED** | `tools/install.sh` (platform-detect → GH Release asset → `~/.local/bin`) | x86_64-linux only today; errors loud on other platforms |
| **GH Release x86_64-linux** | ✅ **SHIPPED** | `release.yml` (tag-triggered) + `release-artifact.sh` (strip + **de-nix the ELF interp** + smoke) | none — this is rung 0, live |
| **GH Release aarch64-linux** | 🟡 **2-line change** | add a matrix row; Lean Tier-1 supports it (glibc 2.27+) | needs an aarch64 runner (GH-hosted arm64 exists) or QEMU/cross |
| **GH Release aarch64-darwin** | 🟡 **matrix row** | add `macos-latest` (Apple Silicon); Lean Tier-1 | the FOD is x86_64-linux-gated in flake.nix — darwin uses the `nix develop -c lake build` path (what `release.yml` already does). Local darwin check machine exists (intel-Mac memory) |
| **brew tap** | 🟡 rung 1 | a `homebrew-bang` tap repo w/ a formula pointing at the GH Release asset | trivial once ≥1 platform ships; Gleam's exact path |
| **scoop / winget** | 🔴 rung 2 | Windows binary first | Lean *is* Tier-1 on Windows, but see §4 |
| **npm-wrapped** | 🟡 rung 2 (assess) | wrapper pkg + per-platform `@bang/<triple>` optionalDeps | **78 MB × N platforms** on npm is heavy; supply-chain optics; defer |
| **container image** | 🟢 cheap anytime | `FROM debian-slim` + COPY the de-nixed binary | near-free; good for CI-of-CI users |
| **nix run / nix build** | ✅ **SHIPPED** | the FOD | stays the **contributor** path, unchanged |

## 3. THE RECOMMENDED LADDER

```
rung 0  (v0.2, MOSTLY DONE)   curl installer + GH Release binary
        ├── x86_64-linux ....... ✅ already ships (release.yml + install.sh)
        ├── aarch64-linux ...... + one matrix row (Lean Tier-1)
        └── aarch64-darwin ..... + one matrix row (Apple Silicon; Lean Tier-1)
                                  → widen install.sh's platform `case` to match
rung 1  (fast-follow)         brew tap  (homebrew-bang, formula → GH Release asset)
rung 2  (later / on-demand)   container image · npm-wrapped · Windows+scoop/winget
never  (contributor lane)     nix develop  — the build-from-source path, unchanged
```

**Rung-0 verdict:** the curl-installer + x86_64-linux binary is **already the front door**
and correctly de-nixed. The single highest-leverage move is **widening the release matrix
to aarch64-linux + aarch64-darwin** — both are Lean Tier-1, and the `release.yml` header
already sketches the matrix promotion. That turns "one binary" into "the three platforms
that cover ~all bang users," which is what makes the story genuinely "more accessible than
Nix."

## 4. The three requested verdicts

- **Rung-0 verdict** — Done and correct for x86_64-linux. It is NOT Nix-gated for the end
  user (the binary is native; Nix is only the *build* substrate in CI). The gap is **breadth,
  not existence**: two matrix rows away from the table-stakes 3-platform matrix.
- **Static-linking verdict** — **Not available.** Lean ships no musl/static-glibc target;
  the runtime dynamically links glibc. bang therefore **cannot** match Zig's "static tarball
  runs on every distro." The mitigation is already in place and sufficient: `release-artifact.sh`
  de-nixes the ELF interpreter to the distro-standard loader, and glibc-2.26+ (Lean's Tier-1
  floor) covers every mainstream distro from ~2018 on. Ship glibc-dynamic, document the floor.
- **Windows verdict** — **Not worth v0.x effort.** Lean *is* Tier-1 on Windows, so it is
  *possible*, but: (a) the whole toolchain/FOD path is Linux-shaped, (b) scoop/winget are
  downstream of a Windows binary that doesn't exist yet, (c) bang's audience (Lean/PL/agent
  users) skews non-Windows. Defer to post-1.0; revisit only if a concrete user asks.

## 5. CI sketch (shape, not YAML)

`release.yml` already has the skeleton and a commented matrix-promotion block. The shape:

```
on: push tags v*  (+ workflow_dispatch for dry-run, tag-gated publish)
strategy.matrix:
  - { os: ubuntu-latest,        triple: x86_64-linux  }   # ← live
  - { os: ubuntu-24.04-arm,     triple: aarch64-linux }   # ← add (GH arm64 runner)
  - { os: macos-latest,         triple: aarch64-darwin}   # ← add (Apple Silicon)
per row:
  nix-installer → cache(elan+.lake) → `lake exe cache get` → `lake build bang`
  → release-artifact.sh <ver> <triple>   (strip + de-nix + smoke on the stripped exe)
  → upload asset  →  (tag only) gh release create --generate-notes
```

The strip/de-nix/smoke steps in `release-artifact.sh` are **already platform-agnostic** (the
header says so); darwin has no ELF interp to rewrite (Mach-O) — a small `case "$TRIPLE"` guard
around the `patchelf` line handles that. `install.sh`'s platform `case` widens to match the
three triples. No new machinery — three matrix rows and two `case` arms.

## 6. Proposed issues (do not file)

1. **Widen the release matrix to aarch64-linux + aarch64-darwin** — promote `release.yml`'s
   commented matrix; guard the `patchelf` line for Mach-O; extend `install.sh`'s platform case.
   *The rung-0 completion; highest leverage.*
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
