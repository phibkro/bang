# Pure packaging of the `bang` runner CLI (issue #63).
#
# `nix run github:phibkro/bang -- eval "1 + 2"` → 3, fully reproducible, no clone.
#
# THE PROBLEM this file solves (see README "Packaging" + issue #63): the `bang`
# exe transitively imports four `Bang/Core/*` modules that `import Mathlib`, so
# Mathlib `.olean`s must exist BEFORE `lake build bang`. Building Mathlib from
# source is multi-GB / hours. Instead we fetch the prebuilt oleans the same way
# the dev shell does (`lake exe cache get`, Lean's Azure CDN) — but network is
# forbidden in a pure derivation, so that step lives in a FIXED-OUTPUT derivation
# (network allowed, output pinned by hash). A second, pure derivation then runs
# `lake build bang` offline against those deps. The exe's runtime closure is
# trivial (glibc + libgcc_s; Lean statically links its runtime).
#
# THREE DERIVATIONS:
#   toolchain  — the official Lean v4.30.0 release, autoPatchelf'd to run on Nix.
#   deps (FOD) — `lake exe cache get` → the resolved `.lake/packages` tree.
#   bang       — pure `lake build bang` against toolchain + deps.
#
# ── RE-PINNING (when `lean-toolchain` or `lake-manifest.json` changes) ─────────
#   toolchainHash: bump `version`/url to the new Lean release, set the hash to
#     lib.fakeHash, build once, copy the "got:" hash from the error.
#   depsHash: the FOD re-pins whenever the resolved dep set changes (a Mathlib
#     rev bump in lake-manifest.json, a toolchain bump). Same procedure: set to
#     lib.fakeHash, `nix build .#deps` (or let `.#default` pull it), copy "got:".
#   A STALE depsHash fails LOUD with nix's "hash mismatch … got: <new>" — never
#   silently. That error IS the re-pin instruction.
# ──────────────────────────────────────────────────────────────────────────────

{
  pkgs,
  # Source of the bang-lang repo (this flake's own tree).
  src,
  leanVersion ? "4.30.0",
  # Hash of the official Lean release tarball for `leanVersion` (see re-pin above).
  toolchainHash ? "sha256-Ta10FBwsEZyhqmJmVr6DuOFCOK+6lycf178es/CBsxk=",
  # Hash of the `lake exe cache get` output tree (see re-pin above).
  depsHash ? "sha256-L2VaBRxB9tNXkt9kjXsLUEgaA7RgEx9UtOKWXZ2umCI=",
}:

let
  lib = pkgs.lib;

  # ── toolchain ───────────────────────────────────────────────────────────────
  # The official Lean release binaries link against the standard
  # /lib64/ld-linux-x86-64.so.2 interpreter, absent on Nix; autoPatchelf rewrites
  # them to the nix-store glibc. `autoPatchelfIgnoreMissingDeps` because the
  # bundled clang/lld pull optional libs we never invoke.
  toolchain = pkgs.stdenv.mkDerivation {
    pname = "lean4-toolchain";
    version = leanVersion;
    src = pkgs.fetchurl {
      url = "https://github.com/leanprover/lean4/releases/download/v${leanVersion}/lean-${leanVersion}-linux.tar.zst";
      hash = toolchainHash;
    };
    nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.zstd ];
    buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.gmp pkgs.zlib pkgs.libuv ];
    dontConfigure = true;
    dontBuild = true;
    installPhase = "mkdir -p $out && cp -r . $out/";
    autoPatchelfIgnoreMissingDeps = true;
  };

  # leanc's bundled clang emits binaries with the /lib64 interpreter (unusable in
  # a pure sandbox → `could not execute external process` when lake runs a
  # freshly-built exe, e.g. Mathlib's `cache` tool, or our `bang`). Pointing
  # LEAN_CC at the nixpkgs cc wrapper makes it inject the nix-store dynamic
  # linker; NIX_LDFLAGS hands that cc the toolchain's own libc++/libuv so the
  # link resolves. This env is shared by BOTH the FOD and the pure build.
  leanCcEnv = {
    LEAN_CC = "${pkgs.stdenv.cc}/bin/cc";
    NIX_LDFLAGS = "-L${toolchain}/lib -L${toolchain}/lib/lean -rpath ${toolchain}/lib -rpath ${toolchain}/lib/lean";
  };

  # ── deps (fixed-output) ──────────────────────────────────────────────────────
  deps = pkgs.stdenv.mkDerivation (leanCcEnv // {
    pname = "bang-lake-deps";
    version = leanVersion;
    dontUnpack = true;

    nativeBuildInputs = [ toolchain pkgs.cacert pkgs.git pkgs.curl pkgs.stdenv.cc ];

    outputHashMode = "recursive";
    outputHashAlgo = "sha256";
    outputHash = depsHash;

    buildPhase = ''
      export HOME=$TMPDIR
      export PATH=${toolchain}/bin:$PATH
      mkdir -p work && cd work
      # Only the files lake needs to RESOLVE deps — not Bang/** or Main.lean, so
      # source edits never invalidate the (expensive) FOD.
      cp ${src}/lakefile.toml ${src}/lake-manifest.json ${src}/lean-toolchain .
      chmod +w lakefile.toml lake-manifest.json lean-toolchain
      lake exe cache get
    '';

    installPhase = ''
      mkdir -p $out
      cp -r .lake/packages $out/packages

      # ── determinism scrub ──
      # Strip every `.git` ENTIRELY: `git clone`'s packs/reflog/index are
      # non-deterministic. The pure `bang` build re-synthesises a minimal
      # deterministic `.git` per package from the manifest (see its buildPhase).
      find $out/packages -type d -name .git -prune -exec rm -rf {} +

      # Remove the build artifacts of Mathlib's `cache` tool. `lake exe cache get`
      # compiles that tool locally, and ITS artifacts are the ONLY non-deterministic
      # content cache-get leaves (the downloaded Mathlib oleans + their .trace/.hash
      # are bit-identical run to run). Verified by diffing two independent real
      # cache-gets (each with the `cache` exe compiled): after this exact removal
      # list the two package trees are BYTE-IDENTICAL. The load-bearing offender is
      # `bin/cache.hash` — lake's 16-byte build-hash of the `cache` exe, which
      # varies run-to-run (link-time hash-map iteration order) exactly like the exe
      # itself; leaving it in was the FOD's sole reproducibility leak.
      # The pure build never rebuilds `cache`, so these are dead weight; dropping
      # them makes this FOD reproducible.
      rm -rf $out/packages/mathlib/.lake/build/bin/cache \
             $out/packages/mathlib/.lake/build/bin/cache.hash \
             $out/packages/mathlib/.lake/build/bin/cache.rsp \
             $out/packages/mathlib/.lake/build/bin/cache.trace \
             $out/packages/mathlib/.lake/build/ir/Cache \
             $out/packages/mathlib/.lake/build/lib/lean/Cache
      # batteries `.export.trace`/`.barrel.trace` are likewise cache-tool link
      # inputs (hash-map iteration order); batteries' OLEANS stay untouched.
      find $out/packages/batteries -name '*.export.trace' -delete
      find $out/packages/batteries -name '*.barrel.trace' -delete

      # ── store-reference scrub (FOD hermeticity) ──
      # An FOD MUST NOT reference other store paths (its hash is content-only).
      # nixpkgs `patchShebangs` rewrites the `#!/usr/bin/env bash` line of every
      # `scripts/*.sh` in mathlib/batteries to a `/nix/store/…-bash` shebang — the
      # ONLY store references cache-get leaves. These are mathlib/batteries dev/CI
      # helpers (lint, bench, adaptation-PR); `lake build bang` never runs them, so
      # drop the whole `scripts/` tree per package.
      find $out/packages -maxdepth 2 -type d -name scripts -prune -exec rm -rf {} +

      # Fail LOUD if any store reference survives — a stale mathlib rev could add a
      # store-ref outside scripts/, which nix would otherwise reject much later with
      # the opaque "fixed-output derivations must not reference store paths". This
      # turns that into a located, actionable failure at the point of the leak.
      if grep -rlI '/nix/store/[a-z0-9]\{32\}-' $out/packages 2>/dev/null | grep -q .; then
        echo "ERROR: deps FOD still references store paths after scrub:" >&2
        grep -rlI '/nix/store/[a-z0-9]\{32\}-' $out/packages >&2
        exit 1
      fi
    '';
  });

  # ── bang (pure) ──────────────────────────────────────────────────────────────
  bang = pkgs.stdenv.mkDerivation (leanCcEnv // {
    pname = "bang";
    version = "0.1.1";
    inherit src;

    nativeBuildInputs = [ toolchain pkgs.stdenv.cc pkgs.git pkgs.jq ];

    buildPhase = ''
      export HOME=$TMPDIR
      export PATH=${toolchain}/bin:$PATH
      git config --global --add safe.directory '*'

      # A writable, real copy of the deps tree (reflink = cheap CoW).
      mkdir -p .lake
      cp -r --reflink=auto ${deps}/packages .lake/packages
      chmod -R u+w .lake/packages

      # lake re-materialises each git dep on build (PackageEntry.materialize): it
      # runs `git rev-parse HEAD` and `git remote get-url origin`, and RE-CLONES
      # (fatal offline) if either fails or HEAD ≠ the manifest rev. The FOD
      # stripped every `.git`, so synthesise a MINIMAL deterministic one per
      # package from lake-manifest.json: `git init` + a detached HEAD holding the
      # raw rev (git echoes it back from `rev-parse` without needing the object) +
      # the origin remote. This is the offline-safe branch lake takes when
      # HEAD == rev, so no network is touched.
      jq -r '.packages[] | select(.type=="git") | [.name, .rev, .url] | @tsv' lake-manifest.json |
      while IFS=$'\t' read -r name rev url; do
        d=".lake/packages/$name"
        [ -d "$d" ] || continue
        rm -rf "$d/.git"
        git -C "$d" init -q
        git -C "$d" remote add origin "$url"
        printf '%s\n' "$rev" > "$d/.git/HEAD"
      done

      lake build bang
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp .lake/build/bin/bang $out/bin/bang
    '';

    meta = {
      description = "The bang-lang runner CLI (eval/run a .bang program)";
      mainProgram = "bang";
      platforms = [ "x86_64-linux" ];
    };
  });
in
{
  inherit toolchain deps bang;
}
