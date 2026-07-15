{
  description = "bang-lang — effect-typed language with verified graded-CBPV → WasmFX compilation (Lean 4)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Pure packaging (issue #63). Only x86_64-linux: the toolchain derivation
        # fetches the linux Lean release tarball. Other systems get the dev shell
        # only (build from source via `nix develop`).
        bangPkgs =
          if system == "x86_64-linux" then
            import ./nix/bang.nix { inherit pkgs; src = self; }
          else
            null;
      in
      {
        # Cheap NO-NETWORK static gate (plan 011 rider) — selfcheck + the fitness legs
        # that touch neither `lake` (no toolchain/oleans in a pure sandbox) nor `.git`
        # (a derivation's `src` is a filtered copy of tracked files, not a real git repo —
        # scripts needing `git log`/`git ls-files`/`git status` history are NOT included
        # here; they stay in `just fitness`/`just verify`, run with real git available).
        # This is NOT verify-as-flake-check (network wall via `lake exe cache get` — the
        # #63 FOD pattern is the future path for that, tracked as a follow-up, not this
        # rider). `nix flake check` runs this on every system (pure file/text checks,
        # no toolchain dependency, unlike `packages`/`apps` which are x86_64-linux-only).
        checks.static =
          pkgs.runCommand "bang-static-checks"
            {
              src = self;
              nativeBuildInputs = [
                (pkgs.python3.withPackages (ps: [ ps.jsonschema ]))
                pkgs.nodejs_22
              ];
            }
            ''
              cp -r $src/. .
              chmod -R u+w .
              node tools/selfcheck.mjs
              bash tools/check-primitives.sh
              bash tools/arch-check.sh
              bash tools/check-audit-sync.sh
              bash tools/check-all-modules.sh
              python3 tools/gen-import-graph.py --check
              touch $out
            '';

        packages = pkgs.lib.optionalAttrs (bangPkgs != null) {
          default = bangPkgs.bang;
          bang = bangPkgs.bang;
          # Exposed for re-pinning / debugging the two-stage build.
          deps = bangPkgs.deps;
          toolchain = bangPkgs.toolchain;
        };

        apps = pkgs.lib.optionalAttrs (bangPkgs != null) {
          default = {
            type = "app";
            program = "${bangPkgs.bang}/bin/bang";
          };
        };

        # Lean 4 dev shell.
        # elan resolves the toolchain from lean-toolchain on first use.
        # Mathlib oleans pulled via `lake exe cache get` (Azure CDN; multi-GB).
        # Direnv auto-enters via .envrc.
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.elan # Lean version manager (reads lean-toolchain)
            pkgs.just # task runner (see ./justfile)
            pkgs.jq # JSON for Claude Code hook scripts
            pkgs.git
            pkgs.curl
            pkgs.cacert # SSL for lake to fetch deps
            pkgs.gmp # Lean runtime dep
            pkgs.nodejs_22 # for tools/selfcheck.mjs
            (pkgs.python3.withPackages (ps: [ ps.jsonschema ])) # docfact generators + JSON Schema validation
            pkgs.ruff # Python formatting + linting (`just autoquality`)
            pkgs.shellcheck # shell linting (`just autoquality`)
            pkgs.poppler-utils # pdftotext for paper-reading scripts
            pkgs.mermaid-cli # mmdc — validate the generated module-graph mermaid (gen-import-graph.py --validate)
          ];
          shellHook = ''
            echo "bang-lang — Lean 4 dev shell"
            echo ""
            echo "  just                 # list available recipes"
            echo "  just verify          # selfcheck + build + audit (default gate)"
            echo "  just check [FILE]    # fast per-file error check"
            echo "  just burndown        # Phase B burndown chart"
            echo "  just loogle QUERY    # Mathlib type-signature search"
            echo "  just install-hooks   # one-time: link git pre-commit"
            echo ""
            echo "Fresh? Read ONBOARDING.md → CLAUDE.md → ROADMAP.md → CONTEXT.md"
          '';
        };

        # Opt-in production docs shell. Keep Bun + Chromium out of the default
        # Lean loop; `nix develop .#site --command just site-build` is the one
        # local equivalent of the CI/Pages rendering gate.
        devShells.site = pkgs.mkShell {
          buildInputs = [ pkgs.bun pkgs.chromium pkgs.just pkgs.git ];
          PUPPETEER_EXECUTABLE_PATH = "${pkgs.chromium}/bin/chromium";
          shellHook = ''
            echo "bang-lang — strict Vocs site shell"
            echo "  just site-build      # locked install + strict Mermaid + Vocs build"
          '';
        };
      }
    );
}
