{
  description = "bang-lang — effect-typed language with verified graded-CBPV → WasmFX compilation (Lean 4)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        # Lean 4 dev shell.
        # elan resolves the toolchain from lean-toolchain on first use.
        # Mathlib oleans pulled via `lake exe cache get` (Azure CDN; multi-GB).
        # Direnv auto-enters via .envrc.
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.elan          # Lean version manager (reads lean-toolchain)
            pkgs.git
            pkgs.curl
            pkgs.cacert        # SSL for lake to fetch deps
            pkgs.gmp           # Lean runtime dep
            pkgs.nodejs_22     # for tools/selfcheck.mjs
            pkgs.poppler-utils # pdftotext for paper-reading scripts
          ];
          shellHook = ''
            echo "bang-lang — Lean 4 dev shell"
            echo ""
            echo "  make verify          # selfcheck + build + audit"
            echo "  make build           # lake exe cache get + lake build"
            echo "  make audit           # static guards + #print axioms gate"
            echo "  make selfcheck       # zero-dep Node smoke for row unifier"
            echo ""
            echo "  bash tools/check.sh [FILE]   # fast per-file error check"
            echo "  bash tools/burndown.sh       # Phase B burndown chart"
            echo "  bash tools/install-hooks.sh  # one-time: link git pre-commit"
            echo ""
            echo "Read CLAUDE.md → CONTEXT.md → ROADMAP.md to orient."
          '';
        };
      });
}
