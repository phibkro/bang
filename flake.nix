{
  description = "bang-lang effect-row verified oracle (Lean 4 / F*) + differential harness";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPkgs = pkgs.ocamlPackages;
        harnessDeps = [ pkgs.nodejs_22 pkgs.nodePackages.pnpm ];
      in {
        # ---- DEFAULT: Lean 4 oracle (recommended substrate) ----
        # Lean's own pinning (lean-toolchain + lake-manifest.json) is the real
        # reproducibility mechanism; elan resolves the exact compiler from
        # lean-toolchain. NUDGE: for bit-identical Nix purity on Mathlib, swap
        # elan for a lean4-nix overlay; elan fetches toolchains at first use.
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.elan pkgs.git pkgs.curl pkgs.cacert pkgs.gmp
          ] ++ harnessDeps;
          shellHook = ''
            echo "bang-effectrow-oracle — Lean dev shell"
            echo "  make selfcheck     # zero-dep algorithm check (Node only)"
            echo "  make lean-oracle   # lake exe cache get + lake build"
            echo "  make harness-lean  # differential suite vs the Lean oracle"
            echo "  make check-lean    # all of the above"
          '';
        };

        # ---- ALTERNATE: original F* / OCaml oracle ----
        devShells.fstar = pkgs.mkShell {
          buildInputs = [
            pkgs.fstar pkgs.z3 pkgs.ocaml pkgs.dune_3
            ocamlPkgs.findlib ocamlPkgs.yojson ocamlPkgs.zarith ocamlPkgs.batteries
          ] ++ harnessDeps;
          shellHook = ''
            echo "bang-effectrow-oracle — F* dev shell"
            export FSTAR_LIB_PATH="${pkgs.fstar}/lib/fstar"
          '';
        };
      });
}
