# F* extraction of the verified brain -> generated/Bang_EffectRow.ml
# Requires the F* toolchain (provided by the repo flake: `nix develop`).
FSTAR ?= fstar.exe
SRC   := src/Bang.EffectRow.fst
OUT   := generated

.PHONY: verify extract build clean

verify:
	$(FSTAR) $(SRC)

# NUDGE: --codegen OCaml is the first-class backend. We extract only the
# computational core; the lemmas (Lemma-typed) are erased automatically.
extract: verify
	$(FSTAR) --codegen OCaml --extract Bang.EffectRow --odir $(OUT) $(SRC)
	@echo ">> overwrote $(OUT)/Bang_EffectRow.ml with verified extraction"

build:
	dune build ./ml/main.exe
	@echo ">> oracle at: $$(pwd)/_build/default/ml/main.exe"

clean:
	dune clean
