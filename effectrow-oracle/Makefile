.PHONY: check check-lean selfcheck verify oracle lean-oracle harness harness-lean clean

# Fast, dependency-free sanity on the algorithm (Node only). Validates the
# SHARED design used by both the F* and Lean oracles.
selfcheck:
	node tools/selfcheck.mjs

# ---- Lean 4 oracle (recommended) -- needs `nix develop` (default shell) ----
lean-oracle:
	cd oracle-lean && lake exe cache get && lake build
	@echo ">> lean oracle at: oracle-lean/.lake/build/bin/oracle"

harness-lean:
	cd harness && pnpm install && \
	ORACLE_EXE=../oracle-lean/.lake/build/bin/oracle pnpm test

check-lean: selfcheck lean-oracle harness-lean

# ---- F* / OCaml oracle (alternate) -- needs `nix develop .#fstar` ----
verify:
	$(MAKE) -C oracle verify
oracle:
	$(MAKE) -C oracle extract && $(MAKE) -C oracle build
harness:
	cd harness && pnpm install && \
	ORACLE_EXE=../oracle/_build/default/ml/main.exe pnpm test
check: selfcheck oracle harness

clean:
	-$(MAKE) -C oracle clean
	-rm -rf oracle-lean/.lake harness/node_modules
