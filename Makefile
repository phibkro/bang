.PHONY: build selfcheck audit verify clean

# Fast, dependency-free sanity check on the row-algebra (Node only).
# Useful smoke test during the ◊2 graded-CBPV refactor before lake is hot.
selfcheck:
	node tools/selfcheck.mjs

# Build the Lean library (Bang/*.lean). First time: pulls Mathlib oleans.
build:
	lake exe cache get && lake build

# Static + dynamic audit gate — see tools/audit.sh.
# Real guarantee is Bang/Audit.lean (#print axioms); audit.sh is the cheap grep CI.
audit: build
	bash tools/audit.sh

# Default verify: smoke test + build + axiom audit.
verify: selfcheck audit

clean:
	-rm -rf .lake
