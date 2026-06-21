#!/usr/bin/env bash
# setup.sh — first-time bootstrap for a fresh clone.
# Usage: just setup
#
# Idempotent: re-running is safe; install-hooks is idempotent,
# lake exe cache get is incremental, just verify is fast when green.

set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

echo "── bang-lang first-time setup ──"
echo ""

echo "[1/3] git pre-commit hook..."
bash tools/install-hooks.sh

echo ""
echo "[2/3] Mathlib oleans (first time: multi-GB; subsequent: incremental)..."
lake exe cache get

echo ""
echo "[3/3] verify (selfcheck + build + audit)..."
just verify

echo ""
echo "✓ setup complete."
echo ""
echo "Next:"
echo "  · Read ONBOARDING.md          (full reference index)"
echo "  · Read CLAUDE.md              (invariants + glossary + architecture)"
echo "  · Read CONTEXT.md             (current position)"
echo "  · Read ROADMAP.md             (long-term map of checkpoints)"
echo ""
echo "  · just orient                 one-shot status print"
echo "  · just                        list available recipes"
