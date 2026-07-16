#!/usr/bin/env bash
# tool: role=check couples=flake.nix,web/docs/package.json,web/docs/page-manifest.json,web/docs/site-model.mjs,web/docs/sync-docs.mjs,web/docs/gen-onboarding.mjs,web/docs/site-smoke.mjs,.github/workflows/site.yml,.github/workflows/pages.yml,.github/workflows/release.yml runs-in=ci
# One production-site build interface for contributors, CI, Pages, and releases.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
if ! command -v bun >/dev/null 2>&1; then
  echo "site-build: FAIL — bun is unavailable." >&2
  echo "Run: nix develop .#site --command just site-build" >&2
  exit 1
fi

cd "$ROOT/web/docs"
bun install --frozen-lockfile

if [[ -n "${PUPPETEER_EXECUTABLE_PATH:-}" ]]; then
  if [[ ! -x "$PUPPETEER_EXECUTABLE_PATH" ]]; then
    echo "site-build: FAIL — PUPPETEER_EXECUTABLE_PATH is not executable: $PUPPETEER_EXECUTABLE_PATH" >&2
    exit 1
  fi
  echo "site-build: using browser $PUPPETEER_EXECUTABLE_PATH"
else
  echo "site-build: installing the lockfile-compatible headless browser for CI…"
  bunx puppeteer browsers install chrome-headless-shell
fi

BANG_SITE_STRICT_MERMAID=1 bun run build
