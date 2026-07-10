#!/usr/bin/env bash
# tool: role=workflow couples=.github/workflows/release.yml runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# install.sh — the curl-able installer for the `bang` binary. Detects the platform,
# downloads the latest GitHub Release asset, and drops it in ~/.local/bin. Paired with
# release.yml (which names the asset `bang-<version>-x86_64-linux`) and the README's
# distribution section. Run it via:
#   curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh
set -euo pipefail

REPO="phibkro/bang"
INSTALL_DIR="${BANG_INSTALL_DIR:-$HOME/.local/bin}"
BIN_NAME="bang"

err() { echo "install.sh: $*" >&2; exit 1; }

# --- platform detection ------------------------------------------------------------
# Linux x86_64 only for now (the only triple release.yml builds). Anything else is a
# clear error, not a silent wrong download.
os="$(uname -s)"
arch="$(uname -m)"
case "$os/$arch" in
  Linux/x86_64) triple="x86_64-linux" ;;
  *)
    err "unsupported platform '$os/$arch'. Prebuilt binaries are x86_64-linux only for now.
     Build from source instead — see the README 'Run a bang program' section."
    ;;
esac

# --- pick the download tool --------------------------------------------------------
# `fetch` for the API (tolerates a 404 body — the expected "no releases yet" case),
# `fetch_hard` for the binary download (fails loudly on any HTTP error).
if command -v curl >/dev/null 2>&1; then
  fetch() { curl -sSL "$1"; }
  fetch_to() { curl -fsSL -o "$2" "$1"; }
elif command -v wget >/dev/null 2>&1; then
  fetch() { wget -qO- "$1"; }
  fetch_to() { wget -qO "$2" "$1"; }
else
  err "need curl or wget on PATH to download the release."
fi

# --- resolve the latest release asset ----------------------------------------------
# HOUSE GOTCHA: under `set -o pipefail`, `x="$(cmd | cmd)"` dies silently if the first
# stage fails (SIGPIPE / non-zero swallowed by the assignment). Capture the raw body
# FIRST (its own guarded line so a network failure is a loud error), THEN parse it.
# We do NOT use curl -f here: `/releases/latest` 404s when there are simply no releases
# yet (the expected pre-first-tag state), and we want to report THAT (build-from-source)
# rather than "the network is down". A real network failure fails the assignment below.
api="https://api.github.com/repos/$REPO/releases/latest"
body=""
if ! body="$(fetch "$api")"; then
  err "could not reach the GitHub releases API ($api) — check your network."
fi

asset="$BIN_NAME-$triple"
# Match the browser_download_url line for our triple's asset. grep|head is fine here:
# both stages read the already-captured \$body, so there is no pipefail-under-network
# race — only a parse of local text.
url=""
url="$(printf '%s\n' "$body" \
  | grep -o "https://[^\"]*/download/[^\"]*/$asset" \
  | head -n1)" || true

if [ -z "$url" ]; then
  err "no '$asset' asset in the latest release of $REPO.
     Releases start at the first version tag — if there are none yet, build from source
     (see the README 'Run a bang program' section)."
fi

# --- download + install ------------------------------------------------------------
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
echo "install.sh: downloading $asset ..." >&2
fetch_to "$url" "$tmp" || err "download failed from $url"

mkdir -p "$INSTALL_DIR"
install -m 0755 "$tmp" "$INSTALL_DIR/$BIN_NAME"
echo "install.sh: installed $BIN_NAME -> $INSTALL_DIR/$BIN_NAME" >&2

# --- PATH hint ---------------------------------------------------------------------
case ":$PATH:" in
  *":$INSTALL_DIR:"*)
    echo "install.sh: run 'bang --help' to get started." >&2
    ;;
  *)
    echo "install.sh: $INSTALL_DIR is not on your PATH. Add it, e.g.:" >&2
    echo "    echo 'export PATH=\"\$HOME/.local/bin:\$PATH\"' >> ~/.bashrc && exec \$SHELL" >&2
    echo "  then run 'bang --help'." >&2
    ;;
esac
