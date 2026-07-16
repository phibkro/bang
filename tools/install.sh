#!/usr/bin/env bash
# tool: role=workflow couples=.github/workflows/release.yml,tools/release-manifest.sh runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# install.sh — the curl-able installer for the `bang` binary. Resolves ONE latest
# release tag, downloads that tag's checksum manifest and platform binary, verifies the
# binary, then atomically replaces ~/.local/bin/bang. Run it via:
#   curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh
#
# Trust boundary: SHA256SUMS and the binary come from the same GitHub Release. This
# detects transport/storage corruption and wrong-asset selection, but is not an
# independent authenticity signature. Release provenance can additionally be checked
# with `gh attestation verify`; keeping that optional avoids making gh a prerequisite.
set -euo pipefail

REPO="phibkro/bang"
INSTALL_DIR="${BANG_INSTALL_DIR:-$HOME/.local/bin}"
BIN_NAME="bang"
MANIFEST_NAME="SHA256SUMS"

err() { echo "install.sh: $*" >&2; exit 1; }

# --- platform detection ------------------------------------------------------------
os="$(uname -s)"
arch="$(uname -m)"
case "$os/$arch" in
  Linux/x86_64) triple="x86_64-linux" ;;
  Linux/aarch64 | Linux/arm64) triple="aarch64-linux" ;;
  Darwin/arm64 | Darwin/aarch64) triple="aarch64-darwin" ;;
  *)
    err "unsupported platform '$os/$arch'. Prebuilt binaries cover x86_64-linux,
     aarch64-linux, and aarch64-darwin (Apple Silicon). For anything else (incl.
     Intel macOS and Windows), build from source with Nix — see the README
     'Run a bang program' section (or 'nix develop')."
    ;;
esac

# Prepare/check the final target before any network request. `mv SOURCE DIRECTORY`
# descends into the directory instead of replacing it, so reject an existing directory
# (including a symlink to one) before temp creation/fetch. A regular file or a symlink
# to a non-directory is intentionally replaced by the final atomic rename itself.
mkdir -p "$INSTALL_DIR"
target="$INSTALL_DIR/$BIN_NAME"
[ ! -d "$target" ] || err "install target is a directory, refusing to replace it: $target"

# --- download seam -----------------------------------------------------------------
# Tests set BANG_INSTALL_FETCH to a local executable accepting URL [DEST]. Production
# deliberately selects only curl/wget. A failing downloader may leave a partial temp
# file; the EXIT trap removes it and the installed binary remains untouched.
if [ -n "${BANG_INSTALL_FETCH:-}" ]; then
  [ -x "$BANG_INSTALL_FETCH" ] || err "BANG_INSTALL_FETCH is not executable: $BANG_INSTALL_FETCH"
  fetch() { "$BANG_INSTALL_FETCH" "$1"; }
  fetch_to() { "$BANG_INSTALL_FETCH" "$1" "$2"; }
elif command -v curl >/dev/null 2>&1; then
  fetch() { curl -fsSL "$1"; }
  fetch_to() { curl -fsSL -o "$2" "$1"; }
elif command -v wget >/dev/null 2>&1; then
  fetch() { wget -qO- "$1"; }
  fetch_to() { wget -qO "$2" "$1"; }
else
  err "need curl or wget on PATH to download the release."
fi

# --- resolve exactly one stable release tag ----------------------------------------
api="https://api.github.com/repos/$REPO/releases/latest"
body=""
if ! body="$(fetch "$api")"; then
  err "could not resolve the latest GitHub release ($api) — check your network."
fi

# The API is JSON, but requiring jq would defeat the dependency-light installer. Match
# only GitHub's complete tag_name line, count it, then constrain it to the stable tag
# grammar before it can enter a URL or filename. Zero/duplicate/malformed is fatal.
tag_matches="$(printf '%s\n' "$body" \
  | sed -n 's/^[[:space:]]*"tag_name":[[:space:]]*"\([^"]*\)"[[:space:]]*,\{0,1\}[[:space:]]*$/\1/p')"
tag=""
tag_count=0
while IFS= read -r candidate; do
  [ -n "$candidate" ] || continue
  tag="$candidate"
  tag_count=$((tag_count + 1))
done <<EOF
$tag_matches
EOF
[ "$tag_count" -eq 1 ] || err "latest-release response must contain exactly one tag_name (found $tag_count)."
[[ "$tag" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]] || err "latest release has unsupported tag '$tag' (expected vX.Y.Z)."

asset="$BIN_NAME-$tag-$triple"
release_base="https://github.com/$REPO/releases/download/$tag"

# --- download into the destination filesystem -------------------------------------
manifest_tmp="$(mktemp "$INSTALL_DIR/.bang-manifest.XXXXXX")"
binary_tmp="$(mktemp "$INSTALL_DIR/.bang-install.XXXXXX")"
trap 'rm -f "$manifest_tmp" "$binary_tmp"' EXIT

echo "install.sh: resolving $asset from $tag ..." >&2
fetch_to "$release_base/$MANIFEST_NAME" "$manifest_tmp" \
  || err "checksum manifest download failed for release $tag"

# Validate the entire deterministic three-platform manifest, not merely the selected
# row: only exact lowercase SHA-256 records and exact tag-scoped filenames are valid.
darwin_asset="$BIN_NAME-$tag-aarch64-darwin"
arm_linux_asset="$BIN_NAME-$tag-aarch64-linux"
x64_linux_asset="$BIN_NAME-$tag-x86_64-linux"
darwin_count=0
arm_linux_count=0
x64_linux_count=0
expected_sha=""
line_no=0
manifest_record_re='^([0-9a-f]{64})  ([^/[:space:]]+)$'
while IFS= read -r line || [ -n "$line" ]; do
  line_no=$((line_no + 1))
  if [[ ! "$line" =~ $manifest_record_re ]]; then
    err "malformed checksum manifest record at line $line_no"
  fi
  digest="${BASH_REMATCH[1]}"
  filename="${BASH_REMATCH[2]}"
  case "$filename" in
    "$darwin_asset") darwin_count=$((darwin_count + 1)) ;;
    "$arm_linux_asset") arm_linux_count=$((arm_linux_count + 1)) ;;
    "$x64_linux_asset") x64_linux_count=$((x64_linux_count + 1)) ;;
    *) err "unexpected checksum manifest asset '$filename' for release $tag" ;;
  esac
  [ "$filename" != "$asset" ] || expected_sha="$digest"
done < "$manifest_tmp"

for record in \
  "$darwin_asset:$darwin_count" \
  "$arm_linux_asset:$arm_linux_count" \
  "$x64_linux_asset:$x64_linux_count"; do
  filename="${record%:*}"
  count="${record##*:}"
  [ "$count" -eq 1 ] || err "checksum manifest must contain '$filename' exactly once (found $count)"
done
[ -n "$expected_sha" ] || err "checksum manifest has no digest for '$asset'"

echo "install.sh: downloading $asset ..." >&2
fetch_to "$release_base/$asset" "$binary_tmp" || err "binary download failed for $asset"

if command -v sha256sum >/dev/null 2>&1; then
  digest_line="$(sha256sum "$binary_tmp")" || err "sha256sum failed"
elif command -v shasum >/dev/null 2>&1; then
  digest_line="$(shasum -a 256 "$binary_tmp")" || err "shasum failed"
else
  err "need sha256sum or shasum on PATH to verify the release binary."
fi
actual_sha="${digest_line%%[[:space:]]*}"
[[ "$actual_sha" =~ ^[0-9a-f]{64}$ ]] || err "checksum tool returned a malformed SHA-256 digest"
[ "$actual_sha" = "$expected_sha" ] \
  || err "checksum mismatch for $asset (expected $expected_sha, got $actual_sha)"

# chmod + rename occurs only after every fallible fetch/parse/verification step. Both
# temp and target live in INSTALL_DIR, so mv is an atomic replacement on one filesystem.
chmod 0755 "$binary_tmp"
[ ! -d "$target" ] || err "install target became a directory during download, refusing to replace it: $target"
# Trust boundary: portable POSIX shell cannot make the target-type recheck and `mv`
# one indivisible operation. An actor able to mutate INSTALL_DIR in the micro-window
# between these two commands can still race directory creation; avoiding that requires
# a platform-specific rename syscall/dirfd helper. Normal operation assumes the user-
# owned installation directory is not concurrently modified by an adversary.
mv -f "$binary_tmp" "$target"
echo "install.sh: verified SHA-256 and installed $BIN_NAME -> $target" >&2

case ":$PATH:" in
  *":$INSTALL_DIR:"*) echo "install.sh: run 'bang --help' to get started." >&2 ;;
  *)
    echo "install.sh: $INSTALL_DIR is not on your PATH. Add it, e.g.:" >&2
    echo "    echo 'export PATH=\"\$HOME/.local/bin:\$PATH\"' >> ~/.bashrc && exec \$SHELL" >&2
    echo "  then run 'bang --help'." >&2
    ;;
esac
