#!/usr/bin/env bash
# tool: role=lane couples=.github/workflows/release.yml,tools/install.sh runs-in=ci
# Build the canonical SHA256SUMS for one complete, tag-scoped release. The fixed asset
# order makes the manifest deterministic across runners and directory enumeration.
set -euo pipefail

TAG="${1:?usage: release-manifest.sh <vX.Y.Z> <asset-directory>}"
DIR="${2:?usage: release-manifest.sh <vX.Y.Z> <asset-directory>}"
[[ "$TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]] \
  || { echo "release-manifest: invalid stable tag '$TAG'" >&2; exit 1; }
[ -d "$DIR" ] || { echo "release-manifest: asset directory not found: $DIR" >&2; exit 1; }

assets=(
  "bang-$TAG-aarch64-darwin"
  "bang-$TAG-aarch64-linux"
  "bang-$TAG-x86_64-linux"
)

# download-artifact should yield exactly these three tag-scoped files. Reject any
# extra bang-* path (including a directory or symlink) instead of silently omitting it
# from the manifest and overstating that the release set was fully inventoried.
shopt -s nullglob
inventory=("$DIR"/bang-*)
shopt -u nullglob
[ "${#inventory[@]}" -eq "${#assets[@]}" ] \
  || { echo "release-manifest: expected exactly ${#assets[@]} bang assets, found ${#inventory[@]}" >&2; exit 1; }
for path in "${inventory[@]}"; do
  [ -f "$path" ] && [ ! -L "$path" ] \
    || { echo "release-manifest: non-regular asset: $(basename "$path")" >&2; exit 1; }
  known=no
  for asset in "${assets[@]}"; do
    [ "$path" != "$DIR/$asset" ] || known=yes
  done
  [ "$known" = yes ] \
    || { echo "release-manifest: unexpected asset: $(basename "$path")" >&2; exit 1; }
done

if command -v sha256sum >/dev/null 2>&1; then
  file_sha() { sha256sum "$1"; }
elif command -v shasum >/dev/null 2>&1; then
  file_sha() { shasum -a 256 "$1"; }
else
  echo "release-manifest: need sha256sum or shasum" >&2
  exit 1
fi

tmp="$(mktemp "$DIR/.SHA256SUMS.XXXXXX")"
trap 'rm -f "$tmp"' EXIT
for asset in "${assets[@]}"; do
  path="$DIR/$asset"
  [ -f "$path" ] && [ ! -L "$path" ] \
    || { echo "release-manifest: missing or non-regular asset: $asset" >&2; exit 1; }
  digest_line="$(file_sha "$path")" || { echo "release-manifest: hashing failed: $asset" >&2; exit 1; }
  digest="${digest_line%%[[:space:]]*}"
  [[ "$digest" =~ ^[0-9a-f]{64}$ ]] \
    || { echo "release-manifest: malformed digest for $asset" >&2; exit 1; }
  printf '%s  %s\n' "$digest" "$asset" >> "$tmp"
done
mv -f "$tmp" "$DIR/SHA256SUMS"
trap - EXIT
echo "release-manifest: wrote $DIR/SHA256SUMS for ${#assets[@]} assets"
