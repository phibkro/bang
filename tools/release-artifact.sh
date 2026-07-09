#!/usr/bin/env bash
# tool: role=lane couples=.github/workflows/release.yml,Main.lean,examples/caesar/main.bang runs-in=ci
# release-artifact.sh — the strip + smoke + name recipe for a release binary, as ONE
# script so CI (.github/workflows/release.yml) and the local dry-run run the identical
# steps (no drift between "what CI does" and "what I proved locally"). Given a version
# and a target triple, it:
#   1. copies .lake/build/bin/bang → the asset path, strips it, reports both sizes;
#   2. smoke-tests the STRIPPED binary (eval, caesar example, check --json exit code);
#   3. on success, emits `asset=` / `path=` to $GITHUB_OUTPUT (CI) or stdout (local).
# Fail-loud: any smoke failure exits non-zero BEFORE the artifact is declared good, so a
# stripped binary that lost behaviour never reaches a Release.
set -euo pipefail

VERSION="${1:?usage: release-artifact.sh <version> <triple>}"
TRIPLE="${2:?usage: release-artifact.sh <version> <triple>}"

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

BUILT=".lake/build/bin/bang"
[ -x "$BUILT" ] || { echo "FAIL: $BUILT not found — run 'lake build bang' first"; exit 1; }

ASSET="bang-${VERSION}-${TRIPLE}"
OUT="$ROOT/dist/$ASSET"
mkdir -p "$ROOT/dist"

# --- 1. strip + size report --------------------------------------------------------
size() { stat -c %s "$1"; }
UNSTRIPPED_SRC_BYTES="$(size "$BUILT")"
cp "$BUILT" "$OUT"
strip "$OUT"
STRIPPED_BYTES="$(size "$OUT")"

human() { numfmt --to=iec --suffix=B "$1" 2>/dev/null || echo "$1 bytes"; }
echo "── artifact size ──"
echo "  unstripped: $(human "$UNSTRIPPED_SRC_BYTES")  ($UNSTRIPPED_SRC_BYTES bytes)"
echo "  stripped:   $(human "$STRIPPED_BYTES")  ($STRIPPED_BYTES bytes)"

# --- 2. smoke the STRIPPED binary --------------------------------------------------
# The proof that stripping preserved behaviour. Each check is fail-loud: a wrong value
# or a wrong exit code aborts the whole script (set -e), so the artifact is never
# declared good on a regressed binary.
echo "── smoke (stripped binary) ──"

smoke_eq() { # <label> <expected> <actual>
  if [ "$2" = "$3" ]; then
    echo "  ok   $1"
  else
    echo "  FAIL $1: expected [$2], got [$3]"; exit 1
  fi
}

# (a) eval 1 + 2 → 3
smoke_eq "eval 1+2" "3" "$("$OUT" eval "1 + 2")"

# (b) the caesar example → its committed expected.txt
smoke_eq "examples/caesar" \
  "$(cat examples/caesar/expected.txt)" \
  "$("$OUT" run examples/caesar/main.bang)"

# (c) check --json on a type-bad (but readable) file → exit 1, and ok:false on stdout.
# A separate exit-code capture: `set -e` would kill us on the expected non-zero, so run
# it guarded. Bad program: `1 + true` is a type error the checker rejects.
BADFILE="$(mktemp)"
trap 'rm -f "$BADFILE"' EXIT
printf '1 + true\n' > "$BADFILE"
set +e
JSON_OUT="$("$OUT" check --json "$BADFILE")"
JSON_CODE=$?
set -e
smoke_eq "check --json bad-file exit" "1" "$JSON_CODE"
case "$JSON_OUT" in
  '{"ok":false'*) echo "  ok   check --json emits ok:false" ;;
  *) echo "  FAIL check --json: expected ok:false JSON, got [$JSON_OUT]"; exit 1 ;;
esac

echo "── smoke: all passed on the stripped binary ──"

# --- 3. emit the asset name + path -------------------------------------------------
if [ -n "${GITHUB_OUTPUT:-}" ]; then
  {
    echo "asset=$ASSET"
    echo "path=$OUT"
  } >> "$GITHUB_OUTPUT"
else
  echo "asset=$ASSET"
  echo "path=$OUT"
fi
