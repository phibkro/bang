#!/usr/bin/env bash
# tool: role=lane couples=.github/workflows/release.yml,Main.lean,examples/caesar/main.bang runs-in=ci
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
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

# --- 1. strip + de-nix the loader path (platform-guarded) --------------------------
# `stat` byte-size differs on BSD/macOS (`-c %s` is GNU; `-f %z` is BSD). Detect once.
size() { stat -c %s "$1" 2>/dev/null || stat -f %z "$1"; }
UNSTRIPPED_SRC_BYTES="$(size "$BUILT")"
cp "$BUILT" "$OUT"

# The de-nix step is ELF-specific. A Lean/nix-built ELF hardcodes NIX-STORE ABSOLUTE
# PATHS in its interpreter (`/nix/store/…/ld-linux-x86-64.so.2`) and RPATH; it links
# only glibc + libgcc_s (ldd-verified) but by nix-store PATH — so off a nix store it
# fails "No such file or directory". Re-point the interpreter at the distro-standard
# loader and drop the nix RPATH so libc/libgcc_s resolve on Ubuntu/Debian/Fedora. This
# is what makes the Release binary portable, not just runnable-on-the-CI-runner.
#
# Mach-O has NO ELF interpreter field, so patchelf does not apply on darwin. What a
# nix-`lake build` Mach-O needs to be portable off a nix store is dylib-path de-nixing
# (`install_name_tool -change /nix/store/…/lib*.dylib @rpath/…`) — but the EXACT set of
# nix-store dylibs a `bang` Mach-O carries is UNVERIFIED here (no darwin machine in this
# lane). The honest posture: on darwin we strip + smoke ONLY, and print the linked libs
# so the FIRST real macos runner shows whether any /nix/store dylib leaked. If the smoke
# set passes on the runner, the binary is self-consistent there; the open risk is a
# nix-store dylib that resolves on the runner but not on a stranger's Mac. That risk is
# named loudly in the release note and the survey, NOT silently assumed away.
case "$TRIPLE" in
  *-linux)
    strip "$OUT"
    patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 --remove-rpath "$OUT"
    DENIX_NOTE="ELF interp: $(patchelf --print-interpreter "$OUT")  (distro-standard, de-nixed)"
    ;;
  *-darwin)
    # `strip` on macOS is the cctools strip; it accepts a bare path. No interp rewrite.
    strip "$OUT"
    # Surface the linkage so the first darwin run reveals any /nix/store leak (see above).
    if command -v otool >/dev/null 2>&1; then
      DENIX_NOTE="dylibs:
$(otool -L "$OUT" | sed 's/^/    /')"
    else
      DENIX_NOTE="dylibs: (otool unavailable — cannot report linkage)"
    fi
    ;;
  *)
    echo "FAIL: unknown TRIPLE '$TRIPLE' — expected *-linux or *-darwin"; exit 1
    ;;
esac
STRIPPED_BYTES="$(size "$OUT")"

human() { numfmt --to=iec --suffix=B "$1" 2>/dev/null || echo "$1 bytes"; }
echo "── artifact size ──"
echo "  unstripped: $(human "$UNSTRIPPED_SRC_BYTES")  ($UNSTRIPPED_SRC_BYTES bytes)"
echo "  stripped:   $(human "$STRIPPED_BYTES")  ($STRIPPED_BYTES bytes)"
echo "  $DENIX_NOTE"

# --- 2. smoke the STRIPPED + de-nixed binary ---------------------------------------
# The proof that stripping + the interpreter rewrite preserved behaviour. Each check is
# fail-loud: a wrong value or a wrong exit code aborts the whole script (set -e), so the
# artifact is never declared good on a regressed binary.
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
