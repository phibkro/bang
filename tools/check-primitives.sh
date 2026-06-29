#!/usr/bin/env bash
# check-primitives.sh — kernel fitness function for CLAUDE.md Invariants #3 & #5.
#
# Invariant #5: "Kernel stays at five primitives: thunk · force · effect rows ·
# handlers · STM. Adding a sixth is a spec change requiring an ADR."
# Invariant #3: "STM is the ONLY privileged kernel primitive."
#
# Those invariants are PROSE. This makes them STRUCTURAL: the kernel's term
# alphabet is the constructor set of `Val` / `Comp` / `Handler` in Bang/Core/IR.lean.
# We assert that set equals a maintained ALLOWLIST. A new constructor (a candidate
# 6th primitive) therefore can't slip in silently — it makes this check RED until
# someone edits the allowlist below, which is the visible, reviewed act the
# invariant demands (and should be accompanied by an ADR).
#
# This is a set EQUALITY check, not a subset: a constructor that VANISHES from the
# allowlist (stale list) is flagged too. Exit 1 on any mismatch (added OR removed).
set -euo pipefail

ROOT="${1:-.}"
CORE="$ROOT/Bang/Core/IR.lean"

[ -f "$CORE" ] || { echo "FAIL: $CORE not found"; exit 1; }

# ── The allowlist: the kernel's known term-syntax constructors (Bang/Core/IR.lean §1.2).
# Grouped by the five-primitive creed. Editing this list is a SPEC CHANGE (ADR).
#
#   thunk/force adjunction : vthunk · force
#   effect rows + ops      : perform            (a labelled operation; rows live in types, EffectRow.lean. ADR-0045: renamed from `up`. ADR-0054: now `perform c op v` — the target handler is named by a CAPABILITY value `c`, not a positional cap)
#   handlers (runtimes)    : handle · state · throws · transaction   (transaction = STM, ADR-0030)
#   CBPV scaffolding       : vunit vint vvar vcap · ret letC lam app   (vcap = the capability identity value, ADR-0054 — a value former like vint, NOT a 6th primitive)
#   ADT data layer (0029)  : inl inr pair fold · case split unfold
#   error/divergence forms : oom wrong
ALLOWLIST="$(cat <<'EOF'
Val.vunit
Val.vint
Val.vvar
Val.vcap
Val.vthunk
Val.inl
Val.inr
Val.pair
Val.fold
Comp.ret
Comp.letC
Comp.force
Comp.lam
Comp.app
Comp.perform
Comp.handle
Comp.case
Comp.split
Comp.unfold
Comp.oom
Comp.wrong
Handler.state
Handler.throws
Handler.transaction
EOF
)"

# ── Extract the ACTUAL constructor set from the three kernel inductives.
# Scope to the `inductive Val … / Comp … / Handler …` blocks inside the §1.2 mutual.
# A constructor line is `  | name  : …` directly under one of those headers.
# `Frame` (§1.3) is operational machinery, not a term primitive — excluded by only
# tracking the three named inductives.
actual="$(awk '
  /^inductive Val : Type/     { sect="Val";     next }
  /^inductive Comp : Type/    { sect="Comp";    next }
  /^inductive Handler : Type/ { sect="Handler"; next }
  # Any new top-level form ends the current section.
  /^(end|mutual|abbrev|def|instance|inductive|namespace|structure)([[:space:]]|$)/ {
    if ($0 !~ /^inductive (Val|Comp|Handler) :/) sect=""
  }
  {
    if (sect != "") {
      line=$0
      sub(/--.*$/, "", line)                       # strip trailing comment
      if (match(line, /^[[:space:]]*\|[[:space:]]*[A-Za-z_]/)) {
        name=line
        sub(/^[[:space:]]*\|[[:space:]]*/, "", name)
        sub(/[^A-Za-z0-9_].*$/, "", name)
        if (name != "") print sect "." name
      }
    }
  }
' "$CORE" | sort -u)"

expected="$(printf '%s\n' "$ALLOWLIST" | sort -u)"

added="$(comm -13 <(printf '%s\n' "$expected") <(printf '%s\n' "$actual"))"
removed="$(comm -23 <(printf '%s\n' "$expected") <(printf '%s\n' "$actual"))"

if [ -z "$added" ] && [ -z "$removed" ]; then
  count="$(printf '%s\n' "$actual" | grep -c .)"
  echo "primitives: OK — $count kernel constructors match the allowlist (Invariants #3/#5 structural)"
  exit 0
fi

echo "FAIL: kernel constructor set ≠ allowlist (CLAUDE.md Invariants #3/#5)."
if [ -n "$added" ]; then
  echo "  ── ADDED (candidate new primitive — needs an ADR + allowlist update in tools/check-primitives.sh):"
  printf '       + %s\n' $added
fi
if [ -n "$removed" ]; then
  echo "  ── REMOVED (allowlist is stale — a primitive was dropped):"
  printf '       - %s\n' $removed
fi
exit 1
