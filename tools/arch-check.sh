#!/usr/bin/env bash
# arch-check.sh — the import-direction fitness function (ADR-0046/0047 ②).
# ──────────────────────────────────────────────────────────────────────────────
# Enforces the layered architecture as a TESTED rung: drift in the dependency
# direction becomes a build failure, not a convention to remember.
#
# The shape is a V with consumer tiers above an apex (verified from the import graph):
#
#       Spec · Audit · Distribution · Examples   ← APEX (rank 3): manifest + gate + worked-examples corpus (imports anything)
#                       ▲
#         Meta · Witness · Reify                 ← CONSUMERS (rank 2): proofs-about / witnesses
#        (LR, BinaryLR)  (regress)  (CalcReify*)    reify the V; never imported BY it
#                       ▲
#     Frontend  ────► Core ◄────  Backend         ← the V (rank 1 edges, rank-0 sink)
#    (Surface,       (IR, Typing, (AbstractMachine,
#     NamedCore)      Semantics,   Wasm)
#                     Grade, Soundness,
#                     Freshness, CapCoh — the SSoT)
#
# RANKS (the V enforced by DIRECTORY STRUCTURE — the tier dir IS the truth):
#   Core = 0 (the sink: imports nothing outward) · Frontend = Backend = 1 (siblings) ·
#   Meta = Witness = Reify = 2 (consumers) · Apex = 3 (unrestricted).
# RULES (the only ones that keep the V from collapsing into a tangle):
#   • importing strictly UPWARD (rank a < rank b) is forbidden — Core can't pull any
#     outer tier; Frontend/Backend can't pull a consumer; consumers can't pull Apex.
#   • Frontend ⊥ Backend (same rank, but the two edges meet ONLY at Core).
#   Downward consumption is free: a consumer imports the V, Reify imports Backend, etc.
#
# Data FLOWS Frontend → Core → Backend (text → IR → WASM); DEPENDENCIES point
# inward at Core. That inward-pointing V is what makes Core reusable and the
# writable IR (Bang.Frontend.NamedCore) a clean plugin/LSP surface.
#
# LAYER ASSIGNMENT is PATH-DERIVED (GENERATE, not convention): the tier is read from
# the `Bang/<Tier>/` directory in the module path (ADR-0048 §6). A new module lands in
# the right layer by WHERE its file lives — drift is unrepresentable, not remembered.
# NOTE (ADR-0048 amendment): Soundness (the syntactic STD metatheory) lives in Core, not
# Meta — the gated kernel closure (AbstractMachine→CapCoh→Freshness→Soundness) depends on
# it, so the dependency graph FORCES it Core-foundational; Meta holds only the binary-LR.
set -euo pipefail

ROOT="${1:-.}"
cd "$ROOT"

# ── layer of a dotted module name (PATH-DERIVED: the tier dir is the truth) ───
layer_of() {
  case "$1" in
    Bang.Frontend.*) echo Frontend; return ;;
    Bang.Core.*)     echo Core;     return ;;
    Bang.Backend.*)  echo Backend;  return ;;
    Bang.Meta.*)     echo Meta;     return ;;
    Bang.Witness.*)  echo Witness;  return ;;
    Bang.Reify.*)    echo Reify;    return ;;
    Bang.Spec|Bang.Audit|Bang.Distribution|Bang.Examples) echo Apex; return ;;
    *)               echo UNCLASSIFIED ;;
  esac
}

# ── rank of a tier (the V's partial order) ───────────────────────────────────
rank() {
  case "$1" in
    Core)               echo 0 ;;
    Frontend|Backend)   echo 1 ;;
    Meta|Witness|Reify) echo 2 ;;
    Apex)               echo 3 ;;
    *)                  echo 9 ;;
  esac
}

# ── is (importer-layer → imported-layer) forbidden? ──────────────────────────
forbidden() {  # $1 = importer layer, $2 = imported layer
  # the two V-edges are incomparable: they meet only at Core
  case "$1:$2" in
    Frontend:Backend|Backend:Frontend) return 0 ;;
  esac
  # importing strictly upward is forbidden (Core is the sink; lower tiers can't pull higher)
  [ "$(rank "$1")" -lt "$(rank "$2")" ] && return 0
  return 1
}

violations=0
unclassified=0

# module path → dotted name: strip leading ./, drop .lean, '/'→'.'
modname() { local p="${1#./}"; p="${p%.lean}"; echo "${p//\//.}"; }

while IFS= read -r file; do
  self="$(modname "$file")"
  selflayer="$(layer_of "$self")"
  if [ "$selflayer" = "UNCLASSIFIED" ]; then
    echo "UNCLASSIFIED MODULE: $self ($file) — add it to layer_of in tools/arch-check.sh"
    unclassified=$((unclassified + 1))
    continue
  fi
  # internal Bang imports only
  while IFS= read -r imp; do
    [ -z "$imp" ] && continue
    implayer="$(layer_of "$imp")"
    if [ "$implayer" = "UNCLASSIFIED" ]; then
      echo "UNCLASSIFIED IMPORT: $self imports $imp — add $imp to layer_of"
      unclassified=$((unclassified + 1))
      continue
    fi
    if forbidden "$selflayer" "$implayer"; then
      echo "VIOLATION: $self [$selflayer] imports $imp [$implayer]  — the V forbids $selflayer → $implayer"
      violations=$((violations + 1))
    fi
  done < <(grep -E '^import Bang\b' "$file" | sed -E 's/^import +//; s/ .*$//')
done < <(find Bang -name '*.lean' | sort)

echo "── arch-check (import-direction fitness function) ──"
if [ "$violations" -eq 0 ] && [ "$unclassified" -eq 0 ]; then
  echo "PASS: the V holds — Core imports neither edge; Frontend and Backend meet only at Core."
  exit 0
else
  echo "FAIL: $violations dependency-direction violation(s), $unclassified unclassified module(s)."
  exit 1
fi
