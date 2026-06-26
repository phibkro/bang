#!/usr/bin/env bash
# arch-check.sh — the import-direction fitness function (ADR-0046/0047 ②).
# ──────────────────────────────────────────────────────────────────────────────
# Enforces the layered architecture as a TESTED rung: drift in the dependency
# direction becomes a build failure, not a convention to remember.
#
# The shape is a V with an apex (verified from the import graph):
#
#             Spec · Audit · Distribution     ← APEX: manifest + gate (imports anything)
#            ╱         │          ╲
#     Frontend  ────► Core ◄────  Backend     ← the V
#    (Surface,       (semantics  (CalcVM,
#     NamedCore,      + IR; the   Compile,
#     Trait)          SSoT)       CalcReify*)
#
# RULES (the only ones that keep the V from collapsing into a tangle):
#   • Core      must NOT import Frontend or Backend   (Core is the sink — depends on nothing outward)
#   • Frontend  must NOT import Backend               (the two edges meet only at Core)
#   • Backend   must NOT import Frontend
#   • Apex      is unrestricted (it aggregates the whole project)
#
# Data FLOWS Frontend → Core → Backend (text → IR → WASM); DEPENDENCIES point
# inward at Core. That inward-pointing V is what makes Core reusable and the
# writable IR (Bang.Frontend.NamedCore) a clean plugin/LSP surface.
#
# LAYER ASSIGNMENT is path-derived where the files have moved
# (Bang/Frontend/*, Bang/Backend/*) and a declared map otherwise — a temporary
# CONVENTION rung that becomes GENERATE (path-derived) once the seam-first file
# moves land (the moves are deferred until the pivot tree is green again).
set -euo pipefail

ROOT="${1:-.}"
cd "$ROOT"

# ── layer of a dotted module name ────────────────────────────────────────────
layer_of() {
  case "$1" in
    Bang.Frontend.*) echo Frontend; return ;;   # path-derived (already moved)
    Bang.Backend.*)  echo Backend;  return ;;    # path-derived (for the deferred moves)
  esac
  case "$1" in
    Bang.EffectRow|Bang.Core|Bang.Mult|Bang.Syntax|Bang.Operational|Bang.LR|Bang.Compat|Bang.Metatheory|Bang.CapEscapeWitness|Bang.LWRegress|Bang.BoccRegress)
      echo Core ;;
    Bang.CalcVM|Bang.Compile|Bang.CalcReify|Bang.CalcReifyRef|Bang.CalcReifySim)
      echo Backend ;;
    Bang.Surface|Bang.Surface.Trait)
      echo Frontend ;;
    Bang.Spec|Bang.Audit|Bang.Distribution)
      echo Apex ;;
    *)
      echo UNCLASSIFIED ;;
  esac
}

# ── is (importer-layer → imported-layer) forbidden? ──────────────────────────
forbidden() {  # $1 = importer layer, $2 = imported layer
  case "$1:$2" in
    Core:Frontend|Core:Backend) return 0 ;;
    Frontend:Backend)           return 0 ;;
    Backend:Frontend)           return 0 ;;
    *)                          return 1 ;;
  esac
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
