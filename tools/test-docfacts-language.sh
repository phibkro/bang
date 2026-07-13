#!/usr/bin/env bash
# tool: role=test couples=docfacts/language.json,docs/reference/language.md,web/docs/bang.tmLanguage.json runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-docfacts-language.sh — focused executable agreement for the language docfact seam.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

python3 tools/docfacts_language.py --check
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

python3 - <<'PY'
import subprocess

from tools.docfacts_language import load_language_fact

fact = load_language_fact()
bang = ".lake/build/bin/bang"
floors = {
    "surface forms": len(fact["surface"]["forms"]),
    "types": len(fact["surface"]["types"]),
    "operators": len(fact["grammar"]["operators"]),
    "keyword rules": len(fact["grammar"]["keywordRules"]),
    "reserved identifiers": len(fact["grammar"]["reservedIdentifiers"]),
    "effect labels": len(fact["grammar"]["effectLabels"]),
    "diagnostic fields": len(fact["diagnostics"]["contract"]["fields"]),
    "diagnostic codes": len(fact["diagnostics"]["registry"]),
    "prelude declarations": len(fact["prelude"]["declarations"]),
    "CLI commands": len(fact["cli"]["commands"]),
    "evidence records": len(fact["evidence"]),
}
for family, count in floors.items():
    if count == 0:
        raise SystemExit(f"empty extracted family: {family}")
print("✓ language-docfact-families-nonempty " + " ".join(f"{k}={v}" for k, v in floors.items()))

help_run = subprocess.run([bang, "--help"], text=True, capture_output=True)
assert help_run.returncode == 0 and "USAGE:" in help_run.stdout and not help_run.stderr
commands = fact["cli"]["commands"]
for command in commands:
    assert command["synopsis"] in help_run.stdout, command["path"]
assert len(commands) == len({tuple(command["path"]) for command in commands})
print(f"✓ serialized-cli-paths-appear-in-real-help ({len(commands)}/{len(commands)})")
PY
