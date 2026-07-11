#!/usr/bin/env bash
# tool: role=test couples=docs/reference/language.md,tools/gen-reference.py runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-reference-samples.sh — the SAMPLE-GATING battery for the generated reference (#131).
#
# The generated docs/reference/language.md carries two kinds of code sample:
#   - the `⟹`/`:`-annotated LIST items in the Examples section — already #guard-gated at the
#     Lean level (Bang/Examples.lean), so they cannot drift; this battery does NOT touch them.
#   - PROSE code samples in fenced blocks — the drift surface stranger-round-5 found. THIS
#     battery closes it: every ```bang block is run through the built `bang` binary.
#
# THE FENCE CONTRACT (emitted by tools/gen-reference.py, consumed here):
#   ```bang          a runnable sample. Always `bang check`ed (stdin). If it carries a
#                    `-- ⟹ <value>` line, ALSO `bang run` it and assert stdout == <value>
#                    (the FIRST whitespace token after ⟹ is the expected value; trailing
#                    prose like `(examples/…)` is ignored).
#   ```bang no-run   a check-only sample (decls-only, or a program whose run-output is not
#                    the teaching point). `bang check` only, no run.
#   <!-- no-gate: reason -->  immediately before ANY fence ⟹ that fence is SKIPPED entirely
#                    (an `error:` diagnostic transcript, a CLI-invocation transcript — not a
#                    bang program). The reason is recorded in the generated doc, in the diff.
# An un-marked ```bang sample that fails `check` (or whose `run` ≠ its ⟹) FAILS this battery
# LOUDLY — that is the whole point: a stale prose sample can no longer ship green.
#
# GOTCHA (set -euo pipefail): `bang run` reads a FILE (not stdin — it prints usage to stdin),
# so each runnable sample is written to a mktemp'd .bang file. `bang check` DOES read stdin.
# Every capture runs standalone with an explicit exit-capture; the FINAL line asserts the
# expected sample COUNT so a parser that silently extracts zero blocks is caught.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"
ref="docs/reference/language.md"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

workdir="$(mktemp -d --tmpdir bang-ref-samples-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT

# ── EXTRACT: split the reference into per-fence sample files, honoring the fence contract. ──
# Emits, into $workdir, one file per gated ```bang block: NNNN.bang (the source) and,
# when present, NNNN.expect (the ⟹ value) and NNNN.mode (`run` or `check`). A `no-gate`
# comment on the line immediately preceding a fence suppresses that fence.
python3 - "$ref" "$workdir" <<'PY'
import re, sys, pathlib
ref, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
lines = ref.read_text(encoding="utf-8").splitlines()
i, n = 0, 0
while i < len(lines):
    line = lines[i]
    m = re.match(r"^```bang(\s+no-run)?\s*$", line)
    if not m:
        i += 1
        continue
    # a `no-gate` HTML comment on the immediately-preceding non-blank line suppresses this fence
    prev = lines[i - 1].strip() if i > 0 else ""
    if prev.startswith("<!-- no-gate:"):
        i += 1
        continue
    norun = m.group(1) is not None
    body, expect = [], None
    j = i + 1
    while j < len(lines) and not lines[j].startswith("```"):
        row = lines[j]
        em = re.search(r"⟹\s*(\S+)", row)
        if em and row.lstrip().startswith("--"):
            expect = em.group(1)          # first token after ⟹; trailing prose ignored
        else:
            body.append(row)
        j += 1
    n += 1
    stem = out / f"{n:04d}"
    stem.with_suffix(".bang").write_text("\n".join(body) + "\n", encoding="utf-8")
    if expect is not None and not norun:
        stem.with_suffix(".expect").write_text(expect, encoding="utf-8")
        stem.with_suffix(".mode").write_text("run", encoding="utf-8")
    else:
        stem.with_suffix(".mode").write_text("check", encoding="utf-8")
    i = j + 1
print(n)
PY

pass=0
fail=0
count=0

for bangfile in "$workdir"/*.bang; do
  [ -f "$bangfile" ] || continue
  count=$((count + 1))
  stem="${bangfile%.bang}"
  name="$(basename "$stem")"
  mode="$(cat "$stem.mode")"

  # (1) every gated sample must type-check (stdin path).
  check_out="$("$bang" check < "$bangfile" 2>&1)" && check_exit=0 || check_exit=$?
  if [ "$check_exit" -ne 0 ]; then
    echo "✗ sample-$name-check — \`bang check\` failed (exit $check_exit): $check_out"
    echo "    source:"; sed 's/^/      /' "$bangfile"
    fail=$((fail + 1))
    continue
  fi
  echo "✓ sample-$name-check"
  pass=$((pass + 1))

  # (2) a run-mode sample additionally runs and must match its ⟹ value.
  if [ "$mode" = "run" ]; then
    want="$(cat "$stem.expect")"
    got="$("$bang" run "$bangfile" 2>/dev/null)" && run_exit=0 || run_exit=$?
    if [ "$run_exit" -eq 0 ] && [ "$got" = "$want" ]; then
      echo "✓ sample-$name-run → $got"
      pass=$((pass + 1))
    else
      echo "✗ sample-$name-run — expected [$want], got [$got] (exit $run_exit)"
      echo "    source:"; sed 's/^/      /' "$bangfile"
      fail=$((fail + 1))
    fi
  fi
done

echo "──────────────────────────────"
echo "reference-samples: $pass passed, $fail failed ($count gated bang blocks)"
# Count assertion (false-green defense): the reference DOES carry gated ```bang samples; a
# parser that silently extracted zero (a regex/format drift) must fail loud, not vacuously pass.
if [ "$count" -lt 1 ]; then
  echo "✗ no-samples-extracted — the reference has no gated bang blocks; the extractor drifted"
  exit 1
fi
[ "$fail" -eq 0 ]
