#!/usr/bin/env bash
# tool: role=check couples=web/run-service/*.ts,examples/*/main.bang runs-in=manual
#
# Smoke battery + GATE for the /run playground exec service (web/run-service/).
# Starts the service on an ephemeral port, posts the tour's 10 lesson programs
# (asserting each expected.txt), a fuel-bomb (must time out cleanly), an oversized
# body (must 413), and a parse error (must return the diagnostic, exit 1). Green =
# every assertion holds.
#
# The 10 lesson sources + expected outputs are read STRAIGHT FROM examples/ — the
# same gated (program, expected) pairs check-examples.sh owns — so this battery
# cannot drift from the corpus.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BANG_BIN="${RUN_BANG_BIN:-.lake/build/bin/bang}"
if [ ! -x "$BANG_BIN" ]; then
  echo "building bang runner (needed by the jail)…" >&2
  lake build bang >&2
fi

command -v bun >/dev/null 2>&1 || { echo "✗ bun not on PATH (nix shell nixpkgs#bun)" >&2; exit 1; }

PORT="${RUN_PORT:-8799}"
BASE="http://127.0.0.1:${PORT}"

# The 10 tour lessons: seed example dir → expected output (interactive-tour-design §5).
LESSONS=(
  effect-op-arith
  nqueens
  derive-eq-ord
  string-stdlib
  state
  handle
  handle-custom-tracer
  logger-silent
  logger-counting
  handle-custom-nested
  gen-seed-a
  gen-seed-b
  tokenizer
)

# ── start the service ────────────────────────────────────────────────────────
export RUN_PORT="$PORT"
export RUN_BANG_BIN="$BANG_BIN"
# Modest wall-clock so the fuel-bomb assertion finishes fast; jail stays on so the
# battery exercises the REAL systemd-run scope path (the deployed posture).
export RUN_JAIL_WALL_SEC="${RUN_JAIL_WALL_SEC:-6}"
# The fuel-bomb needs a fuel ceiling high enough to actually spin past the wall
# clock rather than returning a clean out-of-fuel (exit 2) first — we want to prove
# the WALL-CLOCK backstop, so raise the cap and ask for it.
export RUN_MAX_FUEL="${RUN_MAX_FUEL:-100000000}"

bun run web/run-service/server.ts &
SVC_PID=$!
cleanup() { kill "$SVC_PID" 2>/dev/null || true; wait "$SVC_PID" 2>/dev/null || true; }
trap cleanup EXIT

# wait for /health
for _ in $(seq 1 50); do
  if curl -fsS "${BASE}/health" >/dev/null 2>&1; then break; fi
  sleep 0.2
done
curl -fsS "${BASE}/health" >/dev/null || { echo "✗ service did not come up on ${BASE}" >&2; exit 1; }

pass=0; fail=0
ok()   { echo "✓ $1"; pass=$((pass+1)); }
bad()  { echo "✗ $1"; fail=$((fail+1)); }

# jq-free field extraction from the JSON response (bun's output is stable single-line).
field() { # field <json> <key>
  bun -e 'const d=JSON.parse(process.argv[1]); const v=d[process.argv[2]]; process.stdout.write(v===undefined?"":String(v));' "$1" "$2"
}

# post_run <json-body> → prints response body; writes the HTTP status to the file
# named by $STATUS_FILE (a subshell-set global would be lost across `$(...)`).
STATUS_FILE="$(mktemp)"
post_run() {
  local body="$1" tmp status
  tmp="$(mktemp)"
  status="$(curl -s -o "$tmp" -w '%{http_code}' -X POST "${BASE}/run" \
    -H 'content-type: application/json' --data-binary "$body")"
  printf '%s' "$status" > "$STATUS_FILE"
  cat "$tmp"; rm -f "$tmp"
}
http_status() { cat "$STATUS_FILE"; }

# JSON-encode a file's contents into a {"source": …} body (bun does the escaping).
body_for() { # body_for <src-file> [fuel]
  bun -e '
    const fs=require("fs");
    const src=fs.readFileSync(process.argv[1],"utf8");
    const o={source:src};
    if(process.argv[2]) o.fuel=Number(process.argv[2]);
    process.stdout.write(JSON.stringify(o));
  ' "$1" "${2:-}"
}

echo "── 10 tour lessons ─────────────────────────────────────────────"
for name in "${LESSONS[@]}"; do
  main="examples/${name}/main.bang"
  expected="$(cat "examples/${name}/expected.txt")"
  resp="$(post_run "$(body_for "$main")")"
  got_exit="$(field "$resp" exit)"
  # stdout carries a trailing newline (IO.println); trim for the compare.
  got_out="$(field "$resp" stdout | sed -e 's/[[:space:]]*$//')"
  if [ "$(http_status)" = "200" ] && [ "$got_exit" = "0" ] && [ "$got_out" = "$expected" ]; then
    ok "$name → $got_out"
  else
    bad "$name — want exit 0 / [$expected], got HTTP $(http_status) exit $got_exit / [$got_out]"
    echo "    resp: $resp"
  fi
done

echo "── fuel-bomb (must time out cleanly, not hang) ─────────────────"
# A genuine non-terminating loop: a `! {Div}` recursion with no base case reached
# (the Div annotation is required — an unannotated non-structural rec is a type
# error, ADR-0073; the recursive call forces the fn `$loop` and applies space-
# separated, matching the corpus). With a huge fuel ceiling it spins until the
# wall-clock backstop kills it.
# shellcheck disable=SC2016  # `$loop` is bang source (force), not a shell expansion
BOMB='let rec loop : Int -> Int ! {Div} = fun n => ($loop) (n + 1) in ($loop) 0'
resp="$(post_run "{\"source\":$(bun -e 'process.stdout.write(JSON.stringify(process.argv[1]))' "$BOMB"),\"fuel\":90000000}")"
bomb_timedout="$(field "$resp" timed_out)"
bomb_exit="$(field "$resp" exit)"
# Acceptable clean outcomes (default engine = env, ADR-0094): wall-clock kill
# (timed_out true), the env engine's collapsed no-value outcome (exit 5), or the
# oracle's specific out-of-fuel (exit 2). Any of these = "terminated, no hang, 200".
if [ "$(http_status)" = "200" ] && { [ "$bomb_timedout" = "true" ] || [ "$bomb_exit" = "5" ] || [ "$bomb_exit" = "2" ]; }; then
  ok "fuel-bomb terminated cleanly (timed_out=$bomb_timedout exit=$bomb_exit)"
else
  bad "fuel-bomb — expected clean timeout/out-of-fuel, got HTTP $(http_status) timed_out=$bomb_timedout exit=$bomb_exit"
  echo "    resp: $resp"
fi

echo "── oversized body (must 413) ──────────────────────────────────"
# 200 KiB source (past the 64 KiB cap). Built to a FILE — 200 KiB overflows ARGV.
BIGFILE="$(mktemp)"
bun -e 'const fs=require("fs"); fs.writeFileSync(process.argv[1], JSON.stringify({source:"x".repeat(200*1024)}));' "$BIGFILE"
status="$(curl -s -o /dev/null -w '%{http_code}' -X POST "${BASE}/run" \
  -H 'content-type: application/json' --data-binary "@$BIGFILE")"
printf '%s' "$status" > "$STATUS_FILE"
rm -f "$BIGFILE"
if [ "$(http_status)" = "413" ]; then
  ok "oversized body → 413"
else
  bad "oversized body — expected 413, got HTTP $(http_status)"
  echo "    resp: $resp"
fi

echo "── parse error (must return diagnostic, exit 1) ────────────────"
resp="$(post_run "{\"source\":$(bun -e 'process.stdout.write(JSON.stringify("let x ="))')}")"
pe_exit="$(field "$resp" exit)"
pe_stderr="$(field "$resp" stderr)"
if [ "$(http_status)" = "200" ] && [ "$pe_exit" = "1" ] && echo "$pe_stderr" | grep -qi "error"; then
  ok "parse error → exit 1 with diagnostic: $(echo "$pe_stderr" | head -1)"
else
  bad "parse error — expected exit 1 + diagnostic, got HTTP $(http_status) exit $pe_exit stderr=[$pe_stderr]"
  echo "    resp: $resp"
fi

echo "── rate limit (a burst past capacity must 429) ────────────────"
# Fire more requests than the bucket capacity in a tight burst from one IP.
export RUN_RATE_CAPACITY="${RUN_RATE_CAPACITY:-20}"
got_429=0
for _ in $(seq 1 40); do
  # shellcheck disable=SC2016  # `$(1 + 1)` is bang source (force+group), not a shell subshell
  code="$(curl -s -o /dev/null -w '%{http_code}' -X POST "${BASE}/run" \
    -H 'content-type: application/json' --data-binary '{"source":"$(1 + 1)"}' || true)"
  [ "$code" = "429" ] && { got_429=1; break; }
done
if [ "$got_429" = "1" ]; then
  ok "burst past capacity → 429"
else
  bad "rate limit — no 429 seen in a 40-request burst (capacity=$RUN_RATE_CAPACITY)"
fi

echo "───────────────────────────────────────────────────────────────"
echo "run-service smoke: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
