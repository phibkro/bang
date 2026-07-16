#!/usr/bin/env bash
# tool: role=test couples=Main.lean runs-in=verify
# Fail-closed option grammar for #178: typed values, command scope, duplicates, and pre-effect validation.
# Every rejection checks status, stdout silence, and a command-scoped diagnostic. The final sentinels prove the whole
# argument list is validated before any path-bearing file/host action can begin.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-$PWD/.lake/build/bin/bang}"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

tmpdir="$(mktemp -d --tmpdir bang-cli-options-XXXXXX)"
trap 'rm -rf "$tmpdir"' EXIT
stdout_file="$tmpdir/stdout"
stderr_file="$tmpdir/stderr"
program="$PWD/examples/state/main.bang"

checks=0
fail=0

ok() {
  local name="$1"
  checks=$((checks + 1))
  echo "✓ $name"
}

bad() {
  local name="$1" detail="$2"
  checks=$((checks + 1))
  fail=$((fail + 1))
  echo "✗ $name — $detail"
}

expect_eq() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then ok "$name"; else bad "$name" "expected [$want], got [$got]"; fi
}

expect_contains() {
  local name="$1" got="$2" needle="$3"
  if [[ "$got" == *"$needle"* ]]; then ok "$name"; else bad "$name" "expected [$needle] in [$got]"; fi
}

reject() {
  local name="$1" command="$2" needle="$3"
  shift 3
  local status=0 stdout stderr
  "$bang" "$@" >"$stdout_file" 2>"$stderr_file" || status=$?
  stdout="$(cat "$stdout_file")"
  stderr="$(cat "$stderr_file")"
  expect_eq "$name-exit" "$status" "1"
  expect_eq "$name-stdout-empty" "$stdout" ""
  expect_contains "$name-command-diagnostic" "$stderr" "bang $command"
  expect_contains "$name-offender-diagnostic" "$stderr" "$needle"
}

# Engine / execution options.
reject engine-invalid run "invalid value 'wat'" run --engine=wat "$program"
reject engine-missing-equals run "unknown option '--engine'" run --engine "$program"
reject engine-alias-duplicate eval "duplicate option '--engine=compiled'" \
  eval --compiled --engine=compiled 1
reject no-typecheck-duplicate eval "duplicate option '--no-typecheck'" \
  eval --no-typecheck --no-typecheck 1
reject fuel-invalid run "invalid value 'nope'" run --fuel nope "$program"
reject fuel-missing run "option '--fuel' requires a value" run "$program" --fuel
reject fuel-option-as-value run "option '--fuel' requires a value" run --fuel --compiled "$program"

# Host option families. A malformed/present --allow must never become grant-all.
reject env-invalid run "invalid value 'live'" run --env=live "$program"
reject env-duplicate run "duplicate option '--env=sim'" run --env=real --env=sim "$program"
reject allow-empty run "invalid value ''" run --allow= "$program"
reject allow-whitespace run "invalid value '   '" run "--allow=   " "$program"
reject allow-empty-segment run "invalid value 'Console,,Clock'" run --allow=Console,,Clock "$program"
reject allow-missing run "option '--allow' requires a value" run "$program" --allow
reject allow-option-as-value run "option '--allow' requires a value" run "$program" --allow --record=x
reject allow-duplicate run "duplicate option '--allow=Clock'" run --allow Console --allow=Clock "$program"
reject allow-label-duplicate run "duplicate labels are not allowed" run --allow=Console,Console "$program"
reject allow-trimmed-label-duplicate run "duplicate labels are not allowed" \
  run "--allow=Console, Console" "$program"
reject allow-short-option-not-value run "option '--allow' requires a value" run --allow -z "$program"
reject record-empty run "option '--record' requires a value" run --record= "$program"
reject record-missing run "option '--record' requires a value" run "$program" --record
reject record-duplicate run "duplicate option '--record=b'" run --record a --record=b "$program"
reject record-short-option-not-value run "option '--record' requires a value" run --record -z "$program"
reject replay-empty run "option '--replay' requires a value" run --replay= "$program"
reject replay-missing run "option '--replay' requires a value" run "$program" --replay
reject replay-duplicate run "duplicate option '--replay=b'" run --replay a --replay=b "$program"
reject replay-short-option-not-value run "option '--replay' requires a value" run --replay -z "$program"
reject record-replay-conflict run "'--record' and '--replay'" \
  run --record a --replay b "$program"
reject max-host-invalid run "invalid value 'many'" run --max-host-requests=many "$program"
reject max-host-missing run "option '--max-host-requests' requires a value" \
  run "$program" --max-host-requests
reject max-host-duplicate run "duplicate option '--max-host-requests=2'" \
  run --max-host-requests 1 --max-host-requests=2 "$program"

# Host modes are an explicit compatibility matrix, validated after the total token scan but before
# source resolution, trace access, or real host effects.
missing_source="$tmpdir/does-not-exist.bang"
reject allow-without-host-mode run "requires '--env=real' or '--replay'" \
  run --allow=Console "$missing_source"
reject allow-with-sim-only run "requires '--env=real' or '--replay'" \
  run --env=sim --allow=Console "$missing_source"
reject max-without-host-mode run "requires '--env=real' or '--replay'" \
  run --max-host-requests=0 "$missing_source"
reject max-with-sim-only run "requires '--env=real' or '--replay'" \
  run --env=sim --max-host-requests=0 "$missing_source"

absent_record_sentinel="$tmpdir/absent-record.ndjson"
reject record-without-real run "option '--record' requires '--env=real'" \
  run --record "$absent_record_sentinel" "$program"
expect_eq record-without-real-no-trace \
  "$(test ! -e "$absent_record_sentinel" && echo absent)" absent

sim_record_sentinel="$tmpdir/sim-record.ndjson"
reject record-with-sim run "option '--record' requires '--env=real'" \
  run --env=sim --record "$sim_record_sentinel" "$program"
expect_eq record-with-sim-no-trace \
  "$(test ! -e "$sim_record_sentinel" && echo absent)" absent

real_replay_sentinel="$tmpdir/real-replay-missing.ndjson"
reject replay-with-real run "option '--replay' cannot be used with '--env=real'" \
  run --env=real --replay "$real_replay_sentinel" "$program"
expect_eq replay-with-real-no-read \
  "$(test ! -e "$real_replay_sentinel" && echo absent)" absent

reject engine-with-real-host run "option '--engine'/'--compiled' is not valid" \
  run --env=real --engine=oracle "$missing_source"
reject no-typecheck-with-real-host run "option '--no-typecheck' is not valid" \
  run --env=real --no-typecheck "$missing_source"
reject engine-with-replay run "option '--engine'/'--compiled' is not valid" \
  run --replay "$real_replay_sentinel" --compiled "$missing_source"
reject no-typecheck-with-replay run "option '--no-typecheck' is not valid" \
  run --replay "$real_replay_sentinel" --no-typecheck "$missing_source"

ignored_record_sentinel="$tmpdir/ignored-engine-record.ndjson"
reject engine-with-record run "option '--engine'/'--compiled' is not valid" \
  run --env=real --record "$ignored_record_sentinel" --engine=env "$program"
expect_eq engine-with-record-no-trace \
  "$(test ! -e "$ignored_record_sentinel" && echo absent)" absent
reject no-typecheck-with-record run "option '--no-typecheck' is not valid" \
  run --env=real --record "$ignored_record_sentinel" --no-typecheck "$program"
expect_eq no-typecheck-with-record-no-trace \
  "$(test ! -e "$ignored_record_sentinel" && echo absent)" absent

# Agent output, artifact, scaffold, rewrite, and lint option families.
reject json-duplicate check "duplicate option '--json'" check --json "$program" --json
reject json-inappropriate run "option '--json' is not valid" run --json "$program"
reject out-empty emit "option '--out' requires a value" emit "$program" --out=
reject out-missing emit "option '-o' requires a value" emit "$program" -o
reject out-duplicate emit "duplicate option '--out=b.wat'" emit -o a.wat "$program" --out=b.wat
reject out-short-option-not-value emit "option '-o' requires a value" emit "$program" -o -z
reject component-duplicate build "duplicate option '--component'" \
  build "$program" --component --component
reject adapter-empty build "option '--adapter' requires a value" \
  build "$program" --component --adapter=
reject adapter-missing build "option '--adapter' requires a value" \
  build "$program" --component --adapter
reject adapter-duplicate build "duplicate option '--adapter=b.wasm'" \
  build --component --adapter a.wasm "$program" --adapter=b.wasm
reject adapter-short-option-not-value build "option '--adapter' requires a value" \
  build "$program" --component --adapter -z
reject adapter-without-component build "option '--adapter' requires '--component'" \
  build "$program" --adapter=a.wasm
reject module-duplicate new "duplicate option '--module'" new never-created --module --module
reject write-duplicate rewrite "duplicate option '-w'" rewrite -w fmt "$program" -w
reject write-inappropriate fmt "option '-w' is not valid" fmt -w "$program"
reject fix-duplicate lint "duplicate option '--fix'" lint --fix "$program" --fix
reject fix-json-conflict lint "option '--json' is not valid with '--fix'" lint --fix --json "$program"
reject quiet-duplicate lint "duplicate option '--quiet-clean'" \
  lint --quiet-clean "$program" --quiet-clean
reject quiet-fix-conflict lint "option '--quiet-clean' is not valid with '--fix'" \
  lint --fix --quiet-clean "$program"

# Unknown/inappropriate options and malformed positional values name the exact offender.
reject original-engine-typo run "unknown option '--engin=oracle'" run --engin=oracle "$program"
reject unknown-eq check "unknown option '--jsno=yes'" check --jsno=yes "$program"
reject unknown-short run "unknown option '-z'" run -z "$program"
reject query-json query "option '--json' is not valid" query --json dump "$program"
reject holes-flag holes "unknown option '--jsonish'" holes --jsonish "$program"
reject hover-line query "invalid line value 'nope'" query hover nope 1
reject hover-column query "invalid column value 'nope'" query hover 1 nope
reject help-extra --help "unexpected argument 'extra'" --help extra
reject version-extra --version "unexpected argument 'extra'" --version extra
reject repl-positional repl "unexpected positional argument 'extra'" repl extra
reject fmt-too-many fmt "got 2 positionals" fmt "$program" "$program"
reject run-too-many run "got 2" run "$program" "$program"

# A top-level unknown option is diagnosed explicitly instead of falling through to generic usage.
top_status=0
"$bang" --bogus >"$stdout_file" 2>"$stderr_file" || top_status=$?
expect_eq top-level-unknown-exit "$top_status" 1
expect_eq top-level-unknown-stdout-empty "$(cat "$stdout_file")" ""
expect_contains top-level-unknown-command-diagnostic "$(cat "$stderr_file")" "bang:"
expect_contains top-level-unknown-offender-diagnostic "$(cat "$stderr_file")" "unknown option '--bogus'"

unknown_command_status=0
"$bang" frobnicate >"$stdout_file" 2>"$stderr_file" || unknown_command_status=$?
expect_eq unknown-command-exit "$unknown_command_status" 1
expect_eq unknown-command-stdout-empty "$(cat "$stdout_file")" ""
expect_eq unknown-command-concise-diagnostic \
  "$(cat "$stderr_file")" "error: bang: unknown command 'frobnicate'"

# Whole-list validation precedes effects. Each invocation contains a valid path-bearing option
# followed by an unknown flag; none may read/write/execute before that later token is rejected.
record_sentinel="$tmpdir/should-not-record.ndjson"
reject record-no-side-effect run "unknown option '--late-typo'" \
  run --env=real "$program" --record "$record_sentinel" --late-typo
expect_eq record-no-side-effect-sentinel "$(test ! -e "$record_sentinel" && echo absent)" absent

replay_sentinel="$tmpdir/does-not-exist.ndjson"
reject replay-no-read run "unknown option '--late-typo'" \
  run "$program" --replay "$replay_sentinel" --late-typo
expect_eq replay-no-read-still-missing "$(test ! -e "$replay_sentinel" && echo absent)" absent

emit_sentinel="$tmpdir/should-not-emit.wat"
reject emit-no-side-effect emit "unknown option '--late-typo'" \
  emit "$program" -o "$emit_sentinel" --late-typo
expect_eq emit-no-side-effect-sentinel "$(test ! -e "$emit_sentinel" && echo absent)" absent

build_sentinel="$tmpdir/should-not-build.wasm"
reject build-no-side-effect build "unknown option '--late-typo'" \
  build "$program" -o "$build_sentinel" --late-typo
expect_eq build-no-side-effect-sentinel "$(test ! -e "$build_sentinel" && echo absent)" absent

# Valid compatibility controls: aliases, mixed-order flags, negative expressions, and zero ceilings.
run_out="$("$bang" run "$program" --fuel 100000 --engine=oracle --no-typecheck)"
expect_eq valid-run-mixed-order "$run_out" 5
eval_out="$("$bang" eval --fuel 100000 1 --compiled)"
expect_eq valid-compiled-alias-mixed-order "$eval_out" 1
negative_out="$("$bang" eval -1)"
expect_eq valid-negative-expression "$negative_out" -1
check_out="$("$bang" check "$program" --json)"
expect_contains valid-check-mixed-order "$check_out" '"ok":true'
real_out="$("$bang" run --allow=Console "$PWD/examples/hostio-echo/main.bang" \
  --max-host-requests=0 --env=real)"
expect_eq valid-real-host-options-mixed-order-zero "$real_out" ih

echo_main="$PWD/examples/hostio-echo/main.bang"
empty_trace="$tmpdir/empty.ndjson"
printf '\n' >"$empty_trace"
replay_out="$("$bang" run --env=sim --replay "$empty_trace" --allow=Console \
  --max-host-requests=0 "$echo_main")"
expect_eq valid-sim-replay-allow-max "$replay_out" ih

ambient_main="$PWD/examples/hostio-echo/ambient.bang"
reject allow-canonical-duplicate run "duplicate resolved labels are not allowed" \
  run --env=real --allow=Console,Io_Console "$ambient_main"

ambiguous_program="$tmpdir/ambiguous-allow.bang"
cat >"$ambiguous_program" <<'BANG'
effect A_Console { ping : Int -> Int }
effect B_Console { pong : Int -> Int }
let main = 1
BANG
reject allow-ambiguous-tail run "--allow name 'Console' is ambiguous" \
  run --env=real --allow=Console "$ambiguous_program"
help_out="$("$bang" --help)"
expect_contains valid-help "$help_out" "USAGE:"
expect_contains help-record-mode "$help_out" "requires --env=real"
expect_contains help-replay-mode "$help_out" "conflicts with --env=real"
version_out="$("$bang" --version)"
expect_contains valid-version "$version_out" "bang "

echo "──────────────────────────────"
echo "cli-options: $checks passed, $fail failed"
[ "$fail" -eq 0 ]
