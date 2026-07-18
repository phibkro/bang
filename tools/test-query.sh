#!/usr/bin/env bash
# shellcheck disable=SC2154 # `capture` assigns caller-named output/status variables dynamically.
# tool: role=test couples=Bang/Core/Fingerprint.lean,Bang/Frontend/Query.lean,Main.lean,examples/*/main.bang,examples/calc,examples/reactive-spreadsheet/Formulas.bang,examples/reactive-spreadsheet/expected-dependencies.json,examples/reactive-recomputation/Workload.bang,examples/reactive-observation-reuse/CachedWorkload.bang,tools/module-impact.py runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-query.sh — the non-interactive gate for `bang query <op>` (issue #80, the agent LSP as
# stateless CLI subcommands).
#
# Mirrors test-check-json.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# JSON-emitter internals (`jsonStr`/`jsonField`/`jsonObj` escaping, the schema's per-op byte-exact
# shape on a fixed input) are already gated at the Lean `#guard` level (Bang/Frontend/Query.lean) —
# this file gates the CLI SURFACE specifically: file-arg vs stdin, argument-order per op, the
# resolver-aware multi-file path (imports/qualification plus its actual transitive module DAG),
# the 0/1/2 exit-code contract observed
# THROUGH the binary, AND — the operator's API-first refinement (2026-07-10) — that `dump` is a
# genuine COMPLETE fact base (every curated verb's answer is provably a SUBSET/PROJECTION of what
# `dump` exports) plus a demonstration that a caller can COMPOSE an arbitrary query over `dump`'s
# JSON that no fixed verb answers (a ~5-line `jq` filter, gated below).
#
# GOTCHA (set -euo pipefail, per test-check-json.sh's own documented lesson): an unguarded
# `$(cmd1 | cmd2)` capture can kill this script SILENTLY mid-run. Every capture below either runs
# standalone (no pipe) with an explicit `&& … || …` exit-capture, or pipes into `grep`/`jq` with
# `|| true` on the capture. The FINAL line asserts the expected check COUNT.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-.lake/build/bin/bang}"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0

check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

# Capture stdout and the producer's status separately. Callers must assert the status; this avoids
# a matching JSON payload masking a nonzero CLI exit (and avoids a following grep/jq becoming the
# only status that survives a pipeline).
capture() {
  local out_var="$1" status_var="$2"
  shift 2
  local captured status
  if captured="$("$@")"; then status=0; else status=$?; fi
  printf -v "$out_var" '%s' "$captured"
  printf -v "$status_var" '%s' "$status"
}

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# ── fixtures ──
cat > "$tmpdir/simple.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let quad = {fun n => $double ($double n)}
let main = $quad 3
BANG

cat > "$tmpdir/laws.bang" <<'BANG'
trait Eq { fn eq(a, b) -> Int law refl(x): eq(x, x) == 1 }
impl Eq for Int { fn eq(a, b) = a }
0
BANG

# Resolved-program fingerprint variants. Each isolates one promised observation: formatting/comment
# noise, alpha-renaming, and a semantic negative-literal change (the deterministic collision v1 had).
cat > "$tmpdir/fingerprint-base.bang" <<'BANG'
let main = let x = -1 in x + 2
BANG
cat > "$tmpdir/fingerprint-format.bang" <<'BANG'
-- layout and comments disappear before the kernel boundary
let   main =
  let x=-1 in x+2
BANG
cat > "$tmpdir/fingerprint-alpha.bang" <<'BANG'
let main = let renamed = -1 in renamed + 2
BANG
cat > "$tmpdir/fingerprint-semantic.bang" <<'BANG'
let main = let x = -2 in x + 2
BANG
cat > "$tmpdir/fingerprint-invalid.bang" <<'BANG'
let main = 1 + Left(0)
BANG

# Resolved-module interface variants. The public implementation body and a private binding may move
# the whole-program core while preserving the exported interface; a public type change must move it.
for variant in interface-base interface-public-body interface-private-body interface-signature; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
0
BANG
done
cat > "$tmpdir/interface-base/Lib.bang" <<'BANG'
let hidden = 1
pub let answer : Int = 41
BANG
cat > "$tmpdir/interface-public-body/Lib.bang" <<'BANG'
let hidden = 1
pub let answer : Int = 42
BANG
cat > "$tmpdir/interface-private-body/Lib.bang" <<'BANG'
let hidden = 2
pub let answer : Int = 41
BANG
cat > "$tmpdir/interface-signature/Lib.bang" <<'BANG'
let hidden = 1
pub let answer : Int * Int = (41, 0)
BANG

# Structural declarations carry checked shapes rather than value types; retain a separate pole so
# the public firewall is gated for both sides of ModuleExportFact's type-or-shape contract.
for variant in interface-shape-base interface-shape-changed; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
0
BANG
done
cat > "$tmpdir/interface-shape-base/Lib.bang" <<'BANG'
pub data Signal = One(Int)
BANG
cat > "$tmpdir/interface-shape-changed/Lib.bang" <<'BANG'
pub data Signal = One(Int) | Pair(Int, Int)
BANG

# Runtime effect-label allocation remains whole-program and dense, but checked public rendering must
# project semantic names: adding an unrelated earlier effect may shift the lowered label without
# invalidating Lib's unchanged source interface.
for variant in interface-label-base interface-label-shifted; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/Lib.bang" <<'BANG'
pub effect Trace { log : Int -> Int }
pub let rec identity : Cap Trace -> Int -> Int ! {Trace} =
  fun tr => fun x => tr.log(x)
BANG
done
cat > "$tmpdir/interface-label-base/main.bang" <<'BANG'
import Lib
use Lib (Trace)
0
BANG
cat > "$tmpdir/interface-label-shifted/Noise.bang" <<'BANG'
pub effect Noise { ping : Int -> Int }
BANG
cat > "$tmpdir/interface-label-shifted/main.bang" <<'BANG'
import Noise
import Lib
use Lib (Trace)
0
BANG

# Nested effect rows are part of the public type. The old renderer failed to thread the effect table
# below `.U`, so `{Trace}` silently disappeared and a real signature change could preserve a digest.
for variant in interface-nested-row-base interface-nested-row-changed; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
use Lib (Trace)
0
BANG
done
cat > "$tmpdir/interface-nested-row-base/Lib.bang" <<'BANG'
pub effect Trace { log : Int -> Int }
pub let deferred : Thunk (Cap Trace -> Int -> Int ! {Trace}) =
  {fun tr => fun x => tr.log(x)}
BANG
cat > "$tmpdir/interface-nested-row-changed/Lib.bang" <<'BANG'
pub effect Trace { log : Int -> Int }
pub let deferred : Thunk (Cap Trace -> Int -> Int) =
  {fun tr => fun x => x}
BANG

# Two modules may declare the same local effect name. Their qualified semantic identities must stay
# distinct, and swapping import order must not move either module's public-interface digest.
for variant in interface-same-name-ab interface-same-name-ba; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/LibA.bang" <<'BANG'
pub effect Net { ping : Int -> Int }
pub let deferredA : Thunk (Cap LibA_Net -> Int -> Int ! {LibA_Net}) =
  {fun net => fun x => net.ping(x)}
BANG
  cat > "$tmpdir/$variant/LibB.bang" <<'BANG'
pub effect Net { ping : Int -> Int }
pub let deferredB : Thunk (Cap LibB_Net -> Int -> Int ! {LibB_Net}) =
  {fun net => fun x => net.ping(x)}
BANG
done
cat > "$tmpdir/interface-same-name-ab/main.bang" <<'BANG'
import LibA
import LibB
0
BANG
cat > "$tmpdir/interface-same-name-ba/main.bang" <<'BANG'
import LibB
import LibA
0
BANG

# Rows are sets. A dependency interface mentioning two imported effects must not inherit the global
# effect-table order when entry-side imports are reversed.
for variant in interface-two-row-ab interface-two-row-ba; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/EffA.bang" <<'BANG'
pub effect A { ping : Int -> Int }
BANG
  cat > "$tmpdir/$variant/EffB.bang" <<'BANG'
pub effect B { ping : Int -> Int }
BANG
  cat > "$tmpdir/$variant/Lib.bang" <<'BANG'
import EffA
import EffB
pub let deferred : Thunk (Cap EffA_A -> Cap EffB_B -> Int -> Int ! {EffA_A, EffB_B}) =
  {fun a => fun b => fun x => x}
BANG
done
cat > "$tmpdir/interface-two-row-ab/main.bang" <<'BANG'
import EffA
import EffB
import Lib
0
BANG
cat > "$tmpdir/interface-two-row-ba/main.bang" <<'BANG'
import EffB
import EffA
import Lib
0
BANG

# `pub`/divergence-tainted fixture — the composed-query demo's own corpus: ONE decl is both `pub`
# AND recursive (its type carries `Thunk!{Div}`, the ONLY place a v1 program's decl-level effect
# taint is visible — a top-level decl's OUTER `row` cannot yet carry a genuine user/custom label,
# since the `handle-with` D3 typed-custom-handle syntax (a live, separate lane's own work) hasn't
# landed; this fixture and the demo below are honest about v1's actual reach, not a hypothetical).
cat > "$tmpdir/pubdemo.bang" <<'BANG'
pub let rec fib : Int -> Int = fun n => if n < 2 then n else $fib (n - 1) + $fib (n - 2)
let helper = {fun n => $fib n + 1}
pub let pure_add = {fun a => fun b => a + b}
BANG

# Negative control for the spreadsheet dependency tracer: expression-local binders are not stable
# declaration facts, so the declaration-granular reference graph is intentionally empty. The
# recovery is the real `examples/reactive-spreadsheet/Formulas.bang` module gated below.
cat > "$tmpdir/local-formulas.bang" <<'BANG'
let input = {1} in
let formula = {$input} in
$formula
BANG

# Contract identity fixtures differ ONLY in the selected handler. Resolver-stable IDs must not
# churn merely because `use` deliberately keeps the selected source spelling bare.
mkdir -p "$tmpdir/resource-contract"
cp examples/resource-contract/Permit.bang "$tmpdir/resource-contract/Permit.bang"
cat > "$tmpdir/resource-contract/identity.bang" <<'BANG'
use Permit (Identity)

handle
  use [1] permit in permit.spend(7)
with Identity as permit
BANG
cat > "$tmpdir/resource-contract/negate.bang" <<'BANG'
use Permit (Negate)

handle
  use [1] permit in permit.spend(7)
with Negate as permit
BANG

# ══ 1. `dump` — THE key operation: the complete fact base ══

got_out="$("$bang" query dump "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "dump-exit" "$got_exit" "0"
check "dump-shape" "$got_out" '{"ok":true,"schemaVersion":1,"bangVersion":"0.1.1","coreFingerprint":{"scope":"resolved-program","algorithm":"bang-comp-struct-v2-uint64","digest":"8a70dde011d4e5b5","cacheKeySafe":false},"moduleInterfaces":[{"module":"@entry","scope":"resolved-program-module-interface","algorithm":"bang-module-interface-json-v1-uint64","digest":"46434a463a92408a","cacheKeySafe":false,"separateCompilationReady":false,"exports":[]}],"modules":[{"name":"@entry","origin":"entry"}],"moduleDeps":[],"decls":[{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"quad","kind":"let","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"main","kind":"let","type":"Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}],"refs":[{"from":"quad","to":"double"},{"from":"main","to":"quad"}],"laws":[],"imports":[],"uses":[]}'

# stdin agrees with file.
capture got_stdin got_stdin_exit "$bang" query dump 2>/dev/null < "$tmpdir/simple.bang"
check "dump-stdin-exit" "$got_stdin_exit" "0"
check "dump-stdin-eq-file" "$got_stdin" "$got_out"

# The result-hash firewall's smallest tracer: consume the compiler-emitted fact, not a parallel
# source hash. Equal core means formatting/comment and binder-name edits do not propagate; a real
# literal change does. The fact itself says it is NOT safe for persistent caching yet (64-bit and
# not compiler-version-domain-separated), and invalid typed input reports null instead of a hash.
capture fp_base_dump fp_base_exit "$bang" query dump "$tmpdir/fingerprint-base.bang" 2>/dev/null
capture fp_format_dump fp_format_exit "$bang" query dump "$tmpdir/fingerprint-format.bang" 2>/dev/null
capture fp_alpha_dump fp_alpha_exit "$bang" query dump "$tmpdir/fingerprint-alpha.bang" 2>/dev/null
capture fp_semantic_dump fp_semantic_exit "$bang" query dump "$tmpdir/fingerprint-semantic.bang" 2>/dev/null
check "core-fingerprint-base-exit" "$fp_base_exit" "0"
check "core-fingerprint-format-exit" "$fp_format_exit" "0"
check "core-fingerprint-alpha-exit" "$fp_alpha_exit" "0"
check "core-fingerprint-semantic-exit" "$fp_semantic_exit" "0"
capture fp_rows fp_rows_exit python3 -c 'import json,sys; ds=[json.loads(line) for line in sys.stdin if line.strip()]; fs=[d["coreFingerprint"] for d in ds]; print("|".join([fs[0]["scope"],fs[0]["algorithm"],str(fs[0]["cacheKeySafe"]).lower(),str(len(fs[0]["digest"])),str(fs[0]["digest"]==fs[1]["digest"]),str(fs[0]["digest"]==fs[2]["digest"]),str(fs[0]["digest"]!=fs[3]["digest"])]))' 2>/dev/null <<< "$fp_base_dump
$fp_format_dump
$fp_alpha_dump
$fp_semantic_dump"
check "core-fingerprint-extractor-exit" "$fp_rows_exit" "0"
check "core-fingerprint-invariance-and-discrimination" "$fp_rows" "resolved-program|bang-comp-struct-v2-uint64|false|16|True|True|True"
capture fp_invalid_dump fp_invalid_exit "$bang" query dump "$tmpdir/fingerprint-invalid.bang" 2>/dev/null
capture fp_invalid_value fp_invalid_value_exit python3 -c 'import json,sys; print("null" if json.load(sys.stdin)["coreFingerprint"] is None else "present")' 2>/dev/null <<< "$fp_invalid_dump"
check "core-fingerprint-invalid-dump-exit" "$fp_invalid_exit" "0"
check "core-fingerprint-invalid-extractor-exit" "$fp_invalid_value_exit" "0"
check "core-fingerprint-invalid-null" "$fp_invalid_value" "null"
capture iface_invalid_value iface_invalid_value_exit python3 -c 'import json,sys; print("null" if json.load(sys.stdin)["moduleInterfaces"] is None else "present")' 2>/dev/null <<< "$fp_invalid_dump"
check "module-interface-invalid-extractor-exit" "$iface_invalid_value_exit" "0"
check "module-interface-invalid-null" "$iface_invalid_value" "null"

# Interface and implementation are distinct invalidation boundaries. All four projects type-check;
# body/private changes move the current flat core but not Lib's checked public interface, while a
# signature change moves both. Metadata stays explicit that these facts are whole-program-derived,
# 64-bit, and not an independently compiled artifact.
capture iface_base_dump iface_base_exit "$bang" query dump "$tmpdir/interface-base/main.bang" 2>/dev/null
capture iface_public_dump iface_public_exit "$bang" query dump "$tmpdir/interface-public-body/main.bang" 2>/dev/null
capture iface_private_dump iface_private_exit "$bang" query dump "$tmpdir/interface-private-body/main.bang" 2>/dev/null
capture iface_signature_dump iface_signature_exit "$bang" query dump "$tmpdir/interface-signature/main.bang" 2>/dev/null
check "module-interface-base-exit" "$iface_base_exit" "0"
check "module-interface-public-body-exit" "$iface_public_exit" "0"
check "module-interface-private-body-exit" "$iface_private_exit" "0"
check "module-interface-signature-exit" "$iface_signature_exit" "0"
capture iface_rows iface_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
cores=[d["coreFingerprint"]["digest"] for d in ds]
libs=[next(x for x in d["moduleInterfaces"] if x["module"]=="Lib") for d in ds]
meta=libs[0]
export=meta["exports"]
print("|".join([
  meta["scope"],meta["algorithm"],str(meta["cacheKeySafe"]).lower(),
  str(meta["separateCompilationReady"]).lower(),str(len(meta["digest"])),
  str(export==[{"id":"Lib::answer","name":"answer","kind":"let","type":"Int","row":"{}","typeError":None,"shape":None}]),
  str(libs[0]["digest"]==libs[1]["digest"]==libs[2]["digest"]),
  str(libs[0]["digest"]!=libs[3]["digest"]),
  str(cores[0]!=cores[1] and cores[0]!=cores[2] and cores[0]!=cores[3])]))
' 2>/dev/null <<< "$iface_base_dump
$iface_public_dump
$iface_private_dump
$iface_signature_dump"
check "module-interface-extractor-exit" "$iface_rows_exit" "0"
check "module-interface-boundary-discrimination" "$iface_rows" "resolved-program-module-interface|bang-module-interface-json-v1-uint64|false|false|16|True|True|True|True"

capture iface_shape_base_dump iface_shape_base_exit "$bang" query dump "$tmpdir/interface-shape-base/main.bang" 2>/dev/null
capture iface_shape_changed_dump iface_shape_changed_exit "$bang" query dump "$tmpdir/interface-shape-changed/main.bang" 2>/dev/null
check "module-interface-shape-base-exit" "$iface_shape_base_exit" "0"
check "module-interface-shape-changed-exit" "$iface_shape_changed_exit" "0"
capture iface_shape_rows iface_shape_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
libs=[next(x for x in d["moduleInterfaces"] if x["module"]=="Lib") for d in ds]
exports=[lib["exports"][0] for lib in libs]
print("|".join([str(libs[0]["digest"]!=libs[1]["digest"]),str(exports[0]["shape"]!=exports[1]["shape"]),str(exports[0]["type"] is None and exports[1]["type"] is None)]))
' 2>/dev/null <<< "$iface_shape_base_dump
$iface_shape_changed_dump"
check "module-interface-shape-extractor-exit" "$iface_shape_rows_exit" "0"
check "module-interface-shape-discrimination" "$iface_shape_rows" "True|True|True"

# An unchanged module's checked interface is now invariant when an unrelated earlier effect shifts
# its runtime label. `separateCompilationReady` remains false: lowered bodies still carry the dense
# labels, and there is still no independent code artifact or linker contract.
capture iface_label_base_dump iface_label_base_exit "$bang" query dump "$tmpdir/interface-label-base/main.bang" 2>/dev/null
capture iface_label_shifted_dump iface_label_shifted_exit "$bang" query dump "$tmpdir/interface-label-shifted/main.bang" 2>/dev/null
check "module-interface-label-base-exit" "$iface_label_base_exit" "0"
check "module-interface-label-shifted-exit" "$iface_label_shifted_exit" "0"
capture iface_label_rows iface_label_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
libs=[next(x for x in d["moduleInterfaces"] if x["module"]=="Lib") for d in ds]
types=[next(x for x in lib["exports"] if x["name"]=="identity")["type"] for lib in libs]
print("|".join([str(libs[0]["digest"]==libs[1]["digest"]),str(types[0]==types[1]),types[0],types[1]]))
' 2>/dev/null <<< "$iface_label_base_dump
$iface_label_shifted_dump"
check "module-interface-label-extractor-exit" "$iface_label_rows_exit" "0"
check "module-interface-semantic-label-invariance" "$iface_label_rows" "True|True|Thunk!{Trace} Cap Trace -> Int -> Int|Thunk!{Trace} Cap Trace -> Int -> Int"

capture iface_nested_base_dump iface_nested_base_exit "$bang" query dump "$tmpdir/interface-nested-row-base/main.bang" 2>/dev/null
capture iface_nested_changed_dump iface_nested_changed_exit "$bang" query dump "$tmpdir/interface-nested-row-changed/main.bang" 2>/dev/null
check "module-interface-nested-row-base-exit" "$iface_nested_base_exit" "0"
check "module-interface-nested-row-changed-exit" "$iface_nested_changed_exit" "0"
capture iface_nested_rows iface_nested_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
libs=[next(x for x in d["moduleInterfaces"] if x["module"]=="Lib") for d in ds]
types=[next(x for x in lib["exports"] if x["name"]=="deferred")["type"] for lib in libs]
print("|".join([str(libs[0]["digest"]!=libs[1]["digest"]),types[0],types[1]]))
' 2>/dev/null <<< "$iface_nested_base_dump
$iface_nested_changed_dump"
check "module-interface-nested-row-extractor-exit" "$iface_nested_rows_exit" "0"
check "module-interface-nested-row-sensitivity" "$iface_nested_rows" "True|Thunk!{Trace} Cap Trace -> Int -> Int|Thunk Cap Trace -> Int -> Int"

capture iface_same_ab_dump iface_same_ab_exit "$bang" query dump "$tmpdir/interface-same-name-ab/main.bang" 2>/dev/null
capture iface_same_ba_dump iface_same_ba_exit "$bang" query dump "$tmpdir/interface-same-name-ba/main.bang" 2>/dev/null
check "module-interface-same-name-ab-exit" "$iface_same_ab_exit" "0"
check "module-interface-same-name-ba-exit" "$iface_same_ba_exit" "0"
capture iface_same_rows iface_same_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
def module(d,n): return next(x for x in d["moduleInterfaces"] if x["module"]==n)
mods=[[module(d,"LibA"),module(d,"LibB")] for d in ds]
types=[[next(x for x in m["exports"] if x["name"].startswith("deferred"))["type"] for m in pair] for pair in mods]
print("|".join([str(mods[0][0]["digest"]==mods[1][0]["digest"]),str(mods[0][1]["digest"]==mods[1][1]["digest"]),str(types[0][0]!=types[0][1]),types[0][0],types[0][1]]))
' 2>/dev/null <<< "$iface_same_ab_dump
$iface_same_ba_dump"
check "module-interface-same-name-extractor-exit" "$iface_same_rows_exit" "0"
check "module-interface-same-name-separation" "$iface_same_rows" "True|True|True|Thunk!{LibA_Net} Cap LibA_Net -> Int -> Int|Thunk!{LibB_Net} Cap LibB_Net -> Int -> Int"

capture iface_two_ab_dump iface_two_ab_exit "$bang" query dump "$tmpdir/interface-two-row-ab/main.bang" 2>/dev/null
capture iface_two_ba_dump iface_two_ba_exit "$bang" query dump "$tmpdir/interface-two-row-ba/main.bang" 2>/dev/null
check "module-interface-two-row-ab-exit" "$iface_two_ab_exit" "0"
check "module-interface-two-row-ba-exit" "$iface_two_ba_exit" "0"
capture iface_two_rows iface_two_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
libs=[next(x for x in d["moduleInterfaces"] if x["module"]=="Lib") for d in ds]
types=[next(x for x in lib["exports"] if x["name"]=="deferred")["type"] for lib in libs]
print("|".join([str(libs[0]["digest"]==libs[1]["digest"]),str(types[0]==types[1]),types[0],types[1]]))
' 2>/dev/null <<< "$iface_two_ab_dump
$iface_two_ba_dump"
check "module-interface-two-row-extractor-exit" "$iface_two_rows_exit" "0"
check "module-interface-two-row-order-invariance" "$iface_two_rows" "True|True|Thunk!{EffA_A, EffB_B} Cap EffA_A -> Cap EffB_B -> Int -> Int|Thunk!{EffA_A, EffB_B} Cap EffA_A -> Cap EffB_B -> Int -> Int"

# EVERY curated verb's answer is a PROJECTION of `dump` — the layering claim, checked directly:
# `symbols`'s "decls" entries equal `dump`'s "decls" entries byte-for-byte (same DeclFact.toJson).
capture got_symbols got_symbols_exit "$bang" query symbols "$tmpdir/simple.bang" 2>/dev/null
capture got_dump_decls got_dump_decls_exit python3 -c 'import json,sys; d=json.load(sys.stdin); print(json.dumps({"ok":True,"symbols":d["decls"]}, separators=(",",":")))' 2>/dev/null <<< "$got_out"
check "symbols-projection-exit" "$got_symbols_exit" "0"
check "dump-decls-extractor-exit" "$got_dump_decls_exit" "0"
check "symbols-is-dump-decls-projection" "$got_symbols" "$got_dump_decls"

# a parse failure is an OP-LEVEL answer (exit 1, ok:false on stdout — NOT a tool error).
got_out2="$(printf 'let x 3 in x' | "$bang" query dump 2>/dev/null)" && got_exit2=0 || got_exit2=$?
check "dump-parse-error-ok-false" "$(printf '%s' "$got_out2" | grep -o '"ok":false' || true)" '"ok":false'
check "dump-parse-error-exit" "$got_exit2" "1"

# dump's law/impl/trait facts — a decls-only fixture with a trait+impl+law.
got_out3="$("$bang" query dump "$tmpdir/laws.bang" 2>/dev/null)" && got_exit3=0 || got_exit3=$?
check "dump-laws-exit" "$got_exit3" "0"
check "dump-laws-present" "$(printf '%s' "$got_out3" | grep -o '"laws":\[{"trait":"Eq"' || true)" '"laws":[{"trait":"Eq"'
check "dump-trait-shape-present" "$(printf '%s' "$got_out3" | grep -o '"kind":"trait"' || true)" '"kind":"trait"'
check "dump-impl-shape-present" "$(printf '%s' "$got_out3" | grep -o '"kind":"impl"' || true)" '"kind":"impl"'

# every examples/*/main.bang round-trips ok:true through `dump` (the corpus, not just one file).
examples_pass=0
examples_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  if out="$("$bang" query dump "$main" 2>/dev/null)"; then
    out_exit=0
  else
    out_exit=$?
  fi
  if [ "$out_exit" -eq 0 ] && printf '%s' "$out" | grep -q '"ok":true'; then
    examples_pass=$((examples_pass + 1))
  else
    echo "✗ dump-examples-corpus — $name exited $out_exit or did not report ok:true: $out"
    examples_fail=$((examples_fail + 1))
  fi
done
check "dump-examples-corpus-all-ok" "$examples_fail" "0"
echo "  (dump examples corpus: $examples_pass/$((examples_pass + examples_fail)) ok:true)"

# ── MULTI-FILE dump: imports field must reflect the ENTRY file's OWN header (a real fidelity gap
# found+fixed this slice — `mergeModules` clears `imports`/`uses` on its merged output, so `dump`
# must thread the pre-merge header as presentation data without mutating the semantic `Prog`;
# falsify by requiring both a NONEMPTY header and a non-null resolved core/interface). ──
got_out4="$("$bang" query dump examples/json/main.bang 2>/dev/null)" && got_exit4=0 || got_exit4=$?
check "dump-multifile-exit" "$got_exit4" "0"
check "dump-multifile-imports-present" "$(printf '%s' "$got_out4" | grep -o '"imports":\[{"module":"Json"}' || true)" '"imports":[{"module":"Json"}'
check "dump-multifile-qualified-present" "$(printf '%s' "$got_out4" | grep -o '"name":"Parse_dropWs"' || true)" '"name":"Parse_dropWs"'
check "dump-multifile-core-present" "$(printf '%s' "$got_out4" | grep -o '"coreFingerprint":{"scope":"resolved-program"' || true)" '"coreFingerprint":{"scope":"resolved-program"'
check "dump-multifile-interfaces-present" "$(printf '%s' "$got_out4" | grep -o '"moduleInterfaces":\[{"module":"@entry"' || true)" '"moduleInterfaces":[{"module":"@entry"'

# The resolver's completed dependency-first walk is the SSoT for topology: JSON is a diamond, so
# the public facts must contain four logical nodes and five direct edges exactly once. The facts
# deliberately expose language-level identities/origins, never host paths.
capture json_graph json_graph_exit python3 -c 'import json,sys; d=json.load(sys.stdin); print(json.dumps({"modules":d["modules"],"moduleDeps":d["moduleDeps"]}, separators=(",",":")))' 2>/dev/null <<< "$got_out4"
check "dump-module-graph-extractor-exit" "$json_graph_exit" "0"
check "dump-module-graph-diamond" "$json_graph" '{"modules":[{"name":"@entry","origin":"entry"},{"name":"Json","origin":"project"},{"name":"Parse","origin":"project"},{"name":"Print","origin":"project"}],"moduleDeps":[{"from":"@entry","to":"Json"},{"from":"@entry","to":"Parse"},{"from":"@entry","to":"Print"},{"from":"Parse","to":"Json"},{"from":"Print","to":"Json"}]}'
check "dump-module-graph-path-free" "$(printf '%s' "$json_graph" | grep -o '/' || true)" ""

# Bundled compiler modules retain their distinct origin without exposing an implementation path.
capture bundled_dump bundled_dump_exit "$bang" query dump examples/hostio-echo/main.bang 2>/dev/null
capture bundled_graph bundled_graph_exit python3 -c 'import json,sys; d=json.load(sys.stdin); print(json.dumps({"modules":d["modules"],"moduleDeps":d["moduleDeps"]}, separators=(",",":")))' 2>/dev/null <<< "$bundled_dump"
check "dump-module-graph-bundled-exit" "$bundled_dump_exit" "0"
check "dump-module-graph-bundled-extractor-exit" "$bundled_graph_exit" "0"
check "dump-module-graph-bundled-origin" "$bundled_graph" '{"modules":[{"name":"@entry","origin":"entry"},{"name":"Io","origin":"bundled"}],"moduleDeps":[{"from":"@entry","to":"Io"}]}'

# ── REUSABLE INVALIDATION-FANOUT CONSUMER: this is the product proof that flat resolver facts are
# sufficient for a build-tool question without adding another fixed compiler verb. The measurement
# is deliberately module/change PAIRS, never latency or cache hits. Calc's shared Ast graph avoids
# 21 of 36 whole-program pairs while making the common-dependency worst case explicit. ──
capture calc_dump calc_dump_exit "$bang" query dump examples/calc/main.bang 2>/dev/null
capture calc_impact calc_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$calc_dump"
check "module-impact-calc-dump-exit" "$calc_dump_exit" "0"
check "module-impact-calc-exit" "$calc_impact_exit" "0"
check "module-impact-calc-exact" "$calc_impact" '{"ok":true,"schemaVersion":1,"moduleCount":6,"impacts":[{"changed":"@entry","affected":["@entry"],"affectedCount":1},{"changed":"Ast","affected":["@entry","Ast","Lexer","Parser","Eval","Print"],"affectedCount":6},{"changed":"Lexer","affected":["@entry","Lexer"],"affectedCount":2},{"changed":"Parser","affected":["@entry","Parser"],"affectedCount":2},{"changed":"Eval","affected":["@entry","Eval"],"affectedCount":2},{"changed":"Print","affected":["@entry","Print"],"affectedCount":2}],"structuralWork":{"wholeProgramPairs":36,"dependencyPairs":15,"avoidedPairs":21}}'

capture json_impact json_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$got_out4"
check "module-impact-json-exit" "$json_impact_exit" "0"
check "module-impact-json-exact" "$json_impact" '{"ok":true,"schemaVersion":1,"moduleCount":4,"impacts":[{"changed":"@entry","affected":["@entry"],"affectedCount":1},{"changed":"Json","affected":["@entry","Json","Parse","Print"],"affectedCount":4},{"changed":"Parse","affected":["@entry","Parse"],"affectedCount":2},{"changed":"Print","affected":["@entry","Print"],"affectedCount":2}],"structuralWork":{"wholeProgramPairs":16,"dependencyPairs":9,"avoidedPairs":7}}'

capture single_impact single_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$got_out"
check "module-impact-single-exit" "$single_impact_exit" "0"
check "module-impact-single-exact" "$single_impact" '{"ok":true,"schemaVersion":1,"moduleCount":1,"impacts":[{"changed":"@entry","affected":["@entry"],"affectedCount":1}],"structuralWork":{"wholeProgramPairs":1,"dependencyPairs":1,"avoidedPairs":0}}'

# Consumer-side half of additive schema evolution: inject an unknown nested field and require the
# analysis to remain byte-identical. Corrupt topology, by contrast, must fail loudly.
capture synthetic_module_extra synthetic_module_extra_exit python3 -c 'import json,sys; d=json.load(sys.stdin); d["futureField"]={"nested":[1,2,3]}; print(json.dumps(d,separators=(",",":")))' 2>/dev/null <<< "$calc_dump"
capture future_impact future_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$synthetic_module_extra"
check "module-impact-additive-fixture-exit" "$synthetic_module_extra_exit" "0"
check "module-impact-ignore-unknown-exit" "$future_impact_exit" "0"
check "module-impact-ignore-unknown-equal" "$future_impact" "$calc_impact"

dangling_graph='{"ok":true,"schemaVersion":1,"modules":[{"name":"@entry"}],"moduleDeps":[{"from":"@entry","to":"Ghost"}]}'
duplicate_graph='{"ok":true,"schemaVersion":1,"modules":[{"name":"@entry"},{"name":"A"}],"moduleDeps":[{"from":"@entry","to":"A"},{"from":"@entry","to":"A"}]}'
cycle_graph='{"ok":true,"schemaVersion":1,"modules":[{"name":"@entry"},{"name":"A"}],"moduleDeps":[{"from":"@entry","to":"A"},{"from":"A","to":"@entry"}]}'
capture dangling_impact dangling_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$dangling_graph"
capture duplicate_impact duplicate_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$duplicate_graph"
capture cycle_impact cycle_impact_exit python3 tools/module-impact.py 2>/dev/null <<< "$cycle_graph"
check "module-impact-dangling-refused" "$dangling_impact_exit" "1"
check "module-impact-duplicate-refused" "$duplicate_impact_exit" "1"
check "module-impact-cycle-refused" "$cycle_impact_exit" "1"

# ── Resolver-aware LAW FACTS: the Codec entry imports its effect contract + two named handler
# realizations. `dump` and the curated `laws` view must expose the SAME qualified effect×handler
# instances instead of the old multi-file `laws:[]` grant. ──
codec_dump="$($bang query dump examples/codec-contract/main.bang 2>/dev/null)" && codec_dump_exit=0 || codec_dump_exit=$?
check "dump-multifile-codec-exit" "$codec_dump_exit" "0"
contains_codec='"contract":"Codec_Codec","realization":"Shift7","law":"decode_encode"'
check "dump-multifile-codec-laws" "$(printf '%s' "$codec_dump" | grep -o "$contains_codec" || true)" "$contains_codec"
codec_laws="$($bang query laws examples/codec-contract/main.bang 2>/dev/null)" && codec_laws_exit=0 || codec_laws_exit=$?
check "laws-multifile-codec-exit" "$codec_laws_exit" "0"
check "laws-multifile-codec-view" "$(printf '%s' "$codec_laws" | grep -o "$contains_codec" || true)" "$contains_codec"

# ── GOLDEN-DUMP DRIFT TEST (the DBMS survey's eager-schema-discipline item, §6/§8, REFINED by the
# operator's schemaVersion/bangVersion-disjointness ruling — a pinned `dump` output that FAILS CI
# when the shape drifts UN-versioned; the "test" rung of the derivation-strength ladder applied to
# a public JSON contract). tools/golden-dump-caesar.json is the pinned snapshot of `bang query dump
# examples/caesar/main.bang`; a real BREAKING shape change (a rename/removal/meaning-change) must
# EITHER re-pin this file in the SAME commit as a schemaVersion bump, or the diff is dishonest — a
# schema-version bump with NO re-pin, or a re-pin with NO version bump, are both caught by this
# byte-exact check. An ADDITIVE change (a new field/table) is non-breaking BY CONTRACT (consumers
# must ignore unknown fields — see the demo below) so it does NOT require a schemaVersion bump, but
# STILL requires a golden re-pin (the byte-exact snapshot changed) — the two are orthogonal checks,
# not the same gate. ──
got_golden="$("$bang" query dump examples/caesar/main.bang 2>/dev/null)" && got_golden_exit=0 || got_golden_exit=$?
want_golden="$(cat tools/golden-dump-caesar.json)"
check "golden-dump-exit" "$got_golden_exit" "0"
check "golden-dump-schema-pinned" "$got_golden" "$want_golden"

# ── schemaVersion / bangVersion DISJOINTNESS (operator ruling): schemaVersion is a plain monotonic
# integer (the CONTRACT), bangVersion is compiler provenance — never conflated, never the same
# field. A durable consumer keys ITS compatibility check on schemaVersion alone. ──
check "schema-bang-version-disjoint" "$(printf '%s' "$got_golden" | grep -o '"schemaVersion":1,"bangVersion":"' || true)" '"schemaVersion":1,"bangVersion":"'

# ── THE "IGNORE UNKNOWN FIELDS" CONSUMER CONTRACT (protobuf/k8s discipline, operator-ruled): a
# durable agent script that only reads schemaVersion + decls must survive an ADDITIVE schema change
# (a new top-level field the script never asked for). Simulated here by injecting a synthetic extra
# field into a copy of dump's real output and confirming a naive jq extraction still works —
# demonstrates the CONSUMER half of the contract, not just the producer's schemaVersion field. ──
if command -v jq >/dev/null 2>&1; then
  synthetic_extra="$(printf '%s' "$got_golden" | jq -c '. + {"futureField": {"nested": [1,2,3]}}')"
  extracted="$(printf '%s' "$synthetic_extra" | jq -r '.schemaVersion')"
  check "ignore-unknown-fields-contract" "$extracted" "1"
else
  echo "· ignore-unknown-fields-contract — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

# ── CONCRETE RELATIONAL-SHAPE GATE (operator ruling, compiler-as-dbms-survey.md): the golden dump
# must load into DuckDB with ONE `read_json` call, no unnesting gymnastics — `decls`/`refs` are
# FLAT top-level arrays of flat records (Glean's "predicates = tables" framing), never a nested
# tree. `duckdb` is NOT in the flake (an ad-hoc `nix shell nixpkgs#duckdb`, matching the cross-
# project tooling convention for occasional CLI reach) — SKIPPED (not failed) if unavailable, the
# SAME jq-optionality precedent this file already follows. ──
duckdb_ran=0
if command -v duckdb >/dev/null 2>&1; then
  capture duckdb_rows duckdb_exit duckdb -csv -noheader -c "SELECT count(*) FROM (SELECT unnest(decls) AS d FROM read_json('tools/golden-dump-caesar.json'))" 2>/dev/null
  check "golden-dump-duckdb-exit" "$duckdb_exit" "0"
  check "golden-dump-duckdb-loadable" "$duckdb_rows" "7"
  duckdb_ran=1
else
  echo "· golden-dump-duckdb-loadable — SKIPPED (duckdb not in dev shell; reach via 'nix shell nixpkgs#duckdb -c bash tools/test-query.sh' to exercise this check)"
fi

# ══ 2. THE COMPOSED-QUERY DEMO (operator-required, #80 refinement): a question no fixed verb
# answers — "every EXPORTED (pub) decl whose type carries a divergence taint" — via a jq filter
# over `dump`'s own output, ~5 lines, zero new Lean code. Skipped (not failed) if jq is absent from
# the dev shell, matching test-check-json.sh's own jq-optionality precedent. ──
if command -v jq >/dev/null 2>&1; then
  capture composed_dump composed_dump_exit "$bang" query dump "$tmpdir/pubdemo.bang" 2>/dev/null
  capture composed composed_jq_exit jq -c '[.decls[] | select(.pub and ((.type // "") | contains("Div"))) | .name]' <<< "$composed_dump"
  check "composed-query-dump-exit" "$composed_dump_exit" "0"
  check "composed-query-filter-exit" "$composed_jq_exit" "0"
  check "composed-query-pub-divergent" "$composed" '["fib"]'
else
  echo "· composed-query-pub-divergent — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

# ══ 2b. REACTIVE FORMULA DAG — dependency observation reuses dump's existing refs ══

if python3 tools/gen-reactive-workload.py --check; then workload_fresh=0; else workload_fresh=$?; fi
check "reactive-measure-generated-fixture-fresh" "$workload_fresh" "0"

capture reactive_dump reactive_dump_exit "$bang" query dump examples/reactive-spreadsheet/Formulas.bang 2>/dev/null
capture reactive_edges reactive_edges_exit python3 -c \
  'import json,sys; print(json.dumps(json.load(sys.stdin)["refs"],separators=(",",":")))' \
  <<< "$reactive_dump"
reactive_edges_want="$(cat examples/reactive-spreadsheet/expected-dependencies.json)"
check "reactive-deps-dump-exit" "$reactive_dump_exit" "0"
check "reactive-deps-extractor-exit" "$reactive_edges_exit" "0"
check "reactive-deps-exact-graph" "$reactive_edges" "$reactive_edges_want"

capture reactive_impact reactive_impact_exit "$bang" impact \
  examples/reactive-spreadsheet/Formulas.bang subtotal 2>/dev/null
check "reactive-deps-impact-exit" "$reactive_impact_exit" "0"
check "reactive-deps-impact-subtotal" "$reactive_impact" \
  '{"ok":true,"decl":"subtotal","dependents":[{"name":"total","kind":"let"},{"name":"tax","kind":"let"}]}'

capture local_dump local_dump_exit "$bang" query dump "$tmpdir/local-formulas.bang" 2>/dev/null
capture local_edges local_edges_exit python3 -c \
  'import json,sys; print(json.dumps(json.load(sys.stdin)["refs"],separators=(",",":")))' \
  <<< "$local_dump"
check "reactive-deps-local-negative-dump-exit" "$local_dump_exit" "0"
check "reactive-deps-local-negative-extractor-exit" "$local_edges_exit" "0"
check "reactive-deps-local-negative-empty" "$local_edges" "[]"

# The representative measurement workload keeps graph shape separate from the in-band runtime count.
# This summary catches a shortened workload, direct line→input bypass, or fan-in drift without checking
# in a second 202-edge fixture.
capture measured_dump measured_dump_exit "$bang" query dump \
  examples/reactive-recomputation/Workload.bang 2>/dev/null
capture measured_shape measured_shape_exit python3 -c '
import json, sys
d = json.load(sys.stdin)
refs = d["refs"]
decls = d["decls"]
summary = {
    "decls": len(decls),
    "refs": len(refs),
    "lines": sum(x["name"].startswith("line") for x in decls),
    "priceRefs": sum(x["to"] == "price" for x in refs),
    "quantityRefs": sum(x["to"] == "quantity" for x in refs),
    "unitAmountRefs": sum(x["to"] == "unitAmount" for x in refs),
    "totalRefs": sum(x["from"] == "total" for x in refs),
    "lineInputBypasses": sum(x["from"].startswith("line") and x["to"] in {"price", "quantity"} for x in refs),
}
print(json.dumps(summary, separators=(",", ":")))
' <<< "$measured_dump"
check "reactive-measure-dump-exit" "$measured_dump_exit" "0"
check "reactive-measure-shape-extractor-exit" "$measured_shape_exit" "0"
check "reactive-measure-exact-shape" "$measured_shape" \
  '{"decls":104,"refs":202,"lines":100,"priceRefs":1,"quantityRefs":1,"unitAmountRefs":100,"totalRefs":100,"lineInputBypasses":0}'

# The observation-scoped Memo capability must change runtime policy without changing formula edges.
capture uncached_measured_refs uncached_measured_refs_exit python3 -c \
  'import json,sys; print(json.dumps(json.load(sys.stdin)["refs"],separators=(",",":")))' \
  <<< "$measured_dump"
capture cached_measured_dump cached_measured_dump_exit "$bang" query dump \
  examples/reactive-observation-reuse/CachedWorkload.bang 2>/dev/null
capture cached_measured_refs cached_measured_refs_exit python3 -c \
  'import json,sys; print(json.dumps(json.load(sys.stdin)["refs"],separators=(",",":")))' \
  <<< "$cached_measured_dump"
check "reactive-reuse-uncached-refs-extractor-exit" "$uncached_measured_refs_exit" "0"
check "reactive-reuse-dump-exit" "$cached_measured_dump_exit" "0"
check "reactive-reuse-refs-extractor-exit" "$cached_measured_refs_exit" "0"
check "reactive-reuse-preserves-formula-graph" "$cached_measured_refs" "$uncached_measured_refs"

# ══ 3. `symbols` (thin projection of dump's "decls") ══

got_out="$("$bang" query symbols "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-exit" "$got_exit" "0"
check "symbols-shape" "$got_out" '{"ok":true,"symbols":[{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"quad","kind":"let","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"main","kind":"let","type":"Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}]}'

capture got_stdin got_stdin_exit "$bang" query symbols 2>/dev/null < "$tmpdir/simple.bang"
check "symbols-stdin-exit" "$got_stdin_exit" "0"
check "symbols-stdin-eq-file" "$got_stdin" "$got_out"

got_out="$(printf 'let x 3 in x' | "$bang" query symbols 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-parse-error-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "symbols-parse-error-exit" "$got_exit" "1"

# ══ 4. `type` / `effects` ══

got_out="$("$bang" query type "$tmpdir/simple.bang" double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-exit" "$got_exit" "0"
check "type-shape" "$got_out" '{"ok":true,"type":"Thunk Int -> Int","row":"{}"}'

got_out="$("$bang" query effects double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "effects-exit" "$got_exit" "0"
check "effects-shape" "$got_out" '{"ok":true,"row":"{}"}'

got_out="$(cat "$tmpdir/simple.bang" | "$bang" query effects double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "effects-stdin-exit" "$got_exit" "0"
check "effects-stdin-shape" "$got_out" '{"ok":true,"row":"{}"}'

# naming a nonexistent decl is a LOUD op-level miss (ok:false ON STDOUT) but exit 0: the TOOL ran
# successfully and produced a well-formed (negative) answer (exit 1 is reserved for "the op could
# NOT run" — a parse/resolution failure — not an op-level negative answer).
got_out="$("$bang" query type "$tmpdir/simple.bang" nosuch 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-miss-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "type-miss-exit" "$got_exit" "0"

# ══ 5. `laws` ══

got_out="$("$bang" query laws "$tmpdir/laws.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-exit" "$got_exit" "0"
check "laws-shape" "$got_out" '{"ok":true,"laws":[{"trait":"Eq","contract":"Eq","realization":null,"law":"refl","params":["x"],"body":"eq(x, x) == 1"}]}'

capture got_stdin got_stdin_exit "$bang" query laws 2>/dev/null < "$tmpdir/laws.bang"
check "laws-stdin-exit" "$got_stdin_exit" "0"
check "laws-stdin-eq-file" "$got_stdin" "$got_out"

got_out="$(printf 'let x = 3 in x' | "$bang" query laws 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-empty-exit" "$got_exit" "0"
check "laws-empty-shape" "$got_out" '{"ok":true,"laws":[]}'

# ══ 5b. `contract` evidence integrity ══

identity_card="$("$bang" query contract "$tmpdir/resource-contract/identity.bang" 2>/dev/null)" && identity_exit=0 || identity_exit=$?
negate_card="$("$bang" query contract "$tmpdir/resource-contract/negate.bang" 2>/dev/null)" && negate_exit=0 || negate_exit=$?
refused_card="$("$bang" query contract scratch/resource-contract/reject-duplicate.bang 2>/dev/null)" && refused_exit=0 || refused_exit=$?
check "contract-identity-exit" "$identity_exit" "0"
check "contract-negate-exit" "$negate_exit" "0"
check "contract-accepted-subject-valid" "$(printf '%s' "$identity_card" | grep -o '"subjectValid":true' || true)" '"subjectValid":true'
check "contract-refused-exit" "$refused_exit" "0"
check "contract-refused-operation-ok" "$(printf '%s' "$refused_card" | grep -o '"ok":true' || true)" '"ok":true'
check "contract-refused-subject-invalid" "$(printf '%s' "$refused_card" | grep -o '"subjectValid":false' || true)" '"subjectValid":false'
check "contract-refused-evidence-invalid" "$(printf '%s' "$refused_card" | grep -o '"typeChecked":false' || true)" '"typeChecked":false'

contract_ids() {
  local field="$1"
  python3 -c 'import json,sys; field=sys.argv[1]; d=json.load(sys.stdin); print(",".join(sorted(x["id"] for x in d[field])))' "$field"
}
identity_contract_ids="$(printf '%s' "$identity_card" | contract_ids contracts)"
negate_contract_ids="$(printf '%s' "$negate_card" | contract_ids contracts)"
identity_realization_ids="$(printf '%s' "$identity_card" | contract_ids realizations)"
negate_realization_ids="$(printf '%s' "$negate_card" | contract_ids realizations)"
identity_law_ids="$(printf '%s' "$identity_card" | contract_ids laws)"
negate_law_ids="$(printf '%s' "$negate_card" | contract_ids laws)"
check "contract-selection-stable-contract-ids" "$negate_contract_ids" "$identity_contract_ids"
check "contract-selection-stable-realization-ids" "$negate_realization_ids" "$identity_realization_ids"
check "contract-selection-stable-law-ids" "$negate_law_ids" "$identity_law_ids"

identity_selected="$(printf '%s' "$identity_card" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(next(x["displayName"] for x in d["realizations"] if x["name"] == x["displayName"]))')"
negate_selected="$(printf '%s' "$negate_card" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(next(x["displayName"] for x in d["realizations"] if x["name"] == x["displayName"]))')"
check "contract-selection-display-remains-local" "$identity_selected:$negate_selected" "Identity:Negate"

# ══ 6. `def` / `refs` (thin filters over dump's "decls"/"refs") ══

got_out="$("$bang" query def double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-exit" "$got_exit" "0"
check "def-shape" "$got_out" '{"ok":true,"symbol":{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}}'

got_out="$("$bang" query def nosuch "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-miss-ok-false" "$got_out" "{\"ok\":false,\"error\":\"no top-level decl named 'nosuch'\"}"
check "def-miss-exit" "$got_exit" "0"

got_out="$("$bang" query refs double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "refs-exit" "$got_exit" "0"
check "refs-shape" "$got_out" '{"ok":true,"refs":[{"name":"quad","kind":"let"}]}'

got_out="$("$bang" query refs main "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "refs-empty-exit" "$got_exit" "0"
check "refs-empty-shape" "$got_out" '{"ok":true,"refs":[]}'

got_out="$("$bang" query def Parse_dropWs examples/json/main.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-multifile-exit" "$got_exit" "0"
check "def-multifile-hit" "$(printf '%s' "$got_out" | grep -o '"ok":true' || true)" '"ok":true'

# ══ 6b. `hover` (#52 slice 5) — decl-granularity position query. 1-INDEXED line/col. ══

# HIT — cursor inside a decl's body resolves to that whole decl, Int-typed (avoids asserting on a
# μ-encoded hole string — issue #100, a KNOWN interaction with user data types, not fixed here).
got_out="$("$bang" query hover "$tmpdir/simple.bang" 2 5 2>/dev/null)" && got_exit=0 || got_exit=$?
check "hover-hit-exit" "$got_exit" "0"
check "hover-hit-shape" "$got_out" '{"ok":true,"decl":{"name":"quad","kind":"let","type":"Thunk Int -> Int","row":"{}","typeError":null,"span":{"line":2,"col":5,"endLine":2,"endCol":9}}}'

# MISS — cursor in whitespace BEFORE any decl's name token (col 1 of line 1 is `let`, before
# `double` at col 9) is an honest {"ok":false,...}, still exit 0 (the tool ran).
got_out="$("$bang" query hover "$tmpdir/simple.bang" 1 1 2>/dev/null)" && got_exit=0 || got_exit=$?
check "hover-miss-exit" "$got_exit" "0"
check "hover-miss-shape" "$got_out" '{"ok":false,"error":"no decl at 1:1"}'

# stdin agrees with file.
capture got_stdin got_stdin_exit "$bang" query hover 2 5 2>/dev/null < "$tmpdir/simple.bang"
capture got_file got_file_exit "$bang" query hover "$tmpdir/simple.bang" 2 5 2>/dev/null
check "hover-stdin-exit" "$got_stdin_exit" "0"
check "hover-file-exit" "$got_file_exit" "0"
check "hover-stdin-eq-file" "$got_stdin" "$got_file"

# MULTI-FILE — a position inside the ENTRY file (main.bang) of a multi-file (import-resolved)
# program resolves through the SAME resolver every other query op uses (loose ok:true match,
# matching def-multifile-hit's own precedent — the exact rendered type is not the point here).
got_out="$("$bang" query hover examples/json/main.bang 29 5 2>/dev/null)" && got_exit=0 || got_exit=$?
check "hover-multifile-exit" "$got_exit" "0"
check "hover-multifile-hit" "$(printf '%s' "$got_out" | grep -o '"name":"boolToBit"' || true)" '"name":"boolToBit"'

# BAD FILE — unreadable path is a TOOL error (exit 2, nothing on stdout), matching every other op.
got_out="$("$bang" query hover /no/such/file.bang 1 1 2>/dev/null)" && got_exit=0 || got_exit=$?
check "hover-bad-file-stdout-empty" "$got_out" ""
check "hover-bad-file-exit" "$got_exit" "2"

# non-numeric line/col is a USAGE error (exit 1, stderr — mirrors `type`'s own missing-arg case).
got_usage_exit=0
"$bang" query hover "$tmpdir/simple.bang" abc 1 >/dev/null 2>&1 || got_usage_exit=$?
check "hover-usage-error-nonnumeric-exit" "$got_usage_exit" "1"

# ══ 7. Exit-code contract: TOOL error (exit 2, unreadable file) ══

got_out="$("$bang" query dump /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-dump-stdout-empty" "$got_out" ""
check "tool-error-dump-exit" "$got_exit" "2"

got_out="$("$bang" query symbols /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-symbols-stdout-empty" "$got_out" ""
check "tool-error-symbols-exit" "$got_exit" "2"

got_out="$("$bang" query def foo /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-def-stdout-empty" "$got_out" ""
check "tool-error-def-exit" "$got_exit" "2"

got_out="$("$bang" query laws /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-laws-stdout-empty" "$got_out" ""
check "tool-error-laws-exit" "$got_exit" "2"

got_usage_exit=0
"$bang" query type "$tmpdir/simple.bang" >/dev/null 2>&1 || got_usage_exit=$?
check "usage-error-type-missing-name-exit" "$got_usage_exit" "1"

# ── jq-parseability: every op's output is valid JSON, not just byte-matching our own expectation.
if command -v jq >/dev/null 2>&1; then
  jq_ok=0
  jq_total=0
  for op_args in "dump $tmpdir/simple.bang" "symbols $tmpdir/simple.bang" "type $tmpdir/simple.bang double" \
                 "effects double $tmpdir/simple.bang" "laws $tmpdir/laws.bang" \
                 "def double $tmpdir/simple.bang" "refs double $tmpdir/simple.bang"; do
    jq_total=$((jq_total + 1))
    if jq_in="$("$bang" query $op_args 2>/dev/null)"; then
      jq_in_exit=0
    else
      jq_in_exit=$?
    fi
    if [ "$jq_in_exit" -eq 0 ] && printf '%s' "$jq_in" | jq -e '.ok == true' >/dev/null 2>&1; then
      jq_ok=$((jq_ok + 1))
    else
      echo "✗ jq-parseable — 'query $op_args' did not parse as expected JSON shape: $jq_in"
    fi
  done
  check "jq-parseable-all-ops" "$jq_ok" "$jq_total"
else
  echo "· jq-parseable — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

echo "──────────────────────────────"
echo "query: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run. BASE is every check that
# always runs (160 — dependency observation, recomputation, reuse, module graph, structural
# invalidation-fanout, resolved-core fingerprint, and resolved-module-interface checks included);
# jq's three guarded blocks
# contribute five `check()` calls in total when jq is present (the composed query checks both
# producers in addition to its output;
# jq IS in the standard `nix develop` shell, so this is the steady-state path); duckdb's guarded
# block contributes two checks when
# duckdb happens to be reachable (NOT in the flake — an ad-hoc `nix shell` reach). The total
# tracks WHICH optional tools actually ran, so a genuinely truncated run is still caught
# regardless of which tools happened to be on PATH (never a silently-widened acceptable range).
want_total=160
if command -v jq >/dev/null 2>&1; then want_total=$((want_total + 5)); fi
if [ "$duckdb_ran" -eq 1 ]; then want_total=$((want_total + 2)); fi
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
