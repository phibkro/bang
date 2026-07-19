#!/usr/bin/env bash
# shellcheck disable=SC2154 # `capture` assigns caller-named output/status variables dynamically.
# tool: role=test couples=Bang/Core/Fingerprint.lean,Bang/Core/SHA256.lean,Bang/Core/CompCodec.lean,Bang/Frontend/Query.lean,Bang/Backend/BodyArtifact.lean,Main.lean,examples/*/main.bang,examples/json/Parse.bang,examples/json/query-dump.bang,examples/json/interface-moved.bang,examples/calc,examples/reactive-spreadsheet/Formulas.bang,examples/reactive-spreadsheet/expected-dependencies.json,examples/reactive-recomputation/Workload.bang,examples/reactive-observation-reuse/CachedWorkload.bang,tools/module-impact.py,tools/interface-diff.py runs-in=verify
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

# Source-occurrence-safe initialization order. Duplicate names must remain distinct by their owning
# module + source declaration index, and dependency initializers must precede the entry sequence.
mkdir -p "$tmpdir/initializer-order"
cat > "$tmpdir/initializer-order/Dep.bang" <<'BANG'
let same = 1
let same = 2
pub let answer = same
BANG
cat > "$tmpdir/initializer-order/main.bang" <<'BANG'
import Dep
let before = 0
let rec identity : Int -> Int = fun x => x
let main = ($identity) (Dep.answer + before)
BANG
for variant in initializer-import-ab initializer-import-ba; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/A.bang" <<'BANG'
let a = 1
BANG
  cat > "$tmpdir/$variant/B.bang" <<'BANG'
let b = 2
BANG
done
cat > "$tmpdir/initializer-import-ab/main.bang" <<'BANG'
import A
import B
let main = 0
BANG
cat > "$tmpdir/initializer-import-ba/main.bang" <<'BANG'
import B
import A
let main = 0
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

# Reachable module-body slices. The first three variants differ only in one lexical value: an
# unreachable sibling must stop contaminating `selected`, while a transitive dependency must move
# it. The interface stays fixed throughout. A separate environment-root fixture pins the implicit
# impl→helper dependency that selected-only closure missed in the pre-scope falsifier.
for variant in body-slice-base body-slice-sibling body-slice-reachable; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
let main = $(Lib.selected)
BANG
done
cat > "$tmpdir/body-slice-base/Lib.bang" <<'BANG'
let base : Int = 40
let helper : Thunk Int = {base + 1}
pub let selected : Thunk Int = helper
let unrelated : Int = 7
BANG
cat > "$tmpdir/body-slice-sibling/Lib.bang" <<'BANG'
let base : Int = 40
let helper : Thunk Int = {base + 1}
pub let selected : Thunk Int = helper
let unrelated : Int = 8
BANG
cat > "$tmpdir/body-slice-reachable/Lib.bang" <<'BANG'
let base : Int = 41
let helper : Thunk Int = {base + 1}
pub let selected : Thunk Int = helper
let unrelated : Int = 7
BANG
cat > "$tmpdir/body-slice-env-root.bang" <<'BANG'
let helper = {fun x => x + 1}
trait Inc { fn inc(x) -> Int }
impl Inc for Int { fn inc(x) = ($helper) x }
pub let selected = {inc(1)}
let unrelated : Int = 7
BANG

# Every public export receives a body row. Only concrete let/letRec declarations are sliced;
# bounded generic functions and non-value kinds state their decided absence explicitly.
cat > "$tmpdir/body-slice-coverage.bang" <<'BANG'
pub data Box = B(Int)
pub trait Marker { fn mark(x) -> Int }
pub fn generic(x) : Int where Marker a = x
pub let rec countdown : Int -> Int = fun n => if n == 0 then 0 else ($countdown) (n - 1)
pub let selected : Int = 41
BANG

# The retained environment carries dense effect labels. Body-slice v2 quotients an unrelated earlier
# effect at the digest boundary while leaving the production runtime allocation untouched.
for variant in body-slice-effect-base body-slice-effect-shifted; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
let main = $(Lib.selected)
BANG
done
cat > "$tmpdir/body-slice-effect-base/Lib.bang" <<'BANG'
effect Target { ping : Int -> Int }
pub let selected = {handle target.ping(1) with Target as target { ping(n) => n }}
BANG
cat > "$tmpdir/body-slice-effect-shifted/Lib.bang" <<'BANG'
effect Earlier { pong : Int -> Int }
effect Target { ping : Int -> Int }
pub let selected = {handle target.ping(1) with Target as target { ping(n) => n }}
BANG

# Rank-only canonicalization would collapse these symmetric single-effect slices: both effects would
# become canonical label 4. Binding the qualified effect-name table must keep them distinct.
for variant in body-slice-effect-alpha body-slice-effect-beta; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
let main = $(Lib.selected)
BANG
done
cat > "$tmpdir/body-slice-effect-alpha/Lib.bang" <<'BANG'
effect Alpha { ping : Int -> Int }
pub let selected = {handle alpha.ping(1) with Alpha as alpha { ping(n) => n }}
BANG
cat > "$tmpdir/body-slice-effect-beta/Lib.bang" <<'BANG'
effect Beta { ping : Int -> Int }
pub let selected = {handle beta.ping(1) with Beta as beta { ping(n) => n }}
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

# A public effect-law body is a contract change, but the checked module interface currently carries
# law names only. Keep a realization present so dump's global law-evidence table moves and the first
# invalidation consumer can refuse a falsely complete dependent-check decision.
for variant in interface-law-base interface-law-changed; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Mid
0
BANG
  cat > "$tmpdir/$variant/Mid.bang" <<'BANG'
import Lib
pub handler Identity implements Lib_Gate { check(n) => n }
BANG
done
cat > "$tmpdir/interface-law-base/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(0) == 0
}
BANG
cat > "$tmpdir/interface-law-changed/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(1) == 1
}
BANG

# Compound attribution falsifier: the same Lib public-law edit co-occurs with an unrelated private
# handler addition for Side.Other. The explained Lib row must not mask Side's new realization row.
for variant in interface-law-compound-base interface-law-compound-changed; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Mid
0
BANG
  cat > "$tmpdir/$variant/Side.bang" <<'BANG'
pub effect Other {
  check : Int -> Int
  law preserves(other): other.check(0) == 0
}
BANG
done
cat > "$tmpdir/interface-law-compound-base/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(0) == 0
}
BANG
cat > "$tmpdir/interface-law-compound-changed/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(1) == 1
}
BANG
cat > "$tmpdir/interface-law-compound-base/Mid.bang" <<'BANG'
import Lib
import Side
pub handler Identity implements Lib_Gate { check(n) => n }
BANG
cat > "$tmpdir/interface-law-compound-changed/Mid.bang" <<'BANG'
import Lib
import Side
pub handler Identity implements Lib_Gate { check(n) => n }
handler OtherIdentity implements Side_Other { check(n) => n }
BANG

# A declared public law belongs to the interface even when no realization exists. This is the
# successor's headline recovery of the instance-only dump blind spot.
for variant in interface-law-no-handler-base interface-law-no-handler-changed; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
0
BANG
done
cat > "$tmpdir/interface-law-no-handler-base/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(0) == 0
}
BANG
cat > "$tmpdir/interface-law-no-handler-changed/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(1) == 1
}
BANG

# Private declarations are not public interface contracts. A private law-body edit must preserve
# the module interface; declaration text is not lowered into the whole-program core either.
for variant in interface-law-private-base interface-law-private-changed; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Lib
0
BANG
done
cat > "$tmpdir/interface-law-private-base/Lib.bang" <<'BANG'
effect Hidden {
  check : Int -> Int
  law preserves(hidden): hidden.check(0) == 0
}
pub let marker : Int = 0
BANG
cat > "$tmpdir/interface-law-private-changed/Lib.bang" <<'BANG'
effect Hidden {
  check : Int -> Int
  law preserves(hidden): hidden.check(1) == 1
}
pub let marker : Int = 0
BANG

# Kill-shot stability fixtures. First, inserting an unrelated earlier effect must not move an
# unchanged law contract. Second, reversing entry import order around a law body that uses selected
# values from two modules must preserve its post-merge qualified text and interface digest.
for variant in interface-law-stable-base interface-law-stable-noise; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/Lib.bang" <<'BANG'
pub effect Gate {
  check : Int -> Int
  law preserves(gate): gate.check(0) == 0
}
BANG
done
cat > "$tmpdir/interface-law-stable-base/main.bang" <<'BANG'
import Lib
0
BANG
cat > "$tmpdir/interface-law-stable-noise/Noise.bang" <<'BANG'
pub effect Noise { ping : Int -> Int }
BANG
cat > "$tmpdir/interface-law-stable-noise/main.bang" <<'BANG'
import Noise
import Lib
0
BANG
for variant in interface-law-order-ab interface-law-order-ba; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/HelperA.bang" <<'BANG'
pub let zero : Int = 0
BANG
  cat > "$tmpdir/$variant/HelperB.bang" <<'BANG'
pub let one : Int = 1
BANG
  cat > "$tmpdir/$variant/Lib.bang" <<'BANG'
use HelperA (zero)
use HelperB (one)
pub effect Gate {
  check : Int -> Int
  law preserves(gate): let ignored = one in gate.check(zero) == zero
}
BANG
done
cat > "$tmpdir/interface-law-order-ab/main.bang" <<'BANG'
import HelperA
import HelperB
import Lib
0
BANG
cat > "$tmpdir/interface-law-order-ba/main.bang" <<'BANG'
import HelperB
import HelperA
import Lib
0
BANG

# The positive consumer journey uses a real three-deep graph: entry -> Mid -> Lib. Mid imports Lib
# without depending on its concrete export shape, isolating graph fanout from type-check failure when
# Lib's public signature moves.
for variant in interface-diff-base interface-diff-body interface-diff-signature; do
  mkdir -p "$tmpdir/$variant"
  cat > "$tmpdir/$variant/main.bang" <<'BANG'
import Mid
0
BANG
  cat > "$tmpdir/$variant/Mid.bang" <<'BANG'
import Lib
pub let relay : Int = 0
BANG
done
cat > "$tmpdir/interface-diff-base/Lib.bang" <<'BANG'
pub let answer : Int = 41
BANG
cat > "$tmpdir/interface-diff-body/Lib.bang" <<'BANG'
pub let answer : Int = 42
BANG
cat > "$tmpdir/interface-diff-signature/Lib.bang" <<'BANG'
pub let answer : Int * Int = (41, 0)
BANG
mkdir -p "$tmpdir/interface-diff-added"
cp "$tmpdir/interface-diff-base/Lib.bang" "$tmpdir/interface-diff-added/Lib.bang"
cp "$tmpdir/interface-diff-base/Mid.bang" "$tmpdir/interface-diff-added/Mid.bang"
cat > "$tmpdir/interface-diff-added/Side.bang" <<'BANG'
pub let marker : Int = 1
BANG
cat > "$tmpdir/interface-diff-added/main.bang" <<'BANG'
import Mid
import Side
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
check "dump-shape" "$got_out" '{"ok":true,"schemaVersion":1,"bangVersion":"0.1.1","coreFingerprint":{"scope":"resolved-program","algorithm":"bang-comp-struct-v2-uint64","digest":"4b971e1cbcf3c5ff","cacheKeySafe":false},"moduleInterfaces":[{"module":"@entry","scope":"resolved-program-module-interface","algorithm":"bang-module-interface-json-v2-uint64","digest":"46434a463a92408a","cacheKeySafe":false,"separateCompilationReady":false,"exports":[]}],"moduleBodies":[{"module":"@entry","scope":"resolved-program-module-body-slice","algorithm":"bang-module-body-slice-comp-v2-uint64","cacheKeySafe":false,"linkReady":false,"exports":[]}],"modules":[{"name":"@entry","origin":"entry"}],"moduleDeps":[],"moduleInitialization":{"scope":"resolver-source-initializer-order","order":"dependency-first-source-order","sourceOccurrencesComplete":true,"elaborationProvenance":false,"perBindingEffects":false,"linkReady":false},"moduleInitializers":[{"id":"@entry::decl:0","module":"@entry","sourceIndex":0,"order":0,"name":"double","kind":"letRec","mode":"recursive-knot"},{"id":"@entry::decl:1","module":"@entry","sourceIndex":1,"order":1,"name":"quad","kind":"let","mode":"strict-rhs"},{"id":"@entry::decl:2","module":"@entry","sourceIndex":2,"order":2,"name":"main","kind":"let","mode":"strict-rhs"}],"decls":[{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"quad","kind":"let","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"main","kind":"let","type":"Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}],"refs":[{"from":"quad","to":"double"},{"from":"main","to":"quad"}],"laws":[],"imports":[],"uses":[]}'

# A named file has an entry role and therefore selects computed `main`; stdin remains a library
# context. Structural declaration facts survive there, but no whole-program identity may pretend
# the unselected computed declaration was a valid library initializer.
capture got_stdin got_stdin_exit "$bang" query dump 2>/dev/null < "$tmpdir/simple.bang"
check "dump-stdin-exit" "$got_stdin_exit" "0"
capture dump_role_view dump_role_view_exit python3 -c 'import json,sys; ds=[json.loads(line) for line in sys.stdin if line.strip()]; print("{}|{}".format("present" if ds[0]["coreFingerprint"] else "null", "present" if ds[1]["coreFingerprint"] else "null"))' 2>/dev/null <<< "$got_out
$got_stdin"
check "dump-file-entry-vs-stdin-library-role" "$dump_role_view" "present|null"

# The initializer contract reads unmerged resolver sources, not flattened binder names. Two source
# declarations named `same` therefore retain different occurrence addresses, dependency rows precede
# entry rows, and recursive-knot construction is distinguished from strict RHS execution.
capture initializer_dump initializer_dump_exit "$bang" query dump "$tmpdir/initializer-order/main.bang" 2>/dev/null
check "module-initializers-exit" "$initializer_dump_exit" "0"
capture initializer_meta initializer_meta_exit python3 -c '
import json,sys
m=json.load(sys.stdin)["moduleInitialization"]
print("|".join([m["scope"],m["order"],str(m["sourceOccurrencesComplete"]),str(m["elaborationProvenance"]),str(m["perBindingEffects"]),str(m["linkReady"])]))
' 2>/dev/null <<< "$initializer_dump"
check "module-initializers-metadata-extractor-exit" "$initializer_meta_exit" "0"
check "module-initializers-honesty-metadata" "$initializer_meta" "resolver-source-initializer-order|dependency-first-source-order|True|False|False|False"
capture initializer_rows initializer_rows_exit python3 -c '
import json,sys
rows=json.load(sys.stdin)["moduleInitializers"]
print("|".join("{}:{}:{}:{}:{}:{}".format(r["id"],r["module"],r["sourceIndex"],r["order"],r["name"],r["mode"]) for r in rows))
' 2>/dev/null <<< "$initializer_dump"
check "module-initializers-extractor-exit" "$initializer_rows_exit" "0"
check "module-initializers-duplicate-safe-order" "$initializer_rows" "Dep::decl:0:Dep:0:0:same:strict-rhs|Dep::decl:1:Dep:1:1:same:strict-rhs|Dep::decl:2:Dep:2:2:answer:strict-rhs|@entry::decl:0:@entry:0:3:before:strict-rhs|@entry::decl:1:@entry:1:4:identity:recursive-knot|@entry::decl:2:@entry:2:5:main:strict-rhs"

# Independent imports are not commuted by today's semantics: their source initializer blocks follow
# resolver traversal order. The fact must expose that observable choice instead of sorting it away.
capture initializer_ab_dump initializer_ab_exit "$bang" query dump "$tmpdir/initializer-import-ab/main.bang" 2>/dev/null
capture initializer_ba_dump initializer_ba_exit "$bang" query dump "$tmpdir/initializer-import-ba/main.bang" 2>/dev/null
check "module-initializers-import-ab-exit" "$initializer_ab_exit" "0"
check "module-initializers-import-ba-exit" "$initializer_ba_exit" "0"
capture initializer_import_order initializer_import_order_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
print("|".join(",".join(r["module"] for r in d["moduleInitializers"]) for d in ds))
' 2>/dev/null <<< "$initializer_ab_dump
$initializer_ba_dump"
check "module-initializers-import-order-observable" "$initializer_import_order" "A,B,@entry|B,A,@entry"

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
capture body_invalid_value body_invalid_value_exit python3 -c 'import json,sys; print("null" if json.load(sys.stdin)["moduleBodies"] is None else "present")' 2>/dev/null <<< "$fp_invalid_dump"
check "module-body-invalid-extractor-exit" "$body_invalid_value_exit" "0"
check "module-body-invalid-null" "$body_invalid_value" "null"

# The body-side firewall. Whole-program core still moves on an unreachable sibling edit, but the
# concrete selected export's reachable slice stays stable; changing a transitive helper moves it.
# The environment-root fixture must produce a digest (not null): its impl body is the only syntactic
# owner of `helper`, the exact hidden dependency that refuted selected-only roots.
capture body_base_dump body_base_exit "$bang" query dump "$tmpdir/body-slice-base/main.bang" 2>/dev/null
capture body_sibling_dump body_sibling_exit "$bang" query dump "$tmpdir/body-slice-sibling/main.bang" 2>/dev/null
capture body_reachable_dump body_reachable_exit "$bang" query dump "$tmpdir/body-slice-reachable/main.bang" 2>/dev/null
capture body_env_dump body_env_exit "$bang" query dump "$tmpdir/body-slice-env-root.bang" 2>/dev/null
check "module-body-base-exit" "$body_base_exit" "0"
check "module-body-sibling-exit" "$body_sibling_exit" "0"
check "module-body-reachable-exit" "$body_reachable_exit" "0"
check "module-body-environment-root-exit" "$body_env_exit" "0"
capture body_rows body_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
def module(d,table,name): return next(x for x in d[table] if x["module"]==name)
bodies=[module(d,"moduleBodies","Lib") for d in ds[:3]]+[module(ds[3],"moduleBodies","@entry")]
selected=[next(x for x in b["exports"] if x["name"]=="selected") for b in bodies]
interfaces=[module(d,"moduleInterfaces","Lib") for d in ds[:3]]
print("|".join([
  bodies[0]["scope"],bodies[0]["algorithm"],str(bodies[0]["cacheKeySafe"]).lower(),
  str(bodies[0]["linkReady"]).lower(),str(len(selected[0]["digest"])),selected[0]["status"],
  str(ds[0]["coreFingerprint"]["digest"]!=ds[1]["coreFingerprint"]["digest"]),
  str(selected[0]["digest"]==selected[1]["digest"]),
  str(selected[0]["digest"]!=selected[2]["digest"]),
  str(interfaces[0]["digest"]==interfaces[1]["digest"]==interfaces[2]["digest"]),
  str(selected[3]["status"]=="sliced" and len(selected[3]["digest"])==16),
  str(selected[0]["effectRelocations"]==[]),
  str([[x["module"] for x in d["moduleBodies"]] for d in ds]
      == [[x["module"] for x in d["moduleInterfaces"]] for d in ds])]))
' 2>/dev/null <<< "$body_base_dump
$body_sibling_dump
$body_reachable_dump
$body_env_dump"
check "module-body-extractor-exit" "$body_rows_exit" "0"
check "module-body-reachability-boundary" "$body_rows" "resolved-program-module-body-slice|bang-module-body-slice-comp-v2-uint64|false|false|16|sliced|True|True|True|True|True|True|True"

# Coverage is explicit, never inferred from omitted rows. Generic templates have no concrete
# instantiation at this seam; structural kinds have no value body; concrete let/letRec rows do.
capture body_coverage_dump body_coverage_exit "$bang" query dump "$tmpdir/body-slice-coverage.bang" 2>/dev/null
check "module-body-coverage-exit" "$body_coverage_exit" "0"
capture body_coverage_rows body_coverage_rows_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
lib=next(x for x in d["moduleBodies"] if x["module"]=="@entry")
print("|".join("{}:{}:{}:{}:{}".format(x["name"],x["kind"],x["status"],
  str(x["digest"] is not None).lower(),str(x["effectRelocations"] is not None).lower())
  for x in lib["exports"]))
' 2>/dev/null <<< "$body_coverage_dump"
check "module-body-coverage-extractor-exit" "$body_coverage_rows_exit" "0"
check "module-body-explicit-export-coverage" "$body_coverage_rows" "Box:data:no-body-kind:false:false|Marker:trait:no-body-kind:false:false|generic:fn:unsupported-generic-fn:false:false|countdown:letRec:sliced:true:true|selected:let:sliced:true:true"

# Digest-side quotient: an unrelated earlier effect preserves both the checked interface and the
# environment-relative body observation. The same semantic/canonical row remains stable while its
# runtime label shifts with the whole-program allocation; this is the relocation residual.
capture body_effect_base_dump body_effect_base_exit "$bang" query dump "$tmpdir/body-slice-effect-base/main.bang" 2>/dev/null
capture body_effect_shifted_dump body_effect_shifted_exit "$bang" query dump "$tmpdir/body-slice-effect-shifted/main.bang" 2>/dev/null
check "module-body-effect-base-exit" "$body_effect_base_exit" "0"
check "module-body-effect-shifted-exit" "$body_effect_shifted_exit" "0"
capture body_effect_rows body_effect_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
def module(d,table): return next(x for x in d[table] if x["module"]=="Lib")
interfaces=[module(d,"moduleInterfaces") for d in ds]
bodies=[module(d,"moduleBodies")["exports"][0] for d in ds]
relocs=[b["effectRelocations"] for b in bodies]
print("|".join([str(interfaces[0]["digest"]==interfaces[1]["digest"]),
  str(bodies[0]["digest"]==bodies[1]["digest"]),bodies[0]["status"],bodies[1]["status"],
  str(relocs[0][0]["name"]==relocs[1][0]["name"]=="Lib_Target"),
  str(relocs[0][0]["canonicalLabel"]==relocs[1][0]["canonicalLabel"]==4),
  "{}>{}".format(relocs[0][0]["runtimeLabel"],relocs[1][0]["runtimeLabel"])]))
' 2>/dev/null <<< "$body_effect_base_dump
$body_effect_shifted_dump"
check "module-body-effect-extractor-exit" "$body_effect_rows_exit" "0"
check "module-body-quotients-unrelated-effect" "$body_effect_rows" "True|True|sliced|sliced|True|True|4>5"

# Canonical code is point-queried by the stable export ID, never duplicated into the complete dump.
# The unrelated earlier effect must preserve artifact bytes while only the contextual relocation moves.
capture body_artifact_base body_artifact_base_exit "$bang" query body-artifact Lib::selected \
  "$tmpdir/body-slice-effect-base/main.bang" 2>/dev/null
capture body_artifact_shifted body_artifact_shifted_exit "$bang" query body-artifact Lib::selected \
  "$tmpdir/body-slice-effect-shifted/main.bang" 2>/dev/null
check "module-body-artifact-base-exit" "$body_artifact_base_exit" "0"
check "module-body-artifact-shifted-exit" "$body_artifact_shifted_exit" "0"
capture body_artifact_rows body_artifact_rows_exit python3 -c '
import hashlib,json,re,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
rows=[d["bodyArtifact"] for d in ds]
def expected_address(row):
  artifact=json.dumps(row["artifact"],ensure_ascii=False,separators=(",",":"))
  stable=[[x["name"],x["canonicalLabel"]] for x in row["effectRelocations"]]
  preimage=json.dumps([row["addressAlgorithm"],artifact,stable],ensure_ascii=False,separators=(",",":"))
  return hashlib.sha256(preimage.encode()).hexdigest()
print("|".join([str(all(d["ok"] for d in ds)),rows[0]["id"],rows[0]["format"],
  str(rows[0]["digest"]==rows[1]["digest"]),str(rows[0]["artifact"]==rows[1]["artifact"]),
  str(rows[0]["artifact"][0]==rows[0]["format"]),
  str(rows[0]["producerChecked"] and rows[0]["structurallyRoundTripped"]),
  rows[0]["addressAlgorithm"],
  str(all(r["integrityVerified"] and re.fullmatch(r"[0-9a-f]{64}",r["address"]) and
              r["address"]==expected_address(r) for r in rows)),
  str(rows[0]["address"]==rows[1]["address"]),
  str(not rows[0]["cacheKeySafe"] and not rows[0]["independentlyTypeValidated"] and not rows[0]["linkReady"]),
  "{}>{}".format(rows[0]["effectRelocations"][0]["runtimeLabel"],
                  rows[1]["effectRelocations"][0]["runtimeLabel"])]))
' 2>/dev/null <<< "$body_artifact_base
$body_artifact_shifted"
check "module-body-artifact-extractor-exit" "$body_artifact_rows_exit" "0"
check "module-body-artifact-roundtrip-boundary" "$body_artifact_rows" \
  "True|Lib::selected|bang-core-comp-json-v1|True|True|True|True|sha256-bang-module-body-artifact-v1|True|True|True|4>5"

capture body_artifact_absent_dump body_artifact_absent_dump_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
row=next(x for x in next(m for m in d["moduleBodies"] if m["module"]=="Lib")["exports"] if x["id"]=="Lib::selected")
print(str("artifact" not in row))
' 2>/dev/null <<< "$body_effect_base_dump"
check "module-body-artifact-absent-dump-extractor-exit" "$body_artifact_absent_dump_exit" "0"
check "module-body-artifact-is-on-demand" "$body_artifact_absent_dump" "True"

capture body_artifact_unsupported body_artifact_unsupported_exit "$bang" query body-artifact \
  @entry::generic "$tmpdir/body-slice-coverage.bang" 2>/dev/null
check "module-body-artifact-unsupported-exit" "$body_artifact_unsupported_exit" "0"
capture body_artifact_unsupported_ok body_artifact_unsupported_ok_exit python3 -c '
import json,sys
d=json.load(sys.stdin); print(str(not d["ok"] and "unsupported generic fn" in d["error"]))
' 2>/dev/null <<< "$body_artifact_unsupported"
check "module-body-artifact-unsupported-extractor-exit" "$body_artifact_unsupported_ok_exit" "0"
check "module-body-artifact-unsupported-fails-loud" "$body_artifact_unsupported_ok" "True"

# Semantic discrimination: equal shapes using differently named effects must not collapse merely
# because each used-name set receives the same singleton canonical rank.
capture body_effect_alpha_dump body_effect_alpha_exit "$bang" query dump "$tmpdir/body-slice-effect-alpha/main.bang" 2>/dev/null
capture body_effect_beta_dump body_effect_beta_exit "$bang" query dump "$tmpdir/body-slice-effect-beta/main.bang" 2>/dev/null
check "module-body-effect-alpha-exit" "$body_effect_alpha_exit" "0"
check "module-body-effect-beta-exit" "$body_effect_beta_exit" "0"
capture body_effect_identity_rows body_effect_identity_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
def body(d): return next(x for x in d["moduleBodies"] if x["module"]=="Lib")["exports"][0]
rows=[body(d) for d in ds]
relocs=[x["effectRelocations"] for x in rows]
print("|".join([str(rows[0]["digest"]!=rows[1]["digest"]),rows[0]["status"],rows[1]["status"],
  relocs[0][0]["name"],relocs[1][0]["name"],
  str(relocs[0][0]["canonicalLabel"]==relocs[1][0]["canonicalLabel"]==4)]))
' 2>/dev/null <<< "$body_effect_alpha_dump
$body_effect_beta_dump"
check "module-body-effect-identity-extractor-exit" "$body_effect_identity_rows_exit" "0"
check "module-body-binds-effect-identity" "$body_effect_identity_rows" "True|sliced|sliced|Lib_Alpha|Lib_Beta|True"

# The address binds semantic relocation identity even where canonical artifact bytes coincide.
capture body_artifact_alpha body_artifact_alpha_exit "$bang" query body-artifact Lib::selected \
  "$tmpdir/body-slice-effect-alpha/main.bang" 2>/dev/null
capture body_artifact_beta body_artifact_beta_exit "$bang" query body-artifact Lib::selected \
  "$tmpdir/body-slice-effect-beta/main.bang" 2>/dev/null
check "module-body-artifact-alpha-exit" "$body_artifact_alpha_exit" "0"
check "module-body-artifact-beta-exit" "$body_artifact_beta_exit" "0"
capture body_artifact_identity_rows body_artifact_identity_rows_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
rows=[d["bodyArtifact"] for d in ds]
print("|".join([str(rows[0]["artifact"]==rows[1]["artifact"]),
  str(rows[0]["address"]!=rows[1]["address"]),
  rows[0]["effectRelocations"][0]["name"],rows[1]["effectRelocations"][0]["name"]]))
' 2>/dev/null <<< "$body_artifact_alpha
$body_artifact_beta"
check "module-body-artifact-identity-extractor-exit" "$body_artifact_identity_rows_exit" "0"
check "module-body-artifact-address-binds-effect-identity" "$body_artifact_identity_rows" \
  "True|True|Lib_Alpha|Lib_Beta"

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
  str(export==[{"id":"Lib::answer","name":"answer","kind":"let","type":"Int","row":"{}","typeError":None,"shape":None,"laws":[]}]),
  str(libs[0]["digest"]==libs[1]["digest"]==libs[2]["digest"]),
  str(libs[0]["digest"]!=libs[3]["digest"]),
  str(cores[0]!=cores[1] and cores[0]!=cores[2] and cores[0]!=cores[3])]))
' 2>/dev/null <<< "$iface_base_dump
$iface_public_dump
$iface_private_dump
$iface_signature_dump"
check "module-interface-extractor-exit" "$iface_rows_exit" "0"
check "module-interface-boundary-discrimination" "$iface_rows" "resolved-program-module-interface|bang-module-interface-json-v2-uint64|false|false|16|True|True|True|True"

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

# First consumer of the interface facts: compare complete export records, then join moved modules to
# the already-validated reverse dependency closure. This is a measurement view only—no compiler work
# is skipped and no artifact reuse is authorized.
capture iface_diff_base_dump iface_diff_base_exit "$bang" query dump "$tmpdir/interface-diff-base/main.bang" 2>/dev/null
capture iface_diff_body_dump iface_diff_body_exit "$bang" query dump "$tmpdir/interface-diff-body/main.bang" 2>/dev/null
capture iface_diff_signature_dump iface_diff_signature_exit "$bang" query dump "$tmpdir/interface-diff-signature/main.bang" 2>/dev/null
check "interface-diff-base-dump-exit" "$iface_diff_base_exit" "0"
check "interface-diff-body-dump-exit" "$iface_diff_body_exit" "0"
check "interface-diff-signature-dump-exit" "$iface_diff_signature_exit" "0"
printf '%s' "$iface_diff_base_dump" > "$tmpdir/interface-base.json"
printf '%s' "$iface_diff_body_dump" > "$tmpdir/interface-public-body.json"
printf '%s' "$iface_diff_signature_dump" > "$tmpdir/interface-signature.json"
capture iface_body_diff iface_body_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-base.json" "$tmpdir/interface-public-body.json" 2>/dev/null
check "interface-diff-body-exit" "$iface_body_diff_exit" "0"
capture iface_body_view iface_body_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print(json.dumps({"schema":d["schemaVersion"],"basis":d["comparisonBasis"],"status":d["decision"]["status"],"moved":d["interfaceInvalidation"]["moved"],"candidates":d["interfaceInvalidation"]["recheckCandidates"],"skipped":d["decision"]["actualChecksSkipped"],"authorized":d["decision"]["artifactReuseAuthorized"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_body_diff"
check "interface-diff-body-extractor-exit" "$iface_body_view_exit" "0"
check "interface-diff-body-preserved" "$iface_body_view" '{"schema":2,"basis":"complete-module-interface-exports-including-declared-laws+validated-module-topology","status":"measured","moved":[],"candidates":[],"skipped":false,"authorized":false}'

capture iface_signature_diff iface_signature_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-base.json" "$tmpdir/interface-signature.json" 2>/dev/null
check "interface-diff-signature-exit" "$iface_signature_diff_exit" "0"
capture iface_signature_view iface_signature_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print(json.dumps({"moved":d["interfaceInvalidation"]["moved"],"candidates":d["interfaceInvalidation"]["recheckCandidates"],"modules":d["modules"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_signature_diff"
check "interface-diff-signature-extractor-exit" "$iface_signature_view_exit" "0"
check "interface-diff-signature-fanout" "$iface_signature_view" '{"moved":["Lib"],"candidates":["@entry","Lib","Mid"],"modules":[{"module":"@entry","interface":"preserved","recheckCandidate":true,"invalidatedBy":["Lib"]},{"module":"Lib","interface":"moved","recheckCandidate":true,"invalidatedBy":["Lib"]},{"module":"Mid","interface":"preserved","recheckCandidate":true,"invalidatedBy":["Lib"]}]}'

# First BANG-written fact consumer: read the same two dumps through Console, parse them with the
# example JSON library, and render interface movement. The canonical Python consumer remains the
# oracle; this is a dogfood witness, not a replacement or an authorization to skip/reuse artifacts.
capture iface_signature_lines iface_signature_lines_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print("\n".join("{} {}".format(row["interface"],row["module"]) for row in d["modules"]))
' 2>/dev/null <<< "$iface_signature_diff"
check "bang-interface-consumer-oracle-exit" "$iface_signature_lines_exit" "0"
capture bang_iface_signature bang_iface_signature_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "$3" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump" "$iface_diff_signature_dump"
check "bang-interface-consumer-exit" "$bang_iface_signature_exit" "0"
check "bang-interface-consumer-matches-oracle" "$bang_iface_signature" "$iface_signature_lines"
capture bang_iface_malformed bang_iface_malformed_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "{" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump"
check "bang-interface-consumer-malformed-exit" "$bang_iface_malformed_exit" "0"
check "bang-interface-consumer-malformed-refusal" "$bang_iface_malformed" "invalid dump"
capture bang_iface_wrong_shape bang_iface_wrong_shape_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "{\"ok\":true}" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump"
check "bang-interface-consumer-wrong-shape-exit" "$bang_iface_wrong_shape_exit" "0"
check "bang-interface-consumer-wrong-shape-refusal" "$bang_iface_wrong_shape" "invalid dump"
capture bang_iface_bad_row_dump bang_iface_bad_row_dump_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
d["moduleInterfaces"][0].pop("digest")
print(json.dumps(d,separators=(",",":")))
' 2>/dev/null <<< "$iface_diff_base_dump"
check "bang-interface-consumer-bad-row-fixture-exit" "$bang_iface_bad_row_dump_exit" "0"
capture bang_iface_bad_row bang_iface_bad_row_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "$3" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump" "$bang_iface_bad_row_dump"
check "bang-interface-consumer-bad-row-exit" "$bang_iface_bad_row_exit" "0"
check "bang-interface-consumer-bad-row-refusal" "$bang_iface_bad_row" "invalid dump"
capture bang_iface_duplicate_dump bang_iface_duplicate_dump_exit python3 -c '
import json,copy,sys
d=json.load(sys.stdin)
d["moduleInterfaces"].append(copy.deepcopy(d["moduleInterfaces"][0]))
print(json.dumps(d,separators=(",",":")))
' 2>/dev/null <<< "$iface_diff_base_dump"
check "bang-interface-consumer-duplicate-fixture-exit" "$bang_iface_duplicate_dump_exit" "0"
capture bang_iface_duplicate bang_iface_duplicate_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "$3" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump" "$bang_iface_duplicate_dump"
check "bang-interface-consumer-duplicate-exit" "$bang_iface_duplicate_exit" "0"
check "bang-interface-consumer-duplicate-refusal" "$bang_iface_duplicate" "invalid dump"

# Topology validation is deliberately outside this digest-level witness, but a current dump always
# contains at least @entry. Refuse empty interface sets and a missing second line rather than emitting
# an ambiguous non-status value.
capture bang_iface_empty_dump bang_iface_empty_dump_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
d["moduleInterfaces"]=[]
print(json.dumps(d,separators=(",",":")))
' 2>/dev/null <<< "$iface_diff_base_dump"
check "bang-interface-consumer-empty-fixture-exit" "$bang_iface_empty_dump_exit" "0"
capture bang_iface_empty bang_iface_empty_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "$2" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$bang_iface_empty_dump"
check "bang-interface-consumer-empty-exit" "$bang_iface_empty_exit" "0"
check "bang-interface-consumer-empty-refusal" "$bang_iface_empty" "invalid dump"
capture bang_iface_eof bang_iface_eof_exit bash -o pipefail -c \
  'printf "%s\n" "$2" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump"
check "bang-interface-consumer-eof-exit" "$bang_iface_eof_exit" "0"
check "bang-interface-consumer-eof-refusal" "$bang_iface_eof" "invalid dump"

# Added/removed modules and dependency-edge movement are ordinary diff inputs, not a reason to make
# the consumer unusable. Added Side invalidates itself and @entry; removing it leaves only the
# surviving @entry as a recheck candidate.
capture iface_diff_added_dump iface_diff_added_exit "$bang" query dump "$tmpdir/interface-diff-added/main.bang" 2>/dev/null
check "interface-diff-added-dump-exit" "$iface_diff_added_exit" "0"
printf '%s' "$iface_diff_added_dump" > "$tmpdir/interface-added.json"
capture iface_added_diff iface_added_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-base.json" "$tmpdir/interface-added.json" 2>/dev/null
check "interface-diff-added-exit" "$iface_added_diff_exit" "0"
capture iface_added_view iface_added_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)["interfaceInvalidation"]
print(json.dumps({"added":d["added"],"removed":d["removed"],"topology":d["topologyChanged"],"candidates":d["recheckCandidates"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_added_diff"
check "interface-diff-added-extractor-exit" "$iface_added_view_exit" "0"
check "interface-diff-added-fanout" "$iface_added_view" '{"added":["Side"],"removed":[],"topology":["@entry"],"candidates":["@entry","Side"]}'
capture iface_removed_diff iface_removed_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-added.json" "$tmpdir/interface-base.json" 2>/dev/null
check "interface-diff-removed-exit" "$iface_removed_diff_exit" "0"
capture iface_removed_view iface_removed_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)["interfaceInvalidation"]
print(json.dumps({"added":d["added"],"removed":d["removed"],"topology":d["topologyChanged"],"candidates":d["recheckCandidates"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_removed_diff"
check "interface-diff-removed-extractor-exit" "$iface_removed_view_exit" "0"
check "interface-diff-removed-fanout" "$iface_removed_view" '{"added":[],"removed":["Side"],"topology":["@entry"],"candidates":["@entry"]}'

# Added/removed rows ride the same differential oracle, keeping the BANG witness honest across the
# topology cases the canonical consumer already supports.
capture iface_added_lines iface_added_lines_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print("\n".join("{} {}".format(row["interface"],row["module"]) for row in d["modules"]))
' 2>/dev/null <<< "$iface_added_diff"
check "bang-interface-consumer-added-oracle-exit" "$iface_added_lines_exit" "0"
capture bang_iface_added bang_iface_added_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "$3" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_base_dump" "$iface_diff_added_dump"
check "bang-interface-consumer-added-exit" "$bang_iface_added_exit" "0"
check "bang-interface-consumer-added-matches-oracle" "$bang_iface_added" "$iface_added_lines"
capture iface_removed_lines iface_removed_lines_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print("\n".join("{} {}".format(row["interface"],row["module"]) for row in d["modules"]))
' 2>/dev/null <<< "$iface_removed_diff"
check "bang-interface-consumer-removed-oracle-exit" "$iface_removed_lines_exit" "0"
capture bang_iface_removed bang_iface_removed_exit bash -o pipefail -c \
  'printf "%s\n%s\n" "$2" "$3" | "$1" run --env=real --allow=Console examples/json/interface-moved.bang' \
  _ "$bang" "$iface_diff_added_dump" "$iface_diff_base_dump"
check "bang-interface-consumer-removed-exit" "$bang_iface_removed_exit" "0"
check "bang-interface-consumer-removed-matches-oracle" "$bang_iface_removed" "$iface_removed_lines"

# The previous tracer's strongest adverse case now becomes the positive owner-attribution journey:
# the public law body moves Lib's declared-law export fact, ordinary interface fanout reaches Mid and
# @entry, and the global realization-law movement is explained rather than guessed.
capture iface_law_base_dump iface_law_base_exit "$bang" query dump "$tmpdir/interface-law-base/main.bang" 2>/dev/null
capture iface_law_changed_dump iface_law_changed_exit "$bang" query dump "$tmpdir/interface-law-changed/main.bang" 2>/dev/null
check "interface-diff-law-base-dump-exit" "$iface_law_base_exit" "0"
check "interface-diff-law-changed-dump-exit" "$iface_law_changed_exit" "0"
capture iface_law_premise iface_law_premise_exit python3 -c '
import json,sys
a,b=[json.loads(line) for line in sys.stdin if line.strip()]
lib=lambda d: next(x for x in d["moduleInterfaces"] if x["module"]=="Lib")
laws=lambda d: lib(d)["exports"][0]["laws"]
print("|".join([str(lib(a)["digest"]!=lib(b)["digest"]),str(laws(a)!=laws(b)),laws(a)[0]["body"],str(a["laws"]!=b["laws"])]))
' 2>/dev/null <<< "$iface_law_base_dump
$iface_law_changed_dump"
check "interface-diff-law-premise-extractor-exit" "$iface_law_premise_exit" "0"
check "interface-diff-law-owner-contract-moves" "$iface_law_premise" "True|True|gate.check(0) == 0|True"
printf '%s' "$iface_law_base_dump" > "$tmpdir/interface-law-base.json"
printf '%s' "$iface_law_changed_dump" > "$tmpdir/interface-law-changed.json"
capture iface_law_diff iface_law_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-law-base.json" "$tmpdir/interface-law-changed.json" 2>/dev/null
check "interface-diff-law-attributed-exit" "$iface_law_diff_exit" "0"
capture iface_law_view iface_law_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print(json.dumps({"moved":d["interfaceInvalidation"]["moved"],"contracts":d["publicLawContractsMoved"],"candidates":d["interfaceInvalidation"]["recheckCandidates"],"lawsMoved":d["lawFactsMoved"],"status":d["decision"]["status"],"skipped":d["decision"]["actualChecksSkipped"],"gap":d["gap"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_law_diff"
check "interface-diff-law-extractor-exit" "$iface_law_view_exit" "0"
check "interface-diff-law-owner-fanout" "$iface_law_view" '{"moved":["Lib"],"contracts":["Lib"],"candidates":["@entry","Lib","Mid"],"lawsMoved":true,"status":"measured","skipped":false,"gap":null}'

# Per-row attribution must be monotone under compound edits: Lib's explained public-law movement
# cannot mask Side.Other's unrelated new private-handler realization row.
capture iface_law_compound_base_dump iface_law_compound_base_exit "$bang" query dump "$tmpdir/interface-law-compound-base/main.bang" 2>/dev/null
capture iface_law_compound_changed_dump iface_law_compound_changed_exit "$bang" query dump "$tmpdir/interface-law-compound-changed/main.bang" 2>/dev/null
check "interface-law-compound-base-exit" "$iface_law_compound_base_exit" "0"
check "interface-law-compound-changed-exit" "$iface_law_compound_changed_exit" "0"
printf '%s' "$iface_law_compound_base_dump" > "$tmpdir/interface-law-compound-base.json"
printf '%s' "$iface_law_compound_changed_dump" > "$tmpdir/interface-law-compound-changed.json"
capture iface_law_compound_diff iface_law_compound_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-law-compound-base.json" "$tmpdir/interface-law-compound-changed.json" 2>/dev/null
check "interface-law-compound-diff-exit" "$iface_law_compound_diff_exit" "2"
capture iface_law_compound_view iface_law_compound_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print(json.dumps({"moved":d["interfaceInvalidation"]["moved"],"contracts":d["publicLawContractsMoved"],"unexplained":d["unexplainedLawContractIds"],"status":d["decision"]["status"],"gap":d["gap"]["code"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_law_compound_diff"
check "interface-law-compound-view-exit" "$iface_law_compound_view_exit" "0"
check "interface-law-compound-unmasked" "$iface_law_compound_view" '{"moved":["Lib"],"contracts":["Lib"],"unexplained":["Side_Other"],"status":"indeterminate","gap":"unexplained-realization-law-movement"}'

# A public law with no handler has no row in the realization-instance table. The declaration fact
# must still move the owner and fan out; this flips the previously invisible case green.
capture iface_law_no_handler_base_dump iface_law_no_handler_base_exit "$bang" query dump "$tmpdir/interface-law-no-handler-base/main.bang" 2>/dev/null
capture iface_law_no_handler_changed_dump iface_law_no_handler_changed_exit "$bang" query dump "$tmpdir/interface-law-no-handler-changed/main.bang" 2>/dev/null
check "interface-law-no-handler-base-exit" "$iface_law_no_handler_base_exit" "0"
check "interface-law-no-handler-changed-exit" "$iface_law_no_handler_changed_exit" "0"
capture iface_law_no_handler_premise iface_law_no_handler_premise_exit python3 -c '
import json,sys
a,b=[json.loads(line) for line in sys.stdin if line.strip()]
lib=lambda d: next(x for x in d["moduleInterfaces"] if x["module"]=="Lib")
print("|".join([str(a["laws"]==b["laws"]==[]),str(lib(a)["digest"]!=lib(b)["digest"]),str(lib(a)["exports"][0]["laws"]!=lib(b)["exports"][0]["laws"])]))
' 2>/dev/null <<< "$iface_law_no_handler_base_dump
$iface_law_no_handler_changed_dump"
check "interface-law-no-handler-premise-exit" "$iface_law_no_handler_premise_exit" "0"
check "interface-law-no-handler-visible" "$iface_law_no_handler_premise" "True|True|True"
printf '%s' "$iface_law_no_handler_base_dump" > "$tmpdir/interface-law-no-handler-base.json"
printf '%s' "$iface_law_no_handler_changed_dump" > "$tmpdir/interface-law-no-handler-changed.json"
capture iface_law_no_handler_diff iface_law_no_handler_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-law-no-handler-base.json" "$tmpdir/interface-law-no-handler-changed.json" 2>/dev/null
check "interface-law-no-handler-diff-exit" "$iface_law_no_handler_diff_exit" "0"
capture iface_law_no_handler_view iface_law_no_handler_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print(json.dumps({"moved":d["interfaceInvalidation"]["moved"],"contracts":d["publicLawContractsMoved"],"candidates":d["interfaceInvalidation"]["recheckCandidates"],"lawsMoved":d["lawFactsMoved"],"status":d["decision"]["status"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_law_no_handler_diff"
check "interface-law-no-handler-view-exit" "$iface_law_no_handler_view_exit" "0"
check "interface-law-no-handler-fanout" "$iface_law_no_handler_view" '{"moved":["Lib"],"contracts":["Lib"],"candidates":["@entry","Lib"],"lawsMoved":false,"status":"measured"}'

# The public projection must not launder private declaration text into the interface.
capture iface_law_private_base_dump iface_law_private_base_exit "$bang" query dump "$tmpdir/interface-law-private-base/main.bang" 2>/dev/null
capture iface_law_private_changed_dump iface_law_private_changed_exit "$bang" query dump "$tmpdir/interface-law-private-changed/main.bang" 2>/dev/null
check "interface-law-private-base-exit" "$iface_law_private_base_exit" "0"
check "interface-law-private-changed-exit" "$iface_law_private_changed_exit" "0"
capture iface_law_private_view iface_law_private_view_exit python3 -c '
import json,sys
a,b=[json.loads(line) for line in sys.stdin if line.strip()]
lib=lambda d: next(x for x in d["moduleInterfaces"] if x["module"]=="Lib")
print("|".join([str(a["coreFingerprint"]["digest"]==b["coreFingerprint"]["digest"]),str(lib(a)["digest"]==lib(b)["digest"]),str([x["name"] for x in lib(a)["exports"]]==["marker"]),str(lib(a)["exports"][0]["laws"]==[])]))
' 2>/dev/null <<< "$iface_law_private_base_dump
$iface_law_private_changed_dump"
check "interface-law-private-view-exit" "$iface_law_private_view_exit" "0"
check "interface-law-private-absent" "$iface_law_private_view" "True|True|True|True"

# The rendering kill shot is now committed at the actual export boundary.
capture iface_law_stable_base_dump iface_law_stable_base_exit "$bang" query dump "$tmpdir/interface-law-stable-base/main.bang" 2>/dev/null
capture iface_law_stable_noise_dump iface_law_stable_noise_exit "$bang" query dump "$tmpdir/interface-law-stable-noise/main.bang" 2>/dev/null
capture iface_law_order_ab_dump iface_law_order_ab_exit "$bang" query dump "$tmpdir/interface-law-order-ab/main.bang" 2>/dev/null
capture iface_law_order_ba_dump iface_law_order_ba_exit "$bang" query dump "$tmpdir/interface-law-order-ba/main.bang" 2>/dev/null
check "interface-law-stable-base-exit" "$iface_law_stable_base_exit" "0"
check "interface-law-stable-noise-exit" "$iface_law_stable_noise_exit" "0"
check "interface-law-order-ab-exit" "$iface_law_order_ab_exit" "0"
check "interface-law-order-ba-exit" "$iface_law_order_ba_exit" "0"
capture iface_law_stability_view iface_law_stability_view_exit python3 -c '
import json,sys
ds=[json.loads(line) for line in sys.stdin if line.strip()]
lib=lambda d: next(x for x in d["moduleInterfaces"] if x["module"]=="Lib")
body=lambda d: lib(d)["exports"][0]["laws"][0]["body"]
print("|".join([str(lib(ds[0])["digest"]==lib(ds[1])["digest"]),body(ds[0]),str(lib(ds[2])["digest"]==lib(ds[3])["digest"]),body(ds[2]),str(body(ds[2])==body(ds[3]))]))
' 2>/dev/null <<< "$iface_law_stable_base_dump
$iface_law_stable_noise_dump
$iface_law_order_ab_dump
$iface_law_order_ba_dump"
check "interface-law-stability-view-exit" "$iface_law_stability_view_exit" "0"
check "interface-law-merge-context-invariant" "$iface_law_stability_view" "True|gate.check(0) == 0|True|let ignored = Lib_one in gate.check(Lib_zero) == Lib_zero|True"

# Keep the fail-loud residue executable: realization-law evidence that moves without any public
# declared contract explanation remains indeterminate instead of being silently ignored.
capture iface_unexplained_law_fixture iface_unexplained_law_fixture_exit python3 -c '
import json,sys
d=json.load(open(sys.argv[1]))
d["laws"][0]["body"] += " -- unexplained"
json.dump(d,open(sys.argv[2],"w"),separators=(",",":"))
print("ok")
' "$tmpdir/interface-law-base.json" "$tmpdir/interface-law-unexplained.json" 2>/dev/null
check "interface-law-unexplained-fixture-exit" "$iface_unexplained_law_fixture_exit" "0"
capture iface_unexplained_law_diff iface_unexplained_law_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-law-base.json" "$tmpdir/interface-law-unexplained.json" 2>/dev/null
check "interface-law-unexplained-diff-exit" "$iface_unexplained_law_diff_exit" "2"
capture iface_unexplained_law_view iface_unexplained_law_view_exit python3 -c '
import json,sys
d=json.load(sys.stdin)
print(json.dumps({"moved":d["interfaceInvalidation"]["moved"],"contracts":d["publicLawContractsMoved"],"lawsMoved":d["lawFactsMoved"],"status":d["decision"]["status"],"gap":d["gap"]["code"]},separators=(",",":")))
' 2>/dev/null <<< "$iface_unexplained_law_diff"
check "interface-law-unexplained-view-exit" "$iface_unexplained_law_view_exit" "0"
check "interface-law-unexplained-refused" "$iface_unexplained_law_view" '{"moved":[],"contracts":[],"lawsMoved":true,"status":"indeterminate","gap":"unexplained-realization-law-movement"}'

# Forward-compatibility belongs to the consumer too: additive unknown fields at dump, interface,
# export, and declared-law levels do not manufacture a change under dump schemaVersion 1.
capture iface_future_fixture iface_future_fixture_exit python3 -c '
import json,sys
d=json.load(open(sys.argv[1]))
d["futureTop"]={"ignored":True}
d["moduleInterfaces"][0]["futureInterface"]=1
lib=next(x for x in d["moduleInterfaces"] if x["module"]=="Lib")
lib["exports"][0]["futureExport"]="ignored"
lib["exports"][0]["laws"][0]["futureLaw"]="ignored"
json.dump(d,open(sys.argv[2],"w"),separators=(",",":"))
print("ok")
' "$tmpdir/interface-law-base.json" "$tmpdir/interface-future.json" 2>/dev/null
check "interface-diff-additive-fixture-exit" "$iface_future_fixture_exit" "0"
capture iface_future_diff iface_future_diff_exit python3 tools/interface-diff.py \
  "$tmpdir/interface-law-base.json" "$tmpdir/interface-future.json" 2>/dev/null
check "interface-diff-ignore-unknown-exit" "$iface_future_diff_exit" "0"
capture iface_future_view iface_future_view_exit python3 -c 'import json,sys; d=json.load(sys.stdin)["interfaceInvalidation"]; print(str(d["moved"]==[] and d["recheckCandidates"]==[]))' 2>/dev/null <<< "$iface_future_diff"
check "interface-diff-ignore-unknown-fields" "$iface_future_view" "True"

# A pre-v2 dump fails with the version-domain diagnosis before missing export fields are parsed.
capture iface_v1_fixture iface_v1_fixture_exit python3 -c '
import json,sys
d=json.load(open(sys.argv[1]))
for interface in d["moduleInterfaces"]:
  interface["algorithm"]="bang-module-interface-json-v1-uint64"
  for export in interface["exports"]: export.pop("laws",None)
json.dump(d,open(sys.argv[2],"w"),separators=(",",":"))
print("ok")
' "$tmpdir/interface-base.json" "$tmpdir/interface-v1.json" 2>/dev/null
check "interface-diff-v1-fixture-exit" "$iface_v1_fixture_exit" "0"
capture iface_v1_error iface_v1_exit python3 -c '
import subprocess,sys
p=subprocess.run([sys.executable,"tools/interface-diff.py",sys.argv[1],sys.argv[1]],text=True,capture_output=True)
print(p.stderr.strip())
raise SystemExit(p.returncode)
' "$tmpdir/interface-v1.json"
check "interface-diff-v1-refused-exit" "$iface_v1_exit" "1"
check "interface-diff-v1-version-diagnosis" "$iface_v1_error" "interface-diff: before: moduleInterfaces[0] requires interface algorithm 'bang-module-interface-json-v2-uint64'; got 'bang-module-interface-json-v1-uint64'"

# `cacheKeySafe:false` has executable teeth: if a digest and the complete exports disagree (collision,
# corruption, or producer bug), refuse rather than choosing whichever signal is convenient.
capture iface_tamper_fixture iface_tamper_fixture_exit python3 -c '
import json,sys
d=json.load(open(sys.argv[1]))
lib=next(x for x in d["moduleInterfaces"] if x["module"]=="Lib")
lib["digest"]=("0" if lib["digest"][0]!="0" else "1")+lib["digest"][1:]
json.dump(d,open(sys.argv[2],"w"),separators=(",",":"))
print("ok")
' "$tmpdir/interface-public-body.json" "$tmpdir/interface-tampered.json" 2>/dev/null
check "interface-diff-tamper-fixture-exit" "$iface_tamper_fixture_exit" "0"
capture iface_tamper_error iface_tamper_exit python3 -c '
import subprocess,sys
p=subprocess.run([sys.executable,"tools/interface-diff.py",sys.argv[1],sys.argv[2]],text=True,capture_output=True)
print(p.stderr.strip())
raise SystemExit(p.returncode)
' "$tmpdir/interface-base.json" "$tmpdir/interface-tampered.json"
check "interface-diff-digest-export-disagreement-exit" "$iface_tamper_exit" "1"
check "interface-diff-digest-export-disagreement-refused" "$iface_tamper_error" "interface-diff: module 'Lib' digest and complete export comparison disagree"

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
check "dump-laws-present" "$(printf '%s' "$got_out3" | grep -o '"laws":\[{"id":"Eq:refl"' || true)" '"laws":[{"id":"Eq:refl"'
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

# First BANG-written compiler-fact ingestion journey: feed the freshly generated dump through the
# shipped Console boundary and the example JSON parser. The observable is the top-level object tag,
# not a bare parse-success bit. This deliberately
# reads the live schema instead of pinning a copied dump that would go stale as query facts evolve.
capture bang_dump_header bang_dump_header_exit bash -o pipefail -c \
  '"$1" query dump examples/json/main.bang | "$1" run --env=real --allow=Console examples/json/query-dump.bang' \
  _ "$bang"
check "bang-consumes-live-dump-exit" "$bang_dump_header_exit" "0"
check "bang-consumes-live-dump-object" "$bang_dump_header" "5"

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
contains_codec='"contractId":"Codec_Codec","realization":"Shift7","realizationId":"Codec_Shift7","law":"decode_encode"'
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

# Per-declaration projections are role-agnostic "what type would this selected binding have?"
# questions. Pin the deliberate distinction: stdin remains a library subject for whole-program
# acceptance, while selecting its `main` for a type/effect projection can still answer cleanly.
role_src='let main = 1 + 2'
got_role_check="$(printf '%s\n' "$role_src" | "$bang" check --json 2>/dev/null)" && got_role_check_exit=0 || got_role_check_exit=$?
got_role_effects="$(printf '%s\n' "$role_src" | "$bang" query effects main 2>/dev/null)" && got_role_effects_exit=0 || got_role_effects_exit=$?
check "stdin-computed-main-whole-program-refused" "$got_role_check_exit" "1"
check "stdin-computed-main-whole-program-b019" "$(printf '%s' "$got_role_check" | grep -c '"explainCode":"B019"' || true)" "1"
check "stdin-computed-main-projection-is-role-agnostic" "$got_role_effects_exit:$got_role_effects" '0:{"ok":true,"row":"{}"}'

# naming a nonexistent decl is a LOUD op-level miss (ok:false ON STDOUT) but exit 0: the TOOL ran
# successfully and produced a well-formed (negative) answer (exit 1 is reserved for "the op could
# NOT run" — a parse/resolution failure — not an op-level negative answer).
got_out="$("$bang" query type "$tmpdir/simple.bang" nosuch 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-miss-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "type-miss-exit" "$got_exit" "0"

# ══ 5. `laws` ══

got_out="$("$bang" query laws "$tmpdir/laws.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-exit" "$got_exit" "0"
check "laws-shape" "$got_out" '{"ok":true,"laws":[{"id":"Eq:refl","trait":"Eq","contract":"Eq","contractId":"Eq","realization":null,"realizationId":null,"law":"refl","params":["x"],"body":"eq(x, x) == 1"}]}'

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
                 "def double $tmpdir/simple.bang" "refs double $tmpdir/simple.bang" \
                 "body-artifact Lib::selected $tmpdir/body-slice-effect-base/main.bang"; do
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
# always runs (287 — dependency observation, recomputation, reuse, module graph, initializer order, structural
# invalidation-fanout, resolved-core fingerprint, law-aware interface, and resolved-module-interface
# checks included);
# jq's three guarded blocks
# contribute five `check()` calls in total when jq is present (the composed query checks both
# producers in addition to its output;
# jq IS in the standard `nix develop` shell, so this is the steady-state path); duckdb's guarded
# block contributes two checks when
# duckdb happens to be reachable (NOT in the flake — an ad-hoc `nix shell` reach). The total
# tracks WHICH optional tools actually ran, so a genuinely truncated run is still caught
# regardless of which tools happened to be on PATH (never a silently-widened acceptable range).
want_total=287
if command -v jq >/dev/null 2>&1; then want_total=$((want_total + 5)); fi
if [ "$duckdb_ran" -eq 1 ]; then want_total=$((want_total + 2)); fi
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
