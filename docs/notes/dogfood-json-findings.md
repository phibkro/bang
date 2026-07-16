<!-- note-status: active -->
# Dogfood findings — a JSON parser/printer written in bang

> `examples/json/` is a real program: a value-subset JSON parser + printer +
> the round-trip/consistency checks it can safely run without tripping the
> critical finding below. This note is the friction log from writing it —
> every entry is what-I-tried / what-happened / what-I-expected / severity,
> plus the good surprises. Toolchain used throughout: `bang check --json`,
> `bang run` (kernel), `bang run --compiled` (verified machine), `bang fmt`,
> `bang repl`.

## Summary (counts by severity)

- **Blocker: 1** — non-termination composing Div-declared nested `let rec`s
  past a size/call threshold (both engines hang identically).
- **Missing-feature: 3** — no mutual `data`/`let rec`, no line comments, no
  unary minus.
- **Papercut: 6** — thunk-wraps-a-`let rec` type trap, nested-constructor
  match-arm patterns unsupported, `fst`/`snd` absent, internal metavariable
  IDs leaking into a type error, an under-ascribed match producing a cryptic
  error, ctor-as-bare-arg needing parens.
- **Good (worked better than expected): 5** — see the end of this note.

## BLOCKER — composing two Div-declared nested-`let rec` closures hangs both engines

**What I tried** (minimal repro, verified on unmodified checked-in code paths
— the shape in `examples/json/main.bang` before I scoped it down):

```
let parseTop = { fun s => match ($parseValue s) { None -> JNull, Some(p) -> let (v, rest) = p in v } } in
let objJ = $parseTop "{\"a\": 1, \"b\": 2}" in
$printJson objJ
```

`parseValue` and `printJson` are each a single outer `let rec` with several
SIBLING nested `let rec`s inside different match arms (the only way to write
mutually-recursive-feeling parsers/printers without a mutual `let rec` — see
the missing-feature entry below). Each nested `let rec` is declared `! {Div}`
per ADR-0088 (a body calling the outer knot has a latent effect the knot's
row must cover).

**What happened**: both `bang run` and `bang run --compiled` hang — CPU-bound,
no output, no `outOfFuel`, past 590 real seconds (I killed it with `timeout`; the
default fuel is 100000, documented as "generous... top out around 200" for
the existing corpus). I isolated this extensively:

- Parsing a 2-field object ALONE (`$parseTop "{\"a\":1,\"b\":2}"`, `tagOf`
  it, discard) — **fast, correct**.
- Printing a HAND-BUILT (not parsed) 2-field `Json` value ALONE — **fast,
  correct** (`{"a":1,"b":2}`).
- Parsing it, THEN printing the SAME parsed value (as above) — **hangs**.
- Two structurally-identical calls to the same nested `let rec` (e.g.
  `parseOneField` called twice, no self-recursion involved) — **hangs**,
  even when the second call's argument is a hardcoded `SNil` that hits the
  base case immediately.
- The SAME "outer `let rec` + N sibling nested `let rec`s, each Div-declared,
  each calling the outer knot" shape with `Int`/simple-list return types
  (not `Option (Json * Str)`) — terminates fine, called twice, called
  thrice, at every depth I tried.
- A SINGLE simple (non-nested) `Div`-declared `let rec`, called twice —
  **fast, correct** (sanity check: `fact 5 + fact 6 = 840`).
- The threshold is NOT a fixed call count: 3 sequential `parseTop` calls (flat
  array + flat object + nested-array-with-object) work; adding a 4th
  (`"[null,true,false]"` before the nested one) tips it into hanging. This
  smells like an accumulating cost (each `let`/closure widening some
  per-step re-traversal) rather than a single bad transition — but from the
  outside it is indistinguishable from true non-termination: no partial
  output, no `outOfFuel`, CPU pegged, unresponsive to the 100000 default fuel
  bound that should make it fail fast if it really were "just" fuel-bound.

**What I expected**: `bang run` to either produce `163`-style correct output
in well under a second (matching every other example project's runtime), or
to print `out of fuel` promptly if it genuinely exceeded the budget.

**Severity**: blocker. This directly blocks the natural "parse then print"
composition that is JSON's whole point, and it blocks writing a realistic
multi-shape test program at all — I had to scope `main.bang` down to 3
`parseTop` calls plus exactly one `printJson` call on a hand-built (never
parsed) value to stay under whatever threshold triggers it. A user with no
knowledge of this landmine would write the natural round-trip test first and
watch it hang with zero diagnostic signal.

**Feeds**: new — I did not find an existing issue for this. Likely candidates
to investigate: `structOK`/Div-row bookkeeping cost when MULTIPLE sibling
nested `let rec`s are Div-declared inside one outer knot (ADR-0088/0091's
combined interaction — neither ADR's dogfood corpus exercised siblings this
deep, both landed via a single accumulator-shaped nested `let rec`, not two
or three siblings each independently Div-declared). Given both engines hang
identically, this is very likely upstream of the compiled-machine split
(shared `Source.eval`/kernel-adjacent cost, or something the elaborator bakes
into the lowered term that both engines then dutifully re-traverse).

**Repro files** (not committed — paths in my scratchpad, reproducible from
the description above against the checked-in `examples/json/main.bang`'s
parser/printer verbatim): the minimal 2-line repro above is sufficient to
reproduce from scratch against any build.

## MISSING-FEATURE — no mutual `data` or mutual `let rec`

**What I tried**:
```
data Json = JNull | JArr(JList)
data JList = JNil | JCons(Json, JList)
```
(and the reverse declaration order).

**What happened**: `error: unknown type name 'JList'` (forward reference)
or `unknown type name 'Json'` (backward reference) — `data` declarations
are elaborated sequentially with no forward-visibility, and there is no
`data ... and ...` mutual form.

**What I expected**: either mutual `data` support, or at minimum an error
message suggesting the workaround (fold both types into one self-recursive
`data`).

**Workaround I used**: a SINGLE self-recursive `Json` with a generic
`JCons(Json, Json)` "list cell" constructor reused for BOTH array elements
and object fields (tagging field entries with a `JField(Str, Json)`
wrapper). This works and is arguably fine style, but it is a real
constraint an agent/user has to discover, not something the language
suggests.

Similarly, `let rec f = ... and g = ...` does not exist — confirmed by
grepping `Bang/Frontend/Surface.lean` for `mutual`/`and` in the `let rec`
grammar and by the parse error `expected 'in', got 'and'` when I tried it
for the printer's `printJson`/`printElems`/`printFields`. The workaround
(nested `let rec`s inside the outer function's body, each closing over the
outer name to "call back" recursively) is exactly the shape that triggers
the BLOCKER above — so this missing feature and the blocker are likely
connected: bang's only route to a mutually-recursive-feeling function
group is the shape that hangs.

**Severity**: missing-feature (blocker-adjacent, since the workaround is
what triggers the blocker above).

**Feeds**: new. Distinct from ADR-0076 (module system) — this is about
recursion/data-declaration structure WITHIN one file, not cross-file
imports.

## MISSING-FEATURE — no line comments at all

**What I tried**: `-- a comment` on its own line, and `-- trailing comment`
after code, expecting a Lean-style or C-style line comment.

**What happened**: `unexpected '-' where an atom was expected` — bang
parses `--` as two binary-minus tokens in an atom position, not a comment
marker. Grepping `Bang/Frontend/Surface.lean` for `comment`/block-comment
markers turns up nothing in the SURFACE grammar (the one hit is Lean-side
documentation prose about the Lean file's own comments). None of the
example `main.bang` files in the repo use a comment of any kind — this
appears to be a genuine gap, not something I missed in the docs.

**What I expected**: some form of comment syntax, since a 200-line
recursive-descent parser without any comments (my `main.bang` has zero,
by necessity) is a real ergonomics tax on anyone reading or maintaining
it.

**Severity**: missing-feature. Every non-trivial program benefits from
comments; a language with none forces all documentation external to the
source (as this very note demonstrates).

**Feeds**: new.

## MISSING-FEATURE — no unary minus (negative integer literals)

**What I tried**: `0 - 1` written as `-1` in a match-arm sentinel value
(`JNull -> -1, ...`).

**What happened**: `unexpected '-' where an atom was expected` — `-` is
binary-only (`opInfo`'s table has no prefix/unary form). Confirmed by
grep: `Bang/Frontend/Surface.lean` has no unary-minus handling, only the
binary arithmetic table.

**What I expected**: either unary minus, or — if intentionally omitted for
minimalism — a clear diagnostic hinting at `0 - n` (the actual error just
says "expected an atom", giving no hint).

**Workaround**: `0 - 1` everywhere I needed a negative sentinel. Mechanical
but noisy across a dozen sentinel values in this program (`tagAt`'s
not-found sentinel, `asInt`'s type-mismatch sentinels, etc).

**Severity**: missing-feature/papercut. `Int` is documented as unbounded ℤ
(ADR-0067) with no overflow UB, so the type clearly intends to support
negatives — just the literal syntax doesn't reach them directly.

**Feeds**: new.

## PAPERCUT — wrapping a `let rec` in `{ }` silently makes a double-thunk

**What I tried** (the natural pattern coming from the parser-combinators
example's `let isDigit = { fun n => ... }` style, applied to a recursive
helper):
```
let dropWs = { let rec go : Str -> Str = fun s => match (s : Str) { ... } in go } in
($dropWs) "   ab"
```

**What happened**: `error: app: callee is not a function`. Root cause once
isolated: `let rec go = ...` already binds `go` as a `Thunk (Str -> Str)`
(a VALUE), so wrapping the whole `let rec ... in go` expression in `{ }`
thunks it AGAIN — `dropWs : Thunk (Thunk (Str -> Str))`. `($dropWs)` forces
once, leaving a thunk where a function was expected. `($($dropWs))` doesn't
fix it either (different error: "not a value — wrap a computation in
braces", since `$dropWs` yields a COMPUTATION and the outer `$` demands a
value).

**What I expected**: either this to just work (the non-recursive
`{ fun x => ... }` pattern generalizing to recursive bodies), or a more
specific error than "callee is not a function" pointing at the double-thunk.

**Fix**: bind `let rec` directly at the point of use — no `{ }` wrapper
needed, since it's already a thunk: `let rec dropWs : Str -> Str = fun s =>
... in ($dropWs) "   ab"`.

**Severity**: papercut, but a SPECIFIC one worth flagging: the house style
in `examples/parser-combinators/main.bang` (non-recursive helpers ALL
wrapped in `{ }`) primes exactly this mistake the first time a helper
needs to become recursive.

**Feeds**: new.

## PAPERCUT — no nested constructor patterns in `match` arms

**What I tried**:
```
match v {
  JArr(JCons(JInt(a), JCons(JInt(b), JNilL))) -> a + b,
  ...
}
```

**What happened**: `expected ',' or ')' in a match-arm payload, got '('` —
a named-ctor match arm's payload slots are flat identifiers only (`Ctor(x,
y)`), never a nested constructor pattern (`Ctor(Ctor2(x), y)`).

**What I expected**: either nested patterns, or (if intentionally flat) a
clearer message than a raw parser expectation about `,`/`)`.

**Workaround**: flatten into sequential `match`es via small helper
functions (`elemAt0`, `asInt` in my early drafts) that peel one layer at a
time. Mechanical, but changes the shape of otherwise-natural pattern-match
code significantly — every "match on a specific shape 2 levels deep"
becomes 2+ separate match expressions.

**Severity**: papercut/missing-feature borderline. Common in parser/AST
code (matching a specific nested shape) — I hit it constructing my test
harness's assertions, not the parser itself.

**Feeds**: new.

## PAPERCUT — no `fst`/`snd` in the stdlib

**What I tried**: `let keyJ = fst kp in let rk = snd kp in ...` on a
`Json * Str` pair.

**What happened**: neither identifier resolves (confirmed by grep —
`Bang/Frontend/TypeCheck.lean`'s `stdlibFnSrcs`/`genericPrelude` have no
`fst`/`snd`).

**What I expected**: `fst`/`snd` as free stdlib functions, mirroring
`concat`/`reverse`/`eq`'s "injected in scope of every program" treatment
— products are a builtin type (`A * B`), so their projections feel like
the same tier as `concat` for `Str` (also a builtin-ish type via `data`).

**Workaround**: `let (keyJ, rk) = kp in ...` (product-pattern destructuring
in a `let`, which DOES work) instead of named projections. Fine once
discovered, but `fst`/`snd` are the first thing most people reach for.

**Severity**: papercut.

**Feeds**: new (or folds into the stdlib-map's future stdlib-growth
tracking — `docs/notes/stdlib-map.md`).

## PAPERCUT — internal metavariable IDs leak into a user-facing type error

**What I tried**: `fun j => match j { JNull -> ..., JArr(l) -> (match l {
...}), ... }` — a match on a BARE function parameter (no `(j : Json)`
ascription), where the data type has 9 constructors of mixed arity
(0/1/2) including a self-referential payload.

**What happened**: `error: match scrutinee is #3000020, not Json` — the
raw internal hole/metavariable identifier (`#3000020`) surfaces directly
in the diagnostic. It comes from a genuinely correct rejection (the
scrutinee's type wasn't resolved), but the message is uninterpretable
without reading the checker's internals — no indication that adding
`(j : Json)` fixes it.

**What I expected**: a message like "cannot infer the scrutinee's type;
try annotating it, e.g. `(j : Json)`" — the same class of hint the
`(e : T)` ascription syntax already documents for exactly this situation.

**Fix**: ascribe every match on a function parameter over a many-
constructor recursive `data` type: `match (j : Json) { ... }`. Isolated
precisely — the SAME match arms, unascribed, on a smaller `Json`-alike
(fewer constructors) type-checked fine; it's specifically the combination
of "bare parameter" + "this many constructors / this much self-reference"
that trips inference.

**Severity**: papercut (diagnostics-quality, not a correctness bug — the
REJECTION is correct, only the message is opaque). Cost: burned real debug
time isolating what "not Json" even meant.

**Feeds**: new (diagnostics-quality bucket — pairs with the `--json`
diagnostics work, `tools/test-check-json.sh`).

## PAPERCUT — a bare-application partial-call needs `{ }` to bind as a value

**What I tried**: `let tryVal = ($orElseJ) parseNull { ... } in ...` where
`orElseJ` is curried and the RHS is a partial application (not fully
saturated to a base-typed result).

**What happened**: `error: let-binding 'tryVal': value is not a returner
— force it ($tryVal) or bind a value` — a partially-applied curried call
is a COMPUTATION, and bare `let` requires a value.

**Fix** (already the house style in `examples/parser-combinators/main.bang`,
which I didn't immediately connect to my own case): wrap the whole partial
application in `{ }`: `let tryVal = { ($orElseJ) parseNull { ... } } in`.

**Severity**: papercut — the error message IS actionable (unlike the
metavariable-leak one above), and the fix is directly named in the message.
Noting it because it's a real trip point even with the fix hinted.

**Feeds**: none — this is well-diagnosed already; no action needed beyond
noting it worked as intended.

## PAPERCUT — a bare constructor application as a function ARGUMENT needs parens

**What I tried**: `($f) B(A)` (applying a unary function to a constructed
value, unparenthesized).

**What happened**: `error: constructor 'B' expects 1 argument(s)` — the
parser reads `B(A)` split as `B` (an atom) then a separate application to
`(A)`, or similar; the fix is `($f) (B(A))`.

**Severity**: papercut. Minor, but easy to hit reflexively coming from
languages where juxtaposition binds looser than constructor application
syntax already implies grouping.

**Feeds**: new, low-priority.

## The GOOD — what worked better than expected

- **`bang check --json` is genuinely useful for iteration.** Every
  isolation probe in this session went through `--json` first (fast,
  parseable, one-line) before falling back to `bang run` for the full
  error text. The `{"ok":false,"diagnostics":[...]}` shape is exactly
  right for an agent loop.
- **ADR-0088's declared-row recursion is exactly as advertised.** Every
  place I needed a nested helper to call back into a `Div`-declared outer
  knot, adding `! {Div}` to the helper's own annotation was the ENTIRE
  fix — no fixpoint iteration, no surprising propagation, matches the ADR's
  stated contract precisely (`digits`, `parseElems`, `parseOneField`,
  `parseFields`, `printElems`, `printFields`, `tagAt` all needed exactly
  this and nothing more).
- **ADR-0091's structOK correctly certified my genuinely-structural
  recursions as `⊥`-row with zero ceremony.** `dropWs`, `litMatch`,
  `scanStr`, `scanDigits` (all single-arg, structural) type-checked with
  NO declared row at all — the certifier silently did its job. I only
  needed the `! {Div}` escape hatch for the handful of functions that
  genuinely called something else Div-marked.
- **Strings-as-`List Char` composed completely naturally** with a
  user-defined recursive `data Json` — no friction at the `Str`/`Char`
  boundary anywhere in ~150 lines of parser code. Backslash-escape
  decoding inside JSON string literals (`\n`, `\"`, `\\`) was
  straightforward hand-rolled code point comparison (110/34/92), and it
  worked first try once the parser's own bracket-nesting was correct.
  Separately, bang's OWN string-literal escapes (`\" \\ \n`, ADR-0074)
  worked exactly as documented when I needed to embed a literal `"` in a
  test-input string.
- **`bang fmt` is idempotent and semantics-preserving on real, sizeable
  code.** Ran it on the full ~200-line parser/printer; the reformatted
  output re-typechecked and re-ran to the identical answer, and a SECOND
  `fmt` pass produced a byte-identical file (checked via `diff`).

## Module-system pain (expected; concrete shape for the parallel ADR work)

Single-file-only meant the `Json` data type, `parseValue`, and `printJson`
all live in one ~230-line file with no separation. The concrete shape of
what I wanted, for whoever drafts the module ADR:

- **Split by concern, not by size.** I wanted `Json.bang` (just the `data`
  declaration), `Parse.bang` (importing `Json`), `Print.bang` (importing
  `Json`), and `main.bang` (importing both) — the natural "one type, two
  independent consumers" shape. Nothing about my program wanted CIRCULAR
  imports; `Parse` and `Print` never need each other.
- **Namespace collision was a non-issue in practice** (single-file forces
  everything into one flat scope already), but I DID lean on bang's
  lexical-shadowing rule more than I expected — `key`, `val`, `x`, `y` as
  generic match-arm binder names reused across many nested `let`/`match`
  scopes, relying on shadowing rather than uniquing names by hand. A
  module system with per-file scopes would remove most of the PRESSURE to
  invent unique names across a large file, since today everything
  competes in one global lexical scope.
- **The tokenizer example's `TokList`/parser-combinators' `Parser a` are
  exactly the "would want to `import`" shapes** — a real multi-file
  project would want this JSON parser to `import` the tokenizer's
  `Str`-splitting helpers rather than re-deriving `dropWs`/whitespace
  logic from scratch (I re-wrote a whitespace-skipper that is 80% the
  same shape as the tokenizer's space-splitting `tokenize`).

## Toolchain notes (used all four surfaces, as requested)

- `bang run <file>` / `bang run --compiled <file>` — primary verification
  loop; both engines cross-checked at every stage, and both hang
  IDENTICALLY on the blocker case (ruling it out as compiled-engine-only).
- `bang check --json <file>` — used constantly for fast iteration; see
  the GOOD section above.
- `bang fmt <file>` — used once at the end to canonicalize the final
  `main.bang`; idempotent, semantics-preserving, confirmed by diff + re-run.
- `bang repl` — used briefly (`:t 3 + 4` sanity check) early in
  orientation; did not end up needing it for the main development loop
  since file-based iteration with `check --json` was faster for a
  program this size. Worth noting as a possible gap in MY workflow, not
  necessarily the REPL's: a `:load`-based incremental-definition workflow
  might have caught the blocker's threshold behavior sooner (build up the
  program definition-by-definition inside one REPL session, watching for
  the exact point a call starts taking noticeably longer) — I didn't
  explore this because the blocker's isolation ended up needing many
  independent full-file variants tested in parallel, which suited
  `bang run` over a REPL session better.
