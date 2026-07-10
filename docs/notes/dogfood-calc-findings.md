<!-- note-status: active -->
# Dogfood findings — a multi-module calculator written in bang

> `examples/calc/` is a real program: a lexer → parser → evaluator arithmetic
> calculator split across SIX files (`Ast` / `Lexer` / `Parser` / `Eval` /
> `Print` / `main`, ~300 lines), the LARGEST bang program in the corpus. It has
> precedence + associativity, parentheses, unary minus, guarded division, and
> variables via an environment; the evaluator carries a `Trace` user effect used
> STRUCTURALLY (a per-node `log`, silent-vs-counting handler pair). This note is
> the friction log — every wall is what-I-tried / what-happened (exact
> diagnostic) / workaround-or-stop / severity, plus the good surprises.
> Toolchain: `bang run` (env engine, ADR-0094 default = the gate), `bang run
> --compiled` (CalcVM), `bang run --engine=ck` (kernel), `bang check`, `bang fmt`.

## Summary (counts by severity)

- **Blocker: 0** — the program reaches DONE on the gate engine (`bang run` env),
  deterministic output `11021193`, `check-examples` green.
- **Correctness (in a non-gate tool): 2** — (1) `bang run --compiled` HANGS on
  the parser where env + ck both return the right answer; (2) `bang fmt` is NOT
  semantics-preserving on `$(Mod.op) arg` — it emits a program that no longer
  parses/runs.
- **Missing-feature / arity wall: 2** — constructor payload arity capped at ≤ 2;
  no mutual `let rec` AND sibling nested `let rec`s can't forward-reference.
- **Papercut: 3** — `use Mod (f)` won't hoist a `pub let rec` (only plain `let` +
  ctors), which removed the clean escape from the fmt bug; imported-effect names
  must be spelled with the merged qualified form (`Mod_Eff`) in EVERY position
  (row / `Cap` / `with … as`), even in the effect's OWN defining module; module
  search probes only the entry file's dir + the repo root (not the example's
  subdir).
- **Good (worked better than expected): 5** — see the end.

Ranked "what would have helped most" is the final section.

## CORRECTNESS — `bang run --compiled` hangs on the parser; env + ck agree

**What I tried**: run the finished program on all three engines.

```
bang run              examples/calc/main.bang   → 11021193   (env, ADR-0094 default = the gate)
bang run --engine=ck  examples/calc/main.bang   → 11021193   (kernel)
bang run --compiled   examples/calc/main.bang   → HANGS (timeout 60s, CPU-bound, no output)
```

**Isolation** (bisected against the compiled engine specifically):

- Lexer alone (chars → tokens, count) — **works** on compiled (`9`).
- Full parser on the single-token input `"7"` (hits `parseFactor`→`ENum`
  immediately, no operator loop, no re-entry) — **works** on compiled (`7`).
- `"1 * 2"` (uses `parseTerm`/`termLoop`, which never re-enter the outer
  `parseExpr` knot) — **works** on compiled (`3`).
- `"1 + 2"`, `"0 - 7"` (use `exprLoop`, the OUTERMOST sibling, which calls
  `parseTerm` and lives under the outer `parseExpr` knot) — **HANG**.
- `"( 7 )"` (parens: `parseFactor`'s `TLParen` arm calls `parseExpr`
  RE-ENTRANTLY) — **HANGS**.
- A hand-built minimal repro — an outer `let rec` knot with 2 sibling nested
  `let rec`s returning `Option (Int * Int)`, and even 4 siblings — **works** on
  compiled. So it is NOT the sibling count or the `Option`-pair return per se.

**Diagnosis (best available, external)**: the trigger is a **re-entrant call to
the outer `let rec` knot from within its own nested siblings** — `exprLoop`
calling `parseTerm` (which calls `parseFactor`) all under `parseExpr`, and
`parseFactor` re-entering `parseExpr` for parens. The CalcVM engine (the
Bahr–Hutton `compile`/`exec` triple) diverges here while the env machine
(EnvMachine, ADR-0094) and the CK kernel (`Source.eval`) both terminate with the
correct answer. Given env AND ck agree, the compiled path is the outlier — this
is downstream of the shared kernel semantics, in the CalcVM lowering/exec of
deeply-nested-plus-re-entrant knots.

**What I expected**: all three engines agree (Invariant #1, "proof rides the
reference"), or the compiled engine prints `out of fuel` promptly rather than
pegging CPU with no signal.

**Severity**: correctness, but NON-gating — `check-examples` (and
`check-examples-env`) both use `bang run` (env), which is correct and fast, so
the example is DONE and green. The compiled-engine divergence is a real finding
about the CalcVM's handling of this recursion shape.

**Relation to the JSON round**: the json findings flagged "multiple sibling
nested Div `let rec`s" as a suspected blocker that hung BOTH engines. That case
now runs on compiled (json's `main.bang` returns `163` on `--compiled` today).
The calc parser is a sharper instance — the specific killer is **re-entering the
OUTER knot from a sibling / from a parens arm**, and it is now compiled-ONLY, not
both-engines. Likely candidate: CalcVM `exec` cost/loop on the knot's captured
continuation when a sibling re-invokes the outer name.

**Repro**: `examples/calc/Parser.bang` verbatim + any input containing `+`, `-`,
or `(` (e.g. `"1 + 2"`), run under `bang run --compiled`. Kill with `timeout`.

## CORRECTNESS — `bang fmt` breaks `$(Mod.op) arg` (not semantics-preserving)

**What I tried**: run `bang fmt` over the six files to canonicalize, per the json
round's note that fmt is "idempotent and semantics-preserving on real code".

**What happened**: the five LIBRARY modules (`Ast`/`Lexer`/`Parser`/`Eval`/
`Print`, whose only forces are intra-module `$name`) fmt cleanly and are
idempotent. `main.bang` — the one file using `$(Mod.op) arg` cross-module calls
— came out BROKEN. Minimal repro:

```
# g.bang:  pub let mk = {fun s => s + 1}
# original (runs → 7):
let calc = {fun src => let ast = $(g.mk) src in handle (($(g.mk)) ast) with E as e { op(x) => x }}
# after `bang fmt` (error):
let calc = {fun src => let ast = $g.mk src in handle $g.mk ast with E as e { op(x) => x }}
#   → error: let-binding 'ast': not a value (wrap a computation in braces)
```

fmt drops the parens in `$(g.mk) src`, emitting `$g.mk src`. But `$` forces only
the ATOM to its right (documented — the json README even warns `$mod.op arg`
"does NOT parse the way you'd expect"), so `$g.mk src` re-parses as
`($g).mk src`, `ast` binds a non-value, and the program no longer runs. fmt
canonicalizes INTO the exact trap the docs warn users away from.

**Second facet (non-idempotency)**: fmt also OSCILLATES on the spacing between a
`$Mod.op` and a parenthesized argument — `$Mod.op (arg)` ⟷ `$Mod.op(arg)` flip
on successive passes:

```
fmt once:   let ast = $Parser.parseAll ($Lexer.lex src)
fmt twice:  let ast = $Parser.parseAll($Lexer.lex src)   ← changed again
```

This makes `fmt(fmt(x)) != fmt(x)` — and `tools/test-fmt.sh` (in `just verify`)
gates exactly `fmt(fmt(main)) == fmt(main)` over every `examples/*/main.bang`. A
multi-file `main.bang` that calls imported functions on parenthesized arguments
therefore FAILS the fmt gate outright.

**What I expected**: fmt to preserve `$(Mod.op)` verbatim (or re-emit an
equivalent that still forces the qualified op), since it is the ONLY working way
to force-and-apply a bare-imported `let rec` (see the `use`-won't-hoist-rec wall
below — `use` is not an alternative for recursive functions).

**Severity**: correctness (a formatter that changes program meaning is worse than
no formatter) AND it collides with a `just verify` gate.

**Workaround that keeps the program correct AND the gate green**: flatten so
every cross-module call takes a BARE-identifier / literal argument, never a
parenthesized sub-expression — `let toks = $(Lexer.lex) src in let ast =
$(Parser.parseAll) toks` instead of `$(Parser.parseAll) ($(Lexer.lex) src)`.
`$(Mod.op) bareArg` fmt's to `$Mod.op bareArg`, which is a FIXED POINT (idempotent),
so `test-fmt` passes; meanwhile `check-examples` runs the ORIGINAL source (with the
`$(Mod.op)` parens intact, which is correct) — the gate checks fmt-idempotency of
the source, not that fmt's OUTPUT runs. So the committed `main.bang` is written
with `$(Mod.op)` (correct) and structured so fmt is idempotent (gate-green). This
is a real design tax: the corpus's largest program had to be re-shaped around a
formatter bug to satisfy a formatter gate.

**Repro**: the 3-line `g.bang` + user above, `bang fmt` then `bang run` the
output (semantics break); and `bang fmt … | bang fmt` on any `$Mod.op (paren-arg)`
form (non-idempotency).

## MISSING-FEATURE / ARITY — constructor payload arity capped at ≤ 2

**What I tried**: `pub data Env = EnvNil | EnvCons(Str, Int, Env)` — the natural
"name, value, rest" environment cell.

**What happened**: at the DECL, `error at 1:15: constructor 'Mk': payload arity ≤
2 in v1 (nest tuples)`. At a USE site the surface parser instead reports `cap op
'EnvCons' takes at most 2 arguments (got 3)` — i.e. a 3-arg ctor application is
mis-parsed as a capability-op call (`cap.op(a,b)`, arity ≤ 2), so the error you
hit first depends on whether the decl or the use is seen first, and neither
message says "constructors max out at 2 args".

**What I expected**: either arbitrary ctor arity, or (given the v1 cap) the
`≤ 2 (nest tuples)` hint at BOTH the decl and the use site, not a confusing
"cap op … takes at most 2 arguments" at the use.

**Workaround**: `EnvCons(Str, (Int * Env))` — a 2-arg ctor whose second slot is a
built-in PRODUCT. Works cleanly (`let (v, rest) = p in …` in the match arm). The
hint literally says "nest tuples" and the product does the job — but you only see
it at the decl, and `Int * Env` reads worse than a flat 3-tuple.

**Severity**: missing-feature (with a clean workaround). AST/env code routinely
wants 3-field cells (`name, value, rest` · `op, left, right`); every one becomes
a product-nesting.

## MISSING-FEATURE — no mutual `let rec`; siblings can't forward-reference

**What I tried**: recursive descent wants `expr`/`term`/`factor` to be mutually
recursive (`factor` parses a parenthesized `expr`). bang has no `let rec … and
…`. The workaround (from the json round) is sibling nested `let rec`s inside one
outer knot. My first cut ordered them naturally: `a` calling `b` where `b` is
defined just below.

**What happened**: `error: … unbound variable b` (both env AND compiled). Sibling
nested `let rec`s are elaborated top-to-bottom with no forward visibility — a
sibling may reference only EARLIER siblings (and the outer knot), never a later
one.

**What I expected**: either mutual `let rec`, or forward-visibility among
siblings in one `let rec` group (they already share the outer knot's scope).

**Workaround**: order the four grammar levels so each calls only earlier siblings
+ the outer `parseExpr` knot — `parseFactor` (calls `parseExpr`), `termLoop`
(calls `parseFactor`), `parseTerm` (calls `parseFactor` + `termLoop`), `exprLoop`
(calls `parseTerm`). This is the ONE ordering that type-checks. It works, but it
inverts the natural top-down reading of a grammar (you write the LEAF level
first, the top rule last) and it is the exact shape that trips the compiled-engine
hang above — bang's only route to mutual-recursion IS the shape the CalcVM chokes
on.

**Severity**: missing-feature. Parser/AST code is where mutual recursion is most
natural; every such program pays this ordering tax and inherits the compiled-hang
risk.

## PAPERCUT — `use Mod (f)` won't hoist a `pub let rec` (only plain `let` + ctors)

**What I tried**: to dodge the fmt-`$(Mod.op)` bug, hoist the module functions
with `use Mod (name)` so calls become bare `$name` (which fmt handles cleanly).

**What happened**:

```
pub let plain = {fun n => n + 1}                     use r (plain) … ($plain) 4   → 5   (works)
pub let rec fac : Int -> Int ! {Div} = …             use r (fac)   … ($fac) 4     → error: unbound variable fac
```

`use` hoists a `pub let` (and `data` constructors, per `test-modules.sh`), but a
`pub let rec` comes back `unbound variable`. `bang check --json` confirms:
`{"severity":"error","code":"type","msg":"unbound variable fac"}`. Since `lex`,
`eval`, `countSteps`, `show`, `intToStr` are ALL `pub let rec`, `use` was not
available for them — the `$(Mod.op)` form (with its fmt bug) is the only route.

**What I expected**: `use` to hoist any `pub` decl regardless of `rec`-ness — a
recursive function is exactly as importable as a non-recursive one.

**Severity**: papercut, but load-bearing here — it removed the clean escape from
the fmt bug and forced the bare-arg-flattening workaround instead.

## PAPERCUT — imported effect names need the merged `Mod_Eff` form EVERYWHERE

**What I tried**: declare `pub effect Trace { log : Int -> Int }` in `Eval.bang`,
reference it as `Trace` in the row `! {Div, Trace}`, `Cap Trace`, and `with Trace
as tr` — the way a single-file program writes it.

**What happened** (a whole matrix of near-misses):

```
in Eval.bang (the DEFINING module):
  ! {Div, Trace}                        → error: 'Trace' is not a declared effect (row annotation)
  ! {Div, Eval_Trace}                   → OK   (must use the MERGED name in its OWN module)
  Cap Trace / Cap Eval_Trace            → both parse; Eval_Trace is what type-checks end-to-end

in an importer (main.bang):
  with Eff.Trace as tr { … }            → parse error: expected 'as', got '.'
  use Eff (Trace) …                     → error: unbound variable Eff_Trace  (use won't hoist an effect)
  import Eff … with Trace as tr         → error: 'Trace' is not a declared effect
  import Eff … with Eff_Trace as tr     → OK
```

So the ONLY spelling that works across the whole program is the merged
`Mod_Eff` (here `Eval_Trace`) — in the row, in `Cap`, in `with … as`, AND inside
the effect's own defining module. `data` gets a friendlier surface (`Mod.Ctor`
qualified access, `use Mod (Ctor)` hoisting); effects get neither — you must know
and hand-write the merge-time name.

**What I expected**: parity with `data` — `use Eval (Trace)` to hoist, or
`Eval.Trace` in the handler position, or bare `Trace` after import; and inside
the defining module, the un-prefixed `Trace` to just work in its own row.

**Workaround**: spell `Eval_Trace` everywhere. Documented now in the README so
the next person doesn't re-derive the matrix.

**Severity**: papercut (once you know the rule it is mechanical), but it cost real
time — the row-annotation error and the `with … as` error look unrelated, and
`use`-won't-hoist sends you down a wrong path. This is the effects-side of
ADR-0093's module surface being thinner than the `data` side.

## PAPERCUT — module search probes only the entry dir + the repo root

**What I tried**: run an entry file living in a scratch dir that `import`s a
module sitting next to it — but I first tried invoking from a different cwd.

**What happened**: `error: cannot find module 'Ast' — probed
'<entry-dir>/Ast.bang' and '<repo-root>/Ast.bang'`. The resolver searches exactly
two places: the ENTRY FILE's directory, then the repo root (`git rev-parse
--show-toplevel`) — NOT the current working directory, and NOT an example
subdir unless the entry file itself lives there.

**What I expected**: this is actually FINE and the error is EXCELLENT (it names
both probed paths — the D1 loud-error contract). Noting it because it dictates
project layout: a multi-file example must keep `main.bang` in the SAME dir as its
modules (which `examples/calc/` does), and `check-examples.sh` runs
`examples/<dir>/main.bang`, so same-dir imports resolve. No workaround needed;
recording the search order because it is load-bearing and not obvious.

**Severity**: papercut / non-issue (well-diagnosed). Reads as a "good" as much as
a papercut.

## The GOOD — what worked better than expected

- **The module system carried a 6-file program cleanly.** `import Mod` +
  `Mod.name` qualified access + `Mod_Type` type ascriptions + private-by-default
  (`pub` where I wanted export) all did exactly what the json README described.
  Splitting "one type, two consumers" (`Ast` consumed by both `Parser` and
  `Print`) was frictionless — no circular-import temptation, no namespace
  collisions across files. This is a real jump from the json round, where the
  module system was brand-new; here it just held.
- **A user effect woven STRUCTURALLY into a recursive traversal worked exactly
  as designed.** `eval`/`countSteps` perform `tr.log(1)` per AST node; the SAME
  traversal returns a pure value under `log(x) => 0` and a node count under
  `log(x) => 1`, decided entirely by the handler at `main`. A top-level `let rec`
  taking `Cap Eval_Trace` and calling `tr.log(...)`, called from inside a
  `handle`, needed zero ceremony beyond the qualified-name papercut above — the
  per-stage effect story appears in a real program.
- **env engine and ck (kernel) engine agree bit-for-bit** on the whole program
  (`11021193` both), across parser re-entry, effect handling, products, strings,
  and variables. The differential oracle held everywhere the compiled engine
  did not.
- **Strings-as-`List Char` + `$concat`/`$eq` scaled.** The lexer builds
  identifier tokens by `$concat`-ing `SCons(Char n, SNil)` cells; `Print.show`
  builds a fully-parenthesized string bottom-up; env lookup compares identifier
  strings with `$eq`. ~60 lines of string-building code, no boundary friction,
  and the round-trip check (`eval(parse(src)) == eval(parse(show(parse(src))))`)
  passed first try once precedence was right.
- **ADR-0091 `structOK` + ADR-0088 declared-row recursion behaved as advertised
  again.** Single-arg structural `let rec`s (`show`, `lookup`, `intToStr`,
  `scanNum`, `scanId`) type-checked with `! {Div}` where they call another Div
  fn, and the multi-arg `eval`/`countSteps`/`parseExpr` knots took `! {Div,
  Eval_Trace}` with no fixpoint surprises. The `match (x : T)` scrutinee
  ascription on every curried param past the first (the known let-rec gotcha) was
  the only mechanical tax, and it was predictable.

## Ergonomics at scale — what got tedious ×20 that was fine ×2

The data the small-program corpus can't surface:

- **Exhaustive match arms over a 10-constructor `Tok` type, ×4 match sites.**
  Every `match (h : Ast_Tok)` in the parser (in `parseFactor`, the inner-paren
  check, `termLoop`, `exprLoop`) must list ALL of `TNum TIdent TPlus TMinus TStar
  TSlash TLParen TRParen TEnd TErr` — even though most arms are the same `Some(acc,
  ts)` "stop here" case. Adding ONE token (`TIdent`) meant editing FOUR match
  sites to add the arm, or the checker rejects for non-exhaustiveness. At 2
  constructors this is nothing; at 10 constructors × 4 sites it is ~30 near-
  identical lines that a wildcard `_ ->` arm (bang has none in named-ctor
  matches) would collapse to 4. This is the single biggest line-count and
  edit-fatigue source in the program.
- **No unary-minus literal, ×N sentinels.** Same as the json round: `0 - 1`,
  `0 - n` everywhere a negative is wanted (the lexer's not-found paths, `ENeg`
  eval `0 - v`). `Print.intToStr` handling negatives is `if n < 0 then $concat
  "-" (…(0 - n))`. Fine ×1, noisy ×N.
- **`$(Mod.op)` at every cross-module call site.** `main.bang` calls
  `$(Parser.parseAll)`, `$(Lexer.lex)`, `$(Eval.eval)`, `$(Print.show)` — the
  `$(…)` wrapping is required on each (and, per the fmt finding, must NOT be
  "simplified"). ×2 it is invisible; ×12 the visual noise of `($(Mod.op)) a b c`
  adds up, especially nested (`$(Parser.parseAll) ($(Lexer.lex) src)`).

## What would have helped most (ranked)

1. **A wildcard `_ ->` arm in named-constructor matches.** Would delete ~30 lines
   of boilerplate stop-arms across the parser and make adding a token a 1-site
   edit, not a 4-site one. Highest leverage by far for programs over ~5
   constructors.
2. **Three-engine agreement on the parser (fix the compiled-engine hang, or fuel
   it).** The compiled engine silently diverging from the two references on a
   real program is the correctness item — even non-gating, it violates the
   "proof rides the reference" spirit, and it hangs with no signal.
3. **`bang fmt` preserving `$(Mod.op)`.** A canonical formatter that breaks the
   corpus's largest program the moment you run it is a trap; either preserve the
   parens or emit an equivalent force.
4. **Effect-name parity with `data` in the module surface** (`use Mod (Eff)`,
   `Mod.Eff` in `with … as`, bare name in the defining module's own row).
5. **Mutual `let rec`** (or sibling forward-visibility) — would let recursive
   descent read top-down and might sidestep the compiled-hang shape entirely.
6. **Constructor arity > 2** (or the `≤ 2 (nest tuples)` hint at the USE site,
   not just the decl).
