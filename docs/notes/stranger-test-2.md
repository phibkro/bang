<!-- note-status: active -->
# Stranger test — round 2 (2026-07-10)

> Second outer-loop probe, post-ergonomics-batch (main @ fe67026). Same repeatable method as
> round 1 (`docs/notes/stranger-test-1.md`): a zero-prior agent, roleplay-strict — README →
> install → **generated reference** (`docs/reference/language.md`) → `examples/` → CLI output
> ONLY; NO `Bang/*.lean`, `CLAUDE.md`, `CONTEXT.md`, `docs/notes/`, `docs/decisions/`. Where the
> surface fails, that failure IS the finding. Round 2 adds the NEW surface: **modules**
> (`import`/`use`/`pub`), **multi-binding `let`**, **`bang test` on a law-carrying program**, and
> **`bang check --json` in an agent loop** — while re-scoring the round-1 journey rubric.

## Verdict

**7/10 ship-ability.** The *language-expression* surface (multi-binding `let`, `--` comments,
unary minus, strings/chars, arithmetic, `fmt`, the two-engine `--compiled ≡ kernel` agreement,
and the **runtime-terminal error messages**) is excellent — every documented edge case behaved
exactly as written, including the tricky `3--10` maximal-munch trap and unary-minus precedence.

**The score dropped 1.5 from round-1's 8.5 because the two headline NEW features are
under-surfaced or under-enforced:** (1) the **module system is entirely undocumented in the
generated reference** — a stranger's only source is one example's README; (2) **`pub` /
private-by-default visibility is not enforced at all** (a non-`pub` binding is freely importable),
so the README's central module claim is false against the binary; (3) **`bang test` cannot be
exercised from the outside** — `trait`/`law`/`impl` has zero documented syntax, and my
parser-guided reconstruction never got a single law to PASS (every law run errors with `app:
callee is not a function`), so the counterexample/shrinking journey was unreachable.

**The caveat that dominates round 2: a stale prebuilt binary lies.** The binary present at
`.lake/build/bin/bang` predated the ergonomics batch; run against it, `--help` exits 1 and
`--version` prints no version — i.e. it shows the round-1 bugs as *unfixed*. Rebuilding from the
committed `fe67026` source (`nix develop -c lake build bang`, ~2 min warm) shows them **fixed**.
All findings below are against the **freshly-built fe67026 binary** (the committed content), not
the stale artifact. See papercut #1.

## The one doc change (the round's headline)

**The module system (`import` / `use` / `pub` / qualified `Mod.name` / the `Mod_Type`
type-name hand-qualification / the `$(Mod.op) arg` calling convention) has NO entry in the
generated reference** (`docs/reference/language.md`). The only occurrences of "import" in the
reference are incidental ("no import needed" for the stdlib). Every module fact a stranger needs
was reverse-engineered from `examples/json/README.md` + the four json source files. `use` in
particular appears in **zero** `.bang` source and zero reference text — only the json README's
prose triad `import`/`use`/`pub` names it, and every stranger-plausible `use …` syntax fails to
parse (`error: parse error: expected '(', got …`), so `use` is undiscoverable AND unusable from
the surface. Fix = a **Modules section IN the generated reference** (the `import` directive, the
`pub` marker, qualified access, the `$(mod.op)` convention, and `use` — or the removal of `use`
from the advertised triad if it isn't wired). This is the round-2 analog of round-1's
"Strings & Characters" gap: the feature works (for `import`), but the reference doesn't teach it.

## Stumbles + papercuts (ranked)

Severity: **S1** ships-broken/false-doc · **S2** blocks a documented journey from the outside ·
**S3** friction/regression · **S4** cosmetic.

1. **[S1] `pub` / private-by-default visibility is NOT enforced.** `examples/json/README.md`
   advertises "private-by-default visibility", but a non-`pub` binding is fully importable and
   callable from another file:
   ```
   # Bare.bang:  let plain = {fun x => x + 1}     -- no `pub`
   # main.bang:  import Bare
   #             let main = $(Bare.plain) 41
   $ bang run main.bang   ⟹ 42   exit 0    (private binding reachable)
   ```
   Same for an explicitly-private helper accessed by qualified OR merged-underscore name
   (`$(Math.secret)` and `$(Math_secret)` both resolve). `pub` is currently a no-op for
   visibility. **Consequence for the brief:** the "deliberate visibility mistake → judge the
   error" sub-journey produces NO error, because the mistake isn't one. Smallest outside-view
   fix: either enforce the gate (an importer referencing a non-`pub` name is an
   `unbound`/`private` error) or, if enforcement is deferred, stop advertising
   "private-by-default" in the example README until it's real.

2. **[S2] `bang test` is unreachable from the surface — `trait`/`law`/`impl` is undocumented,
   and my best reconstruction never PASSES a law.** No `trait`/`law`/`impl` appears in the
   reference (one incidental `Self` row) or in any example source/README. Reverse-engineering
   purely from parser error messages (which ARE helpful — see "What worked") I recovered the
   grammar: trait body = `fn name(args) -> T` | `law name(vars) : expr` | `name : T`; impl =
   `impl Trait for Type { fn name(args) = body }`. But every law I could get *discovered* then
   **errors at run**:
   ```
   trait Eq { fn eq(a, b) -> Int   law refl(x) : eq(x, x) == 1 }
   impl Eq for Int { fn eq(a, b) = if a == b then 1 else 0 }
   $ bang test  ⟹  ✗ Eq.refl — ERROR — app: callee is not a function ('eq')
                    laws: 0/1 passed
   ```
   Even a trait-op-free law body (`law selfeq(x) : x == x`) fails identically
   (`app: callee is not a function`), so the failure is in how `bang test` *invokes* the law, not
   in my body. I never reached a PASS, a FAIL, or a counterexample/shrink display — so the
   Journey-4 "break the law, judge the shrinking" step could not run. Note `--help` promises
   "sample-check … reports per-law PASS/FAIL/ERROR/STUCK" — the result vocabulary exists; the
   evaluation path for a stranger-authored law does not reach it. Smallest outside fix: a **worked
   trait+law example project under `examples/`** (build-gated like the others) that `bang test`
   passes — this both documents the syntax and proves the feature end-to-end.

3. **[S3] `bang check --json` type-mismatch errors carry no span; file-input parse errors lose
   their span AND get mislabeled `code:"type"`.** Round-1 praised `check --json`'s "exact span"
   as what turned a stumble into a 15-second fix. The span still works for **stdin + parse/unbound**
   errors, but is absent for the common **type-mismatch** case, and the **file path** drops it:
   ```
   input×kind (check --json)      span            code
   stdin,  parse error            {line,col} ✓    "parse" ✓
   stdin,  unbound var            {line,col} ✓    "type"
   stdin,  type mismatch          null       ✗    "type"
   FILE,   parse error            null       ✗    "type"  ← mislabeled + span lost
   FILE,   type mismatch          null       ✗    "type"
   ```
   The span *exists in the pipeline* (human `eval`/`check` prints `error at 1:13:` for the same
   parse error) — `--json` + file just doesn't surface it. Also the type-mismatch message is bare
   `"type mismatch"` (no expected/actual), weaker than the round-1 experience. The binding-name
   prefix (`let-binding 'c': …`) partially compensates as a locator. Smallest fix: thread the span
   into the type-mismatch diagnostic and keep `code:"parse"` on the file path.

4. **[S3] `examples/README.md` is stale: "no import system yet" / "ONE file — no import system
   yet" contradicts `examples/json/` (four files, an import system).** Also `examples/json/README.md`
   says "**`bang check` … does NOT resolve imports**", but the running binary (and `--help`)
   resolve imports for `check` — `bang check --json examples/json/main.bang ⟹ {"ok":true}`. Two
   product docs disagree with the binary and with `--help`. Smallest fix: regen/patch
   `examples/README.md` to name the json multi-file project and drop the "no import system"
   sentence; reconcile the json README's `check`-doesn't-resolve claim with the shipped behavior.

5. **[S3] Trait/law surface is internally inconsistent between curried and paren-call forms.**
   The rest of the language is curried (`fun x => …`, `$f x`, trait op typed `-> A -> B`), but a
   trait op is *declared* `fn eq(a, b) -> Int` and *implemented* `fn eq(a, b) = …` with a
   tuple-style parameter list, and a law body must call `eq(x, x)` not `eq x x`. A `name : T`
   sig with an arrow type (`eq : Self -> Self -> Int`) is read as arity-0 (`impl has 2 params,
   the trait declares 0`), so the two op-declaration forms don't agree on arity. From the
   outside this reads as two different function conventions in one language.

6. **[S4] `bang test` has no `--json` mode** (`bang test --json file` reads `--json` as a
   filename → "could not read file '--json'", exit 1). Round-1's agent-loop win was `check --json`;
   the law-checker has no structured-output counterpart, so an agent can't consume law results
   programmatically.

7. **[S4] Bare `bang` (no subcommand) exits 1** printing usage. Defensible (no command = usage
   error), but `--help`/`--version` correctly exit 0 now, so a bare invoke exiting 1 is a mild
   inconsistency for a smoke check. Low priority.

## What worked (preserve these properties)

- **Every documented language-expression edge case behaved exactly as written.** `3--10 ⟹ 3`
  (comment maximal-munch), `3 - -10 ⟹ 13`, `-x + 1 ⟹ -4` (unary-minus precedence), multi-binding
  `let x = …; y = … in` sequential-not-recursive, string `match SNil/SCons(Char(n),_)`. The
  reference's documentation of these traps is accurate and load-bearing — I hit none of them by
  surprise.
- **Runtime-terminal error messages are outstanding and actionable.** Fuel names the ceiling
  (100000), the likely cause, and distinguishes divergence from the #61 cost-cliff. Escaped-cap
  (exit 3) names the exact mechanism (forced after the block returned), cites the design decision,
  says defined-not-corruption, and gives two concrete fixes. The library-file message ("no `main`
  decl … import it from an entry file instead") is a genuinely helpful redirect.
- **Parser error messages double as a teaching tool.** With zero trait docs, messages like
  `expected 'fn', 'law', a 'name :' signature, or '}' in a trait body` and `impl … expected 'for'`
  let me reconstruct most of the trait/impl grammar by iteration. This is a real strength — the
  parser is self-documenting even where the reference isn't.
- **`--compiled ≡ kernel` holds on my own programs, including multi-file** (sum-of-squares 25/25,
  my 2-file module program 30/30). The two-engine agreement round-1 praised survives the modules
  work.
- **`bang fmt` is clean, idempotent, and value-preserving**; multi-binding `let` correctly expands
  to the fully-nested chain, exactly as documented. **Comment-stripping is documented discoverably**
  in the reference (§Lexical notes + §Grammar) — round-1's concern (is the strip behavior
  *documented*?) is addressed.
- **The ~90 build-gated `#guard` reference examples were trusted completely and never burned** —
  the docs' superpower (drift-is-a-failing-diff) is intact.

## Comparison vs round-1

| round-1 finding | round-2 status |
|---|---|
| `bang --help` exits 1 (papercut #1) | **FIXED** (exit 0) — but a *stale prebuilt binary* still shows exit 1; rebuild required (papercut #1 below) |
| `--version` (implied by #67) | **FIXED** — `bang 0.1.0-dev`, exit 0 |
| strings/chars absent from reference (the headline) | **FIXED** — "Strings & Characters" section present, ~15 gated examples |
| no line comments | **FIXED** — `--` to EOL, works; maximal-munch traps documented + accurate |
| attribution-comment parse failure (caesar) | **FIXED** — trailing `-- …` parses |
| `intToStr` looks-stdlib but example-local (papercut #2) | **RESOLVED/moot** — no longer ambient; it's a `pub let rec` in `Print.bang`; stdlib table has the "these three only" callout (concat/reverse/eq) |
| GAP D — multi-arg `! {Div}` ceremony overstated | not re-tested (round-2 scope was modules/laws) |
| **`bang check --json` exact-span (the praised property)** | **PARTIAL REGRESSION** — span gone for type-mismatch; file-input parse errors lose span + mislabel `code:"type"` (papercut #3) |
| **module system** | **NEW** — works for `import`, but undocumented in reference + `pub` unenforced + `use` unusable (papercuts #1, #2-doc, #4) |
| **`bang test` / trait laws** | **NEW** — CLI exists; feature unreachable from the surface (papercut #2) |
| **examples/README "no import system yet"** | **NEW (regression)** — stale vs the json multi-file example (papercut #4) |

## Score breakdown (/10)

| dimension | round-1 | round-2 | note |
|---|---|---|---|
| install / orient | 1.0 | 1.0 | README build path clean; `--help`/`--version` fixed (fresh binary) |
| language-expression surface | 2.0 | 2.0 | multi-binding let, comments, unary minus, strings — all exact |
| modules journey | — | 0.5 | `import` works; undocumented + `pub` unenforced + `use` broken |
| laws journey (`bang test`) | — | 0.5 | CLI + parser hints exist; no law reachable to PASS from outside |
| error actionability | 1.5 | 1.5 | runtime terminals outstanding; type-mismatch span/detail thin |
| agent loop (`check --json`) | 1.5 | 1.0 | works for stdin/parse; type-mismatch + file spans lost |
| fmt / conformance / docs-trust | 1.0 | 1.0 | idempotent, value-preserving, gated examples trusted |
| **total** | **8.5** | **7.0** | |

## Method note (repeatable)

Same protocol as round 1 (roleplay-strict + forbidden-files + verbatim-stumbles +
"one doc change"), with two round-2 additions worth keeping:

1. **Gate the committed content, not the artifact.** The prebuilt `.lake/build/bin/bang` was
   stale (pre-ergonomics-batch) and would have produced *four false regressions* (`--help` exit 1,
   no `--version`, etc.). Checking the binary's mtime against the relevant commit times, then
   rebuilding from the base sha, is the difference between testing the code and testing a lie.
   A future stranger test should **always rebuild from the base sha first** (or verify the
   artifact's provenance) — the same gate-the-clean-sha discipline the proofs use.
2. **The parser's error messages are a discovery instrument.** Where the reference is silent
   (traits/laws/modules), iterating on `parse error: expected X` reconstructs most of the grammar.
   This is a testable surface property in its own right — a good target to preserve as the language
   grows undocumented corners.

Round-2 template programs (all original, not example copies): a char-classifier (multi-binding
let + unary minus + string match), a 2-file `Math`/`main` module, a `sum-of-squares` fmt subject,
and the trait/law reconstruction battery. Re-run at each ◊; the modules + laws surface is the
part most likely to move.
