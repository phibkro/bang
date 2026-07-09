# json

A **JSON value-subset parser + printer written in bang, split across FOUR files**
(`Json.bang` / `Parse.bang` / `Print.bang` / `main.bang`) — the FIRST multi-file
example project, dogfooding ADR-0093's module system (`import`/`use`/`pub`,
private-by-default visibility). Exercises `let rec` structural and non-structural
recursion (ADR-0091 `structOK` multi-arg descent, ADR-0088 declared-row effectful
recursion), strings as `List Char` (ADR-0074), user `data` with mixed-arity
constructors, and now the module system itself (top-level `let`/`let rec` decls,
ADR-0093 D5's operator ruling — every export here is a `pub let`/`pub let rec`).

## The split

- **`Json.bang`** — `pub data Json = JNull | JBool(Int) | JInt(Int) | JStr(Str) |
  JArr(Json) | JObj(Json) | JCons(Json, Json) | JNilL | JField(Str, Json)`. ONE
  self-recursive `data` declaration (no mutual `data`, since bang has none — see
  the findings note); arrays and objects are both `JCons`/`JNilL` linked lists
  threaded through the SAME type — `JArr(list-of-values)`, `JObj(list-of-JField)`.
- **`Parse.bang`** — `import Json`; `pub let rec parseValue : Str -> Option
  (Json_Json * Str) ! {Div}`, the recursive-descent parser (array/object/string
  sub-parsers are nested `let rec`s inside `parseValue`'s body, closing over the
  outer name — bang has no mutual `let rec`), plus its `pub let` helpers
  (`isDigit`/`isWs`/`dropWs`/`litMatch`/`parseTop`).
  Its `data`-ctor and value references to `Json`'s constructors read `Json.JNull`
  (bare-import qualified access, rewritten to `Json_JNull` at merge time); its
  TYPE ascriptions spell the qualified name directly (`Json_Json` — `pTy` has no
  dot syntax, so a bare-`import`ed type name must be written qualified by hand).
- **`Print.bang`** — `import Json`; `pub let rec printJson : Json_Json -> Str !
  {Div}` + `pub let rec intToStr`, the inverse of `parseValue`, structured the
  same way.
- **`main.bang`** — `import Json`/`Parse`/`Print`; a plain `let main = …` (D5:
  no special entry-point syntax, `main` is just a `let` decl like any other) that
  calls `$(Parse.parseTop)`/`$(Print.printJson)` (the `$(mod.op) arg` calling
  convention for a bare-imported function — `$mod.op arg` does NOT parse the way
  you'd expect, since `$` forces only an ATOM and `mod.op` isn't one), parses a
  flat array, a flat object, and a nested array/object — verifying constructor
  tags via `tagOf`/`tagAt` — then separately prints a hand-built `Json` value and
  checks the output against the expected canonical string.

```
lake exe bang run examples/json/main.bang              # -> 163 (kernel oracle)
lake exe bang run --compiled examples/json/main.bang    # -> 163 (verified machine, agrees)
```

`bang check` (unlike `bang run`) does NOT resolve imports — it is a single-file
diagnostic pipeline, so it cannot type-check `main.bang`/`Parse.bang`/`Print.bang`
standalone (each references names their own `import` lines bring in). `Json.bang`
(the one pure-`data`, import-free file) is the exception and checks clean alone.

## A critical finding this example surfaced (module-adjacent)

Composing `parseValue`'s output into `printJson` (or making enough sequential
calls into these Div-declared, multiply-nested `let rec` closures within one
program) causes **non-termination** past a size/call-count threshold that is
much lower than would be expected from the 100000-fuel budget — both the
kernel oracle and the compiled machine hang identically. `main.bang` is
scoped conservatively (3 `parseTop` calls, `printJson` called once on a
hand-built value, never composed with a parser-produced value) to stay under
that threshold; see `docs/notes/dogfood-json-findings.md` for the full
isolation (minimal repro: parse a 2-field object, then `printJson` it — 2
lines, hangs both engines). This is orthogonal to the module split (it hangs
identically whether the code lives in one file or four) and remains a
separate, tracked issue (#61).
