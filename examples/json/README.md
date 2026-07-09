# json

A **JSON value-subset parser + printer written in bang** — null/bool/int/string/
array/object, recursive-descent, hand-rolled without a modules system (single
file). Exercises `let rec` structural and non-structural recursion (ADR-0091
`structOK` multi-arg descent, ADR-0088 declared-row effectful recursion),
strings as `List Char` (ADR-0074), and user `data` with mixed-arity constructors.

## What it does

`Json` is ONE self-recursive `data` declaration (no mutual `data`, since bang
has none — see the findings note): `JNull | JBool(Int) | JInt(Int) | JStr(Str)
| JArr(Json) | JObj(Json) | JCons(Json, Json) | JNilL | JField(Str, Json)`.
Arrays and objects are both encoded as `JCons`/`JNilL` linked lists threaded
through the SAME type — `JArr(list-of-values)`, `JObj(list-of-JField)`.

`parseValue : Str -> Option (Json * Str) ! {Div}` is a single recursive-descent
function (bang has no mutual `let rec`, so array/object/string sub-parsers are
nested `let rec`s inside `parseValue`'s body, closing over the outer name for
recursive calls into nested values). `printJson : Json -> Str ! {Div}` is the
inverse, structured the same way.

`main.bang` parses a flat array, a flat object, and an array containing both a
nested array and a nested object — verifying constructor tags via `tagOf`/
`tagAt` — then separately prints a hand-built `Json` value and checks the
output against the expected canonical string.

```
lake exe bang run examples/json/main.bang              # -> 163 (kernel oracle)
lake exe bang run --compiled examples/json/main.bang    # -> 163 (verified machine, agrees)
```

## A critical finding this example surfaced

Composing `parseValue`'s output into `printJson` (or making enough sequential
calls into these Div-declared, multiply-nested `let rec` closures within one
program) causes **non-termination** past a size/call-count threshold that is
much lower than would be expected from the 100000-fuel budget — both the
kernel oracle and the compiled machine hang identically. `main.bang` is
scoped conservatively (3 `parseTop` calls, `printJson` called once on a
hand-built value, never composed with a parser-produced value) to stay under
that threshold; see `docs/notes/dogfood-json-findings.md` for the full
isolation (minimal repro: parse a 2-field object, then `printJson` it — 2
lines, hangs both engines).

## What's NOT covered (module-system gap)

The parser/printer/data-decl live in one file because bang has no import/
module system yet (ADR-0076 pins the future architecture). A real project
would want `Json` + `parse` + `print` in separate files, importable by a
consumer — see the findings note for the concrete shape this gap takes here.
