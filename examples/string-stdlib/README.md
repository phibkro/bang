# string-stdlib

Uses the **injected string stdlib** — `concat`, `reverse`, `eq` are `let rec`
folds in scope of every program (#49 stage 3), so a program uses them without
re-inlining (the #50 gap the tokenizer hit). Strings are `List Char` (ADR-0074).

The program checks `reverse "dcba" == concat "ab" "cd"` — both are `"abcd"`, so
`eq` returns true and the `if` yields 1.

```
lake exe bang run examples/string-stdlib/main.bang    # -> 1
```
