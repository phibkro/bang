# tokenizer

A whitespace tokenizer **written in bang** — "bang writes its own tools" (#49
stage 5). `tokenize : Str -> TokList` structurally recurses over the char-list,
splitting on spaces (code point 32) and building tokens right-to-left; `tokCount`
counts them. All `let rec` folds over `data` + strings — no kernel primitive.

Demonstrates: structural recursion certified TOTAL (ADR-0073 #47), strings as
`List Char` (ADR-0074), user `data` types.

```
lake exe bang run examples/tokenizer/main.bang    # "ab cd ef" -> 3
```

Note: a hand-written `#guard` for the same program lives in
`Bang/Frontend/TypeCheck.lean` (validation ⑨i). This run-oracle supersedes it for
gating; the guard is left in place (harmless, and it exercises the checker path).
