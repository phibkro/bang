# handle-custom-abort-coexist

Ported from the Stage-2 kernel's `customAbortCoexist` `#guard` (`Bang/Core/Semantics/Eval.lean`)
to SOURCE TEXT — a custom handler frame sitting BETWEEN a `raise` and its `throws` handler. The
`raise 42` aborts PAST the custom `Net` frame entirely (the read continuation, `net.fetch(5)`,
never runs) straight to the outer AMBIENT `throws` install. Proves real custom-handler dispatch
does not break the zero-shot abort of a coexisting built-in.

```
lake exe bang run examples/handle-custom-abort-coexist/main.bang    # raise 42 aborts -> 42
```
