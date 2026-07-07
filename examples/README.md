# examples — bang programs (the run oracle)

Real bang programs, each in its own directory, gated end-to-end by
`tools/check-examples.sh` (run every `main.bang`, diff stdout against
`expected.txt`). This is the run-oracle for whole programs — it supersedes the
per-example hand-written `#guard`s. Wired into `just verify` via
`just check-examples`.

```
examples/<project>/
  main.bang        the program (ONE file — no import system yet)
  expected.txt     the expected `bang run main.bang` stdout (the oracle)
  README.md        what it is · what it demonstrates · how to run
```

| project | demonstrates | output |
|---|---|---|
| [parser-combinators](parser-combinators/) | **the polymorphism milestone** — higher-order combinators (ADR-0075) + generic data (ADR-0079) compose into a real `Parser` library | 25 |
| [tokenizer](tokenizer/)         | a tokenizer written in bang; structural recursion + strings + user `data` | 3 |
| [string-stdlib](string-stdlib/) | the injected `concat`/`reverse`/`eq` string stdlib | 1 |
| [state](state/)                 | the State effect as a library handler | 5 |
| [stm](stm/)                     | STM/TVars as a transactional handler (ADR-0030) | 70 |
| [handle](handle/)               | an effect handler catching `raise` | 7 |

## Running

```
nix develop                                       # dev shell (lake on PATH)
lake exe bang run examples/<project>/main.bang    # run one
just check-examples                               # gate them all
```

All six run cleanly as `bang run` (type-check → lower → eval). The default
pipeline type-checks first, so an ill-typed program is a type error before it
runs (ADR-0076).

## Notes / limitations

bang has **no comment syntax** and **no import system** yet, so each program is a
single comment-free `.bang` file; shared explanation lives in these READMEs. The
parser-combinators README documents the annotation-driven-generic-data wall that
keeps its combinators monomorphic-in-result-type (the next PATH-polymorphism bite).
