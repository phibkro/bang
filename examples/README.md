# examples — bang programs (the run oracle)

Real bang programs, each in its own directory, gated end-to-end by
`tools/check-examples.sh` (run every `main.bang`, diff stdout against
`expected.txt`). This is the run-oracle for whole programs — it supersedes the
per-example hand-written `#guard`s. Wired into `just verify` via
`just check-examples`.

```
examples/<project>/
  main.bang        the program (a single entry file; a multi-file project — see json/ —
                    additionally has its own imported `.bang` modules alongside main.bang)
  expected.txt     the expected `bang run main.bang` stdout (the oracle)
  README.md        what it is · what it demonstrates · how to run
```

| project | demonstrates | output |
|---|---|---|
| [parser-combinators](parser-combinators/) | **the polymorphism milestone** — higher-order combinators (ADR-0075) + generic data (ADR-0079) compose into a real `Parser` library | 35 |
| [tokenizer](tokenizer/)         | a tokenizer written in bang; structural recursion + strings + user `data` | 3 |
| [string-stdlib](string-stdlib/) | the injected `concat`/`reverse`/`eq` string stdlib | 1 |
| [state](state/)                 | the State effect as a library handler | 5 |
| [stm](stm/)                     | STM/TVars as a transactional handler (ADR-0030) | 70 |
| [handle](handle/)               | an effect handler catching `raise` | 7 |
| [effect-op-arith](effect-op-arith/) | arithmetic composing with effect operations in one line (issue #26) | 70 |
| [caesar](caesar/)               | an encode/decode/round-trip cipher, originally authored by the round-1 stranger-test agent | see README |
| [json](json/)                   | **the first multi-file project** — a JSON parser + printer split across FOUR files, dogfooding the ADR-0093 module system (`import`/`use`/`pub`, qualified access) | 163 |
| [handle-custom-tracer](handle-custom-tracer/) | ADR-0095 D1's own worked example — declare + perform + handle a user `effect` end to end | 30 |
| [handle-custom-resume](handle-custom-resume/) | a parameter-carrying custom handler, one-shot resume with a continuation after it | 106 |
| [handle-custom-abort-coexist](handle-custom-abort-coexist/) | `raise` aborts PAST a custom handler frame straight to the outer `throws` | 42 |
| [logger-silent](logger-silent/) / [logger-counting](logger-counting/) | **handler-swap pair 1** — a `Log` effect; one handler discards every message, the other tallies the call count via the return path | 0 / 3 |
| [fail-parser-strict](fail-parser-strict/) / [fail-parser-default](fail-parser-default/) | **handler-swap pair 2** — a `Try` effect guarding a chooser; `raise` aborts past the custom frame with either the raw failure code or a safe fallback | 999 / 0 |
| [gen-seed-a](gen-seed-a/) / [gen-seed-b](gen-seed-b/) | **handler-swap pair 3** — generation-as-effect (`Choice.pick`); two seeded handlers produce two deterministic, replayable runs of the same program | 6 / 15 |

## Running

```
nix develop                                       # dev shell (lake on PATH)
lake exe bang run examples/<project>/main.bang    # run one
just check-examples                               # gate them all
```

Every project runs cleanly as `bang run` (type-check → lower → eval). The default
pipeline type-checks first, so an ill-typed program is a type error before it
runs (ADR-0076).

## Notes / limitations

bang HAS a line-comment syntax (`--` to end-of-line) and a module system (ADR-0093:
`import`/`use`/`pub`, one file per module) — see `docs/reference/language.md`'s Lexical
notes and Modules sections for the full grammar. `json/` is the one multi-file example;
every other project here is still a single comment-free `.bang` file (comments are
stripped before parsing regardless, so they carry no meaning to `check`/`run` — see the
reference's Lexical notes for why `bang fmt` doesn't preserve them). The
parser-combinators README documents the annotation-driven-generic-data wall that
keeps its combinators monomorphic-in-result-type (the next PATH-polymorphism bite).
