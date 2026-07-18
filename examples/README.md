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
| [ndet-sim-kv-a](ndet-sim-kv-a/) / [ndet-sim-kv-b](ndet-sim-kv-b/) | **the R1 DST warm-up** — a `Choice`-driven replica race resolved by last-writer-wins, two seeded handlers converging to different values (`docs/notes/ndet-dst-design.md`) | 1120 / 1100 |
| [ndet-replicated-kv-a](ndet-replicated-kv-a/) / [ndet-replicated-kv-b](ndet-replicated-kv-b/) | **the R2 replicated-KV hello-world** — two replicas, three totally-stamped writes, a genuine order-free LWW `merge` fold; both seeds converge to the SAME final state while their schedule-dependent trace legitimately differs (the CALM claim in miniature, `docs/notes/distributed-story.md` §5) | 1700 / 1900 |
| [ndet-repkv-fail-a](ndet-repkv-fail-a/) / [ndet-repkv-fail-b](ndet-repkv-fail-b/) | **R2b failure injection** — per-write delivery as another `Choice` consult; seed B drops a write, replicas VISIBLY diverge pre-merge and the anti-entropy fold re-converges them (eventual consistency made observable) | 113603 / 103602 |
| [handle-custom-nested](handle-custom-nested/) | **identity dispatch pinned e2e** — two active handlers of ONE effect; the outer cap dispatches past the nearer same-label handler (`210`, where nearest-label would give `30` — ADR-0055) | 210 |
| [echo-mock](echo-mock/) | **ADR-0084 slice A** — a `Net { recv, send }` effect echoed by a PURE mock handler; IO-as-paradigm, swappable for a real handler with zero body changes | 3085 |
| [hostio-echo](hostio-echo/) | **ADR-0104 host-IO wedge** — imports the bundled `std/Io.bang` (`Console` print/readLine); the corpus run installs the SIM handler (deterministic, verified-core); the real+record+replay path is exercised by `tools/test-hostio-seam.sh`, not the corpus | ih |
| [calc](calc/) | **the dogfood program** — a 6-module lexer→parser→evaluator (297 lines): modules, stdlib, recursion, a structural `Trace` effect; found #95/#96/#97 (`docs/notes/dogfood-calc-findings.md`) | 11021193 |
| [nqueens](nqueens/) | **the pure-fragment stress test** — N-queens 4/5/6 fused into one self-recursion (no mutual `let rec` in v1); also the live env-vs-oracle fuel-cliff benchmark (#61) | 21004 |
| [dst-rounds-lcg](dst-rounds-lcg/) / [dst-rounds-const](dst-rounds-const/) | **handler-swap pair 4 (DST rounds)** — a RECURSIVE driver with a declared user-effect row (`! {Div, Sched}`) performing through a captured cap; this historical baseline threads the seed through the driver and contrasts with ADR-0114's later explicit updating clauses | 9 / 16 |
| [wildcard-match](wildcard-match/) | **the `_` wildcard match arm (issue #101)** — one shared body covers every constructor not named explicitly (including one WITH payload); expands to concrete arms before elaboration, so the kernel-facing eliminator (ADR-0069) is unchanged | 2 |
| [pledged-plugin](pledged-plugin/) | **row attenuation as a type boundary** — `pledge {Audit} in …` admits an audited plugin while statically rejecting any extra `Secret` effect (ADR-0112) | 1 |
| [policy-host-allowlist](policy-host-allowlist/) | **value-level resource policy at the handler boundary** — one pledged `{Net}` plugin runs unchanged under two runtime host allowlists carried by an ordinary handler parameter | 1001 |
| [stateful-quota](stateful-quota/) | **handler-owned evolving policy (ADR-0114)** — one stable capability is called twice while an `update` clause atomically advances its private quota parameter | 10 |

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
