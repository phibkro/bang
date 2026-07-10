# examples-draft — Stage-7 consumer drafts (NOT YET RUNNABLE)

Draft `.bang` programs written against the **ruled** Stage-7 `handle e with Name as h { … }`
grammar (ADR-0095) — which has **not yet landed** on `main` (only the `effect`-decl half is).
They live here, NOT in `examples/`, precisely because they cannot run yet: no
`lake exe bang run` will parse `handle e with Choice as sched { … }` until the Stage-7 surface
lands.

Design note: `docs/notes/ndet-dst-design.md` (lane ndet, task #28 — nondeterminism-as-effect +
the DST handler + the sim-KV hello-world; the first real consumer of the Stage-7 surface).

## The drafts

| dir | what it shows | v1 status |
|---|---|---|
| `choice-min/` | `Choice` as an ordinary effect; the trivial deterministic scheduler | **zero-gap** — runs the instant Stage-7 lands |
| `choice-two/` | two picks; the interleaving is handler-chosen (swap the clause ⇒ different output) | **zero-gap** — the handler-swap demo in miniature |
| `sim-kv/` | the replicated-KV skeleton: seeded stateless scheduler + externalized world | **straddles the wall** — the scheduler clause is a compute-then-return body (ADR-0095 D4 / gap G1); stays a draft until binop typing (ADR-0065) + grade surfacing (Q27) land |

## When the surface lands

Follow `docs/notes/ndet-dst-design.md` §8: move `choice-min` and `choice-two` into `examples/`,
run them, assert the ACTUAL outputs, report. `sim-kv` stays here until gap G1 (D4) lifts.
