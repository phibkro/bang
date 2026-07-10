# choice-min (DRAFT — not yet runnable)

`Choice` as an **ordinary user effect** — the invariant-#5 showcase. `effect Choice { pick : Int
-> Int }` declares a one-op nondeterminism effect; `handle … with Choice as sched { pick(n) => ret
0 }` installs the *trivial deterministic scheduler* (always choose 0). The kernel never learns
`Choice` exists — nondeterminism is a value, not a language feature.

Zero-gap against v1: `ret 0` is ret-shape (ADR-0095 D4), implicit tail-resume (D5), one curried arg
(D3), `as sched` binder present (D1a). Runs the instant Stage-7 lands.

```
# once Stage-7 handle-with lands:
lake exe bang run examples/choice-min/main.bang    # pick(10) resolved by the always-0 scheduler -> 0
```

Design note: `docs/notes/ndet-dst-design.md` §4.2.
