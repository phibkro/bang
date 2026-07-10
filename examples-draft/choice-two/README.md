# choice-two (DRAFT — not yet runnable)

Two picks, one handler — the **handler-swap demo in miniature**. Each `sched.pick(2)` is a
nondeterministic coin ("which message delivers first", "deliver-or-drop"); the installed handler
resolves both. `a + b` is a stand-in observable outcome of the interleaving.

The point: swap the clause body `ret 1` → `ret 0` and the SAME program yields `0` instead of `2`.
Same program, different runtime (the installed handler), different outcome — "paradigm is a value;
runtime is a handler installed at the use site" (ADR-0016) on the distributed axis.

The limitation it exposes (deliberately): a **constant** clause makes both picks identical (both
1). A real seeded scheduler needs the coin to depend on seed+step — the stateless seed-splitting
design (ndet note §5.1), whose compute-then-return clause hits ADR-0095 D4 (gap G1).

Zero-gap against v1: both clauses are ret-shape constants.

```
# once Stage-7 handle-with lands:
lake exe bang run examples/choice-two/main.bang    # 1 + 1 -> 2   (swap to ret 0 -> 0)
```

Design note: `docs/notes/ndet-dst-design.md` §4.3.
