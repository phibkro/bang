# gen-seed-b

Half of the **Gen handler-swap pair** (with [`gen-seed-a`](../gen-seed-a/)) — the IDENTICAL
generator program (three `sched.pick(6)` performs summed), run under a DIFFERENT seed. This
handler is SEED B: `pick(n) => 5` always returns `5`, so the run is `5+5+5 = 15` — a different
deterministic sequence of choices from `gen-seed-a`'s `6`, produced by swapping only the `with`
clause. This is the DST/QuickCheck thesis in miniature (`docs/notes/ndet-dst-design.md` §2):
nondeterminism is an ordinary effect, a "seed" is just which handler value is installed, and
"generate a different run" means "install a different handler" — no language feature, no kernel
change, the SAME program driven by two different scheduler values.

```
lake exe bang run examples/gen-seed-b/main.bang    # 5 + 5 + 5 -> 15
```
