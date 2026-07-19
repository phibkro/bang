# C2 exact-live-stack edge witnesses (#134 — the flagged subtle spots)

These two control-flow spots constrain the exact `$liveCaps` stack:

- **nested1.bang** — nested state, OUTER cap used AFTER inner pops:
  `state 100 in (let a = state 5 in get in let b = get in a+b)` ⇒ **105** (inner 5 +
  outer 100). Confirms `$capExit(inner)` removes the inner node while the outer id remains
  an exact member. This is also the positive legal-program control in `emit-escape-diff.sh`.

- **abort/unwind** (examples/handle-custom-abort-coexist, ⇒ 42): a `raise 42` unwinds
  PAST a nested custom handler (whose $capExit is skipped on the throw), caught outside.
  ⇒ 42 oracle == emit. The skipped inner exit is why `$capExit(m)` must pop THROUGH `m`,
  discarding `m` and all newer nodes. Strict-pop would trap on the enclosing exit; merely
  leaving the inner node would revive stale capabilities.
