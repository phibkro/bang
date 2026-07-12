# C2 watermark edge witnesses (#134 — the flagged subtle spots)

The manager flagged two off-by-one-prone spots for the $liveTop stamp. Both verified
oracle == emit on wasmtime 45 (feat-cap-gc-rep @ 7355a803):

- **nested1.bang** — nested state, OUTER cap used AFTER inner pops:
  `state 100 in (let a = state 5 in get in let b = get in a+b)` ⇒ **105** (inner 5 +
  outer 100). Confirms $capExit restores $liveTop so the outer cap (id 0) stays live
  (0 < liveTop 1) after the inner (id 1) popped — the nested-restore off-by-one.

- **abort/unwind** (examples/handle-custom-abort-coexist, ⇒ 42): a `raise 42` unwinds
  PAST a nested custom handler (whose $capExit is skipped on the throw), caught outside.
  ⇒ 42 oracle == emit. Confirms the unwind-skips-$capExit case is safe: too-high
  $liveTop is the SAFE direction (more caps look live ⇒ never a wrong-trap on a legit
  cap). The rung-3 explicit-restore finding is the precedent (wasm unwinds free, the
  restore is the delicate part).
