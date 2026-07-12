# Structurally-refused escape attempts (#134 surface-expressibility experiment)

Attempts that the checker/elaborator REFUSES — evidence bounding the reachable escape surface.
Verdicts machine-cited on the built bang @ fa2572b0, 2026-07-12.

- **cap-in-state** (`put({ logger.emit(5) })` then read+force outside):
  `bang check` → `error: let-binding 'z': type mismatch`. The state cell's type cannot hold an
  effectful thunk that closes over a live cap — the checker refuses. Path CLOSED.

- **return-bare-cap** (`let leak = handle logger with … in $(leak.emit(3))`):
  `bang check` → `error: not a value (wrap a computation in braces)` (TypeCheck.lean:1042). A bare
  `handle … logger` returning the cap value directly is not a value-position term. Path CLOSED.

The REACHABLE escape shape is `let leaked = <handle/state returning a cap-capturing thunk> in
<force outside>` — witnessed by b3.bang (state), c1.bang (custom Log), d2-sched-capture.bang (Sched).
All three: check ok · oracle escapedCap · emit silently returns a value. See cap-gc-rep-design.md §8.1.
