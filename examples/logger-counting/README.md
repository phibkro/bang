# logger-counting

Half of the **Logger handler-swap pair** (with [`logger-silent`](../logger-silent/)) — the
IDENTICAL program, `(logger.log(10)) + (logger.log(20)) + (logger.log(30))`, run under a
different `Log` handler. This handler COUNTS: `log(msg) => 1` returns one per call, so the sum
of the three performs' return values (`1 + 1 + 1 = 3`) IS the call count — v1 has no mutable
handler state (ADR-0092 D5 defers param-update), so counting rides the return path, not a
counter register. Swapping only the `with` clause between this project and `logger-silent`
turns every `log` from a no-op into a tally: the handler, not the program, decides what logging
means.

```
lake exe bang run examples/logger-counting/main.bang    # 1 + 1 + 1 -> 3
```
