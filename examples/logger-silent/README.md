# logger-silent

Half of the **Logger handler-swap pair** (with [`logger-counting`](../logger-counting/)) — the
same program, `(logger.log(10)) + (logger.log(20)) + (logger.log(30))`, run under two different
`Log` handlers. This handler is SILENT: `log(msg) => 0` discards every message, so the three
performs contribute nothing and the sum is `0`.

```
lake exe bang run examples/logger-silent/main.bang    # 0 + 0 + 0 -> 0
```
