# fail-parser-strict

Half of the **Fail-parser handler-swap pair** (with
[`fail-parser-default`](../fail-parser-default/)) — a small chooser: a custom `Try` handler
services a *first* candidate (`try.attempt(4)` succeeds), then a guard picks between a *second*
candidate and an abort. Here the guard is false (`6 < 5`), so `raise 999` fires — the SAME
raise-past-a-custom-frame shape as `examples/handle-custom-abort-coexist`: the abort skips the
still-installed `Try` frame entirely (the second `try.attempt(6)` never runs) and is caught by
the outer `handle`. This is the STRICT policy: on failure, surface the raw failure code (`999`)
so the caller can see exactly what went wrong — fail-fast, no silent recovery.

```
lake exe bang run examples/fail-parser-strict/main.bang    # 4 ok, second candidate rejected -> raise 999 -> 999
```
