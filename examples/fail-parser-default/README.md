# fail-parser-default

Half of the **Fail-parser handler-swap pair** (with
[`fail-parser-strict`](../fail-parser-strict/)) — the IDENTICAL chooser shape (a custom `Try`
handler services the first candidate, a guard rejects the second, `raise` aborts past the still-
installed `Try` frame to the outer `handle`), but with the DEFAULT-VALUE policy: on failure,
raise a safe fallback (`0`) instead of the raw failure code. Comparing this against
`fail-parser-strict` line for line, only the abort's payload differs (`raise 999` vs `raise 0`)
— v1's `handle` installs a fixed zero-shot `throws` catcher (it cannot itself be swapped for a
value-transforming handler), so the failure POLICY — surface the error vs substitute a default —
is expressed at the raise site the custom `Try` frame protects, not as a second built-in handler
variant. The `Try` handler and its abort-past-frame mechanism are shared; the policy is what
changes.

```
lake exe bang run examples/fail-parser-default/main.bang    # 4 ok, second candidate rejected -> raise 0 -> 0
```
