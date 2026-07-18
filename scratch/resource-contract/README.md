# Resource-contract refusal fixtures

These four programs are the refute-first inputs that froze `use [q] x in body` before its
implementation. They remain the negative/edge corpus for `PATH-resource-contract-tracer`.

| Fixture | Required result |
|---|---|
| `accept-once.bang` | checks and evaluates to `7` |
| `reject-duplicate.bang` | rejects with the stable quantity diagnostic |
| `reject-forget.bang` | rejects with the same diagnostic family |
| `erase-zero.bang` | evaluates to `7`; emitted Wasm evaluates `ghost`'s RHS but allocates no environment cell for its result |

The permit is an ordinary user effect with two named realizations. The quantity is a separate
value-use assertion; the effect row remains an unweighted set. `use [0]` does not erase an effectful
RHS—the kernel's `q_or_1` let floor intentionally preserves that evaluation.
