# effect-op-arith

**Arithmetic composes with effect operations** (issue #26). Both halves of the
fix are exercised in one line:

- `read a - 30` — an effect op (`read`) feeds the operator chain. The ops
  (`raise`/`put`/`new`/`read`/`write`) parse at application precedence like the
  nullary `get`, so `read a - 30` is `(read a) - 30`, not a parse error
  (part-2, the precedence fix).
- `write a (read a - 30)` — the op's argument is a *computation* (`read a - 30`),
  A-normalized in the lowering: let-bind it, perform on the bound value
  (part-1, the value-restriction fix).

`new 100` allocates a TVar at 100, `write a (read a - 30)` stores `100 - 30`,
`read a` observes it.

```
lake exe bang run examples/effect-op-arith/main.bang    # 100 - 30 -> 70
```
