# stm

**STM** as a transactional handler (ADR-0030: v1 ships STM as a handler, the
privileged shared-heap form returns with concurrency). `atomically …` runs a
transaction; `new 100` allocates a TVar, `write r 70` updates it, `read r`
observes it. TVars are usable only inside `atomically`.

```
lake exe bang run examples/stm/main.bang    # write 70 then read -> 70
```
