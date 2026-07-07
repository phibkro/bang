# handle

An **effect handler** catching a performed operation. `handle (… raise 7 …)`
installs a handler for `raise`; performing `raise 7` transfers control to the
handler, which yields `7` (the `99` continuation is discarded). Demonstrates that
exceptions are just an effect + handler over the kernel.

```
lake exe bang run examples/handle/main.bang    # raise 7 (handled) -> 7
```
