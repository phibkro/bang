# stage-swap

The per-stage story (#84): the SAME effectful logic — `net.fetch(1) + net.fetch(2)` — run under
TWO different handler installations, producing two different, distinguishable stage outputs
(combined into one printable Int: `stage1_result * 1000 + stage2_result`, so both are legible in
the single `expected.txt` value). Demonstrates the thesis directly: "the stage IS the handler; the
row is the interface contract" — the SAME expression, unchanged, means something different under
`fetch(n) => n * 10` (stage 1, `30 * 1000 = 30000`) vs `fetch(n) => n + 1` (stage 2, `5`).

```
lake exe bang run examples/stage-swap/main.bang    # 30005
```

**Known scope gap (not this example's doing):** the ideal form of this demo abstracts the shared
logic into a `pub` function taking a `Cap Net` parameter (`pub let get2 = fun (net : Cap Net) =>
…`), called once per stage with a different `as`-bound capability supplying the handler
(#84's own target sketch). That abstraction is currently BLOCKED on a row-annotation gap: `T !
{ρ}` type ascriptions can only name the four BUILT-IN effects (`throws`/`state`/`stm`/`Div`) —
`effNames`/`effOf` (`Bang/Frontend/TypeCheck.lean`) have no `env.effects` access, so `Thunk (Cap Net
-> Int ! {Net})` cannot yet be written for a USER-declared effect like `Net`. Until that lands
(tracked as a follow-up to #84, the same class of fix `resolveTyG`'s `Cap` special-case made — see
the `#84 gap 1` section of `Bang/Frontend/TypeCheck.lean`'s `#guard` corpus for the full account),
this example inlines the shared expression under each `handle` rather than abstracting it into a
callable function — the RECEIVER-DISPATCH mechanism (a capability typed `Cap ℓ`, wherever it is
bound, dispatches `.dotPerform` correctly) is proven separately by the `#84 gap 1` `#guard`
corpus, which DOES exercise a `Cap Net`-typed BINDING (via `checkPerformUnderCap` and an ascribed
identity function) — just not yet a full effectful `pub` function callable per-stage.
