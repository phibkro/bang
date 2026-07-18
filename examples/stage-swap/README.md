# stage-swap

The per-stage story (#84): ONE shared effectful LOGIC function — `net.fetch(1) + net.fetch(2)` —
composed with TWO different reusable HANDLER-INSTALLER functions (`test`/`prod`, each installing
a named realization of the `Stage_Net` contract), producing two different, distinguishable stage outputs (combined
into one printable Int: `stage1_result * 1000 + stage2_result`, so both are legible in the single
`expected.txt` value). Demonstrates the thesis directly: "the stage IS the handler; the row is the
interface contract" — the SAME `logic` function, unchanged, means something different depending on
which installer it is passed to: `test` (`fetch(n) => n * 10`, `30 * 1000 = 30000`) vs `prod`
(`fetch(n) => n + 1`, `5`).

```
lake exe bang run examples/stage-swap/main.bang    # 30005
lake exe bang test examples/stage-swap/Stage.bang  # 2/2 laws pass
lake exe bang query laws examples/stage-swap/main.bang
```

`Stage.bang` owns the reusable semantic unit: the `Net` effect contract, a `stable`
law saying repeated fetches of one key agree, and the `Test`/`Prod` named handler
realizations. The law runner checks the same obligation against both realizations;
resolver-aware queries retain both imported facts from the entry file.

## The wrapper pattern (operator-ruled, #84 gap 2)

A runtime-selectable stage is a FUNCTION that installs a statically named realization around a
body it receives:

```
let test = ( {fun body => handle (($body)(net)) with Stage_Test as net}
             : Thunk (Thunk (Cap Stage_Net -> Int ! {Stage_Net}) -> Int) )
```

Wrapper functions are already first-class values — passable, storable, and RUNTIME-selectable
— which is what the per-stage story needs. `main.bang` now exercises that route directly with
`let selected = if 1 == 1 then test else prod`: choice is dynamic at the installer layer while
each installer expands a named realization through the existing custom-handler path. This delivers
runtime stage selection with ZERO kernel change; the first-class artifact is the installer, not a
reified handler value.

The SHARED logic is an ordinary `Cap Stage_Net`-typed function (#84 gap 1: cap-typed function params):

```
let logic =
  ( {fun net => (net.fetch(1)) + (net.fetch(2))}
    : Thunk (Cap Stage_Net -> Int ! {Stage_Net}) )
```

**v1 surface notes** (both pre-existing, not this example's doing — see `Bang/Frontend/TypeCheck.lean`'s
`#84 gap 1` / `#90` `#guard` sections for the full account):

- `fun` has no inline per-parameter ascription (`fun (x : T) => …` does not parse) — the v1 way to
  type a lambda's parameter is the OUTER ascription, `(fun x => body : A -> B)`.
- Binding ANY function by name requires THUNKING (`{fun x => body}`, not a bare `fun x => body` —
  the latter is rejected as "not a returner"). A `{…}`-thunked value's ascription must ALSO be
  `Thunk (…)`-wrapped on the outside (`( {expr} : Thunk T )`, never `( {expr} : T )` bare) — the
  thunk's real TYPE is `Thunk T`, so the outer wrap is not optional sugar.
- Calling a bound function value needs the explicit `$`-force: `($f) arg`, never bare `f(arg)` when
  `f` is a value in scope (as opposed to `h.op(args)`, the DIFFERENT `.dotPerform` method-call form
  for a capability receiver, which stays bare).

Once #90 (row annotations naming USER-declared effects, `T ! {UserEffect}`) landed, this example's
ideal shape — the one sketched above — types and runs end to end; earlier revisions of this
example worked around that gap by inlining the shared expression under each `handle` rather than
abstracting it into a callable function.

## The former #94 gate: reusing ONE installer binding across differently-effectful bodies — CLOSED

This example's shape — TWO installer BINDINGS (`test`, `prod`), each applied ONCE to the SAME
`logic` — is fully general and works today (as does runtime-selecting between them, since they
share one type: `(if flag then test else prod)(logic)` types and runs, confirmed live). What does
NOT yet work is reusing the SAME installer binding against operands at genuinely DIFFERENT effect
rows in one program:

```
-- WORKS since ADR-0107 (effect-row subeffecting at reuse sites; #94 closed):
let pureBody = ( {fun net => 99} : Thunk (Cap Net -> Int) ) in
(($test) logic) + (($test) pureBody)     -- `test` reused at {Net} then at {} — now admitted
```

This was `unifyRow`'s "single shared row var" incompleteness, closed by ADR-0107: on a
row mismatch at the one `unifyRow` call site, an open row variable is re-bound to the wider
join (the narrower use is always ⊆ the join — the relation `subRow` already proves sound), and
closed rows admit a subset directly. The exact program above is now a compiled `#guard`
(`stageSwapReuseSrc` = 129) — this section survives as the record of the gate and its closing.
Full Rémy row polymorphism (incomparable rows) remains consumer-gated per ADR-0107.
