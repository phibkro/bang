# stage-swap

The per-stage story (#84): ONE shared effectful LOGIC function — `net.fetch(1) + net.fetch(2)` —
composed with TWO different reusable HANDLER-INSTALLER functions (`test`/`prod`, each installing
its own `handle … with Net`), producing two different, distinguishable stage outputs (combined
into one printable Int: `stage1_result * 1000 + stage2_result`, so both are legible in the single
`expected.txt` value). Demonstrates the thesis directly: "the stage IS the handler; the row is the
interface contract" — the SAME `logic` function, unchanged, means something different depending on
which installer it is passed to: `test` (`fetch(n) => n * 10`, `30 * 1000 = 30000`) vs `prod`
(`fetch(n) => n + 1`, `5`).

```
lake exe bang run examples/stage-swap/main.bang    # 30005
```

## The wrapper pattern (operator-ruled, #84 gap 2)

A reusable "handler" is a `pub` FUNCTION that installs the `handle` around a body it receives:

```
let test = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n * 10 }}
             : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) )
```

Wrapper functions are already first-class values — passable, storable, and RUNTIME-selectable
(`(if flag then test else prod)(logic)`) — which is what the per-stage story needs, and delivers
it with ZERO kernel change: the reusable artifact is the INSTALLER, not a reified handler value.

The SHARED logic is an ordinary `Cap Net`-typed function (#84 gap 1: cap-typed function params):

```
let logic = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) )
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

## Known gate: reusing ONE installer binding across differently-effectful bodies (#94)

This example's shape — TWO installer BINDINGS (`test`, `prod`), each applied ONCE to the SAME
`logic` — is fully general and works today (as does runtime-selecting between them, since they
share one type: `(if flag then test else prod)(logic)` types and runs, confirmed live). What does
NOT yet work is reusing the SAME installer binding against operands at genuinely DIFFERENT effect
rows in one program:

```
-- FAILS today ("effect row mismatch"), even though each application alone type-checks:
let pureBody = ( {fun net => 99} : Thunk (Cap Net -> Int) ) in
(($test) logic) + (($test) pureBody)     -- `test` reused at {Net} then at {} — the wall
```

This is `unifyRow`'s pre-existing, already-documented "single shared row var" incompleteness
(`TypeCheck.lean`'s `rowPolyDivSrc` corpus, `compose incPure <effectful>` — the SAME wall, not
specific to the wrapper pattern or capabilities; confirmed via an isolated non-cap repro). Filed as
issue #94 (a type-system-design decision — subeffecting vs full Rémy row polymorphism — not a local
elaboration fix, so it is NOT ground this lane's rider budget covers). The per-stage story ships
today in the form this example demonstrates (separately-named installer bindings); reusing ONE
binding across stages with genuinely different effect rows is the named next rung.
