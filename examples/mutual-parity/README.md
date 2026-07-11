# mutual-parity — `let rec … and …` (#97 item 2)

The canonical example for mutual `let rec`: `even`/`odd` hand off to EACH OTHER
(neither calls itself), the shape a single `let rec` cannot express directly —
today's workaround is one hand-fused function carrying a parity flag (see the
differential `#guard`s against exactly that fused shape in
`Bang/Frontend/TypeCheck.lean`'s ⑨j′ validation section).

A second group, `cycleA`/`cycleB`/`cycleC`, is a 3-way cycle — confirms the H2
tuple-of-thunks μ-knot (`buildLetRecMulti`) generalizes past a pair.

Exercises: the `and`-chained grammar, mutual visibility by construction (not
textual ordering — `even` calls `odd` before `odd` is bound), the mandatory
per-sibling `! {Div}` annotation (mutual groups default conservatively to
`Div` — structural certification is not extended to co-recursive name sets,
a documented gap, see `docs/decisions/` for the ADR), and N-way (N=3) beyond
the pair case.
