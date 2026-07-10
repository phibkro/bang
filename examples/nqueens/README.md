# nqueens

**N-queens solution counter** — a stress test of the pure `Div` fragment:
deep self-recursion, curried multi-arg `let rec`, generic `data List a`, and
A-normalized arithmetic over recursive calls. The classic two nested loops
(per-column recursion × per-row candidate scan) are **fused into one
self-recursion** because v1 has no mutual `let rec` (sibling `let rec`s
cannot forward-reference).

Counts solutions for boards 4/5/6 and packs them into one answer:
`q4 * 10000 + q5 * 100 + q6 = 2*10000 + 10*100 + 4 = 21004`.

Also a live benchmark of the ADR-0094 env engine: 8-queens (92) runs in
~0.2 s and 10-queens (724) in ~4 s interpreted, while `--engine=oracle`
exhausts its fuel ceiling even at 4-queens (the issue-#61 substitution-cost
cliff) — the honest current boundary of the differential seam.

```
lake exe bang run examples/nqueens/main.bang    # -> 21004
```
