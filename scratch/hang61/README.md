# scratch/hang61 — issue #61 diagnosis probes

Diagnosis: the "hang" is per-step `Comp.subst` cost (whole-body substitution on
every Landin's-knot unfold), NOT term blowup or step-count explosion. Full
write-up + data: `docs/notes/hang-61-diagnosis.md`.

## Self-contained probes (committed, runnable as-is)

- `sib{1..5}.bang` — minimal "outer knot + N sibling nested Div-declared `let
  rec`s" programs. Feed `SizeProbe*.lean` (elaborated-term-size = linear, +54/N).
- `SizeProbe.lean`, `SizeProbe2.lean` — constructor-count fold over the lowered
  `Comp` for `sib*.bang` (and the real `examples/json/main.bang`).
    `nix develop -c lake env lean --run scratch/hang61/SizeProbe2.lean`
- `small.bang` / `bigbody.bang`, `small200.bang` / `bigbody200.bang` — the
  controlled body-size experiment: identical recursion, differing only by dead
  (never-used) `let`s in the knot body. Shows step-cost scales with body size.
    `.lake/build/bin/bang run scratch/hang61/bigbody200.bang`   # 0.35s vs 0.11s
- `flat50.bang` / `nested50.bang` — flat vs nested knot at equal outer depth.

## Derived repros (regenerate from `examples/json/main.bang`)

`RunProbe.lean` / `StepCount*.lean` were run against a `prelude.bang` (=
`head -323 examples/json/main.bang`, the parser/printer defs through `parseTop`)
plus a body. Regenerate:

```sh
P=scratch/hang61/prelude.bang
head -323 examples/json/main.bang > "$P"          # ends at `parseTop = {...}`
gen() { { cat "$P"; printf '  in\n'; printf '%s\n' "$1"; } > "scratch/hang61/$2.bang"; }
gen '$tagOf ($parseTop "[1]")'                 arr1     # ~1.0s
gen '$tagOf ($parseTop "[1,2,3,4,5]")'         arr5     # ~2.8s
gen 'let a = $parseTop "[1, 2, 3]" in $tagAt 0 a'                                         r1  # ~2.1s
gen 'let a = $parseTop "[1, 2, 3]" in let b = $parseTop "{\"a\": 1, \"b\": 2}" in let c = $parseTop "[10, [20, 30], {\"x\": true, \"y\": null}]" in $tagAt 0 a + $tagOf b + $tagAt 0 c'  r3  # ~12s
gen 'let a = $parseTop "[1, 2, 3]" in $printJson a'  rp  # ~5.6s
```

Then time with `.lake/build/bin/bang run scratch/hang61/<f>.bang`, or measure
step counts by pointing `StepCount*.lean`'s `include_str` at the generated files.
The measured numbers are tabulated in the diagnosis note.
