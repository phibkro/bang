# issue #95 investigation — CalcVM `--compiled` "hang" on re-entrant let-rec knots

Scratch evidence for issue #95. NOT proof-bearing; NOT wired into the build gate.

## STATUS: FIXED (2026-07-10, branch `fix-95-knot-sharing`)

Route (i) — elaborator-side μ-knot sharing in `buildLetRec` (`Bang/Frontend/TypeCheck.lean`)
— is LANDED. The fix is ONE line: the knot body's self-argument changes from the raw `sv`
(a second free reference to the growing, embedded self-value) to `fold #g` (a re-wrap of the
just-`unfold`ed, freshly-LOCAL `#g` binding — semantically identical by the fold/unfold iso,
ADR-0029, but syntactically removes `sv` as a free variable from the app-argument position).
See the `buildLetRec` doc comment for the full mechanism writeup. The kernel/machine
(`Bang/Core/Semantics/Subst.lean`, `Bang/Backend/AbstractMachine.lean`) is UNTOUCHED — this is
a tested-stratum elaboration change only.

### Post-fix numbers (measured 2026-07-10, same corpus, same machine)

| measurement | before | after | ratio |
|---|---|---|---|
| `examples/calc/main.bang` on `--compiled` (full 10-input corpus) | 873 s | **7.3–7.9 s** | ~115× |
| `"1+2"` single-input (`scratch/calc95/runc.sh`) | 43 s | **0.36 s** | ~120× |
| `"1+2"` probe `maxCodeSize` | 331,587 | **19,342** | ~17× |
| `"1+2"` probe `maxSubstTermSize` | 330,037 | **18,879** | ~17× |
| `"1+2"` probe `totalSubstWork` | 9,365,512 | **1,291,988** | ~7× |
| `"1+2"` probe `steps` (machine-instruction fuel) | 741 | 741 | unchanged (fuel counts instructions, not per-instruction cost — see "why `#guard` fuel can't pin this" below) |
| codeSize trace shape | exponential doubling burst (`18K→34K→100K→166K→331K`) | flat/linear region (peaks ~19K, stays there) | doubling ELIMINATED |
| `repro-min.bang` sweep (`n=6..80`) `maxSubstTermSize` | grows with `n` (small shape doesn't hit the full exponential regime pre-fix either — see §4 below) | **flat 655** across `n=6..80` | linear→constant per-level cost |
| Three-engine agreement (`repro-min.bang`, env=ck=compiled) | 12 = 12 = 12 | 12 = 12 = 12 | unchanged (value-soundness held throughout — this was always a COST bug) |
| `examples/calc/main.bang` value | `11021193` | `11021193` | UNCHANGED (matches `expected.txt`; invariant #1 preserved) |

All numbers measured with `bash tools/seed-lake.sh` + `nix develop --command lake build` on
branch `fix-95-knot-sharing`, `.lake/build/bin/bang run --compiled …` / `scratch/calc95/gen.sh`
+ `runc.sh` / `StepProbe95.lean` (rebuild recipe below, unchanged).

### Why a `#guard` fuel bound can't pin the performance delta
`CalcVM.exec`'s `fuel : Nat` counts machine-INSTRUCTION-decrementing transitions, one per
`Instr` consumed — NOT the cost of processing that instruction's (potentially huge) residual
`Comp`/`Val` payload. The probe confirms `steps=741` IDENTICAL pre- and post-fix on the exact
same `"1+2"` input — only `maxCodeSize`/`maxSubstTermSize`/`totalSubstWork` (and wall-clock)
change. So `lake build`'s `#guard`s (which gate on fuel-bounded TERMINATION + VALUE, never
wall-clock or memory) cannot express this regression directly; `Bang/Examples.lean`'s new
`C-LETREC` guard (§D) pins VALUE correctness on the compiled path for a re-entrant knot
(a real, permanent regression against any future SOUNDNESS break here), and the wall-clock
collapse is pinned externally by this README's measured table + the `examples/calc/main.bang`
corpus (already permanently gated by `check-examples`/`check-examples-env`, though those run
the default `env` engine, not `--compiled` — the `--compiled` numbers above are this lane's
manual verification per issue #95's acceptance criteria).

## Original verdict (2026-07-10, pre-fix — preserved for the mechanism record)

The `--compiled` (CalcVM `exec ∘ compile`) engine does **NOT hang** and does **NOT loop**
on the calc parser inputs. It **TERMINATES with the correct value** (agreeing with `env`
and `ck`) but pays a **super-linear residual-recompile cost**, so at a 60 s dogfood timeout
it *presented* as a hang. This is a **cost pathology, NOT unsoundness** — invariant #1's
value-agreement holds; only the "fail-loud-promptly" expectation is missed (it grinds
rather than OOMing quickly).

**Capstone**: the FULL `examples/calc/main.bang` (10 `$calc` inputs + nodes + roundTrips)
on `--compiled` **terminates with `11021193` in 873 s** — the exact value `env`/`ck`/
`expected.txt` give. No hang, no loop, no unsoundness; just a ~15-minute cost blowup.

## Evidence (all measured on the calc corpus, 2026-07-10)

### 1. The 2×2 whitespace grid (--compiled) — whitespace is NOT the discriminator
| operator | unspaced        | spaced          |
|----------|-----------------|-----------------|
| `+`      | `1+2` → 3 (44s) | `1 + 2` → 3 (43s) |
| `*`      | `1*2` → 2 (25s) | `1 * 2` → 2 (25s) |

Spacing changes nothing. The discriminator is the **operator/production**: `*` (termLoop
path) vs `+`/`-`/`(` (exprLoop path = the re-entrant outer knot). Refutes the lexer-
whitespace hypothesis; confirms N5's re-entrant-outer-knot diagnosis.

### 2. Fuel-vs-loop split — VERDICT (a) blowup, not (b) loop
Step-counting probe (`StepProbe95.lean`, a faithful mirror of `exec` that counts fuel-
decrementing transitions):

| input | steps | maxSubstTermSize | maxCodeSize | totalSubstWork |
|-------|-------|------------------|-------------|----------------|
| `"7"`   | 345 | 329,897 | 331,447 | 3,810,277 |
| `"1*2"` | 728 | 330,007 | 331,557 | 5,307,056 |
| `"1+2"` | 741 | 330,037 | 331,587 | **9,365,512** |
| `"(7)"` | 757 | 330,027 | 476,860 | 9,937,372 |

- **Only ~741 machine steps** — trivially few. NOT a loop (a loop never terminates at any
  fuel; every input DID terminate). NOT fuel-count explosion.
- The **residual `Code` reaches ~331K nodes** even for `"7"`, and wall-time tracks
  `totalSubstWork` (linear), NOT step count. The cost is PER-STEP: each of the hundreds of
  `compile (Comp.subst v N) c` recompiles traverses/copies a huge residual term.
- A codeSize-over-time trace on `"1+2"` shows an **exponential doubling burst**:
  `18K → 34K → 100K → 166K → 331K` within a single eval descent (steps ~505–581).

### 3. Mechanism — μ-encoding residual duplication (ADR-0073 `buildLetRec`)
`let rec` desugars to `recTy := μX. Thunk(X → T)` with knot body
`let #g = unfold sv in ($#g) sv`. The knot var `sv` appears **twice** (in `unfold sv` AND
as the argument), so `SUBST` substitutes the large `fold {inner}` value into BOTH positions
= a **doubling**. `inner` contains the whole function body (all nested siblings), so a deep
single-descent chain of μ-unfolds compounds multiplicatively: **~2^(unfold-depth)** residual.
calc's parseExpr (4 large nested siblings) + parseFactor re-entering parseExpr is exactly the
deep re-entrant unfold chain that pushes maxCodeSize to 331K.

### 4. Minimal repro (`repro-min.bang`, <15 lines) — QUALITATIVE
`env` = `ck` = `--compiled` = **12** (values AGREE). Same shape (outer knot `p`, nested
siblings, `factor` re-enters `p`). At `$p 6` the cost is small; bumping the arg makes
`--compiled` measurably slower while `env`/`ck` stay instant (n=80 → env 0 s, compiled 6 s).
The FULL exponential burst (331K residual, ~40 s) does NOT shrink below the calc example —
it needs calc's four *large* siblings + deep re-entry. So the **calc example remains the
exact-40s pin**; `repro-min.bang` is the faithful small qualitative pin.

## How to rebuild the step probe
`StepProbe95.lean` was built as a throwaway lake exe (stanza reverted, file parked here).
To reproduce: copy `StepProbe95.lean` to the repo root, add to `lakefile.toml`:
```
[[lean_exe]]
name = "stepprobe95"
root = "StepProbe95"
```
`nix develop --command lake build stepprobe95`, then
`.lake/build/bin/stepprobe95 Ast.bang Lexer.bang Parser.bang Eval.bang entry.bang`
(5-file calc mode) or `--single file.bang` (single-file typed mode).

## What needed an operator ruling (RESOLVED — route (i) landed)
The fix is a **cost fix, not a soundness fix** (per issue #95's own framing). The ruled
fix was route (i) — **elaborator-side μ-knot sharing in `buildLetRec`** (NOT a machine/kernel
change): `fold #g` instead of `sv` as the self-application argument, eliminating the SECOND
free occurrence of the growing self-value in the knot body's substitution target. See the
"STATUS: FIXED" section above for the mechanism + measured numbers, and `buildLetRec`'s own
doc comment (`Bang/Frontend/TypeCheck.lean`) for the full writeup with the ADR-0029 fold/unfold-
iso justification. `Bang/Core/Semantics/Subst.lean` / `Bang/Backend/AbstractMachine.lean`
(the proof-bearing substitution + machine) are UNTOUCHED — invariant #4 (the machine is a
calculation output, never hand-tuned) holds.
