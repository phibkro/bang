# issue #95 investigation — CalcVM `--compiled` "hang" on re-entrant let-rec knots

Scratch evidence for issue #95. NOT proof-bearing; NOT wired into the build gate.

## Verdict

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

## What needs an operator ruling (NOT this lane's edit)
The fix is a **cost fix, not a soundness fix** (per issue #95's own framing). Candidates:
sharing/memoizing the μ-knot value so `unfold sv … sv` doesn't duplicate; or a `letC`-share
so `compile (subst v N)` doesn't copy a large `v` twice; or prompt `out of fuel` when the
residual crosses a size threshold. All touch the proof-bearing `AbstractMachine.lean` /
`buildLetRec`, so they are findings for the operator, not edits here.
