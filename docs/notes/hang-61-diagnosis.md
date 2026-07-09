<!-- note-status: active -->
# Issue #61 diagnosis — the "hang" is per-step `Comp.subst` cost, not term blowup

> **Verdict (one sentence).** The reported hang is NOT exponential elaboration
> term-growth (term size is LINEAR in sibling count, +54 nodes/sibling) and NOT a
> step-count explosion (step count is ~linear in the work) — it is a large
> **per-step cost**: the reference semantics reduces by *whole-term substitution*
> (`Comp.subst = substFrom 0`, a full structural rebuild), so every Landin's-knot
> unfold (ADR-0073) re-`subst`s into a fresh copy of the entire recursive-function
> body, making each `Source.step` cost O(knot-body size) ≈ **~1 ms/step** on the
> JSON parser. Both engines are equally slow because both share this substitution
> reduction. Fix belongs to the **runtime/machine lane** (an environment/closure
> representation or explicit-substitution VM), NOT the elaborator.

## What was measured (data, not speculation)

Diag lane: `/srv/share/projects/lang-bang-diag61`, branch `diag-61-hang`. All
probes committed under `scratch/hang61/`. Measurements on the compiled `bang`
binary (`.lake/build/bin/bang`) and compiled Lean harnesses (`lake env lean
--run`; `lake env lean` #eval is unreliable for fuel recursion, so step counts
use compiled runs — the repo gotcha).

### 1 — Elaborated term size is LINEAR (refutes the primary suspect)

Minimal "one outer `let rec` + N sibling nested Div-declared `let rec`s, each
calling the outer knot" (`scratch/hang61/sib{1..5}.bang`), measured with a
constructor-count fold over the lowered `Comp` (`scratch/hang61/SizeProbe*.lean`):

| N siblings | elaborated `Comp` size |
|---:|---:|
| 1 | 321 |
| 2 | 375 |
| 3 | 429 |
| 4 | 483 |
| 5 | 537 |

Constant **+54 nodes per sibling** — linear, not geometric. The real (scoped-down)
`examples/json/main.bang` lowers to **4047** nodes: small. **The μ-knot elaboration
does NOT duplicate closures exponentially.** Hypothesis 1 (term blowup) is refuted.

### 2 — The cost is at RUNTIME, and it is per-step, not step-count

The real parser, timed on the compiled binary (`scratch/hang61/r*.bang`, `arr*.bang`):

| repro | work | wall time |
|---|---|---:|
| `arr1` | parse `[1]` | 1.05 s |
| `arr2` | parse `[1,2]` | 1.46 s |
| `arr3` | parse `[1,2,3]` | 1.97 s |
| `arr4` | parse `[1,2,3,4]` | 2.60 s |
| `arr5` | parse `[1,2,3,4,5]` | 2.80 s |
| `r1` | 1 `parseTop` + tag | 2.08 s |
| `r2` | 2 `parseTop` | 5.75 s |
| `r3` | 3 `parseTop` | 12.37 s |
| `examples/json/main.bang` (kernel) | 3 parses + 1 print | 16.85 s |
| `examples/json/main.bang` (`--compiled`) | same | 16.46 s |

Even parsing a **single-element array costs ~1 second**. Step counts (smallest fuel
to `done`, `scratch/hang61/StepCount*.lean`):

| repro | steps to `done` | wall | cost/step |
|---|---:|---:|---:|
| `arr1` | 1000 | 1.05 s | ~1.0 ms |
| `arr2` | 1500 | 1.46 s | ~1.0 ms |
| `r1` | 2000 | 2.08 s | ~1.0 ms |
| `r2` | 6000 | 5.75 s | ~1.0 ms |

Step count grows ~linearly with the work (+500 steps/array element); wall time
grows ~linearly; **cost-per-step is a large constant ~1 ms.** A CK step should be
nanoseconds. **~1 ms/step means each step traverses ~10⁵–10⁶ term nodes** — i.e.
it is rebuilding the elaborated body, not doing constant work.

### 3 — The mechanism, confirmed by a controlled experiment

`Bang/Core/Semantics/Subst.lean:112` — `Comp.substFrom` is a **full recursive
rebuild** of the term. Every reducer step that fires a redex uses `Comp.subst v M
= substFrom 0 v M` (`Eval.lean:89-99`: `handle`, `let`, `β`, `case`, `split` all
`Comp.subst`). There is **no environment / no closures** — this is pure
substitution semantics.

The recursion encoding (ADR-0073, Landin's knot, `buildLetRec` in
`Bang/Frontend/TypeCheck.lean:1936`): `Rec = μX. Thunk(X -> T)`, self-knot
`{ let #g = unfold sv in ($#g) sv }`, where the `inner` term is
`lam (let name = thunk(knotBody) in funBody')` and **`funBody'` is the entire user
function body**. Each recursive call unfolds the knot and `Comp.subst`s the
argument into a fresh copy of `funBody'`. So per unfold the reducer walks the whole
function body — and for the JSON parser that body is large and contains *further*
nested knots (`parseElems`, `parseFields`, `scanStr`, …), each themselves
re-substituted, which compounds the constant.

**Controlled confirmation** (`scratch/hang61/{small,bigbody}200.bang`): the SAME
200-iteration `Str -> Int` recursion, identical computation, differing only by 8
**dead** (never-forced, never-called) `let d_i = {fun x => x+i}` bindings inside
the knot body:

| knot body | wall time |
|---|---:|
| small (no dead lets) | 0.109 s |
| + 8 dead `let`s | 0.349 s |

3.2× slower from bindings that are never used — because they are re-`subst`-ed into
on every unfold. This isolates the cost to **body-size re-substitution per step**,
exactly the `Comp.subst` whole-body rebuild.

## Why both engines hang identically

The compiled machine (`exec ∘ compile`, ADR-0016) is `Agree`-tied to `Source.eval`
and reduces by the same substitution discipline — it inherits the same per-step
`Comp.subst` cost. Measured: `r3` = 12.59 s compiled vs 12.37 s kernel; `main.bang`
= 16.46 s vs 16.85 s. The cost is in the SHARED reduction relation, upstream of the
kernel/machine split — which is why the dogfood lane saw both hang identically.

## What was RULED OUT

- **Exponential elaboration term-growth** — refuted (§1: linear +54/sibling, 4047
  total). The μ-knot does not duplicate siblings geometrically.
- **Step-count explosion** — refuted (§2: step count ~linear in work, ~1 ms/step
  constant). It is not "too many steps", it is "each step is expensive".
- **A single bad transition / true non-termination** — refuted; every repro
  terminates at a fuel bound proportional to its work. The dogfood "hang past 590 s"
  is `defaultFuel = 100000` steps × ~1 ms + the compounding on nested/composed
  knots (a 4th parse or a `printJson` roughly doubles the knot-body traversal) —
  slow finite progress, not a loop.
- **Div-declaration (ADR-0088) as the cause** — not load-bearing for the cost. The
  `! {Div}` row only `divMark`-wraps the outer thunk; the cost is the substitution
  of `funBody'`, which is present for any `let rec` (Div-declared or not). Div knots
  merely tend to be the *large-bodied, nested* ones (parsers), so they surface it.

## Recommended fix (shape only — NOT implemented; this lane is diagnosis-only)

The correct fix is to stop reducing by whole-term substitution:

1. **Reference semantics (`Source.eval`): move to an environment machine.** Replace
   the substitution reducer with a closure/environment representation (values close
   over an environment; variable lookup is O(1) instead of "everything was already
   substituted in"). This makes a knot unfold O(1) instead of O(body-size). This is
   the state-of-art answer (every practical CBPV/abstract-machine implementation
   uses environments, not meta-level substitution) and it is the *root* fix.
   - Cost: it re-bases `Source.eval` and every proof indexed on `Comp.subst`
     (`type_safety`, the `Agree` battery, the LR). Large. This is the honest price
     of the current "pure substitution semantics" choice, which was taken for
     *proof simplicity* (substitution has no environment-wellformedness side
     conditions), per invariant #7 deferring perf.
2. **Cheaper interim (if (1) is too large for now): explicit-substitution / thunk-
   sharing at the knot.** Represent the recursive value so an unfold does not copy
   `funBody'` — e.g. share the body via a heap cell / recursive closure the machine
   dereferences, so the giant body is traversed once, not per call. Narrower blast
   radius than (1) but still touches the reduction relation and its metatheory.

**Owner lane:** the **runtime / calculated-machine lane** (whoever owns
`Bang/Core/Semantics/Eval.lean` + the CalcVM `exec`), NOT the elaborator/frontend.
The elaborator is correct; the encoding is correct; the reduction *strategy* is the
cost. This is a design decision (substitution vs environment reference semantics)
that reverses a load-bearing simplicity assumption, so it warrants an **ADR**
(supersedes the "TCO deferred / slow-correct-first" framing of ADR-0073 §5, which
anticipated deep-recursion `oom` but not per-shallow-step O(body) cost).

## Reproduce

```
cd /srv/share/projects/lang-bang-diag61      # branch diag-61-hang
nix develop -c lake build                    # cold: minutes
# term size (linear):
nix develop -c lake env lean --run scratch/hang61/SizeProbe2.lean    # 321/375/429/483/537
# runtime curve (the ~1 ms/step cost):
.lake/build/bin/bang run scratch/hang61/arr1.bang   # ~1 s to parse [1]
.lake/build/bin/bang run scratch/hang61/r3.bang     # ~12 s
# controlled body-size experiment:
.lake/build/bin/bang run scratch/hang61/small200.bang    # 0.11 s
.lake/build/bin/bang run scratch/hang61/bigbody200.bang  # 0.35 s (dead lets, same work)
```
