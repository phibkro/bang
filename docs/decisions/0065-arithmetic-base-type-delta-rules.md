# ADR-0065 · Arithmetic & comparisons as base-type δ-rules (`Comp.binop`) — pure, ⊥-row

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Integer arithmetic (`+ − × ÷`) and comparisons (`< ==`) enter the kernel as pure base-type δ-rules via ONE new computation form `Comp.binop : BinOp → Val → Val → Comp`, ⊥-row typed. Comparisons return `Bool = 1+1` (a sum), so `if` is surface sugar over `case`. A δ-rule is NOT a sixth computational primitive — invariant #5 governs effect/computation structure, not base-type operations.
- **Resolves**: tracer-finding #1 (the deferred "arithmetic needs a separate K-ADR")
- **Depends-on**: 0029, 0020, 0007

- **Status:** Accepted (kernel form + reduction locked; spine propagation + surface staged below).
- **Date:** 2026-06-30
- **Layer:** K (kernel — term syntax + operational semantics + the metatheory over it). **Tag: K-ADR** (semantic).
- **Resolves:** the long-deferred *"arithmetic needs a separate K-ADR"* tracer finding #1 (referenced
  across `paths/archive/PATH-rung1-state.md` and the FINDING in `Bang/Frontend/Surface.lean`). Unblocks
  the *premise* of **Q15** (eager-folding of `4+2`), which presupposes `+` exists.
- **Builds on:** ADR-0029 (iso-recursive ADTs — `Bool = 1+1` reuses the sum former; comparisons return
  `inl/inr unit`). ADR-0020 (de-Bruijn graded context — `binop` is closed, binds nothing). ADR-0007
  (`force`/thunk — arithmetic is pure, observed only via the surrounding sequencing).
- **Reference:** Levy, *Call-by-Push-Value* (base types come with their values AND their primitive
  operations; an operation is a computation `op(v⃗)` returning a value). Plotkin (δ-reduction in typed
  λ-calculi — a base-type op is not a new binding/effect construct).

## Context — integers exist as values, but have no operations

`Bang/Core/IR.lean` already has `Val.vint : Int → Val`: machine integers are first-class values. What
is missing is any way to OPERATE on them — there is no `+`. Every "counter" (`get; put (get+1)`) across
the rungs has been blocked on exactly this, and the gap was explicitly deferred as *"a separate K-ADR
(tracer finding #1)"*. Two non-kernel routes were refuted (below), establishing that arithmetic genuinely
requires a kernel form. This ADR settles the SHAPE of that form.

## Decision — one pure δ-rule computation form

Add a single closed computation former and an operator enum:

```lean
inductive BinOp | add | sub | mul | div | lt | eq

-- in Comp:
| binop : BinOp → Val → Val → Comp    -- δ-rule: both operands are VALUES; reduces immediately
```

**Reduction** (in `Source.eval`, alongside `case`/`split`/`unfold` — value scrutinees, no eval-context
frame is needed):

```
binop add (vint a) (vint b)  ↦  ret (vint (a + b))            -- sub, mul likewise
binop div (vint a) (vint b)  ↦  ret (vint (a / b))            -- Lean Int division: TOTAL, a/0 = 0 (below)
binop lt  (vint a) (vint b)  ↦  ret (boolVal (a < b))
binop eq  (vint a) (vint b)  ↦  ret (boolVal (a = b))
binop _   _        _         ↦  wrong "binop: non-int operand"  -- fail-loud; unreachable for typed terms
```

- **`Bool = 1 + 1`** (reuses the sum, ADR-0029): `boolVal true = inr vunit`, `boolVal false = inl vunit`.
  No kernel `Bool` type, no kernel `if`. `if c then t else e` is **surface sugar** → `case c e t`
  (inl/false → `e`, inr/true → `t`).
- **Division by zero is total**: mirrors Lean's `Int` division (`a / 0 = 0`), keeping `div` PURE and
  total — no effect, no partiality. A *checked* division that fails loudly is an EFFECT (`raise`), hence
  post-v1 library code over the existing `throws` handler, NOT a kernel concern. Recorded so the `a/0=0`
  choice is deliberate, not an accident.
- **Typing**: `binop (arith) : Int → Int → Int` and `binop (compare) : Int → Int → Bool`, both with the
  **⊥ effect row** — arithmetic is pure. This is the load-bearing property (see rejected alt 1).

## Invariant #5 is not violated — a δ-rule ≠ a sixth primitive

Invariant #5 ("the kernel stays at five primitives: thunk · force · effect rows · handlers · STM")
governs the **effect/computation structure** — how a program suspends, observes, and handles effects. A
base-type δ-rule is the **base type being non-trivial**: `vint` literals are already base-type *values*;
`binop` is their *eliminator*, exactly as `case`/`split`/`unfold` (ADR-0029) eliminate the ADT
value-formers without being counted among the five. Adding `binop` no more adds a "sixth primitive" than
`vint` itself did — were `Int` removed, the five would be unchanged. This clause exists so a future
session does not misread `binop` as a moat violation.

## Rejected alternatives

1. **Arithmetic as an effect + handler** (`perform addCap "+" (pair a b)`, an `arithmetic` handler).
   *On-brand* (the moat: paradigms are values) but **breaks purity**: performing an operation puts its
   label in the effect row, so `4 + 2` would type as EFFECTFUL. Q15 establishes "the effect row is the
   license to fold" — a pure closed `4+2` must stay ⊥-row to be foldable at compile time. Effectful
   arithmetic also forces every numeric function's type to carry an `arith` label. **Refuted on
   correctness** (mis-types purity), independent of taste.
2. **Church/Scott encoding** (`Nat = μX.1+X`, `+` by recursion). Zero kernel change, but (a) ignores the
   machine `Int` already in `Val`, (b) is unary and pathologically slow, (c) needs general recursion. A
   non-starter when `vint` already exists.
3. **A general foreign/native-op escape** (`Comp.foreign : (Val → Val) → Val → Comp`). One construct
   yields all base ops + IO, but injects opaque Lean functions into terms — destroying
   `Repr`/`DecidableEq`/serializability of the term language and the "machine is calculated, not
   hand-designed" property (invariant #4). Wrong for a verified, inspectable calculus.

## Consequences — a spine increment, bounded by δ-rule simplicity

Unlike the ADT *surface* (ADR-free, leaf-only — issue #1), `binop` is a new `Comp` case → every match
over `Comp` across the verified spine gains one arm:

```
Source.eval (reference) → evalD → CalcVM compile/exec → Wasm backend → Typing (HasCTy)
  → Soundness (progress / preservation / type_safety) → LR / BinaryLR
```

The re-proof is **bounded**: `binop` is a deterministic, store-free, capture-free local reduction
(`ret (vint r)`) — the easiest case for forward simulation (no continuation, no heap, no fresh identity).
`progress`: a well-typed `binop` on two `vint` always steps. `preservation`: the reduct has the typed
result type. No headline axiom changes (the census stays ⊆ {propext, Classical.choice, Quot.sound}; the
new case is *handled*, not deferred to a sorry).

**Staging** (each gated; STOP-and-SHOW at the spine seam):
① this ADR → ② kernel form + `Source.eval` (the oracle) + a kernel `#guard` (`3+4 ⟶ 7`, `3<4 ⟶ true-sum`)
→ ③ mechanical spine propagation (one arm per `Comp` match) → ④ re-prove the soundness arms → ⑤ surface
(infix precedence-climbing parser + lowering + `if`-sugar + corpus `#guard`s).
