/-
  Bang/Surface/PropTest.lean — the STACK LAWS, property-tested via `plausible`.

  Extracted from Surface.lean (Phase-1a modules-everywhere): this is the ADR-0028
  rung-2 *tested* superset — `plausible`'s `Gen`/`Arbitrary` API is `meta` in v4.30,
  and a `meta` generator may not call the RUNTIME stack constructors (`push`/`empty`/
  `pop`). That meta/runtime phase split is irreducible, so this property-test harness
  CANNOT be a `module` (the generators bridge meta sampling and runtime values). It is
  the one documented non-module exception — and that is exactly the verified-spine /
  tested-superset seam made structural: the proptest rung lives outside the module spine.

  Surface-proper is a `module`; this file `import`s it (non-module importing a module
  is fine) and re-opens its namespace, so the laws read `push`/`empty`/`pop`/`Source.eval`
  exactly as before. Behaviour is unchanged — the same three `#test`s, same generators.
-/

import Bang.Surface
import Plausible

namespace Bang.Surface

open Bang
open Bang.EffectRow (Label)

/-! ### Stage 1d — the STACK LAWS, property-tested via `plausible` (rung 2 Q19).

THE moat demo, and the first use of the ADR-0026 *tested* rung (ADR-0028 adopts
`plausible` — Lean's QuickCheck — at rung 2). The push/pop laws are stated OVER THE
EVAL SEMANTICS (run through `Source.eval`) for arbitrary `Int x` and arbitrary
bounded-depth `Stack Int` value `s`, then `#test`-ed: `#test` (= `#eval
Testable.check`) SAMPLES the generators and THROWS at elaboration on a counter-example,
so a false law FAILS THE BUILD. It admits no `sorry` (unlike `by plausible`) and is not
a banned tactic — it is the compiled-evaluation idiom (same family as `#guard`), which
is exactly the point of the tested rung: a real sampling test where a proof is not (yet)
spent.

`StackVal` wraps a `Val` so plausible's instance resolution (`SampleableExt` ←
`Repr`/`Shrinkable`/`Arbitrary`) targets STACK values specifically, not arbitrary `Val`s.
The generator builds `push`/`empty` to a depth bounded by the `Gen` size parameter, so
every sample is a well-formed `Stack Int`. -/

/-- A generated `Stack Int` value (a `Val` known to be `push`/`empty`-shaped). The wrapper
exists so `Arbitrary`/`Repr`/`Shrinkable` resolve to the stack generator below, not to a
generic `Val` instance (there is none). -/
structure StackVal where
  val : Val

/-- Stack depth (number of pushes), for a readable `Repr` of a counter-example. -/
def stackDepth : Val → Nat
  | .fold (.inr (.pair _ rest)) => stackDepth rest + 1
  | _                            => 0

instance : Repr StackVal := ⟨fun s _ => s!"StackVal(depth={stackDepth s.val})"⟩

open Plausible

/-- Build a stack of EXACTLY `d` pushes (`vint`s drawn from the `Gen` size) on top of
`empty`. Structural recursion on `d` — total, no fuel needed. -/
def genStackOfDepth : Nat → Gen Val
  | 0     => pure empty
  | d + 1 => do
      let n : Int ← Arbitrary.arbitrary
      let rest ← genStackOfDepth d
      pure (push n rest)

/-- Arbitrary `Stack Int`: pick a depth in `0 … size` (bounded by the `Gen` size
parameter), then fill it. Bounded depth keeps samples finite and `Source.eval`'s fuel
sufficient. -/
instance : Arbitrary StackVal where
  arbitrary := do
    let d ← Gen.choose Nat 0 (← Gen.getSize) (Nat.zero_le _)
    return ⟨← genStackOfDepth d⟩

/-- Shrink toward the empty stack by dropping the top element (one structural step). -/
instance : Shrinkable StackVal where
  shrink
    | ⟨.fold (.inr (.pair _ rest))⟩ => [⟨rest⟩]
    | _                              => []

/-- Fuel for `Source.eval` in the laws: pops + pushes are O(depth); the size parameter
caps depth at `plausible`'s `maxSize` (default 100), so this is comfortably above it. -/
def lawFuel : Nat := 400

/-- The popped result of `pop s`, read back from `Source.eval` (the eval semantics). -/
def evalPop (s : Val) : Result Val := Source.eval lawFuel (pop s)

/-- **Law 1 — push/pop round-trip:** `pop (push x s) = some (x, s)`. Over eval: popping
a freshly-pushed stack yields `done (inr (pair (vint x) s))` — the pushed element AND the
original stack, recovered. -/
def roundTrip (x : Int) (s : StackVal) : Bool :=
  match evalPop (push x s.val) with
  | .done (.inr (.pair (.vint top) rest)) => top == x && (rest == s.val)
  | _                                     => false

/-- **Law 2 — pop empty = none:** `pop empty` yields `done (inl unit)`. (Constant, but
stated as a property so it sits in the same tested suite.) -/
def popEmptyNone : Bool :=
  match evalPop empty with
  | .done (.inl .vunit) => true
  | _                   => false

/-- **Law 3 — LIFO ordering:** `pop (push x (push y s))` exposes `x` first; popping the
remaining stack then exposes `y`. The most recent push is the first pop. -/
def lifo (x y : Int) (s : StackVal) : Bool :=
  match evalPop (push x (push y s.val)) with
  | .done (.inr (.pair (.vint top1) rest)) =>
      top1 == x &&
      (match evalPop rest with
       | .done (.inr (.pair (.vint top2) rest2)) => top2 == y && (rest2 == s.val)
       | _                                       => false)
  | _ => false

-- The properties. `#test` SAMPLES and throws at elaboration on a counter-example
-- (build-fail); on success it logs "Unable to find a counter-example". No `sorry`.
#test ∀ (x : Int) (s : StackVal), roundTrip x s = true
#test popEmptyNone = true
#test ∀ (x y : Int) (s : StackVal), lifo x y s = true

end Bang.Surface
