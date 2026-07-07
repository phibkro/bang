---
type: design-question
title: "Memoization as a pure-function combinator: the `⊥`-row license, opt-in because space↔time is a resource EFFECT"
description: "memoization = a resource EFFECT (space↔time trade), opt-in; a library memo combinator over ⊥-row fns"
status: open
area: effects
ties: ["Q27", "Q30", "Q31", "ADR-0027", "ADR-0030"]
see-also: ["#48"]
---
**Question**: should BANG offer memoization (cache a recursive/pure function's results)? If so, what is
the CORRECT, least-intrusive shape, and is it opt-in or opt-out?

**Why it matters** — recursion (esp. `let rec`) invites it (fib, DP), and it's a natural test of the
"paradigm/runtime are values" thesis: is caching a language feature or a library value? The answer
threads the effect row, #48, and the quotient/refinement work (Q31).

**The load-bearing reframe (operator's):** *exchanging computation time for memory space is an
OBSERVABLE EFFECT* — a **resource effect**. That is the whole argument in one line: memoization is not
"pure with a hidden cache," it TRADES an unbounded, observable memory cost for speed, and observable
costs are effects, and **effects are opt-in / tracked** (like mutability, ADR-0030). This mirrors `Div`
exactly: `Div` makes *time-might-not-terminate* type-visible; a memo cache is *space-grows* — both are
RESOURCE effects the type system could name. (Possible deep form: a `Space`/`Alloc` effect in the row,
so the trade is type-visible — same move as making `Div` visible, #46/#47.)

**Correctness precondition — purity, which the effect row already tracks:**
```
f : A -> B ! ⊥        (pure — empty row)   →  referentially transparent  →  SAFE to memoize
f : A -> B ! {state}  (effectful)           →  caching DROPS the effect    →  UNSAFE
```
The effect row IS the license ("constraint is generative"). Consequence of #48 (recursive bodies must
be pure today): **every current `let rec` is unconditionally memoizable.** `Div` does NOT break it — a
pure-but-partial fn is still RT (cache terminating results; diverging inputs cache nothing).

**Correct BY CONSTRUCTION (not by discipline):**
```
memo : [DecEq A] => (A -> B ! ⊥) -> (A -> B ! ⊥)
```
`memo` accepts ONLY a `⊥`-row function → handing it an effectful fn is a TYPE ERROR, not a runtime bug.
Unsound memoization is unrepresentable (SOUL). Extra preconditions: **decidable equality on `A`** to key
the cache (⟹ first-order args only — functions/thunks have no decidable eq); over a QUOTIENT `A/~`, key
on the quotient's equality — `Quot.lift` guarantees `f` respects `~`, so quotient types (Q31) compose
cleanly.

**Least-intrusive shape — a combinator, not a keyword (the thesis):** runtime/eval-strategy is a VALUE,
and memoization is an eval strategy. So: a library `memo` (a handler over pure fns) — cache = STM/`TVar`
(mutable but ENCAPSULATED, invisible behind a pure interface), purity gate = the row, key = `DecEq`. NO
new primitive, NO new syntax (invariant #5). Subtlety for it to actually speed up RECURSION: the cache
must sit INSIDE the recursion (recursive calls hit it), so `memo` composes with the `let rec` FIXPOINT
(the Landin's knot ties its self-reference through the cache) — a `memoRec` / `let memo rec`, still a
combinator over the fixpoint.

**Opt-in / opt-out**: **OPT-IN.** By the reframe: the space↔time trade is a resource effect, effects are
opt-in, so caching is opt-in — the caller declares `memo f` (config explicit at boundaries). Auto-memo
would silently accrete unbounded caches → surprising `oom` (a "surprising default is a latent bug" +
invariant #7, performance second-class). Aligns with immutable-default / mutable-opt-in: the cache is
opt-in mutability, and immutability-by-default is what makes it safe (nothing else aliases/invalidates
it).

**Options**: (1) **library `memo`/`memoRec` combinator, opt-in** (recommended — on-thesis, no kernel
change, correct-by-construction via the `⊥`-row type). (2) auto call-by-NEED thunks (per-thunk value
caching as an eval-strategy handler — a WEAKER, orthogonal automatic caching; distinct from function
memoization). (3) a type-tracked `Space`/`Alloc` resource effect so the trade is type-VISIBLE (the deep
form; parallels `Div`). (4) no memoization (users hand-roll with a `state`/STM cache).

**Recommended**: (1) as the near-term library shape when perf on pure recursion bites; keep (3) on record
as the principled deep form (resource effects in the row). Post-v1 — needs `DecEq` (⟸ polymorphism /
type classes, ADR-0027) and ideally the fixpoint-composition ergonomics.

**Blocked on**: `DecEq`/type-class machinery (ADR-0027 polymorphism); the `let rec` fixpoint exposed
enough to compose a cache through it. Both post-v1.

**Revisit signal**: perf pressure on pure recursion (DP, repeated pure calls); OR taking up resource
effects / grades (Q27, Q30 FBIP — the sibling space-accounting question); OR when `DecEq` lands with
polymorphism.
