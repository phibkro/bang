<!-- note-status: active -->
# `structOK` multi-arg / accumulator descent — design note (#50)

> Ground truth for extending the #47 structural-termination certifier
> (`Bang/Frontend/TypeCheck.lean:1608-1662`, current as of `52aa739`) past single-argument
> direct recursion. Written design-first per the operator's ruling: #48 (effectful recursion)
> is landed, closing issue #50's other half; this is the one remaining #50 sliver. No code in
> this unit — recommendation only, ADR-ready.

## 1. What the corpus actually needs (grounded in a real program, not a hypothetical)

The motivating case is `examples/tokenizer/main.bang`'s landing commit (`ce6d738`), whose own
message names the constraint precisely: *"a naive accumulator-threading tokenizer is multi-arg
⟹ Div, and #48 would then reject it… KEY MOVE: single-arg structural (recurse on the char-list
tail, build tokens RIGHT-TO-LEFT, char-prepend INLINED) so #47 certifies it TOTAL."* The shipped
tokenizer therefore does NOT exercise the gap — it was rewritten to avoid it. I reconstructed the
avoided (naive) shape and ran it against the current checker to confirm the exact failure, rather
than guessing:

```
data L = LNil | LCons(Int, L)
let rec sumAcc : L -> Int -> Int
  = fun xs => fun acc =>
      match xs { LNil -> acc, LCons(h, t) -> ($sumAcc) t (acc + h) }
  in ($sumAcc) (LCons(1, LCons(2, LCons(3, LNil)))) 0
```

`bang run` → `6` (correct, terminates). `bang repl :t` on the same program → `Int ! {Div}`
(NOT certified — the current default). This is the single pattern issue #50 point 1 names:
**accumulator-passing recursion where exactly ONE argument is the structural (`data`) subject
and the other(s) are non-structural (here `Int`) but bounded in shape by the subject** — the
accumulator never causes non-termination; it just isn't what's being matched.

I also tested the tuple-encoded equivalent (`sumAcc : (L * Int) -> Int`, single parameter,
destructured via `let (xs, acc) = p in …`) since v1 `let rec` only accepts ONE lambda parameter
(curried `fun x => fun y => …` bodies are rejected outright by `letRecRow`, see §2). Same result:
runs to `6`, types `Int ! {Div}`. So the gap is not "the parser can't spell two arguments" — it's
"the certifier doesn't recognize a subterm buried inside a bigger call-argument expression,"
whether that expression is a curried application or a tuple.

**What is NOT needed**, checked against the same corpus: a genuinely *lexicographic* pattern
(two structural arguments where either may decrease, Ackermann-style) does not appear anywhere in
the shipped examples or the tokenizer's own history — the real cases are uniformly "one data
argument descends, the other argument(s) accumulate a non-decreasing or monotonically-changing
non-data value (an `Int` counter, a growing `Str`/list accumulator)." This matters for scoping:
the corpus asks for **accumulator-passing certification**, not general lexicographic descent.

## 2. The certification rule, precise enough to implement

### 2a. Where the wall actually is (two separate rejections, not one)

1. **`letRecRow`** (`TypeCheck.lean:1728-1734`) rejects ANY curried body outright: `.lam _ _` inside
   the outer `.lam` (i.e., `fun x => fun y => …`) unconditionally returns `{divLabel}` without
   ever calling `structOK`. A multi-arg `let rec` written CURRIED never even reaches the
   structural check today.
2. **`structOK`** itself (`TypeCheck.lean:1647-1704`) tracks exactly one `matchable`/`subterms`
   pair, seeded from the single lambda parameter `[x]` (`letRecRow`'s `.lam x body` arm). Its
   call-site check (`.app (.force (.var g)) a`, line 1655-1658) only accepts a call argument `a`
   that is a BARE variable found in `subterms` — `match a with | .var v => subterms.contains v |
   _ => false`. A tuple-argument call (`($f) (t, acc+h)`) or a second curried argument
   (`($f) t (acc+h)`) never matches this shape, so it falls through to the generic `.app f a`
   arm (line 1659), which only checks `a` doesn't MISUSE `name` — it does not validate descent at
   all for a compound argument. Confirmed by the tuple-arg test above: it runs, but is silently
   NOT certified (correctly conservative — `structOK` never asserts `false` there, it just never
   reaches a `true` verdict through the single-bare-var path).

### 2b. The rule for accumulator-passing (the case the corpus needs)

Generalize `structOK`'s single-slot `matchable`/`subterms` to a **per-positional-argument**
version, where "argument" means "one component of whatever payload the recursive call passes" —
whether that payload arrives curried (`($f) a1 a2 … an`) or tupled (`($f) (a1, a2, …, an)`) is a
SURFACE distinction the certifier should treat identically (both desugar to the same
"n logical arguments" shape). Concretely:

- **Seed**: for a curried `let rec f : T1 -> T2 -> … -> Tn -> R = fun x1 => fun x2 => … => fun xn
  => body`, seed `n` independent `(matchable_i, subterms_i)` pairs, one per `xi`. For a
  single-tuple-parameter `let rec f : (T1 * T2 * … * Tn) -> R = fun p => let (x1, x2, …, xn) = p
  in body` (the ADR-0069 arity-≤-2 product-elim, `splitS`, generalizes the same way to n via
  right-nesting), seed identically from the `splitS` binders.
- **Descent obligation**: a recursive call `($f) v1 v2 … vn` (curried) or `($f) (v1, v2, …, vn)`
  (tupled) certifies iff **at least one** position `i` has `vi` a bare variable in `subterms_i`
  (a strict `data` subterm of `xi`) — a genuine STRUCTURAL decrease on that slot — AND **every
  other** position `j ≠ i` is *permitted to be non-descending*, subject to a shape restriction (2c)
  that keeps the check sound. This is "single-argument projection" descent: exactly one designated
  slot must strictly decrease each call; the rest ride along. It is deliberately NOT full
  lexicographic descent (no ordering/priority among slots, no requirement that a DIFFERENT slot
  decrease when slot `i` is unchanged) — see §4 for why that's the right cut for what the corpus
  needs.
- **Which slot is "the" descending one**: v1 does not need INFERENCE here — require the CALLER's
  every recursive call site to agree on the SAME slot index `i` (the common case: the tokenizer's
  and `sumAcc`'s subject is always argument 1). If different call sites descend on different
  slots, conservatively reject (stay `Div`) rather than build a multi-slot lattice — that is
  exactly the kind of "more machinery for a marginal completeness gain" the agent-first lens
  (ADR-0088's own framing) argues against; nothing in the corpus needs it.
- **Non-descending slots (`j ≠ i`)**: `vj` may be ANY well-typed expression in scope — a bare
  passthrough (`acc`), a computed update (`acc + h`), a different subterm, a literal. `structOK`
  should recurse into `vj` with its EXISTING generic rule (no `name` misuse, no re-binding) — it
  is not asserting anything about `vj`'s termination, only that it cannot smuggle a
  non-structural RECURSIVE reference to `f` itself. This is the same discipline the current
  generic `.app f a` arm already applies; it just needs to be reachable from inside a multi-arg
  call, not bypassed.

### 2c. Shadowing / curried-param interaction (the `let rec` gotchas apply directly)

Two hard-won facts from implementing #48 (memory `lang-bang-let-rec-stdlib-gotchas`, confirmed
again while reading `structOK`'s existing shadowing arms) constrain the extension:

- **Every binder shadows** (`shadowAdd`, line 1617-1619) — a curried lambda's SECOND parameter
  (`fun x1 => fun x2 => body`) is itself a NEW binder that must extend `matchable_2`/`subterms_2`
  from `[]`, exactly as `x1` does for slot 1, and any inner `let`/`match`/`fun` that re-binds `x2`
  must shadow slot 2's tracking the same way `structOK`'s existing `.lett`/`.lam`/`.matchS` arms
  already shadow slot 1's. The generalization is mechanical (thread `n` lists instead of 1
  everywhere `matchable`/`subterms` appear) but every shadowing site must be touched — a partial
  port that shadows slot 1 but forgets slot 2 is a SOUNDNESS bug (a re-bound `x2` whose new value
  is wrongly still trusted as "descends"), not just an incompleteness one.
- **A re-bound recursion NAME still refuses unconditionally** (`v != name` guards throughout) —
  unaffected by this extension; multi-slot tracking doesn't touch the `name`-shadowing check.
- **Curried params past the first need scrutinee ascription** in existing stdlib code (the
  `(b : Str)` idiom) — that is an ELABORATION-mode gotcha (bidirectional check-mode needs a type
  hint for a bare lambda parameter used in `anfSplit`), separate from `structOK`, which operates
  on already-parsed `Surf` before elaboration's HM layer runs. Not a blocker for this design, but
  worth flagging: a `let rec` with curried params reaching `structOK` at all requires `letRecRow`
  to stop rejecting the curried SHAPE first (§2a item 1) — which is itself gated by whichever
  fork §4 recommends, since `letRecRow`'s `.lam _ _ => {divLabel}` line is the FIRST wall, before
  `structOK` is ever consulted on a curried body.

### 2d. Tuple-argument descent (the second corpus shape)

For the `(T1 * T2 * … * Tn) -> R` single-tuple-parameter encoding: `structOK`'s existing
`.splitS a b p body` arm (line 1690-1694) ALREADY threads `matchable`/`subterms` correctly for a
2-way split of the recursion PARAMETER `p` itself (splitting `p` into `a`/`b` and re-adding them
as subterms when `p` was matchable) — that machinery is reusable almost as-is; the missing piece
is purely at the CALL-SITE check (§2a item 2: recognizing `($f) (v1, v2)` as a 2-slot call, not
falling through to the generic `.app` arm). No new shadowing logic needed here — `splitS`'s
existing shadow-and-conditionally-readd behavior already generalizes to the tuple encoding for
free once the call-site recognizer is extended.

## 3. Soundness posture — why false-certification stays impossible

`structOK`'s existing contract (its own doc comment, line 1637-1642) is **default `false`,
conservative by construction**: anything not manifestly structural stays `Div`. The extension
preserves this by construction, not by argument, for three reasons:

1. **No new TRUE-producing path bypasses the subterm check.** The only way a call certifies under
   the extension is: (a) the designated slot's argument is syntactically a bare variable, AND (b)
   that variable is in the CURRENT `subterms_i` set for that slot — the exact same "strict subterm
   of the tracked parameter, established only by matching/splitting a MATCHABLE scrutinee" logic
   `structOK` already uses for slot 1. Multi-slot tracking is `n` COPIES of an already-sound
   check, not a new inference. The non-descending slots (`j ≠ i`) are checked with the EXISTING
   generic recursion (no `name` misuse) — they never contribute a `true` verdict on their own,
   only a `false` (rejection) if they misbehave.
2. **The "same slot at every call site" rule (§2b) forecloses the one way multi-slot tracking
   COULD go unsound**: if call site A were allowed to certify via slot 1 descending while call
   site B certifies via slot 2 descending (independently), the WHOLE function is not
   well-founded by either single measure — a value could shrink on slot 1 at one call and stay
   fixed (or an unrelated `L` subterm) at another, forever, with slot 2 doing nothing to
   compensate (no lexicographic PRIORITY is being enforced). Requiring one globally-fixed
   descending slot keeps the well-foundedness argument IDENTICAL to the current single-arg proof
   (finite `data` depth on that one slot) — it is not a new termination argument, it is the old
   one applied to a parameter list instead of a single parameter.
3. **Adversarial-shape parity**: the existing five adversarial guards (`TypeCheck.lean:2995-3013`
   — reconstructed-value calls, unchanged-parameter calls, different-value-field calls, shadowed
   recursion names) each have a direct multi-arg analogue that the extension must reject
   identically (e.g. `($f) (Cons(h,t)) acc` — a reconstructed, not matched, structural argument —
   must stay `Div` on the designated slot exactly as `($f)(Cons(h, t))` does today). Any
   implementation must port all five adversarial guards to their curried/tupled form as part of
   the extension's own regression corpus — this note does not re-derive them since #47's existing
   proof of each case transfers verbatim (the SAME `matchable`/`subterms` tracking, just indexed).

The escape hatch that makes this safe to ship incrementally is unchanged: **missing a
terminating function costs nothing but a `Div` marker** (the function still runs, fuel-bounded);
only certifying a genuinely-diverging one is a soundness bug. The extension's failure mode if
some edge case is missed is "stays conservatively `Div`," never "silently wrong."

## 4. Recommendation — this IS a genuine fork; ADR-ready

Two live candidates, both sound, with a real cost/benefit difference — not mechanically forced:

**(A) Single-designated-slot descent (RECOMMENDED)** — §2b's rule: exactly one argument position,
fixed across all recursive call sites in the function, must be a strict subterm each call; other
positions ride free. Scope: certifies the tokenizer's avoided shape AND the tuple-accumulator
shape directly. Cost: `structOK`'s `matchable`/`subterms` becomes `List (List String × List
String)` (indexed by slot) instead of a pair — every shadowing arm needs the `n`-way
generalization (§2c), a real but mechanical diff, roughly proportional to `structOK`'s current
~55 lines. `letRecRow`'s curried-rejection (§2a item 1) must also lift for the curried surface
form specifically (the tuple form already reaches `structOK` today, just fails there).

**(B) Full lexicographic descent** (ranked slots, any slot may decrease as long as no
higher-priority slot INCREASES, Ackermann-style multi-measure well-founded orders) — REJECTED for
this unit, not foreclosed. No example in the corpus needs it (§1); it requires either a declared
priority ordering (more annotation surface, cutting against the agent-first "concise explicit
context" lens the same way ADR-0088 argued fixpoint-row-inference down) or an inferred one (a
search over orderings — real complexity for zero current payoff). Revisit if a genuine
lexicographic case surfaces (e.g., a two-list zip/merge where either list may exhaust first) —
nothing in (A)'s design forecloses layering (B) on top later, since (A)'s single-slot check is a
special case of (B) with a priority list of length 1.

**(C) Numeric well-founded measures** (`Nat`-floor descent, e.g. `f n → f (n-1)`, `n ≥ 0`) — OUT
OF SCOPE for this note entirely; already tracked as a SEPARATE deferred item in `structOK`'s own
doc comment and ADR-0073 §2's IMPLEMENTATION STATUS (blocked on Q31 — no `Nat`/floor type exists
yet, ADR-0067's `Int` is unbounded ℤ with no floor). Not part of issue #50's motivating cases
(the tokenizer's non-certified dimension is always a `data`-shaped accumulator or an `Int` counter
that is NOT the descending measure).

**Recommendation for the operator**: promote (A) to an ADR. It is a real, consequential design
choice (accept the `n`-slot generalization's implementation cost now vs. wait for lexicographic
need to materialize) with a named rejected alternative (B) and an explicit non-goal (C) — exactly
the ADR bar per CLAUDE.md ("a choice a future session could reasonably reverse or relitigate").
The ADR should freeze: the single-fixed-slot-across-call-sites rule (not inferred, not
per-call-site), the curried-vs-tuple surface parity (both reach the same certifier logic), and
that `letRecRow`'s curried-body rejection lifts ONLY when `structOK`'s multi-slot check actually
fires (never a blanket "curried let rec is now unconditionally allowed" — an uncertified curried
body should still fall back to `Div`, matching v1's `if structOK … then ∅ else {divLabel}`
pattern rather than becoming a NEW rejection class).

## Evidence

- `Bang/Frontend/TypeCheck.lean:1608-1662` (structOK, current), `1728-1734` (letRecRow, the
  curried-rejection wall), `1690-1694` (splitS arm, the reusable tuple-descent machinery),
  `2995-3013` (the five adversarial guards to port).
- `examples/tokenizer/main.bang` + its landing commit `ce6d738` (the avoided naive shape, quoted
  verbatim in §1).
- Manual repro (this session, `bang run`/`bang repl :t` on the reconstructed naive
  curried-accumulator and tuple-accumulator programs): both RUN correctly, both type `Int !
  {Div}` under the current checker — confirms the gap is exactly as issue #50 describes, not
  stale.
- ADR-0073 (`docs/decisions/0073-recursion-fix-div-let-rec.md`) §2's IMPLEMENTATION STATUS: names
  "multi-arg, lexicographic" as the two items #47 deferred, and separately tracks numeric
  measures behind Q31 — the three-way split this note's §4 (A)/(B)/(C) mirrors.
- ADR-0088 (`docs/decisions/0088-effectful-recursion-row-carrying-recursive-thunk.md`): the
  agent-first "declared, not inferred" precedent this note's §4 recommendation for (A)'s
  fixed-slot rule follows (reject a fixpoint/search-based alternative in favor of an explicit,
  simple rule, even at some completeness cost).
- Issue #50's 2026-07-09 re-scope comment: confirms the REUSE half (issue point 2) is resolved by
  `3fcdeba` (first-order) + ADR-0088/#48 (curried helpers calling into effectful/Div-carrying
  recursion, verified working end-to-end in this session's repro), leaving exactly the
  certification half (issue point 1) as this note's scope.
