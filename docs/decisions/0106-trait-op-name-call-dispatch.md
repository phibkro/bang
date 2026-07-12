# 0106 — trait-op name-call dispatch (#78 operator ruling)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: #78 (trait ops were operator-dispatch-ONLY — `env.insts` consulted exclusively at
  the `.binopS` arm, a bare name-call like `show(x)` was `unbound variable`) is ruled: **option
  (a), extend dispatch to name-calls, user-binding-wins (LEXICAL shadowing)**. An application whose
  head names a trait op consults `env.insts` the same way `.binopS` already does (the `#118`
  one-candidate-pins-the-hole precedent, reused verbatim); `c` resolves through the ORDINARY
  environment (`Γ`) FIRST, so a user's own `let`/`let rec`/lambda-param binding of the same name
  wins unconditionally — no implicit capture (ADR-0005/0006's own rule, generalized to trait-op
  names). Unlocks `deriving (Show)` for its ONE fully-working shape (an all-nullary carrier) and
  every future non-operator trait op (Hash, ADR-0082's Functor/Monad auto-derive). A SEPARATE,
  PRE-EXISTING `#112`-vintage knot-scoping wall (found, not fixed, this session) still blocks
  `Show`/any hand-written impl whose op body calls ANOTHER top-level binding — see §5.
- **Depends-on**: #74 (the diagnosis that exposed the fork), #112 (the knot-dispatch mechanism this
  generalizes), #118 (the one-candidate-pins-the-hole precedent), ADR-0005/0006 (no implicit
  capture — the lexical-shadowing rule this ruling extends)
- **Date**: 2026-07-12
- **Deciders**: operator (Frontend lane, #78 ruling on the issue)
- **Ties**: docs/notes/traits-prelude-survey.md (the census that flagged Show/Hash as "GATED #78"),
  #128 (the type-qualified-ctor-name derive lesson `showFoldBody` reuses)

## Context

#78 found trait ops dispatch EXCLUSIVELY through the `.binopS` overload arm — `env.insts` (the
elaborator's instance table) was never consulted anywhere else. A trait op with a genuine NAME
(not an operator symbol — `show`, `hash`, a future `Functor.fmap`) had no execution path at all:
calling it by name (`show(x)`) was a bare `unbound variable`, confirmed live and reported by the
stdlib-tier-2 lane, which stopped `deriving (Show)` honestly on this exact wall rather than ship a
derive that can't be called.

#78's own issue text named the fork precisely: (A) keep operator-only (document it); (B) extend
dispatch to name-calls (a convention decision: tupled vs curried args, lexical-shadowing vs
trait-wins); (C) park until Stage-7/Q38 forces the same convention question for effect ops. Park
was the 2026-07-11 default; this ADR records the follow-up ruling once Stage-7 landed without
actually resolving #78 (a gap the carrier-inference lane's own report surfaced).

## The decision

**Option (a): extend dispatch, user-binding-wins.** `elabS`'s `.app (.var c) a` arm — the SAME arm
that already resolves ctor-intro (`Cons(h,t)`) — gains a THIRD case, after ctor resolution fails:

1. **Lexical shadow check first.** `Γ.any (fun (n,_) => n == c)` — if `c` is bound in the ordinary
   (local + folded-in-top-level-let) context, dispatch is skipped entirely; `c` resolves as an
   ordinary application, exactly as if trait dispatch never existed. This is the ADR-0005/0006 "no
   implicit capture" rule applied to a NEW name-resolution site — a user's own `showIt` always wins
   over a same-named trait op, matching every other scoping rule in the language.
2. **Candidate collection.** `env.insts.filter (opName == c && params.length == 1)` — SINGLE-ARG
   only (the surface shape `.app (.var c) a` reaches; a multi-arg name-call like `eq(a, b)` is out
   of this arm's scope, already covered by `.binopS`'s own `==` overload).
3. **Type-directed resolution.** The argument is A-normalized (#41) and its type synthesized;
   candidates are filtered by `target == τ` (mirroring `.binopS`'s `dispatchInst τ`). Zero
   candidates ⟹ `c` names no trait op at all, DEFER to the checker's ordinary "unbound variable"
   (never a guess). One candidate ⟹ dispatch. Two+ candidates targeting the SAME `τ` ⟹ refuse loud
   (a genuine duplicate-impl program, never silently pick one).

**The `#112` knot generalization this needed.** `.binopS` only EVER dispatched exactly 2 params, so
the `#112` self-/backward-reference fix (`PendingOpKnot`, `wrapPendingKnots`) only ever built an
arity-2 tupled knot. Name-call dispatch reaches arity 1 too (`show(x)`), and a 1-ary op recursing on
its own carrier's tail (`show`'s recursive-field case, `total`'s self-recursive fold) hits the
IDENTICAL splice-vs-knot wall `#112` closed for arity 2 — reachable for the first time because
dispatch can now REACH that arity. `PendingOpKnot`/`wrapPendingKnots` are generalized from a
hardcoded `p1`/`p2` pair to `params : List String` (any arity ≥1): a 1-ary knot binds its param
directly (no tupling, `T -> RetTy`); 2+-ary right-nests via `prodOfTys`/`bindPayload`'s own N-ary
convention (#144's own generalization, reused verbatim). Arity 0 stays on the pre-`#112` splice
path (no `Self`-typed param to knot-bind).

## Witnessed (compiled corpus, `Bang/Frontend/TypeCheck.lean` Validation ⑨q/⑨r)

- A hand-written 1-ary `impl ShowT for Box { fn showIt(x) = … }`, called bare (`showIt(B(42))`) →
  `42`. RED before this ADR (confirmed live pre-fix).
- Lexical shadowing: a user's own `let rec showIt : Int -> Int = …` wins; the SAME bare call now
  resolves to the user's binding, not the trait impl.
- Self-recursion on a recursive carrier through the SAME name-call + generalized knot (`total`, a
  1-ary op recursing via `total(t)` on `MyList`'s own tail) → `6` for a 3-element list.
- `deriving (Show)` on an all-nullary carrier (`data Color = Red | Green | Blue`) → works end to
  end (`show(Red)` renders `"Color_Red"`, the #128 type-qualified-ctor-name convention).

## §5 — the binder-nesting wall (CLOSED, issue #139)

`deriving (Show)` on ANY carrier with a non-nullary ctor failed to ELABORATE AT ALL — not just at
the non-nullary call site. `show`'s ONE generated knot covers every ctor arm in a single `matchD`;
a `$concat`/`intToStr` reference ANYWHERE in that fold (needed to render a field or join a ctor's
name with its payload) poisoned the WHOLE knot, even for a call that only ever hit an unrelated
nullary arm (confirmed live at the time: `data Wrap = W(Wrap) | End deriving (Show)`, calling ONLY
`show(End)`, still failed `unbound variable 'concat'`).

**Root cause** (confirmed on a HAND-WRITTEN impl with zero derive/Show involvement):
`impl Eq for Box { fn eq(a, b) = $eq "x" "x" }` (calling the PRELUDE's own `eq`, nothing to do with
`Show`) failed `unbound variable 'eq'`. `wrapPendingKnots`'s knot was `letRecS`-wrapped OUTSIDE the
program's own top-level let-chain (`foldedBody`, built by `elabProg`'s `foldLetDecls`) — so a
knot's OWN body was elaborated in a scope that had NOT yet descended into `foldedBody`'s nested
lets, meaning a knot's op body could NEVER see another top-level binding, prelude alias or user
function, regardless of arity. This was a `#112`-vintage gap (the ORIGINAL 2-arg knot mechanism had
always had it) that stayed invisible until this session: `Eq`/`Ord`'s generated fold bodies only
ever call the binop itself (`==`/`<`), never a prelude function; `Show`'s field-rendering was the
FIRST derive whose generated body genuinely needed to.

**Fix (#139, landed this session).** `foldLetDecls` now knot-wraps EVERY `letD`/`letRecD`'s OWN
right-hand side (not just the trailing `tail`), index-scoped so a decl only sees knots whose
originating `impl` came textually BEFORE it (`PendingOpKnot.declIdx`, mirroring the forward-only
visibility ordinary sibling `let`/`let rec` decls already have). Two load-bearing companion fixes
were needed for the index-scoping to be SOUND, not just plausible: (1) `buildEnv` is now called on
`prelude ++ p.decls` (not the pre-filtered `prelude ++ nonLetDecls`) so `PendingOpKnot.declIdx`
indexes the SAME list `foldLetDecls` folds — the two functions previously read TWO DIFFERENT,
silently-misaligned index spaces; (2) `expandDerives` now splices each derived `impl` right AFTER
its OWN `data` decl (was: appended at the very end of `p.decls` regardless of where `deriving(…)`
textually sat), so a derived knot's `declIdx` reflects where the carrier is DECLARED, not where
the LAST `deriving` clause in the file happens to land — both PREPENDING wholesale (breaks
`buildEnv`'s own "impls resolve after their target `data`" ordering) and APPENDING wholesale (put
the derived knot's `declIdx` after every ordinary top-level `let`, including ones that dispatch to
it) were tried and refuted live before the per-`data`-decl splice. Witnessed: the hand-written
`Eq`/`abs` repro above now runs to `42`; `data Pair = Mk(Int,Int) deriving (Eq)` + a LATER `let
main = if Mk(1,2) == Mk(1,2) then 1 else 0` (a library-mode program — exactly the shape that
regressed under an earlier, less-careful cut of this fix) now runs to `1`; the ADR's own worked
`Wrap`/`show(End)` repro above now runs to `"Wrap_End"`, and the RECURSIVE arm
`show(W(End))` self-recurses through the knot to `"Wrap_W(Wrap_End)"` (`structOK` correctly
certifies the self-call). A separate `concat2`-shape bug in `showArmBody` (calling curried
`concat : Str -> Str -> Str` as if it took ONE paired argument) was ALSO fixed in the same landing
— unrelated to the binder-nesting wall, but blocking the exact same corpus program.

## §6 — the row-admission wall this fix does NOT close (STOP-and-SHOW, item 2's scope)

`deriving (Show)` on a carrier with an `Int` FIELD (e.g. `data Box = B(Int) deriving (Show)`) still
fails — now with `thunk body performs {Div}, exceeding its declared bound {}`, a DIFFERENT error at
a DIFFERENT layer than §5's `unbound variable`. Widening `Prelude.bang`'s `trait Show { fn show(a)
-> Str … }` to `-> Str ! {Div}` has ZERO effect on this (confirmed live) — a knot's admitted row is
governed ENTIRELY by `letRecRow`'s `structOK` self-recursion certifier (ADR-0091), never by the
trait signature's own declared row. `showIt`'s generated body calls `intToStr`/`concat` (both
themselves `Div`-rowed via THEIR OWN self-recursion) but `structOK`'s check on `#opknotN`'s OWN
body sees no SELF-recursive call for a leaf `Int` field, so `letRecRow` returns `∅` regardless of
what the trait declares — the row-admission machinery and the surface row-annotation are two
DISJOINT systems today. Fixing this needs either (a) `structOK`/`letRecRow` widened to admit `Div`
when the body calls an EXTERNALLY `Div`-rowed function (not just on self-recursion), or (b) the
trait's declared row genuinely threaded into the knot's admitted bound at `buildLetRec` — either is
a typing-rule-adjacent change to `ADR-0091`'s own mechanism, STOP-and-SHOW territory, not attempted
here. The RECURSIVE-carrier case (§5's `Wrap`/`show(W(End))`) does NOT hit this wall — a genuine
self-call through `show` certifies fine under `structOK` as-is; only a call to an UNRELATED
Div-rowed prelude function (never itself the knot's own name) is blocked.

## Rejected / staged

- **Multi-arg name-call dispatch** (`eq(a, b)`-shaped, tupled args) — out of THIS arm's scope;
  `.binopS` already covers the 2-arg case via `==`. A future name-callable multi-arg op (not yet
  named by any corpus need) would need its own surface-parsing decision (tupled call syntax at a
  bare name-call site is not what `.app (.var c) a` parses today).
- **Trait-wins shadowing** (a trait op always dispatches, a same-named user binding is shadowed) —
  REJECTED: violates ADR-0005/0006's "no implicit capture" invariant, which this ruling extends
  rather than carves an exception into.
- **Deferring `#78` further** (option C, re-park) — REJECTED: Stage-7 landed without forcing the
  same convention question #78 needed, so parking further had no natural resolution point left.

## Consequences

- `Bang/Frontend/DiagCodes.lean` gains no NEW code for the dispatch extension itself (it reuses
  `.binopS`'s existing multi-candidate refusal SHAPE, inline, not registry-tracked) — a follow-up
  if agent-facing `bang explain` coverage is wanted for the ambiguous-name-call message.
- `PendingOpKnot`'s `p1`/`p2` fields are GONE (replaced by `params : List String`) — an internal,
  non-public-API shape change; no external caller depended on the old field names.
- Every existing `Eq`/`Ord` derive + hand-written 2-param impl is UNCHANGED (the arity-2 knot path
  is byte-identical in behavior, only its internal representation generalized) — confirmed via the
  full example battery + existing corpus `#guard`s, zero regressions.

## Revisit if

The §5 wall is taken up (a `wrapPendingKnots`/`elabProg` binder-nesting redesign — kernel-engineer
or operator territory); OR multi-arg name-call dispatch is genuinely needed (a real program wants
`eq(a, b)` bare, not just `a == b`); OR #78's Hash/Functor-derive follow-ons surface a convention
question this ruling didn't anticipate.
