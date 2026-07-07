# ADR-0081 · Annotation-free generic-data introduction — a generic constructor is a polymorphic function; its instantiation is inferred from field types by HM over a template μ

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Generic-data INTRODUCTION becomes annotation-free (lifting ADR-0079's staged annotation-driven limitation, the #50-successor #55). A generic constructor IS a polymorphic function (`Some : ∀a. a → Option a`); in SYNTH position the checker INFERS its instantiation from the FIELD types via ordinary HM (the IVTy/ICTy machinery), NOT via `monoData`. Mechanism: the constructor carries a **template μ** (params left as markers `.tVar (paramBase+i)`); `embVInst` mints a FRESH hole per marker when the annotation is embedded; unifying the field expressions against the hole-carrying μ SOLVES the instantiation — concrete at a concrete use, a let-generalized hole inside a polymorphic function body. This is real HM over generic data; `monoData`/`Source.eval`/`HasCTy`/kernel stay UNTOUCHED (elaborate-to-mono). It unifies the annotation-driven (ADR-0079 check-mode) and annotation-free (synth-mode) paths into ONE mechanism.
- **Depends-on**: 0079, 0075
- **Relates-to**: #55 (closed by this), #50 (the tokenizer mono-limit → the parser-combinator #55 finding), the parser-combinator library (`examples/parser-combinators/` — the acceptance test, now GENERIC), the IVTy/ICTy re-rep (`b6c66a6`), Item 3 row-polymorphism (the residual)

- **Status:** Accepted (operator-approved 2026-07-07) — landed `a462728` (annofree)
- **Date:** 2026-07-07
- **Layer:** C + checker/elaborator (tested superset). Frontend LEAF (`TypeCheck`, fan-in 0); census byte-identical, kernel untouched.
- **Builds on:** ADR-0079 (generic data — this lifts its "Rejected/staged: annotation-FREE introduction"), ADR-0075 (elaborate-to-mono). It's ordinary HM constructor typing (a constructor is a function; application infers the type parameters) done over the IVTy/ICTy inference substrate.

## Context

ADR-0079 shipped generic data with ANNOTATION-DRIVEN introduction: a bare generic constructor in SYNTH
position failed loud ("annotate"), and you can't annotate with a type VARIABLE — so a generic combinator
(`map : (a→b) → Parser a → Parser b` building `Some((f a, rest)) : Option (b × Str)`, `b` a type var) could
not CONSTRUCT generic data. The parser-combinator library (the milestone acceptance test) pinned this
empirically as #55 (the #50-successor): the library was stuck monomorphic-in-result (`Int`). This ADR
records the fix + the mechanism + the residual.

## Decision

A generic constructor is typed as the polymorphic function it is, and its instantiation is INFERRED:

1. **Template μ + markers.** A generic decl's constructor carries its μ with the type params left as MARKERS
   (`.tVar (paramBase+i)`, a range above the rigid/hole bases and distinct from the μ-recursion vars). The
   monomorphic path is unchanged (no markers → byte-identical).
2. **`embVInst` mints fresh holes.** When the checker embeds the constructor's template annotation, it mints
   a FRESH IVTy hole per marker (`collectMarkers`/`substMarkers`/`embVInst`/`embCInst`). Unifying the field
   expressions against the hole-carrying μ SOLVES the instantiation — concrete at a concrete use,
   let-generalized inside a polymorphic function body. `elabS` emits `annotS (foldS (inj v)) template` for
   generic ctors, unifying the annotation-driven and annotation-free paths into ONE mechanism.
3. **Hole-preserving `unrollI`.** `ivShiftV`/`ivSubstV` mirror the kernel's `VTy.tyShiftFrom`/`tySubstFrom`
   IVTy-natively (byte-identical on hole-free types → safe drop-in). The old `extract→unrollMu→embV` FROZE
   holes into reserved tvars; the native unroll keeps them live for unification.
4. **The three elimination walls cleared** (parser-combinator findings): (a) construction-in-synth (above);
   (b) match through a higher-order parser — `matchD` recovers the scrutinee's data type from its ARM
   CONSTRUCTORS (`None`/`Some` ⟹ `Option`) and annotates the otherwise-unresolvable scrutinee with the
   template; (c) computation nested in a constructor arg — `splitS` invents `?A × ?B` for a hole scrutinee
   (elab binds placeholder holes, checker `.vhole ⟹ prod`), so `Some(($f) x)` needs NO let-bind fallback.

Payoff (build-verified): `Cons(1, Nil)`/`Some(5)` type + run with no annotation; the parser library is now
GENERIC — `mapP : (a→b) → Parser a → Parser b` reused at result `(Int×Int)` (`b ≠ a`), runs → 35
(`check-examples` 6/6). ADR-0079's negative `Cons(1,Nil)`-must-fail guard INVERTS by design (replaced with
6 positive guards).

## Rejected / staged (residual — NOT this ADR)

- **Infer-then-`monoData`** — rejected: it needs a CONCRETE element type, dead for a generic function body
  where the element is a hole. The template-μ + HM-holes approach handles both concrete and hole cases.
- **VALUE-generic combinators that COMBINE elements** (`andThen`/`many`/`firstVal` in the parser demo stay
  `Int`) — they fix the element via `+`/`0` (the arithmetic), not via generic-data construction. A
  value-generic `andThen : Parser a → Parser b → Parser (a×b)` is EXPRESSIBLE; left `Int`-shaped for the
  demo's numeric result. This is a demo choice, not a #55 wall.
- **Effect ROW-polymorphism** (a parser that's generic over its effect row) — the one genuine remaining
  frontier, orthogonal to #55: it's Item 3 (row variables), not generic-data introduction.

## Consequences

- Generic DATA is now fully first-class (introduction + elimination, annotation-free); `Parser a` and
  generic combinators are expressible. The tokenizer's #50 → the parser's #55 chain is closed.
- The elaborator stays TOTAL (no `partial`); kernel/census byte-identical (frontend-only diff, 16 headlines
  trusted-three).

## Revisit if

Value-generic combining combinators are wanted (`andThen → Parser (a×b)` — expressible now, just not in the
demo); OR effect row-polymorphism is taken up (Item 3) for parsers generic over their effect row.
