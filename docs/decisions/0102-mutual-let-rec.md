# ADR-0102 · Mutual `let rec … and …`: H2 tuple-of-thunks μ-knot (#97 item 2)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: `let rec f : T1 = e1 and g : T2 = e2 … in body` generalizes ADR-0073's single-function
  self-knot `Rec = μX. Thunk(X → T)` to an N-tuple self-knot `Rec = μX. Thunk(X → T1 * T2 * … * Tn)`
  every sibling shares — each sibling forces the SAME knot and projects its own slot, giving mutual
  visibility by construction, not textual ordering. No new kernel primitive (invariant #5 holds —
  same elaborator-level move as ADR-0073's own `buildLetRec`). Every sibling requires its own
  mandatory type ascription (ADR-0073's rule generalized: HM cannot break the mutual circularity
  without one). Every mutual group conservatively carries `Div` (`structOK` is not extended to
  certify a co-recursive name set — a documented, deliberate scope cut, not an oversight). Rejects
  the alternative H1 (a Bekić-style sum-dispatcher folding the group into ONE `let rec`) on two
  independent, build-confirmed walls: constructor/generic-type arity ≤ 2, and `Div`-row
  all-or-nothing certification that would make the sugar strictly worse than today's nested-`let
  rec` workaround for any mixed structural/non-structural group. Scope: EXPRESSION-LEVEL ONLY
  (`let rec … and … in body`) — the top-level DECL form (`let rec f : T1 = e1 and g : T2 = e2`, no
  trailing `in`, ADR-0093 D5's shape) is explicitly OUT of this ADR's scope; it needs a genuinely
  new multi-name `Decl` variant (touching `Decl.name`'s single-name contract, module qualification,
  `pub` export bookkeeping — 8-10 real sites, not a pass-through extension), tracked as a follow-up.
- **Resolves**: #97 item 2
- **Depends-on**: 0073 (the single-function μ-knot this generalizes), 0091 (the `structOK`
  extension-point precedent this ADR declines to take), 0071 (Pratt rule-table / `pApp` stop-list
  discipline — the `and` keyword-swallowing fix follows the SAME lesson as `with`/`resume`)

## Status

Accepted (2026-07-11). Landed on branch `feat-mutual-rec`. Preceded by a refute-first design probe
(`docs/notes/mutual-rec-design.md`, branch `design-mutual-rec` off `main @ f03cbad3`) that ruled H1
refuted and H2 spike-verified before any implementation work began.

## Context

BANG's only recursion form (ADR-0073) is a SINGLE self-referential `let rec f : T = <fun> in body`.
A genuinely mutual pair — `even`/`odd`, a parser's `factor`/`term`/`expr` tower, a lexer/parser
co-routine — has no direct expression today; the existing workaround is either (a) hand-fuse the
mutual functions into ONE function carrying a dispatch flag (correct but obscures the natural
two-function shape and burdens the AUTHOR with the fusion), or (b) nest one `let rec` inside
another's body, which only lets the INNER function call the OUTER (never the reverse) — genuine
mutual visibility (both directions, simultaneously) is unreachable by nesting alone. Issue #97 item
2 tracks this gap; the design note (`docs/notes/mutual-rec-design.md`) is the refute-first probe
that resolved which encoding to adopt before any grammar/elaborator work started.

## Decision

### 1. Surface: `and`-chained siblings, script-mode only

```
let rec f : T1 = e1
    and g : T2 = e2
    and h : T3 = e3
in body
```

Each sibling repeats `name : Ty = <fun>` — the IDENTICAL head shape a single `let rec` already
requires (ADR-0073's mandatory ascription). Zero `and`s parses to the EXISTING `.letRecS` node,
UNCHANGED (no behavior change to any existing program); one or more `and`s parses to a NEW
`.letRecMultiS` node carrying a `LetRecBindings` sibling list (a `Surf`-mutual list, the
`LetBindings`/`DArms` precedent — keeps `Surf`'s `DecidableEq`/`Repr` derivations structural).

A genuinely new keyword-swallowing bug surfaced building this: `pApp`'s application-fold loop had no
`and` in its stop-list, so `fun n => n` immediately followed by `and g : …` silently folded `and`/`g`
into the application spine as bare-identifier ARGUMENTS (`(fun n => n) and g`) before the `and`-chain
parser ever ran — the exact #26-class lesson `pIdent`'s own `with`/`resume` reservation comments
already document: an operation/keyword form needs its terminator reserved at EVERY loop that could
swallow it, not just where the form is introduced. `pApp`'s stop-list now includes `and`; `and`
itself stays an ORDINARY, non-globally-reserved identifier everywhere else (the SAME contextual
disambiguation `rec` itself already uses — `rec` is not in `pIdent`'s reserved-word list either,
only recognized positionally after `let`).

The top-level DECL lookahead (`isLetDecl`, ADR-0093 D5's script-vs-decl disambiguation) was
similarly extended to short-circuit on `and` the same way it already does on `;`/`in` — seeing `and`
right after a `let rec` head's first sibling is exactly as decisive as seeing `in`: it can ONLY be
the script-mode `and`-chained form (the top-level decl form has no `and` analogue, this ADR's own
scope cut, §5 below).

### 2. Elaboration: the H2 tuple-of-thunks μ-knot

Generalizes `buildLetRec`'s single self-knot to an N-tuple:

```
Rec  = μX. Thunk(X → T1 * T2 * … * Tn)          -- the shared self-knot's type (right-nested product)
knotBody sv = let #g = unfold sv in (force #g) (fold #g)     -- BYTE-IDENTICAL to buildLetRec's own
                                                                 (the #95 knot-sharing fix, inherited
                                                                 verbatim — see §3)
sibThunk i sv = let #p = force (thunk (knotBody sv)) in
                  <right-nested splitS projecting slot i> in
                    force <the projected slot>              -- MUST force (the CBPV trap, §4)
```

Each sibling's OUTER (call-site) binding is a BARE `.thunk`, `.annotS`-ascribed against its own
declared `Thunk Ti` — mirroring the H2 spike's verified shape exactly (`evenThunk`/`oddThunk` in
`scratch/H2Spike-VERIFIED-GREEN.lean`, both inner and outer bindings ascribed). The pair VALUE
itself (inside the knot's self-referential lambda) is ALSO `.annotS`-wrapped at its own
construction site against the product type — not left to the generic type-checking catch-all (§4).

### 3. `Div`-row placement mirrors ADR-0073 exactly

The INNER knot (every sibling's re-derivation thunk inside the self-referential lambda) stays PURE;
EVERY sibling's OUTER (call-site) thunk is `divMark`-wrapped when the group's row is nonempty —
`buildLetRec`'s own "Div rides the outer knot only" placement (ADR-0073 §2, Option A), generalized
per-sibling. `elabS`'s `.letRecMultiS` arm unconditionally passes `{Div}` as the group's row —
`structOK` (ADR-0091's own extension point) is NOT extended to certify a co-recursive NAME SET.
`structOK`'s call-recognizer (`callSpine`) is keyed on a SINGLE function name and cannot attribute
one sibling's calls to another sibling's descent argument; making mutual structural certification
work needs a group-level co-recursive name-set threaded through `callSpine`/`structOKSpine` — a
real, bounded extension, deliberately deferred (not attempted here). Every mutual group defaults
conservatively to `Div` on every sibling, sound per `structOK`'s own "default false" discipline —
this is a known COMPLETENESS gap (a group with an entirely-structural membership still pays the
`! {Div}` annotation tax today), named explicitly rather than silently regressed.

### 4. Two traps found only by building, both now permanent regression guards

- **The CBPV double-thunk trap.** Projecting a sibling's slot and returning it DIRECTLY
  (`splitS … in #slot`, no `force`) types "fine" at each isolated sub-step — the checker's
  structural unification silently accepts a `U (U ρ arrow)` thunk-of-a-thunk mismatch — but runs to
  `STUCK`. Fix: `force` the projected slot before returning, made structural in `sibThunk` so no
  future N-way caller can omit it.
- **The unification-vs-subsumption trap (found live during implementation, NOT anticipated by the
  probe's spike — the spike never exercised a `Div`-declared LEAF sibling).** A sibling that never
  references any name in the mutual group (a legitimate, common shape — a mutual group's base case
  can be a simple leaf) failed `effect row mismatch` even though its declared `! {Div}` bound
  strictly ADMITS its own (emptier) actual row. Two stacked causes: (a) the elaborator's per-sibling
  function-body annotation used the RAW, unresolved `Ty` from the parse tree instead of the resolved
  form used everywhere else in the same knot; (b) once (a) was fixed, the pair-VALUE's outer type
  ascription still forced the checker's generic catch-all path (`synthSC` + `unifyC`), whose `.U`
  (thunk) arm does EXACT row equality with no subsumption — unlike the checker's explicit `.annotS`
  arm, which correctly applies `subRow` (declared bound ⊇ actual). Fix: `.annotS`-wrap the pair
  value at its OWN construction site so the subsumption-aware path is the one that runs. Both fixes
  are narrow and now carry permanent `#guard` regressions (a leaf-sibling case, and an N=3 fully-
  cyclic case, `Bang/Frontend/TypeCheck.lean`'s ⑨j′ validation section).

### 5. Scope cut: expression-level only

The top-level DECL form is explicitly OUT of this ADR. `Decl.name : Decl → String` returns exactly
ONE name per declaration today; a mutual top-level decl group needs N names, each independently
`pub`-able and independently module-qualifiable — genuinely new machinery (`moduleTopNames`,
`qualifyDeclName`/`qualifyDeclBody`, `firstPrivateDotAccess`/`firstBareOpCall`'s per-decl
enumeration, `pubNames` bookkeeping), not a pass-through extension of the ~10 sites this ADR's
expression-level form already touched. Tracked as an explicit follow-up, not silently dropped.

## Rejected: H1 (Bekić-style sum-dispatcher)

Fold an N-way mutual group into ONE `let rec` over a sum-typed dispatcher `go : (Args₁ + … + Argsₙ)
→ (Res₁ + … + Resₙ)`, with injected per-function callers. REFUTED on two independent,
build-confirmed walls (either alone is sufficient — no spike built beyond confirming both):

- **Constructor/generic-type arity ≤ 2 (`B011`).** An N-way dispatcher needs an N-way argument sum
  AND an N-way result sum; bang's constructor payload arity is capped at 2 (`data T = C(Int, Int,
  Int)` → `error[B011]: payload arity ≤ 2 in v1`), forcing nested-tuple encoding of the sum itself —
  and issue #108 (open at probe time, build-confirmed live) means bang constructor names are not
  type-namespaced, so any fresh dispatcher-sum ctor name a desugar mints collides with the SAME
  desugar's ctors from another mutual group, or a user's own same-named type.
- **`Div`-row all-or-nothing certification.** `Div` is a single boolean fact per KNOT
  (`buildLetRec`'s `if divLabel ∈ recRow then …`), computed once by `letRecRow`/`structOK`. Folding
  N functions into ONE `let rec` forces ALL N to share ONE certification verdict — if even one
  sibling is non-structural (the common case; a parser's `factor`/`term`/`expr` tower is rarely
  uniformly structural), the whole group falls to `Div`, including siblings that as SEPARATE `let
  rec`s would certify total today. This makes the sugar STRICTLY WORSE than the existing nested-
  `let rec` workaround for any mixed-membership group — a real completeness regression, not an
  implementation inconvenience.

H2 (adopted) sidesteps both: the tuple-of-thunks encoding uses the BUILT-IN product type
(`tProd`/`pairS`/`splitS`), never a fresh `data` declaration, so it never touches the ctor-arity cap
or #108's namespace collision at all — H2's main structural advantage over H1.

## Consequences

- No kernel change (invariant #5 holds — five primitives, elaborator-only).
- A mutual group's completeness ceiling matches today's single-function `let rec` (`Div`-fallback,
  fuel-bounded execution) — this ADR does not change the totality story, only the SURFACE.
- The `structOK` group-certification extension (§3) is real future work with a known shape
  (co-recursive name set threaded through `callSpine`), not a design dead end.
- The top-level decl form (§5) is real future work with a known shape (a multi-name `Decl` variant),
  not a design dead end.

## Revisit if

- `structOK` gains group-level co-recursive descent certification — some mutual groups could then
  drop `Div` (the completeness gap named in §3 closes).
- The top-level decl form is picked up — needs its own ADR (a genuinely new `Decl` shape, not an
  amendment to this one).
- A future N-way group's right-nested product depth becomes a real performance concern — the current
  encoding's projection cost is O(N) `splitS`s per sibling access, matching the ordinary tuple-
  projection cost anywhere else in the language; no evidence of this being a problem at v1 program
  scale, flagged only as a place to look if it ever is.
