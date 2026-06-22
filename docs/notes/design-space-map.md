# Design-space map — the open language-design questions

> A survey of the design/semantics questions bang must answer, across the lenses: systems languages,
> pragmatic general-purpose languages, proofs-as-programs languages, DSLs. Companion to
> `OPEN_QUESTIONS.md` (per-question deferred *decisions*) — this is the *map* (what's open, what it
> costs, who the neighbours are). Established 2026-06-23.
>
> Status legend: ✓ decided (ADR/Q) · ◑ partially · ✗ unrecorded/open · ★ foundational (blocks the vision)

## Already settled (don't relitigate)

Rows-as-sets (ADR-0001); five primitives (invariant #5); QTT grades (Q2); de Bruijn (ADR-0020);
calculation-as-method (ADR-0009/0016); WasmFX target (ADR-0016); the convergence/ladder/staging
product decisions (PRD); resumptive state (ADR-0025). The **proof-power dial is now decided** —
**correctness is a dispatched ladder, kernel = semantics, checkers = pluggable** (ADR-0026). The
**tech-stack division + the total/partial stratification** are decided too — **verified core + tested
superset + explicit seam**, at the correctness, tooling, and language levels (ADR-0028; resolves the
meta-circular/totality wall via fuel-total or `Div`-tested `eval`).

## The big rocks (foundational — sequenced by the product ladder)

```
#  question                       bang's lean / status        closest neighbours           where
─────────────────────────────────────────────────────────────────────────────────────────────────
1  POLYMORPHISM + effect-row      ✓ STAGED — ADR-0027         Koka, Frank, Eff, OCaml 5,   Q17 →
   polymorphism                   (monomorphic v1 → HM →       Helium, Links                ADR-0027
   `map : (a →/e b) → …/e`        System F + rows + grades)    → HM forced at reuse/HOFs (rung 3+)
2  the PROOF-POWER dial           ✓ DECIDED — ADR-0026         F*, Liquid Haskell, Dafny,   ADR-0026
   (verify how much, how)         (dispatched ladder)          Verus / Agda,Idris,Lean / Granule
3  the LAWS surface (the moat):   ◑ mechanism decided          algebraic-effect eqns        Q19
   state + discharge a law        (assert + property test,     (Plotkin-Pretnar); lawful
                                  ADR-0026); SURFACE open      typeclasses; QuickCheck
4  DATA TYPES: ADTs, ind/coind,   ✓ RESOLVED — ADR-0029       Agda/Coq (ind/coind),        Q18 →
   how laws attach                (iso-recursive sum/prod/μ;   GADTs (Haskell/OCaml),       ADR-0029
                                  inductive; equi rejected)    ML (iso-recursive)
5  TYPECLASSES / traits + laws    ✗ — a class IS "ops + laws"  Haskell classes, Rust traits, Q19
   (ad-hoc poly, the moat link)   = the moat surface           Lean implicits, Coq canonical
```

**#2 is the keystone and it's decided (ADR-0026).** It cascades: #3/#5 (the laws surface) inherit the
ladder's "assert + property-test by default, climb on demand". **#1 is staged (ADR-0027** — monomorphic
v1, HM next, System F ambitious**)**. **#4 is resolved (ADR-0029** — iso-recursive ADTs**)**. So **all
four big rocks are now decided**; #3/#5 (the laws *surface*, Q19) remain partially open (discharge
decided via the ladder; user-facing law syntax still open).

## By lens (secondary — mostly deferrable, captured here not as individual Q's)

```
SYSTEMS                           bang today              neighbours                  status
──────────────────────────────────────────────────────────────────────────────────────────
memory: ownership / BORROWING     grades = linearity only Rust, Austral, Vale,        ✗ (grades give
  (not just 0/1/ω linearity)      (no aliasing/lifetimes) Cyclone regions, LinearHaskell  use-once, not borrow)
concurrency MEMORY MODEL          STM only; ordering?     C11/Rust MM, Promising sem.  ✗ (matters for xv6)
layout / representation control   "perf 2nd-class" (#7)   Rust repr, Zig, Terra        ✗ (tension w/ #7)
error model                       throws (effect) ✓       Result vs effects vs panic   ◑ (errors = effects)

PRAGMATIC GP                      bang today              neighbours                  status
──────────────────────────────────────────────────────────────────────────────────────────
type INFERENCE (+ grade infer)    annotation-heavy?       bidirectional (Dunfield-     ✗ (grade inference
                                                          Krishnaswami); HM+effects       is HARD)
MODULE system / packaging         none                    ML functors, 1ML, Backpack   ✗ (post-v1)

DSL / EXTENSIBILITY               bang today              neighbours                  status
──────────────────────────────────────────────────────────────────────────────────────────
user-defined CONSTRUCTS           effects+handlers = the  tagless-final, free monads,  ◑ (semantic DSLs
  (the "write your own")          DSL mechanism ✓         Racket, Eff                     ✓; surface syntax?)
METAPROGRAMMING / notation        principle decided:      Lean 4 macros, MetaOCaml,    Q20
  (pseudoinstructions, macros)    no primitive if         Terra, LMS, Racket           (mechanism open)
                                  composite (#5 invariant)
DISTRIBUTION ("where" axis)       §5 names it; D3 enables Unison (ships code!),        ◑ (CALM conjecture
  serializable thunks @ data      serializable closures   Bloom/CALM, Spark               in Distribution.lean)
staged DSLs (compile-away)        §5 / Q15                LMS (Rompf-Odersky), MetaOCaml  ◑ (Q15)
```

## Know our niche — the closest existing languages

bang's coordinate is the **intersection**: verified (proofs-as-programs) × multi-paradigm × systems.
Nearest neighbours, worth studying directly:

```
Granule   ★ graded modal types (linear + coeffect + effect grading) — the CLOSEST research language
            to the graded-CBPV substrate (Orchard, Liepelt, Eades). Study it.
Idris 2     QTT — bang already USES its grade calculus (Atkey/Brady). Not systems-focused.
F* / Low*   verified systems via DT+SMT, extracts to C (HACL*, EverParse) — the ladder's "verified" rung
Verus       Rust + SMT verification — the "Rust-like by construction" anchor
Austral     tiny linear-types systems language — the minimalist memory story
Unison      content-addressed, ships code over the wire — the at-the-data §5 vision, already real
Koka/Frank/Eff   row-typed algebraic effects + handlers — the effect-polymorphism reference (#1/Q17)
```

## Sequencing (what forces what)

```
rung 2 (verified stack)  forces →  #4 data types (Q18) + #3/#5 laws surface (Q19)
rung 3+ (reuse, HOFs)    forces →  #1 polymorphism + effect-row vars (Q17)
extensibility (any rung) wants  →  #metaprogramming (Q20) — but principle (no-new-primitive) is set
the secondary lens items →  ◊4/◊5/post-v1; deferred, mapped here so they're not lost
```
