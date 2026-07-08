<!-- note-status: active -->
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
meta-circular/totality wall via fuel-total or `Div`-tested `eval`). The **polymorphism ladder is now
SHIPPED** — elaborate-to-mono (ADR-0075): bite-0 HM → generic data (ADR-0079) → bounded traits (ADR-0080)
→ annotation-free intro (ADR-0081) → HKT Functor+Monad (ADR-0082) → prelude Option/Result + witnessed
isomorphisms (ADR-0083) → effect row-polymorphism (`cea8ae2`); the kernel stayed monomorphic + axiom-clean
throughout (the only Core touch was #57's free SSoT row-unifier consolidation).

## The criticality ladder — no-language → language, every fork ranked

The full pipeline of design forks, ranked by **reversal-cost × blast-radius** (kernel choices are
near-irreversible; syntax is a formatter away). The operating model: decide the fork upfront (ADR),
implementation paves the road between checkpoints. The meta-move that dissolves fork #3: pick ONE
root semantics and DERIVE the other presentations with agreement proofs (`Source.eval` root →
calculated machine → forward-sim'd WasmFX) — SSoT applied to semantics itself.

```
#   fork                                                        status
──────────────────────────────────────────────────────────────────────────────────────────
1   TRUST architecture — verified vs tested, the seam;          ✓ ADR-0026 (ladder) + ADR-0028
    internal Curry-Howard vs external vs solver-backed            (core/superset/seam)
2   SEMANTIC substrate — calculus, grades, thunk/force          ✓ graded CBPV · ADR-0007 ($-force)
3   semantics PRESENTATION + proof method — root + derivations  ✓ def-interp root, calculated
                                                                  machine (ADR-0009/0016), fwd
                                                                  sim (ADR-0035)
4   EFFECT discipline — monads vs rows+handlers vs caps;        ✓ ADR-0001 (rows-as-sets),
    dispatch semantics                                            ADR-0052–0063 (lexical-by-identity)
5   TYPE-power dial + polymorphism staging                      ✓ ADR-0026 · ADR-0027 · QTT (Q2)
6   TOTALITY seam — total fragment vs Div, how marked           ✓ ADR-0028 (Div in row + fuel)
7   COMPILATION architecture — target, hops, verified per hop   ✓ ADR-0016 (CalcVM → WasmFX)
8   DATA types — iso/equi-recursive, ind/coind                  ✓ ADR-0029 (iso-recursive)
9   LAWS/abstraction surface — traits + first-class laws        ◑ ADR-0040 mechanism; surface = #24
10  MEMORY/resource model — borrowing beyond 0/1/ω grades       ✗ post-v1 (Rust/Austral/Vale)
11  CONCURRENCY/runtime model — shared vs shared-nothing        ◑ multikernel direction (§ below);
                                                                  Q21 gates the Iris bill
12  MODULE system                                               ✗ post-v1 (ML functors, 1ML)
13  INFERENCE — esp. grade inference                            ◑ bidirectional ✓ (ADR-0066);
                                                                  grade inference ✗ (hard)
14  METAPROGRAMMING / notation                                  ◑ Q20 (no-new-primitive set)
15  SURFACE syntax / formatting                                 ◑ per tracer bullet; Q24
```

Open forks in priority order: **#9 (= #24 laws-surface, mechanism landed ADR-0068/0080) → #10 memory → #11/Q21 concurrency →
#12 modules → #13 grade inference**. The rank order ≈ the order the project decided them —
evidence the sequencing held.

## The big rocks (foundational — sequenced by the product ladder)

```
#  question                       bang's lean / status        closest neighbours           where
─────────────────────────────────────────────────────────────────────────────────────────────────
1  POLYMORPHISM + effect-row      ✓ SHIPPED — ADR-0075/0082    Koka, Frank, Eff, OCaml 5,   Q17 →
   polymorphism                   (elaborate-to-mono: HM →      Helium, Links                ADR-0075
   `map : (a →/e b) → …/e`        generic data → traits → HKT Functor+Monad → row-poly, `cea8ae2`)
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
ladder's "assert + property-test by default, climb on demand". **#1 is SHIPPED (ADR-0075/0082** — the whole
ladder landed `cea8ae2`: HM → generic data → bounded traits → HKT Functor+Monad → effect row-poly, all
elaborate-to-mono**)**. **#4 is resolved (ADR-0029** — iso-recursive ADTs**)**. So **all four big rocks are
now decided**; #3/#5 (the laws *surface*, Q19) remain partially open — the laws MECHANISM landed (ADR-0068
trait wiring + ADR-0080 bounded traits); user-facing law syntax still open.

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

## ★ Concurrency & the OS runtime model (post-v1; foundational for the xv6 north-star)

The vision endgame (xv6, rung 9) needs a **multicore execution model**. Two related, both
shared-nothing, both verification-friendly decompositions are on the table:

```
LOGICAL   actors-as-wasm-instances   `!` (actor-send) over a mailbox effect+handler (library,
                                      invariant #5); each actor = a separate wasm instance →
                                      separate linear memory = STRUCTURAL isolation
PHYSICAL  per-CORE wasm module        the MULTIKERNEL (Barrelfish, SOSP'09): treat the machine
          + coordinator               as a network of cores, NO shared memory, coordination by
                                      message-passing; OS state REPLICATED, not shared
```

**Why this is the right model for bang specifically (not just one option):**
1. Shared-nothing keeps each core/actor a **sequential** program → verifiable with the existing
   sequential machinery + per-instance forward simulation (ADR-0035). The only concurrent part is the
   message channels.
2. It **avoids Iris concurrent separation logic.** Iris is forced by *shared mutable state under
   interference*; shared-nothing eliminates exactly that. (Corrects an earlier coarser read that
   "parallel processes → Iris" — parallelism per se doesn't force it; **sharing** does.)
3. On-thesis: it trades fine-grained-sharing performance for verifiability = invariant #7
   (performance second-class, correctness first). A perf-first project picks shared-memory SMP;
   bang's correctness-first stance picks the multikernel.
4. wasm fits: separate linear memories by construction; stack-switching gives each module its
   *internal* concurrency (green-threaded actors, scheduler-as-a-handler).

**The load-bearing invariant** (keeps the cheap proof method valid as concurrency lands):
> messages **by-copy**; **NO cross-instance shared TVars / no shared global heap** baked into the
> runtime (`Wasmfx.run` / the `⊨` modelling relation).

Violate it — a shared central-manager hot spot, or shared TVars across cores — and you reintroduce
concurrent state → the Iris bill + a bottleneck/SPOF. **Barrelfish's lesson: the "central manager"
must itself be message-passing / replicated, not a shared-memory coordinator.** Rework risk is gated
by ONE decision (Q21, post-v1): *do two actors/cores ever share a TVar across instances?* Never →
forward-sim composes sequentially, no Iris. Ever → the iris-wasmfx / Affect POPL'25 regime.

```
neighbours   Barrelfish (multikernel) · seL4 (verified kernel; big-lock vs clustered multicore) ·
             Erlang/BEAM (actors, shared-nothing, by-copy) · Singularity (SIPs, typesafe isolation) ·
             Unison (already mapped — ships code @ the data)
status       ✗ open / ★ — post-v1, but CONSTRAINS ◊5+ via the by-copy invariant above (don't bake a
             shared global heap into the runtime now). Supersedes the bare "concurrency MEMORY MODEL"
             row above with a concrete direction.
```
