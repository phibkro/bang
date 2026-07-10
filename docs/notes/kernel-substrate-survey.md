<!-- note-status: active -->
# Kernel-as-substrate — design survey: the verified semantic substrate + the profile ladder

> The operator's question (2026-07-10): *"Can bang's kernel — five primitives, graded-CBPV
> semantics, proven soundness + binary LR + calculated VM — be a **verified semantic substrate**:
> an interface other languages implement against (elaborate into) to inherit its theorems?"*
> Sharpened to the note's spine: **factor the spec into subsets mapped to lambda-cube corners
> (λ→ → System F → Fω → …), so implementing against subset X is valid for formality class X — "a
> set of specs for each corner of the lambda cube."** This note mines the prior art (verified-
> semantics frameworks, CBPV universality, effects-as-theories, ISA/SQL conformance profiles),
> factors the spec into a **(type-rung × row-rung) matrix**, states the honest typed-vs-erased
> embedding boundary per corner, sketches the interface contract, and scopes a tracer bullet. It
> is an **ADR-input note, not an ADR**: it records what an ADR *would* decide and does not decide
> it. Web citations live in §References; every in-repo claim carries a `file:line`.

## 0 · The one-paragraph thesis

bang's kernel is already a **verified semantic substrate** in all but name: a source language
elaborates (ADR-0075) into a graded-CBPV `Comp`, and that `Comp` runs on a reference semantics
(`Source.eval`) with machine-checked **type safety**, **effect soundness**, **contextual
equivalence** (the binary LR), and **verified compilation** to WasmFX. The moat (`docs/PRD.md` §2)
already sells "a language safe to generate into"; the substrate direction generalizes that from
*bang programs* to *other languages' programs* — elaborate language L into the kernel, and L
inherits the kernel's theorems **at the corner of the design space L's elaboration lands in**.
The operator's sharpening is the load-bearing structural move: the guarantees are not monolithic,
they are **graded along two orthogonal axes** — a **type-power axis** (the lambda cube: λ→ →
System F → Fω) and a **computational-power axis** (the effect row: ⊥-total → Div → labelled
effects). A conformance *profile* is a cell in that matrix: a named (type-rung × row-rung) pair,
plus a statement of exactly which theorems an embedding into that cell inherits. The prior art
for "a base spec + named certified subsets an implementer claims" is **RISC-V profiles**
(RV64I base + ratified extensions) and **SQL conformance** (Core + optional feature packages) —
mature in hardware and databases, and, to this survey's knowledge, **never applied to a *verified*
semantic substrate**. That is the defensible novelty (§7), and it comes with an honest wall the
kernel's own types force (§2, §5): the kernel's *formalized type language* is **λ→ + iso-recursive
types**, with **no ∀-former** — so λ→ and (via elaborate-to-mono) System-F/Fω *dynamics* embed and
inherit safety, but the *typed* inheritance boundary is sharp and must be stated, not blurred.

```
   TWO ORTHOGONAL LADDERS (the profile matrix's axes)

   type-power  (lambda cube)          computational-power (effect row)
   ─────────────────────────          ────────────────────────────────
   λ→   simply typed                  ⊥      total fragment (System-F-shaped core, ADR-0026)
   F    ∀ (System F)                  Div    fuel-bounded, Turing-complete (the descent seam)
   Fω   type operators                {ℓ…}   labelled effects (state · throws · txn · user)
   ─────────────────────────          ────────────────────────────────
   graded by the TYPE SYSTEM          graded by the EFFECT ROW (already a lattice, ADR-0018)
   (surface/elaborator; erased        (kernel-native: the row IS the grade,
    into mono kernel — ADR-0075)       categorical-architecture.md §3)

   a PROFILE = one (type-rung × row-rung) cell + the theorems an embedding into it inherits.
```

---

## 1 · The competitive census — verified-semantics frameworks on five axes

The question "is the kernel a substrate other languages inherit theorems from?" has a dense
neighbourhood. The axes that matter: does the framework give an **executable spec**? a
**soundness** theorem? **contextual equivalence** (a binary relation, not just safety)?
**verified compilation** to a real target? and does it **classify paradigms/effects** as
first-class structure? The last two axes are where bang is unusual.

```
 framework            exec-spec  soundness  ctx-equiv  verified-compile  paradigm-class    substrate-shape
 ─────────────────    ─────────  ─────────  ─────────  ────────────────  ──────────────    ───────────────────────
 K / KEVM             ✅ (rewrite ◑ (reach-  ✗          ✗ (interp, not    ✗                 META-LANGUAGE: define a
 [k-overview]           logic)     ability)              a compiler)                         semantics, tools derived
 Iris (+ logrel)      ✗ (a logic, ✅ (semantic ✅ (binary  ✗ (reasons about  ◑ (effects via   META-LOGIC: instantiate
 [timany-jacm24]        not exec)   soundness)  logrel)    a compiler,        HeapLang forks)   per language; not a
                                                          not one)                             *target* you elaborate to
 CompCert             ✅ (Clight   ✅ (type    ◑ (refine- ✅ (C → asm, the   ✗                 A VERIFIED COMPILER for
 [leroy-cacm09]         interp)     safety of   ment,      canonical one)                      ONE fixed language (C)
                                    the langs)  simulation)
 CakeML / PureCake    ✅          ✅          ◑          ✅ (end-to-end)   ✗                 verified compiler +
 [kumar-popl14]                                                                              bootstrapped, ONE language
 skeletal semantics   ✅ (Necro-   ◑ (per      ✗          ✗                ✗                 META-LANGUAGE: one skeleton,
 [bodin-popl19]         gen interp) interp)                                                    many interpretations
 MetaCoq              ✅ (verified ✅ (type-   ✗          ◑ (verified      ✗                 the HOST's checker verified;
 [sozeau-popl20]        checker)    checker      erasure)                                     not a substrate to embed into
                                    correct)
 Levy CBPV            — (a         — (a        — (the     —                ✅ (subsumes CBV  THE THEOREM the whole
 [levy-thesis]          calculus)   calculus)   universality             /CBN by translation) direction leans on (§1a)
                                                theorem)
 ─────────────────    ─────────  ─────────  ─────────  ────────────────  ──────────────    ───────────────────────
 bang kernel          ✅ Source-   ✅ type_    ✅ lr_     ✅ compile_       ✅ paradigm=the   THE PROPOSAL: a verified
 (this repo)            eval        safety      sound     forward_sim       row (§1b)         *target language* + profiles
```

**In-repo anchors for bang's row** (checked at base `5ffa837`):
`Source.eval` (`Bang/Core/Semantics.lean`; the executable reference oracle) · `type_safety` /
`custom_program_safe` (`Bang/Spec.lean:155`, `:83`; well-typed ⟹ never `.stuck`) · `lr_sound` /
`lr_fundamental` (`Bang/Spec.lean:236`, `:267`; contextual approximation via the biorthogonal
binary LR — **currently `sorryAx`-flagged**, a single named residual, see §4 + the paper skeletons
`docs/papers/binary-lr-skeleton.md`) · `compile_forward_sim` (`Bang/Spec.lean:321`; the calculated
machine → WasmFX simulation) · `effect_sound` (`Bang/Spec.lean:190`; static row over-approximates
every observed trace).

### 1a · The one theorem the whole direction leans on — Levy's CBPV universality

The reason "elaborate L into the kernel" is a *principled* move and not a hack: **CBPV subsumes
both call-by-value and call-by-name** via semantics-preserving translations (Levy's thesis;
[levy-thesis], [levy-subsuming]). "A value *is*, a computation *does*" is exactly bang's `Val`/`Comp`
split (`Bang/Core/IR.lean:94`, `:113`). So a CBV language and a CBN language *both* have a
faithful home in a CBPV target — the universality theorem is the licence for the substrate claim's
*computational* axis. bang extends Levy's target with **grades** (Torczon effects/coeffects,
OOPSLA'24; `Bang/Core/IR.lean:30`) — so the target isn't just CBPV, it's *graded* CBPV, and the
grade is what carries the profile information (§2). The honest limit: Levy's theorem is about
CBV/CBN *evaluation order*; it does **not** hand you an embedding of an arbitrary type system —
that owes an adequacy proof per language (§4), and the *type-power* corner it lands in is the
separate axis this note's matrix pins.

### 1b · Effects are algebraic theories — the paradigm-classification axis

Plotkin–Power ([plotkin-power]): computational effects are **algebraic theories**, and their
generic effects ⇔ algebraic operations. bang instantiates this operationally — `perform` is a
generic effect, a `Handler` is (the structural half of) its algebra
(`categorical-architecture.md` §4; `laws-taxonomy.md` §3). This is the axis no compiler-shaped
framework (CompCert, CakeML) has: bang classifies a program's *paradigm* as **which effect labels
are in its row**, so an embedded language's paradigm is *read off* its elaborated row rather than
asserted. The census row "paradigm-class ✅" is this, and it is what makes the substrate a
*multi-paradigm* one — the moat (`docs/PRD.md` §2), restated as a conformance surface.

### 1c · The honest read of the census

Two frameworks are close enough to threaten the novelty and must be named precisely:

- **Iris is the strongest prior art**, and it is a *meta-logic*, not a *target*. Iris gives a
  reusable, language-parametric program logic + step-indexed logical relations; it has been
  instantiated for DOT/Scala, reachability types, WasmFX, and CompCert-C
  ([timany-jacm24], and the repo already cites `legoupil-pldi26-iris-wasmfx`). The distinction
  that preserves bang's claim: with Iris you **instantiate the logic to your language and prove
  your own soundness**; with the bang substrate you **elaborate your language into a fixed target
  and inherit the target's already-proven soundness** (owing only an adequacy proof, §4). Iris
  gives you the *tools* to prove; bang gives you the *theorems* for free at your corner. That is a
  real difference, but it is a difference of *packaging and reuse granularity*, not of raw power —
  state it that way, don't oversell it.
- **K's "language framework" vision is the same dream, differently cashed.** K derives tools
  "correct-by-construction" from one semantics ([k-overview]); its recent proof-generation work
  ([knite-proofgen]) even emits per-execution proof certificates. K's semantics are *executable*
  but the derived tools are trusted-by-construction of the framework, not accompanied by a
  contextual-equivalence theorem or a verified compiler to a real ISA. bang's narrower, deeper
  stack (one language, but with `lr_sound` + `compile_forward_sim`) is the complement: less
  breadth, more depth-of-guarantee.

**Verdict:** the census supports the claim *"nobody offers a verified *target language* with
named conformance profiles that other languages elaborate into to inherit contextual-equivalence +
verified-compilation theorems."* It does **not** support *"nobody has language-parametric verified
semantics"* — Iris and K do. The honest headline is the **profiles-for-a-verified-substrate**
framing (§7), not "first verified substrate."

---

## 2 · The profile matrix — (type-rung × row-rung), with the typed-vs-erased boundary

The operator's "spec for each corner of the lambda cube" becomes concrete once you notice bang
**already grades both axes**, and the repo vocabulary already names them:

- The **row axis** is kernel-native and already a lattice (ADR-0018; the total ⊥-fragment is
  literally an arrow in the effect lattice, `categorical-architecture.md` §8). The stratification
  table (CLAUDE.md) already names the verified core *"total fragment (⊥-row, System F)"*.
- The **type axis** is the polymorphism ladder — and it is **not** in the kernel's types; it is in
  the **elaborator** (ADR-0075 "polymorphism elaborates to mono"; `stdlib-map.md` gates its whole
  catalogue by "type-system power"). This is the crux the note must be honest about.

### 2a · The load-bearing finding — the kernel's formalized types are λ→ + iso-recursion, no ∀

`VTy`/`CTy` (`Bang/Core/IR.lean:221`–`242`) are: `unit`, `int`, `U φ C` (thunk), `cap ℓ`, `sum`,
`prod`, `mu` (iso-recursive), `tvar`, `F q A`, `arr q A B`. The comment at `IR.lean:229`–`231`
states it outright: **`tvar` is NOT a polymorphic ∀-variable (ADR-0027); it is bound only by
`mu`, so `μX. 1 + (Int × X)` is a CLOSED, monomorphic type.** There is **no ∀-quantifier former in
the kernel types.** Therefore:

```
  the kernel's FORMALIZED type system  =  λ→  +  iso-recursive μ  +  sums/products  +  graded F/U/arr
                                          ───────────────────────────────────────────────────────────
  it is SIMPLY TYPED (with recursion). It is NOT System F at the kernel-type level.
```

The System-F / Fω power advertised in `stdlib-map.md` (generic `Option a`, HKT `Functor`,
ADR-0079/0082) is **surface polymorphism that ELABORATES AWAY**: a generic definition is
monomorphized (ADR-0075/0081) into closed kernel terms before `Source.eval`/`HasCTy` ever see it
(Q40 confirms this is the standing strategy: "AOT elaborate-to-mono … still targeting the verified
kernel"). This is the single most important boundary in the note, and it dictates the honest
typed-vs-erased column below.

### 2b · The matrix

Read a cell as: *"an embedding whose types land at this (type-rung × row-rung) inherits these
theorems, TYPED or ERASED."* **Typed** = the embedding's own types map to kernel `VTy`/`CTy` and
it inherits `type_safety` **at those types** (safety is a property *of the typed embedding*).
**Erased** = the embedding monomorphizes/erases its polymorphism into closed kernel terms; it
inherits safety **of the resulting mono program** and equivalence/compilation, but the kernel's
type judgment does **not** witness the *source* language's type discipline — only the mono residue.

```
                 row: ⊥ (total)              row: Div (fuel)             row: {ℓ…} (effects)
 ───────────────────────────────────────────────────────────────────────────────────────────────
 type: λ→        TYPED. Full inheritance:    TYPED + Div seam. Safety     TYPED. Effects as handlers;
 (simply         type_safety at the embed's  holds; termination NOT       inherits no_accidental_
  typed)         own types · effect_sound ·  claimed (fuel-bounded,       handling + custom_program_
                 lr_sound (equational rsng)· ADR-0028 descent). This is   safe. THE STLC/IMP tracer-
                 compile_forward_sim.        the workhorse cell.          bullet cell (§6).
                 ── the CLEANEST corner ──
 ───────────────────────────────────────────────────────────────────────────────────────────────
 type: F         ERASED (mono). ∀ has no     ERASED. Same, + Div.         ERASED. Same, + effects.
 (System F,      kernel VTy home → embed     Source-level parametricity   Inherits mono safety; the
  ∀)             monomorphizes (ADR-0075).   is the EMBEDDER's obligation  ∀-parametricity theorem
                 Inherits safety OF THE      (kernel gives it no free     is NOT inherited (the kernel
                 MONO RESIDUE, not a ∀-      parametricity theorem — its   has no ∀ to be parametric
                 parametricity theorem.      types are mono).             over). A FINDING, not a fail.
 ───────────────────────────────────────────────────────────────────────────────────────────────
 type: Fω        ERASED / dynamics-only.     ERASED. As above.            ERASED. As above.
 (type           Type operators (f : *→*,    Kinds-as-arity monomorph-    HKT effect-generic code
  operators,     HKT) have NO kernel type-   ization (ADR-0082) erases    erases to mono handlers;
  HKT)           former (no kind structure   the constructor variable      inherits mono guarantees.
                 in VTy) → erased to mono.    before the kernel.           Fω-typed inheritance = OUT
                 Inherits mono dynamics +     Functor/Monad SHIPPED this   OF SCOPE with reason (§2c).
                 safety, never Fω-typing.     way (ADR-0082).
 ───────────────────────────────────────────────────────────────────────────────────────────────
 dependent       OUT OF SCOPE (named, §2c). No kernel path intends Π-types; the verifier (Lean) is the
 corners (λΠ,     dependent layer, and in-language dependent types are explicitly set aside
  CoC)           (verification-ladder.md, the HoTT verdict). Not a failure — a deliberate non-goal.
```

### 2c · The out-of-scope corners, named with reason (not papered over)

- **Fω-*typed* inheritance** (inheriting a type-operator discipline at the kernel-type level)
  needs the kernel `VTy` to gain **kinds** (a `*→*` former) — a kernel type-system change, i.e. a
  spec change requiring an ADR, and squarely against the elaborate-to-mono grain that "has now won
  five times *because* the kernel stays simple" (`verification-ladder.md`). The **dynamics** of Fω
  code embed fine (erased); only the *typed* inheritance is out.
- **Dependent corners** (λΠ, Calculus of Constructions): explicitly a non-goal
  (`verification-ladder.md`: HoTT/dependent types set aside; the *host* Lean is the dependent
  layer, not the object language). Naming them keeps the cube honest — the substrate is a
  **λ-cube-lower-face** substrate (λ→, and the *erased* image of F/Fω), not a full-cube one.

### 2d · What each locked corner would COST to unlock (the generative-constraint read)

Stating the cost is the SOUL "name the right answer first, then its price" discipline:

```
  corner to unlock            kernel growth required                        against invariant?
  ──────────────────────      ──────────────────────────────────────────   ──────────────────────
  System-F-TYPED (not erased) add a ∀-former to VTy + a type-abstraction    NO new primitive, but a
                              computation former; re-prove type_safety +     TYPE-system change → ADR.
                              the LR over the extended type grammar.         Cost: the LR re-index.
  Fω-TYPED                    the above + KINDS (a *→* former, kind ctx).    Bigger; ADR + real proof.
  dependent                   Π-types; the kernel becomes a proof language.  Non-goal (ladder verdict).
```

The **payoff of NOT unlocking them** is the whole elaborate-to-mono thesis: a simple kernel keeps
the proof budget on the *core* and lets the surface carry polymorphism for free (ADR-0075). So the
matrix's "erased" cells are not a weakness to fix — they are the **design working as intended**;
the finding is simply that *typed* inheritance stops at λ→ + iso-recursion, and an embedder above
that line owes their own parametricity story (§4).

---

## 3 · The kernel interface contract — what must become public + versioned

If the kernel is a substrate, its surface is a **public contract**, and the compiler-as-DBMS
survey already established the precedent to reuse: **`bang query dump` is a versioned public fact
schema** (`compiler-as-dbms-survey.md` §6, the schema-evolution wall; issue #80). The same
discipline applies one level down — the *semantics* becomes a versioned contract, not just the
*fact dump*. What an embedder binds against:

```
  contract surface            in-repo home (base 5ffa837)              stability obligation
  ────────────────────        ──────────────────────────────────      ───────────────────────────
  the term algebra            Val / Comp / Handler  (IR.lean:94/113/   FROZEN shape; adding a former
    (elaboration TARGET)        139)                                    = a kernel change (invariant #5)
  the type algebra            VTy / CTy  (IR.lean:221/236)             FROZEN; the λ→+μ grammar §2a
  the grade algebras          EffSig / Lattice+OrderBot (Eff);         the ROW is the profile's
    (the profile axes)          CommSemiring (Mult)  (IR.lean:52)       computational coordinate
  the typing judgment         HasVTy / HasCTy  (Typing.lean:103)       the "valid embedding" predicate
  the reference oracle        Source.eval  (Semantics.lean)            the differential-test referent (§4)
  the theorem statements      Spec.lean (the 18 headlines)             THE INHERITED GUARANTEES; frozen
                                                                        statements, census-gated
```

**The versioning move (borrowed verbatim from the DBMS survey's smallest step):** the substrate
contract emits a `substrateVersion`; theorem-statement changes are **major** bumps (they change
what an embedder inherits), additive formers/labels are **minor**, proof-internal changes are
**patch**. This is the *"decide-now-because-retrofit-is-costly"* logic ADR-0076 #2 used for spans:
once a second language elaborates into the kernel, its `Comp`-generation is pinned to the term
algebra, and an unversioned change silently breaks it. The `Bang/Spec.lean` census gate (`#print
axioms`, byte-identical statements) is **already** a schema-snapshot test for the theorem surface —
the contract's integrity constraint exists; the substrate framing just names it as one.

**The honest wall:** freezing the term/type algebra as a public embedding target trades away the
pre-1.0 licence to "change public shapes freely" (SOUL, correctness-by-construction). Today that
licence is load-bearing (the kernel is still moving — envm/ADR-0094, the LR residuals). So the
contract is **not** something to freeze now; it is something to *identify now and freeze at the
◊ where a second embedder appears*. Naming it prevents a later session from freezing it
accidentally or too late.

---

## 4 · The transfer condition — what an embedder owes, and the rung available today

Inheritance is not free. The kernel supplies the **target, the theorems, and an oracle**; the
embedder owes **elaboration adequacy** — a proof that their language L's own semantics agrees with
the semantics of the elaborated `Comp`. Stated honestly:

```
  the kernel GIVES                           the embedder OWES
  ─────────────────────────────────          ──────────────────────────────────────────
  a target (graded CBPV Comp)                an elaboration  ⟦·⟧ : L-term → Comp
  theorems over Comp (Spec.lean)             ADEQUACY:  ⟦·⟧ preserves L's semantics
    type_safety, lr_sound, …                   (evalᴸ e  ≃  Source.eval ⟦e⟧)  — the proof obligation
  an oracle (Source.eval)                     — OR, the cheap rung: DIFFERENTIAL TEST vs the oracle
```

The adequacy proof is the analogue of CompCert's semantic-preservation obligation ([leroy-cacm09])
and Levy's translation-correctness (§1a): **a per-language theorem**, not something the substrate
discharges. This is the correct division — the kernel cannot know L's semantics, so it cannot prove
the bridge; it can only be the well-defined thing the bridge lands in.

**The rung available *today*, at zero new machinery:** the stratification invariant (invariant #1,
"proof rides the reference") is *already* a substrate transfer mechanism. An embedder can **skip
the adequacy proof and instead differentially test** their elaboration against `Source.eval` — the
exact discipline every in-repo eval already lives under (`evalD_agrees_source`, the `Agree`
battery). So the substrate offers a **two-rung transfer**, mirroring the verification ladder:

```
  transfer rung        what it buys                         cost              available
  ─────────────────    ────────────────────────────────     ───────────────   ──────────────
  differential test    "my embedding agrees with the         write test cases  TODAY (invariant #1;
    (fuzz)               oracle on these inputs"               + a fuzzer        the bang test harness)
  adequacy proof       "my embedding agrees ALWAYS →          a Lean proof      the Q43-shaped rung
    (Lean)               L inherits the kernel's theorems"     per language      (proof-export, post-1.0)
```

This is the **stratification principle applied to embeddings**: fuzz-by-default, prove-on-demand,
one seam, explicit. It is also why the substrate claim is *not* vapourware — the cheap rung is
shippable now; the expensive rung is the same Q43 proof-export machinery the repo already scopes
(`verification-ladder.md`, `proof-export-survey.md`), pointed at an embedding instead of a `law`.

---

## 5 · The tracer bullet — STLC (or IMP) embedded as handlers, SCOPED not built

The cheapest thing that would make the substrate claim *real* rather than aspirational: embed a
tiny known language into the kernel and show it inheriting the theorems **without writing a new
logical relation**. Two candidates, both landing in the **λ→ row** of the matrix (§2b):

```
  candidate   embeds as                              inherits (from Spec.lean)          matrix cell
  ─────────   ──────────────────────────────────     ─────────────────────────────      ───────────
  STLC        pure λ→ terms → Comp (lam/app/ret;      type_safety (λ→-typed) ·           (λ→ , ⊥)
                no effects, ⊥-row)                     lr_sound equational reasoning ·      the cleanest
                                                       compile_forward_sim (runs on Wasm)   corner
  IMP         state-as-a-handler: assignment →         type_safety · effect_sound          (λ→ , {state})
                perform put; deref → perform get;       (the row = {state}) ·               the "effects
                the whole program under one `handle`    no_accidental_handling              are library"
                                                                                            demo
```

**Why this is the right tracer bullet.** It exercises the *inheritance* claim end-to-end with the
least new code: no new relation, no kernel change — just an elaboration function `⟦·⟧` and a
differential test against `Source.eval` (the §4 cheap rung). STLC is the purest demonstration
("inherit safety + equational reasoning at your own types"); IMP is the more *rhetorically*
valuable one because **state-as-a-handler** is the moat's "paradigms are values" thesis made
literal — an imperative language embedded with **zero imperative primitives in the target**, its
whole store discipline riding the existing state handler (`stdlib-map.md` §C; ADR-0030).

**Honest size estimate.** The elaboration `⟦·⟧` for STLC is small — the CBPV embedding of λ→ is
textbook (Levy), and bang's `lam`/`app`/`ret`/`force` are exactly the CBPV formers; call it a few
hundred lines of Lean + a `#guard`/fuzz battery, days not weeks, **because it reuses the whole
existing stack** (no new theorem, the oracle already exists). IMP adds the state-handler wiring —
comparable. The *adequacy proof* (the expensive rung) is the part that is genuinely open and
should **not** be in the tracer bullet: the bullet ships the **differential-tested** embedding
(rung 1), demonstrating inheritance operationally; the adequacy theorem is a follow-on that waits
on Q43 proof-export, exactly as the verification ladder sequences it. **Scoped, not built** — this
note names the artifact and its size; a later increment builds it.

**One caveat surfaced by §2a.** STLC's inheritance is genuinely *typed* (STLC types → kernel λ→
types, safety at those types). But an embedder tempted to do **System-F** as the tracer bullet
would hit the erased boundary immediately (§2b): the kernel has no ∀ to receive System-F's type
abstractions, so the "inheritance" would be of the *monomorphized residue*, and the demo would
silently be weaker than it looks. **Pick λ→ for the bullet precisely because it is the corner where
typed inheritance is real** — the matrix isn't decoration, it changes which tracer bullet is honest.

---

## 6 · The scoped design — what an ADR would DECIDE (this note does not)

Recording the decision-shaped residue, ADR-input posture (no decision taken):

1. **Adopt the profile framing?** — whether to *publicly* factor the guarantees as named
   (type-rung × row-rung) profiles (RISC-V/SQL precedent, §7), or keep them as monolithic
   "the kernel is sound." The matrix (§2b) is the artifact an ADR would ratify or reject.
2. **Freeze the substrate contract, and when?** — §3 says *identify now, freeze at the second
   embedder*. An ADR would pin the `substrateVersion` policy + the freeze-◊. Premature freeze
   costs the pre-1.0 licence the moving kernel still needs.
3. **Which transfer rung is the v1 story?** — §4: differential-test (shippable now) vs
   adequacy-proof (Q43-gated). An ADR would state that v1's substrate story is the *tested* rung,
   with the proof rung named as the post-1.0 top of the ladder.
4. **Is the STLC/IMP embedding worth an increment?** — §5. A demonstrator that makes the moat's
   "paradigms are values" concrete for an *external* language, at low cost. An ADR/roadmap entry
   would slot it (it rides the existing stack; it competes with kernel-forward work for attention,
   not for machinery).
5. **The out-of-scope corners stay out** (§2c) — an ADR would record System-F-*typed* and
   dependent inheritance as deliberate non-goals with the elaborate-to-mono rationale, so a later
   session doesn't read the "erased" cells as bugs and try to add ∀ to the kernel (which would
   trip invariant #5's spirit — a type-system spec change).

---

## 7 · THE NOVEL CLAIM — certified conformance profiles for a verified substrate

**The claim.** RISC-V profiles ([riscv-rva23]) and SQL conformance ([sql-conformance]) are the
mature pattern of *a base spec + named subsets an implementer claims conformance to*: RVA23 =
RV64I base + ratified extensions, each mandatory/optional; SQL = Core + optional feature packages.
Both grade an implementation's conformance along named axes. **No one has applied this pattern to a
*formally verified semantic substrate*** — i.e. named (type-power × computational-power) profiles
where claiming conformance to profile X means *inheriting a machine-checked theorem set*, not just
"supports feature X." That is the defensible novelty, and it is a *reframing* of assets bang
already has (the graded rows, the elaborate-to-mono ladder, the frozen Spec.lean statements) into a
**public conformance surface**.

```
  ISA / SQL profile                    VERIFIED-SUBSTRATE profile (bang)
  ─────────────────────────────        ──────────────────────────────────────────────
  base + named extensions              (type-rung × row-rung) cell
  "conforms to RVA23"                  "embeds at (λ→, {state})"
  conformance = feature presence       conformance = a MACHINE-CHECKED THEOREM SET inherited
  claimed by the implementer           EARNED by an adequacy proof (or the fuzz rung, §4)
  tested (compliance suite)            tested (differential vs Source.eval) → proven (Q43 adequacy)
```

**Why it holds, checked honestly.** The census (§1) shows the *ingredients* exist elsewhere —
Iris/K are language-parametric verified semantics; RISC-V/SQL are conformance profiles — but the
*combination* (profiles indexing inherited *proofs* over a fixed verified *target language*) is, to
this survey's knowledge, unclaimed. The novelty is **narrower** than "first verified substrate"
(false — Iris) and narrower than "first conformance profiles" (false — RISC-V); it is precisely
**"profiles as an index into a lattice of inherited theorems for a verified elaboration target."**
That precision is the claim to protect — a later session must not inflate it to "first verified
substrate" (the census refutes that) nor collapse it to "just documentation of what's proven" (it
is a *public contract with a conformance semantics*, §3).

**The honest wall on the novelty.** The profiles are only as strong as the *typed* inheritance
they promise, and §2 shows typed inheritance stops at λ→ + iso-recursion. So the **rich** cells of
the matrix (System F, Fω) are *erased* profiles — they inherit mono dynamics, not source-typed
guarantees. A profile system whose upper-right cells are all "erased" is honest but less dramatic
than "inherit your full type discipline." The claim to protect is therefore *"a verified target
with a **λ→-typed** conformance floor and an **erased** conformance ceiling, indexed by the effect
row"* — which is real, novel, and load-bearingly honest about where the typed guarantee ends.

---

## 8 · Refutation check — did the ruled design shape survive?

The brief pre-ruled **two orthogonal ladders (type-power × row-power), profiles = the matrix,
RISC-V/SQL as the shape-anchor.** The evidence:

- **SURVIVES, strengthened.** The row axis is kernel-native and already a lattice (ADR-0018); the
  type axis is the elaborate-to-mono polymorphism ladder (`stdlib-map.md`, ADR-0075). The two are
  genuinely orthogonal — the row grades *computation*, the cube grades *types*, and the repo
  vocabulary ("total fragment (⊥-row, System F)") already sits at their intersection. The matrix
  (§2b) is the natural artifact.
- **ONE REFINEMENT the shape forced (a partial refutation of the naive reading).** The naive
  reading — "each cube corner is a *typed* profile you inherit at" — is **false above λ→**. The
  kernel has no ∀-former (`IR.lean:229`), so System-F/Fω corners are **erased**, not typed. The
  ladders are orthogonal, but the *type* ladder's upper rungs collapse into "mono residue" at the
  kernel boundary. This is not a refutation of the two-ladder shape; it is a refutation of the
  assumption that the cube axis is *typed all the way up*. The matrix survives; the "typed" label
  is correct only on its bottom row. I flag this as the note's sharpest finding because it is the
  thing a later session would most easily get wrong.
- **RISC-V/SQL anchor SURVIVES as *shape*, with a caveat.** They are the right precedent for "base
  + named claimed subsets," but neither indexes *proofs* — so they anchor the *form* of the
  profile system, not its *content*. The content-novelty (§7) is bang's; the form is borrowed.

No part of the ruled shape was refuted outright. The one correction — *typed inheritance is a λ→
floor, not a full-cube surface* — is a sharpening the kernel's own types dictated, and it is the
finding the note is built around (§2a).

---

## References

- **Levy, Call-by-Push-Value** (the universality theorem — CBPV subsumes CBV & CBN): PhD thesis,
  Queen Mary 2001 (<https://www.cs.bham.ac.uk/~pbl/papers/thesisqmwphd.pdf>); "Call-by-Push-Value:
  A Subsuming Paradigm", TLCA'99
  (<https://link.springer.com/chapter/10.1007/3-540-48959-2_17>). [levy-thesis], [levy-subsuming]
- **Plotkin & Power, "Algebraic Operations and Generic Effects"**, Applied Categorical Structures
  11(1):69–94, 2003 (<https://link.springer.com/article/10.1023/A:1023064908962>). [plotkin-power]
- **K framework / KEVM**: "An Overview of the K Semantic Framework" (Roșu & Șerbănuță)
  (<https://runtimeverification.com/blog/k-framework-an-overview>); Roșu, "K: A Semantic Framework
  …", Marktoberdorf 2017 (<https://fsl.cs.illinois.edu/publications/rosu-2017-marktoberdorf.pdf>);
  proof-generation / trustworthy K (<https://link.springer.com/chapter/10.1007/978-3-030-81688-9_23>).
  [k-overview], [knite-proofgen]
- **Iris — logical approach to type soundness** (language-parametric logrel; DOT, reachability
  types, WasmFX instances): Timany, Krebbers, Dreyer, Birkedal, "A Logical Approach to Type
  Soundness", JACM 2024 (<https://iris-project.org/pdfs/2024-jacm-logical-type-soundness.pdf>);
  cf. in-repo `legoupil-pldi26-iris-wasmfx`. [timany-jacm24]
- **CompCert** (verified C compiler, semantic preservation): Leroy, "Formal verification of a
  realistic compiler", CACM 2009 (<https://xavierleroy.org/publi/compcert-CACM.pdf>). [leroy-cacm09]
- **CakeML / PureCake** (end-to-end verified compilation): Kumar et al., "CakeML: A Verified
  Implementation of ML", POPL'14 — already in-repo (`kumar-popl14-cakeml`, `kanabar-pldi23-purecake`).
- **Skeletal semantics** (a meta-language; Necro-generated Coq/OCaml interpreters): Bodin, Gardner,
  Jensen, Schmitt, "Skeletal Semantics and their Interpretations", POPL'19
  (<https://inria.hal.science/hal-01881863v1>). [bodin-popl19]
- **MetaCoq** (verified Coq type-checker + erasure): Sozeau et al., "Coq Coq Correct!", POPL'20
  (<https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf>).
  [sozeau-popl20]
- **RISC-V profiles** (base + ratified extensions, mandatory/optional): "RVA23 Profiles v1.0",
  ratified 2024-10-17 (<https://docs.riscv.org/reference/rva23/_attachments/rva23-profile.pdf>);
  ratification announcement
  (<https://riscv.org/blog/risc-v-announces-ratification-of-the-rva23-profile-standard/>). [riscv-rva23]
- **SQL conformance** (Core + optional feature packages, ISO/IEC 9075): PostgreSQL Appendix D "SQL
  Conformance" (<https://www.postgresql.org/docs/current/features.html>). [sql-conformance]
- **Internal anchors**: `Bang/Core/IR.lean` (the term + type algebras — the λ→+μ finding, §2a) ·
  `Bang/Core/Typing.lean` (`HasVTy`/`HasCTy` — the "valid embedding" judgment) · `Bang/Spec.lean`
  (the 18 frozen theorem statements — the inherited guarantees) · ADR-0075 (polymorphism
  elaborates to mono — the type axis lives in the elaborator) · ADR-0018 (rows are a lattice — the
  computational axis) · ADR-0016 (two-hop architecture — the verified compile the substrate
  inherits) · `docs/PRD.md` §2–3 (the moat + "safe to generate into" — the substrate generalizes
  it) · `docs/notes/categorical-architecture.md` (§3 the graded monad = paradigm; §8 the total
  fragment as an arrow) · `docs/notes/stdlib-map.md` (the type-power gating ladder = the cube axis)
  · `docs/notes/verification-ladder.md` (the fuzz→prove transfer rungs; the HoTT/dependent verdict)
  · `docs/notes/laws-taxonomy.md` (effects = algebraic theories; the gradeable criterion) ·
  `docs/notes/compiler-as-dbms-survey.md` (the versioned-public-contract precedent, §3) · Q40 /
  ADR-0082 (elaborate-to-mono is the standing strategy, including HKT).
