<!-- note-status: active -->
# Lambda-cube ascent — design survey (R6, ROADMAP §Pre-v1 research ladder)

> The R6 question: *how far up the cube (F → Fω → CoC) can the SURFACE climb while the
> kernel stays ∀-free?* The polymorphism arc already answered the first two rungs —
> **F + HKT + row-polymorphism landed via elaborate-to-mono** (ADR-0075, ADR-0079–0083)
> with the kernel untouched (`IR.lean:229`: `tvar` is bound only by `mu`; no ∀-former).
> So this survey's real content is **where elaborate-to-mono runs out**: (a) which
> Fω/dependent ergonomics still elaborate away, (b) which genuinely demand kernel Π and
> what that K-ADR costs, (c) what the dependent-CBPV literature says the stratified
> compromise looks like, (d) where the mono-instantiation set becomes unbounded — the hard
> wall. Ends with a profile-ladder extension (for `kernel-substrate-survey.md` §2c), the
> falsifiable probes, and a verdict. **ADR-input note, not an ADR.** The theoretical frame
> is `effects-vs-cic.md` (dependency over VALUES only; the CBPV compose point);
> `refinement-types-survey.md` (R5) is the cheap face of the same dependency question.

## 0 · The one-paragraph verdict

**The surface can climb one more rung — "dependent-by-elaboration" (closed type-level
computation + finite value indexing) — without the kernel learning anything; genuine
kernel Π is refutable-by-need for everything currently on the roadmap and should stay a
named, priced, closed door.** The literature is unanimous on the shape a kernel ascent
would have to take if it ever happens: **dependency over values/total-fragment only** —
Vákár's dCBPV⁻, Ahman–Ghani–Plotkin's "types depend only on value terms", F*'s Tot base,
Zombie/Trellys' logical fragment, and Pédrot–Tabareau's fire-triangle no-go theorem all
converge on the same stratification bang already has (the ⊥-row total fragment). So the
K-ADR's design is effectively pre-written by the field; what is genuinely open is only
*whether the demand ever materializes*, and the mono-instantiation wall (§4) gives the
precise, machine-checkable criterion for when elaboration stops being able to fake it:
**the instantiation set must stay finite and closed at elaboration time**. Everything
below is that sentence with evidence.

## 1 · Ground truth — what elaborate-to-mono has already bought (and its standing wins)

```
 cube rung        surface status                          kernel status          how
 ─────────        ─────────────────────────────────────   ────────────────────   ─────────────────────
 λ→ (+μ, +rows)   native                                  NATIVE (the only        —
                                                          typed rung; §2b of
                                                          kernel-substrate)
 F  (∀)           ✅ SHIPPED — generics, let-general-      ∀-free, untouched      monomorphization
                  ization, annotation-checked rank-n                              (ADR-0075/0080/0081)
 row-poly         ✅ SHIPPED (first-class from bite 0)     rows stay ground       instantiation
 Fω (HKT)         ✅ SHIPPED — Functor/Monad               no kinds in VTy        kinds-as-arity
                                                                                  monomorphization
                                                                                  (ADR-0082)
 λP (dependent)   ── the R6 frontier ──                    no Π, non-goal so far  THIS SURVEY
```

The strategy "has now won five times *because* the kernel stays simple"
(`verification-ladder.md`); the census (18→20 headline theorems) never moved. The
Fω-*typed*-inheritance boundary is already honestly stated (`kernel-substrate-survey.md`
§2c/§2e: erased, not typed, above λ→). R6 asks whether the *next* rung up bends the same
trick.

## 2 · Question (a) — which Fω/dependent ergonomics still elaborate away

The test for each candidate: does elaboration reach a **closed, finite** set of
monomorphic kernel residues? Four families pass:

1. **Type-level computation with closed reduction.** A type function whose arguments are
   always closed types at elaboration time (`Flatten (Pair Int Bool) ↝ ...`) is just a
   total function the *elaborator* runs — GHC's closed type families are the shipped
   precedent, and ADR-0082's kinds-as-arity move is already a special case (the elaborator
   computes the constructor application away). No kernel change: the kernel sees only the
   normal form.
2. **Finite dependent indexing over closed values** — sized vectors `Vec 3 Int` where the
   index is an elaboration-time literal. The industrial precedents are C++ templates and
   **Rust const generics**: value-indexed types compiled by *instantiation per index* —
   i.e. elaborate-to-mono with values in the index slot. Each `Vec n` used at a concrete
   `n` becomes its own closed `mu`-type (or a `prod`-chain). Works exactly as long as the
   set of `n`s appearing is finite and known.
3. **Singleton-style faked dependency.** Where the index must *flow* through generic code,
   the singletons technique ([eisenberg-haskell12]) promotes values to types and pairs
   them with a runtime witness — dependency simulated inside System-F-with-promotion,
   which bang's surface (post-ADR-0075) is rich enough to host in principle. GHC ran an
   entire dependently-flavored ecosystem on this for a decade — evidence the ergonomic
   *surface* of dependency does not require kernel Π, at real annotation cost.
4. **Refinements erased-to-base** — the R5 cheap face (`refinement-types-survey.md` §5,
   probe 2): `{x : A // P x}` elaborates to kernel `A` + a discharged obligation. Value
   precision without value-indexed kernel types.
5. **Runtime-dependent choice over a FINITE index set.** `if b then Int else Bool` with
   runtime `b` looks dependent but elaborates to a **sum** — the kernel's `sum`/`mu` are
   exactly the existential-over-a-finite-set packaging. (This is the dodge ADR-0075
   already names for first-class polymorphic values: defunctionalize.)

**The common denominator: elaboration-time closure.** All five are "the index/type
computation normalizes away before `HasCTy` looks." That is the same erased-inheritance
contract as the F/Fω rungs — dynamics + mono safety inherited, source-level *dependent
typing* NOT witnessed by the kernel (the embedder/surface owes its own story, as with
parametricity at the F rung).

## 3 · Question (b) — what genuinely demands kernel Π, and the price

What survives elimination by §2? The residue is small and sharp:

- **Unbounded runtime indexing**: `Vec n` where `n` arrives at runtime and the type must
  *track* it (not just guard it) — no finite instantiation set exists. (Often dodgeable:
  list + refinement `{xs // len xs = n}` — the R5 face again — but then the LENGTH is a
  proposition, not a type index, and type-level flow like `append : Vec n → Vec m →
  Vec (n+m)` needs arithmetic in the checker, not the kernel.)
- **Proofs-as-programs in-language** — Q42's far end (bang as its own prover): `Π` is the
  point, by definition. No elaboration can fake the judgment "this term IS the proof."
- **Type-level computation over OPEN/runtime data** — schema-indexed deserialization where
  the schema is a runtime value; printf typed by a runtime format string.

**The price of kernel Π** (the ADR-0027/0075 rationale, restated with the survey's
evidence):

```
 cost item                      size                     evidence
 ─────────────────────────      ──────────────────────   ─────────────────────────────────────
 type grammar + conversion      VTy/CTy gain Π + a       every dependent checker; decidability
   in the checker               normalization judgment    needs the TOTAL fragment (#47) first —
                                                          type-level eval must terminate
 the census re-proof            ALL headline theorems     the LR re-indexes over a dependent
   (18→20 → re-proven)          (type_safety, lr_sound,   grammar; the ◊4/◊4.5 arc + its LR
                                compile_forward_sim)      residuals are the repo's single
                                                          largest proof investment — for the
                                                          SIMPLY-typed relation
 the effects interaction        dependent elimination     Pédrot–Tabareau's NO-GO THEOREM
   is not free                  must be RESTRICTED in     [pedrot-popl20]: substitution +
                                the presence of effects   dependent elim + effects = ⊥ (the
                                                          fire triangle); ∂CBPV's restriction
                                                          is mandatory, not stylistic
 invariant pressure             a kernel that can state   the "kernel is not a proof language"
                                propositions is a proof   non-goal (verification-ladder HoTT
                                language                  verdict; kernel-substrate §2e)
```

This is a **K-ADR + full downstream re-validation** — the expensive fork ROADMAP R6
already names. Nothing on the current roadmap (R1–R5, the xv6 narrative, the demo pack)
needs any of the three residue items; Q42 explicitly defers the prover story to
parametricity-now/Curry-Howard-later.

## 4 · Question (d, taken before c — it sets the wall) — the mono-instantiation blowup

Elaborate-to-mono's precondition is that **instance discovery terminates**: collect every
instantiation a program uses, generate one residue each. The literature pins exactly where
that fails:

- **Polymorphic recursion.** Go's generics implementation (monomorphisation + hybrid
  dictionary-passing) documents the canonical divergence: `Box[int].Nest()` needs
  `Box[Box[int]].Nest()` needs `Box[Box[Box[int]]]`… — *"perfectly well-behaved programs
  may produce infinitely many type instantiations"* ([griesemer-oopsla20],
  [ellis-icfp22]). Instance discovery is non-terminating; Go rules such programs out with
  a static check, Haskell type-checks them but cannot monomorphize them.
- **First-class polymorphism / existential packing.** The 2025 SOTA on monomorphization
  ([lutze-oopsla25]) extends it to higher-rank + existentials via type-based flow
  analysis — refuting the folklore that rank-n kills monomorphization — but identifies
  **"polymorphic packing"** (the existential analog of polymorphic recursion) as the
  remaining divergence, and its guarantee is still conditional on the flow analysis
  reaching a finite set.
- **Dependency is the limit point of the same wall.** A value index drawn from a runtime
  value has an instantiation set that is unbounded *by construction* — monomorphization
  over `Vec n, n : Nat` is instance discovery over all of ℕ. Rust const generics work
  because indices are compile-time constants; the moment the index is dynamic, the
  strategy is not "slow", it is *undefined*.

**The wall, stated as a criterion the elaborator can CHECK:** elaborate-to-mono is valid
iff the instantiation set computed by flow analysis is finite ⟺ no (mutual/polymorphic/
packing) recursion grows its own index ⟺ dependency, if any, is over
elaboration-time-closed values. This is a decidable-per-program gate (Go ships one;
[lutze-oopsla25] gives the general analysis) — meaning the surface can offer the §2 rungs
honestly, with a *fitness-function-shaped* error at the boundary instead of a silent
divergence.

## 5 · Question (c) — the dependent-CBPV literature: every design converges on one seam

If the K-ADR ever opens, the field has already fixed its shape:

```
 system                        the stratified compromise                       verdict for bang
 ──────────────────────        ─────────────────────────────────────────────   ───────────────────────
 dCBPV⁻ / dCBPV⁺               types depend only on VALUES; dCBPV⁻ (no          dCBPV⁻ is the shape: the
 [vakar-thesis]                Kleisli extension of dependency across           semantics stays "no more
                               sequencing) is well-behaved — subject             complicated than simply
                               reduction, determinism, SN, clean semantics;      typed"; dCBPV⁺'s power
                               dCBPV⁺ (dependency crosses `letC`) is needed      is what costs
                               for full CBV/CBN translations but turns hairy
                               per-effect
 Ahman–Ghani–Plotkin           "types depend only on value terms";              independent confirmation
 [ahman-fossacs16],            computational Σ for sequencing; handlers          of the same seam, with
 Ahman [ahman-popl18]          fit (fibred algebraic effects)                    handlers — the closest
                                                                                 to bang's kernel
 ∂CBPV / the fire triangle     NO-GO: substitution × dependent elimination       the reason the seam is
 [pedrot-popl20]               × effects is inconsistent; CBPV decomposition     MANDATORY, not a style;
                               shows CBN must restrict dep. elim, CBV must       already the frame of
                               restrict substitution                             effects-vs-cic.md
 F* [swamy-popl16]             full dependency lives in the Tot base;            the engineering-grade
                               effects layered above via WP monads;              existence proof at scale
                               refinement/dependency never crosses into
                               an effectful computation's type unguarded
 Zombie / Trellys              TWO FRAGMENTS sharing one syntax: a logical       fragment-separation as a
 [casinghino-popl14]           (total, proof-bearing) fragment + a               LANGUAGE design — bang's
                               programmatic (partial, type-safe) fragment,       stratification principle,
                               with explicit cross-fragment rules                independently invented
 Idris 2 / QTT, GrTT           dependency and GRADES coexist in one              grades ⊥ dependency:
 [brady-ecoop21],              judgment (0/1/ω on binders; GrTT the              the two axes compose,
 [moon-esop21]                 general graded dependent theory)                  confirming the substrate
                                                                                 survey's family framing
```

**The convergence is total**: dependency over values / a total base, effects quarantined,
the seam explicit. That is *already bang's architecture* (the ⊥-row total fragment, the
Div descent, `effects-vs-cic.md`'s CBPV synthesis) — so a future kernel Π is not a new
stratification, it is a new tenant for an existing floor: **Π, if ever, is Π over the
⊥-row fragment's values** (F*'s `Tot` reconstructed inside the row lattice; the fire
triangle discharged by the row where F* discharges it by the monad ladder). The R6 finding
is that bang would enter the dependent-CBPV design space with its hardest structural
decision already made and machine-checked.

## 6 · The profile-ladder extension (feeds kernel-substrate-survey §2c)

The type-power axis grows two honest rungs between Fω and the out-of-scope dependent
corners — both ERASED (elaboration-computed), one new gate:

```
 type rung          what the surface offers                      kernel cost        inheritance
 ─────────          ─────────────────────────────────────────    ────────────       ───────────
 λ→ (+μ)            native                                       —                  TYPED (floor)
 F · Fω             generics · HKT (shipped)                     none               ERASED
 λP-closed  NEW     closed type-level computation · const-       none (elaborator   ERASED; VALID
                    generic value indexing · singletons ·        work + the §4      iff the FINITE-
                    finite-set existentials-as-sums              finiteness GATE)   INSTANTIATION
                                                                                    gate passes
 λP-refined NEW     refinements erased-to-base + obligation      none for rungs     ERASED; the R5
                    ladder (the R5 face)                         0–1 (Q31 path)     discharge ladder
 ΠV  (named,        kernel Π over ⊥-row VALUES                   K-ADR: census      TYPED dependent
  CLOSED door)      (dCBPV⁻/AGP/F*-Tot shape, pre-written §5)    re-proof + #47     floor — priced,
                                                                 prerequisite       not planned
 CoC                dependency across effectful computation      REFUTED (fire      non-goal,
                                                                 triangle)          theorem-backed
```

The `CoC` row upgrades kernel-substrate §2e from "deliberate non-goal" to
"**theorem-backed** non-goal" — [pedrot-popl20] is a no-go result, not a taste decision.

## 7 · The falsifiable probes an R6 probe-increment would run

1. **The Vec-over-closed-nat probe (does λP-closed work on today's elaborator?).**
   Implement `Vec n Int` for literal `n` by const-generic-style instantiation (each `n` a
   mono `mu`/`prod` residue) + `append` at concrete sizes. Falsifier: the elaborator's
   HM/instantiation machinery hits a structural wall (the ADR-0075 hole-id-collision
   class) that makes per-value instantiation different in kind from per-type — would mean
   λP-closed is NOT "the same trick one rung up" and needs its own design.
2. **The finiteness-gate probe (make the §4 wall a fitness function).** Implement the
   instantiation-set finiteness check (Go's nomono condition / [lutze-oopsla25]'s flow
   analysis, simplified) over the elaborator's instantiation graph; wire a red test with a
   `Box.Nest`-shaped program. Falsifier: the check can't be stated over bang's
   elaboration (instantiations not reified anywhere) — which would itself be a finding:
   the elaborator lacks the observable the wall needs, fix that first.
3. **The demand probe (is the ΠV residue real for bang's roadmap?).** Sweep the R1–R4
   design notes + the demo-pack scope for any construct that fails ALL of: λP-closed
   (§2), sum-packaging (§2.5), the R5 refinement face. Expected: zero hits (§3's residue
   is prover-shaped, and Q42 defers the prover). A single genuine hit reopens the K-ADR
   conversation with a concrete consumer instead of a hypothetical.

## 8 · Verdict — recommend / defer, with cost

**RECOMMEND adopting the ladder extension (§6) as survey truth + the finiteness gate
(probe 2) as the one cheap follow-up; DEFER kernel Π (ΠV) behind a pre-registered
trigger.** Concretely:

- **λP-closed and λP-refined are surface/elaborator rungs** — the elaborate-to-mono
  licence extends to them *conditional on the finiteness gate*, kernel untouched, census
  stable. Cost when demanded: elaborator work, the ADR-0075 pattern (its sixth and seventh
  wins, if they land).
- **ΠV stays a closed, priced door**: open only on probe 3's falsifier (a roadmap consumer
  that defeats all three elaboration dodges). If opened, the design is pre-selected by the
  literature's convergence (§5): dCBPV⁻-shaped, Π over ⊥-row values, #47 the prerequisite,
  the full census re-proof the honest price. Write THAT K-ADR then, not now.
- **CoC-style dependency across effects is refuted, not deferred** — cite the fire
  triangle whenever it resurfaces.
- The R5+R6 pair closes cleanly: **refinements are the value-side answer to the same
  demand that would otherwise pull the kernel up the cube** — most "I need dependent
  types" pressure is `{x // P x}`-shaped, and R5's discharge ladder absorbs it at
  elaborator cost. The cube ascent is what remains when refinement pressure is *type-flow*
  pressure — and §4 gives the machine-checkable line between them.

## References

- **Levy, CBPV** — in-repo (`levy-thesis`; `kernel-substrate-survey.md` §1a).
- **Vákár** — "In Search of Effectful Dependent Types", DPhil thesis, Oxford 2017
  (<https://www.cs.ox.ac.uk/people/aleks.kissinger/theses/vakar-thesis.pdf>); "A Framework
  for Dependent Types and Effects", arXiv [1512.08009](https://arxiv.org/abs/1512.08009);
  dCBPV⁻/dCBPV⁺. [vakar-thesis]
- **Ahman, Ghani, Plotkin** — "Dependent Types and Fibred Computational Effects", FoSSaCS
  2016, DOI [10.1007/978-3-662-49630-5_3](https://link.springer.com/chapter/10.1007/978-3-662-49630-5_3);
  Ahman, "Handling Fibred Algebraic Effects", POPL 2018, DOI 10.1145/3158095.
  [ahman-fossacs16], [ahman-popl18]
- **Pédrot, Tabareau** — "The Fire Triangle: How to Mix Substitution, Dependent
  Elimination, and Effects", POPL 2020, DOI
  [10.1145/3371126](https://dblp.org/rec/journals/pacmpl/PedrotT20.html) (∂CBPV; the no-go
  theorem). [pedrot-popl20]
- **Swamy et al.** — F*, POPL 2016, DOI
  [10.1145/2837614.2837655](https://fstar-lang.org/papers/mumon/) (the Tot-base ladder).
  [swamy-popl16]
- **Casinghino, Sjöberg, Weirich** — "Combining Proofs and Programs in a Dependently
  Typed Language", POPL 2014, DOI
  [10.1145/2535838.2535883](https://dl.acm.org/doi/10.1145/2535838.2535883)
  (Zombie/Trellys fragment separation). [casinghino-popl14]
- **Brady** — "Idris 2: Quantitative Type Theory in Practice", ECOOP 2021, DOI
  [10.4230/LIPIcs.ECOOP.2021.9](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2021.9).
  [brady-ecoop21]
- **Moon, Eades, Orchard** — "Graded Modal Dependent Type Theory", ESOP 2021, arXiv
  [2010.13163](https://arxiv.org/abs/2010.13163) (grades ⊥ dependency compose).
  [moon-esop21]
- **Eisenberg, Weirich** — "Dependently Typed Programming with Singletons", Haskell 2012,
  DOI [10.1145/2364506.2364522](https://dl.acm.org/doi/10.1145/2364506.2364522).
  [eisenberg-haskell12]
- **Griesemer et al.** — "Featherweight Go", OOPSLA 2020, DOI 10.1145/3428217; **Ellis et
  al.** — "Generic Go to Go: Dictionary-Passing, Monomorphisation, and Hybrid", ICFP 2022,
  arXiv [2208.06810](https://arxiv.org/abs/2208.06810) (instance-discovery
  non-termination). [griesemer-oopsla20], [ellis-icfp22]
- **Lutze, Schuster, Brachthäuser** — "The Simple Essence of Monomorphization", OOPSLA
  2025, DOI [10.1145/3720472](https://dl.acm.org/doi/10.1145/3720472) (flow-based
  monomorphization incl. higher-rank/existentials; "polymorphic packing").
  [lutze-oopsla25]
- **In-repo anchors**: `Bang/Core/IR.lean:229` (no ∀; `tvar` is μ-only) · ADR-0027/0075/
  0079–0083 (the elaborate-to-mono arc) · `effects-vs-cic.md` (the CBPV compose point +
  Herbelin; the R6 frame) · `kernel-substrate-survey.md` §2c/§2e (the base matrix this
  extends) · `verification-ladder.md` (HoTT verdict; "won five times") · Q40 (JIT-mono =
  same strategy late) · Q42 (parametricity now, Curry-Howard later) · #47 (the total
  fragment — the ΠV prerequisite) · `refinement-types-survey.md` (R5, the value-side
  face).
