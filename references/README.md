# bang-lang reference library

This directory holds papers and books supporting the bang-lang verification work.
Citation keys match BibTeX entries in `refs.bib`. Per-paper reading notes go in `notes/`.

## What's here

### Effects & handlers
- `papers/effects-handlers/biernacki-popl18-handle-with-care.pdf` — logical relations for effect handlers; **spine of the LR** (Vrel/Srel/Krel/Crel); §5.4 set-row fragment licenses bang-lang's ρ-map-free model
- `papers/effects-handlers/plotkin-pretnar-esop09-handlers.pdf` — **handler semantics origin** (Plotkin, Pretnar); the operational story `compile_forward_sim` lowers to typed continuations
- `papers/effects-handlers/bauer-pretnar-algebraic-effects-and-handlers.pdf` — foundational tutorial; effect syntax and denotational semantics
- `papers/effects-handlers/tang-popl24-soundly-handling-linearity.pdf` — *(Pass-B)* control-flow linearity for multi-shot handlers; relevant to the CalcReify frontier and `runState × throw` decision

### Graded CBPV
- `papers/graded-cbpv/torczon-oopsla24-effects-coeffects.pdf` — **the substrate** for bang-lang's graded CBPV; Coq mechanization, resource-aware dynamics
- `papers/graded-cbpv/katsumata-popl14-parametric-effect-monads.pdf` — **graded monad laws**; ordered-monoid effects; soundness of (subeffecting); the F-monad shape `Crel` follows

### Logical relations
- `papers/logical-relations/ahmed-esop06-step-indexed-syntactic.pdf` — **step-indexed syntactic LR for recursive and quantified types** (Ahmed); well-founded recursion on step-index — the foundational technique
- `papers/logical-relations/pitts-step-indexed-biorthogonality.pdf` — **biorthogonality + step-indexing in tutorial form** (Pitts); the combination move the LR uses
- `papers/logical-relations/proving-correctness-step-indexed.pdf` — additional step-indexed LR notes (provenance unverified)

### Verified compilation
- `papers/verified-compilation/benton-hur-icfp09-biorthogonality-step-indexing.pdf` — **template for `compile_forward_sim`**; biorthogonality + step-indexing for compiler correctness (Benton, Hur)
- `papers/verified-compilation/kumar-popl14-cakeml.pdf` — **the verified-compiler model we're imitating** (CakeML; verified ML→ASM); architecture reference for the two-hop story (ADR-0016)

### Graded CBPV *(cont.)*
- `papers/graded-cbpv/weirich-wg211-2024-cbpv-effects-coeffects-slides.pdf` — Weirich's WG2.11 talk slides for the Torczon OOPSLA'24 paper; same material, slide-form

### WasmFX target
- `papers/wasmfx-target/phipps-costin-pacmpl23-continuing-webassembly.pdf` — **the WasmFX proposal** (Phipps-Costin, Rossberg et al.); typed continuations, `suspend`/`resume`; the target abstract syntax for `compile_forward_sim`
- `papers/wasmfx-target/ma-oopsla24-lexa.pdf` — *(Pass-B)* Lexa: stack-switching handler compilation, formal stack semantics; template for lowering effect handlers to typed continuations
- `papers/wasmfx-target/ma-oopsla25-zero-overhead-handlers.pdf` — *(Pass-B)* Zero-overhead lexical handlers (Ma et al. follow-up); cost-aware compilation
- `papers/wasmfx-target/emrich-hillerstrom-continuing-stack-switching-wasmtime.pdf` — Wasmtime-side report on implementing stack switching; engineering counterpart to the proposal

### Calculated compilers
- `papers/calculated-compilers/bahr-hutton-calculating-effectively.pdf` — deriving a correct stack-machine compiler by equational calculation; the source of the K2/K3 method
- `papers/calculated-compilers/bahr-hutton-dependently-typed.pdf` — extending the calculation to dependently-typed compilers
- `papers/calculated-compilers/monadic-compiler-calculation.pdf` — monadic framing of the calculation (relevant to effects)
- `papers/calculated-compilers/swierstra-compilation-alacarte.pdf` — modular compiler components via data types à la carte
- `papers/calculated-compilers/hutton-bahr-jfp17-compiling-50-year-journey.pdf` — JFP'17 functional pearl; survey of the calculation tradition K2/K3 sits in

### Reversible / Frobenius
- `papers/reversible-frobenius/heunen-karvonen-reversible-monadic.pdf` — reversible computation via monadic structure; dagger-Frobenius. **`group_recovers` rests on this** — does `E` a group ⇒ `F e` dagger-Frobenius?
- `papers/reversible-frobenius/compositional-reversible-2024.pdf` — recent compositional treatment; graded instance

### Cost / AARA
- `papers/cost-aara/chu-guo-hoffmann-oopsla26-aara-effects.pdf` — AARA extended to algebraic effects and handlers; *(Pass-B)* relevant if cost-grading is later added as a third grade

### Type theory *(adjacent)*
- `papers/type-theory/bove-dybjer-dependent-types-at-work.pdf` — Agda/Martin-Löf primer; background for the Lean encoding choices
- `papers/type-theory/tang-hillerstrom-structural-subtyping-as-parametric-polymorphism.pdf` — structural subtyping via row polymorphism; useful if effect-row subeffecting moves toward subtyping
- `papers/type-theory/wilshaw-hutton-flow-typing-lightweight-linearity.pdf` — flow typing for linearity; cross-reference for the AARA / linearity story

### Partial evaluation / staging *(adjacent)*
- `papers/partial-evaluation/jones-gomard-sestoft-partial-evaluation-book.pdf` — the foundational PE textbook (Jones, Gomard, Sestoft)
- `papers/partial-evaluation/taha-multi-stage-programming-thesis.pdf` — Walid Taha's MSP thesis; staging-as-language-design
- `papers/partial-evaluation/williams-perugini-revisiting-futamura-projections.pdf` — diagrammatic restatement of the Futamura projections

### PL semantics *(adjacent)*
- `papers/pl-semantics/hutton-jfp23-programming-language-semantics-1-2-3.pdf` — Hutton's JFP'23 tutorial on the three styles (denotational/operational/axiomatic)

### Category theory *(adjacent)*
- `papers/category-theory/boisseau-gibbons-yoneda-profunctor-optics.pdf` — Yoneda + profunctor optics functional pearl; background for the LR's representation choices

### Tooling
- `papers/tooling/de-moura-ullrich-lean4-system-description.pdf` — the Lean 4 system-description paper
- `papers/tooling/smt-lib-standard-v2.7.pdf` — SMT-LIB v2.7 standard reference
- `papers/tooling/dolstra-purely-functional-software-deployment-thesis.pdf` — Dolstra's Nix thesis (build/deploy reproducibility — context for the dev environment)

### General *(off-topic but archived)*
- `papers/general/ashby-introduction-to-cybernetics.pdf` — Ashby (1956); systems-thinking background reading
- `papers/general/mokhov-jfp20-build-systems-a-la-carte.pdf` — Mokhov, Mitchell, Peyton Jones; build-systems framework
- `papers/general/peng-nous-efficient-pretraining-token-superposition.pdf` — ML preprint; off-topic
- `papers/general/bloom-sawin-arxiv2605-sum-product-conjecture-false.pdf` — number-theory preprint; off-topic

> Some papers have a sha256-distinct second PDF rendering on disk with an `-alt`
> suffix (e.g. `plotkin-pretnar-esop09-handlers-alt.pdf`,
> `torczon-oopsla24-effects-coeffects-alt.pdf`). Same content, different bytes;
> cite the non-alt key.

---

## External resources

Live online resources we link to rather than mirror. Reach for these when looking
beyond the on-disk corpus.

### Bibliographies & indices
- **[yallop/effects-bibliography](https://github.com/yallop/effects-bibliography)**
  — community-maintained index of effect-handler literature; canonical starting
  point when looking for a paper not yet on disk.
- **[effect-handlers.org](https://effect-handlers.org/)** — EHOP portal: curated
  papers, projects, implementations, and a tutorial index.

### Reference implementations
- **[plclub/cbpv-effects-coeffects](https://github.com/plclub/cbpv-effects-coeffects)**
  — Coq mechanization of Torczon et al. OOPSLA 2024 (the bang-lang substrate).
  **Cross-check our Lean defs against their Coq** when in doubt — same judgments,
  same lemmas, ported. Cited from `Bang/Spec.lean`. Clone locally if/when needed
  for line-by-line comparison.

### Benchmarks
- **[effect-handlers/effect-handlers-bench](https://github.com/effect-handlers/effect-handlers-bench)**
  — cross-language effect-handler benchmark suite. *(Post-◊5 relevance.)* When
  the WasmFX backend has something to compare, this is the natural target;
  add a `PATH-benchmark-against-ehop` then.

---

## Gaps — still to fetch

Pass A = urgent (LR spine + verified-compilation template).
Pass B = fetch when relevant hop is being worked on.

### Pass A
**Complete.** All six Pass-A papers are on disk.

### Pass B (fetch when needed)
- Tang, Lindley. Modal Effect Types (OOPSLA 2025) — modal alternative to lacks-discipline
- Niu et al. calf (POPL 2022); Grodin et al. decalf (POPL 2024) — mechanized cost
- Balik et al. Deciding Not to Decide (ESOP 2026) — Coq-mechanized inference for constrained rows
- Voigt et al. Dynamic Wind (OOPSLA 2025) — rollback/cleanup operational
- Atkey. QTT (LICS 2018); McBride. I Got Plenty o' Nuttin' (2016) — origins of the multiplicity grade
- Gaboardi et al. Combining Effects and Coeffects (ICFP 2016) — graded comonads
- Orchard et al. Granule (ICFP 2019) — graded modal types in practice
- Appel, McAllester. Indexed Model of Recursive Types (TOPLAS 2001) — foundations of step-indexing
- Katsumata. ⊤⊤-Lifting (CSL 2005) — the original ⊤⊤-lifting technique

---

## Conventions

- Filenames: `<firstauthor>-<venue><year>-<keywords>.pdf` (lowercase, hyphens)
- Citation keys in `refs.bib` mirror filename stems
- Cite from Lean sources as comments. Examples:
  - `-- shape: biernacki-popl18-handle-with-care §5.4`
  - `-- step-index per benton-hur-icfp09-biorthogonality-step-indexing`
  - `-- calculation per bahr-hutton-calculating-effectively`
- Per-paper reading notes go in `notes/<key>.md` (created on demand)
