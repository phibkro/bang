# ADR-0075 · Polymorphism = a tested checker/elaborator over the monomorphic verified kernel (elaborate-to-mono); bidirectional inference with annotation-required decidability descent; row-polymorphism first-class

<!-- adr-frontmatter -->

- **Status**: Accepted (the architecture for the polymorphism initiative; bites are staged — see `paths/PATH-polymorphism.md`)
- **Summary**: Polymorphism is realized as inference + elaboration in the CHECKER (a tested superset), NOT as a System F kernel — generic surface code ELABORATES to MONOMORPHIC kernel terms (monomorphization / dictionary-passing), so the verified kernel (`Source.eval`/`HasCTy`/soundness) stays UNTOUCHED, census-stable (the ADR-0026 stratification: verified core + tested superset, seam = elaboration). Type establishment is BIDIRECTIONAL and stratified by DECIDABILITY: HM-INFERRED where decidable (no annotation) → ANNOTATION-CHECKED where inference is undecidable (higher-rank / dependent — the user gives the intended type, checking is decidable) → ASSERTED/postulated (can't check — the escape hatch). Decidability is the invariant: an un-annotated undecidable term is a TYPE ERROR, never an unsound guess — the annotation is the explicit-descent marker (the type-system analog of `Div`). Row-polymorphism (over effect rows, and eventually grades — ADR-0027) is first-class from the first bite.
- **Depends-on**: 0027, 0026
- **Relates-to**: Q26 (HKT/optics — bites 3-4), Q27 (grade variables), Q31 (dependent/refinement — bite 5, may touch the spine), #50 (the dogfood motivation — reusable generic helpers)

- **Status:** Accepted (operator-approved 2026-07-06) — the architecture; individual bites each get their own spike/ADR
- **Date:** 2026-07-06
- **Layer:** C + checker/elaborator (tested superset). Bites 0-4 are surface/checker LEAVES (census untouched). Bite 5 (dependent) MAY reach the spine (type-level computation) — its own decision.
- **Builds on:** ADR-0027 (staged polymorphism: mono v1 → HM → System F + effect-row + grade vars — this records HOW), ADR-0026 (the verified-core/tested-superset stratification — polymorphism rides it). Reference: Dunfield-Krishnaswami "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (the canonical HM-infer + annotation-required-rank-n design); Leijen/Koka row polymorphism.

## Context

Polymorphism (ADR-0027 stage 2+) is the next major DIRECTION — the gate to a generic reusable stdlib
(the #50 dogfood limit: reusable multi-arg/generic helpers are blocked under monomorphism) and the Q26
lawful-polymorphism / optics northstar. Unlike the recursion + strings work (surface/checker leaves,
kernel untouched), polymorphism *could* touch the type-system core. This ADR fixes the architecture so
it DOESN'T (for bites 0-4), and so the type-establishment discipline is decidable-by-construction.

## Decision

1. **ELABORATE-TO-MONO, not a System F kernel.** Polymorphism lives in the CHECKER + ELABORATOR (a
   tested superset). Generic surface code elaborates to MONOMORPHIC kernel terms — via monomorphization
   (instantiate each generic use to a concrete type, Rust-style) or dictionary-passing (Haskell-style;
   the bite-2 fork, deferred to `PATH-polymorphism.md`). The kernel (`Source.eval`, `HasCTy`, the LR,
   soundness, CalcVM) is UNTOUCHED and census-stable. **Seam** = the elaboration; **tested** = the
   elaborated monomorphic term kernel-typechecks + runs correctly (differential, like the current
   checker). Rejected: a System F kernel (the LR/soundness/CalcVM would carry type vars — spine work,
   unnecessary when you can elaborate away; violates the "verified core untouched" property held all
   the recursion/strings work).
2. **BIDIRECTIONAL + the DECIDABILITY stratification** (the Verified→Tested→Asserted move applied to
   typing; recurs at each power level):
   ```
   INFERRED           HM rank-1 (+ row) — decidable, NO annotation           the "verified" analog
   ANNOTATION-CHECKED higher-rank (System F) / HKT / dependent — inference    "tested vs a spec": the
                      UNDECIDABLE, checking DECIDABLE given the annotation     annotation is the oracle
   ASSERTED           postulate / unsafe — can't check, trust me              the escape hatch
   ```
   Bang already has bidirectional synth/check (#45): synth does HM inference (let-generalization) where
   decidable; check consumes annotations where not. **Decidability is the INVARIANT:** an un-annotated
   term that needs annotation is a TYPE ERROR (missing annotation), never an unsound inference — the
   annotation is the explicit-descent marker, the type-system analog of `Div`/fuel. "Fall back to HM" =
   HM-infer is the default; annotation is the opt-in escape to System F where inference can't decide.
3. **ROW-POLYMORPHISM is first-class from bite 0**, NOT deferred. Type-poly must compose with effect-row
   poly (a generic `map : ∀a b ρ. (a -> b ! ρ) -> List a -> List b ! ρ` is useless if it can't be
   polymorphic in the mapping function's effects) — and eventually grade poly (ADR-0027). This is bang's
   genuine extra complexity over textbook HM.
4. **TWO ORTHOGONAL AXES** (like the row and the grade, Q27): the POWER ladder (mono → HM → System F →
   Fω/HKT → dependent) × the DECIDABILITY tier (inferred / annotation-checked / asserted). The
   decidability tier applies at every power level.

## Rejected / not-now

- **System F kernel** — spine work (LR/soundness/CalcVM carry type vars); unnecessary (elaborate away).
- **Undecidable inference with guessing** — unsound; the whole point is decidable-or-annotated.
- **Deferring row-polymorphism** — makes generic `map`/`fold` useless in an effectful language.
- **Committing dict-passing vs monomorphization now** — the bite-2 fork (separate compilation + code
  size vs simplicity + speed; dict-passing is more effect-system-idiomatic, monomorphization simpler).
  Both elaborate-to-mono, so this ADR holds either way; decide at bite 2 (`PATH-polymorphism.md`).

## Consequences

- Bites 0-4 stay surface/checker LEAVES — the verified-kernel-untouched, census-stable property that
  held through recursion + strings CONTINUES. This is the big de-risk: no spine work for generics.
- Bite 5 (dependent/refinement, Q31) MAY reach the spine (type-level computation needs the total
  fragment #47) — its own decision when reached.
- The initiative is multi-session; `paths/PATH-polymorphism.md` is the tracker (bite ladder + status +
  the open forks). Each bite gets a spike (de-risk the mechanism first, à la recursion) then an ADR.

## Revisit if

- Bite 2 is reached → decide dict-passing vs monomorphization.
- Bite 5 (dependent) is reached → the type-level-computation / spine question.
- A concrete need forces first-class polymorphic VALUES at runtime (would pressure the elaborate-away
  choice — but even then, defunctionalization keeps the kernel mono).
