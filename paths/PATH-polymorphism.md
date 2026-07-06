# PATH · Polymorphism — the multi-session initiative (ADR-0027 staged, ADR-0075 architecture)

**Goal:** a generic, reusable, lawful stdlib — the gate the #50 dogfood limit pointed at, and the Q26
optics / lawful-polymorphism northstar. **Architecture (ADR-0075, don't re-derive):** polymorphism is a
TESTED checker/elaborator over the MONOMORPHIC verified kernel (elaborate-to-mono → kernel untouched,
census-stable) · BIDIRECTIONAL with the decidability stratification (HM-inferred → annotation-checked →
asserted) · ROW-polymorphism first-class. Reference: **Dunfield-Krishnaswami** (HM-infer + annotation-
required rank-n) · Leijen/Koka (row poly).

## The two orthogonal axes

```
POWER (expressiveness)                 DECIDABILITY (how the type is established — the V→T→A stratification)
mono → HM → System F → Fω/HKT          INFERRED (HM, decidable, no annotation)          ← "verified" tier
     → dependent/refinement            ANNOTATION-CHECKED (rank-n/dep: infer undecidable, ← "tested vs spec"
                                          check decidable given the annotation)            (annotation = the
                                       ASSERTED/postulate (can't check — trust me)          Div-analog descent)
```
Decidability is the INVARIANT: un-annotated-undecidable = TYPE ERROR, never an unsound guess.

## The bite ladder (each: SPIKE the mechanism first à la recursion, then an ADR)

```
bite  unlocks                                          power     decid.        touches        status
──────────────────────────────────────────────────────────────────────────────────────────────────
0   type vars + HM rank-1 inference                    HM        inferred      checker (leaf)  SPIKE ✅ / in-place NEXT
      id, const, compose; map over List a (pure)       — spike `Bang/Frontend/HMSpike.lean` (e946adb): POSITIVE
0b  ROW polymorphism (generic over effect rows)        HM+row    inferred      checker (leaf)  after 0
      map : ∀a b ρ. (a -> b ! ρ) -> List a -> List b ! ρ
1   generic DATA types                                 HM        inferred      surface+checker after 0b
      data List a = Nil | Cons(a, List a) — subsumes StrList/IntList/TokList; String = List Char literal
2   generic TRAITS + bounds (typeclasses + laws)       HM+bound  inferred      checker+elab    after 1
      trait Monoid a; fold : Monoid a => List a -> a   ← the generic-lawful-stdlib payoff (Q26)
      ⚠ FORK: dictionary-passing vs monomorphization (both elaborate-to-mono; ADR-0075 defers to here)
3   higher-rank (System F)                             System F  ANNOTATION    checker (bidir) later
      (∀a. a -> a) -> …  — first-class polymorphic values; annotation at the rank boundary
4   higher-kinded (Fω / HKT)                           Fω        annotation    checker+elab    later (Q26)
      trait Functor f; map : ∀a b. (a -> b) -> f a -> f b  ← "any iterable"; optics northstar
5   dependent / refinement                             dependent annotation +  checker (Q31), later (Q31)
      Vec n · {n : Int // P n}  — needs the TOTAL fragment (#47) for decidable type-level  MAYBE spine
```

## Bite 0 — the first spike (de-risk the substrate)

Prove the HM substrate lands on the bidirectional checker + elaborates to mono kernel terms:
- **Add type variables** to the surface `Ty` (a generic `∀`/type-var form — distinct from `Ty.tVar`
  which is μ-bound-internal). Represent quantified schemes (`∀ā. τ`).
- **Unification** + **let-generalization** (Algorithm-W-style, or the bidirectional D-K variant) for a
  TINY PURE fragment: `id : ∀a. a -> a`, `compose`, `map` over `List a` with PURE functions (no effects
  yet — row-poly is bite 0b).
- **Elaborate to mono**: each generic USE instantiates to a concrete type → the elaborated term is
  monomorphic → it kernel-typechecks (`HasCTy`) + runs (`Source.eval`). Gate: differential — the
  elaborated output passes the existing monomorphic kernel checker + evaluates correctly.
- **Guards**: `id 5 → 5`, `id "hi" → hi` (one `id`, two types — the polymorphism proof); `map` a pure
  fn over a `List a`; a use that SHOULD fail (occurs-check / unbound tyvar) fails loud.
- Success ⟹ the substrate works, kernel untouched. Then bite 0b (row-poly) is the bang-specific add.

## Open forks (decide when reached)

1. **Bite 2: dictionary-passing vs monomorphization** — dict-passing (Haskell; separate compilation,
   effect-system-idiomatic) vs monomorphization (Rust; simpler, faster, code-size cost). Both mono-kernel.
2. **Row-poly representation** — how effect-row variables unify (Rémy rows vs Leijen scoped labels)
   given bang's rows are SETS (invariant #2 / ADR-0001 — idempotent, union=join). Must preserve set-rows.
3. **Bite 5: type-level computation** — the one place that may reach the verified spine (Q31).

## Status

- **2026-07-06:** initiative established (ADR-0075 + this PATH). **Bite-0 SPIKE DONE — POSITIVE**
  (`Bang/Frontend/HMSpike.lean`, `e946adb`; a standalone leaf, census untouched). The HM substrate
  (type-var/scheme rep `HTy` = pure-CBPV + `hole`/unif-var + `rigid`/∀-var; `StateT (Except)`;
  fuel-total unify/zonk/occurs; let-generalization + fresh-hole instantiation) lands cleanly on the
  bidirectional checker. **Killer guard: `let id = {fun x=>x}` used at Int AND (Int*Int) → types + runs
  (6); the DISCRIMINATOR — the SAME body with a `fun`-bound (mono) `id` → FAILS — proves generalization
  is load-bearing.** Elaborate-to-mono is TRIVIAL (`Source.eval` untyped → erase-and-run, kernel
  untouched). **NEXT = bite-0 IN-PLACE**: fold HM into `synthSC`/`synthSV` — a mechanical RESTRUCTURE
  (checker types `VTy` structural-eq → `HTy`+holes+zonk; `Except` → `StateT`), NOT a case-add; the two
  "annotate the `fun`" errors dissolve; generalization did NOT resist (a one-shape `.lett` insertion).
  Then **bite 0b = row polymorphism** (rows are SETS, invariant #2 → open-row unification, Rémy/Leijen —
  the bang-specific add). No spine work; ADR-0075 holds unrevised.
- Motivation banked: #50 (the tokenizer's reusable-helper limit) is the concrete need; traits+laws
  (ADR-0068) work NOW but monomorphic — bite 2 makes them generic.
