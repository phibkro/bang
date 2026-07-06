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
0   type vars + HM rank-1 inference                    HM        inferred      checker (leaf)  ✅ DONE (f063c78)
      id, const (first-order let-poly) — RUNS via bang eval; spike `HMSpike.lean` (e946adb) + in-place (f063c78)
      DEFERRED to 0b: higher-order compose (needs computation-level holes), value restriction, row vars
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

## Bite 0b status (2026-07-06): item 1 DONE; items 2+3 = grounded design findings → fresh sessions

- **Item 1 VALUE RESTRICTION — ✅ DONE (`e6cdc93`).** `synthSC .lett` generalizes only `if isValueSurf e`
  (`{…}`/lit/var/pair), else monomorphic. The ML soundness gate, in place before effect-typed poly. Guard
  (via `check`, the type checker): a non-value `if … then {fun} else {fun}` used at two types FAILS.
  Corpus + bite-0 poly guards UNCHANGED, kernel/census untouched.
- **Item 2 COMPUTATION HOLES — ESCALATED (proven bigger than the hook).** A computation hole CANNOT ride
  `CTy` the way a value hole rides `VTy.tvar` — grep-verified it COLLIDES with 57 `.F`/`.arr` matches
  (esp. the 6+ sites extracting a value type from `.F _ A`: `anfSplit`, `elabS .lett`, `checkSC`). ⟹ item 2
  is a proper **`IVTy`/`ICTy` inference-type re-rep** (`IVTy`=`VTy`+`vhole`, `ICTy`=`CTy`+`chole`; subst
  binds both; `force` unifies vhole~`U ρ chole`; convert at boundaries), EFFORT ≈ the bite-0 in-place port.
  Silver lining: this IS the correct-by-construction cleanup (a hole unrepresentable-as-μ-var, retires the
  reserved-`tvar` smell for BOTH kinds). Payoff: `compose` types+runs. → its own fresh-context session.
- **Item 3 ROW VARIABLES — ESCALATED (design pass, AFTER item 2).** Rows are `EffRow = Finset Label`
  (closed). Row-poly needs OPEN rows = `(Finset Label × Option RowVar)` (Rémy-style tail); unification
  `{throws}∪ρ₁ ~ {state}∪ρ₂` → fresh shared tail (set-rows make this SIMPLER than scoped labels — no order,
  union handles dups). Forks for the design pass: (a) does `EffRow` change EVERYWHERE (all `⊔`/`⊆`/`.erase ℓ`
  handler-discharge threading) or stay an inference-only parallel `IRow` with embed/extract? (b) `.erase ℓ`
  on an OPEN row (tail present) needs defined semantics. (c) value restriction (item 1) is the prerequisite —
  now in place. Do AFTER item 2: the `IVTy`/`ICTy` infra is what `IRow` slots into.

## Bite 0b scope (the three items, as the in-place rewrite + item-1 mapped them)

All on the landed `HTy`+`Infer` substrate (`f063c78`), all still checker leaves:
1. **Computation-level holes** (unlock higher-order — `compose`, HKT-lite). `CTy` has no `tvar` (kernel,
   forbidden), so add an INFERENCE-side computation type `ICTy` with holes, zonk to `CT` at the boundary
   (the sibling of the value-hole `HTy`). Today `force`-of-a-value-hole is a DEFINED fail-loud error
   ("annotate — higher-order is 0b"), never a wrong accept — so this is an EXTENSION, not a soundness fix.
   HOOK (hmspike): smallest unblock = a tiny `ICTy` (F/arr + a `chole`); `force` unifies a value-hole with
   `U ρ (chole)`; zonk `ICTy → CT` at the boundary. This is ALSO the moment the correct-by-construction
   `ITy`/`ICTy` rep pays off — do it here rather than extending the reserved-`tvar` ranges further.
2. **⚠ VALUE RESTRICTION (a SOUNDNESS gate for 0b).** Bite-0 generalizes any `let`-RHS holes — SOUND
   today because poly values are syntactic values (`{fun…}` thunks) and effectful RHS have concrete
   types (no holes to over-generalize) + effects can't escape a `let` scope (state discharged, TVars
   `atomically`-confined). But 0b (effect-typed / escaping poly) MUST restrict generalization to
   syntactic VALUES before it can over-generalize an effectful RHS — the classic ML value restriction.
   Do NOT ship 0b without it. HOOK (hmspike): gate on "RHS is a syntactic value (`{…}` thunk / lit / var
   / pair)"; the insertion point is the `.lett` arm in `synthSC`, right before `generalize Γ A`. One predicate.
3. **Row variables** (generic over effect rows). Rows are SETS (invariant #2 / ADR-0001 — idempotent,
   union=join), so a row var unifies via OPEN-ROW (Rémy/Leijen) differently from a type hole — the
   genuinely bang-specific add. HOOK (hmspike): bite-0 runs a SEPARATE `Infer` per `elabS` resolution
   site (`runInferV`/`runInferC`); row-poly that spans elaborate+check wants the row unifier threaded
   through the SAME `Infer` state.
   **REP DECISION (manager, 2026-07-06) — a PARALLEL inference `IRow`, kernel `EffRow` UNTOUCHED.** SAME
   pattern as poly item 2's `IVTy`/`ICTy` (and the unifying through-line): the KERNEL `EffRow = Finset
   Label` stays CLOSED (invariant #2 preserved, no rippling `⊔`/`⊆`/`.erase ℓ` across the whole spine);
   the INFERENCE layer gets `IRow = (Finset Label × Option RowVar)` (known labels + an optional
   polymorphic tail) that EMBEDS a closed `EffRow` and ZONK-EXTRACTS to a closed `EffRow` at the boundary
   (exactly as `IVTy` zonks to `VTy`). So the whole inference layer is one shape: parallel superset types
   (`IVTy`/`ICTy`/`IRow`) that erase to the closed kernel types — consistent with ADR-0075 elaborate-to-mono.
   Rejected: mutating `EffRow` to `(Finset × Option RowVar)` EVERYWHERE (touches the verified spine's row
   algebra — over-broad; the inference `IRow` keeps it out of the kernel). Unification `{throws}∪ρ₁ ~
   {state}∪ρ₂` → `ρ₁:={state}∪ρ₃`, `ρ₂:={throws}∪ρ₃` (fresh tail ρ₃); set-rows make it SIMPLER than
   scoped labels (no order, idempotent — union handles dups free). Sub-detail for the build: handler
   discharge `.erase ℓ` on an OPEN row (tail present) — the discharged ℓ is CONCRETE (the handler's
   label) so remove it from the known part; the tail ρ carries an implicit ℓ-LACKS constraint (Rémy).
   First cut may restrict to "ℓ in the known part, ρ built ℓ-free"; full lacks-constraints are the
   refinement. VALUE RESTRICTION (item 1) is the prerequisite — in place.

## Open forks (decide when reached)

1. **Bite 2: dictionary-passing vs monomorphization** — dict-passing (Haskell; separate compilation,
   effect-system-idiomatic) vs monomorphization (Rust; simpler, faster, code-size cost). Both mono-kernel.
2. **Bite 5: type-level computation** — the one place that may reach the verified spine (Q31).
3. **Hole encoding cleanup** — bite-0 rides `VTy.tvar` reserved ranges (pragmatic, lowest-regression);
   the correct-by-construction alt (a separate `ITy` where a hole is unrepresentable-as-μ-var) is the
   natural cleanup once 0b adds `ICTy` anyway.

## Status

- **2026-07-06:** initiative established (ADR-0075 + this PATH). **Bite-0 SPIKE DONE — POSITIVE**
  (`Bang/Frontend/HMSpike.lean`, `e946adb`; a standalone leaf, census untouched). The HM substrate
  (type-var/scheme rep `HTy` = pure-CBPV + `hole`/unif-var + `rigid`/∀-var; `StateT (Except)`;
  fuel-total unify/zonk/occurs; let-generalization + fresh-hole instantiation) lands cleanly on the
  bidirectional checker. **Killer guard: `let id = {fun x=>x}` used at Int AND (Int*Int) → types + runs
  (6); the DISCRIMINATOR — the SAME body with a `fun`-bound (mono) `id` → FAILS — proves generalization
  is load-bearing.** Elaborate-to-mono is TRIVIAL (`Source.eval` untyped → erase-and-run, kernel
  untouched).
- **Bite-0 IN-PLACE DONE — POSITIVE (`f063c78`).** HM folded into the production `synthSC`/`synthSV`/
  `checkSC`/`checkSV` (`Except` → `Infer = StateT USt (Except)`; `A=expected` → `unifyV/unifyC` subsumption;
  `let` → generalize the RHS value type; bare `fun` → fresh domain hole [the annotate-the-fun errors
  DISSOLVED]; holes/rigids ride `VTy.tvar` RESERVED RANGES → no mirror type = lowest regression surface;
  zonk-at-boundary so trait/data/binop resolution + reported types are always CONCRETE). **First-order
  let-poly (`id`/`const`) RUNS via `bang eval`** (`let id = {fun x=>x}` at two types → 6/41 — the standalone
  spike couldn't). **Regression oracle HELD**: 136 existing #guards UNCHANGED + 8 poly; broad real-journey
  green (arithmetic/recursion/strings/Vec/caps/handle/tokenizer); kernel/`HasCTy`/`Source.eval` UNTOUCHED
  (primitives OK 25 ctors, census stable, leaf fan-in 0). Honest boundary: higher-order `compose` DEFERRED
  (fail-loud, NOT wrong-accept) → 0b. **NEXT = bite 0b** (see scope below). No spine work; ADR-0075 unrevised.
- Motivation banked: #50 (the tokenizer's reusable-helper limit) is the concrete need; traits+laws
  (ADR-0068) work NOW but monomorphic — bite 2 makes them generic.
