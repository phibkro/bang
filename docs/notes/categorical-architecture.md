# The categorical reading of bang's architecture

> **Epistemic status — READING, not formalization.** The repo proves everything
> *operationally* + via *step-indexed logical relations* in Lean. Nothing below is
> constructed or checked categorically. This is the shape those operational/LR proofs
> take, written in the language of objects and morphisms because that language is
> clarifying. Tags: **[THM]** = an in-repo theorem or a cited result we instantiate;
> **[READ]** = a structural analogy, faithful but unproven here.
>
> Single source of truth: the architecture-in-force is **ADR-0016**; the row algebra is
> **ADR-0001 / ADR-0018**; capability-by-identity is **ADR-0054 / ADR-0055**; the
> cap-non-escape soundness story is **ADR-0056 / ADR-0057 / ADR-0060**. This note links
> them through a categorical lens; it does not restate their content.

## 1. The objects live in three categories

```
 𝒱   value types        unit · int · cap ℓ · U φ C · A+B · A×B · μX.A      objects
 𝒞   computation types  F q A · arr q A B                                  objects
 ── graded by ──
 (Mult, ·, 1)   multiplicities q     [QTT grades]      a monoidal category
 (Eff, ⊔, ⊥)    effect rows φ        [ADR-0018]        a join-semilattice (poset)
```

**[READ]** Morphisms in 𝒱/𝒞 are well-typed terms-in-context. The two grade structures
are the *colours* on the wires — and both turn out to be load-bearing (§5, §6).

## 2. The kernel is one graded adjunction

Levy's CBPV **[THM, cited]**: the value/computation polarity *is* an adjunction `F ⊣ U`.
Bang grades it — `F` by a multiplicity `q`, `U` by an effect row `φ`:

```
        F_q                          force   = counit ε  (run a thunk:  $)
   𝒱 ⥦──────⇄──────⥧ 𝒞              thunk   = unit  η  (defer:  bare name)
        U_φ                          ret     = monad unit into T

   the zig-zag (triangle identities):

      A                 U C
      │ η                │
   ┌──┴──┐ ret        ┌──┴──┐
   │ F   │            │     │ force
   └──┬──┘            └──┬──┘
      │ ε  force          │
     FUA  → A            U C   (thunk ∘ force = id)
```

This is the categorical content of glossary terms: `$` / force, bare-name / thunk,
`:` vs `=` (ADR-0005's "equality over thunks") all live here.

## 3. The grade is a *semilattice*-graded monad — and idempotence is the point

A graded monad on 𝒞 graded by `(E,⊗,I)` is a family `T_e`, unit `η : Id → T_I`,
multiplication `μ_{e,e'} : T_e T_{e'} → T_{e⊗e'}`, plus monotone coercions when `E` is a
poset (Katsumata POPL'14) **[THM, cited]**. Bang instantiates `E = (Eff, ⊔, ⊥)`
**[THM, in-repo: ADR-0018]**:

```
   monoid op  ⊗  =  ⊔   (row union = join)        unit  I = ⊥  (pure)
   coercion   φ ≤ φ'   (subeffecting = lattice order = "lacks" membership)
   μ : T_φ T_φ' → T_{φ⊔φ'}
```

The non-obvious part: **the grading monoid is idempotent** (`φ ⊔ φ = φ`), so
`μ_{φ,φ} : T_φ T_φ → T_{φ⊔φ} = T_φ`. **[READ]** That is invariant #2 ("rows are sets, not
multisets") read categorically — re-performing an effect doesn't accumulate grade. It
makes `T` a **lax functor from the poset `(Eff,≤)` into `[𝒱,𝒱]`**, strictly weaker than an
arbitrary `ℕ`-graded monad — and the weakness is *bought capability*: idempotence is what
lets a row be a `Finset` with decidable membership, which is what dispatch runs on. A
constraint that generates a mechanism.

**The paradigm = the grade** **[THM, framing]**: the monad `T_φ = U_φ ∘ F`, graded by the
row, is exactly "which effects a function may perform."

## 4. Handlers are algebras — the structural half; the equations are deliberately skipped

Plotkin–Pretnar **[THM, cited]**: for a theory `(Σ,E)` with free monad `T`, an EM-algebra
`(X, α : TX → X)` *is* a model — an interpretation of each operation respecting the
equations; a handler's `return`-clause + op-clauses supply `α`, and handling is the unique
algebra hom from the free algebra (the computation) into `(X,α)`.

Bang's `Handler` object is exactly three carriers **[THM, in-repo: Core.lean]** (a fourth
is a 6th-primitive ADR — invariant #5):

```
 handler        theory of ℓ            algebra (X, α)                  status
 ───────        ──────────             ─────────────                   ──────
 throws ℓ       exception (abort)      X + E → X   (a map E → X)       cleanest EM-algebra
 state ℓ s      get/put (7 eqns)       X^S → X^S   (parameter-passing) algebra on X^S
 transaction ℓ  read/write/retry       carrier threads the journal Θ   schematic; v1 = single-
                                                                       threaded (ADR-0030)
```

**The honest limit — [READ], and the cost named.** Bang does *not* impose or verify the
theories' equations (state's 7 laws, etc.). So bang's handlers are "handlers into the
operational free model" — the *structural* half of handler≈algebra, **not verified
EM-algebras**. That's a stratification choice: the algebra *laws* belong to the
differential-tested superset, not the verified core. Promoting them to the core would be a
real proof project, not a relabel. This is the precise boundary of the claim.

## 5. Handling *decrements one generator of the grade*

A handler for `ℓ` discharges **one** join-generator — so `handle` is a *grade-indexed*
algebra map **[THM, in-repo: the handle typing rule + ADR-0057]**:

```
                install the ℓ-algebra h
   T_e  ════════════════════════════════▶  T_{e ∖ ℓ}        answer type A,
        handle (h : handles ℓ) (−)                          s.t. ¬LabelOccurs ℓ A  (B-occ)
```

The inner computation carries `ℓ`; the outer is `ℓ`-discharged; the ADR-0057 B-occ premise
forbids `ℓ` in the *answer object* — "the discharged generator can't leak through the
algebra's output." This is why `handleF` is a **delimiter**: it marks where one generator of
the semilattice grading is introduced and eliminated.

## 6. A `cap` is a reference to an algebra instance — and the grade bounds its lifetime

The tie that binds the design together. **[READ, tightly grounded]**

```
   categorical              operational (ADR-0054/55)        Lexa (lexical handlers)
   ───────────              ────────────────────────         ───────────────────────
   installed ℓ-algebra      handleF n h   (frame, id n)       the handler frame
   reference to it          vcap n ℓ      (cap by identity)   a POINTER to the handler
   invoking it              perform → splitAtId n → dispatch  DEREFERENCE the pointer
```

A `cap ℓ` value **is** a reference to a specific installed algebra; `splitAtId n` is the
dereference; `perform` applies the algebra's operation. Bang *searches* (`splitAtId`) where
Lexa *dereferences* — same object, different access cost (see `compiler-overview.md` §8).

Now the **two gradings interlock** — this is exactly the cap-non-escape soundness result
(**ADR-0060**):

```
   φ  (effect row, on U)   :  WHICH algebras are in scope          (semilattice grade)
   q  (multiplicity, on F) :  whether THIS reference gets invoked   (QTT grade)

   soundness diagonal  =  NonEscape  =  "no dangling algebra-reference"
                          (every LIVE cap resolves to an in-scope algebra instance)

   grade-driven liveness gate   b ∧ decide(q ≠ 0)   =
        a cap may outlive its algebra ONLY at q = 0,
        where "outlive" is VACUOUS because the algebra is never dereferenced.
```

**[THM, in-flight: ADR-0060 / task #41]** The categorical sentence for the wall we close:
the QTT multiplicity on the returner **bounds the lifetime of the effect-algebra
reference**; a cap escapes its handler's extent iff it does so at grade 0 — a pointer that
is provably never dereferenced. The escape counterexample (`app (lam (ret vunit)) w`) is
precisely a grade-0 reference to a torn-down algebra: categorically harmless, which is why
the language is sound and why the *grade*, not the type, is what witnesses it. (The grade
rig must be `NoZeroDivisors` + `ZeroSumFree` + `Nontrivial` for this to compose — ADR-0060.)

## 7. Compilation is a functor with two factorizations

ADR-0016, two hops. Objects = IRs; the interesting morphisms are the *proofs* (2-cells):

```
  Source ──elab──▶ (Comp, φ) ──compile──▶ Code ──lower──▶ Wasm
                      │  ╲                  │   ╲
                      │   ╲ eval            │    ╲  (Benton–Hur LR)
                     eval  ╲               exec   ╲
                      ▼     ◀───────────────▼      ▼
                    Value   exec ∘ compile = eval  ≈_obs
                            └─ hop 1: Bahr–Hutton ─┘ └ hop 2 ┘
```

- **Hop 1 [THM]:** the machine is the *factorization of `eval` through `Code`* —
  `exec ∘ compile = eval`, **calculated, not designed** (invariant #4). That commuting
  triangle *is* "the VM is an output of the calculation."
- **Hop 2 [THM, in progress]:** `lower` is correct iff a logical relation
  `R ⊆ Code-cfg × Wasm-cfg` is preserved by stepping — a bisimulation-shaped 2-cell, not an
  equation.

## 8. The verification objects are relations (subobjects of a product)

The two routes we live in are both subobjects of a product — the categorical shape of a
logical relation:

```
  route β  (soundness)            route α  (compiler correctness)
  ─────────────────────          ───────────────────────────────
  NonEscape ↪ Config             CrelK ↪ Config × Config
  a SUBOBJECT (unary pred)       a RELATION (span Config ← R → Config)
  preserved by `step`            preserved by `step` (step-indexed)
  = a coalgebra invariant        = contextual equivalence
```

**[READ]** The **stratification** (verified core ⊂ tested superset, ADR-0026/0028) is the
inclusion of a subcategory: the **total fragment** is where the monad collapses to the
`⊥`-row (pure, System F), and **descent** is the inclusion functor `total ↪ Div`, marked by
the `Div` effect in the row. The seam is literally an arrow in the effect lattice.

## 9. The one-line summary, and the ROI on formalizing

> **Bang is a graded `F ⊣ U` adjunction (the kernel) whose grade is an idempotent-
> semilattice-graded monad (the paradigm) with algebras (the runtimes); `handle` is a
> grade-decrementing algebra map discharging one generator; a `cap` is a reference to an
> algebra instance; and the soundness theorem says the QTT grade bounds that reference's
> lifetime. Compilation is a functor whose correctness is the commuting triangle
> `exec∘compile = eval` (hop 1) and a step-indexed relation (hop 2).**

**Should any of this be formalized in Lean?** Not on current evidence. None of the
monad/algebra/functor structure is *constructed* in-repo — the proofs target the operational
shadows (dispatch, preservation, the LRs), and that is canonical. Formalizing the graded
monad + the algebra correspondence would be a genuine effort whose payoff is *explanatory*,
not new safety. Spend the proof budget there only if the categorical layer starts **buying a
theorem we cannot get operationally** — which, so far, it has not. This note exists to make
the structure legible, not to schedule its formalization.

---

*References:* ADR-0016 (two-hop) · ADR-0001/0018 (row lattice) · ADR-0054/0055 (cap-by-
identity) · ADR-0056/0057/0060 (cap-non-escape + grade-driven liveness) · ADR-0026/0028
(stratification) · ADR-0030 (STM-as-handler) · `compiler-overview.md` (the Lexa comparison).
Cited: Levy (CBPV); Plotkin–Pretnar (handlers); Katsumata, Fujii–Katsumata–Melliès (graded
monads); Bahr–Hutton (calculated machines); Benton–Hur (cross-language LR).
