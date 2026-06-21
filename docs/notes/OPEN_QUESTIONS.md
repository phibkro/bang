# Open questions — design decisions deferred

> Questions that surfaced during work but were intentionally deferred. Each
> entry includes: **the question**, **why it matters**, **options under
> consideration**, **what blocks resolution**, and a **revisit signal**.
>
> Discipline (per `docs/notes/spec-proof-discipline.md`): never silently
> mutate a theorem statement or definition to dodge a question; record it
> here instead. A red build with honest gaps beats a green build that lies.

## Index

- [Q1 — Eff algebra: Semiring vs Lattice](#q1--eff-algebra-semiring-vs-lattice)
- [Q2 — Mult = QTT concretization](#q2--mult--qtt-concretization)
- [Q3 — Ctx representation: List vs FinMap](#q3--ctx-representation-list-vs-finmap)
- [Q4 — `handle` typing rule: simplified vs label-removing](#q4--handle-typing-rule-simplified-vs-label-removing)
- [Q5 — `up` typing rule + opArgTy/opResTy](#q5--up-typing-rule--oparGty-opresty)
- [Q6 — Source.step's deep-handler resumption](#q6--sourcestep-deep-handler-resumption)
- [Q7 — Operation names as strings vs symbolic enum](#q7--operation-names-as-strings-vs-symbolic-enum)
- [Q8 — `group_recovers` bridge: E group ⇒ F dagger-Frobenius?](#q8--group_recovers-bridge-e-group--f-dagger-frobenius)

---

## Q1 — Eff algebra: Semiring vs Lattice

**Question**: what algebraic structure does `Eff` (the effect-row grade) have?

**Why it matters**: blocks ◊2 finalization (concrete `Eff = Finset Label`
needs an algebra; current `[Semiring Eff]` doesn't fit Finset).

**Detail**: Spec.lean has `variable {Eff : Type} [Semiring Eff]`. Our
intended concrete is `Eff = Finset Label`. The clash:
- Semiring requires `0 * a = 0` (zero absorption in multiplication).
- For effect rows, `*` naturally means "sequencing of effects" = union `∪`.
- But `∅ ∪ a = a`, not `∅`. So `Finset Label` doesn't form a Semiring
  under `(+, *) = (∪, ∪)`.

**Options**:
1. **Spec change**: replace `[Semiring Eff]` with `[Lattice Eff] [OrderBot Eff]`
   (Finset has these natively). Change `l * e` in `no_accidental_handling`
   to `l ⊔ e` or `l + e` (join). Theorem *shapes* stay; the typeclass and
   one operator change.
2. **Different Eff carrier**: use `Nat` (clock-counting, à la Torczon).
   Loses the row-of-labels reading; conflicts with ADR-0001 (rows-as-Finset).
3. **Keep parametric**: don't concretize Eff; let instantiation happen at
   the theorem use-site. Punts the question.

**Recommended**: (1). The `Semiring` was inherited from Torczon's
clock-effect example; it doesn't fit our row-of-labels model. Lattice is
the honest fit for ADR-0001.

**Blocked on**: design decision from orchestrator.

**Revisit signal**: any work that needs to instantiate `Eff` concretely
(e.g., `no_accidental_handling` proof; `traceWithin` definition; the
`effect-row well-formedness` axioms in Spec.lean §0.5).

---

## Q2 — Mult = QTT concretization  · ✓ RESOLVED 2026-06-21

**Resolution**: Concretized as `Bang.QTT` in `Bang/Mult.lean`. CommSemiring
instance via case analysis (3 enum elements; proofs by `cases <;> rfl`).
Build green on first try, smoke-tested via `tools/eval.sh`.

The spec stays parametric in `[Semiring Mult]`; QTT is one valid instance
(the bang-lang default per ROADMAP.md). Phase B proofs may specialize to
QTT or stay parametric depending on what the proof needs.

---

## Q3 — Ctx representation: List vs FinMap

**Question**: is the current `List (Var × Mult × VTy)` representation good
enough, or should `Ctx` be a `FinMap Var (Mult × VTy)`?

**Why it matters**: `Ctx.add Γ₁ Γ₂` currently uses `List.zipWith` which
requires matching variable lists in matching order. A FinMap representation
handles arbitrary contexts cleanly.

**Options**:
1. Keep List + zipWith. Document the precondition (matching shape).
   Proofs work for "well-formed pairs"; harder when contexts diverge.
2. Switch to FinMap. Cleaner arithmetic; richer typeclass requirements
   (decidable Var equality, ordering for canonicalization).
3. Switch to a custom `Multiset (Var × Mult × VTy)` or similar.

**Recommended**: (1) for now. Switch to (2) if/when proofs surface the
need (typical Phase B compat lemmas may demand arbitrary Γ₁ + Γ₂).

**Blocked on**: nothing. Defer until proofs demand.

**Revisit signal**: a Phase B compat lemma that can't be stated cleanly
under the current Ctx representation.

---

## Q4 — `handle` typing rule: simplified vs label-removing

**Question**: the current `HasCTy.handle` rule says the handled computation
has the SAME effect grade as the unhandled body. The "real" rule should
REMOVE the handler's handled label from the effect row.

**Detail**: current rule (Phase A part 2 first cut):
```
| handle : HasCTy Γ M φ B → HasCTy Γ (handle h M) φ B
```
Real rule (label-removing):
```
| handle : HasCTy Γ M (φ ⊎ {ℓ_of_h}) B → HasCTy Γ (handle h M) φ B
```

**Why it matters**: type safety + soundness depend on the handler actually
discharging an effect. Without removal, the effect row never shrinks.

**Blocked on**: depends on Q1 (Eff algebra) — "remove label from row"
requires concrete row operations.

**Revisit signal**: Phase B proof of `preservation` or `effect_sound`
fails because handler doesn't discharge.

---

## Q5 — `up` typing rule + opArgTy/opResTy

**Question**: the `HasCTy.up` constructor was OMITTED in Phase A part 2
because it depends on `opArgTy` and `opResTy` (which are still axioms in
§5 LR helpers).

**What we'd want**:
```
| up : ℓ ∈ φ → HasVTy Γ v (opArgTy ℓ) → HasCTy Γ (up ℓ op v) φ (F q (opResTy ℓ))
```

**Blocked on**: concrete `opArgTy` / `opResTy` (needs an effect signature
registry; either built into Eff or carried separately).

**Revisit signal**: cannot type-check programs that use `perform` (i.e.,
literally any effectful program).

---

## Q6 — Source.step's deep-handler resumption

**Question**: the current `Source.step` uses substitution-based small-step.
When `handle h (up ℓ op v)` doesn't match (h doesn't handle ℓ.op), we
return `none` (stuck). The "correct" behavior for deep handlers is to
propagate `up` outward while the inner handler is preserved for the
resumption.

**Why it matters**: real algebraic-effect programs nest handlers and
resume across multiple handler frames. Current Source.step can't model
this.

**Options**:
1. Keep substitution-based; accept it can't handle deep resumption. Use a
   different operational semantics for that.
2. Migrate to a CK-machine: `Source.step` operates on `EvalCtx × Comp`.
   The `Frame` ADT (§1.3) is already defined for this. Handler propagation
   captures the prefix-context as the resumption.
3. Add explicit continuation reification (CalcReify-style); Comp.up
   carries the captured continuation as data.

**Recommended**: (2) when proofs need deep handlers. The Frame / EvalCtx
infrastructure is already there.

**Blocked on**: nothing. Just session time to migrate.

**Revisit signal**: writing test programs that demonstrate handler
nesting, or Phase B proofs of `compile_forward_sim` for multi-handler
programs.

---

## Q7 — Operation names as strings vs symbolic enum

**Question**: `Comp.up` carries an `OpId := String`. Source.step matches
on string literals `"raise"`, `"get"`, `"put"`. String-typed operation
names lose type safety (no exhaustiveness check; typos compile).

**Options**:
1. Keep `OpId = String`. Pragmatic; user-extensible.
2. Symbolic enum: `inductive OpId | raise | get | put | ...`. Type-safe
   but not extensible without modifying the kernel.
3. Per-effect operation namespacing: each `Eff` carries its own operation
   alphabet (similar to algebraic theory presentation).

**Recommended**: (1) for now. Revisit if proofs demand string-free
operations.

**Blocked on**: nothing. Style/ergonomics question.

**Revisit signal**: cannot prove a property because it requires
exhaustive case analysis on operation names.

---

## Q8 — `group_recovers` bridge: E group ⇒ F dagger-Frobenius?

**Question** (from the original wasmfx spec; surfaced in ADR-0016 + §6 of
Spec.lean): if `Eff` forms a group (effects are invertible), does the
graded monad `F` become dagger-Frobenius (Heunen-Karvonen)? If yes,
`group_recovers` is a corollary. If no, the theorem needs an explicit
observability side-condition.

**Why it matters**: rollback semantics (PROOF_ORDER #2 in
`docs/notes/spec-proof-discipline.md`). Genuine research question.

**Blocked on**: literature review (Heunen-Karvonen, compositional reversible
computation). References on disk:
- `references/papers/reversible-frobenius/heunen-karvonen-reversible-monadic.pdf`
- `references/papers/reversible-frobenius/compositional-reversible-2024.pdf`

**Revisit signal**: Phase B PROOF_ORDER #2 (sequenced second precisely so
this surfaces before compiler work depends on it).

---

## Adding a new question

Append below with the same format:
- Question (one sentence)
- Why it matters
- Detail
- Options
- Recommended (if any)
- Blocked on
- Revisit signal
