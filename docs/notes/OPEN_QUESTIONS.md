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
- [Q9 — WasmFX target drift: frozen OOPSLA'23 syntax vs Phase-3 standard](#q9--wasmfx-target-drift-frozen-oopsla23-syntax-vs-phase-3-standard)

---

## Q1 — Eff algebra: Semiring vs Lattice  · ✓ RESOLVED 2026-06-21 — Option (a)

**Resolution**: Switched `[Semiring Eff]` → `[Lattice Eff] [OrderBot Eff]`
across all modules (Core / Syntax / Operational / LR / Spec). The effect
algebra is now:
  - `⊥`     = no effects (empty row)
  - `e₁ ⊔ e₂` = combined effects (join)
  - `≤`      = effect inclusion (sub-effecting)

Concrete: `Bang.EffRow := Finset Label` (in `Bang/EffectRow.lean`).
Mathlib gives Finset the required Lattice + OrderBot instances natively.

Knock-on effects:
- `HasCTy.ret` and `HasCTy.lam`: `0 (CTy.F ...)` → `⊥ (CTy.F ...)`
- `HasCTy.letC`: effect combine `φ₁ + φ₂` → `φ₁ ⊔ φ₂`
- `no_accidental_handling`: `l * e` → `l ⊔ e`
- `Disjoint` now concrete via Mathlib's `_root_.Disjoint` for Lattice
  + OrderBot (was axiom — closed)
- `group_recovers`'s `[AddGroup Eff]` hypothesis is now vacuous for our
  Lattice Eff (no Lattice + AddGroup nontrivial instance) — theorem statement
  preserved as conditional; see Q8 for the H-K bridge question

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
- `references/papers/adjacent/heunen-karvonen-reversible-monadic.pdf`
- `references/papers/adjacent/compositional-reversible-2024.pdf`

**Revisit signal**: Phase B PROOF_ORDER #2 (sequenced second precisely so
this surfaces before compiler work depends on it).

---

## Q9 — WasmFX target drift: frozen OOPSLA'23 syntax vs Phase-3 standard

**Question**: ADR-0016 freezes the WasmFX *abstract syntax* (from the OOPSLA'23
paper) as the verified compiler-output target. The WebAssembly stack-switching
proposal has since advanced to **Phase 3**, and its instruction set has diverged.
Is the frozen target still the right thing to compile to and verify against?

**Why it matters**: invariant #8 — "the WasmFX backend is the verified compiler
target." If `compile_forward_sim` proves correctness against an abstract syntax
the real engine no longer implements, the proof is green against a fiction. A
frozen, drifted target is the worst case: it *looks* verified.

**Detail** (confirmed by the 2026-06-21 SOTA sweep — see `references/README.md`
→ Integration findings; sources in `refs.bib`):

```
Frozen (OOPSLA'23)            Phase-3 standard (live)        Status
──────────────────            ──────────────────────        ──────
cont.new / resume / suspend   + switch                      NEW primitive — symmetric
  + cont.bind                                                peer-to-peer switching,
                                                             not sugar over suspend/resume
resume_throw                  + resume_throw_ref             NEW
cont (top type)               + nocont (bottom heap type)    NEW
handlers: (tag $e $h) pairs   handlers: (on $tag $label)     RENAMED — old codegen is wrong
                                clauses on `resume`
```

The frozen target is now a **strict subset** of the standard. Per the SpecTec
experience report (WAW 2025), *semantics* (not just surface syntax) were adjusted
during standardization.

**Options**:
1. **Pin-to-engine, defer reconciliation to ◊5** *(recommended)*. The target
   doesn't bind until ◊5 (Compiler v0); we're at ◊2. Do NOT chase a Phase-3
   (still-mutable) proposal now. When ◊5 begins: pin a specific commit of
   `WebAssembly/stack-switching` + a Wasmtime version, and gate
   `compile_forward_sim` on differential testing against that engine
   (`wasm_stack_switching`, x86-64 Linux) rather than against the paper.
2. Re-freeze the target now against the current Explainer.md. Premature: the
   proposal will move again before Phase 4; we'd just re-drift.
3. Adopt a mechanized oracle. WasmFXCert + Iris-WasmFX (PLDI'26, Rocq) is a
   mechanized type-soundness model of WasmFX — aligns with invariant #1
   ("proof rides the reference"). Caveat: Rocq, not Lean; and verify whether it
   models the new `switch`/`nocont` or only the `suspend`/`resume` core.

**Recommended**: (1) now + (3) as the reference to ride at ◊5. Record here; do
NOT rewrite ADR-0016 (the two-hop *architecture* is unchanged — only the target's
concrete syntax drifted, which is a ◊5 reconciliation, not an architecture
reversal).

**Blocked on**: nothing now. This is a ◊5 obligation, surfaced early.

**Revisit signal**: starting ◊5 compiler/backend work; OR the stack-switching
proposal reaching Phase 4 (becomes stable — re-freeze then); OR a decision to
adopt WasmFXCert as the backend oracle.

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
