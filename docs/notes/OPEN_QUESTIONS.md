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
- [Q10 — Typing rules must enforce grades (resource discipline)](#q10--typing-rules-must-enforce-grades-resource-discipline)  · ACTIVE
- [Q11 — Open-term substitution: capture-avoiding subst vs de Bruijn](#q11--open-term-substitution-capture-avoiding-subst-vs-de-bruijn)

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

## Q3 — Ctx representation: List vs FinMap  · ✓ RESOLVED 2026-06-21 → ADR-0019

**Resolution**: Forced active by Q10 (resource-enforcing rules need "grade ρ at
`x`, 0 elsewhere", which `List`+`zipWith` can't express). **Split** the context
into a Finsupp grade-vector `Var →₀ Mult` + an ambient type context
`List (Var × VTy)`, mirroring Torczon's `gradeVec`/`context`. Mathlib's
`Finsupp` supplies total `+`, `•`, and `single`. See **ADR-0019**. The original
deliberation is preserved below.

---

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

## Q10 — Typing rules must enforce grades (resource discipline)  · ACTIVE (Path B chosen 2026-06-21)

**Question**: `HasVTy` / `HasCTy` carry a multiplicity in each context binding
(`Var × Mult × VTy`) but **never thread or check it**. Should they be upgraded
to be resource-enforcing (Torczon-faithful), so the grade actually constrains
typing?

**Why it matters**: this is the gate for the entire grade-soundness story —
the QTT payoff. Surfaced 2026-06-21 while fixing `subst_value`, which was
*vacuous* (conclusion = hypothesis). The real graded substitution lemma is now
stated (`Bang/Spec.lean`) but **unprovable** until the rules thread grades; the
same gap blocks `zero_usage_erasable` and `effect_sound`. Without this, ◊2
"kernel frozen v1" is not actually met — `HasCTy` is grade-insensitive.

**Detail** — the divergence from Torczon (`/tmp` clone of
plclub/cbpv-effects-coeffects, `resource/CBPV/typing.v`):

```
                TORCZON (resource-enforcing)        BANG (Phase-A first cut)
variable        T_Var i: γ i = Qone,                vvar: (∃ ρ, (x,ρ,A) ∈ Γ)
                  ∀ j≠i, γ j = Qzero                 └ ρ existential — IGNORED
return          T_Ret q V: γ = q Q* γ1              ret: Γ untouched
application     T_App: γ = γ1 Q+ (q Q* γ2)          app: same Γ for M and v
subsumption     T_VSub: γ Q<= γ'                    (none)
```

Torczon grades via a per-variable `gradeVec` (γ : fin n → Q); we fold the grade
into the context `List (Var × Mult × VTy)` with `Ctx.scale` (ρ·) and `Ctx.add`
(zipWith +) already defined but unused by the rules.

**Decision**: **Path B** (resource-enforce, then prove the real lemma). Chosen
over Path A (ungraded substitution lemma matching the weak rules — rejected as a
weakening we'd have to un-do, giving up the QTT payoff).

**Blocked on / collides with Q3**: the var rule needs "grade ρ at `x`, zero
elsewhere." `List` + `zipWith` (`Ctx.add`) requires matching shape and can't
cleanly express "zero on the rest" the way Torczon's `gradeVec` does. **Q3
(List vs FinMap) must be resolved as part of this upgrade** — it is no longer
deferrable; the rule shape forces the context-representation decision.

**Plan (sequenced)**:
1. Resolve Q3 (context representation) — the rule shape needs it.
2. Upgrade `HasVTy.vvar` to enforce the grade (one-at-`x` discipline).
3. Thread grades through `ret`/`app`/`letC`/`lam` (scale + add).
4. Discharge `subst_value`, then the STD block (preservation/progress/safety).
5. Then `zero_usage_erasable` / `effect_sound` become reachable.

**Revisit signal**: this IS the active ◊2 task — no deferral. Resolves when the
graded `subst_value` is proven with a clean axiom set.

---

## Q11 — Open-term substitution: capture-avoiding subst vs de Bruijn  · ✓ RESOLVED 2026-06-21 → ADR-0020 (option C)

**Resolution**: **Option C — de Bruijn.** The named encoding produced FOUR
more machine-checked falsities while proving `subst_value` (capture,
grade-freshness, context-wf, bound-var-grade, non-deterministic lookup) — five
structural side-conditions for one lemma, each free under de Bruijn. Switched the
term representation to de Bruijn indices; **ADR-0020**. Option A (closed
side-condition) was the in-force stopgap that surfaced the full cost. Original
deliberation preserved below.

---

**Question**: `Comp.subst` is **not capture-avoiding** (Operational.lean §subst,
scoped to "closed-program reductions"). The graded substitution lemma
`subst_value` is therefore only true with a closedness side-condition (currently
`v` typed in the empty type context). How do we eventually support **open-term**
substitution — needed for the *interesting* graded case where the substituted
value carries its own resource demands (`γ_Δ ≠ 0`)?

**Why it matters**: the closed-`v` `subst_value` suffices for `type_safety`
(closed programs) but trivializes the grade arithmetic (`ρ·γ_Δ = ρ·0 = 0`). The
full coeffect payoff — substituting open values while tracking their usage — and
`preservation` for a *general* context both want open-term substitution.

**Detail** — the unconditional open lemma is FALSE under non-capture-avoiding
subst. Counterexample: `[vvar y / x](lam y. ret (vvar x)) = lam y. ret (vvar y)`
— the free `y` of the substituted value is captured by `lam y`.

**Options** (from the 2026-06-21 decision; A chosen for now):
- **A — closedness side-condition** *(in force)*. `subst_value` requires `v`
  closed. Cheap, true, unblocks the STD block. Trivializes grades for `v`.
- **B — capture-avoiding `Comp.subst`**. α-rename binders (fresh-name supply +
  α-equivalence machinery over named vars). True in general; a real sub-project.
- **C — de Bruijn representation**. Capture structurally impossible (Torczon's
  choice via autosubst2). Most robust; a ◊3-scale rewrite of syntax/subst/eval.

**Blocked on**: nothing now (A unblocks the STD block). Revisit when open-term
graded reasoning is needed.

**Revisit signal**: a coeffect theorem (or `preservation` for non-empty `Γ`)
that needs `subst_value` with `γ_Δ ≠ 0`; or the ◊3 CalcVM port, where a de
Bruijn switch (C) could be folded in.

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
