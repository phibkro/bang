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
- [Q4 — `handle` typing rule: simplified vs label-removing](#q4--handle-typing-rule-simplified-vs-label-removing)  · ✓ RESOLVED (ADR-0022 D4 + ADR-0023)
- [Q5 — `up` typing rule + opArgTy/opResTy](#q5--up-typing-rule--oparGty-opresty)  · ✓ RESOLVED (ADR-0022 + ADR-0023)
- [Q6 — Source.step's deep-handler resumption](#q6--sourcestep-deep-handler-resumption)  · ◑ throws resolved (ADR-0023); state → Q12
- [Q7 — Operation names as strings vs symbolic enum](#q7--operation-names-as-strings-vs-symbolic-enum)
- [Q8 — `group_recovers` bridge: E group ⇒ F dagger-Frobenius?](#q8--group_recovers-bridge-e-group--f-dagger-frobenius)
- [Q9 — WasmFX target drift: frozen OOPSLA'23 syntax vs Phase-3 standard](#q9--wasmfx-target-drift-frozen-oopsla23-syntax-vs-phase-3-standard)
- [Q10 — Typing rules must enforce grades (resource discipline)](#q10--typing-rules-must-enforce-grades-resource-discipline)  · ✓ RESOLVED (ADR-0019+0020; subst_value proven)
- [Q11 — Open-term substitution: capture-avoiding subst vs de Bruijn](#q11--open-term-substitution-capture-avoiding-subst-vs-de-bruijn)  · ✓ RESOLVED (ADR-0020)
- [Q12 — Graded state handlers: how does `state ℓ s` thread grades?](#q12--graded-state-handlers-how-does-state--s-thread-grades)  · ✓ RESOLVED (ADR-0025; preservation state-resume cases are RUNG1-OBLIGATIONs)
- [Q13 — Operation-granularity: `progress` for `throws`](#q13--operation-granularity-progress-for-throws-needs-op-aware-signatures)  · ✓ RESOLVED (ADR-0023)
- [Q14 — `effect_sound`: what does the trace observe?](#q14--effect_sound-what-does-the-trace-observe)  · OPEN
- [Q15 — Thunk strictness: uniform laziness vs demand-driven eager folding](#q15--thunk-strictness-uniform-laziness-vs-demand-driven-eager-folding)  · OPEN
- [Q16 — Undecidable + unsafe programs: effects-with-oracles vs FFI](#q16--undecidable--unsafe-programs-effects-with-oracles-vs-ffi)  · OPEN
- [Q17 — Polymorphism + effect-row polymorphism](#q17--polymorphism--effect-row-polymorphism)  · ✓ RESOLVED (ADR-0027 — staged: monomorphic v1 → HM → System F)
- [Q18 — Data types: ADTs, inductive/coinductive, law attachment](#q18--data-types-adts-inductivecoinductive-law-attachment)  · ✓ RESOLVED (ADR-0029 — iso-recursive sum/product/μ)
- [Q19 — Typeclasses/traits with laws (ad-hoc polymorphism + the laws surface)](#q19--typeclassestraits-with-laws-ad-hoc-polymorphism--the-laws-surface)  · OPEN
- [Q20 — Surface extensibility: pseudoinstructions via aliasing + macros](#q20--surface-extensibility-pseudoinstructions-via-aliasing--macros)  · OPEN

> See also `design-space-map.md` (the survey) and **ADR-0026** (the correctness-ladder keystone that
> resolved the proof-power dial, design-space #2).

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
- `group_recovers`'s `[AddGroup Eff]` hypothesis is vacuous for our Lattice
  Eff (no nontrivial Lattice + AddGroup instance) — theorem **RETIRED** (ADR-0032),
  not preserved; v1 rollback is the txn handler. See Q8 (resolved-but-bounded).

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

## Q4 — `handle` typing rule: simplified vs label-removing  · ✓ RESOLVED (ADR-0022 D4 + ADR-0023)

**Resolution (2026-06-22)**: Both refinements landed. F-restriction (ADR-0021 C2) +
**label-removal**: `handleThrows` now DISCHARGES its label (`e ≤ labelEff ℓ ⊔ φ`, output `φ` —
ADR-0022 D4), and the corrected answer-type premise `opArg ℓ "raise" = some A` (ADR-0023) makes the
zero-shot abort type-preserving. The effect row shrinks at the handler, which is what `effect_sound`
will need. Historical update + deliberation below.

**Update (2026-06-22, ADR-0021, C2)**: the `handle` rule body was restricted from
general `B` to `CTy.F q A` — handlers handle *returners*. This was forced by
`progress` (a general-`B` `handle h (lam M')` is a stuck non-`ret` normal form).
The rule is STILL same-φ; the label-removing refinement below remains deferred and
will be forced by `effect_sound` (a handler must discharge its label for the static
effect to over-approximate the trace). So Q4 is half-resolved: F-restriction yes,
label-removal no.

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

## Q5 — `up` typing rule + opArgTy/opResTy  · ✓ RESOLVED (ADR-0022 + ADR-0023)

**Resolution (2026-06-22)**: Landed. Per-`(Label, OpId)` signatures via the `EffSig`
typeclass; the `up` rule in `Bang/Syntax.lean`. ADR-0023 D6 made `opArg`/`opRes` **op-partial**
(`Label → OpId → Option VTy`, `none` = not in the label's interface); the `up` rule now requires
`opArg ℓ op = some A` / `opRes ℓ op = some B`. `preservation`/`progress`/`type_safety` are proven
axiom-clean over the CK machine (ADR-0023), so the rule is non-vacuously exercised. Original
deliberation preserved below.

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

## Q6 — Source.step's deep-handler resumption  · ◑ PARTIAL — throws resolved (ADR-0023), state deferred (Q12)

**Resolution (2026-06-22, ADR-0023)**: `Source.step` is now a **CK machine** over
`Config = EvalCtx × Comp` (option 2 below — the `Frame`/`EvalCtx` infra). `up` dispatch scans the
frame stack for the nearest catching handler; the **throws** (zero-shot) case discards the captured
continuation and aborts with the payload. `preservation`/`progress`/`type_safety` re-proven
axiom-clean over it. The **state** (resumption) case still uses the same scan but must KEEP the
captured continuation and thread the stored state — deferred to **Q12** (graded state). Original
deliberation preserved below.

**Question (historical)**: the substitution-based `Source.step` returned `none` (stuck) when
`handle h (up ℓ op v)` didn't match. The "correct" behavior for deep handlers is to
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

## Q8 — `group_recovers` bridge: E group ⇒ F dagger-Frobenius? — ✓ RESOLVED (unresolved-but-bounded, ADR-0032)

**Question** (from the original wasmfx spec; surfaced in ADR-0016 + §6 of
Spec.lean): if `Eff` forms a group (effects are invertible), does the
graded monad `F` become dagger-Frobenius (Heunen-Karvonen)? If yes,
`group_recovers` is a corollary. If no, the theorem needs an explicit
observability side-condition.

**Resolution (2026-06-23, ADR-0032 — the ◊4 PROOF_ORDER #2 research gate):** the
H-K bridge as stated is **unsupported** — reversibility needs the monoid to be
**Frobenius** (involutive + the Frobenius coherence law), strictly stronger than a
group; our idempotent join-semilattice `Eff` is even further from Frobenius. AND
`group_recovers` was **false-as-stated** (a diverging `c` makes `(c;ret()) ≉ ret()`)
and **vacuous** (no `AddGroup` instance for the real effect lattice). So
`group_recovers` is **RETIRED**, not side-conditioned: v1 rollback is a HANDLER
mechanism (`all_or_nothing_abort`, ADR-0030/0031), not an effect-algebra inverse.
Q8 stays formally open (post-v1: a correct Frobenius-conditioned law would be a NEW
theorem) but bounded — it gates nothing in v1. References on disk:
`references/papers/adjacent/{heunen-karvonen-reversible-monadic,compositional-reversible-2024}.pdf`.

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

## Q10 — Typing rules must enforce grades (resource discipline)  · ✓ RESOLVED 2026-06-22

**Resolution**: Done. The rules now thread + enforce grades (Path B / ADR-0019),
and after the de Bruijn switch (ADR-0020) the carrier is positional `List Mult`
rather than the Finsupp this entry assumed — `subst_value` is proven on it
(`e00ee9a`, axiom-clean). The original deliberation (which still names the
`Var × Mult × VTy` named context) is preserved below as the historical record.

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

## Q12 — Graded state handlers: how does `state ℓ s` thread grades?  · ✓ RESOLVED 2026-06-23 → ADR-0025

**Resolution**: the CK machine (ADR-0023) keeps the FOCUS CLOSED (substitution-based binding), and
that dissolves the grade tension below — **no `ω`-restriction on the state type `S` is needed**
(rejecting Q12 option 1; the closed focus is Q12 option 2 *subsuming* it). The `state` dispatch RESUMES
(keeps `Kᵢ`, reinstalls a deep `state ℓ s'` frame); `get` returns the stored `s`, `put w` stores `w`.
The stored/threaded state is always a CLOSED value (grade vector `[]`), so duplicating it at `get`
costs zero variable budget for any `S`. Machine + typing (`HasCTy.handleState` / `HasStack.stateF`) +
`progress` are axiom-clean and the state CELL (`put 7; get ⟶ 7`) runs green (`Bang/Surface.lean`).
The **preservation** state-resume cases (typing the resumed stack `Kᵢ ++ handleF (state ℓ s') :: Kₒ`)
are marked `RUNG1-OBLIGATION` in `Bang/Metatheory.lean` for the proof-engineer. See **ADR-0025**.
Original deliberation preserved below.

**Question (historical)**: the `state` handler's `Source.step` reductions don't thread grades cleanly,
so `state`-handler typing was deferred from ADR-0022's Unit 2 (which does `up` + `throws`).

**Detail**: two grade mismatches in the simplified (Q6) reductions:
- `get`: `handle (state ℓ s)(up ℓ "get" u) ↦ handle (state ℓ s)(ret s)` — the reduct's grade
  is `q • γ_s` (from `ret s`) but the redex's is `q • γ_u` (from `up`'s unit arg `u`).
  Preservation needs `γ_s = γ_u`; only holds if both are `zeros` (closed).
- `put`: `handle (state ℓ _)(up ℓ "put" v) ↦ handle (state ℓ v)(ret unit)` — stores the
  *program* value `v` (typed in the ambient `γ Γ`, NOT closed) as the new handler state, but
  the handler-state typing wants it closed. Open-term preservation breaks.

The root: a stateful handler *threads a resource* (the state) across operations, and QTT grades
track resource usage — the two interact non-trivially. `throws` avoids this (zero-shot, no
threading).

**Options**: (1) require the state type `S` to be unrestricted (grade `ω`, freely
copyable/discardable) so grades don't constrain threading; (2) move to the CK-machine handler
semantics (Q6) where the continuation is captured and the state threads through the frame, not
by substitution; (3) a dedicated graded-state metatheory (literature: graded state / coeffectful
references).

**Blocked on**: Q6 (handler operational semantics) is the likely real fix — graded state wants
the continuation reified, not the substitution shortcut.

**Revisit signal**: `state`-using programs need type safety; or the CK-machine migration (Q6).

---

## Q13 — Operation-granularity: `progress` for `throws` needs op-aware signatures  · ✓ RESOLVED (ADR-0023)

**Resolution (2026-06-22, ADR-0023)**: Co-resolved with the CK machine. The Unit-2 `sorry` had TWO
facets, not one: (a) the wrong-op-same-label case this entry names (`up ℓ "get"` under `throws ℓ`),
and (b) a DEEPER one this entry MISSED — an operation nested under `letC`/`app` inside the handle is
stuck under the shallow step *even with the right op* (machine-checked: `handle (throws ℓ)(letC (up ℓ
"raise" v) N)`). (b) needs the **CK machine** (ADR-0023); (a) needs **op-partial `EffSig`
signatures** (recommended option 1 below) — `opArg`/`opRes : Label → OpId → Option VTy`, `up`
requires `some`, `handleThrows` requires the interface `= {raise}`. Both landed in ADR-0023 (D6 + the
machine); `progress`/`type_safety` are axiom-clean over the machine. The `labelEff_sep` law (sub-gap
b of this entry) also landed as an `EffSig` law. Original deliberation preserved below.

**Question (historical)**: effect rows are **label**-granular (`labelEff ℓ : Eff`), but the `throws`
handler reduces only the `"raise"` **operation**. So `handle (throws ℓ) (up ℓ "get" v)` is
well-typed (label `ℓ` is in the row) yet **stuck** (`Source.step`'s throws arm matches only
`"raise"`), and `progress` cannot exclude it. This is the single `sorry` left in Unit 2
(`Bang/Metatheory.lean` `progress_gen` handleThrows case); `preservation` + `up` + `handleThrows`
are axiom-clean.

**Why it matters**: `progress`/`type_safety` (now stated at `⊥`, ADR-0022 D3) are headline ◊2
theorems; they regressed from axiom-clean to `sorry` when effects were added. The root is that
`EffSig.opArg`/`opRes : Label → OpId → VTy` are **total** over op-strings — the kernel "declares"
every operation for every label, so it out-permits the source language (where `effect Exn { raise }`
has no `get`).

**Two sub-gaps** (the proof-engineer named both):
1. **label separation** — `labelEff ℓ' ≤ labelEff ℓ ⊔ φ → ℓ' ≠ ℓ → labelEff ℓ' ≤ φ`. Easy:
   add as an `EffSig` law (holds for `Finset` singletons; needs a distributive lattice +
   atom-ness). This closes the `ℓ' = ℓ` half.
2. **throws-op restriction** — under `handle (throws ℓ)`, the body's `ℓ`-operations are only
   `"raise"`. The hard half; not expressible with label-granular effects.

**Options**:
1. **Op-aware signatures** *(recommended)*: `EffSig.opArg/opRes : Label → OpId → Option (VTy)`
   (`none` = not in the effect's interface); `up` requires `opArg ℓ op = some _`; `handleThrows`
   requires `ℓ`'s only defined op is `"raise"`. Closes the gap; re-touches the `up` rule + every
   `up` proof case.
2. **Op-granular effect rows**: track `(Label, OpId)` in `Eff`, not just `Label`. Bigger; changes
   ADR-0001's row carrier.
3. **Specialize `progress`/`type_safety` to `Eff = EffRow`** (Finset Label) with the separation
   lemma decidable — but there is currently **no `EffSig EffRow QTT` instance** in the tree, and
   it doesn't fix the op restriction.

**Blocked on**: the (1)-vs-(2) design choice. (1) is the lighter, recommended path.

**Revisit signal**: closing the `progress`/`type_safety` `sorry` (next Unit-2 follow-up).

---

## Q14 — `effect_sound`: what does the trace observe?  · OPEN (deferred from ADR-0024)

**Question**: `effect_sound` states `HasCTy [] [] c e (F q A) → evalTrace fuel c = done (v,t) →
traceWithin t e` — the static effect `e` over-approximates the observed trace `t`. With what trace
semantics is this both TRUE and meaningful?

**Why it matters**: it's a ◊2-block soundness theorem (the dynamic counterpart of the static effect
discipline). Currently `sorry` (not the ◊2 *gate*, which is `no_accidental_handling`).

**Detail (the tension, ADR-0023/0024)**: in the deep-handler machine, `e` bounds only the operations
that **escape** `c`'s own handlers, NOT those handled internally. `handle (throws ℓ)(… raise ℓ …)`
performs `raise ℓ` during evaluation, but ℓ is discharged by `c`'s handler, so `labelEff ℓ ⊄ e`. So:
- trace = **all dispatched labels** ⇒ `traceWithin t e` is FALSE (internal handling hides labels from `e`).
- trace = **escaping labels only** ⇒ for a program that runs to `done`, nothing escaped (an escaping op
  is stuck, not `done`), so `t = []` and the theorem is trivially true but vacuous.

**Options**: (1) trace logs `(label, handled-by-depth)` and `traceWithin` checks each label against the
effect *at the point it was performed* (the focus effect, which preservation bounds) rather than the
top-level `e`; (2) a two-level statement: internal labels ⊆ (labels discharged by `c`'s handlers),
escaping labels ⊆ `e`; (3) instrument `evalTrace` to log only at the program boundary and prove the
(weak) escaping-bound. (1) is the most informative.

**Blocked on**: choosing the trace semantics (a design decision, like ADR-0024 was for
`no_accidental_handling`). The CK machine makes either tractable (each DISPATCH is an observable point).

**Revisit signal**: taking up `effect_sound` / `Trace` concretization after the ◊2 gate.

---

## Q15 — Thunk strictness: uniform laziness vs demand-driven eager folding  · OPEN

**Question**: should the surface/compiler evaluate pure closed expressions (e.g. `4+2`) eagerly
("declare/resolve thunks upfront") and suspend only genuinely-deferred ones (`4+x`, or anything
effectful), or keep the kernel semantics **uniformly lazy** (everything is a thunk; `force` is the
only observation, ADR-0007) and treat eager evaluation purely as a *compiler optimization*?

**Why it matters**: it is the surface manifestation of the §5 evaluation-stage axis (when/where a
thunk is forced). Get the boundary wrong and you either bloat every program with thunk allocations
(naive uniform-lazy) or perform effects at the wrong stage (naive eager — unsound).

**Detail**: the discriminant for "safe to fold now" is NOT "has a free variable" — it is **pure
(`⊥` effect row) AND closed**:
- `4 + 2`       `⊥`, closed         → safe to fold at compile-time (`$comptime`)
- `4 + x`       `⊥`, x unbound       → residual; fold once x is known (partial evaluation)
- `print(); 2`  row ⊇ `{IO}`         → MUST NOT fold early — folding performs the effect
The **effect row is the license to fold** (constraints-are-generative). A thunk in THIS kernel is the
minimal `vthunk : Comp → Val`; the richer "scoped env + deps + cached return" structure is a
**reactive cell** (ADR-0005/0006, rung 4) — an enrichment built *over* the minimal thunk, not the
thunk itself. Don't enrich the kernel thunk (collapses the moat / the five-primitive invariant).

**Options**: (1) **uniform-lazy semantics + an effect-row-gated fold/eager pass in the compiler**
*(recommended)* — one thunk concept; folding is an optimization that must preserve observable
behavior (invariant #7); (2) two syntactic thunk kinds (eager/lazy) at the surface — a second
concept, rejected unless (1) proves insufficient; (3) binding-time analysis as a surface-visible
stage annotation (`$comptime`/`$runtime`, §5) — likely the eventual UX, *layered on* (1).

**Prior art / framing** (the established names for option-1's "fold pass", for the ◊5 compiler
session): the loop "fold what's static, iterate to fixpoint, emit the residual" is **partial
evaluation driven by binding-time analysis** (Jones/Gomard/Sestoft 1993); the fold step is
**constant folding** enabled by **constant propagation** (a forward dataflow analysis); "safe to
force eagerly in a lazy language" is **strictness analysis** (Mycroft 1980); the fixpoint is the
least fixed point of a monotone map over a lattice — the shape shared by dataflow analysis and its
superframe **abstract interpretation** (Cousot² 1977). bang's edge: facts (1) purity and (2) usage
come FREE from the effect row + QTT grade (the type IS a precomputed static analysis); only
(3) constant-ness needs the dataflow pass. The static/dynamic partition = the compile-/run-time
stage assignment (Futamura), which is the §5 axis — bang layers MetaML-style explicit `$comptime`
staging (option 3) on top of the inferred default. Compiler ARCHITECTURE for hanging these passes:
the **nanopass/micropass** discipline (Sarkar-Waddell-Dybvig 2004; Keep-Dybvig 2013) — many tiny
typed-IL passes — is the compiler-level echo of the kernel's correctness-by-construction, and the
right host for a VERIFIED two-hop pipeline (each small pass individually provable; cf. CompCert).

**Blocked on**: nothing now (v1 ships uniform-lazy per invariant #7).

**Revisit signal**: building the `$comptime` stage, the reactive cell (rung 4), or a perf pass that
wants to elide thunk allocations.

---

## Q16 — Undecidable + unsafe programs: effects-with-oracles vs FFI  · OPEN

**Question**: how does bang admit programs that (a) may not terminate ("undecidable") or (b) leave the
verified abstraction ("unsafe": raw memory, MMIO, type holes, foreign code)? Write them in the
language, or port them over FFI?

**Why it matters**: the xv6 golden test (PRD §3.1) NEEDS both — a scheduler loop runs forever, device
drivers poke MMIO. If these are FFI escape hatches, invariant #1 ("never ship an execution path with
no oracle") is violated at exactly the places correctness matters most. The answer shapes whether
`Div`/`Foreign` effects and coinduction enter the kernel.

**Detail (the on-thesis direction — proposed, NOT built)**: both axes become **effects in the row**,
contained by handlers, each backed by an oracle — generalizing STM (invariant #3: one privileged,
axiom-backed primitive):
- **Undecidability = partiality as the `Div` effect** (Capretta's `Delay` monad; McBride,
  *Turing-Completeness Totally Free*, 2015). `⊥`-row = total (provable, foldable); `Div`-row = may
  diverge (only runnable). bang ALREADY embodies this: `Source.eval : Nat → Comp → Result Val` — fuel
  is the partiality handler, `oom` the honest timeout. Rice/Halting forces the total-vs-partial
  tiering (can't have Turing-completeness + a total static termination check). Third tier: *productive*
  non-termination (the xv6 event loop) = **coinduction**, which is the reactive model (rung 4).
- **Unsafety = a privileged op named by an effect, backed by a differential-test oracle.**
  unsafe-but-modelable (MMIO, syscalls) → a `Mem`/`IO` privileged primitive tested against the real
  hardware/model (NOT proven — invariant #1's boundary discipline). Genuinely foreign code → a
  `Foreign` effect; the artifact is its own oracle.
- The **effect row is the firewall**: pure code cannot silently call a diverging/unsafe op — the tag
  propagates into the type, so contamination is visible and type-enforced.

**Decision rule (proposed)**: write it in bang if you can give it an oracle (a proof, or a model to
differential-test); FFI only when the foreign artifact IS its own best oracle and re-verifying isn't
worth it — and name what FFI gives up (the proof stops at the boundary; downstream is `Foreign`-
tainted). For the xv6 showcase, lean write-it-all-in-bang (seL4 / CertiKOS precedent — CertiKOS has
only a tiny verified-asm layer); FFI is for real-world pragmatics (don't re-verify OpenSSL), not the
golden test.

**Options**: (1) effects-with-oracles as above — `Div` + coinduction for partiality, privileged
primitives + `Foreign` for unsafety, all row-tracked *(recommended; on-thesis)*; (2) a two-world
split (a separate "unsafe bang" dialect outside the verified core) — rejected unless (1) proves
unworkable, as it abandons the firewall; (3) FFI-only for everything non-total — rejected (blind spot
at the highest-stakes code).

**Blocked on**: nothing now — this is ◊4/◊5/post-v1 (needs the compiler + a richer effect zoo). Far
ahead of rung 1.

**Revisit signal**: a program on the ladder needs non-termination (the scheduler, rung 6) or a raw/
MMIO op (the device driver, rung 8); or the effect-zoo design for v1+ effects begins.

---

## Q17 — Polymorphism + effect-row polymorphism  · ✓ RESOLVED 2026-06-23 → ADR-0027

**Resolution**: **Staged across three tiers; v1 takes only the first.** (1) v1/MVP = **monomorphic**
(no type/row/grade variables; rung 2's stack is `Stack Int`, not `Stack a`); (2) next = **Hindley-Milner**
(rank-1, decidable inference — where "paradigms as libraries" becomes real); (3) ambitious = **System F**
+ effect-row variables `⟨e | ε⟩` (cashing the K1 unifier) + grade polymorphism. See **ADR-0027**.
Original deliberation preserved below.

**Question**: the kernel type syntax (`VTy = unit | int | U eff cty`; `CTy = F mult vty | arr …`) is
**monomorphic** — no type variables, no effect-row variables. How does bang express parametric
polymorphism, and crucially **effect-row polymorphism** (a function generic over the effects of its
argument)?

**Why it matters**: without it there is no reusable higher-order effectful code. `map : (a →^e b) →
List a → List b !e` must be polymorphic in BOTH the element types AND the effect row `e` — otherwise
every effect needs its own `map`. Forced at rung 3+ (any HOF over effects); blocks the whole library
story (paradigms-as-libraries needs effect-generic combinators).

**Detail**: two axes — (1) ordinary parametric polymorphism (System-F-style type variables / `∀`);
(2) **row polymorphism** (effect-row variables `ε` with `e ⊔ ε`), the Koka/Frank/Links mechanism. The
grades complicate both: a polymorphic function must also be generic in the multiplicity/coeffect
grades (grade polymorphism — Granule territory). Interacts with Q18 (polymorphic data types) and
inference (grade + row inference is hard).

**Options**: (1) System-F + row variables (Koka-style open rows `⟨e | ε⟩`); (2) bounded/qualified
polymorphism (constraints, links to Q19 typeclasses); (3) stay monomorphic + rely on metaprogramming
(Q20) to generate monomorphic instances — rejected as a non-answer (no real genericity). The row
algebra is already `Lattice + OrderBot` (ADR-0001); row variables sit on top as `e ⊔ ε`.

**Blocked on**: nothing structural now; forced when rung 3 (or any effect-generic combinator) is built.

**Revisit signal**: writing the first effect-generic higher-order function (a `map`/`fold` over an
arbitrary effect row); or rung 2's stack needing element-type polymorphism.

---

## Q18 — Data types: ADTs, inductive/coinductive, law attachment  · ✓ RESOLVED 2026-06-23 → ADR-0029

**Resolution**: **Iso-recursive ADTs** — extend `VTy` with sum (`+`), positive product (`×`), and
iso-recursive μ (`fold`/`unfold`, which erase). **Inductive only** (coinductive → the Div fragment,
ADR-0028). μ-recursion variables are **not** polymorphism (a fixpoint binder, not `∀`), so ADR-0027's
monomorphic v1 is preserved. User-definable (the moat needs it): `List = μX. 1 + (Int × X)`. Laws via
assert + `plausible` (ADR-0026). Iso over equi because the functional difference is zero but
equi-recursive type equality is coinductive (brutal metatheory); the surface hides `fold`/`unfold` in
constructors/patterns (Q20). See **ADR-0029**. Original deliberation below.

**Question**: the kernel has `unit` + `int` only. How do users define data types — products, sums,
recursive (μ) types, GADTs — and how do **inductive** (terminating, total) vs **coinductive**
(productive, the event loop) types lower to graded CBPV? How do a type's **laws** (Q19) attach to it?

**Why it matters**: rung 2 (verified stack) needs at least products/lists; the moat (laws between
operations) needs user-defined types to attach laws to. Coinduction is needed for productive
non-termination (Q16 — the xv6 scheduler loop, reactive streams rung 4).

**Detail**: CBPV already splits value/computation; ADTs are *value* types (sums + products), with
recursion via a μ/fixpoint. Inductive = least fixpoint (total, foldable); coinductive = greatest
fixpoint (productive, the `Div`/stream side of Q16). The grades index data too (a linear pair vs an
unrestricted one). Open: whether bang has full inductive *families* (dependent, Agda-style) or simple
ADTs (Haskell/OCaml-style) + refinement — this is gated by ADR-0026 (the ladder: structural ADTs +
laws-on-the-ladder, NOT full dependent inductive families in the kernel).

**Options**: (1) simple ADTs (sum/product/μ) + laws via assertions on the ladder (ADR-0026-consistent;
recommended); (2) full dependent inductive families (Agda/Lean) — rejected per ADR-0026 (proof-assistant
in the kernel); (3) Church/CBPV-encoded data (no new kernel types, encode via `U`/functions) — elegant
but poor ergonomics + performance; possibly an *internal* lowering target.

**Blocked on**: nothing structural; forced at rung 2.

**Revisit signal**: building rung 2 (the verified stack) — it needs the first user data type.

---

## Q19 — Typeclasses/traits with laws (ad-hoc polymorphism + the laws surface)  · OPEN

**Question**: how does bang do ad-hoc polymorphism / overloading (`+`, `Eq`, `Ord`, `Monoid`)? And —
since **a typeclass IS a set of operations + laws** — is the typeclass mechanism *also* the **laws
surface** (the moat's user-facing face, design-space #3)?

**Why it matters**: `Monoid {op, id; assoc, unit-laws}` is exactly "fields, operations, and the
laws/relations between them" from the original vision. Unifying ad-hoc polymorphism with the
law-declaration surface would make the moat fall out of the module/class system rather than being a
separate feature (one-construct-per-problem).

**Detail**: the discharge of the laws is settled (ADR-0026: assert + property-test by default, climb to
SMT/proof). Open is the *surface*: how a `class`/`trait`/`structure` declares ops + laws, how instances
are resolved (typeclasses à la Haskell? traits à la Rust? canonical structures / implicits à la
Lean/Coq?), and how that resolution interacts with the grades + effect rows (a method may itself be
effectful). Links tightly to Q17 (qualified polymorphism = constrained type variables).

**Options**: (1) Haskell-style typeclasses with law obligations attached, discharged on the ADR-0026
ladder (recommended — unifies ad-hoc poly + the moat); (2) Rust-style traits (coherence via orphan
rules); (3) Lean/Coq implicits + canonical structures (powerful resolution, heavier). All three make
laws first-class; the choice is the resolution discipline.

**Blocked on**: Q17 (polymorphism) — qualified polymorphism needs type variables first.

**Revisit signal**: the first overloaded operation (rung 2's stack wanting `Eq`/`Monoid`), or building
the user-facing law surface.

---

## Q20 — Surface extensibility: pseudoinstructions via aliasing + macros  · OPEN (principle leaning decided)

**Question**: the surface is sugar over the semantics (formatter, linter, **pseudoinstructions**). The
*principle* is set: **never add a kernel primitive for something expressible as a composite of existing
primitives** (invariant #5) — instead provide **aliasing + metaprogramming** that expands to primitive
composites (like assembly pseudo-ops). Open: the *mechanism* — how macros/aliasing work, and how much
syntactic extensibility the surface offers.

**Why it matters**: this is "write your own constructs" from the vision, and the discipline that keeps
the kernel at five primitives as the surface grows. Get it right and new paradigms/notations are
libraries; get it wrong and the kernel bloats or the surface fragments.

**Detail**: levels of extensibility — (a) plain *aliasing* (a name for a composite, no new syntax);
(b) *hygienic macros* that expand to core terms before lowering (Lean 4 elaboration, Racket
`define-syntax`, Scheme); (c) full *user-defined notation* / reader extension (custom operators,
mixfix — Lean `notation`, Agda mixfix). Hygiene (capture-avoidance) interacts with ADR-0006/0020 (no
implicit capture; de Bruijn). The *semantic* DSL mechanism already exists (effects + handlers = a
little language per effect); this Q is about *syntactic* extension on top.

**Options**: (1) elaboration-style hygienic macros expanding to core `Comp` (recommended; Lean 4 model
— composes with the existing lowering pass in `Bang/Surface.lean`); (2) aliasing only (no new syntax —
minimal, may be too weak for ergonomic DSLs); (3) full reader/notation extension (most powerful, most
rope). The five-primitive invariant + "no new primitive if composite" is the *constraint*; the
mechanism is the *choice*.

**Blocked on**: nothing now — a surface-layer concern (liquid); meaningful once the surface grows past
the rung-0/1 toy parser.

**Revisit signal**: the surface accumulating repeated composite patterns that want a name; or building
the first user-defined construct/notation.

---

## Q21 — Concurrent STM: the privileged shared-heap upgrade  · OPEN (deferred from ADR-0030)

**Question**: how does STM become genuinely *concurrent* (its privileged form) when threads / multi-shot
handlers arrive?

**Why it matters**: ADR-0030 ships v1 STM as a *single-threaded transactional handler* (`state ⊗
exception`); **privilege** — a runtime-owned shared heap that racing transactions validate against — is
exactly what a per-computation handler-fold CANNOT provide, and is load-bearing *only* under concurrency.
The upgrade is the real STM. The all-or-nothing law (`all_or_nothing_abort`, proven) climbs to **opacity**
(Guerraoui–Kapalka) at that point.

**Detail**: needs a shared heap *outside* any handler, optimistic read-set validation, conflict detection,
and `retry`-as-blocking (vs v1's `retry ≈ abort`). Couples to multi-shot handlers (ROADMAP ◊5+) and the
**cooperative-not-preemptive** concurrency model (PRD rung 6). The deferral is sound *only while no effect
observes mid-transaction partial state* (ADR-0030 Revisit-if). Sub-forks already scoped: `orElse` needs a
**recovery handler** even single-threaded (rung-3 follow-on, corrects ADR-0030's "costs nothing");
**general-`S` TVars** via a default-witness (ADR-0030 amendment, deferred to avoid helper churn).

**Options**: (literature in `references/` per ADR-0030) Harris-style log-based optimistic STM with
validation-at-commit; C4-style (Lesani–Chlipala OOPSLA'22) verified transactional objects proving strict
serializability via linearizability — the mechanized exemplar.

**Blocked on**: concurrency / multi-shot (post-v1, ◊5+).

**Revisit signal**: threads / multi-shot land; or a single-threaded program genuinely needs blocking-retry
(which is a concurrency need wearing a single-threaded mask).

---

## Q22 — `orElse`: how does the alternative discard the first branch's writes?  · OPEN (rung-3 follow-on)

**Question**: `orElse a b` runs `a`, and if `a` aborts runs `b` — but `b` must run as if `a`'s **writes
never happened** (Harris OR3). How does the kernel discard `a`'s transactional writes on fallthrough?

**Why it matters**: `orElse` is STM's *compositional alternative* (the reason "composable memory
transactions" is the paper title). ADR-0030 listed it as minimal-core "costs nothing" — **that was wrong**
(corrected in the ADR): the `throws` handler *discards the continuation and yields the payload*; it cannot
run an alternative, and it cannot roll back only `a`'s sub-writes. So `orElse` is a real (small) increment,
not free.

**Detail**: `a`'s writes live in the transaction heap `Θ`. On `a`-abort, `Θ` must be rolled back to its
state at `orElse`-entry before `b` runs; on `a`-commit, `a`'s writes persist. The current single-threaded
rollback (abort = `throws` escaping the *whole* transaction frame) is too coarse — it discards the *entire*
transaction, not just `a`'s sub-effects.

**Options**:
1. **Savepoint (★ recommended for v1)** — snapshot `Θ` at `orElse` entry (`Θ_sp`); run `a`; on `a`-abort
   restore `Θ ← Θ_sp` and run `b`; on `a`-commit keep. One heap + a saved copy. Smallest extension: the
   transaction handler (or an `orElse` Comp form) brackets `a` with save/restore-on-abort. *Allocation
   subtlety*: truncating `Θ` to `Θ_sp` also drops `a`'s allocations — observationally fine (`b` can't name
   `a`'s TVars) though it diverges slightly from Harris's "keep `∆`"; record the choice.
2. **Nested transaction** — `a` runs in a sub-transaction (heap = copy of parent's current); commit merges
   to parent, abort discards + runs `b`. More general (composable nesting), needs snapshot-at-install +
   merge-on-commit. The **concurrency-era** form (couples to [[Q21]]).
3. **Recovery handler** — a `Handler.orElse`/`recover` variant catching `a`'s abort, restoring the heap,
   running `b`. ≈ option 1 framed as a handler; needs the variant to reach the transaction's heap.

**Recommended**: **savepoint (1)** for single-threaded v1; **nested-tx (2)** is where it generalizes when
concurrent STM (Q21) lands. Either way the *correctness* obligation is `orElse a b ≈ b` when `a` aborts
(its writes invisible) — provable like `all_or_nothing_abort`.

**Blocked on**: nothing — a bounded rung-3 follow-on. Needs the transaction handler to expose heap
snapshot/restore (a small kernel extension; touches Core/Operational/Syntax/Metatheory + a surface form).

**Revisit signal**: a program wants composable transactional alternatives (the canonical `orElse`
use-case); or concurrent STM (Q21) lands and nested-tx becomes the natural form.

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
