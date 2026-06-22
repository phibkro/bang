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
- [Q12 — Graded state handlers: how does `state ℓ s` thread grades?](#q12--graded-state-handlers-how-does-state--s-thread-grades)  · OPEN
- [Q13 — Operation-granularity: `progress` for `throws`](#q13--operation-granularity-progress-for-throws-needs-op-aware-signatures)  · ✓ RESOLVED (ADR-0023)
- [Q14 — `effect_sound`: what does the trace observe?](#q14--effect_sound-what-does-the-trace-observe)  · OPEN

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

## Q12 — Graded state handlers: how does `state ℓ s` thread grades?  · OPEN (deferred from ADR-0022 Unit 2)

**Question**: the `state` handler's `Source.step` reductions don't thread grades cleanly,
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

## Adding a new question

Append below with the same format:
- Question (one sentence)
- Why it matters
- Detail
- Options
- Recommended (if any)
- Blocked on
- Revisit signal
