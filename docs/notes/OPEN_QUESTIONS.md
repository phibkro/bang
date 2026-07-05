<!-- note-status: active -->
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
- [Q3 — Ctx representation: List vs FinMap](#q3--ctx-representation-list-vs-finmap)  · ✓ RESOLVED (ADR-0019)
- [Q4 — `handle` typing rule: simplified vs label-removing](#q4--handle-typing-rule-simplified-vs-label-removing)  · ✓ RESOLVED (ADR-0022 D4 + ADR-0023)
- [Q5 — `up` typing rule + opArgTy/opResTy](#q5--up-typing-rule--oparGty-opresty)  · ✓ RESOLVED (ADR-0022 + ADR-0023)
- [Q6 — Source.step's deep-handler resumption](#q6--sourcestep-deep-handler-resumption)  · ◑ throws resolved (ADR-0023); state → Q12
- [Q7 — Operation names as strings vs symbolic enum](#q7--operation-names-as-strings-vs-symbolic-enum)
- [Q8 — `group_recovers` bridge: E group ⇒ F dagger-Frobenius?](#q8--group_recovers-bridge-e-group--f-dagger-frobenius)  · ✓ RESOLVED (ADR-0032 — unresolved-but-bounded)
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
- [Q19 — Typeclasses/traits with laws (ad-hoc polymorphism + the laws surface)](#q19--typeclassestraits-with-laws-ad-hoc-polymorphism--the-laws-surface)  · ✓ RESOLVED (ADR-0040)
- [Q20 — Surface extensibility: pseudoinstructions via aliasing + macros](#q20--surface-extensibility-pseudoinstructions-via-aliasing--macros)  · OPEN
- [Q21 — Concurrent STM: the privileged shared-heap upgrade](#q21--concurrent-stm-the-privileged-shared-heap-upgrade)  · OPEN (deferred from ADR-0030)
- [Q22 — Capability representation: labelling vs closure (multi-shot fork)](#q22--capability-representation-labelling-vs-closure-multi-shot-fork)  · OPEN (revisit at multi-shot)
- [Q23 — `orElse`: how does the alternative discard the first branch's writes?](#q23--orelse-how-does-the-alternative-discard-the-first-branchs-writes)  · OPEN (rung-3 follow-on)
- [Q24 — Surface concrete-syntax discipline: canonical vs lenient](#q24--surface-concrete-syntax-discipline-canonical-formatter-normalized-vs-lenient)  · OPEN (surface-layer)
- [Q25 — Integer semantics: unbounded Int vs fixed-width](#q25--integer-semantics-unbounded-int-vs-fixed-width-width--overflow)  · ✓ RESOLVED (ADR-0067 — unbounded ℤ v1; width behind the oracle)
- [Q26 — Optics as the lawful-polymorphism north-star (+ the HKT fork, + graded optics)](#q26--optics-as-the-lawful-polymorphism-north-star--the-hkt-fork--graded-optics)  · OPEN (gated on ADR-0027 stage 2)
- [Q27 — Surfacing the grade axis: declare effect shape AND grade (resumption grade → compilation)](#q27--surfacing-the-grade-axis-declare-effect-shape-and-grade-resumption-grade--compilation)  · OPEN (surface the second axis; links #35/#36)
- [Q28 — Recursion marker: reuse `rec` for data + functions, or keep them separate?](#q28--recursion-marker-reuse-rec-for-data--functions-or-keep-them-separate)  · ✓ RESOLVED (ADR-0073 — keep separate; unify at the `Div` row, `let rec` for functions)
- [Q29 — Handler-application syntax: prefix binder vs postfix eliminator (the effect eliminator wants eliminator syntax)](#q29--handler-application-syntax-prefix-binder-vs-postfix-eliminator-the-effect-eliminator-wants-eliminator-syntax)  · OPEN (surface effect-model)
- [Q30 — FBIP (Functional But In Place): static in-place reuse justified by the value-grade (verified enabler, compiled-path optimization)](#q30--fbip-functional-but-in-place-static-in-place-reuse-justified-by-the-value-grade-verified-enabler-compiled-path-optimization)  · OPEN (post-v1 perf; enabled by grades)
- [Q31 — Refinement types surface / quotient-proposition underlying: `Nat`, decidable checking, and the road to dependent types](#q31--refinement-types-surface--quotient-proposition-underlying-nat-decidable-checking-and-the-road-to-dependent-types)  · OPEN (major type-system direction, post-polymorphism)

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

Concrete: `Bang.EffRow := Finset Label` (in `Bang/Core/EffectRow.lean`).
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

**Resolution**: Concretized as `Bang.QTT` in `Bang/Core/Grade.lean`. CommSemiring
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
typeclass; the `up` rule in `Bang/Core/Typing.lean`. ADR-0023 D6 made `opArg`/`opRes` **op-partial**
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

> **Note (2026-06-23):** the ◊5 *proof method* is now settled — **ADR-0035**: `compile_forward_sim`
> uses AsmFX-style one-directional annotated simulation (not the biorthogonal LR, which stays ◊4-only).
> Q9 remains open on the *target* alone: AsmFX is its own abstract ISA, not WasmFX, so "pin the engine,
> not the paper" (options 1+3) is unchanged.
>
> **Cross-prover clarification (2026-06-23 recon):** option (3) "ride the mechanized oracle" CANNOT mean
> *import* — WasmFXCert / Iris-WasmFX are **Rocq** (`logsem/iris-wasmfx`, builds on WasmCert; confirmed
> models `switch` via `switch.addr` in `theories/`), and **no Lean-4 WasmFX semantics exists** (checked:
> T-Brick/lean-wasm, cajal/talos, Utrecht LeanWasm all model plain Wasm). So (3) = **transcribe** the Rocq
> operational semantics into a Lean `Wasmfx.run` (a few hundred lines for the trivial fragment, comparable
> to `Source.eval`), with the Rocq artifact as the faithful line-by-line reference (invariant #1 satisfied
> by transcription, not import). NEW SEAM this introduces — the Lean↔Rocq transcription — earns confidence
> from BOTH a line-by-line Rocq cross-check AND the real-engine differential test (a Lean-only-green
> `compile_forward_sim` would be "green against a fiction", relocated from syntax-drift to run-level).
> Engine status: stack-switching is Phase 3 (mutable); **Wasm 3.0 (Sept 2025) did NOT include it**;
> Wasmtime #10248 has core support behind the flag but x64-only, no `resume_throw`, "all test cases fail"
> — confirm a usable version by hands-on build at ◊5 start.
>
> **ENGINE PROBE RESOLVED (◊5, 2026-06-24):** stack-switching now RUNS on a RELEASED Wasmtime — no
> dev-commit pin needed. `wasmtime 44.0.1` (nixpkgs) executes a suspend/resume generator `.wat` on
> **x86_64 Linux**, deterministically returning the expected value. Required flag combination (the
> "conflated features" the brief flagged):
> `-W stack-switching=y,function-references=y,gc=y,exceptions=y`
> plus `(elem declare func $gen)` for the `ref.func`. The working shape (matches the ◊5
> markH/opH/unmarkH lowering): `(type $ct (cont $ft))` · `(tag $yield (param i32))` · `(cont.new $ct
> (ref.func …))` · `(resume $ct (on $yield $label) …)` · `(suspend $yield)` — the CURRENT Explainer
> form, NOT the OOPSLA'23 `(tag $e $h)`. The tracer/generator path (suspend/resume) needs NEITHER
> `resume_throw` NOR exceptions-as-control (exceptions is enabled only because the tag machinery shares
> it). ⟹ leg #2 (the differential-test oracle) is VIABLE: `compile_forward_sim` can gate on BOTH the
> Rocq cross-check (leg #1) AND a real wasmtime diff-test, not Lean-only-green. Probe `.wat` +
> invocation reproducible; not committed to the repo (a scratch artifact).

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
`progress` are axiom-clean and the state CELL (`put 7; get ⟶ 7`) runs green (`Bang/Frontend/Surface.lean`).
The **preservation** state-resume cases (typing the resumed stack `Kᵢ ++ handleF (state ℓ s') :: Kₒ`)
are marked `RUNG1-OBLIGATION` in `Bang/Core/Soundness.lean` for the proof-engineer. See **ADR-0025**.
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
(`Bang/Core/Soundness.lean` `progress_gen` handleThrows case); `preservation` + `up` + `handleThrows`
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

## Q19 — Typeclasses/traits with laws (ad-hoc polymorphism + the laws surface)  · ✓ RESOLVED 2026-06-24 → ADR-0040

**Resolution**: **ADR-0040** (the user-grilled laws-surface design) answers this: laws are
first-class, enforced **algebraic interfaces** (Rust-ish traits whose `law` members are
operations + equations relating them; the moat's user-facing face). Discharge is **proof-first**
→ property-test → assert, descent explicit + marked (amends ADR-0026's test-default). Monomorphic
first, Hindley-Milner next (ADR-0027). The *resolution discipline* (option 1 vs 2 vs 3 below) is
subsumed by the algebraic-interface framing. The full rationale + rejected alternatives live in
**ADR-0040** (the SoT); the original deliberation is preserved below.

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
— composes with the existing lowering pass in `Bang/Frontend/Surface.lean`); (2) aliasing only (no new syntax —
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

## Q23 — `orElse`: how does the alternative discard the first branch's writes?  · OPEN (rung-3 follow-on)

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

## Q22 — Capability representation: labelling vs closure (multi-shot fork)  · OPEN (revisit at multi-shot)

**Question**: When bang extends to **multi-shot / non-tail resumption** (`Bang/Reify/CalcReify.lean`, post-v1),
should a capability stay a generative NAME resolved by stack-search (`vcap n ℓ` + `splitAtId K n` + a
global-fresh gensym — ADR-0054/0055, **labelling**), or switch to a **closure / capability-passing**
representation (the cap captures the handler + delimited context directly, invoked without any search)?

**Why it matters**: The VM-calc spike (2026-06-27, on the `vm-calc-spike` branch) build-proved this is a
REPRESENTATION CHOICE *upstream* of the Bahr–Hutton calculation, not forced by the language: a labelling
`eval` calculates a machine WITH `gensym` + `splitAtId`; a closure `eval` calculates one with NEITHER
(O(1) `perform`, no fresh names). So that machinery is **introduced, not calculated** — invariant #4
degrades locally and precisely here (the spike's recommended honest framing: "calculated except for two
seams" — the cap representation, and the gensym discipline).

**★ CONCRETE MANIFESTATION (2026-06-29, inc-5 route-1) — `lr_sound` (task #72).** The labelling rep surfaces
this seam EARLIER than multi-shot: `lr_sound`'s adequacy needs to bridge `CrelK`'s observation of the RAW
focus `(g, K, c)` to `converges_plug_iff`'s RESHAPED focus `capSubstInto C c` (the labelling rep pushes
`C`'s frame caps INTO the focus; the raw RHS is provably FALSE — a raw `vvar`-cap focus is stuck). No
`CrelK` instantiation bridges them (build-witness `scratch/AdequacySpike.lean` @ `7574a5b`; `crelK_adequacy_nil`
for `C=[]` is CLEAN → it's specifically the arbitrary-context reshape). Two design options, both touching
FROZEN LR defs: (a) re-shape `CrelK` to the reshaped config; (b) plug-congruence (= `crelK_fund_up`'s
deferred direction). Under a **closure** rep this bridge would be a direct re-invoke (no reshape) — so the
seam is rep-specific, exactly as this Q frames it. Tracked: task #72 + `CONTEXT.md` lead.

**Detail** — the tradeoff:
```
                    labelling (name + search)        closure (capture + invoke)
  perform cost      O(stack depth) — a walk          O(1) — direct call
  minting           needs a gensym (fresh names)     none
  cap as a value    tiny, storable, first-class      heavier — captures context
  escape detection  FAIL-LOUD: escaped name → stuck  can be MASKED — closure still runs
                    (= the v1 NonEscape theorem)
  what you verify   NonEscape + freshness            closure-validity on re-invoke
```
v1 picked labelling because escape becomes fail-loud (exactly the `NonEscape` soundness theorem) and caps
stay small/storable — clean for SCOPED/affine caps. But **multi-shot re-invokes a captured continuation
AFTER its handler returned**, natural for a closure (it kept its context) and awkward for "the handler must
still be on the stack." That's where closure gets attractive. This is the literature's **search vs
evidence-passing** split: Xie–Leijen evidence passing (ICFP'21, motivated to eliminate the linear search)
and Brachthäuser–Schuster–Ostermann **Effekt** capability-passing (OOPSLA'20). bang's labelling is the
IDENTITY-keyed refinement of classic op-based search.

**Options**: (1) **keep labelling**, extend to multi-shot by reifying continuations as values while keeping
name-dispatch (the current `CalcReify` direction; cf. Q6 option 3); (2) **switch to closure /
evidence-passing** for the multi-shot fragment — kills gensym + `splitAtId`, O(1) `perform`, natural
multi-shot; cost: heavier caps, escape needs separate machinery, a representation migration; (3) **hybrid**
— labelling for v1 scoped/affine caps, closure for the multi-shot fragment (two reps, an explicit seam).

**Recommended**: none yet — decide WHEN multi-shot is scoped. If going closure, keep the machine
CALCULATED via an effectful identity-`evalD` (Garby–Hutton, *Calculating Compilers Effectively*, Haskell
2024). Keep the spike's `splitAtId_rename` lemma (cap names unobservable → any injective allocator is
correct) as the proof that the gensym discipline is a *provably-free* choice if labelling is kept.

**Blocked on**: nothing now (v1 ships labelling, scoped + fail-loud).

**Revisit signal**: scoping the multi-shot / non-tail resumption extension (`CalcReify` goes live); OR a
perf requirement where O(depth) `perform`-search becomes a bottleneck (evidence-passing's original motivation).

---

## Q24 — Surface concrete-syntax discipline: canonical (formatter-normalized) vs lenient  · OPEN (surface-layer)

**Question**: should the surface have ONE canonical textual form (a formatter normalizes to it, gofmt/rustfmt
style) or a lenient grammar that tolerates whitespace/style variation? And — the orthogonal axis — should
the grammar be whitespace-*insensitive*?

**Why it matters**: it sets the human↔agent ergonomics trade. Inference + loose input is nice for humans;
a single canonical, explicit form is nice for agents, diffs, and CI (less ambiguity, stable blame). The
two concerns (type-annotation optionality, text-format canonicality) are SEPARATE axes and shouldn't be
conflated — bidirectional typing already answers the first (optional, mandatory exactly where synthesis is
stuck; ADR-0066).

**Detail**: the current surface is the worst quadrant on the format axis — whitespace-*sensitive* (operators
are space-delimited: `a + b` parses, `a+b` does not — `Bang/Frontend/Surface.lean` tokenizer) AND non-canonical.
The modern answer (Go, Rust, Elm) is **both**: a whitespace-insensitive grammar PLUS a canonical formatter.
Humans write loose; the formatter normalizes to one true form; agents/diffs/CI see only canonical text. This
is the same single-source-of-truth move as everywhere else (the formatter GENERATES the canonical form).

**Options**: (1) **whitespace-insensitive grammar + canonical formatter** (recommended — Go/Rust model; serves
human, agent, machine at once); (2) lenient/whitespace-tolerant but no canonical form (compiles despite style
drift — but diffs/agents see noise); (3) status quo (whitespace-sensitive operators — the trap; fix via #30).

**Recommended**: (1). Precondition is the Pratt parser (#30) which removes the space-delimited-operator hack →
whitespace-insensitive; a `bang fmt` canonical formatter is then pure gravy (and pairs with the tree-sitter
grammar, #111).

**Blocked on**: nothing hard; sequencing — do the Pratt parser (#30) first, then the formatter. Liquid until
the surface stabilizes past the toy parser.

**Revisit signal**: building the Pratt parser (#30), or the first `bang fmt` / formatter; or agent-ergonomics
friction from non-canonical diffs.

---

## Q25 — Integer semantics: unbounded Int vs fixed-width (width + overflow)  · ✓ RESOLVED 2026-07-05 → ADR-0067

**Question**: what is the *specified* semantics of `Int` — arbitrary precision (what the kernel oracle
computes today) or fixed-width (i32/i64) with a defined overflow behavior?

**Why it matters**: the decision is currently *hiding inside a proved theorem*. `Val.vint : Int → Val`
is Lean's unbounded `Int`, and the Wasm model's `Val.i32` (`Bang/Backend/Wasm.lean`) ALSO carries an
unbounded `Int` — the constructor name promises 32 bits, the semantics deliver bignum. So the ◊5
forward sim is proven against an idealized bignum machine; real WasmFX emission (#6) that emitted
`i64.add` against this spec would be an unsound compiler. GitHub **#34** tracks the work.

**Detail**: whichever way it goes, width lives in the ORACLE or nowhere — `Source.eval`'s δ-rule
(`Comp.binop`, ADR-0065) defines arithmetic, and invariant #1 (proof rides the reference) forbids the
backend from quietly deciding it. Overflow may never be *undefined*: the UB set is empty by
construction (fail-loud invariant, cf. `escapedCap` ADR-0063).

**Options**: (1) **spec Int = unbounded**; the Wasm runtime ships bignum arithmetic — matches the
oracle by construction, zero proof rework now; an i64 fast path becomes a later *verified
optimization* (slow-but-correct, invariant #7). (2) **fixed-width i64, wrapping** (two's complement)
— the mainstream systems answer; requires changing the kernel δ-rule to wrap + re-deriving the
spine's binop arms + the sim. (3) **fixed-width, trap → defined terminal** — overflow becomes a
fail-loud terminal like `escapedCap`; same proof rework as (2) plus a new terminal.

**Recommended**: (1) for v1 — correct by construction against the existing census; defer width to a
verified-optimization decision when #6 makes performance observable. Immediate cheap step regardless:
rename the Wasm constructor `i32` → `int` so the name stops asserting an undecided width.

**Blocked on**: nothing — an ADR closes it. Must land before #6 (compiled path) starts.

**Revisit signal**: starting #6; or perf pressure on arithmetic benchmarks; or the lawful-algebra
layer (#24) wanting `Int` instances whose laws depend on width (overflow breaks associativity-with-
bounds claims).

---

## Q26 — Optics as the lawful-polymorphism north-star (+ the HKT fork, + graded optics)  · OPEN (gated on ADR-0027 stage 2)

**Question**: when and how does bang provide **optics** — composable, first-class, law-carrying
accessors (lens for products, prism for sums, traversal) — as STDLIB, given they gate on the
polymorphism lift and force an unrecorded higher-kinded-types decision?

**Why it matters**: optics are the grown-up dogfood of the pieces bang just built — lawful traits
(ADR-0040) over `data` declarations (ADR-0069). An optic IS a trait carrying its laws (lens:
get-set / set-get / set-set; prism: its build-match pair), checked on the tested rung exactly like
today's `comm` law. So "generic lawful lens over a `data` type" is the natural *validating demo* for
the ADR-0027 HM lift — it proves generic-code-over-a-lawful-interface end to end. And the profunctor /
van-Laarhoven unification forces the **HKT question** (`Functor f`, `Monad f`, `Profunctor p` all
abstract over a type CONSTRUCTOR `f : *→*`), a fork ADR-0027 does NOT cover (it stages to System F,
whose kinds are all `*`). Optics is therefore the lens (pun intended) through which the whole tier-2
stdlib — Functor/Monad/Traversable — comes into focus. See `docs/notes/stdlib-map.md` for the tier.

**Detail** — the encodings tier by required type-power:
```
concrete monomorphic accessor   get/set for ONE fixed type      ~now (traits+data) — but not "optics"
concrete generic optic          Lens s t a b = {get,set},  ∀stab System F (ADR-0027 stage 3)
van-Laarhoven                    ∀f. Functor f ⇒ (a→f b)→(s→f t) HKT (f : *→*) — the fork
profunctor                       ∀p. Profunctor p ⇒ p a b→p s t  HKT + constraint abstraction (F_ω-ish)
```
The bang-native angle: van-Laarhoven optics are parameterized by a `Functor`/`Applicative`
constraint — *effect-shaped*. Bang has **graded effect rows** as first-class kernel structure, so a
**graded / effect-indexed optic** (a traversal whose walk carries `! {ρ}`, grades tracked) is a
question the substrate uniquely poses — standard libraries bolt effects onto traversal awkwardly.

**Options**: (1) **concrete optics at System F** (records of get/set/match/build), forgo the
profunctor unification — no HKT, simpler type system, optics don't compose by bare `∘` (need explicit
combinators). (2) **full profunctor optics** — needs HKT/F_ω; elegant, composes by `∘`, but a much
heavier type + kind system and harder inference. (3) **defer entirely** until HM lands, then decide
(1) vs (2) with the concrete monomorphic lawful accessor as the near-term stepping stone.

**Recommended**: (3) — record now as the polymorphism-lift's validating demo; build the concrete
monomorphic lawful accessor when it's a useful stepping stone; decide (1) vs (2) when HM (ADR-0027
stage 2) lands. Do NOT add HKT speculatively — the same fork gates Functor/Monad, so decide it ONCE,
deliberately, when the first generic container or optic actually needs it.

**Blocked on**: ADR-0027 stage 2 (HM) for any generic optic; a SEPARATE, unrecorded HKT/F_ω decision
for the van-Laarhoven / profunctor forms (this Q is where that fork is first named).

**Revisit signal**: the HM lift starting (ADR-0027 stage 2); OR the first request for generic
containers with `map`/`traverse` (Functor/Monad hit the same HKT fork — decide together); OR anyone
reaching for effectful traversal (the graded-optic research angle).

---

## Q27 — Surfacing the grade axis: declare effect shape AND grade (resumption grade → compilation)  · OPEN (surface the second axis; links #35/#36)

**Question**: should the surface let a program declare, alongside its effect ROW (`! {ρ}`, WHICH
capabilities it depends on), the GRADE it wants (HOW those effects/resources are used)? The kernel
already tracks both axes (`HasCTy` carries `EffRow = Finset Label` AND `GradeVec Mult`, separately);
the surface hides the grade (ADR-0066 defaults it to `ω`). This asks whether — and where — to expose it.

**Why it matters**: the row and the grade are ORTHOGONAL and bang is unusually positioned to surface
both (it is *graded* CBPV — most effect languages have rows XOR quantitative types; Granule is the
one neighbour with both). The payoff is concentrated in ONE of the grades (below): the **resumption
grade** determines the compilation strategy, which is the generative-constraint move — a declared
invariant that lets the machine-calculation fire a cheaper machine.

**Detail** — "the grade" is THREE distinct notions; conflating them is the trap:
```
grade attaches to…    means…                                buys…
──────────────────────────────────────────────────────────────────────────────────
a VALUE / variable    QTT use-count of `x` (0/1/ω)          linear resources: use-once tokens,
  (coeffect)                                                  in-place update (design-map #10:
                                                              grades give use-once, NOT borrow)
RESUMPTION            how many times a handler invokes `k`   THE compilation strategy ← the win
  (handler property)    abort=0 / tail=1 / general=ω           (see table); #35/#36
an EFFECT's use        per-label multiplicity in the row     quantitative effect bounds — ★ THE TRAP
  (a graded row)                                              (see below)
```
The resumption-grade payoff — why it is the killer:
```
declared grade   handler behaves like    compiles to
0 (abort)        exception               a jump — no continuation saved
1 (tail)         state / reader          a plain stack frame — no copy
ω (general)      generators / backtrack  heap-allocated resumable closure (expensive)
```
Without the declaration every handler compiles as the ω worst case (copy the continuation); with it,
`state`/`throws` compile to a stack discipline. Koka (`fun`/`ctl`/`brk`), Effekt (2nd-class handlers),
OCaml-5 (one-shot conts) all found declaring resumption multiplicity worth it.

**THE TRAP — do not grade the ROW.** Making the row carry a per-label multiplicity (`state ↦ 3`) is a
graded monad, and it is FORECLOSED by invariant #2 / ADR-0001: rows are SETS (idempotent, union=join,
never a multiset), and the set structure is load-bearing for `no_accidental_handling` + the
join-semilattice effect-safety (Yoshioka ICFP'24, cited in the kernel). A per-label-weighted row IS
the forbidden multiset. So the grade must live BESIDE the row (on resumption / handler / value),
never INSIDE it — keep the two axes orthogonal exactly as the kernel already does
(`Finset Label × GradeVec Mult`). "Declare both" = two separate declarations, not one fused graded row.

**Options**: (1) **surface the resumption grade only** (a `tail`/`abort`/general annotation on a
handler; unlocks the no-copy compile) — highest value, tightest scope, aligns with #35/#36. (2) also
**surface value-grades** (a `once` on a consumable capability / linear thunk) — real but more
speculative for v1 (grades give use-once, not borrowing). (3) **status quo** (default ω, hide grades)
— the current pragmatic floor.

**Recommended**: (1) opt-in, exactly where it buys the machine strategy — a resumption annotation on
a handler clause, feeding the calculated-machine choice. Do NOT surface grades everywhere (inference
is HARD — design-space-map; ω-default is the right floor). Value-grades (2) wait for a concrete
resource use-case. The row stays a set (never option-graded-row).

**Blocked on**: #35/#36 (the resumption-grade multiplicity: abort/tail/general in the kernel/machine)
— surfacing needs the kernel distinction to exist first.

**Revisit signal**: #35/#36 landing (resumption grades in the machine); OR a compilation pass that
wants to avoid continuation-copying for tail-resumptive handlers; OR a consumable-capability
use-case that wants linear (use-once) effect typing.

---

## Q28 — Recursion marker: reuse `rec` for data + functions, or keep them separate?  · ✓ RESOLVED 2026-07-05 → ADR-0073 (keep separate; `let rec` for functions, unify at the `Div` row)

**Question**: when recursive FUNCTIONS land (the deferred `fix`/`Div` bullet), should the surface
reuse ONE `rec` modifier for both recursive data types and recursive functions (one construct,
multiple uses), the way some designs unify — or keep them distinct?

**Why it matters**: it is the SOUL "one construct per problem" test applied to a case where the
surface intuition (self-reference) tempts unification but the language's central axis pulls them
apart. Getting it wrong hides the total/Div seam that IS bang's identity.

**Detail** — the lean is: **keep them separate**, for three grounded reasons:
```
recursive DATA type          recursive FUNCTION
structural / well-founded    general / may not terminate
TOTAL (⊥-row, ADR-0029 μ)    DESCENDS into Div (fuel-bounded)   ← opposite sides of the seam
a value-type former          a computation-level fixpoint (fix)
```
1. **Data needs no marker at all** — ADR-0069 auto-detects recursion (the type's own name in a
   payload position IS the recursion, auto-μ-wrapped). A `rec` there is redundant.
2. **Functions DO need a marker** — to bring the name into scope in its own body. Different NEEDS ⟹
   not really one construct.
3. **`rec` is the wrong cut even for functions** — the load-bearing distinction is STRUCTURAL
   recursion (total, stays ⊥-row) vs GENERAL recursion (Div); `rec` blankets both.

**The constructive unification** (more on-thesis than a shared keyword): unify at the EFFECT-ROW
level — *recursion that can't be shown to terminate introduces `Div`*. Data contributes nothing
(total by construction); function recursion contributes `Div` unless structural. The row carries the
distinction (the generative constraint the type system reasons about), not a cosmetic keyword.

**Options**: (1) **separate + row-level unification** (recommended: `data` marker-free; recursive
functions signal generality via `Div` in the row). (2) shared `rec` modifier on both (surface
uniformity, but conflates the seam). (3) Lean-style separate keywords (`inductive` vs a recursive
`let`) — but bang's `data` already needs no keyword, so this is (1) without the row insight.

**Blocked on**: the recursion/`fix` bullet existing at all (not yet implemented; deferred from
ADR-0069's scope note). This is a design pin to apply THEN.

**Revisit signal**: starting the recursion bullet (`fix` + the `Div` row); or a request for
structural-recursion totality checking (which is where the structural-vs-general cut becomes real).

---

## Q29 — Handler-application syntax: prefix binder vs postfix eliminator (the effect eliminator wants eliminator syntax)  · OPEN (surface effect-model)

**Question**: should installing a handler be spelled as a PREFIX binder (`state 5 as h in body`, today)
or a POSTFIX eliminator chained on the body (`body ⟨…⟩ state 5`, Effect-TS/ZIO-style)?

**Why it matters** — *"syntax should serve and communicate semantics, not the other way around"*
(Pratt, via Cheng-Parreaux ECOOP'26 §Introduction, the paper behind ADR-0071). The current syntax
**mis-signals** the semantics. A handler is not a binder that happens to scope a body — it is the
**ELIMINATOR for effects**, the dual of the introduction/sequencing constructs (grounded in the
checker):
```
perform / h.get / raise    ADD ℓ to the row       INTRODUCE an effect  (φ ∪ {ℓ})
let x = e in body          UNION the rows          SEQUENCE             (φ₁ ⊔ φ₂)   ← NOT an eliminator
handler install            ERASE ℓ from the row    ELIMINATE an effect  (φ.erase ℓ) + delimit conts
```
So **handler : effects :: match : data** — both are eliminators, both correctly separate from `let`
(sequencing). This answers a related question ("why is handler-install a separate construct from
`let`?" — because it eliminates + delimits; `let` only sequences). But the PREFIX-binder spelling
(`state 5 as h in body`) dresses an eliminator as a binder, which is exactly why it keeps reading
awkwardly (the `with … as` wart ADR-0072 already trimmed once). POSTFIX reads as elimination —
`body.handle(state 5)` parallels `data.match(…)`; the syntax finally matches the operation.

**Detail — the regime split (load-bearing):**
- **AMBIENT effects** (row = deps, bubble up, ops resolve to the nearest lexical handler): postfix is
  a *pure syntactic reorder* — `state 5 in body` and `body ⟨install⟩ state 5` scope identically, only
  the reading order differs. It matches the mainstream Effect-TS/ZIO mental model (R in the type,
  handlers `provide`d postfix, handle-location flexible) — squarely on-moat ("safe to generate into").
- **NAMED capabilities** (explicit `Cap ℓ` value, ADR-0070/0072): CANNOT go postfix — `state 5 as h in
  body` binds `h` INSIDE `body`, but postfix writes `body` first, so `h` isn't in scope. Lexical
  capability binding structurally requires the handler to ENCLOSE the body (prefix). This is why
  Effect-TS *can* be postfix (ambient ops, no binder) and Koka/Effekt named handlers can't.
  ⟹ the clean split: **ambient application → postfix eliminator; named caps → prefix binder.** Two
  syntaxes, but principled — they mark two genuinely different regimes.

**⚠ The line to hold:** postfix `provide`-chaining as SUGAR OVER THE LEXICAL kernel (handler still
encloses a directly-written body) is cheap + sound. The FULL ZIO/Effect-TS *environment/reader* model
— pass an effect VALUE around (a thunk) and `provide` it later at the top — drifts toward
reader-passing, a bigger and possibly-unsound-under-lexical-dispatch (ADR-0052) fork. Keep
"postfix-sugar-over-lexical" and "full environment-passing" SEPARATE.

**Options**: (1) **status quo** — all prefix (`state 5 [as h] in body`, ADR-0072). (2) **ambient
postfix + named prefix** (recommended direction) — the eliminator framing made visible; matches the
mainstream model for the common case; named stays lexical-prefix. (3) full-environment (ZIO `R`+provide)
— rejected-for-now (the ⚠ line).

**Recommended**: (2) as the *direction*, but design-first (an ADR, not a snap change — unlike ADR-0072
which was cosmetic). Open sub-decisions: the exact postfix SPELLING (bang's `.` is already cap-perform,
`h.get`, so handler-application needs a DISTINCT token — not `.handle`), whether ambient+named
two-syntaxes is acceptable, and the thunk/environment boundary.

**Blocked on**: nothing hard — a design pass + ADR. Interacts with #44 (user-defined effects: a
user handler is also an eliminator, so its syntax should follow whatever this decides) and the
`handle`/`state`/`atomically` keyword-regularization deferred by ADR-0072.

**Revisit signal**: taking up #44 (user-defined effects & handlers — settle handler *application*
syntax as part of it); or agent/user ergonomics friction from the prefix-binder-dressed eliminator;
or when the effect surface-model is deliberately chosen (Koka-lexical vs Effect-TS-environment lens).

---

## Q30 — FBIP (Functional But In Place): static in-place reuse justified by the value-grade (verified enabler, compiled-path optimization)  · OPEN (post-v1 perf; enabled by grades)

**Question**: should BANG support FBIP — turning functional data updates (build a new constructor from
an old one) into IN-PLACE memory reuse (O(1) instead of O(n) allocation) — and if so, HOW, given
bang's verified-compilation discipline?

**Why it matters** — FBIP (Koka / Perceus: Reinking-Xie-de Moura-Leijen) is what makes purely-functional
data structures competitive with imperative ones: `map`/tree-update/etc. reuse the consumed
constructor's memory instead of allocating. It is the perf story for a language whose data is
immutable by default. The operator's intuition is right — **FBIP is a COMPILATION-PATH optimization,
not a reference-semantics change**: a program with FBIP computes the SAME values (Source.eval, a pure
functional interpreter, has no memory model), just with less allocation.

**The bang-specific twist (load-bearing):** FBIP's CORRECTNESS requires UNIQUENESS — you may only reuse
a constructor in place if its old value is DEAD (no other live reference). Koka proves this DYNAMICALLY
(Perceus = precise reference counting at runtime). **BANG already has the type-level uniqueness: the
value-GRADE** (QTT multiplicities 0/1/ω — the value-grade of Q27, `HasVTy`/`HasCTy`'s resource
discipline). A value used LINEARLY (grade 1) is provably the last reference — EXACTLY FBIP's
precondition. So bang's grade (a verified invariant) is the ENABLER for FBIP: "the constraint is
generative" (SOUL) — the grade is what lets the reuse fire, PROVABLY. Potentially an ADVANTAGE over
Koka: **STATIC grade-justified reuse** (compile-time, no runtime RC) vs Koka's dynamic RC-based FBIP.

**Where it sits (the stratification):** the OPTIMIZATION is compiled-path (CalcVM→WasmFX / the
runtime's memory reuse — invariant #7, performance second-class); the ENABLING INVARIANT is the
verified value-grade (kernel-path). The grade is the SEAM — verified core (uniqueness) + optimized
output (in-place reuse). This is the exact stratification pattern, applied to memory.

**Detail / dependencies**:
- Needs the value-GRADE surfaced/enforced (currently defaulted to ω, ADR-0066; Q27 is "surface the
  grade axis"). FBIP wants the grade-1 (linear) case reliably tracked.
- Interacts with the MEMORY MODEL (design-space-map #10: grades give use-once, not borrowing — FBIP is
  the use-once payoff).
- A verified FBIP would be a COMPILED-PATH proof: the reuse preserves the reference semantics *given*
  the grade-1 uniqueness. Koka's Perceus is the reference (but RC-based, dynamic); the grade-based
  static variant is the bang-native question.

**Options**: (1) **static grade-justified reuse** (recommended direction — compile-time, no runtime
RC, leans on bang's existing grades; the on-thesis version). (2) Perceus-style dynamic RC (Koka's
proven approach; a runtime, not grade-based — less on-thesis but battle-tested). (3) no FBIP
(functional-immutable, accept the allocation cost — invariant #7 says a slow correct path is fine
until it touches the user).

**Recommended**: record (1) as the direction; it's post-v1 perf, gated on the value-grade being real
(Q27) and the memory-model choice (#10). Design-first when perf on immutable data actually bites.

**Blocked on**: the value-grade surfaced + enforced (Q27); a memory-model decision (#10). Both post-v1.

**Revisit signal**: perf pressure on immutable data-structure updates (map/tree/list rebuild); OR
taking up Q27 (the grade axis) — FBIP is the concrete payoff that motivates surfacing the value-grade;
OR the memory-model / borrowing decision (#10).

---

## Q31 — Refinement types surface / quotient-proposition underlying: `Nat`, decidable checking, and the road to dependent types  · OPEN (major type-system direction, post-polymorphism)

**Question**: how does BANG get value-indexed precision — starting with `Nat` (a floor for total
recursion), reaching toward refinement and eventually dependent types — WITHOUT making type-checking
undecidable or the kernel un-verifiable?

**Why it matters** — three threads converge here. (1) `Nat` = the floor that turns measure-recursion
(factorial, countdown) TOTAL — `#47` certifies only STRUCTURAL recursion because unbounded ℤ (ADR-0067)
has no floor, so `($sum)(n-1)` genuinely diverges on negatives and correctly stays `Div`. (2)
Refinement types (`{n : Int // n ≥ 0}`) are the full form of "make illegal states unrepresentable"
(SOUL) — negative-`Nat`, out-of-bounds indices, div-by-zero become unrepresentable BY CONSTRUCTION.
(3) Dependent types NEED a total language (type-level computation must terminate to be decidable) — so
the total fragment (`#47`) is their prerequisite brick.

**The architecture (operator's direction — the load-bearing design):**
```
SURFACE (user-facing)   refinement types   { n : Int // P n }      ergonomic; illegal states
                                                                    unrepresentable; Liquid Haskell / F* / Dafny lineage
UNDERLYING (kernel)     QUOTIENT props     P realized as a         proof-IRRELEVANT (a subsingleton) —
                        (truncation ∥P∥ =  quotient by the total   the checker needs only that a proof
                        the (-1)-trunc)    relation → subsingleton  EXISTS, never to compare witnesses
CHECKING                decidable          discharge P via a        FEASIBLE: no witness-tracking (proof
                                           `Decidable`/decision     irrelevance) + the total fragment (#47)
                                           procedure                ensures the predicate's own evaluation halts
```
Why the quotient layer is the crux: proof-RELEVANT dependent checking is where feasibility dies (you
must compare proof terms, and with non-termination that's undecidable). **Propositional truncation via
QUOTIENT collapses all proofs of `P` to one point** → proof irrelevance → checking a refinement =
DECIDING `P` (a decision procedure), not comparing proofs. **`quotient underlying, refinement
surface`**: the kernel manipulates quotient/truncated propositions (verified, decidable), the user
writes the ergonomic subset type.

**The axiom-clean bonus (bang-specific):** `Quot.sound` is ALREADY one of BANG's trusted-3 axioms
(`{propext, Classical.choice, Quot.sound}`). The quotient foundation is on-hand and adds NOTHING to the
trust base — the underlying mechanism is already in the axiom budget. (And `propext` + proof
irrelevance are the same proof-collapsing move at the `Prop` level.)

**`Nat`, three ways (the concrete near-term instance — see also ADR-0073 §2 / #47):**
```
                     free termination     arithmetic    new machinery         expressiveness
inductive Nat        ✓ (structural — #47  O(n) Peano    none (rides data)     just Nat
  Zero | Succ           certifies it AS-IS: n-1 = the
                        Succ-predecessor subterm)
refinement Nat       ✗ (needs measure +   O(1) Int      quotient props +      Nat, {0≤i<len}, {n>0}, …
  {n:Int // n≥0}         floor reasoning)                a decision procedure  (the general mechanism)
stratified (Lean's)  ✓ structural for proof/type-level ⊕ efficient Int runtime ⊕ verified bridge
                        — verified core + tested superset + explicit seam (the project's signature move)
```
Near-term: **inductive `Nat` is the minimal win** — it rides `data` + the #47 structural checker with
ZERO new type machinery, making factorial-on-`Nat` total for free (measure-recursion collapses into
structural recursion: `n-1` IS `match n { Succ(m) -> m }`). Refinement types are the bigger, later
fork this question is really about.

**Options**: (1) **inductive `Nat` now** (rides #47, no new machinery — the incremental floor). (2)
**refinement types** with quotient-truncated decidable propositions (the operator's direction — the
general "unrepresentable by construction" mechanism; needs a decision procedure + the truncation layer).
(3) **full dependent types** (Π/Σ, `Vec n`) — the far end; rests on (2) + the total fragment. (4) none
(stay simply-typed + inductive data).

**Recommended**: inductive `Nat` opportunistically now (it's free once #47 lands); record refinement-
types-over-quotient-propositions as THE intended path to value-indexed precision (decidable by
construction, axiom-clean via `Quot.sound`), design-first when it's taken up. It sits post-polymorphism
(ADR-0027) — refinements interact with the poly lift (a refined generic type) and with grades (Q27).

**Blocked on**: the total fragment (`#47`, in flight — the termination floor + decidable type-level
evaluation); polymorphism (ADR-0027) for refined generics; a decision-procedure story (how far: syntactic
· `Decidable` instances · SMT). All post-v1.

**Revisit signal**: taking up `Nat` (do it the moment #47 lands — free total factorial); OR array/index
safety, positivity, or div-by-zero pressure (the refinement payoff); OR when the type system's power
axis (Q27 grades, ADR-0027 poly) is next lifted — refinements are the same "richer types" frontier.

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
