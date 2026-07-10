<!-- note-status: skeleton — ◊6 paper draft, NOT full prose -->
# Paper 1 skeleton — *A Calculated Machine for Graded Effect Handlers*

> **One-sentence claim.** A verified compiler for a graded call-by-push-value language
> with lexically-dispatched effect handlers, in which the abstract machine is *calculated*
> (Bahr–Hutton) from the reference semantics rather than designed and verified after the
> fact, and the calculated machine is connected to a WasmFX-shaped target by an **annotated
> forward simulation** (`compile_forward_sim`, axiom-clean modulo two vacuous premises).
>
> **Riskiest related-work overlap.** PureCake (PLDI'23) and CakeML already deliver
> end-to-end verified compilation for functional languages; our novelty is *not* "a verified
> compiler" but "the machine is an **output of a calculation** over a *graded, effectful,
> identity-dispatched* source, with a concrete cross-kind divergence witness motivating the
> id-uniqueness invariant." The paper must foreground the calculation-vs-design axis and the
> handler/grading content, or a reviewer reads it as a weaker CakeML.

Status: SKELETON. Outline + precise claims + exact Lean theorem names/files/**real** axiom
sets + related-work map + honest what-remains. Not prose. Target audience: ICFP/PLDI/CPP FP-
verification track. All theorem citations below were checked against the repo at the base sha
(`lake env lean Bang/Audit.lean`, census reproduced in §7).

---

## 0. Metadata / framing

- **Substrate.** Graded CBPV (Torczon et al. OOPSLA'24 for the grading; Levy for CBPV), effect
  rows as an idempotent join-semilattice (`Finset Label`), handlers as values, capabilities by
  generative identity. Architecture-in-force: **ADR-0016** (two-hop: reference → CalcVM →
  WasmFX).
- **The two hops (the spine of the paper):**
  ```
  source → graded-CBPV reference (Source.eval)          [the specification]
         → CalcVM (Bahr–Hutton: exec ∘ compile = eval)   [the executable interpreter]
         → WasmFX-shaped target (annotated forward sim)   [the compiler output]
  ```
- **What is genuinely new** (claim inventory, defend each in §6):
  1. A Bahr–Hutton **calculation** run over a source with *effect handlers + QTT grading +
     identity dispatch* — prior calculation pearls (Bahr–Hutton JFP'15, Calculating Compilers
     Effectively '24, dependently-typed '21, monadic '22, graph-based '24) do not calculate a
     *handler* machine with lexical/identity dispatch.
  2. **Identity-first dispatch** with a machine-checked **cross-kind store-shadow divergence
     witness** that *forces* the store-disjointness invariant (`StoresBelow ∧ StoresDisjoint`).
     This is the paper's motivating example — a bug the naive machine has, made unrepresentable.
  3. The **annotated forward simulation** as the ◊5 method (ADR-0035), distinguished from the
     biorthogonal LR used for contextual equivalence (that is Paper 2).
  4. **Premised completeness** (ADR-0086): an honestly-premised headline (`VcapFree ∧
     CustomFree`) that is *true on every probed class but provable on none of the excluded
     ones*, with the premises vacuous for every elaborator-produced program.

---

## 1. Introduction — the calculation-vs-design axis

- **Hook.** Verified compilers usually *design* an IR/machine and then *prove* a simulation.
  The machine is a human artifact; the proof chases it. Bahr–Hutton invert this: specify
  correctness (`exec ∘ compile = eval`), and *calculate* the machine — `compile`, the `Code`
  datatype, and `exec` all fall out of equational reasoning. Invariant #4 of this project:
  "the machine is an **output** of the calculation, never hand-designed."
- **Gap prior work leaves.** The calculation pearls are pure/untyped (or dependently-typed but
  effect-free); the verified-compiler heavyweights (CakeML, PureCake) design their IRs. Nobody
  has calculated a machine for a language whose *paradigm is a value* — effects + handlers as
  ordinary library code over a five-primitive kernel (thunk · force · effect rows · handlers ·
  STM).
- **Contribution list** = the four claims in §0. Plus: the whole development is machine-checked
  in Lean 4; the axiom gate (§7) is the reproducible artifact.
- **Non-goals** (state up front, honesty): we do *not* verify handler algebra laws (state's 7
  equations — the structural, not equational, half of handler≈algebra; categorical-
  architecture.md §4); we do not close the Div (non-terminating) fragment inside the verified
  core; we ship *one* target shape, not a full WasmFX engine binding (Q9).

## 2. The graded-CBPV source and its reference semantics

- **2.1 Syntax + typing.** CBPV value/computation polarity; `F q A` (returner, QTT grade `q`),
  `arr q A B`; effect rows `φ : Finset Label` after `with`. Handlers as the `Handler` value
  with three built-in carriers (throws / state / transaction) + a fourth `custom` constructor
  (ADR-0087 finite-clause rep — `List (OpId × Comp)`).
- **2.2 The reference `Source.eval`** — a handler-based CK machine over configs
  `Config := (Nat × EvalCtx × Comp)` (the `Nat` is the global-fresh id counter, ADR-0055).
  This is *the oracle*: every other evaluator in the paper is differential-tested against it
  (invariant #1: "proof rides the reference").
- **2.3 Capabilities by identity (ADR-0054/0055).** A `vcap n ℓ` carries a generative identity
  `n` (minted monotonically at each `handle`) and a label `ℓ`. Typing is by **label**; dispatch
  is by **identity** (`splitAtId n` — an identity match, not a label search). This gap is the
  connective tissue between the two papers; here we need only that dispatch is deterministic
  and lexical.
- **2.4 Metatheory we rely on** (cite with axiom sets, §7): `subst_value`, `preservation`,
  `progress`, `type_safety` — all axiom-clean; `no_accidental_handling` — **0 axioms**
  (structural). These give us a well-behaved source to calculate from.

## 3. Calculating the machine (hop 1)

- **3.1 The Bahr–Hutton method, adapted to handlers.** Specify `exec (compile c) = eval c`;
  push `compile`/`exec`/`Code` through equational reasoning. The dispatch-agnostic Code
  constructors (`RET, LAMI, SUBST, APP, CASE, SPLIT`) fall out mechanically; the *novel*
  calculation is the handler machinery (`MARK, UNMARK, THROW, OP` + `unwindFind`), identity-
  keyed (ADR-0052 route B — the reference is re-derived cap-keyed so it dispatches by identity,
  not nearest-label).
- **3.2 The middle reference `evalD`.** The kernel's semantics with effects realized as
  explicit STATE (`SStore` + `THeap` + `CStore`, the per-kind stores) — a stateful *lowering*
  of `Source.eval`. Must agree: `evalD_agrees_source` (axiom-clean, §7).
- **3.3 The calculated triple** `(compile, Code, exec)` with `compile_correct`
  (`Bang.CalcVM.compile_correct`, axiom-clean) — the executable spec. The end-to-end diff-test
  `Agree fuel M v := exec (compile M) = some [ret v] ∧ Source.eval fuel M = .done v` ties
  `exec ∘ compile` back to the kernel.
- **3.4 The two-part simulation forms** `Bang.CalcVM.sim` and `Bang.CalcVM.run_evalD` (both
  axiom-clean) — pin the term-and-raised shapes against silent regression.

## 4. The motivating example — id-first dispatch and the cross-kind store shadow

**This is the section that earns the paper its "calculation buys you a real invariant" story.**

- **4.1 The naive machine has a bug.** Under identity-first dispatch (issue #62, operator
  ruling 2026-07-09), the identity `n` picks *which per-kind store services* a `perform`:
  `σ.get? n` (state) → `τ.get? n` (transaction) → `κ.get? n` (custom); the op only selects the
  operation *within* the resolved frame.
- **4.2 The divergence witness (the concrete example).** If an identity `n` could resolve in
  more than one store, a `perform` whose op mismatches the first-resolved kind must **RAISE** in
  `evalD` (fail-loud, the `handlesOp` image), but a machine that walks *past* the mismatched
  frame (via `stateUpdate`/`txnUpdate`/`customUpdate`) could find a **same-id shadow of another
  kind and RESUME** — a genuine raise-vs-resume divergence, *not* a proof gap. (Source:
  `Bang/Backend/AbstractMachine.lean:670-701`, the `StoresDisjoint`/`StoresBelow` doc-block.)
- **4.3 The fix is structural, not a runtime check.** `StoresBelow g` (every stored key `< g`,
  the fresh-id counter — the machine-store twin of the kernel's `WellCounted`) makes
  `StoresDisjoint` push-stable: each `handle` mints a globally-fresh key `≥` every existing key
  ⇒ distinct from the other stores ⇒ bumps `g→g+1`. The bad state is **unrepresentable by
  generative freshness**, not detected by a guard. This is the SOUL "correctness by
  construction" root move, and it is *the calculation surfacing an invariant the reference
  quietly relied on*.
  ```
  StoresDisjoint σ τ κ  :=  ∀ n, (σ.get? n ≠ none → τ.get? n = none ∧ κ.get? n = none) ∧ …
  StoresBelow g σ τ κ   :=  (∀ n, σ.get? n ≠ none → n < g) ∧ …          -- freshness supplies it
  ```
- **4.4 Why it stays inside `sim`.** The invariant is a *correspondence-side* bridge invariant
  (`Corr`/`StratFresh`/`WellCounted` lineage), NOT a program premise — so the public headline
  `compile_forward_sim` stays `VcapFree`-only and does not leak the store-disjointness premise.
  Both are trivially true at the empty-store entry and DERIVED at the fail-loud perform arms.

## 5. Hop 2 — the annotated forward simulation

- **5.1 Why forward simulation, not the LR (ADR-0035).** `compile_forward_sim` is
  one-source / one-target / one-direction — no context quantification, no two-sidedness. A
  state simulation suffices (AsmFX Thm 7.2 / Benton–Hur ICFP'09 shape). The biorthogonal LR is
  reserved for the *two-sided* contextual-equivalence theorems (Paper 2); using it here would
  be over-engineering (⊤⊤-closure buys compositionality the single-source statement does not
  need).
- **5.2 The exact headline** (checked, `Bang/Spec.lean:297`, axiom set
  `[propext, Classical.choice, Quot.sound]` — CLEAN):
  ```lean
  theorem compile_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
      Bang.Model.VcapFree c → Bang.CustomFree.CFComp c →
      Source.eval fuel c = Result.done v →
      ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v)
  ```
- **5.3 The proof structure.** PURE arm routes through the always-clean
  `compile_forward_sim_pure` (`Bang/Backend/Wasm.lean:2605`, clean); the HANDLER arm through the
  U5b completeness spine `evalD_complete_gen` (`Bang.Backend.U5bComplete`) — the converse-of-
  `run_evalD` bridge (1226 lines, every arm closed for the three built-in handler kinds,
  K=[] adapter included). `source_eval_to_exec` (clean) is the eval→exec leg.
- **5.4 The AsmFX epilogue/annotation technique.** Compiled-only fragments (suspend/resume
  scaffold, leave records) with no source counterpart get AsmFX's §7 annotation treatment.
  AsmFX (Lindley et al., "Effect Handlers All the Way Down", Oct'25 draft) is the nearest
  published twin — we adopt its *method*, not its machine (its ISA is not WasmFX; Q9).

## 6. Premised completeness — the ADR-0086 honesty move (a methodological contribution)

- **6.1 The situation.** The frozen ◊5 headline quantified over *raw* `Comp` with no premise.
  Wiring in the completeness spine exposed that the only known proof architecture (store-
  threaded converse; congruence and determinism routes build-refuted) requires `FreshCfg`,
  which two program classes violate: (i) non-`VcapFree` programs (a buried never-forced `vcap`
  completes in the kernel but fails `FreshCfg`), (ii) `Handler.custom` programs (`evalD custom
  = none` by ADR-0085 Stage-1, while kernel + machine both handle custom generically).
- **6.2 The key epistemic point** (the reviewer-facing defense). Both witnesses
  machine-check that the headline is **TRUE on those classes** (both sides complete
  identically, all `rfl`) — so this is "premise an unprovable *true* statement," not "repair a
  *false* one." Witnesses are census-protected regression files:
  `Bang/Witness/VcapFreeRefute.lean`, `Bang/Witness/CustomStage1Refute.lean`.
- **6.3 Premise lifecycle** (why this is not a permanent weakening). `CustomFree` is scaffolding
  with a named expiry (ADR-0085 Stage 4 derives the custom machine arm, then the premise
  DROPS — a consumer-safe strengthening). `VcapFree` persists until #21 (scoped capability
  types) makes a raw source `vcap` untypeable, after which it is derivable. **Both premises are
  vacuous for every elaborator-produced program** (the elaborator emits `vvar`, never raw
  `vcap`; no surface form emits `custom` until Stage 7), so the product-facing meaning of ◊5 is
  unchanged.
- **6.4 Generalizable pattern.** "Scaffolding premise with named expiry, justified by a
  true-on-the-class witness" is applied *three times* in this codebase (ADR-0086 `CustomFree`,
  ADR-0087 `NoCustomFrame`, ADR-0092's additive arms). Worth writing up as a discipline for
  frozen-statement evolution under proof-architecture limits.

## 7. Verification / reproducibility — the axiom census (checked at base sha)

The gate is `lake env lean Bang/Audit.lean`: PASS ⟺ every headline's `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`; any `sorryAx` = FAIL. **Real** axiom sets for this
paper's theorems (reproduced from the census, not the docs):

| theorem | file:line | axiom set | status |
|---|---|---|---|
| `compile_forward_sim` | `Spec.lean:297` | `propext, Classical.choice, Quot.sound` | **clean** |
| `compile_forward_sim_pure` | `Wasm.lean:2605` | `propext, Classical.choice, Quot.sound` | **clean** |
| `source_eval_to_exec` | (Wasm/backend) | `propext, Classical.choice, Quot.sound` | **clean** |
| `compile_well_typed` | `Spec.lean:283` | `propext` | **clean** |
| `zero_grade_no_code` | `Spec.lean:308` | `propext` | **clean** |
| `subst_value` / `preservation` / `type_safety` | `Spec.lean:79/94/131` | `propext, Classical.choice, Quot.sound` | **clean** |
| `progress` | `Spec.lean:109` | `propext, Quot.sound` | **clean** |
| `no_accidental_handling` | `Spec.lean:59` | *none* | **clean (0 axioms)** |
| `CalcVM.compile_correct` / `evalD_agrees_source` / `sim` / `run_evalD` | `CalcVM.lean` | `propext, Classical.choice, Quot.sound` | **clean** |
| `handler_compiles` | `Spec.lean:304` | **`sorryAx`** | **FLAGGED (bare `sorry`)** |

## 8. What is NOT proven (the honest scope section — mandatory)

- **8.1 `handler_compiles` is a bare `sorry`** (`Spec.lean:304`, axiom set `[sorryAx]`). The
  "handler ↦ suspend/resume compiles to an equivalent WasmFX handler" statement is *stated, not
  proven*. The forward-simulation headline routes around it (through the completeness spine),
  so `compile_forward_sim` does not depend on it — but the standalone handler-equivalence lemma
  is open. Do not claim it.
- **8.2 The two vacuous premises are still premises.** `compile_forward_sim` is clean *because*
  of `VcapFree ∧ CustomFree`. The unpremised form has no known proof (§6.1). Honest phrasing:
  "clean for the elaborator-image fragment," not "clean for all `Comp`."
- **8.3 `CustomFree` retention.** ADR-0085 Stage 4 (the derived custom machine arm) is the
  riskiest #44 obligation and is NOT done; until it lands the `CustomFree` premise stays. The
  converse-custom direction is pending (ADR-0087 rung-2 landed real dispatch census-clean, but
  Stage 4's *derived* arm — invariant #4 — is future work).
- **8.4 The Div fragment.** The verified core is the total (⊥-row, System F) fragment; the
  Turing-complete Div fragment rides fuel + differential testing, not proof (the stratification
  seam is the effect row itself). `compile_forward_sim` is fuel-bounded (`∃ fuel'`).
- **8.5 Target fidelity (Q9).** `Wasmfx.run` is an annotated *simulation* of the WasmFX
  semantics, not a binding to a live engine (wasm3 / Iris-WasmFX / WasmFXCert). The proof
  bindings are target-syntax-sensitive; the architecture is target-agnostic but the theorem is
  stated against our modeled machine.

## 9. Related work map (positioning — defend the delta for each)

| work | what they do | our delta |
|---|---|---|
| **CakeML** (Kumar et al. POPL'14; cakeml.org) | end-to-end verified compiler, hand-designed IRs, verified-after simulation | our front half is **calculated** (invariant #4), not designed; effect handlers + grading in the source |
| **PureCake** (Kanabar et al. PLDI'23) | first verified compiler for a *lazy* functional language, composes with CakeML | lazy vs our CBPV-graded-effectful; they design + verify, we calculate; they have machine-code end-to-end (we stop at a WasmFX-shaped target — an honest gap to name) |
| **Bahr–Hutton, "Calculating Correct Compilers"** (JFP'15) + pearls: dependently-typed (ICFP'21), monadic (ICFP'22), effectively ('24), graph-based ('24) | the calculation method; monadic pearl adds divergence, dependently-typed adds typed source | none calculate a **handler** machine with **identity/lexical dispatch**; ours is graded-CBPV + effects + the store-disjointness invariant |
| **Ager, Biernacki, Danvy, Midtgaard** (interpreter→compiler derivations, "A functional correspondence…") | derive abstract machines from interpreters by defunctionalization/CPS | our derivation targets a *compiler* (`compile`+`exec`), is Bahr–Hutton equational, and handles effects+grading |
| **AsmFX / Lindley et al.** ("Effect Handlers All the Way Down", Oct'25) | handler-compiler correct via plain annotated simulation (no Iris/biorthogonality) | we adopt the *method* for hop 2 (ADR-0035); their ISA ≠ WasmFX; our front half is calculated, not their concern |
| **Xie & Leijen, "Generalized Evidence Passing"** (ICFP'21) | efficient handler compilation to C via evidence passing | a *compilation technique* comparison point (our identity dispatch vs their evidence vectors); they are not verified end-to-end |
| **Torczon et al.** (OOPSLA'24, graded/coeffect QTT) | the grading discipline we inherit | we *compile* a graded language and show grade-0 erasure is observable in output (`zero_grade_no_code`) |

## 10. Venue candidates (fit notes — operator picks, do NOT commit)

- **ICFP** — best fit for the calculation-pearl lineage + FP framing; handler-compiler
  calculation is squarely in scope; Lean artifact welcome. Risk: "is the delta over the pearls
  a full paper?" — answer with the graded+effect+dispatch content + the divergence witness.
- **CPP** (Certified Programs & Proofs) — best fit for the *machine-checked* angle and the
  axiom-gate reproducibility story; smaller-delta results are acceptable there; the premised-
  completeness discipline (§6) is a natural CPP contribution.
- **PLDI** — highest bar; viable only if paired with a stronger target-fidelity result (a live
  WasmFX engine binding, §8.5) so it reads as end-to-end like PureCake. Currently a stretch
  given the `handler_compiles` gap and the modeled target.

## 11. What remains to write (author TODO before submission)

1. Full prose for §3 (the actual calculation steps for `MARK/UNMARK/THROW/OP` + `unwindFind` —
   the novel handler-Code derivation; currently only cited as landed).
2. A worked run of the §4 divergence witness as a figure (two-column raise-vs-resume trace).
3. Either **close `handler_compiles`** or reframe §5.3 so the contribution does not appear to
   need it (it does not — but the paper must say so cleanly and the reviewer must believe it).
4. Decide target-fidelity story (§8.5): ship as "modeled target" (CPP/ICFP-honest) or invest in
   an engine binding (PLDI-grade). Operator call.
5. Confirm the Stage-4 `CustomFree`-drop timeline vs submission date (§8.3) — if Stage 4 lands
   first, the headline strengthens and §6.3 shortens.
