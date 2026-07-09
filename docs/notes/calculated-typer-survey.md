<!-- note-status: active -->
# Calculated type CHECKING — design inputs for a future ADR

> Research lane (typerx), 2026-07-09. Evaluates **The Calculated Typer** (`garby-haskell25-calculated-typer`)
> and **Sound-By-Construction Type Systems** (`bahr-pearl25-sound-by-construction`) as bang's answer to its
> biggest trust gap: `Bang/Frontend/TypeCheck.lean` (~3800 lines, UNVERIFIED) is load-bearing for every proof
> above it — a silent mis-elaboration poisons the kernel differential-test while every gate stays green.
> Docs-only research; no production code. SoT for the "calculate the CHECKER" idea.

## TL;DR (the one-sentence recommendation)

**Build the elaborator fuzz-harness NOW (near-term, cheap, closes most of the live risk); park the
calculated CHECKER as a post-Stage-7 research arc scoped to the pure declarative fragment; reject
evidence-passing for v1 (it optimizes a cost bang doesn't yet pay).** A calculated checker is *feasible for
a fragment* but does **not** cover what actually makes `TypeCheck.lean` dangerous — the elaboration (holes,
the μ-knot, row insert/erase, modules) — so it is a rigor upgrade to the safe part, not a fix for the risky
part. That asymmetry is the survey's sharpest finding.

## How this relates to the two BANKED docs (read them; this does not duplicate them)

There are already two archival docs on "calculate the type system", banked 2026-06-27. They target a
**different half** of the problem. Keep the split straight — it is the whole reason this doc is not a
duplicate:

```
                    ┌─────────────────────────────────────────────────────────────────┐
                    │  DECLARATIVE  HasCTy rules  (Bang/Core/Typing.lean, 403 lines)    │
   RELATION-calc ──▶│  "solve the soundness property for the RULES"  (Sound-By-Constr)  │◀── banked docs:
   (their SoT)      │  target: effect_sound / grade-erasure over the DEFERRED binary LR  │    frontier.md +
                    │  verdict: effect axis free · grade axis = #35 (fixpoint-complete)  │    experiment-findings.md
                    └─────────────────────────────────────────────────────────────────┘
                                              ▲  (spec the checker is derived FROM)
                                              │
                    ┌─────────────────────────────────────────────────────────────────┐
   CHECKER-calc  ──▶│  ALGORITHMIC checker  (Bang/Frontend/TypeCheck.lean, ~3800 lines) │◀── THIS doc
   (this doc)       │  "derive the decision PROCEDURE from HasCTy by fold fusion" (TCT)  │
                    │  target: the TRUST GAP — unverified checker/elaborator            │
                    └─────────────────────────────────────────────────────────────────┘
```

- `calculated-type-system-frontier.md` — **SoT for RELATION-calculation.** Its verdict (verified against
  source): the SbC/Cousot method ports, effect axis calculates for free, the grade axis derives at single
  steps but its *fixpoint* is sound-not-complete = **#35**; it targets `effect_sound`/grade-erasure over the
  *deferred* binary-LR route, **NOT** `type_safety`/`preservation` (diagonal-routed, already proven). So it
  does not help close v1 soundness.
- `calc-typer-experiment-findings.md` — the deployed Cousot join-preservation experiment. Headline: both axes
  preserve joins; the real break is **non-idempotence of the grade `+` at the fixpoint** (#35 = Cousot §II.3
  variant-bounded under-approximation, the resumption count is the variant).

**This doc is the missing third piece: the CHECKER, plus the trust-map / fuzz-harness / evidence-passing
questions the banked docs never touch.** The declarative relation is their input; deriving the *decision
procedure* from it is mine. A future ADR on "calculate the checker" cites all three.

---

## (a) What the two papers actually give

### The Calculated Typer (TCT, Haskell'25) — the direct template

The recipe (paper §4–8), specialized to what bang would do:

1. **Spec, not rules.** Start from a behavioural spec of the checker as an INEQUATION against the semantics:
   `texp e ≼ tval (eval e)` — "type-checking either returns a type error, or the type of the value `eval`
   would produce." The order `≼` is the *information order* (`ERROR ≼ everything`), reversed subtyping, made
   partial so it need not decide termination.
2. **Calculate by induction on `e`.** Each case strengthens `tval (eval e)` into a term of the form
   `texp e` by *defining* a suitable clause. Steps are equalities or reverse-inclusions. The type-level
   operations (`add'`, `cond'`, `catch'`) are *invented* by the calculation — they fall out of solving the
   distributivity/monotonicity obligations, not fed in.
3. **Fold fusion (the payoff, §6).** Once `eval = folde val add cond` and `texp = folde tval add' cond'`,
   correctness `tval (eval e) ≽ texp e` is a single **fold-fusion** application: it holds iff `tval` is a
   *homomorphism* from the value-operations to the type-operations (`tval (add x y) ≽ add' (tval x)(tval y)`,
   etc.) and the type-ops are monotonic. Induction is discharged once, structurally.
4. **Constraint composition (§7–8).** The homomorphism obligations become *inequational constraints* on
   `add'`/`cond'`; solving them for the greatest (most informative) solution yields the optimal, monotonic-
   by-construction definitions — no invented lemmas.

**Prerequisite — the judgment/semantics must be a FOLD.** TCT's entire leverage is fold fusion, which needs
`eval` (hence the checker) expressed as `folde` over the expression algebra. This is the load-bearing scope
gate for bang (see the feasibility table below).

**What TCT explicitly does NOT cover:**
- **Inference.** TCT derives a *checker* (a decision procedure over a fixed typing discipline), not an
  inference/elaboration algorithm. The paper's own Further Work (§12) flags inference and polymorphism as
  open. bang's `TypeCheck.lean` is *mostly inference + elaboration* (HM unification, holes, generalization).
- **Elaboration / desugaring.** TCT's `texp` returns a *type*; it does not rewrite the term. bang's checker
  ELABORATES: it desugars the μ-knot (`elabProg`/`letRecS`, ADR-0073), named ADTs (`matchD`, ADR-0069),
  modules (ADR-0076), the injected prelude, row insert/erase. None of that is in TCT's scope.
- **Non-termination.** TCT assumes terminating first-order languages (paper §1). bang has a Div fragment.
  (The checker itself is total via `fuel`/`bigFuel`, so this bites the *relation* side — SbC — not TCT.)

### Sound-By-Construction (SbC) — the companion discipline

SbC derives the declarative typing RELATION by *solving* the soundness property
`⊨ e : t ≡ ∃v. e ⇓ v ∧ v ∈ ⟦t⟧` algebraically (Knaster–Tarski: rules of strictly-positive form give the
least relation ⊆ the semantic one, sound by construction). TCT and SbC *compose*: SbC gives the relation, TCT
gives the program deciding it.

**SbC's blocker for bang is already settled in the banked docs**: strong normalisation is load-bearing (`∃v.
e ⇓ v` is vacuous on divergence), and bang threw SN away. The banked verdict: the *method* survives the move
to step-indexed `Crel`, but the grade axis is #35 and it targets the deferred soundness route. **This doc
takes SbC as done-elsewhere and focuses on TCT (the checker).**

---

## (b) The three-tier trust map for bang's frontend

The trust gap is real and structural. `TypeCheck.lean` is ~3800 lines, `Except`/`StateT`-based, and its
soundness link to the kernel is TODAY only a handful of `#guard`s and *one* worked `example` (`infer "3"`
matched to a hand-built `HasCTy` derivation, `TypeCheck.lean:156-166`). Everything above the checker trusts
its output. Three tiers, cheapest first:

```
tier                        what it buys                        reachable fragment              cost
─────────────────────────────────────────────────────────────────────────────────────────────────────────
③ fuzz the elaborator       "elaborate∘parse is total + its     ALL of surface bang            LOW · near-term
   (property tests)          output kernel-typechecks + agrees   (the whole checker)            (#14 template
                             with evalD" — caught, not proven                                   exists)
② elaboration soundness      "the elaborated kernel term HAS     the elaborated fragment        MED-HIGH · a real
   as a THEOREM               the type the checker claimed"       (needs the μ-knot etc.         Lean theorem, per
                             (`synthSC e = τ ⟹ HasCTy ⟦e⟧ τ`)    modelled in Lean)              construct
① calculated checking core   soundness BY CONSTRUCTION (the      the PURE DECLARATIVE           HIGH · research arc,
   (TCT fold fusion)          checker can't disagree with the     fragment only (§(d))           post-Stage-7
                             relation — no separate proof)
```

**The load-bearing insight: the tiers cover DIFFERENT fragments, and the risky part is the least covered.**
Tier ① (the calculated checker, the "correct by construction" dream) reaches only the *pure declarative
fragment* — the part that is already `synthC`/`checkC`, ~60 lines, and already the safest. The *dangerous*
~3700 lines are the `Infer`-monad elaboration (`synthSC`/`checkSC`/`elabProg`), which tier ① does **not**
reach. So the trust map is upside-down relative to intuition: **the more rigor a tier gives, the less of the
actual risk it covers.** This is why the recommendation leads with tier ③.

### What tier ③ (fuzz) can assert — concrete invariants over generated surface programs

The `#14` Lean-level fuzz harness (`Bang/Witness/Fuzz.lean`) is the template; ADT decls are the generator
spec (verification-ladder.md rung "derived generators"). Generated well-formed surface programs can assert:

- **`elabProg ∘ parse` is TOTAL on well-formed input** — no `throw`, no partiality escape. (Fail-loud: a
  crash is a located counterexample, not a silent skip.)
- **Elaboration OUTPUT kernel-typechecks**: `synthC (lower (elabProg e))` succeeds whenever `synthSC e`
  succeeds — the annotation-free lowering and the surface checker agree (there is already a *stated* agreement
  lemma target at `TypeCheck.lean:1191`, "`synthSC e` and `synthC (lower e)` agree" — fuzzing tests it
  before it is proven).
- **Type stable under `fmt` round-trip**: `synthSC e = synthSC (parse (fmt e))` — the canonical formatter
  (verification-ladder rung, live) must not change inferred types. Cheap, high-value (catches parser/printer
  drift).
- **evalD agreement already covers RUNTIME**: the `Agree` battery (`exec∘compile` back to `Source.eval`) is
  the existing oracle for *behaviour*; fuzzing extends it to *checker* outputs, so a mis-elaboration that
  changes runtime meaning is caught by the differential test even before tier ② proves it can't.

This is the near gap the verification-ladder already names (`#60 bang test`, "the declared-but-unchecked
property gap"). The elaborator invariants above ARE that runner's first payload.

### Tier ② — elaboration soundness as a theorem

The honest statement: `synthSC Γ e = (τ, φ) ⟹ HasCTy ⟦elab e⟧ φ τ` (elaborated term inhabits the claimed
type at the claimed row), per construct. This is *provable* (it is a standard elaboration-correctness
theorem) but expensive — it must model the μ-knot, generalization (the value restriction, `TypeCheck.lean:964`),
and row insert/erase in Lean. It is the natural climb once tier ③ fuzzing has de-risked the shape. It is
**not** the same as tier ①: tier ② proves the hand-written checker correct *after the fact*; tier ① makes it
correct *by construction*. Given elaborate-to-mono keeps winning, tier ② per-construct proofs are the
pragmatic middle rung.

---

## (c) Evidence passing — assessment (not a design)

**The static analog of bang's identity-keyed dispatch.** `xie-icfp21-generalized-evidence-passing`: the
single `perform op v` rule bundles two costs — **Searching** (a linear scan up the evaluation context for the
innermost handler of `op`) and **Capturing** (the resumption). Evidence passing pushes an **evidence vector**
(one entry per effect in the row) down the context so that `perform` becomes a **local O(1) lookup** — the
search is gone. Canonical vectors give constant-time lookup (Koka's choice); insertion-ordered are cheaper to
build but linear to look up (paper §2.5).

**Mapping to bang.** bang's core principle is *typing by LABEL, dispatch by IDENTITY* (CLAUDE.md glossary).
At runtime, `perform c op v` dispatches by the capability's identity `n` via `splitAtId` — which is exactly a
**Searching** step (walk the stack to the frame whose id matches). Where the effect row at a call site is
**concrete** (the common case — bang's rows are label sets, mostly closed after elaboration), the handler
that `splitAtId` will find is *statically determined*, so the evidence-vector move applies verbatim: replace
the runtime `splitAtId` search with a compile-time-resolved evidence index. This is precisely the operator's
earlier "dispatch-table / JIT" intuition, formalized — and it is the *static* counterpart to what bang
already does dynamically.

**What it would buy:** dispatch O(1) instead of O(stack-depth) unwind-find; and (the bigger Koka win)
tail-resumptive ops (bang's `get`/`put`/`read`/`write` — all one-shot, `Compat.lean:1080`) evaluate IN-PLACE,
skipping the yield/resume cycle entirely.

**What it threatens — why it is NOT for v1:**
- **It optimizes a cost bang doesn't yet pay.** Invariant #7: performance is second-class; "a slow correct
  path beats a fast unverified one." `splitAtId` is correct and its cost is invisible to the user today.
- **It threatens the calculated machine's SHAPE.** The CalcVM is an *output of calculation* (invariant #4);
  its dispatch is `splitAtId` by construction of `evalD`. An evidence vector is a *different runtime
  representation* — adopting it means re-deriving the machine with evidence in the state (a new `evalD`, a
  new `compile`/`exec`, a new `Agree` battery). That is a machine-calc research arc, not a checker change.
- **It presupposes row-concreteness.** With single-ρ row polymorphism (`#56`) a call site's row may be
  *open* (a fresh ρ), and the evidence index is then not statically known — the same limit Koka's polymorphic
  handlers hit. bang's row-poly is deliberately limited (ADR-0075 mixing limit), so this is a real constraint.

**Assessment: park it.** Evidence passing is a *backend/machine* optimization keyed on concrete rows, not a
*checker* technique. It is worth a note against the CalcReify/multi-shot work (where dispatch cost becomes
visible), but it is orthogonal to the trust gap this survey exists to close, and it fights invariant #4/#7.
Cross-reference: `bang-lang-cap-rep-labelling-vs-closure` (labelling vs closure cap-rep) is the adjacent
memory — evidence vectors are a *third* rep, and the same "does it survive multi-shot" question gates it.

---

## (d) Recommendation with costs — and the feasibility verdict (incl. the refutation)

### Which fragment is reachable by a calculated checker? (the feasibility table)

TCT needs the checker expressed as a **fold** over the term algebra, deriving *type-level operations* by
solving homomorphism constraints against the semantics. Grade bang's constructs against that gate:

| construct                         | fold-expressible? | calculable checker? | why |
|-----------------------------------|-------------------|---------------------|-----|
| pure CBPV core (ret/let/force/app/case/split/lam) | ✅ yes | ✅ **yes** | `synthC`/`checkC` (TypeCheck.lean:76-109) is ALREADY a structural fold on `Comp` — the TCT template transcribes directly; the pure fragment is the reachable core |
| ADT formers/eliminators (ADR-0029)| ✅ yes | ✅ yes | structural; `case`/`split` are folds with a branch-agreement constraint (TCT's `cond'` pattern) |
| effect rows (perform/handle)      | ⚠️ partial | ⚠️ single-step yes | the banked experiment DERIVED `perform`'s row `{op} ⊔ φ` by TCT/Cousot at single steps; the *fold* over handle-discharge is `eraseRow` — expressible, but see grades |
| **grades** (the `let`-rule `γ₁ + (q1·q_or_1 q2)•γ₂`) | ⚠️ single-step | ❌ **NOT at fixpoints** | banked finding: grade `+` is non-idempotent ⟹ fixpoint sound-not-complete = **#35**. Grades are CHECKED not INFERRED at loops *by construction* (frontier.md:143) |
| **HM inference** (unification, holes, generalization) | ❌ no | ❌ **no** | not a fold — it is stateful constraint solving (`Infer = StateT USt`). TCT explicitly defers inference (§12). This is the bulk of `TypeCheck.lean` |
| **elaboration** (μ-knot, modules, prelude, `elabProg`) | ❌ no | ❌ **no** | term-rewriting, not type-computing. Outside TCT's scope entirely |

### THE REFUTATION (first-class deliverable)

> **"Calculate the checker" does NOT fix the trust gap, because the calculable fragment and the dangerous
> fragment are disjoint.**

The trust gap is `TypeCheck.lean`'s ~3700 lines of **inference + elaboration** (`Infer`-monad `synthSC`/
`checkSC`/`elabProg`). TCT calculates **checking over a fixed discipline**, which in bang is the ~60-line pure
bidirectional core (`synthC`/`checkC`) — *already the safest, simplest, most testable part*. TCT gives
**no** purchase on unification, holes, generalization, or desugaring — exactly where a silent mis-elaboration
would hide. So a calculated checker is a **rigor upgrade to the part that is not the risk**. It is genuinely
valuable (it would make the declarative-fragment checker correct-by-construction and serve as the verified
*spine* the elaborator targets), but it is **not** the answer to "TypeCheck.lean is load-bearing and
unverified." The honest scope: calculate the CORE; **fuzz + per-construct-prove the ELABORATION.**

This refutes the premise as stated ("a calculated checker is bang's answer to its biggest trust gap") while
salvaging the real value (a calculated core + the fuzz harness together *do* close the gap, from two sides).

### Build / reject / defer

| verdict | what | cost | rationale |
|---|---|---|---|
| **BUILD NOW** | Tier ③ elaborator **fuzz harness** — total-elaboration, output-kernel-typechecks, fmt-stable-types, over `#14`'s template | LOW (days; `#60 bang test` is already the planned runner) | closes MOST of the live risk cheaply; the ~3700 dangerous lines get an oracle they lack today; fail-loud + declared-in-program (verification-ladder shape) |
| **DEFER (post-Stage-7 research arc)** | Tier ① **calculated checking core** — TCT fold fusion over the pure declarative fragment, producing a verified checker-spine the elaborator targets | HIGH (research; needs the pure fragment frozen + Stage-7 effects landed) | genuinely-novel only if it composes with the graded relation-calc (#35); serves ADR-0076's queryable-compiler (one checker, no second impl) |
| **DEFER (climb from ③)** | Tier ② **elaboration soundness theorems** — `synthSC e = τ ⟹ HasCTy ⟦elab e⟧ τ`, per construct | MED-HIGH (real Lean, per construct) | the pragmatic middle rung; prove what fuzzing keeps catching-clean; the elaborate-to-mono seam makes this the right altitude |
| **REJECT (for v1)** | **Evidence passing** in the checker/machine | — | optimizes an unpaid cost; fights invariant #4 (machine = calc output) & #7 (perf second-class); presupposes concrete rows (breaks under `#56`). Revisit at CalcReify/multi-shot |

### Is there an ADR-ready fork?

**Not yet — the near-term move (fuzz harness) is unambiguous and needs no ADR** (it is `#60`, already
planned). An ADR becomes warranted at the **Stage-7 boundary**, when the pure declarative fragment is frozen
and the question "do we calculate the checker-core, or keep hand-porting + fuzzing?" is a genuine
forks-in-the-road with a reversible cost. The frozen inputs for that ADR are exactly the three docs (this +
the two banked): relation-calc verdict (#35-gated, deferred route) + checker-calc scope (pure fragment only)
+ the trust-map (fuzz covers the elaboration, calc covers the core). Draft the ADR when Stage-7 lands, not
before.

## Status / gating

Post-Stage-7 for the calculated core; **near-term for the fuzz harness** (the one actionable thread — it
touches `#60`/`#14` real code and closes live risk). Off the current critical path for the calc-checker
research; the fuzz harness is not. SoT for CHECKER-calculation; the two 2026-06-27 docs remain SoT for
RELATION-calculation.
