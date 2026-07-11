<!-- note-status: active -->
# Compute-then-return design map — lifting the ADR-0095 D4 ret-shape restriction (#44 exit gate)

> **⚠ VERDICT CORRECTION (2026-07-11, ctr-g1 lane, F1 MACHINE-REFUTED). The DECISION lives in
> [ADR-0100](../decisions/0100-g1-compute-then-return-ships-tested-superset.md) — this note is the
> design probe; the ADR is the one decision home.** The "(γ) GO" verdict below (§2.3/§5) is
> **WRONG**. F1 — the ⊥-row computing-body grade-freedom claim — is **REFUTED, axiom-clean**, and
> the correct picture inverts the note's remedy:
>
> 1. **The kernel `HasClauses` computing-body carve-out is UNSTATEABLE at the grade the surface
>    actually uses.** The surface types every `binopS` AND every `perform` at grade **`.F .omega`**
>    (`TypeCheck.lean:1047, 1201`) — NOT grade 1. The kernel `binop` rule (`Typing.lean:212`) PINS
>    the returner grade to **1**. `1 ≠ ω`, so a lowered `binop` clause body cannot type at the
>    perform's grade in the kernel. §2.3's grade-freedom argument OVER-GENERALIZED: it holds only
>    for a CLOSED `ret w` (grade `[]`, so `q • [] = []` for all q), NOT a computing body whose
>    returned value carries a non-`[]` grade. Witnesses (build-gated in `Bang/Witness/CtrGradeRefute.lean`,
>    axiom-clean ⊆ trusted-3): `binop_body_fixed_grade` (bare binop types only at `F 1`),
>    `letc_body_not_at_zero` (the `q_or_1` floor breaks it at grade 0), `binop_body_not_at_omega`
>    (the §2.5 fallback fails at THE surface grade ω). KEPT as do-not-retry regression witnesses.
> 2. **But G1's CONSUMER is NOT blocked.** The surface already ACCEPTS ⊥-row computing clause
>    bodies (`checkHClauses` only checks the ROW is ∅, `TypeCheck.lean:1305` — it does NOT check
>    ret-shape), and `Source.eval` RUNS them correctly (`scratch/CtrTracerRuns.lean`: `n*10` ⇒ 30,
>    `let m = n*2 in m+1` ⇒ 11, both green vs the kernel oracle). G1 works TODAY, in the tested
>    superset — it is simply **not covered by `custom_program_safe`**, which is the intended
>    stratification seam, not a bug.
> 3. **The honest gate is therefore: G1 ships as a TESTED-SUPERSET feature** (surface-accepted +
>    differential-tested vs `Source.eval`), and the kernel `HasClauses` **stays ret-shape** (no
>    carve-out). Lifting it into the verified core would require making the kernel `binop` returner
>    grade POLYMORPHIC (a genuine kernel change far bigger than a carve-out — the §2.5 ∀q' premise
>    does NOT collapse to the ret-shape as the note claims; it is simply FALSE, because binop's
>    grade is pinned to 1, not free). **Q27 is still not needed for G1's RUN path; the answer-grade
>    pillar (B) IS load-bearing for the kernel-COVERAGE path, contradicting §2.4.**
>
> The original verdict is preserved below for the record. Read §"⚠ F1 REFUTATION" (appended) for
> the corrected slice plan. — the STOP-and-SHOW that produced this correction is the ctr-g1 report.

> **Verdict (one sentence — SUPERSEDED, see correction above).** The answer-grade wall **still
> stands** on current main
> (`69b16e2`) — all three D3 probes re-verify axiom-clean — but it is **narrower than the
> ADR-0095 D4 diagnostic implies**: the *surface* already accepts a **pure**
> compute-then-return body (`n * 10` type-checks and runs, the tracer), and the ndet G1
> consumer's `pick(n) => lcg(seed ⊕ step) mod n` is **exactly that shape — pure arithmetic,
> ⊥-row**. So G1 is **not** blocked by the grade wall at all; it is blocked by **one thing**:
> the *kernel* `handleCustom` soundness only covers `Comp.ret w` clause bodies, so a pure
> computing clause **runs in the tested superset, uncovered by `custom_program_safe`**. The
> honest exit gate is therefore **ADR-0065 stage ④ (a `HasCTy` rule for `Comp.binop`) + a
> ret-normalization of the clause body — NOT Q27**. Q27 (resumption grades) is a **mis-named
> co-requisite**: it gates *effectful* clause bodies (a genuinely harder, later thing), which
> G1 does not need. **v1.x-shaped for G1 (a bounded kernel-typing slice); bigger only if we
> insist on effectful bodies.**

Probe branch `probe-ctr-design`, witness `scratch/CtrWallRecheck.lean` (compiles clean,
`#guard`s green, RE2 prints the lowered-body head constructor). The three D3 probes
(`scratch/Custom{GradeFork,RetGrade,Resume}Probe.lean`) re-verified axiom-clean against
`69b16e2` — the do-not-retry ledger is intact and re-confirmed, not merely cited.

---

## 1 · Re-verify the wall against current main (the do-not-retry ledger, re-run)

The task's first ask: the D3 probes predate the term-measured LR rebuild, Stage 6, and the
landed Stage-7 surface (`1284c8e`). Re-run each on today's code. **All three still hold**,
machine-checked on `69b16e2`:

```
probe (committed 61ea80b)          claim                                          re-verify on 69b16e2
──────────────────────────────────────────────────────────────────────────────────────────────────
CustomGradeForkProbe               (1) flagship binop body types at NO grade      ✓ axioms [propext]
  .flagship_body_untypeable            (`HasCTy.binop_untypable`, pillar A)
  .const_ret_grade_generic         (2) bare `ret` types at ∀q' (ret grade-free)   ✓ axioms [propext]
CustomRetGradeProbe                the ret-shape resume re-types at the perform's ✓ axioms
  .custom_ret_resume_any_grade         FREE grade q_perf (pillar B's escape)          [propext,Classical,Quot]
CustomResumeProbe                  preservation-of-dispatch for the ret-clause     ✓ axioms
  .custom_resume_focus_types           resume, mono system suffices                   [propext,Classical,Quot]
```

And the wall's live consumers in the frozen metatheory are unchanged:

- `HasCTy.binop_untypable` (`Soundness.lean:1801`) is **live**, consumed as an absurdity in
  **three** preservation/progress arms (`:2618`, `:2984`, `:3113`). Every `Comp.binop` focus
  is discharged by "this can't be typed", not by a real typing arm.
- `HasClauses.cons` (`Typing.lean:346`) still **pattern-matches `(op, Comp.ret w)`** with
  `w : opRes` a **`HasVTy` value** — a clause body that is not syntactically `Comp.ret w`
  cannot construct a `HasClauses` derivation.
- The custom-dispatch preservation arm (`Soundness.lean:2417-2442`) and the LR custom arm
  (`BinaryLR.lean:1252 custom_clause_resume_of`, `:1306 krelS_custom_reinstall`) both consume
  `mem_typed`'s `body = Comp.ret w` fact; the resume focus reduces to `ret r` **definitionally**.

**Nothing dissolved.** The Stage 6 / term-measured landings *rode* the ret-shape, they did not
loosen it. The wall is exactly as ADR-0092 D3 recorded it. **BUT** the re-verification surfaced
a structural fact the D3 probes did not name, which reshapes the whole gate ⇩.

### 1.1 The wall is a KERNEL-TYPING wall, not a surface wall — and it has two independent pillars

The single most valuable output of this probe. The lowered clause body of the tracer
`fetch(n) => n * 10` is, machine-checked (`CtrWallRecheck.lean` RE2):

```
RE2: clause 'fetch' body head = Comp.letC (COMPUTATION — HasClauses.cons CANNOT match)
```

`n * 10` lowers (via `Surface.lowerHClauses → lowerC`, `Surface.lean:547`) to
`letC ca (letC cb (binop add …))` — a **computation**, not `Comp.ret w`. So:

```
                        the TRACER  fetch(n) => n * 10    the DIAGNOSTIC case  fetch(n) => raise n
──────────────────────────────────────────────────────────────────────────────────────────────────
surface check           ACCEPTS  (synthSC: F ω Int, ⊥ row) REJECTS (D4 diagnostic, ADR-0065+Q27)
  (checkHClauses,          — pure arithmetic passes the      — non-⊥ row fails the explicit
   TypeCheck.lean:1270)      explicit `φ = ∅` row check         `φ = ∅` check
lowered kernel Comp     letC…(binop…)  — a COMPUTATION       (never lowered — rejected first)
kernel HasClauses       CANNOT type it (needs Comp.ret w)    n/a
runs under Source.eval  YES ⇒ 30, diff-tested                n/a
covered by              NO — tested superset, oracle only    n/a
  custom_program_safe
```

Two consequences that the ADR-0095 D4 wording obscures:

1. **The surface type-gate (`synthSC`/`checkHClauses`) and the kernel soundness
   (`HasClauses`/`custom_program_safe`) are DIFFERENT layers**, joined by the stratification
   seam (differential test vs `Source.eval`), not by a kernel typing derivation on lowered
   output. `checkAndLower` (`TypeCheck.lean:3608`) runs `synthSC` then `lower` — it **never
   builds a kernel `HasCTy`/`HasClauses` derivation**. So "the surface accepts it" and "the
   kernel soundness covers it" are already decoupled for the pure case. The tracer is a
   *tested-superset* program that happens to type-check at the surface — exactly the
   language-level stratification seam (CLAUDE.md), operating as designed.

2. **The wall therefore has two independent pillars**, and they gate different things:

```
pillar   what it blocks                            what lifts it                     G1 needs it?
──────────────────────────────────────────────────────────────────────────────────────────────
A (binop) a clause body containing arithmetic       ADR-0065 stage ④: a HasCTy rule   YES — lcg
          types at NO kernel grade                   for Comp.binop (+ its 3 sound-     is arithmetic
          (HasCTy.binop_untypable)                   ness arms)
B (grade) a FIXED-grade computing body cannot        a general F q → F q' re-grading    NO — see §2.3;
          adapt to the perform's FREE grade q_perf   lemma (does not exist) OR the      G1 is ⊥-row +
          (the answer-grade wall proper)             ret-normalization dodge (§2.2)     ret-normalizable
```

Pillar A is the ADR-0065 staged-but-unlanded soundness work. Pillar B is the *actual*
answer-grade wall. **The D4 diagnostic names BOTH (ADR-0065 for A, "Q27 grade surfacing" for
B) — but G1 only trips A**, because a pure arithmetic body is ret-normalizable (§2.2) and never
reaches pillar B's fixed-grade problem. This is the finding that makes G1 v1.x-shaped.

---

## 2 · The minimal typed rule for compute-then-return bodies

### 2.1 What the ndet G1 consumer actually needs (the real requirement, narrowed)

`docs/notes/ndet-dst-design.md` §5.1/§7 G1: the stateless seeded scheduler's clause is

```
pick(n) => lcg(seed ⊕ step) mod n        -- seed, step: values in scope; lcg = a * x + c; mod, ⊕ arithmetic
```

Every operation here is `Comp.binop` (mul, add, mod-as-a-binop, xor-as-a-binop) over **values**
— it is **pure, ⊥-row, and terminates in one β/δ chain**. It is *precisely the tracer's
`n * 10` shape, one size up*. It does **not** perform, does not resume-non-tail, does not
mutate the param (G2/G3 are externalized away, ndet §7 items 3-4). So the requirement is
**narrow and specific**:

> **G1 = "a `⊥`-row, `Comp.binop`-only clause body must be covered by the kernel `handleCustom`
> soundness, not just accepted by the surface."**

### 2.2 The cheaper rung the D4 check already hints at: the effect-free carve-out + ret-normalization

The task asks: "does v1.x need the FULL grade channel or just an effect-free-computation
carve-out: body may compute but its row must be ∅ — the D4 check already tests exactly that row
property?" **Yes — this is the right rung, and it is cheaper than Q27.** Two moves compose:

**Move 1 — the effect-free carve-out (already the surface's check).** `checkHClauses`
(`TypeCheck.lean:1287`) already gates on `decide (φr.labels = ∅) && φr.tail.isNone` — the clause
body's row must be `∅`. This is the D4 property ("`ret w` is EFFECT-FREE") checked *directly on
a computation*, not via `synthSV`'s row-blindness. So the surface **already distinguishes** the
pure-compute case (accept) from the effectful case (reject). The kernel rule should mirror this:
admit a computing body **iff its effect row is `⊥`**.

**Move 2 — ret-normalization dodges pillar B entirely.** A `⊥`-row `Comp.binop`-only body is
**strongly-normalizing to a value** (δ-reduction is a total, store-free, one-step local
reduction, ADR-0065 §Consequences). So there exists a value `w` with `body ⟶* ret w`. Two ways
to exploit this:

```
option        the kernel rule admits…                             pillar B?      cost
──────────────────────────────────────────────────────────────────────────────────────────────
(β) ELABORATE  the surface pre-reduces the ⊥-row body to `ret w`   AVOIDED       elaboration-only:
    to ret     BEFORE building Handler.custom; HasClauses is         (body IS      the kernel/LR/
               UNCHANGED (still literally Comp.ret w)                 ret-shape)    soundness see NO change
(γ) TYPE the   HasClauses.cons gains a `| computeRet` arm: body :    FACED but     kernel typing rule
    body       F q opR at row ⊥, THEN the resume re-types via the     tractable     (ADR + operator) +
               body's OWN grade q (not q_perf), because a ⊥-row       for ⊥-row     the 3 binop soundness
               body's grade IS free the same way ret's is (§2.3)                    arms (pillar A)
```

**Option (β) is the v1.x recommendation.** It makes G1 land with **zero kernel/LR/soundness
change** — the surface elaborator normalizes a `⊥`-row `Comp.binop`-only clause body to its
`ret w` normal form, and every downstream proof (which already covers `Comp.ret w`) is
untouched. The kernel `HasClauses`, `custom_program_safe`, the preservation custom arm, the LR
custom arm — **all survive verbatim**, because the body they receive *is* `ret w`. This is the
elaborate-away move (ADR-0075/0088/0091/0093, invariant #5) applied once more: the surface owns
the normalization; the kernel never learns compute-then-return exists.

The cost of (β) is honest and bounded: the elaborator must **evaluate the clause body at
elaboration time** (constant-fold the pure arithmetic). But `seed`/`step` are **not constants**
— they are the op-arg `n` and the carried param, bound at *runtime*, not elaboration time. So
(β) as "constant-fold to a literal" **does not work for G1** — `lcg(seed ⊕ step) mod n` has free
variables. (β) degrades to (γ).

**So the honest recommendation is (γ): a kernel typing rule for `⊥`-row computing clause
bodies.** §2.3 shows why pillar B is tractable for the `⊥`-row case, and §2.4 sizes it.

### 2.3 Why pillar B (the grade wall) does NOT bite a ⊥-row body — the load-bearing argument

The answer-grade wall (ADR-0092 D3): the resume focus `body[p, v]` must plug into `Kᵢ` at the
perform's returner type `F q_perf opR`, where **`q_perf` is FREE** (a closed perform's
`q • γ_v = []` for any `q`). A general clause body pins a FIXED grade and cannot adapt. The
ret-shape adapts because `HasCTy.ret` re-derives the grade from the **closed payload** for ANY
`q_perf` (`const_ret_grade_generic`, re-verified).

The crux: **a `⊥`-row body that normalizes to `ret w` (closed `w`) has the SAME grade-freedom**,
because its grade is determined *entirely* by the terminal `ret` of its normal form, and a
closed `ret w` is grade-free. Concretely, for `letC (binop …) (ret (vvar 0))`:

- The `binop` produces a **closed value** (grade `[]`), bound by the `letC`.
- The outer `ret (vvar 0)` returns that closed binder — a `ret` of a closed value.
- So the composed `letC` grade is `q_binop • [] ⊔ q_ret • [] = []` for the *result* slot — the
  same `[]` a bare `ret w` gives. **The grade is free.**

This is *exactly* what `CustomGradeForkProbe.const_ret_grade_generic` shows for the constant
`ret`, and what pillar B's "no `F q → F q'` re-grading" fears for a *general* body. The
resolution: **a `⊥`-row body is not "general" — its grade collapses to `[]` because every
intermediate value is closed and inert.** The `F q → F q'` re-grading that "does not exist" for
an *effectful* body is *not needed* for a `⊥`-row body, because the `⊥`-row body's terminal grade
is already free. Pillar B was stated for the general case; **it over-generalizes to the ⊥-row
case it need not cover.**

> **This is the pre-registered falsifier for the whole slice (§3): construct, in Lean, a
> `HasClauses`-analogue derivation for `letC (binop add (vvar 0) (vint 100)) (ret (vvar 0))`
> that re-types the resume focus at ∀ `q_perf`. If it closes axiom-clean, pillar B does not
> bite the ⊥-row case and (γ) is a GO. If the `letC` grade composition pins a non-free grade,
> the wall is deeper than §2.3 argues and (γ) is refuted — fall back to §2.5.**

### 2.4 Where ADR-0065's binop typing enters — is it really "half the gate"?

**ADR-0065 is the LOAD-BEARING half, not merely half.** Pillar A is the whole of what G1 needs
beyond the ret-shape. Specifically, the general-body kernel rule (γ) cannot even be *stated*
until `Comp.binop` has a `HasCTy` rule, because the clause body's typing derivation
`HasCTy [opArg, P] body ⊥ (F q opR)` **inverts through the `binop`** — and today that inversion
hits `binop_untypable` (the `cases hM` in `flagship_body_untypeable`). So:

```
ADR-0065 stage ④ (the unlanded arm)          →  binop gets a HasCTy rule + 3 soundness arms
                                                  (Soundness.lean:2618/2984/3113 become REAL)
THEN the D4 general-body rule (γ)             →  HasClauses admits ⊥-row computing bodies
                                                  (rides §2.3's grade-freedom)
```

ADR-0065 §Consequences already scoped stage ④ ("re-prove the soundness arms") as **bounded**:
"`binop` is a deterministic, store-free, capture-free local reduction — the easiest case for
forward simulation; no headline axiom changes." That estimate is credible and re-confirmed here:
the three `binop_untypable` call sites are the exact arms that flip from vacuous to real.

**Q27 is NOT half the gate — it is mis-named as a co-requisite.** Q27 (resumption grades:
abort=0 / tail=1 / general=ω, `docs/notes/questions/Q27-surfacing-the-grade-axis.md`) is about
**how many times `k` is invoked** — a *different grade* than the answer/returner grade the wall
turns on. Q27 gates **effectful** clause bodies (a body that `perform`s before resuming needs
its resumption multiplicity declared, and is blocked on #35/#36 landing resumption grades in the
kernel). **G1's body is pure and tail-resumptive (one-shot, `k` at grade 1, implicit) — the v1
resumption discipline already covers it.** The ADR-0092 D3 / ADR-0095 D4 text bundles "Q27 grade
surfacing" into the exit gate because it conflated the *answer grade* (pillar B, which the
ret-shape/⊥-row-normalization handles) with the *resumption grade* (Q27, which only effectful
bodies need). **For G1, Q27 is not required.** (It remains required for the *effectful* clause
body — G4 multi-shot / a clause that performs — which is genuinely post-v1.)

This is a **first-class finding**: the named exit gate "ADR-0065 + Q27" is **half-right**.
ADR-0065 is necessary and load-bearing; Q27 is a mis-attribution for the pure case. The honest
gate for G1 is **ADR-0065 stage ④ + a ⊥-row-carve-out `HasClauses` arm** (§2.3's grade
argument), operator-ruled as a kernel typing change.

### 2.5 The fallback if §2.3 is refuted

If the pre-registered falsifier (§2.3) shows the `letC` grade pins a non-free grade, pillar B
genuinely bites the ⊥-row case. Then the fallback is the ADR-0092 §Revisit-if candidate
restated: restrict v1.x clause bodies to `φ' = ⊥` **AND** a **∀q'-quantified body typing**
premise (`∀ q', HasCTy [opArg,P] body ⊥ (F q' opR)`) — the (A)-fork the GradeForkProbe named.
The GradeForkProbe already showed this "collapses to value-returning bodies anyway" for the
*binop* body (because binop is untyped) — but once ADR-0065 types binop, the ∀q' premise becomes
*sourceable* for a ⊥-row body **iff** §2.3's grade-freedom holds. So §2.3 and the ∀q'-premise
fallback are the same claim viewed two ways; the falsifier tests both at once.

---

## 3 · The ripple — what gains an obligation, and its shape

The task: does the term-measured LR custom arm (`crelK_fund`) survive a general body? Does
`custom_program_safe`? Name each theorem + expected shape. **Under recommendation (γ) with the
§2.3 grade-freedom, the ripple is bounded; under a naive "any computing body" it is large.**

```
theorem / lemma                          survives ⊥-row (γ)?   obligation shape if general body
──────────────────────────────────────────────────────────────────────────────────────────────────
ADR-0065 stage ④ (PILLAR A)              — (this IS the work)  a HasCTy.binop rule + 3 real arms at
  Soundness.lean:2618/2984/3113                                 Soundness :2618/:2984/:3113 (progress:
  (currently `absurd … binop_untypable`)                        a typed binop on 2 vints steps;
                                                                 preservation: reduct has result type)
HasClauses.cons (Typing.lean:346)        NO — needs new arm    a `| computeRet` cons: body : F q opR
                                                                 at row ⊥ (drops the `Comp.ret w`
                                                                 pattern; §2.3 supplies grade-freedom)
mem_typed (Soundness.lean:2083)          NO — `body=ret w`     weakens to `∃ w, body ⟶* ret w ∧ …`
  / hasClauses_mem_typed (BinaryLR:1216)   is its conclusion     (a NORMALIZATION premise, not syntactic)
custom_resume_focus_types                RIDES §2.3            re-type at q_perf via the ⊥-row body's
  (Soundness.lean:2107)                    if grade-free         OWN free grade, not ret's directly
preservation custom arm                  NEEDS the above       consumes mem_typed's new `⟶* ret w`;
  (Soundness.lean:2417-2442)               chain                 the resume focus STEPS to ret w first
custom_clause_resume_of (BinaryLR:1252)  NO — hard-codes       the double-subst focus is `⟶* ret r`,
  / krelS_custom_reinstall (:1306)         `= Comp.ret r`        NOT `= Comp.ret r` — a ▷-guarded
                                                                 EVALUATION step before the reinstall
                                                                 (biernacki-popl18 §5.4 FULL resumptive
                                                                 clause — the case D3 was designed to
                                                                 EXCLUDE; this is the LR's real cost)
custom_program_safe_proof                YES — UNCHANGED       thin corollary of frozen type_safety';
  (Soundness.lean:3291)                                          constructor-agnostic. Gains NOTHING
                                                                 directly — the ripple is ENTIRELY
                                                                 inside preservation/progress, which
                                                                 it delegates to. (A structural win:
                                                                 the e2e headline needs no re-proof.)
```

**The two load-bearing ripples:**

1. **`mem_typed` stops being syntactic.** Today it reads a clause body *is* `Comp.ret w`. A
   computing body forces it to `∃ w, body ⟶* ret w` — a **normalization** fact. For a `⊥`-row
   `Comp.binop`-only body this normalization is a finite δ-chain (provable by structural
   induction on the body once binop is typed), so it is bounded — but it is genuinely new.

2. **The LR custom arm faces the case D3 was built to exclude.** `krelS_custom_reinstall`
   (BinaryLR:1306) currently gets `subst … clause.2 = Comp.ret r` **definitionally** (the
   ret-shape), which is why Stage 5 was "one grind session" (`stage5-lr-design.md`: "the hard
   continuation-capture case *does not arise in v1*"). A computing body makes the resume focus a
   computation that must **step to `ret r`** before the ▷-guarded reinstall — the full resumptive
   clause of biernacki-popl18 §5.4. This is the **single hardest** piece of the whole slice, and
   it is a **binary-LR** obligation (contextual equivalence), which sits in the already-deferred
   `lr_sound` cluster (PATH W1/W2). **It is NOT on the `custom_program_safe` / soundness critical
   path** — soundness (preservation/progress) needs only move (1), not the LR.

**Verdict on the ripple:** `custom_program_safe` and the soundness headline survive with a
**bounded** normalization ripple (pillar A + move-1 mem_typed). The **LR** custom arm takes a
genuinely harder obligation — but the LR is a *separate theorem* (◊4 contextual equivalence, the
binary LR) already behind its own walls, and G1's consumer (the DST demo, a *run*-oracle) needs
**soundness + differential test, not the LR**. So the LR ripple can be **sequenced after** G1
ships and does not gate the consumer.

---

## 4 · The slice plan — pre-registered falsifiers, order, per-layer cost

### 4.1 Pre-registered falsifiers (refute-first)

```
F1 (the pivot)   §2.3's grade-freedom: a Lean derivation re-typing the resume focus of
                 `letC (binop add (vvar 0) (vint 100)) (ret (vvar 0))` at ∀ q_perf, axiom-clean.
                 REFUTED ⇒ pillar B bites the ⊥-row case ⇒ fall back to §2.5's ∀q'-premise (and
                 if THAT collapses to ret-shape, G1 is NOT v1.x — escalate).
F2 (binop cost)  ADR-0065 stage ④: the 3 `binop_untypable` arms flip to real arms with NO new
                 headline axiom + no fuel-recursion blowup. REFUTED ⇒ ADR-0065 is bigger than its
                 §Consequences claims ⇒ re-scope before the D4 rule.
F3 (mem_typed)   the ⊥-row `Comp.binop`-only body normalizes to `ret w` by structural induction,
                 provable without well-founded-recursion pain. REFUTED ⇒ normalization needs a
                 termination measure ⇒ heavier than "bounded".
F4 (surface)     the elaborator can DISTINGUISH a ⊥-row computing body (admit to (γ)) from an
                 effectful one (reject, D4 diagnostic) — already TRUE (CtrWallRecheck RE1/RE1b,
                 machine-checked). Not at risk; recorded as the green baseline.
```

### 4.2 Probe / slice order

```
slice 0  (this note)  DONE. Wall re-verified, two-pillar structure named, Q27 mis-attribution
                      surfaced, ripple mapped. Scratch witness CtrWallRecheck.lean (the slice-0
                      F2-dependency probe was superseded when F2 landed — see the F1 refutation).
slice 1  ADR-0065 ④   land the binop HasCTy rule + 3 soundness arms (F2). Kernel lane; ADR-0065
                      is already Accepted, so this is EXECUTION of a decided ADR, not a new one.
                      ← RECOMMENDED SLICE 1 (the machine-checked dependency below FORCES this order).
slice 2  F1 probe     scratch: the ⊥-row-body grade-freedom derivation (§2.3), NOW STATEABLE (binop
                      types). GO/NO-GO for pillar B. [OUTCOME: REFUTED — see the F1 refutation
                      section. The body types at F 1, not the perform's grade ω; the carve-out is
                      unstateable. Witnesses in Bang/Witness/CtrGradeRefute.lean.]
slice 3  D4 kernel    the `⊥`-row `HasClauses` arm + mem_typed normalization (F3) + the preservation
         rule         custom arm's step-to-ret. Needs an ADR (kernel typing change) + operator ruling.
slice 4  surface      lift checkHClauses' reject → accept for ⊥-row computing bodies; wire the
                      D4 diagnostic to fire ONLY for non-⊥ rows (already the row check — just stop
                      rejecting ⊥-row computations). Elaboration-leaf.
slice 5  consumer     ndet G1: `pick(n) => lcg(seed ⊕ step) mod n` type-checks + runs; the sim-KV
                      Draft C moves from examples-draft/ to examples/. The payoff.
slice 6  LR (defer)   krelS_custom_reinstall's step-to-ret (§3 ripple 2). Behind lr_sound's walls;
                      NOT gating slice 5. Sequenced last.
```

### 4.3 Per-layer cost

```
layer                        cost            gate
──────────────────────────────────────────────────────────────────────────────────────────
F1 probe (slice 1)           hours           scratch build, axiom-clean
ADR-0065 ④ (slice 2)         days            operator: none (ADR Accepted); gate = 3 arms + census
D4 kernel rule (slice 3)     days–1 week     ADR + operator ruling (kernel typing change, invariant-
                                             adjacent); gate = HasClauses arm + soundness census-clean
surface (slice 4)            hours           frontend leaf; gate = tracer-shaped #guards + example run
consumer (slice 5)           hours           the DST demo runs; gate = tools/check-examples.sh
LR (slice 6, deferred)       1+ week         binary-LR resumptive clause; gate = lr_sound cluster
                                             (already deferred — does NOT block slices 1-5)
```

---

## 5 · Honest verdict

**v1.x-shaped for G1 — a bounded, mostly-decided kernel-typing slice — provided F1 holds.**

The exit gate is **not** the intimidating "answer-grade wall + Q27 resumption grades" the D4
diagnostic implies. It is:

1. **ADR-0065 stage ④** (already an Accepted ADR; execution, not decision) — the load-bearing
   half. Types `Comp.binop`, flipping 3 vacuous soundness arms to real ones (bounded by
   ADR-0065's own §Consequences estimate).
2. **A `⊥`-row carve-out for `HasClauses`** — the D4 check *already tests this exact row
   property* at the surface; the kernel rule mirrors it, riding §2.3's grade-freedom argument
   (the pre-registered F1 falsifier).

**Q27 is a mis-attribution for the pure case** and drops out of G1's gate entirely — it gates
*effectful* clause bodies (post-v1, G4). This is the sharpest correction the probe produces
against the standing ADR text.

**Bigger only if:** F1 is refuted (pillar B bites the ⊥-row case — then §2.5's ∀q'-premise, and
if *that* collapses, G1 is not v1.x and the effectful-body / Q27 machinery is genuinely
required); OR the project insists on *effectful* clause bodies now (G4 territory — multi-shot,
first-class `k`, Q22/Q27 — weeks-to-months, correctly deferred).

**The LR custom arm's harder obligation (§3 ripple 2) is real but off the critical path** — it
lives in the already-deferred `lr_sound` cluster, and G1's consumer needs soundness +
differential test, not contextual equivalence. Sequence it last.

**Recommended slice 1: the F1 grade-freedom probe** (`scratch/`, no live edits) — a single Lean
derivation that either greenlights the whole (γ) approach or refutes pillar-B-for-⊥-row in an
afternoon. It is the cheapest possible GO/NO-GO for the operator's twice-prioritized ask.

---

## Evidence

- **This lane's witness:** `scratch/CtrWallRecheck.lean` (RE1 surface-accepts-pure `#guard`; RE1b
  effectful-rejected-with-ADR-0065+Q27-diagnostic `#guard`; RE2 `#eval` printing the lowered
  clause-body head = `Comp.letC`). Compiles clean on `69b16e2`.
- **Re-verified do-not-retry ledger:** `scratch/Custom{GradeFork,RetGrade,Resume}Probe.lean`
  (committed `61ea80b`) — all axiom-clean on `69b16e2` (§1 table).
- **The wall in force:** `Bang/Core/Typing.lean:317` (`handleCustom`), `:344` (`HasClauses`, the
  `Comp.ret w` pattern); `Bang/Core/Soundness.lean:1801` (`binop_untypable`), `:2083`
  (`mem_typed`), `:2107` (`custom_resume_focus_types`), `:2417-2442` (preservation custom arm),
  `:3291` (`custom_program_safe_proof`, the thin corollary); `Bang/Meta/BinaryLR.lean:1216`
  (`hasClauses_mem_typed`), `:1306` (`krelS_custom_reinstall`, the resumptive-clause ripple).
- **The surface path:** `Bang/Frontend/TypeCheck.lean:1270` (`checkHClauses`, the `φ=∅` row
  check), `:3608` (`checkAndLower`, the synthSC-then-lower pipeline — no kernel HasCTy);
  `Bang/Frontend/Surface.lean:547` (binop lowering to `letC…binop`), `:652` (`lowerHClauses`).
- **The consumer pull:** `docs/notes/ndet-dst-design.md` §2.2 (the triple-block table), §5.1 (the
  stateless G1 design), §7 G1 (the ranked ask — "the ONE blocker on the critical path").
- **ADR inputs:** ADR-0065 (binop δ-rule + §Consequences stage ④ estimate), ADR-0092 §D3
  (the ret-shape wall + three probes), ADR-0095 §D4 (the teaching diagnostic naming the gate),
  `docs/notes/questions/Q27-surfacing-the-grade-axis.md` (resumption grade ≠ answer grade —
  the mis-attribution source), `docs/notes/multishot-survey.md` (Q22/Q27 the effectful/multi-shot
  future).

---

## ⚠ F1 REFUTATION — the corrected slice plan (ctr-g1 lane, 2026-07-11)

The header correction supersedes the "(γ) GO" verdict. Here is what the F1 refutation forces,
grounded in machine-checked witnesses.

### The refutation, precisely

```
witness (Bang/Witness/CtrGradeRefute.lean, axiom-clean)  claim
────────────────────────────────────────────────────────────────────────────────────────────
binop_body_fixed_grade                                  a bare binop body types ONLY at F 1 int;
                                                        NO derivation at F q_perf int for q_perf ≠ 1
letc_body_not_at_zero                                   the letC-wrapped body (returning the bound
                                                        result) cannot type at F 0 int — the q_or_1
                                                        floor forces usage ≥ 1, ret at grade 0 needs 0
letc_body_types_at_one                                  POSITIVE baseline: the SAME body DOES type at
                                                        F 1 int (the wall is grade-SPECIFIC, q ≠ 1)
binop_body_not_at_omega                                 the §2.5 ∀q' fallback FAILS at q' = ω — THE
                                                        grade the surface's perform actually uses
scratch/CtrTracerRuns.lean (2 #guards)                  BUT the body RUNS: n*10 ⇒ 30, let m=n*2 in
                                                        m+1 ⇒ 11, both green vs Source.eval
```

### Why the kernel carve-out is unstateable (the grade-layer mismatch)

```
                          SURFACE (ω-liberal)              KERNEL (grade-precise)
────────────────────────────────────────────────────────────────────────────────────────────
binop returner grade      .F .omega  (TypeCheck:1047)      F 1  (Typing:212, PINNED)
perform returner grade    .F .omega  (TypeCheck:1201)      F q  (q universally free, incl ω)
clause-body check         unifyC vs .F .omega resTy        HasClauses needs body : F q_perf opR
                          (TypeCheck:1297) — row-∅ only     at the perform's q_perf
verdict                   ACCEPTS the computing body       CANNOT type it at q_perf = ω (1 ≠ ω)
```

The surface and kernel grade algebras differ by design — the surface admits at ω what the kernel
types at 1. `checkHClauses` never builds a kernel `HasClauses`; it types via `synthSC` +
row-emptiness. So "surface accepts" and "kernel covers" were ALWAYS decoupled (the note's §1.1 got
this right). The error was believing the kernel could be RETROFITTED to cover the computing body —
F1 shows it cannot, because the binop returner grade is pinned to 1 while the perform is at ω.

### The corrected slices

```
slice     status         action
────────────────────────────────────────────────────────────────────────────────────────────
F2        LANDED (main)  ADR-0065 stage ④ HasCTy.binop rule + soundness arms — ALREADY MERGED
                         (45697d59 / b7269acb). Witness: Bang/Witness/BinopTyping.lean.
F1        REFUTED        the ⊥-row computing-body kernel carve-out is UNSTATEABLE at the surface
                         grade. Witnesses above. DO NOT attempt slice-3 (HasClauses carve-out).
slice-3   CANCELLED      the ret-shape HasClauses STAYS. No kernel typing change ships for G1.
surface   NO-OP          checkHClauses ALREADY accepts ⊥-row computing bodies (row-∅ check only).
                         B005 already fires only for effectful bodies. No surface change needed.
consumer  SHIPS AS       G1's compute-then-return clause bodies ship as a TESTED-SUPERSET feature:
          TESTED-        surface-accepted + differential-tested vs Source.eval. NOT covered by
          SUPERSET       custom_program_safe (the intended stratification seam, CLAUDE.md).
verified  DEFERRED       kernel coverage of computing bodies needs a GRADE-POLYMORPHIC binop
  core                   returner (F ∀q' int) — a genuine kernel change, NOT a carve-out, and out
                         of scope for G1. The answer-grade pillar (B) IS load-bearing for THIS
                         (contradicting §2.4); Q27 remains not-needed for the RUN path.
```

### Honest bottom line

G1 (⊥-row compute-then-return clause bodies) **already works** at the surface + run level and
needs **no kernel change** to ship as a tested-superset feature. What CANNOT be done — and what the
original note wrongly promised — is lifting those bodies into the verified core via a `HasClauses`
carve-out. That is blocked by a real grade-layer mismatch (surface ω vs kernel binop-1), refuted
axiom-clean. The `custom_program_safe` headline stays ret-shape; the computing bodies ride the
stratification seam, exactly as the language-level seam is designed to permit.
