# Consult note — the grade-polymorphic binop returner (`F ∀q'`), issue #115

**Status:** DEFER (feasible + sound, ripple real, no consumer needs it yet).
**Witnesses:** `Bang/Witness/GradePolyReturner.lean` (6, axiom-clean ⊆ trusted-3).
**Companion:** `Bang/Witness/CtrGradeRefute.lean` (the CARVE-OUT refutation — the DIFFERENT shape).
**Decides:** whether to change the frozen kernel `binop` typing rule (Typing.lean:212) so its
returner grade is polymorphic, admitting COMPUTING custom-handler clause bodies into the verified
core (`custom_program_safe`) — closing the gap ADR-0100 accepted as a tested-superset.

## TL;DR

The change is **SOUND and feasible** — the falsifier hunt came back NEGATIVE. A grade-polymorphic
binop returner is not unsound: the operational reduct of a binop is `ret (op.eval a b)`, a CLOSED
literal, and a closed value types at ANY returner grade (`q' • zeros = zeros`), exactly the
grade-freedom the ret-shape clause already rides. The obstruction is purely the RULE SHAPE (today's
rule pins `1`), not the metatheory.

But **DEFER**: the ripple is real (three preservation/progress sites hard-code `F 1 (resTy)`, and
`binop_inv`'s conclusion must be re-shaped), and **no consumer needs verified-core clause bodies
today.** G1 — the ONE critical-path ask — is already met at the RUN level (tested-superset,
ADR-0100); its consumer (ndet/DST) needs soundness + differential test, which it HAS. The papers
(◊6) headline the calculated machine + binary LR, not custom-clause verified-core coverage. So the
prize is real but currently unclaimed. Land the door when a named consumer needs it, priced there.

## The three design questions, answered from witnesses

### Q1 — the rule shape (schematic vs grade-variable vs subsumption)

Three candidate shapes for admitting the freedom:

| shape | stateable? | witness |
|---|---|---|
| **schematic** `∀q'. HasCTy … (F q' (resTy))` (conclusion universally quantified in `q'`) | YES — the natural form; the reduct discharges it uniformly | `poly_returner_reduct_ok` |
| **grade-variable** in the judgment (a metavariable `q'` in the conclusion, unified at the perform site) | YES — operationally the same as schematic; this is the likely implementation form | (same discharge) |
| **subsumption** `1 ⊑ q'` (weaken the pinned `1` up) | **NO — unstateable today** | `grades_distinct_no_order`, `subsumption_needs_added_order` |

The subsumption shape is the *narrowest* on paper but is **blocked by the absent grade order**: the
kernel `HasCTy` is bound by `[CommSemiring Mult]` ONLY — there is no `LE`/`Preorder`/`Lattice` on
`Mult`, and QTT defines none (`Grade.lean`). The `lam` rule's own comment (Typing.lean:165-169)
records that Torczon's `Qle q' q` subsumption was DROPPED for exactly this reason. A weakening rule
would require ADDING an order to `Mult` first — a SEPARATE kernel change with its own ripple across
every grade-consuming rule (subsumption changes what `preservation` must show at each site). So the
subsumption "shortcut" is more expensive than the schematic form, not less.

**Verdict: the schematic/grade-variable shape** (`F ∀q' (resTy)` in the conclusion), NOT subsumption.

### Q2 — the soundness ripple, priced precisely

The binop returner grade is consumed at exactly these sites (all in `Bang/Core/Soundness.lean`):

| site | line | what it hard-codes | change under `F ∀q'` |
|---|---|---|---|
| `HasCTy.binop_inv` | 1844 | `C = CTy.F 1 (BinOp.resTy op)` in its conclusion | re-shape to `∃ q', C = F q' (resTy)` (or keep `q'` as an inversion output) |
| preservation binop arm | 2691 | re-types reduct at `F 1 (resTy)` | re-type at the redex's `q'` — **already discharged**: `BinOp.eval_hasVTy` (Soundness.lean:1860) types the reduct at `zeros`, so `ret` at any `q'` closes (this is exactly witness `reduct_closed_types_at_any_q`) |
| second preservation site | 3069 | same `F 1` re-type | same — closes via the closed-reduct fact |
| progress binop arm | 3209 | consumes `binop_inv` (ignores the grade: `_,_,_`) | inert to the grade — closes unchanged |

**The metatheory already contains the load-bearing lemma.** `BinOp.eval_hasVTy` (Soundness.lean:1860)
proves the reduct is a closed value at grade `zeros` — the EXACT fact witness W1 re-proves. So the
preservation arms' re-typing obligation is met for any `q'` with zero new lemmas; only the `F 1`
literals must become `F q'`. This is mechanical, not deep.

**`custom_resume_focus_types` (Soundness.lean:2176) — THE consumer that failed at 1≠ω — CLOSES.**
Under the grade-poly rule, a computing clause body `binop …` would type at the perform's `q_perf`
directly (no adaptation gap), so `custom_resume_focus_types` would extend to computing bodies by the
same closed-reduct move it already performs for ret-shape (invert to closed value, re-`ret` at
`q_perf`). The `letC`-of-binop case additionally needs the `q_or_1` floor argument re-examined at
the bound variable (`CtrGradeRefute.letc_body_not_at_zero` shows the floor bites at grade 0) — but
the surface uses `q_perf = ω`, and at ω the floor `q_or_1 ω = ω` is compatible; the grade-0 obstruction
is not on the load-bearing path. This wants its own witness before implementation (see "what remains").

**The LR custom arm (`BinaryLR.lean:1557`) adds NO new burden.** The binop arm is ALREADY a `sorry`
in the `lr_fundamental` cluster (independent of #115), waiting on a `crelK_binop` step-lemma that
relates equal `vint` literals to equal `op.eval` results. That lemma is about VALUE equality, not
the returner grade — the grade-poly change does not touch it. The compiler cluster
(`compile_forward_sim`) threads grades but the binop reduct's grade is `zeros` regardless of `q'`, so
the forward simulation is grade-inert here.

**Total price:** ~4 mechanical edits (turn `F 1` literals into `F q'` at the four sites +
`binop_inv`), 1 new witness for the `letC`-of-binop resume-focus at ω, and the extension of
`custom_resume_focus_types` + `HasClauses` to admit the computing shape (the actual verified-core
lift). The soundness DIAGONAL (`type_safety`/`preservation`/`progress`) does not gain new axioms —
it re-types uniformly in `q'` off the existing `BinOp.eval_hasVTy`.

### Q3 — the falsifier hunt (the make-or-break): NEGATIVE

**Is a program where an ω-graded binop returner is UNSOUND?** No. The usage-counting argument
resolves in favour of soundness:

- The returner grade `q'` on `F q' A` records how many times the continuation may consume the
  produced value. Soundness requires the produced value to actually TOLERATE being consumed `q'`
  times — i.e. its own variable budget must scale by `q'`.
- A binop produces `op.eval a b`, a **closed literal** (`BinOp.eval`, IR.lean:180 — `vint`/`boolVal`,
  no free variables, grade `zeros`). A closed value carries ZERO variable budget, so `q' • zeros =
  zeros` for every `q'` — consuming it ω times costs nothing. The returner grade is genuinely FREE
  because the result is a ground value, exactly like a closed `ret`.
- Witness `reduct_closed_types_at_any_q`: `∀ q', HasCTy (zeros) Γ (ret (op.eval a b)) ⊥ (F q'
  (resTy op))`. Witness `reduct_types_at_both_one_and_omega`: it types at BOTH the pinned `1` AND
  the surface `ω` — the adaptation `custom_resume_focus_types` performs, working for the binop
  reduct.

**Contrast with the CARVE-OUT refutation.** `CtrGradeRefute.binop_body_not_at_omega` shows the
un-reduced BODY (`binop op (vvar 0) 100`, with a FREE operand) cannot type at ω — because the RULE
pins `1`. The freedom is present at the REDUCT (W1) but withheld by the RULE (W2,
`binop_pins_one_not_freedom`). That is the whole design point: #115 is a rule-shape change over a
metatheory that already tolerates the freedom, NOT a soundness repair. The `CtrGradeRefute` witnesses
refute the fixed-grade carve-out; they do NOT refute the grade-poly rule — and these witnesses show
why (the reduct is grade-free).

### Q4 — the alternative (subsumption at the clause boundary only)

Stated: instead of changing the binop rule, add a grade-weakening step at the `HasClauses` boundary
(`1 ⊑ q_perf` only where a clause body plugs into the resume focus). Priced: **blocked by the same
absent grade order** (`grades_distinct_no_order`, `subsumption_needs_added_order`). A boundary-local
weakening still needs `≤` on `Mult` to state `1 ⊑ q_perf`, and QTT has none. So it collapses to the
same prerequisite as the general subsumption (add order to `Mult`), while covering strictly less. No
advantage over the schematic binop rule. Rejected.

## The honest do-nothing (Q5): the DEFER verdict

ADR-0100's tested-superset ships TODAY. The consult's job is to check whether the prize justifies the
ripple. It does not, YET:

- **No v1 consumer needs verified-core clause bodies.** G1 (compute-then-return) is "the ONE
  critical-path ask" (ndet-dst-design.md §7) and is MET at the run level: the DST demo + tracer run
  correctly against `Source.eval`, differential-tested. The consumer needs soundness + differential
  test, NOT contextual equivalence or `custom_program_safe` coverage. ADR-0100 already delivers that.
- **The ◊6 papers don't headline it.** The paper skeletons (`docs/papers/`) headline the calculated
  machine (`compile_correct`) and the binary LR (`lr_sound`) — neither needs custom-clause
  verified-core coverage. A "computing clause bodies are verified-core" result would be a NICE
  addendum, not a load-bearing claim.
- **The stratification seam is working as designed.** ADR-0026/0028: verified core + tested superset,
  explicit type-visible seam. Computing bodies riding differential-test is the seam operating
  correctly, not a gap to plug.

So: the door is real, sound, and reasonably cheap (~4 mechanical edits + 2 witnesses + the
`HasClauses`/`custom_resume_focus_types` extension). It is NOT on any current critical path. **Land it
when a named consumer needs verified-core computing bodies** — most likely the post-v1 verified-core
DST demo (ndet §7's "a verified-core DST demo waits on the grade-polymorphic returner"). Priced there,
against a live consumer, not speculatively now.

## What remains before implementation (if the door is opened)

1. A witness for the `letC`-of-binop resume focus at `q_perf = ω` (the load-bearing grade), extending
   `custom_resume_focus_types` past the ret-shape. The `q_or_1` floor is compatible at ω but must be
   discharged, not assumed (the grade-0 case `CtrGradeRefute.letc_body_not_at_zero` shows the floor
   CAN bite — confirm ω is clear).
2. The `HasClauses` extension: a `cons_computing` constructor admitting `(op, body)` where `body`
   types at `F q_perf (resTy)` for the perform's grade (not just `(op, ret w)`). This is the actual
   verified-core lift; `custom_program_safe` then covers computing bodies.
3. Hand the ~4 `F 1`→`F q'` edits + the `binop_inv` re-shape to `proof-engineer` with the exact
   obligation (each closes off `BinOp.eval_hasVTy`); gate the soundness diagonal axiom-clean after.

## Recommendation

**DEFER, with the door fully mapped.** Update issue #115 to record: refute-first outcome = NEGATIVE
(sound, feasible, priced); shape = schematic `F ∀q'`, NOT subsumption (no grade order); ripple =
~4 mechanical edits off the existing `BinOp.eval_hasVTy`, LR arm already-sorry-independent; consumer
= none in v1/◊6, named future consumer = post-v1 verified-core DST demo. Keep the tested-superset
(ADR-0100) as the shipping answer. Open the door the moment a consumer claims it.
