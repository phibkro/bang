# ADR-0100 · G1 compute-then-return clause bodies ship as a tested-superset feature (the kernel carve-out is refuted)

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: A ⊥-row COMPUTING custom-handler clause body (compute-then-return, e.g.
  `fetch(n) => let m = n * 2 in m + 1`, the ndet G1 scheduler `pick(n) => lcg(seed ⊕ step) mod n`)
  **ships as a TESTED-SUPERSET feature, NOT as verified-core coverage.** The surface already
  ACCEPTS such bodies (`checkHClauses` types the body via `synthSC` and checks only that the effect
  row is `∅`, `TypeCheck.lean:1305` — no ret-shape check) and `Source.eval` RUNS them correctly
  (differential-tested: `n*10 ⇒ 30`, `let m=n*2 in m+1 ⇒ 11`). The kernel `HasClauses` **STAYS
  ret-shape** (`Typing.lean:357`, the `(op, Comp.ret w)` pattern); `custom_program_safe` does NOT
  cover computing bodies. This is the stratification principle applied exactly as designed (ADR-0026
  / ADR-0028: verified core + tested superset, joined by an explicit type-visible seam — here the
  differential test vs `Source.eval`). **The `ctr-design.md` "(γ) GO" verdict — a kernel `HasClauses`
  carve-out lifting computing bodies into the verified core — is REFUTED, machine-checked**: the
  carve-out is UNSTATEABLE at the grade a well-typed surface program uses. The surface types every
  `binopS` AND `perform` at grade `.F .omega` (`TypeCheck.lean:1047, 1201`) while the kernel `binop`
  rule PINS the returner grade to `1` (`Typing.lean:212`); a computing resume focus must type at the
  perform's grade (`ω`) to plug into the captured continuation (`custom_resume_focus_types`,
  `Soundness.lean:2508`), but a binop body types ONLY at `F 1`, and `1 ≠ ω`.
- **Resolves**: #44 stage-D4 exit gate (the compute-then-return question), for the ⊥-row PURE case
  (G1); the effectful-body case (G4) remains genuinely deferred (Q22/Q27, multi-shot).
- **Depends-on**: 0065 (the `binop` δ-rule + stage-④ `HasCTy.binop` typing rule — the pinned-`1`
  returner grade is the load-bearing fact this ADR turns on; F2, already landed), 0092 (the
  `handleCustom`/`HasClauses` ret-shape v1 restriction this ADR declines to lift), 0095 (the D4
  teaching diagnostic — B005 — whose message this ADR keeps honest), 0026/0028 (the stratification
  ladder this decision instantiates)
- **Relates-to**: `docs/notes/ctr-design.md` (the design probe; its verdict header now points AT
  this ADR as the one decision home), `docs/notes/ndet-dst-design.md` §7 (G1 = "the ONE
  critical-path ask" — met at the RUN level, open at the verified-core level),
  `docs/notes/questions/Q27-surfacing-the-grade-axis.md` (resumption grade ≠ answer grade — Q27
  stays not-needed for G1's run path), `Bang/Witness/CtrGradeRefute.lean` (the do-not-retry
  refutation witnesses)

## Status

Proposed. The operator ratifies (per `ctr-design.md`, this is the honest exit gate for the G1
arc — a decision a future session could relitigate, so it is recorded here rather than left in a
design note).

## Context

The #44 stage-D4 exit gate asks whether custom-handler clause bodies can COMPUTE before resuming
(compute-then-return), not just return a bare value. The `ctr-design.md` probe mapped the wall and
predicted a "(γ) GO": a bounded kernel-typing slice — ADR-0065 stage ④ (`HasCTy.binop`) plus a
⊥-row carve-out to `HasClauses` admitting computing bodies into the verified core, riding a
grade-freedom argument (§2.3).

Executing that plan surfaced a refutation the probe's paper argument missed. The grade-freedom
argument holds only for a CLOSED `ret w` (grade `[]`, so `q • [] = []` for any returner grade `q`
— the ret-shape adapts to the perform's free grade). A COMPUTING body returns a value whose grade
is NOT `[]`: a bare `binop` produces `F 1 (resTy)` at a FIXED grade `1` (`Typing.lean:212`), and a
`letC (binop …) (ret bound-var)` inherits that pinned grade (the `q_or_1` let-coeffect floor forces
the bound variable's usage to `≥ 1`). So a computing body types at a FIXED grade, and cannot adapt
to the perform's returner grade `q_perf` when `q_perf ≠ 1`.

The decisive fact is which grade a real program uses. The surface types every `binopS` AND every
`perform` at grade **`.F .omega`** (`TypeCheck.lean:1047, 1201`) — NOT grade `1`. So the kernel
resume focus for a compute-then-return clause would have to type at `q_perf = ω`, and `1 ≠ ω`.
The carve-out is unstateable at the load-bearing grade. This is pillar B (the answer-grade wall,
ADR-0092 D3) biting the ⊥-row case exactly as originally feared; `ctr-design.md` §2.4's claim that
Q27/the answer-grade pillar is a "mis-attribution for the pure case" is itself the mis-attribution.

Crucially, none of this blocks G1's CONSUMER. The surface/kernel grade algebras differ by design:
the surface is ω-liberal, the kernel grade-precise, and `checkHClauses` never builds a kernel
`HasCTy` derivation (it types via `synthSC` + a row-∅ check, then lowers). The computing body is a
tested-superset program that type-checks at the surface and runs correctly under `Source.eval` —
the language-level stratification seam operating as designed.

## Decision

**G1 (⊥-row compute-then-return custom clause bodies) ships as a tested-superset feature.** Three
concrete commitments:

1. **The surface accepts them, unchanged.** `checkHClauses` (`TypeCheck.lean:1288`) types the
   clause body via `synthSC` (full computation typing) and admits it iff the effect row is `∅`
   (`decide (φr.labels = ∅) && φr.tail.isNone`, `:1305`). A pure compute-then-return body passes;
   an effectful one is rejected with the B005 diagnostic. No surface change is needed — this is
   already the behaviour.

2. **The kernel `HasClauses` stays ret-shape.** No carve-out. `HasClauses.cons` (`Typing.lean:364`)
   keeps its `(op, Comp.ret w)` pattern; `custom_program_safe` covers only ret-shape clauses. A
   computing clause body runs in the tested superset, differential-tested against `Source.eval`
   (the `Agree` diff-test), NOT covered by the kernel soundness theorem. This is the intended
   stratification seam (ADR-0026/0028), not a gap.

3. **B005 names the honest boundary.** The D4 diagnostic (`TypeCheck.lean:1306`) fires only for
   NON-⊥-row (effectful) clause bodies — the genuinely-deferred G4 case (effects-before-resume,
   Q22/Q27, multi-shot). Its message stays truthful: what is rejected is effectful bodies, not
   pure compute-then-return.

The verified-core status: G1 is met at the RUN level (the DST demo and the tracer run correctly
against the oracle) and OPEN at the verified-core level (computing bodies are not in
`custom_program_safe`'s coverage). `docs/notes/ndet-dst-design.md` §7's "G1 = the ONE
critical-path ask" is therefore satisfied for the consumer (which needs soundness + differential
test, not contextual equivalence) while remaining a named verified-core gap.

## Rejected alternatives

- **The kernel `HasClauses` ⊥-row carve-out (the `ctr-design.md` "(γ) GO").** REFUTED,
  machine-checked. A computing clause body's resume focus cannot type at the perform's grade `ω`
  because the kernel `binop` returner grade is pinned to `1`. Witnesses (all axiom-clean ⊆
  trusted-3, KEPT as do-not-retry regressions in `Bang/Witness/CtrGradeRefute.lean`):
  `binop_body_fixed_grade` (a bare binop types only at `F 1`), `binop_body_not_at_omega` (it cannot
  type at `F ω` — THE surface grade), `letc_body_not_at_zero` (the `q_or_1` floor breaks it at
  grade 0), `letc_body_types_at_one` (positive baseline: the body DOES type at `F 1`, so the wall
  is grade-specific, not a syntactic defect). This is the do-not-retry evidence for the CARVE-OUT
  SHAPE specifically.

- **The `∀q'`-quantified body-typing premise (`ctr-design.md` §2.5 fallback).** REFUTED at the
  load-bearing grade. `ctr-design.md` claimed the ∀q' premise "collapses to the ret-shape"; it does
  not — it is simply FALSE, because binop's returner grade is pinned to `1`, not free.
  `binop_body_not_at_omega` witnesses the ∀q' premise failing at `q' = ω`.

- **A grade-polymorphic `binop` returner (`F ∀q' (resTy)`) — DEFERRED, not refuted, UNPRICED.**
  Verified-core coverage of computing clause bodies WOULD be reachable if the kernel `binop` rule
  produced a grade-polymorphic returner (so a binop body could adapt to any `q_perf`). This is a
  DIFFERENT shape from the refuted carve-out — the `CtrGradeRefute` witnesses do NOT refute it (they
  refute the FIXED-grade binop, which is today's rule). But it is a genuine kernel change to a
  frozen typing rule (invariant #4/#5 territory) with its own ripple across preservation/progress
  and the LR custom arm, and it needs its own design consult before it could be scoped. Deferred
  as unpriced; NOT part of G1. If a future session wants verified-core computing bodies, that is the
  door — priced there, not here.

- **Elaborate-to-ret (constant-fold the body to `ret w` at elaboration, `ctr-design.md` §2.2
  option β).** Does not work for G1: `seed`/`step`/the op-arg `n` are RUNTIME values (bound at
  dispatch, not elaboration), so the body has free variables and cannot be constant-folded to a
  literal. Ruled out by the note itself; recorded here for completeness.

## Ground (witnesses run against the real artifacts, this session)

- **Refutation, axiom-clean ⊆ trusted-3** (`Bang/Witness/CtrGradeRefute.lean`, build-gated by the
  `Bang.+` glob): `binop_body_fixed_grade`, `binop_body_not_at_omega`, `letc_body_not_at_zero`,
  `letc_body_types_at_one`. `#print axioms` on each: `[propext, Classical.choice, Quot.sound]` (the
  refutations that don't touch smul) / `[propext]` — no `sorryAx`.
- **Run evidence** (`scratch/CtrTracerRuns.lean`, checked via `lake env lean`): the two computing
  bodies the kernel cannot type DO run correctly under `Source.eval` — `n*10 ⇒ 30` (bare-binop
  clause), `let m=n*2 in m+1 ⇒ 11` (letC-of-binop clause). Both `#guard`-green vs the kernel oracle.
- **Surface baseline** (`scratch/CtrWallRecheck.lean`): the surface ACCEPTS the pure computing body
  (RE1 green), REJECTS the effectful body with the B005 diagnostic naming ADR-0065+Q27 (RE1b green),
  and the lowered body is `Comp.letC` not `Comp.ret` (RE2).
- **The soundness diagonal is UNTOUCHED** (this decision makes NO kernel edit): `type_safety`,
  `preservation`, `progress`, `no_accidental_handling`, `no_accidental_handling_custom`,
  `custom_program_safe` all axiom-clean ⊆ trusted-3, byte-identical before/after. `just verify`
  green.

## Consequences

- **Positive.** G1's consumer ships now, with zero kernel change and zero new proof burden. The
  DST demo runs against the oracle; the tracer runs. The verified core stays exactly as frozen. The
  stratification seam does its job: the expensive proof budget is spent only on the ret-shape core,
  and computing bodies ride differential testing.
- **The named gap.** `custom_program_safe` does not cover computing clause bodies. A program using
  one is safe by differential test + fuel, not by the kernel soundness theorem. This is explicit
  and type-visible (the clause body is not `Comp.ret w`), fail-loud in the sense that a future
  attempt to prove `custom_program_safe` over such a body will hit the refuted wall.
- **Roadmap honesty.** ndet §7's "G1 = the ONE critical-path ask" is met at the RUN level (tested
  superset) and open at the verified-core level. The distributed story's DST-as-handler arc can
  proceed on the run-oracle; a verified-core DST demo waits on the grade-polymorphic returner
  (above), which is post-v1.

## Revisit if

- The kernel `binop` rule is made grade-polymorphic (`F ∀q'`) — then the verified-core carve-out
  becomes stateable and this decision's rejected-alternative-3 gets its design consult. The
  `CtrGradeRefute` witnesses would need re-checking (they refute the FIXED-grade shape; a
  grade-polymorphic rule is a different object).
- The project decides G1's consumer needs contextual-equivalence / LR coverage (not just soundness
  + differential test) — that is a separate, larger obligation (the binary LR custom arm's
  resumptive-clause case, `BinaryLR.lean` `krelS_custom_reinstall`), already behind its own walls.
- Effectful clause bodies (G4, effects-before-resume) come into scope — then Q22/Q27 and the
  resumption-grade machinery are genuinely required, and B005's boundary moves.
