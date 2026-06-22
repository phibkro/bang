# Spec proof discipline

> Reference doc for proof work against `Bang/Spec.lean`. Distilled from the
> original `bang-lang-wasmfx/CLAUDE.md` during the wasmfx merge (2026-06-21).
> The `proof-engineer` subagent (`.claude/agents/proof-engineer.md`) cites
> this doc as its primary discipline reference.

## Mission

Discharge every `sorry` in `Bang/Spec.lean` with a real, machine-checked proof.
Zero cheating. The theorem **statements are the spec** — they are frozen.

## Hard invariants (CI-enforced, non-negotiable)

1. **No `sorry`, no `admit`, no `sorryAx`** in any committed `.lean` file
   outside `Bang/Audit.lean` itself.
2. **No new `axiom`.** Every headline theorem may transitively depend ONLY on
   the trusted three: `propext`, `Classical.choice`, `Quot.sound`. Verify with
   `#print axioms <thm>` (see `Bang/Audit.lean`). Anything else = FAIL.
3. **Do not weaken a theorem STATEMENT.** You may not add a hypothesis, remove
   a conclusion, or specialise a quantifier. If a statement looks false or
   unprovable, STOP and record it (open question / CONTEXT.md). Never "fix"
   it by mutating it — a vacuous proof is worse than no proof.
4. **`≈` / `⊑` are fixed** (`Bang/Spec.lean §5`). Do not redefine
   `ctxApprox`, `ctxEquiv`, `Vrel`, or `Crel` to trivialise a goal. Their
   *content* gets filled in Phase A; their *role* is settled.
5. **No `opaque` survives in the proven core.** A proof about an `opaque`
   symbol is meaningless. Phase A replaces every stub with a real definition.
6. **No laundering.** No `native_decide` / `decide` on the metatheorems, no
   unproven `@[simp]` lemmas, no `Classical`-coercing a false goal to `True`.

## Scope

The engineering spine is the **two-grade** system: effect row `Eff` +
multiplicity `Mult`, both `OrderedSemiring`. That is the whole contract.
Build exactly this.

OUT of scope for the engineering phase (research-layer extensions — do NOT
start them, do NOT let them leak into `Bang/Spec.lean`):

- **cost / potential as a third grade** (AARA / calf line). Real direction,
  not the spine. Adding it now destabilises the contract.
- **distribution / CALM** (`Bang/Distribution.lean`) — separate result; stays
  a flagged conjecture.
- **modal-row alternative** to the lacks-discipline (Tang–Lindley) — a design
  fork already decided against in ADR-0018; do not re-litigate in code.
- **multi-shot cost, polynomial AARA** — open problems, not engineering tasks.

If a task seems to require any of the above, it is mis-scoped: STOP and
escalate rather than expanding the spine.

## Phases — do A fully before B

### Phase A — Definitions (NO theorem proofs yet)

Turn every `opaque` into a real definition:
- AST: `VTy`, `CTy`, `Val`, `Comp`, `Var`, constructors incl. `U ρ`, `F e`.
- Judgments: `HasVTy`, `HasCTy` as `inductive … : Prop`.
- Semantics: `Source.step` / `eval` / `evalTrace` as the fuel interpreter
  (reuse the existing `Bang/Eval.lean` once it's ported to graded CBPV at ◊2).
- The logical relation: `Vrel`, `Crel` by well-founded recursion on the step
  index then on types. **The `F e A` case is the crux — get it reviewed.**

Exit criterion: file builds, `sorry` appears ONLY in theorem bodies.

### Phase B — Proofs

Discharge `sorry`s in `PROOF_ORDER`. After each: `lake build` + run
`Bang/Audit.lean`.

## PROOF_ORDER (risk-first, not file order)

1. **`lr_sound`, `lr_fundamental`** — the LR is the spine; nothing is
   legitimate until soundness holds. `lr_fundamental` decomposes into the
   per-rule compatibility lemmas in `Bang/Compat.lean`; prove `compat_handle`
   LAST (it is the `[KEY]` one that consumes `Srel`). The rest of Compat is
   mechanical.
2. **`group_recovers`** — rollback; may force an observability side-condition.
   Surface it NOW, it reshapes the effect algebra.
3. **`compile_forward_sim`** — the contribution. Fail fast if it won't go.
4. **`subst_value`** — validates the CBPV "no σ-split" assumption. ✓ PROVEN
   (de Bruijn, `Bang/Metatheory.lean`, axiom-clean).
5. **the `[STD]` block** (preservation · progress · type_safety) — ✓ PROVEN
   (2026-06-22, axiom-clean). ⚠ It was NOT "mechanical": proving `preservation`
   exposed 4 ways the Phase-A typing rules diverged from the Torczon port and made
   the frozen statements FALSE (lam dropped its body effect; handle over non-`F`
   bodies broke progress; the letC grade reshape needs commutative `Mult`; progress
   is false at general `B`). All corrected in **ADR-0021**. Lesson: "mechanical
   once X holds" is a hypothesis the proof tests, not a license to skip the proof —
   the STD block is where the typing rules' fidelity to the reference finally bit.

## Definition of done

- `lake build` clean; `tools/audit.sh` exits 0.
- `Bang/Audit.lean`: every headline theorem's axiom set ⊆ {`propext`,
  `Classical.choice`, `Quot.sound`}. No `sorryAx` anywhere.
- Phase-A design choices recorded in ADRs (per project ADR discipline; see
  `docs/decisions/`).
- Anything you could not prove WITHOUT mutating it: escalated to the
  orchestrator and logged in `CONTEXT.md`.

## When stuck

Surface the gap; move to the next independent goal. Never fabricate a lemma,
weaken a statement, or `sorry` to "make progress". A red build with honest
gaps beats a green build that lies.

---

## What a clean proof looks like (canonical example)

The standard shape for a proof body in Bang/Spec.lean (or downstream
modules implementing Phase B). Note: statement unchanged from the frozen
PRD; only the body fills in.

`subst_value` is now PROVEN on the de Bruijn base (`Bang/Metatheory.lean`,
axiom-clean) — the real proof is a bottom-up lemma tree, not a single `induction`.
The block below is kept only to ILLUSTRATE the pattern (intro → induction →
case-by-case, technique cited, `sorry`-with-comment for blocked cases), using the
*current* (de Bruijn, ADR-0020) statement:

```lean
-- pattern: structural case-analysis on the typing derivation, technique cited.
-- shape: torczon-oopsla24-effects-coeffects §graded-subst  (port: resource/CBPV/typing.v)
-- the REAL proof (and its weakening/grade-arithmetic lemmas) is in Bang/Metatheory.lean.
theorem subst_value
    (ρ : Mult) {γ γ_v : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasVTy γ_v Γ v A →
    HasCTy (ρ :: γ) (A :: Γ) c e B →
    HasCTy (γ + ρ • γ_v) Γ (Comp.subst v c) e B := by
  intro hv hc
  induction hc with
  | ret hv'  => exact .ret hv'   -- structural: ret rule
  | letC hM hN ihM ihN => grind  -- handled by SMT-style closer
  | force hu => -- TODO(blocking-on): example only — see Metatheory for the real case
                sorry
  -- ... cases for force, lam, app, handle ...
```

What this exhibits:

1. **Statement frozen** — copied verbatim from `Bang/Spec.lean`; only the
   body changes.
2. **Technique citation** — `-- shape: biernacki-popl18-handle-with-care §5.4`.
   Cite the source paper / chapter as a comment so future readers can
   verify the adaptation.
3. **Pattern**: `intro → induction → case-by-case`. For 4-6-constructor
   judgments, this is the workhorse.
4. **Tactic choice**: `exact` for cases that match a constructor;
   `grind` (≥4.28) for cases SMT-style closure can handle; `sorry` only
   when blocked AND commented WHY.
5. **Sorry-with-comment** — never bare. The comment names what's blocking
   (e.g., a missing lemma, a definitional adjustment needed in the kernel)
   so a future session knows where to pick up.

## What an anti-pattern proof looks like

```lean
theorem subst_value ... := by
  intros
  sorry   -- ← bad: no reason, no plan
```

```lean
-- ALSO BAD: weakening the statement to make the proof close.
-- (Original statement removed a precondition; this version weakens.)
theorem subst_value_weakened (h : False) : True := by trivial
```

```lean
-- BAD: a generic `by tactic_chain` that masks failure modes.
theorem subst_value ... := by aesop  -- if aesop times out or
                                      -- fails partially, the actual
                                      -- structure is lost
```

**Discipline**: if a proof needs to weaken the statement, that's a signal
to escalate to `kernel-engineer` (statement might be wrong) — not a license
to mutate.
