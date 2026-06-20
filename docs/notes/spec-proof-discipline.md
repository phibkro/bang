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
4. **`subst_value`** — validates the CBPV "no σ-split" assumption.
5. **the `[STD]` block** — mechanical once the above hold.

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
