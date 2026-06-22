# bang-lang CONTEXT

> Where we are on the map RIGHT NOW. Volatile. Updated as paths complete and
> new ones begin. **Read this first on every fresh session**, after `CLAUDE.md`.
>
> For the long-term map, see `ROADMAP.md`. For research-grade keyframes, see
> `docs/roadmap/bang-northstar-roadmap.md`.

## Position

```
◊1 ✓ Reconciliation landed        ── 2026-06-20
◊2 ✓ Kernel frozen v1 (GATE MET)  ── 2026-06-22. STD block proven on the de Bruijn
                                     base (ADR-0020); preservation EXPOSED 4 Torczon
                                     divergences (ADR-0021, corrected).
                                     ✓✓ STD BLOCK AXIOM-CLEAN OVER A CK MACHINE
                                     (ADR-0023): Source.step is config-level (EvalCtx ×
                                     Comp); deep handlers catch operations nested under
                                     letC/app; throws discards the captured continuation.
                                     FIXED a machine-checked FALSITY (ADR-0022 D3's
                                     "progress at ⊥ under the shallow step" — handle(throws ℓ)
                                     (letC (raise v) N) is well-typed at ⊥ yet stuck).
                                     preservation/progress/type_safety GENUINELY TRUE for
                                     effectful programs, axiom-clean, zero sorry. Exposed the
                                     handleThrows answer-type fix + op-partial EffSig (D6,
                                     co-resolves Q13).
                                     ✓✓ no_accidental_handling PROVEN 0-axiom (ADR-0024):
                                     correct-by-construction in the label-indexed machine
                                     (the ∀-h placeholder was vacuous; restated faithfully).
                                     WfInst carries the lacks-constraint (rowinst proven).
                                     GATE MET (just verify green). RESIDUAL (non-gate):
                                     effect_sound (trace semantics → Q14), zero_usage → ◊4.
◊3   CalcVM ported
◊4   LR foundation
◊5   Compiler v0
◊6   Release v0
```

## Most recent stable checkpoint

**◊1 — Reconciliation landed (2026-06-20)**

What changed:
- **ADR-0016** committed (`docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md`)
  — establishes the two-hop architecture: graded-CBPV semantics → CalcVM
  (Bahr-Hutton) → WasmFX (Benton-Hur LR).
- **ADRs 0003 (own-the-runtime) and 0004 (calculated-vm-canonical) deleted** —
  subsumed by 0016, not just superseded.
- **ADR-0015** annotated: CalcReifySim bisimulation is **paused**
  (LR subsumes the goal); the machine itself stays.
- **`references/`** scaffolded — 30+ papers organized into topical subdirs,
  `refs.bib` seeded.
- **`ROADMAP.md`, `CONTEXT.md`, `paths/`** scaffolded — the orchestrator-
  layer doc system.

## Subsequent landings (housekeeping; not new checkpoints)

### SOTA literature sweep + reconciliation (2026-06-21)

Five-axis web sweep of 2024–2026 literature, integrated. **Four of five axes
confirm our frozen choices; the WasmFX target drifted.** See
`references/README.md` → "Integration findings".
- Library reorganized by pipeline stage (`papers/1-kernel 2-calcvm 3-lr
  4-wasmfx adjacent`); 7 new papers fetched + sorted; `refs.bib` corrected
  (the "calculating-effectively" PDF is Garby-Hutton-Bahr Haskell'24, not the
  ICFP'22 it was labeled).
- SOTA confirmations cited in source: Yoshioka ICFP'24 (join-semilattice =
  exact effect-safety structure) → `EffectRow.lean`/ADR-0001; Zhang-Myers
  POPL'19 tunneling (accidental-handling origin) → `Spec.lean`; McDermott
  FSCD'25 → `Core.lean`.
- **WasmFX drift** recorded as OPEN_QUESTIONS Q9 (◊5 obligation, pin-to-engine).
- Commit `d1aff27`.

### subst_value reframed → ◊2 is bigger than it looked (2026-06-21)

Fixing the (vacuous) `subst_value` exposed that the typing rules **carry but
never enforce** grades — `HasCTy` is grade-insensitive. The real graded
`subst_value` is now stated (sorry); proving it (and `zero_usage_erasable`,
`effect_sound`) requires a **resource-enforcing rule upgrade** (Torczon-faithful:
`vvar` grade-one-at-x, `ret`/`app` scale+add). Decision: **Path B** (do the
upgrade, don't weaken the lemma). Recorded as **Q10 (active)**; sequences
**Q3** (context rep → Finsupp grade-vec + type ctx) first.

- **Lean toolchain v4.30.0** (Mathlib matching). Build green: **729/729**.
- **Module split**: Spec.lean → Core / Mult / Syntax / Operational / LR /
  Compile / Spec (PRD). Each module owns its definitions; Spec.lean is the
  frozen theorem-statement manifest.
- **Loogle** added as `lake require` —
  `nix develop --command lake exe loogle "?n + 0 = ?n"` for Mathlib type
  search.
- **`tools/eval.sh`** — submit Lean snippet via stdin (with `import Bang;
  open Bang` prepended), get elaborator output. Programmatic Lean for agents
  without an MCP bridge.
- **`tools/check.sh [FILE]`** — fast per-file error check.
- **`tools/burndown.sh`** — Phase B burndown chart per module.
- **`.editorconfig`** + **`.vscode/`** + **pre-commit hook** + **dev-env
  rationale** (Nix manages elan only — never Lean itself — so Mathlib's
  olean cache stays live).
- **Tactics survey** (`docs/notes/tactics-survey.md`) — `grind`, `iris-lean`,
  custom aesop rule sets recommended for Phase B.

### Codebase merge (2026-06-21)

- `bang-lang-wasmfx/` merged into root Lean project; `effectrow-oracle/`
  flattened to root per standard Lean conventions.
- **Deleted**: TS differential harness, F* alternate, `Bang/EvalJson.lean`,
  `effectrow-oracle/oracle-lean/Main.lean`.
- **ADR-0018** (effect-row lacks-constraints) extracted from wasmfx ADR.

### Phase A part 2 (2026-06-21)

Spec.lean axioms **44 → 36** (8 closed):

| Closed | How |
|---|---|
| `Val.subst` / `Comp.subst` / `Handler.subst` | concrete mutual structural recursion |
| `Ctx.scale`, `Ctx.add` | concrete (List-based; `Mult.*` arithmetic) |
| `isReturn` | concrete pattern-match on `Comp.ret` |
| `HasVTy`, `HasCTy` | mutual inductive Props (4 + 6 typing rules) |
| `Source.step` | substitution-based small-step, sizeOf-terminating |
| `Source.eval` | fuel-iterated step |
| `Disjoint` | `_root_.Disjoint` from Mathlib (post-Q1, Lattice + OrderBot) |

**Q1 resolved (option a)**: Eff algebra switched from `[Semiring Eff]` to
`[Lattice Eff] [OrderBot Eff]`. Concrete instance:
`Bang.EffRow := Finset Label` (in `Bang/EffectRow.lean`). Operator changes:
`0` → `⊥`, `+` → `⊔`, `l * e` → `l ⊔ e` in `no_accidental_handling`.

**Q2 resolved**: `Mult` concretized as `Bang.QTT = {zero, one, omega}` with
`CommSemiring` instance (`Bang/Mult.lean`). All Semiring laws via case
analysis. Spec stays parametric in `[Semiring Mult]`; QTT is the default.

**Operational-side headline theorems** (subst_value, preservation, progress,
type_safety) now have CLEAN axiom sets: only `sorryAx` + the kernel-trusted
three (propext, Classical.choice, Quot.sound). Proof bodies are the only
remaining gap → Phase B PROOF_ORDER #4 (STD block).

## Product definition

**`docs/PRD.md`** is now the canonical product doc (2026-06-22 product zoom-out). bang-lang is the
**LANGUAGE** (verified, multi-paradigm, own-surface — convergence decision B); audience = human + agent
developers ("safe to generate into"); moat = proof-by-construction; north-star golden test = a verified
OS (xv6; seL4/CertiKOS lineage). v1 MVP = imperative/State + STM. The **surface is pulled forward** as a
product spine (PRD §7) parallel to the verification spine — see ROADMAP.md "Product spine".

## Active paths

- **`paths/PATH-tracer-bullet.md`** — ⭐ **the recommended next work** (product spine, PRD §7). Thin
  end-to-end: surface → graded-CBPV `Comp` → `Source.eval` → a VALUE. Makes the language RUN; de-risks
  the surface→kernel lowering. READY, not started. Pure + throws only (State deferred, Q12). Additive —
  must not touch the verification spine.
- **`paths/PATH-calcvm-port.md`** — ◊3 (verification spine). Collapse the K3 Calc* matrix into one
  graded-CBPV calculated machine. SCOPED; D1=A decided (calculate from a denotational `evalD`, prove
  `evalD ≡ Source.eval`). Tasks #16–#20.
- **`paths/PATH-graded-cbpv-eval.md`** — graded CBPV kernel. Status: **◊2 GATE MET** — STD block +
  `no_accidental_handling` axiom-clean over the CK machine (ADR-0023/0024). Residual: `effect_sound`
  (Q14), `zero_usage_erasable` (→◊4).

## Next stable checkpoint we are paving toward

**◊3 — CalcVM ported.** (◊2 gate met 2026-06-22; see Position block.)

Definition of stable per `ROADMAP.md`: the Calc* machines collapsed into one
graded-CBPV calculated machine (Bahr-Hutton); `exec ∘ compile ≡ eval` proven;
single unified `Calc.lean` sorry-free; unified diff-test green. Input: the K3
work (`docs/notes/k3-historical-status.md`) + the now-proven graded-CBPV kernel.

**◊2 — Kernel frozen v1 — GATE MET.** `Source.eval` concrete over the CK machine
(ADR-0023); row algebra with lacks-constraints (`WfInst`, ADR-0024 D3);
`no_accidental_handling` proven 0-axiom (ADR-0024 D2). The whole STD block
(`subst_value`/`preservation`/`progress`/`type_safety`) is axiom-clean over the
machine, true for effectful programs. NON-gate residual: `effect_sound` (trace
semantics, Q14), `zero_usage_erasable` (→◊4). NOTE the grade-vec carrier is
positional `List Mult` (ADR-0020), NOT the Finsupp of ADR-0019.

## Outstanding for full ◊2 closure

```
DONE — Path B rule upgrade (Q10/Q3, ADR-0019):
[x] Q3: context representation → Finsupp GradeVec + ambient TyCtx (ADR-0019)
[x] CTy.arr carries argument multiplicity (`arr q A B`)
[x] Re-shape HasVTy/HasCTy to thread + ENFORCE grades (Torczon-faithful)
    landed in Syntax.lean (defs) + Spec.lean + Compat.lean (statements); build green

DONE — de Bruijn rewrite (ADR-0020, `5bcc469`) + first STD theorem:
[x] Core/Operational/Syntax/Spec rewritten to de Bruijn; 5 side-conditions GONE
[x] subst_value PROVEN (`e00ee9a`) — axiom-clean, zero sorry; List carrier held
    (length_eq lemma; no Fin n fallback). Machinery in Bang/Metatheory.lean.

DONE — STD block (ADR-0021, `Bang/Metatheory.lean` §E):
[x] preservation — step-inversion lemmas + subst_value; the β cases needed the
    ADR-0021 lam-body-effect + CommSemiring fixes to make `e' ≤ e` hold
[x] progress — generalized terminal motive (ret ∨ lam ∨ steps), specialized to F
[x] type_safety — fuel induction over progress(F) + preservation
    ALL axiom-clean {propext, Classical.choice, Quot.sound}; progress: {propext, Quot.sound}

ACTIVE — the harder block (RESUME HERE). Dependency map (2026-06-22 analysis):
unlike the STD block, NONE of these is a clean isolated proof — each is gated on a
deferred design fork, and the `up` rule CASCADES BACK into the just-proven STD block.

[ ] **Q5 — the `up` typing rule** is the foundation: without it NO effectful program
    type-checks, so effect_sound / no_accidental_handling are VACUOUS (no `up` can
    appear in a well-typed body). Needs: opArgTy/opResTy signature mechanism + a
    Label→Eff embedding (`ℓ ∈ φ` works abstractly as `labelEff ℓ ≤ φ`). ⚠ CASCADE:
    adding `up` makes `handle h (up …)` typeable, so preservation's handle head-redex
    cases (throws/state/get/put) — currently VACUOUS because `up` is untypable — must
    be RE-PROVEN, and that forces Q4 (label-removing handle) + Q6 (handler op
    semantics). So Q5 is the head of a coupled arc, not a standalone add.
[ ] no_accidental_handling — needs RowAll/WfInst/HandlesIntended concretized
    NON-vacuously (HandlesIntended must be an operational/trace property, not
    "= Disjoint"); depends on Q5 (operations exist) + Q6 (handler reduction).
    rowinst_requires_disjoint is near-definitional once WfInst carries the constraint.
[ ] effect_sound — Trace=List Label + traceWithin (needs Label→Eff) + Q4 + Q5.
[ ] zero_usage_erasable — LR-flavored: "0-graded ⇒ not forced" is provable in
    substitution semantics only via 0-SCALED-position reasoning, which Torczon proves
    SEMANTICALLY (resource/semtyping.v). Likely belongs to ◊4 (LR), not ◊2.

**ADR-0022** (up rule + EffSig + label-discharging handle) — Units 1+2 landed; **D3
superseded by ADR-0023** (the CK machine). **ADR-0023 (CK machine) — LANDED, axiom-clean**:
[x] **Unit 1 (ADR-0022)**: `EffSig` typeclass in Core.lean. (opArg/opRes now `Option`, ADR-0023 D6.)
[x] **Unit 2 (ADR-0022)**: `up` rule + label-discharging `handleThrows`. preservation axiom-clean.
[x] **CK machine (ADR-0023)**: `Source.step : Config → Option Config` (deep handlers, throws
    discards the captured continuation); op-partial `EffSig` + `labelEff_sep` (D6, closes the Q13
    op-granularity facet the shallow step couldn't); handleThrows answer-type correction.
    preservation/progress/type_safety re-proven axiom-clean OVER THE MACHINE, true for effectful
    programs. Was forced by a machine-checked falsity in ADR-0022 D3 (shallow-step progress).
[ ] **Unit 3**: no_accidental_handling + effect_sound — now NON-vacuous (operations + deep
    handlers real). The ◊2 headline. Needs RowAll/WfInst/HandlesIntended + Trace concretized.
Defer zero_usage_erasable to ◊4 (LR-flavored; Torczon proves it via semtyping.v).
```

## Pending meta-work (not on the critical path)

- **Pass-A paper fetching**: Pass-A complete; Pass-B can be fetched on demand
  (gap list in `references/README.md`).
- **CLAUDE.md playhead table** — still references deleted ADRs 0010-0014 in
  the right column; should cite ADR-0017 (retrospective). Low priority;
  content remains historically accurate.
- **`codebase-maintenance` skill — pending homelab rebuild** (2026-06-22): the
  general skill is committed to homelab source (`c6746bc`, nix-managed) but NOT
  yet materialized — the operator must run `just rebuild` in homelab. AFTER that:
  remove lang-bang's temporary local copy
  `.claude/skills/codebase-maintenance/{SKILL,BOOTSTRAP,REFERENCE}.md` (keep its
  `instances/` derivation) to avoid two copies of the skill. Until rebuild, the
  lang-bang local copy is what makes the skill available here.
- **`tools/check.sh` follow-up**: the grep false-green is fixed (`e00ee9a`), but the
  robust fix is to key off `lake env lean`'s exit code, not grep (drift-proof).

## OPEN_QUESTIONS — design decisions

See `docs/notes/OPEN_QUESTIONS.md` for the full list with options +
revisit signals.

| Q | Topic | Status |
|---|---|---|
| Q1 | Eff algebra (Semiring vs Lattice) | ✓ resolved — Lattice + OrderBot |
| Q2 | Mult = QTT concretization | ✓ resolved — QTT enum + CommSemiring |
| Q3 | Ctx representation (List vs FinMap) | ✓ resolved — ADR-0019: Finsupp grade-vec + ambient TyCtx |
| Q4 | `handle` typing rule refinement | ✓ resolved — F-restriction (ADR-0021) + label-removal (ADR-0022 D4) + answer-type (ADR-0023) |
| Q5 | `up` typing rule + opArgTy/opResTy | ✓ resolved — `up` rule + op-partial `EffSig` (ADR-0022/0023) |
| Q6 | Source.step deep-handler resumption | ◑ throws resolved (ADR-0023 CK machine); state → Q12 |
| Q7 | Op names string vs enum | defer (cosmetic) |
| Q8 | `group_recovers` H-K bridge | Phase B research |
| Q9 | WasmFX target drift | recorded — ◊5 obligation (pin-to-engine) |
| Q10 | Typing rules must enforce grades | rules landed (ADR-0019); proof bodies remain |
| Q12 | Graded state handlers | open — state dispatch deferred (needs reified continuation) |
| Q13 | Op-granularity progress wall | ✓ resolved — CK machine + op-partial sigs (ADR-0023) |

## Subagents available

Project-local subagent definitions in `.claude/agents/`:

- **`kernel-engineer`** — graded-CBPV semantics, effect-row algebra,
  `no_accidental_handling`.
- **`proof-engineer`** — Lean proofs, axiom hygiene, LR machinery.

Three more roles (`compiler-engineer`, `surface-engineer`, `librarian`)
designed but not written — activate when their layer becomes active
(◊4+, ◊5+, on-demand).

## Quick orient for fresh sessions

1. Read `CLAUDE.md` — the primary orientation (invariants, glossary, playhead).
2. Read this file (`CONTEXT.md`) — current position.
3. Read `ROADMAP.md` — the map.
4. Read `docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md` —
   the architecture in force.
5. For proof work: read `docs/notes/spec-proof-discipline.md` (PROOF_ORDER
   + invariants).
6. For deferred design decisions: `docs/notes/OPEN_QUESTIONS.md`.
7. For dev tooling: `docs/notes/dev-env.md`.
8. For Lean tactics: `docs/notes/tactics-survey.md`.
9. Read the active `paths/PATH-*.md` if a path is in flight.
10. Verify locally:
    ```
    nix develop          # dev shell with lean/elan
    just verify          # selfcheck + lake build + tools/audit.sh
    bash tools/burndown.sh   # Phase B burndown chart
    ```

## Update discipline

This file is rewritten when:
- A checkpoint is reached → bump position; archive blocker list
- A new path begins → add to "Active paths"; create `paths/PATH-<slug>.md`
- A path completes → remove from "Active paths"; the seam test is the
  durable record
- Major outstanding work appears or resolves → update blocker list
- A session ends with meaningful state shift → bring the doc current

Do NOT rewrite for: routine commits, in-path progress, casual notes. Those
belong in the active path's `PATH-*.md`.
