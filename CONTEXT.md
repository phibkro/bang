# bang-lang CONTEXT

> Where we are on the map RIGHT NOW. Volatile. Updated as paths complete and
> new ones begin. **Read this first on every fresh session**, after `CLAUDE.md`.
>
> For the long-term map, see `ROADMAP.md`. For research-grade keyframes, see
> `docs/roadmap/bang-northstar-roadmap.md`.

## Position

```
◊1 ✓ Reconciliation landed        ── 2026-06-20
◊2   Kernel frozen v1             ── IN PROGRESS. De Bruijn rewrite landed
                                     (ADR-0020; the named encoding cost 5
                                     side-conditions / 4 machine-checked falsities).
                                     ✓✓ WHOLE STD BLOCK PROVEN on the de Bruijn base
                                     (2026-06-22): subst_value → preservation →
                                     progress → type_safety, ALL axiom-clean
                                     {propext, Classical.choice, Quot.sound}, zero
                                     sorry. Proving preservation EXPOSED 4 typing-rule
                                     divergences from Torczon (ADR-0021): lam dropped
                                     the body effect (made β-preservation false);
                                     handle over non-F bodies broke progress; Mult
                                     needed CommSemiring for the letC grade reshape;
                                     progress is false at general B. All corrected.
                                     NEXT: the harder block — no_accidental_handling
                                     + effect_sound + zero_usage_erasable (needs
                                     RowAll/WfInst/HandlesIntended + Trace concrete).
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

## Active paths

- **`paths/PATH-graded-cbpv-eval.md`** — graded CBPV kernel.
  Owner: claude as kernel-engineer. Status: **STD block COMPLETE**. de Bruijn
  (ADR-0020) dissolved the 5 named side-conditions; `subst_value` closed clean
  (`e00ee9a`); then `preservation → progress → type_safety` all closed axiom-clean
  (2026-06-22), after ADR-0021 corrected 4 Torczon-divergent typing rules that
  preservation exposed (lam body-effect, handle F-restriction, CommSemiring Mult,
  progress-at-F). Proof machinery in `Bang/Metatheory.lean` (subst_gen + step
  inversion lemmas + the three STD proofs). **NEXT: the harder block** — concretize
  RowAll/WfInst/HandlesIntended + Trace, then no_accidental_handling / effect_sound
  / zero_usage_erasable.

## Next stable checkpoint we are paving toward

**◊2 — Kernel frozen v1.**

Definition of stable per `ROADMAP.md`: graded-CBPV `Source.eval` concrete
(no `opaque`/axiom in `Bang/Spec.lean §0–§4`); row algebra with lacks-
constrained quantifiers; `no_accidental_handling` proven.

Current ◊2 status: rules enforce grades (ADR-0019), the representation is de
Bruijn (ADR-0020), the rules are Torczon-faithful on effects+grades (ADR-0021),
and **the entire STD block is proven** — `subst_value`, `preservation`,
`progress`, `type_safety`, all axiom-clean. The remaining gate is the harder
block (no_accidental_handling, effect_sound, zero_usage_erasable) which needs the
row-quantifier mechanism (RowAll/WfInst/HandlesIntended) and a concrete Trace.
NOTE the grade-vec carrier is now positional `List Mult` (ADR-0020), NOT the
Finsupp of ADR-0019 — earlier prose mentioning Finsupp grade-vectors is superseded.

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

ACTIVE — the harder block (RESUME HERE):
[ ] RowAll, WfInst, HandlesIntended — concretize (lacks-quantifier mechanism)
    + prove rowinst_requires_disjoint, no_accidental_handling
[ ] Concretize Trace + Source.evalTrace + traceWithin (now possible
    with Lattice Eff: a Trace is a List Label; traceWithin is ⊆ semantics)
[ ] Concretize NotEvaluated semantically via Source.step reachability
[ ] zero_usage_erasable / effect_sound — unblocked only AFTER the Q10 upgrade
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
| Q4 | `handle` typing rule refinement | partial — F-type restriction landed (ADR-0021); label-removing rule still deferred (effect_sound will force it) |
| Q5 | `up` typing rule + opArgTy/opResTy | revisit |
| Q6 | Source.step deep-handler resumption | defer until tests demand |
| Q7 | Op names string vs enum | defer (cosmetic) |
| Q8 | `group_recovers` H-K bridge | Phase B research |
| Q9 | WasmFX target drift | recorded — ◊5 obligation (pin-to-engine) |
| Q10 | Typing rules must enforce grades | rules landed (ADR-0019); proof bodies remain |

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
