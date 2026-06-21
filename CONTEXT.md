# bang-lang CONTEXT

> Where we are on the map RIGHT NOW. Volatile. Updated as paths complete and
> new ones begin. **Read this first on every fresh session**, after `CLAUDE.md`.
>
> For the long-term map, see `ROADMAP.md`. For research-grade keyframes, see
> `docs/roadmap/bang-northstar-roadmap.md`.

## Position

```
◊1 ✓ Reconciliation landed        ── 2026-06-20
◊2   Kernel frozen v1             ── IN PROGRESS — NOT as close as it looked.
                                     Typing rules carry grades but don't ENFORCE
                                     them; the grade-soundness theorems (and a
                                     real subst_value) need a resource-enforcing
                                     rule upgrade first (Q10, active).
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
  Owner: claude as kernel-engineer. Status: **Phase B started — Path B
  (resource-enforcing rule upgrade)**. Definitions concrete; `subst_value`
  reframed to the real graded lemma (sorry); next is the Q3-a context-rep ADR
  then re-shaping the typing judgments to enforce grades (Q10).

## Next stable checkpoint we are paving toward

**◊2 — Kernel frozen v1.**

Definition of stable per `ROADMAP.md`: graded-CBPV `Source.eval` concrete
(no `opaque`/axiom in `Bang/Spec.lean §0–§4`); row algebra with lacks-
constrained quantifiers; `no_accidental_handling` proven.

Current ◊2 status: syntactic definitions are done, but the **typing rules are
grade-insensitive** — the STD proofs are NOT mechanical (a prior reading of this
doc that called them so was wrong). The gate is a resource-enforcing rule
upgrade (Q10).

## Outstanding for full ◊2 closure

```
ACTIVE — Path B rewrite (Q10), sequenced:
[ ] Q3: resolve context representation → Finsupp grade-vec + type ctx (ADR)
[ ] Re-shape HasVTy/HasCTy to thread + ENFORCE grades (Torczon-faithful)
    blast radius: Syntax.lean (defs) + Spec.lean + Compat.lean (statements)
[ ] Prove subst_value (graded), then preservation / progress / type_safety
    (STD block — now reachable once rules enforce grades; watch Q4 in preservation)

STILL DEFERRED (harder block):
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

## OPEN_QUESTIONS — design decisions

See `docs/notes/OPEN_QUESTIONS.md` for the full list with options +
revisit signals.

| Q | Topic | Status |
|---|---|---|
| Q1 | Eff algebra (Semiring vs Lattice) | ✓ resolved — Lattice + OrderBot |
| Q2 | Mult = QTT concretization | ✓ resolved — QTT enum + CommSemiring |
| Q3 | Ctx representation (List vs FinMap) | **ACTIVE** — forced by Q10; → Finsupp grade-vec + type ctx |
| Q4 | `handle` typing rule refinement | revisit (will surface in preservation) |
| Q5 | `up` typing rule + opArgTy/opResTy | revisit |
| Q6 | Source.step deep-handler resumption | defer until tests demand |
| Q7 | Op names string vs enum | defer (cosmetic) |
| Q8 | `group_recovers` H-K bridge | Phase B research |
| Q9 | WasmFX target drift | recorded — ◊5 obligation (pin-to-engine) |
| Q10 | Typing rules must enforce grades | **ACTIVE** — the live ◊2 task (Path B) |

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
