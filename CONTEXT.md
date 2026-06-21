# bang-lang CONTEXT

> Where we are on the map RIGHT NOW. Volatile. Updated as paths complete and
> new ones begin. **Read this first on every fresh session**, after `CLAUDE.md`.
>
> For the long-term map, see `ROADMAP.md`. For research-grade keyframes, see
> `docs/roadmap/bang-northstar-roadmap.md`.

## Position

```
◊1 ✓ Reconciliation landed       ── 2026-06-20
◊2   Kernel frozen v1            ── CURRENT TARGET
◊3   CalcVM ported
◊4   LR foundation
◊5   Compiler v0
◊6   Release v0
```

## Most recent stable checkpoint

**◊1 — Reconciliation landed (2026-06-20)**

What changed:
- **ADR-0016** committed (`docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md`) — establishes the two-hop architecture: graded-CBPV semantics → CalcVM (Bahr-Hutton) → WasmFX (Benton-Hur LR).
- **ADRs 0003 (own-the-runtime) and 0004 (calculated-vm-canonical) deleted** — subsumed by 0016, not just superseded.
- **ADR-0015** annotated: CalcReifySim bisimulation is **paused** (LR subsumes the goal); the machine itself stays.
- **`references/`** scaffolded — 11 on-disk papers organized into 8 topical subdirs, `refs.bib` seeded, README cataloging present + gaps (Pass A urgent, Pass B on-demand).
- **`ROADMAP.md`, `CONTEXT.md`, `paths/`** scaffolded — the orchestrator-layer doc system.

## Subsequent landings since ◊1 (housekeeping; not a new checkpoint)

**Dev-env upgrades (2026-06-21):**
- **Lean toolchain bumped to v4.30.0** (was v4.29.0); Mathlib bumped to
  matching v4.30.0. Build green: 723/723 jobs.
- **Loogle added** as a `lake require` — `nix develop --command lake exe loogle "..."`
  for Mathlib type-signature search. Now compatible with our toolchain.
- **tools/eval.sh** — submit Lean snippet via stdin, get elaborator output
  (with `import Bang; open Bang` prepended). Programmatic Lean access for
  agents / scripts without an MCP bridge.
- **Dev-env architecture** recorded in `docs/notes/dev-env.md`: Nix manages
  elan + system deps; elan fetches the official Lean toolchain; Mathlib's
  cache keys to that hash and stays live. (If Nix built Lean itself, the
  hash would diverge and the cache would miss — multi-GB recompiles.)



**Codebase merge & restructure (2026-06-21):**
- `bang-lang-wasmfx/` merged into the root Lean project, then deleted. Its `.lean` files moved into `Bang/` (now `Bang/Spec.lean`, `Bang/Compat.lean`, `Bang/Audit.lean`, `Bang/Distribution.lean`). `audit.sh` moved to `tools/audit.sh`.
- `effectrow-oracle/` flattened to project root. `Bang/` is now at root; `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `flake.nix`, `flake.lock`, `.envrc`, `Makefile` all live at root per standard Lean 4 conventions.
- **Deleted:** the TS differential harness (`effectrow-oracle/harness/`), the F\* alternate (`effectrow-oracle/oracle/`), `Bang/EvalJson.lean` (harness IPC bridge), `effectrow-oracle/oracle-lean/Main.lean` (harness exe entry).
- **ADR-0018** extracted from `bang-lang-wasmfx/ADR-effect-row-algebra.md` — formal record of the lacks-constraint extension to the row algebra.
- **`docs/notes/spec-proof-discipline.md`** extracted from wasmfx CLAUDE.md — canonical source of PROOF_ORDER + hard invariants for proof work.
- **`docs/notes/spec-handover.md`** extracted from wasmfx README.md — preserves the thin-interface framing.
- Subagent files (`kernel-engineer`, `proof-engineer`) refreshed for new paths.

**Why retire the TS harness now?** The eight per-machine harness tests (`calc-*.test.ts`) were testing machines that collapse into one graded-CBPV machine at ◊3 (per ADR-0017). The harness was already going to need a rewrite; better to remove the dead weight than maintain it through the refactor. Diff-testing returns when there's a unified graded-CBPV machine to test against (post-◊3).

## Active paths

- **`paths/PATH-graded-cbpv-eval.md`** — refactor toward graded CBPV. Owner:
  claude as kernel-engineer. Status: **Phase A part 2 well underway**.
  Spec.lean now split across 6 modules (Core, Mult, Syntax, Operational,
  LR, Compile + Spec PRD). Spec.lean axioms 44 → 37 (subst, Ctx ops,
  isReturn, HasVTy, HasCTy, Source.step, Source.eval all concrete);
  Mult = QTT concrete (closes Q2). Operational theorems (preservation,
  progress, type_safety, subst_value) have CLEAN axiom sets (only
  `sorryAx` + kernel axioms). Remaining for ◊2: Q1 Eff algebra design
  question (Semiring vs Lattice — see OPEN_QUESTIONS.md), then row
  well-formedness theorems. Build green: 729/729.

## Next stable checkpoint we are paving toward

**◊2 — Kernel frozen v1.**

Definition of stable: graded-CBPV `Source.eval` concrete (no `opaque` in
`Spec.lean §0–§4`); row algebra extended with lacks-constrained quantifiers;
`no_accidental_handling` proven; existing K1 unifier proofs still green;
existing K2/K3 diff-tests still green on the un-graded subset.

## Outstanding blockers for ◊2

```
[ ] Eval.lean refactor to graded CBPV
    (value/computation split made explicit; multiplicity grades added)
    — paired with regression diff-test against existing Eval on the
      all-ω subset (must be identical behavior)

[ ] EffectRow.lean: add lacks-constraints to quantifiers
    — the soundness obligation the existing unifier doesn't yet surface

[ ] State + prove no_accidental_handling
    — currently schematic in Spec.lean §0.5

[ ] Spec.lean §0–§4: replace opaques with concrete definitions
    backed by the refactored Eval + extended EffectRow
```

These are kernel-layer linear work — must sequence; cannot parallelize.

## Pending meta-work (not on the critical path)

- **Pass-A paper fetching**: 6 papers (Benton-Hur, Ahmed, Pitts,
  Plotkin-Pretnar ESOP'09, Katsumata POPL'14, CakeML POPL'14) — deferred
  until they're actually being cited; gap list lives in
  `references/README.md`.

## Subagents available

Project-local subagent definitions in `.claude/agents/`:

- **`kernel-engineer`** — graded-CBPV semantics, effect-row algebra,
  no_accidental_handling
- **`proof-engineer`** — Lean proofs, axiom hygiene, LR machinery

Three more roles (`compiler-engineer`, `surface-engineer`, `librarian`) are
*designed but not written* — they activate when their layer becomes active
(◊4+, ◊5+, on-demand respectively). Don't pre-write subagents whose layer
isn't active yet — same anti-pattern as designing for hypothetical futures.

## Quick orient for fresh sessions

1. Read `CLAUDE.md` — the primary orientation (invariants, glossary, playhead).
2. Read this file (`CONTEXT.md`) — current position.
3. Read `ROADMAP.md` — the map.
4. Read `docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md` —
   the architecture in force.
5. Read the relevant `paths/PATH-*.md` if a path is active.
6. For proof work: read `docs/notes/spec-proof-discipline.md` (PROOF_ORDER + invariants).
7. Verify locally:
   ```
   nix develop          # dev shell with lean/elan
   make verify          # selfcheck + lake build + tools/audit.sh
   ```

## Update discipline

This file is rewritten when:
- A checkpoint is reached → bump position; archive blocker list
- A new path begins → add to "Active paths"; create `paths/PATH-<slug>.md`
- A path completes → remove from "Active paths"; the seam test is the durable record
- Major outstanding work appears or resolves → update blocker list

Do NOT rewrite for: routine commits, in-path progress, casual notes. Those
belong in the active path's `PATH-*.md`.
