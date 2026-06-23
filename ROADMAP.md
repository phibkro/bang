# bang-lang ROADMAP

> **Long-term map of checkpoints and paths.** Stable across sessions; changes
> only at checkpoint boundaries. Read `CONTEXT.md` for current position.
>
> This is the **orchestrator's map** — checkpoints (◊) and the parallel paths
> between them. For the **research-grade keyframes** (what's actually being
> built in each rep), see `docs/roadmap/bang-northstar-roadmap.md`. The two
> abstractions complement each other: keyframes say *what*, this roadmap says
> *when paths can fork*.

## North star

bang-lang is a small effect-typed language whose **paradigm and runtime are
values, not language features**. The contribution is a **verified two-hop
architecture**:

```
  source ─►  graded-CBPV semantics  ─Bahr-Hutton calc─►  CalcVM
                                                            │
                                                            └─Benton-Hur LR─►  WasmFX
```

The CalcVM is the **executable specification** (canonical operational meaning).
The WasmFX backend is the **optimized compiler output**, proven to preserve
contextual equivalence. See ADR-0016 for the architecture commitment.

Success = a runnable bang-lang program compiled to WasmFX, with kernel-checked
proofs that observed behavior equals what the reference semantics says.

## The map

```
                                                                ┌─► Path-Surface
                                                                │   (parser, type-checker, CLI)
                                                                │
[◊1]──►[◊2]──►[◊3]──►[◊4]────────────────────────────────►[◊5]──┼─► Path-Compiler-Optim
 recon  kernel  Calc  LR    compile_forward_sim                 │   (effect-specific lowerings,
 ✓     gate✓  ported       for trivial fragment                 │    dead-code, zero-grade erasure)
        (v1)   to graded                                        │
               CBPV                                             └─► Path-Kernel-Extensions
                                                                    (multi-shot, STM, cost grading)
                                                                                          │
                                                                                          ▼
        │                                                                              [◊6] ── release v0
        │
        │ ◊ = stable checkpoint (road may diverge here into parallel paths)
        │ ─►= linear segment (one path at a time; paths would tangle if forked)
```

## Checkpoints

| ◊ | Name | Definition of stable | Gate test |
|---|---|---|---|
| ◊1 | **Reconciliation landed** | ADR-0016 committed; obsolete ADRs deleted; reference library + project-orientation docs exist | `ls docs/decisions/0016*` + `ls references/` succeed |
| ◊2 | **Kernel frozen v1** · **gate ✓ (2026-06-22)** | Graded-CBPV `Source.eval` concrete (no `opaque`); row algebra extended with lacks-constraints; `no_accidental_handling` proven | ✅ gate met: `Source.eval` concrete (CK machine, ADR-0023); lacks-constraints (`WfInst`); `no_accidental_handling` proven 0-axiom (ADR-0024); `just verify` green. Residual (non-gate): `effect_sound` (trace semantics, Q14), `zero_usage_erasable` (→◊4) |
| ◊3 | **CalcVM ported** · **gate ✓ (2026-06-23)** | Calc* machines collapsed into one graded-CBPV calculated machine; `exec ∘ compile ≡ eval` still proven | ✅ gate met: unified `Bang/CalcVM.lean` (pure CBPV + deep handlers/throws + resumptive state + transaction + ADT elims), `compile_correct`/`evalD_agrees_source`/`sim`/`run_evalD` axiom-clean ⊆ {propext, Classical.choice, Quot.sound}; K2 matrix (8 Calc* + Eval) archived → `archive/` (ADR-0017); 16-case 5-axis diff-test battery (`Agree`, all `rfl`, 0-axiom) green; `just verify` 723 jobs. ◊2 gate held 0-axiom throughout |
| ◊4 | **LR foundation (non-▷ fragment)** · **gate ✓ scoped (2026-06-24, ADR-0039)** | `lr_fundamental` proven for the **non-▷ fragment** (pure CBPV · functions · non-recursive ADTs · throws); the cohesive **▷-subsystem** (μ fold/unfold · `up` · resumptive state/txn handlers) → **◊4.5**. (`group_recovers` RETIRED — ADR-0032.) | ✅ scoped gate met: `lr_fundamental` reads the real proof, `sorryAx` ONLY from the documented ▷-subsystem; ◊2 (`no_accidental_handling` 0-axiom, STD trusted-three) + ◊3 (CalcVM trusted-three) held; arrow clause = peeling+F-restriction (ADR-0038), closed-value carrier (ADR-0036). `lr_sound_closed` (F-typed) proven; `lr_sound`(arbitrary-C)/`zero_usage` → ◊4.5. `effect_sound` (Q14) → ◊5 |
| ◊4.5 | **LR ▷-subsystem** | Re-phrase `Crel`/`Krel`/`Srel` with the **IxFree `∀k≤n` Kripke-monotone** reading; close μ fold/unfold + `up` + resumptive handlers (state/txn) + `krel_refl` / `lr_sound`(arbitrary-C) / `zero_usage_erasable`. Build-confirmed necessary (ADR-0039); plain-Nat relations lack the both-ways monotonicity μ/resume need | `Audit.lean`: `lr_fundamental` / `lr_sound` / `zero_usage_erasable` axioms ⊆ {propext, Classical.choice, Quot.sound} (`sorryAx` gone). `crel_unfold(a)` / `krel_appF_intro` / all infra carry over from ◊4 |
| ◊5 | **Compiler v0** | `compile_forward_sim` proven for a trivial fragment; WasmFX module type concrete | Round-trip test by fragment (corrected 2026-06-23, ADR-0035/0036 recon): **pure-arith** `.bang` → ANY engine incl. wasm3; **one-handler** `.bang` → **Wasmtime** `Config::wasm_stack_switching` (x86-64; wasm3 has NO stack-switching). Pick a **suspend/resume** effect (state/generator) for the tracer, NOT `throws` — `throws` lowers to `resume_throw`, unlanded in Wasmtime (#10248). Same value as `Source.eval`. |
| ◊6 | **Release v0** | Three parallel paths from ◊5 converged into a releasable artifact | Public release tag + paper drafts for the three theorems (`lr_fundamental`, `compile_forward_sim`, `group_recovers`/its resolution) |

## Product spine — pulled forward (PRD §7)

`docs/PRD.md` settles that bang-lang is the **language** (not the methodology) and that lang-bang
grows its **own surface** (convergence decision B). That makes the surface the product *spine*, not a
◊5 deferral. So a **thin surface tracer bullet** runs as an **early parallel track** alongside the
verification spine:

```
verification spine:   ◊2 ✓ ──► ◊3 CalcVM ──► ◊4 LR ──► ◊5 compiler ──► ◊6
                                  (backbone — proof rides the reference)
product spine (NEW):  [tracer bullet ✓] ─► thin surface ✓ ─► multi-paradigm MVP (v1) ✓
                       minimal parser → graded-CBPV Comp → Source.eval → a VALUE
                       ✓✓ v1 MVP SPINE COMPLETE (rungs 0–4, 2026-06-23): State · STM ·
                          reactive · user-types on one verified kernel — see CONTEXT.md
```

The tracer bullet is the first product-spine issue (`paths/PATH-tracer-bullet.md`). It de-risks the
surface→kernel lowering — the biggest product unknown — and makes the language *run* before ◊5. The
full end-to-end (surface → CalcVM → WasmFX → engine) thickens as the verification spine reaches it.

This is the **one sanctioned exception** to "linear segments admit no parallelism" below: the product
spine is a *different layer* (surface) from the verification spine (kernel/compiler), so per rule 2
(cross-layer paths run in parallel freely) it does not tangle the ◊-march.

## The layer × path model

Three layers stack vertically. Each layer has its own **invariant discipline**
and its own **cadence**.

```
┌─ SURFACE LAYER ─ liquid ──────────────────────────────────────┐
│   parser · syntax · IDE · errors                              │
│   no theorems; iterate freely; throw it away                  │
│   commits don't need ADRs                                     │
│   cadence: hours                                              │
└──────────────────┬────────────────────────────────────────────┘
                   │ SEAM: typed AST contract
┌──────────────────┴ COMPILER LAYER ─ evolving ─────────────────┐
│   graded-CBPV  ─Bahr-Hutton→  CalcVM  ─Benton-Hur→  WasmFX    │
│   theorems: type safety, lr_fundamental, compile_forward_sim  │
│   optimizations welcome; must preserve preceding theorem      │
│   cadence: days                                               │
└──────────────────┬────────────────────────────────────────────┘
                   │ SEAM: WasmFX module + handler protocol
┌──────────────────┴ KERNEL LAYER ─ frozen ─────────────────────┐
│   graded-CBPV reference + effect-row algebra                  │
│   theorems: unifier sound, no_accidental_handling             │
│   THE DEFINITION of what a bang-lang program means            │
│   changes require a K-ADR + re-validation downstream          │
│   cadence: weeks                                              │
└───────────────────────────────────────────────────────────────┘
```

## The vertical principle — correctness above, performance below (ADR-0037)

The vertical stack is not just decomposition; it encodes a **contract**:

```
  ABSTRACT layer (above a seam)  ─ fights for CORRECTNESS  (strong invariants, provability)
        │  seam = the contract (observable behaviour = the layer-above's semantics)
  IMPL layer (below a seam)      ─ fights for PERFORMANCE  (rewrite freely, BOUND by the seam)
```

Each **seam IS that contract** — the typed-AST seam, the WasmFX-module + handler-protocol seam. The
preserving theorem at each (`type_safety`, `lr_fundamental`, `compile_forward_sim`) is what **forbids
the implementation from assuming an invariant the layer above does not actually prove** — the
miscompilation guardrail.

**Corollary — constraints are generative:** every invariant *proven* in the layer above is one the
layer below gets to *assume* instead of *check*, so the deleted dynamic check **is** the performance.
Correctness and performance are **one ledger viewed from two sides** (instanced: QTT grade-0 → no code;
effect rows → no dynamic dispatch; linearity → no GC; shared-nothing → no Iris + no locking). Invariant
#7 ("performance second-class") is this principle's near-term face: we don't chase speed directly — we
**earn** it by proving invariants upstream. Full treatment + the shared-nothing concurrency instance:
ADR-0037.

## Parallelism rules

1. **One path per layer at a time.** Two paths in the same layer touch the
   same files → they tangle. Sequence them, or split one off.
2. **Cross-layer paths run in parallel freely** — that's what seams are for.
   The typed contract at each seam is the synchronization point.
3. **No path crosses ◊ without re-aligning.** When a path reaches its target
   checkpoint, `CONTEXT.md` updates and any other paths must re-anchor to
   the new state before continuing.
4. **Linear segments (◊1 → ◊2 → ◊3 → ◊4) admit no parallelism.** The
   architecture changes propagate too widely; forking before ◊5 risks
   reworking the same code in two paths.

## Paths from ◊5 (the first real fork)

```
◊5 ──► PATH-compiler-optim     ─ owner: compiler-engineer
   │   (effect-specific lowerings, dead-code, zero-grade erasure)
   │
   ├──► PATH-kernel-extensions ─ owner: kernel-engineer + proof-engineer
   │   (multi-shot handlers, STM, cost grading)
   │
   └──► PATH-surface-v0        ─ owner: surface-engineer
       (parser, type-checker, CLI, error messages)
```

## What's frozen vs liquid

| | Frozen | Liquid |
|---|---|---|
| **Kernel layer** | rows-as-sets · five primitives · graded-CBPV substrate · calculation-as-method | proof-body internals · helper lemmas |
| **Compiler layer** | two-hop architecture · WasmFX as target · LR as correctness notion | individual machine designs · optimization strategies |
| **Surface layer** | AST seam contract | EVERYTHING ELSE — syntax · glyphs · error formats · CLI shape |

Frozen things change only via K-ADR + downstream re-validation. Liquid things
change without ceremony.

## The repo layout

```
lang-bang/                  ← project root (Lean 4 conventions)
├── lakefile.toml           ← Lean project config (library: Bang)
├── lean-toolchain          ← pinned Lean version
├── lake-manifest.json      ← dependency lock (Mathlib + plausible)
├── flake.nix .envrc        ← Nix dev shell
├── Makefile                ← just verify | build | audit | selfcheck | clean
├── Bang/                   ← the Lean library
│   ├── EffectRow.lean      ← row algebra + sound unifier (K1)
│   ├── Eval.lean           ← reference interpreter (K2/K3) — graded-CBPV port at ◊2
│   ├── Calc*.lean          ← K3 calculated machines (collapsing into one at ◊3; see ADR-0017)
│   ├── Spec.lean           ← wasmfx spec (graded-CBPV + LR + WasmFX target)
│   ├── Compat.lean         ← per-rule compatibility lemmas (Phase B targets)
│   ├── Audit.lean          ← #print axioms gate
│   └── Distribution.lean   ← semilattice / CALM asset (flagged conjecture)
├── tools/
│   ├── audit.sh            ← static cheats grep + lake build
│   └── selfcheck.mjs       ← zero-dep Node smoke for the row unifier
│
├── ROADMAP.md              ← this file (stable, the map)
├── CONTEXT.md              ← volatile, current position on the map
├── README.md               ← human-facing intro
├── CLAUDE.md               ← agent-facing read-first orientation
├── paths/
│   ├── _template.md        ← per-path doc template
│   └── PATH-<slug>.md      ← one per active path
├── docs/
│   ├── decisions/          ← ADRs (governance) — taxonomy: K / C / S
│   ├── spec/               ← language spec
│   ├── roadmap/            ← K-keyframe research roadmap (complementary view)
│   └── notes/              ← reading notes, design discipline
│       ├── spec-proof-discipline.md   ← PROOF_ORDER + invariants for proof work
│       ├── spec-handover.md           ← thin-interface framing
│       └── k2-calculation-playbook.md ← calculation proof patterns
├── references/             ← cited papers + refs.bib + index
└── .claude/agents/         ← domain-specific subagent definitions
    ├── kernel-engineer.md
    └── proof-engineer.md   ← (compiler / surface / librarian: defined on activation)
```

**Amnesiac team model**: a fresh agent reads `CLAUDE.md` → `CONTEXT.md` →
`paths/PATH-<active>.md` and has enough context to continue. `ROADMAP.md` is
slow background. Memory is the index; files are the substance.

## ADR taxonomy

Future ADRs are tagged by layer for cull discipline:
- **K-ADR** (kernel): semantic decisions; near-permanent; deep review
- **C-ADR** (compiler): methodology decisions; stable statements, evolving impl
- **S-ADR** (surface): experimental; expected to churn; cheap to write/delete

S-ADRs may be deleted outright when superseded. K-ADRs are superseded but
preserved. C-ADRs are case-by-case.

## When to update this file

- Reaching a checkpoint (mark ◊ as ✓; advance the "current" cursor)
- Adding a new path or layer
- Changing a checkpoint definition (rare; treat as architecture change)
- A K-ADR lands that affects the architecture diagram

Everything else goes in `CONTEXT.md`.
