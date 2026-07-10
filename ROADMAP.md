# bang-lang ROADMAP

> **Long-term map of checkpoints and paths.** Stable across sessions; changes
> only at checkpoint boundaries. Read `CONTEXT.md` for current position.
>
> This is the **orchestrator's map** — checkpoints (◊) and the parallel paths
> between them. For the **research-grade keyframes** (what's actually being
> built in each rep), see `docs/roadmap/bang-northstar-roadmap.md`. The two
> abstractions complement each other: keyframes say *what*, this roadmap says
> *when paths can fork*.
>
> For the **PRODUCT axis** — real programs as checkpoints and the features each
> one pulls into existence (a demand-driven dependency DAG that grounds features
> in the projects that need them), see `docs/roadmap/project-roadmap.md`. This
> ◊-map answers *"is it correct?"*; that one answers *"what can you build, and
> why that feature next?"*

## North star

bang-lang is a small effect-typed language whose **paradigm and runtime are
values, not language features**. The contribution is a **verified two-hop
architecture** (ADR-0016 as revised by ADR-0059):

```
  source ─►  graded-CBPV semantics  ─Bahr-Hutton calc─►  CalcVM
                                                            │
                                                            └─annotated fwd-sim─►  Wasm 3.0
                                                               (grade-directed lowering)
```

The CalcVM is the **executable specification** (canonical operational meaning).
**Wasm 3.0 is the verified compiler target** (ADR-0059): grade-directed
lowering — pure→native, abort→exceptions, tail→direct call, general→the
GC-frame-chain runtime; WasmFX `switch`/`resume` is the one pluggable fast-path
slot once it standardizes (stack switching did NOT land in Wasm 3.0). The hop
is proven by annotated forward simulation (`compile_forward_sim`, ADR-0035);
the binary LR (◊4) is the separate contextual-equivalence theorem.

Success = a runnable bang-lang program compiled to Wasm 3.0, **executed on a
real engine**, with kernel-checked proofs that observed behavior equals what
the reference semantics says. (As of 2026-07-10 the proof half is met and the
real-engine half is not — that asymmetry is what ◊5.5 exists to close.)

## The map

```
[◊1]──►[◊2]──►[◊3]──►[◊4]──►[◊5]───►[◊5.25]────►[◊5.5]─────►[◊5.75]────►[◊6]──► …v1 (label
 recon  kernel  Calc   LR    fwd-sim  close+demo  EMISSION    compiled     public   deferred —
 ✓      gate✓   ported ✓scoped  ✓     census 18→20  bang build  demo pack   v0.2+    see the
        (v1)    ✓             (proof) sim-KV·IO mock  → .wasm on  in-browser  papers+  research
                                      CTR #87        a real engine  ·xv6 slice  validation ladder)

parallel, cross-layer (rule 2 — these don't tangle the emission spine):
  RESEARCH LADDER (pre-v1, pulled forward — see §Pre-v1 research ladder)
  PLANS BACKLOG   (advisor plans 001–007: tests·dx·hardening — see plans/README.md)

        │ ◊ = stable checkpoint (road may diverge here into parallel paths)
        │ ─►= linear segment (one path at a time; paths would tangle if forked)
```

## Checkpoints

| ◊ | Name | Definition of stable | Gate test |
|---|---|---|---|
| ◊1 | **Reconciliation landed** | ADR-0016 committed; obsolete ADRs deleted; reference library + project-orientation docs exist | `ls docs/decisions/0016*` + `ls references/` succeed |
| ◊2 | **Kernel frozen v1** · **gate ✓ (2026-06-22)** | Graded-CBPV `Source.eval` concrete (no `opaque`); row algebra extended with lacks-constraints; `no_accidental_handling` proven | ✅ gate met: `Source.eval` concrete (CK machine, ADR-0023); lacks-constraints (`WfInst`); `no_accidental_handling` proven 0-axiom (ADR-0024); `just verify` green. Residual (non-gate): `effect_sound` (trace semantics, Q14), `zero_usage_erasable` (→◊4) |
| ◊3 | **CalcVM ported** · **gate ✓ (2026-06-23)** | Calc* machines collapsed into one graded-CBPV calculated machine; `exec ∘ compile ≡ eval` still proven | ✅ gate met: unified `Bang/Backend/AbstractMachine.lean` (pure CBPV + deep handlers/throws + resumptive state + transaction + ADT elims), `compile_correct`/`evalD_agrees_source`/`sim`/`run_evalD` axiom-clean ⊆ {propext, Classical.choice, Quot.sound}; K2 matrix (8 Calc* + Eval) retired to git history (`87d5aeb`, ADR-0017); 16-case 5-axis diff-test battery (`Agree`, all `rfl`, 0-axiom) green; `just verify` 723 jobs. ◊2 gate held 0-axiom throughout |
| ◊4 | **LR foundation (non-▷ fragment)** · **gate ✓ scoped (2026-06-24, ADR-0039)** | `lr_fundamental` proven for the **non-▷ fragment** (pure CBPV · functions · non-recursive ADTs · throws); the cohesive **▷-subsystem** (μ fold/unfold · `up` · resumptive state/txn handlers) → **◊4.5**. (`group_recovers` RETIRED — ADR-0032.) | ✅ scoped gate met: `lr_fundamental` reads the real proof, `sorryAx` ONLY from the documented ▷-subsystem; ◊2 (`no_accidental_handling` 0-axiom, STD trusted-three) + ◊3 (CalcVM trusted-three) held; arrow clause = peeling+F-restriction (ADR-0038), closed-value carrier (ADR-0036). `lr_sound_closed` (F-typed) proven; `lr_sound`(arbitrary-C)/`zero_usage` → ◊4.5. `effect_sound` (Q14) → ◊5 |
| ◊4.5 | **LR ▷-subsystem** · **✓ SCOPED-SEAM LANDED + MERGED into main @ `4c77ba8` (2026-06-24, gated 724 jobs); sorryAx-zero PROBED NO-GO under DYNAMIC dispatch → PIVOT to typed+static (ADR-0045) DISSOLVES the edge** | Answer-typed KrelS rebuild + (g) migration (frozen `Crel:=CrelK`) + `lr_sound` over typed ⊑ + μ fold/unfold + `up` + throws/state/txn resumptive composition ALL closed end-to-end. The resume-through-a-wrap edge is the ONE documented `krelS_splitAt_decomp` sorry (ADR-0026 descent; **ADR-0043**). `NoWrapMiss` predicate banked = the right primitive | **BROAD moat, NOT sorryAx-zero:** `lr_sound`/`lr_fundamental` hold for ALL contexts (incl. state-over-throws + legit stacking) modulo the single documented resume-edge sorry. The cheap typed-CrelK close (Architecture D) was BUILD-PROBED (`typed-crelk-probe@ffac1b0`) and is **NO-GO**: `HasStack` pins the bottom answer but the strip's intermediate `KrelS` hole can't be typed (no `KrelS⇒HasStack` bridge; LR one-way) — D only relocates the leak. Only the heavy index-everything reshape remains (4–7 sessions + frozen break, not worth one edge). **Seam was verified-final FOR THE DYNAMIC KERNEL; ADR-0045 pivots to typed+static dispatch, which DISSOLVES the edge** (build-gated — it was an artifact of dynamic dispatch; see CONTEXT ★ ACTIVE DIRECTION + `paths/archive/PATH-typed-static-pivot.md`). Merged cleanly (only README conflicted → regenerated; ADR-0043 re-frontmattered to the 0042 schema). |
| ◊5 | **Compiler v0 (the PROOF half)** · **✓ DONE, IN MAIN (`0e5e28d`, 2026-06-24); COMPLETENESS closed 2026-07-10: `compile_forward_sim` UNCONDITIONAL over user effects (#62, `d35295c`)** | `compile_forward_sim` proven; Wasm module type concrete. **Honesty note (2026-07-10): the engine round-trip this row's original gate described never ran — the ✓ covers the proof against the GC-frame abstract machine. The round-trip is RE-HOMED to ◊5.5** (and retargeted from WasmFX to Wasm 3.0 by ADR-0059 — pre-revision gate text preserved in git history). | Proof gate: `compile_forward_sim` ⊆ trusted-three on a clean-tree build of the pinned sha. |
| ◊5.25 | **Close + demo** | Census 18→20 landed (task #37: the StackInc carrier unit, `crelK_fund_up` rewrite); sim-KV nondeterminism demo (post-#94 probe) + IO mock echo server (ADR-0084 slice A) + CTR carried-param binder (#87) in `examples/` | `just verify` green incl. the new examples; proof-state block shows 20 clean; a public v0.1.x tag + short post (the public-early policy starts HERE, not at ◊6) |
| ◊5.5 | **EMISSION — the real ◊5 gate** | `bang build -o out.wasm` emits Wasm 3.0 by grade-directed RUNGS (ADR-0059): rung 1 = ⊥-row/pure fragment → core wasm on ANY engine; rung 2 = abort→exceptions + tail→direct-call; rung 3 = general → the GC-frame-chain runtime | Per rung: the emitted `.wasm` runs on a real engine (wasmtime/node) and prints the SAME value as `Source.eval` on a differential corpus (proof rides the reference, now crossing a real engine boundary). Rung 1 alone unlocks ◊5.75 partially. |
| ◊5.75 | **Compiled demo pack** | `examples/` run compiled; JSON parser + sim-KV in a browser; the xv6-slice narrative once real IO lands (ADR-0084 decision D — needs FFI design) | Demo repo/page with the compiled artifacts; each demo's output diffed against the kernel oracle |
| ◊6 | **Public release v0.2 + papers + validation** (the "v1" LABEL stays deferred — see the research ladder) | Papers drafted from the ◊6 skeletons (`docs/papers/`: calculated-machine — ready once census lands; binary-LR — after 18→20); LICENSE; deliberate outsider exposure (Lean Zulip / HN / lobsters) | Public release tag + submitted-or-preprinted drafts + **the validation gate** (verification ≠ validation): ≥1 outsider ran an `examples/` project unassisted · ≥3 outsider-filed issues. **Pulled forward: exposure STARTS during ◊5.5** (experience-report post), because this gate has other-people latency no internal work can compress. |

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

The tracer bullet is the first product-spine issue (`paths/archive/PATH-tracer-bullet.md`). It de-risks the
surface→kernel lowering — the biggest product unknown — and makes the language *run* before ◊5. The
full end-to-end (surface → CalcVM → WasmFX → engine) thickens as the verification spine reaches it.

This is the **one sanctioned exception** to "linear segments admit no parallelism" below: the product
spine is a *different layer* (surface) from the verification spine (kernel/compiler), so per rule 2
(cross-layer paths run in parallel freely) it does not tangle the ◊-march.

## Pre-v1 research ladder — pulled forward (2026-07-10 operator ruling)

The research frontier moves BEFORE the "v1" label, not after it. The label is deferred;
**publicness is not** — every ◊ from ◊5.25 on ships a public v0.x tag + a short post, and the
◊6 validation gate's outsider exposure starts during ◊5.5 (it has other-people latency no
internal work can compress). "v1" is stamped when the ladder's rungs below have landed or been
consciously cut — not on a date.

These run as cross-layer parallel tracks (parallelism rule 2): R1–R3 are library-code +
handlers over the frozen kernel (design notes already banked), R4 is the one that eventually
needs a K-ADR, R5 is survey-tier. None tangles the ◊5.5 emission spine.

```
R1  NONDETERMINISM   `Choice` as ordinary effect · seeded-deterministic DST handler
     status: DESIGNED (docs/notes/ndet-dst-design.md) · sim-KV queued at ◊5.25 (#94 gate)
R2  DISTRIBUTED      sim-KV grows into the replicated-KV under DST — nondeterminism-as-effect ·
     SYSTEMS         DST-as-handler · certified CRDTs (docs/notes/distributed-story.md)
     status: story mapped · first slice follows R1 (same lattice of handlers)
R3  CALM-AS-GRADE    lattice-store core + `coord` row label; the monotone fragment discharges
     coordination-freeness (docs/notes/calm-as-grade-survey.md)
     status: SURVEYED · probe after R2's lattice-store exists to grade
R4  CONCURRENCY      Q21, the multikernel: STM's privileged concurrent form returns; shared-
     nothing per ADR-0037. KEY SEQUENCING INSIGHT: R1's deterministic scheduler
     makes concurrency semantics TESTABLE-BY-SIMULATION before any real threads —
     design + DST-simulated semantics pre-v1, real-thread implementation post-◊6.
     status: design-first; K-ADR territory; do not start impl before the DST rung exists
R5  REFINEMENT TYPES survey-tier ONLY pre-v1: grades vs refinements — bang's n-axis grade
     family may subsume the cheap cases; refinements-as-an-axis is the question, not a
     commitment. No design note exists yet — the survey is the deliverable.
R6  LAMBDA-CUBE      how far up the cube (F → Fω → CoC) the SURFACE can climb while the
     ASCENT          kernel stays ∀-free (IR has no ∀ — the elaborate-to-mono wall,
     ADR-0027/0075): the polymorphism arc already proved F-and-HKT-without-kernel-∀;
     the question is where that stratified compromise runs out — which dependent-type
     ergonomics elaborate away (the R5 refinement fragment is likely the cheap face of
     this same question) and which demand kernel Π (a K-ADR + downstream re-validation,
     the expensive fork). Grounded in the profile ladder
     (docs/notes/kernel-substrate-survey.md); survey-then-rule, sequenced with R5.
──  MULTI-SHOT (Q22) PARKED, possibly permanently: nothing in R1–R5 or the xv6 narrative
     needs it (cooperative scheduling = one-shot + scheduler loop). Reopening it is a
     deliberate operator act, not a default.
```

## Post-MVP direction — the tracks from here (stable map; live edge in `CONTEXT.md`)

The tracer-bullet MVP is COMPLETE (ADTs · recursive `data` · arithmetic · effect-typed signatures ·
named capabilities · compiled path) — the verified kernel surfaced end-to-end, both engines agree.
Below are the stable tracks. **For where we are RIGHT NOW, read `CONTEXT.md`** — this section is the
map, not the cursor (re-implementing the live edge here is what drifts it).

```
ERGONOMICS (dogfooding pain points)
  #30 parser ✅ (Pratt rule-table, ADR-0071/0072). Downstream OPEN: `bang fmt` (Q24) · tree-sitter (#9) · #31.
  #41 checker A-normalization · #10 elaborator error quality · #7 REPL                       [OPEN]

THREE NORTH-STAR TRACKS (each design-first, ≈post-v1; the operator sequences them, not a default)
  (a) TOOLCHAIN-CAPABLE ✅ CLOSED — recursion (#42, ADR-0073) → strings (#49, ADR-0074) →
        a tokenizer WRITTEN IN BANG (#49 stage 5, `ce6d738`; zero compiler change). Verified kernel
        untouched. Follow-ons: inductive `Nat` (Q31) · #48 effectful recursion · packed-string runtime
        + Char refinement (ADR-0074 deferred).
  (b) POLYMORPHISM ✅ CLOSED (`cea8ae2`) — the generic, lawful, verified stdlib: HM → generic data
        (ADR-0079) → bounded traits (ADR-0080) → annotation-free intro (ADR-0081) → HKT Functor+Monad
        (ADR-0082) + prelude Option/Result/Either (ADR-0083) + effect row-poly (`5d0a32f`), all
        elaborate-to-mono (ADR-0075) — verified kernel UNTOUCHED the entire arc. Forward frontier: optics (Q26).
  (c) USER-DEFINED EFFECTS & HANDLERS ✅ ARC COMPLETE — "paradigm is a value" MADE REAL, THE MOAT.
        #44 (ADR-0085): a general kernel handler + `effect` decl + handler expression, landed end-to-end
        kernel→machine→LR→soundness→surface (`handle … with`, ADR-0095). Spine-touching + furthest-reaching;
        forward slices (compute-then-return, carried-param, IO/net) are operator-sequenced — cursor in `CONTEXT.md`.

VERIFICATION COMPLETION (parallel, verification-spine layer)
  #15 lr_sound ◊4 seam — OPERATOR-RULED deferred (D-now/A-probe-later, 2026-07-09; PATH-inc5)
  #16 U5b-handler ✅ CLOSED (ADR-0086 premised re-freeze) · #17/Q27 resumption grades →
  compilation strategy · Q21 concurrency (the multikernel)
```

### Pratt downstream — ✅ ①②③④ ALL LANDED (this section is now historical)

```
② keyword rules      reify if/let/match/with/do as first-class Rules; retire the bespoke pExpr arms
③ generated grammar  gen-reference.py grammar leg from the rule table (closes #38) — grammar can't drift
④ whitespace + fmt   whitespace-insensitive tokenizer + `bang fmt` canonical form (Q24) — papercut killer
#31 / #26            fold into ②/① (explicit "program start" rule; the precedence loop)
```
Each is guard-gated by the existing `parsesTo` corpus (behaviour-preserving) — dispatchable to an IC
the moment stage ① merges.

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
│   graded-CBPV  ─Bahr-Hutton→  CalcVM  ─fwd-sim→  Wasm 3.0     │
│   theorems: type safety, lr_fundamental, compile_forward_sim  │
│   optimizations welcome; must preserve preceding theorem      │
│   cadence: days                                               │
└──────────────────┬────────────────────────────────────────────┘
                   │ SEAM: Wasm 3.0 module + GC-frame handler protocol (ADR-0059)
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
   │   (◊5.5 emission rungs first; then effect-specific lowerings,
   │    dead-code, zero-grade erasure — with a real engine to measure against)
   │
   ├──► PATH-kernel-extensions ─ owner: kernel-engineer + proof-engineer
   │   (the research ladder R4 concurrency/STM + cost grading;
   │    multi-shot PARKED with Q22 — see §Pre-v1 research ladder)
   │
   └──► PATH-surface-v0        ─ owner: surface-engineer
       (parser, type-checker, CLI, error messages)
```

## What's frozen vs liquid

| | Frozen | Liquid |
|---|---|---|
| **Kernel layer** | rows-as-sets · five primitives · graded-CBPV substrate · calculation-as-method | proof-body internals · helper lemmas |
| **Compiler layer** | two-hop architecture · Wasm 3.0 as target (ADR-0059; WasmFX `switch` = post-standardization fast-path only) · LR as correctness notion | individual machine designs · optimization strategies |
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
├── Bang/                   ← the Lean library (tier folders; `ls Bang/` reads as the architecture)
│   ├── Frontend/           ← Surface · NamedCore (parse/elaborate → IR)
│   ├── Core/               ← IR · Typing · Semantics · Grade · EffectRow · Freshness · CapCoh · Soundness
│   ├── Backend/            ← AbstractMachine (calculated VM) · Wasm (verified target)
│   ├── Meta/               ← LR · BinaryLR (the logical relations)
│   ├── Witness/  Reify/    ← refute-witnesses · CalcReify
│   ├── Spec.lean           ← wasmfx spec (graded-CBPV + LR + WasmFX target) — frozen acceptance criteria
│   ├── Audit.lean          ← #print axioms gate
│   └── Distribution.lean   ← semilattice / CALM asset (flagged conjecture)
│   (authoritative module graph: GENERATED in docs/architecture/core-overview.md §2)
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
└── .claude/agents/         ← domain-specific subagent definitions (models pinned in frontmatter)
    ├── kernel-engineer.md  proof-engineer.md  lean-proof-auditor.md   (opus)
    ├── compiler-engineer.md (opus) · surface-engineer.md (sonnet)     ← activated 2026-07-09
    └── (librarian: defined on activation)
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

- Reaching a checkpoint (mark ◊ as ✓; advance the "current" cursor) — and refresh
  `docs/notes/loop-audit.md` in the same commit (`tools/check-loop-audit.sh` enforces
  the freshness: a ROADMAP commit newer than the loop-audit fails fitness)
- Adding a new path or layer
- Changing a checkpoint definition (rare; treat as architecture change)
- A K-ADR lands that affects the architecture diagram

Everything else goes in `CONTEXT.md`.
