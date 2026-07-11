# AGENTS.md — read this first

## What BANG is

A small language whose **paradigm and runtime are values, not language features**. The kernel is thunks + effects + STM; everything else (mutability, IO, async, actors, signals) is ordinary library code over it. Programs are **descriptions** until forced with `$` (ADR-0007; `!` is actor-send); a function's **paradigm** is which effects are in its row; a program's **runtime** is a handler installed at the use site.

**First time in this repo?** Read `ONBOARDING.md` for setup + a tighter reference index.

## Reference index

This file is the always-loaded core: invariants, glossary, architecture-in-force,
verify-command. Everything else is on-demand — consult the relevant doc when
its trigger arises.

| When you need… | Read |
|---|---|
| **Product definition** (what bang-lang is, the moat, v1 scope, tracer bullet) | `docs/PRD.md` |
| **Current session position** (where we are RIGHT NOW) | `CONTEXT.md` |
| **Long-term checkpoint map** (◊1 → ◊6) | `ROADMAP.md` |
| **First-time setup + reference table** | `ONBOARDING.md` |
| **How to contribute** (workflow · where docs live · agent write-discipline) | `CONTRIBUTING.md` |
| **How work flows** (lifecycle + feedback loops + quality gates) | `docs/notes/development-lifecycle.md` |
| **What an `incN` is** (the increment unit: scoped→de-risked→ground→done→merged) | `docs/notes/increment-lifecycle.md` |
| **Codebase maintenance** (objects · rungs · cadence · debt-prevention) | `.claude/codebase-maintenance.md` |
| **Active in-flight work** | `paths/PATH-*.md` |
| **Architecture in force** | `docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md` |
| **All ADRs** (why-we-chose-X log) | `docs/decisions/README.md` |
| **Deferred design questions** | `docs/notes/OPEN_QUESTIONS.md` |
| **Design-space survey** (open language-design questions + neighbour languages) | `docs/notes/design-space-map.md` |
| **structOK multi-arg descent design** (#50 · the ADR-0091 fork's full analysis) | `docs/notes/structok-multiarg-design.md` |
| **Multi-shot survey** (Q22/Q27 · one-shot-precedent · WasmFX backend constraint · verification-tax · the labelling-vs-closure verdict-shape) | `docs/notes/multishot-survey.md` |
| **Distributed-systems story** (post-v1 arc: nondeterminism-as-effect · DST-as-handler · certified CRDTs · CALM-as-grade · the KV-store hello-world) | `docs/notes/distributed-story.md` |
| **Ndet/DST design** (rung-2 entry slice · `Choice` as ordinary effect · seeded-deterministic DST handler = replayable sim, no IO · sim-KV handler-swap · designed within the D4 ret-shape wall via stateless seed-splitting · the gap list = G1 is the only critical-path ask) | `docs/notes/ndet-dst-design.md` |
| **Host-IO design** (filesystem/net/ambient IO as effects+handlers · the pause/resume seam = a 4th `MOutcome` `msuspended` in the ENV machine, driven by `Main.lean` — `Source.eval`/`evalE` stay pure (no kernel prim) · the TRACE-REPLAY gate = record real IO as a Sendable trace, replay as a sim handler under `Source.eval` (invariant #1 for the tested-stratum host handler) · **Q(conc-6) ruling: recorded-effects replay** · v1 wedge = Console+Clock · `--env=sim/real`+`--allow` least-authority = WASI preopens · static residue: no Lean musl (#2931 not-planned), compiled-wasm component IS the static story) | `docs/notes/host-io-design.md` |
| **Compute-then-return exit gate** (#44 D4 lift · the answer-grade wall re-verified STANDING but reframed as a KERNEL-typing wall · two pillars: binop-untypeable vs answer-grade · Q27 mis-attributed for the pure case · G1 = ⊥-row arithmetic, ret-normalizable · honest gate = ADR-0065 ④ + a ⊥-row HasClauses carve-out · slice order F2-before-F1 machine-forced) | `docs/notes/ctr-design.md` |
| **Proof-export survey** (Q43 design: law → Lean goal over the elaborated Comp · QuickChick-Dec analog · content-addressed cache · nothing enters the TCB) | `docs/notes/proof-export-survey.md` |
| **CALM-as-grade survey** (rung-3 map: lattice-store core + `coord` row label · grading-the-row rejected · the Datalog-transfer wall · SPU = monotone fragment discharging `rowmonotone_coordination_free`) | `docs/notes/calm-as-grade-survey.md` |
| **Laws taxonomy** (model-shaped vs morphism-shaped · composition-closed ⇒ gradeable criterion · the free/graded/law/runtime ladder · Q38 = one theory, three coats) | `docs/notes/laws-taxonomy.md` |
| **Compiler-as-DBMS survey** (salsa scheduler + Merkle trace rebuilder · dump = Glean-style fact base · VERIFIED VIEWS named · the eager versioned-schema step) | `docs/notes/compiler-as-dbms-survey.md` |
| **OS-inspiration survey** (five-primitives-as-microkernel CONFIRMED load-bearing · row-attenuation = pledge-as-a-type (the cheap item) · seL4 noninterference = the security headline shape) | `docs/notes/os-inspiration-survey.md` |
| **Kernel-as-substrate survey** (verified semantic substrate · profile ladder = λ→-typed FLOOR + erased ceiling (kernel has NO ∀, IR.lean:229) · n-axis grade FAMILY named by RISC-V extension letters (5 axes already in-repo) · adequacy transfer condition · STLC/IMP tracer scoped) | `docs/notes/kernel-substrate-survey.md` |
| **Effects vs CIC** (derivable-as-DATA vs additive-as-BEHAVIOR · fuel = the CIC-compatibility seam · Herbelin inconsistency = why quarantine is mandatory · CBPV as the synthesis · the R6 lambda-cube frame) | `docs/notes/effects-vs-cic.md` |
| **Refinement-types survey** (R5 · refinements ≠ a grade axis (3 structural failures, GHL corroborates) · grade family eats the arrow-shaped half, value-predicate residue stays · discharge ladder rung 0–3 (Q31 solver-free → SMT tested-stratum → lean-smt TCB-neutral) · CBPV dodges the lazy-binder unsoundness by construction · verdict: defer impl, framing adopted) | `docs/notes/refinement-types-survey.md` |
| **Lambda-cube ascent survey** (R6 · where elaborate-to-mono runs out · λP-closed + λP-refined = two more ERASED rungs gated by instantiation-set FINITENESS (the §4 wall: polymorphic recursion/packing, runtime indices) · dependent-CBPV field converges on dependency-over-values/total-base = bang's existing seam · CoC corner theorem-excluded (fire triangle) · verdict: extend the ladder, kernel Π stays a priced closed door) | `docs/notes/lambda-cube-ascent-survey.md` |
| **Emission rung-1 probe** (◊5.5 SPIKE: pure ⊥-row arithmetic → core `.wat`, RAN on wasmtime 45 · 4/4 == `Source.eval` — first bang output outside Lean · HOP DECISION emit-from-`Comp` (compile folds pure to `RET`; `Code` degenerate) · former→wasm map · TESTED-stratum, proof-grade = §5 · rung-2 wall throws→`try_table` · leaf `Bang/Backend/WasmEmit.lean`) | `docs/notes/emission-rung1-probe.md` |
| **Emission rung-3 design** (◊5.5: txn journal/rollback DEMONSTRATED on wasmtime — linear-memory + $heaplen snapshot (WasmGC heap = rung-4) · catch_all_ref+throw_ref restore INSIDE the throws try_table · KEY: wasm unwinds free but memory rollback is EXPLICIT (the restore is load-bearing, hand-witnessed) · corpus 66→72 · slice map S0-done→S4 proof-grade (ADR-0035 shape: memory↔Θ bijection)) | `docs/notes/emission-rung3-design.md` |
| **Emission rung-4 design** (◊5.5: closures+ADTs+recursion → WasmGC DEMONSTRATED — **nqueens = 21004 on wasmtime 45**, 10 whole programs all == `Source.eval` (first bang closures/generic-ADT/deep-recursion outside Lean) · KEY: recursion FALLS OUT of the μ-knot (fold/unfold/force/app), machine stays a calc-output (inv#4) · uniform `$val` GC supertype (boxed-i64/`$sum`/`$pair`/erased-fold/`$clos`) · env=cons-list · app/force=`call_ref` · thunk≠lam index-shift bug · bignum=i64-LOUD-wrap (rung-5) · effects=NAMED refusal (inline path) · corpus 72+10=82 · separate `emitModuleGC`, axiom `[propext]`) | `docs/notes/emission-rung4-design.md` |
| **Emission rung-5 design** (◊5.5 entry: unified `$val` READBACK shipped — `emitModuleGCPrint` renders the GC graph in-wasm + WASI `fd_write` (the exact image of `valPretty`; one printer gates Int AND Str, corpus 82+1=83, **caesar's Str result joins**) · fidelity gap: erased `fold` reads back `inl ()` (never bites, documented) · Part-2 VERDICT: **v1 needs NO frame chain** — every v1 handler form resumes one-shot in-place (ADR-0025 D1), so rung 5 = a REPRESENTATION merge onto `$val`/`$env` (state cell = mutable `$ref` box; two hand-unified witnesses ran) · slice map S0–S5, no frame-chain slice · ADR-0059's GC-frame-chain slot = post-v1 multi-shot) | `docs/notes/emission-rung5-design.md` |
| **Memory-management survey** (no memory subsystem — CBPV + the grade family IS one · mutable handler = param-passing (D5 slice over `Dispatch.lean:137`) · closures = the only heap escapers · U grade = 0/1/ω policy dial · host-GC→Perceus→regions ladder · backend = Wasm 3.0 (ADR-0059): the WasmGC frame-chain IS heap+general-resumption, v1 needs only abort→exn+tail→call · VERDICT cap-escape ≈ region-escape TRUE at the type level (scoped-cap = `runST`), FALSE at runtime (escapedCap catches caps not data)) | `docs/notes/memory-management-survey.md` |
| **Stage-5 LR design map** (the three pre-registered debts probed · ret-shape tractability CONFIRMED · one-session verdict · the HandlerRel-ripple slice order) | `docs/notes/stage5-lr-design.md` |
| **Stage-6 soundness design** (the composition was already met incrementally · the instantiation lemmas + custom_program_safe e2e headline · Q14 out of #44) | `docs/notes/stage6-soundness-design.md` |
| **Stage-6 soundness-composition map** (#44 Stage 6 · the headline gate met by composition as Stages 2-5 landed · the two instantiation lemmas + the e2e capstone · Q14 out of scope) | `docs/notes/stage6-soundness-design.md` |
| **Stage-7 elaboration probe** (#44 Stage 7, now LANDED `1284c8e` · the 4 walls: label-slot → ADR-0095 D1a · checkHClauses mutual sibling · elabBind effects fix · WALL 4 = synthSV→synthSC) | `docs/notes/stage7-elab-probe.md` |
| **◊6 paper skeletons** (calculated-machine + binary-LR: census-checked claims · venue candidates · honest what-remains) | `docs/papers/` |
| **Verification ladder** (agent-speed quality gates · HoTT verdict · Q43 proof-export) | `docs/notes/verification-ladder.md` |
| **Dogfood: JSON parser findings** (#61 blocker · module-shape needs · what worked) | `docs/notes/dogfood-json-findings.md` |
| **Dogfood: calculator findings** (largest corpus program, 6 modules · `--compiled` hangs on re-entrant parser knot (env+ck agree) · `bang fmt` breaks `$(Mod.op)` · ctor arity ≤ 2 · sibling let-recs no forward-ref · imported-effect names need `Mod_Eff` everywhere · wildcard-arm = top ask) | `docs/notes/dogfood-calc-findings.md` |
| **Stranger test round 1** (8.5/10 · the reference-strings blind spot · the repeatable method) | `docs/notes/stranger-test-1.md` |
| **Stranger test round 2** (7/10 · modules+laws under-surfaced · the pub-bypass find (#73) · rebuild-first method addendum) | `docs/notes/stranger-test-2.md` |
| **Stranger test round 3** (7/10 · Stage-7 user-effect surface: single-op works, multi-op broken (#86) · param-init inert (#87) · undocumented (#88) · laws+check-json FIXED vs r2 · probe-one-step-past-the-example addendum) | `docs/notes/stranger-test-3.md` |
| **Stranger test round 4** (8/10, up from 7 · round-3 blockers ALL fixed (#86/#87/#88) · the gaps MOVED: features work, docs don't teach the authoring idioms · F1 = the misleading force-suggestion diagnostic · F2 = deriving absent from reference + generic-carrier derive fails · F3 = cap-threading idiom undocumented + effect-op/prelude-ctor name clash · 90-line RPN calculator shipped) | `docs/notes/stranger-test-4.md` |
| **Calculated CHECKER survey** (TCT/SbC · the frontend trust-map · fuzz-harness · evidence-passing verdict) | `docs/notes/calculated-typer-survey.md` |
| **Feedback-loop audit** (loops by radius; refresh at each ◊ — `check-loop-audit.sh` enforces) | `docs/notes/loop-audit.md` |
| **Standard-library map** (the third stratum: reusable abstractions as library code, gated by type-power) | `docs/notes/stdlib-map.md` |
| **Prelude/stdlib survey** (10-language census × the bang gate-map · first-slice menu #105 · the stdlibFnSrcs-vs-Prelude.bang fork #106 · row-propagation = the Koka/Unison/Flix camp by construction) | `docs/notes/stdlib-prelude-survey.md` |
| **Traits/derivability survey** (trait census × derive matrix: model-shaped folds (Eq/Ord/Show/Hash) vs choice (Monoid — 0 derive-paths in 10 languages) · tier-1 = Eq/Ord (binop-dispatched TODAY, zero #78 dependency) · the derived-AND-law-checked ladder = bang-native, no peer ships it · dead-impl carrier check · ADR-0082 = hand-written Functor/Monad, NOT auto-derived) | `docs/notes/traits-prelude-survey.md` |
| **Mutual let rec design** (#97-2 probe: H2 tuple-of-thunks μ-knot ADOPTABLE (spike-verified, kernel untouched, inherits the #95 fix verbatim) · H1 Bekić REFUTED twice (B011 arity wall + the shared-Div completeness regression) · the double-thunk split-reproject trap = the mandatory differential guard · mandatory per-sibling ascriptions mirror ADR-0073 · H3 teaching diagnostic ships independently · structOK group-certification unscoped, conservative-Div default) | `docs/notes/mutual-rec-design.md` |
| **Effect-algebra survey** (R6's computation-axis twin · the four-rung higher-order ladder (forwarding SHIPPED < parameterised=D5 < bidirectional < scoped/hefty) — D4 IS the rung-1→2 boundary · handler-memory = D5 param-update, recursive-effects a red herring · stack-alloc-as-effect NOT earned (escape is structural in CBPV; continuation-responsibility TRUE, literature-held) · the effect cube = ANALOGY along U⊣F not theorem, three real axes (row-poly=λ2 SHIPPED · effect-operators=λω · value-indexed=λP) · hefty-elaboration extends elaborate-to-mono to effects: scoped ops = surface-only, kernel intact) | `docs/notes/effect-algebra-survey.md` |
| **Wasm concurrency survey** (2026-verified · scheduler-as-handler = THE MODEL, components/threads = backends · WASI 0.3 async SHIPPED 2026-06 on a cooperative event loop — the platform independently converged on bang's demonstrated Choice/Sched shape · stack-switching = one-shot by construction ⇒ multi-shot NOT a concurrency requirement (Q22 stays parked; DST-forking only) · components = deployment/isolation, GC values COPY across · threads+STM = reserved seat, substrate years out · concurrency enters the ROW not a grade axis · the grill sheet §6 + 5 unfiled OQs §7) | `docs/notes/wasm-concurrency-survey.md` |
| **Actor-sendable design** (G7 answered: `Sendable` = closed first-order values (the CLI ground-value vocabulary lifted to the ADT closure) — NO vthunk/vcap/vvar · copy≡share: syntactic core PROVEN axiom-clean (`sendable_substFrom_eq` = the inertness fixed-point), contextual form rides the parked LR · Pony ref-caps REJECTED (values already immutable; Erlang = the precedent) · static `!`-site refusal designed · in-process share = a free optimization BY the theorem · §7 = the ready ADR-input for the concurrency-model ADR) | `docs/notes/actor-sendable-design.md` |
| **Grade-poly returner consult** (#115 DEFER: the F ∀q′ door is SOUND (falsifier NEGATIVE — the binop reduct is a closed literal at grade zeros, any q′ free) and CHEAP (~4 mechanical edits off the existing BinOp.eval_hasVTy) · subsumption UNSTATEABLE (no order on Mult — Torczon Qle was dropped) · custom_resume_focus_types CLOSES under the shape · no consumer today (G1 met tested-superset; the named future consumer = the post-v1 verified-core DST demo) — open the door when claimed, priced here) | `docs/notes/grade-poly-returner-consult.md` |
| **Traction survey** (the census: wedge/timeline/content-mechanics per language · LEAD = "docs that cannot lie" (shipped, not promised), replay = beat 2 · top-3: ship site/ on the tag → stranger-journey tutorial → #70 announcement+asciinema · media team = NOT-YET (census-backed; operator IS the media team pre-1.0) · killer-app un-schedulable (Bun/Servo/Phoenix) · playground = rung-1-only honest · registry = the everyone-names must-have, correctly v1-non-goal) | `docs/notes/traction-survey.md` |
| **Distribution survey** (rung-0 ALREADY BUILT — release.yml + curl install.sh + the patchelf de-nix trick · gap = matrix breadth (widen to aarch64-linux/darwin, Lean Tier-1) · static IMPOSSIBLE (glibc-2.26+ floor, document it) · 78MB stripped = the real cost line · Windows post-1.0 · ladder: matrix → brew tap → container/npm-assess) | `docs/notes/distribution-survey.md` |
| **Interactive tour design** (ladder: v0 no-exec corpus-lessons on the existing site ($0, expected.txt = the lesson oracle, drift-proof) → v1 server-backed /run — THE NO-IO SANDBOX WIN: bang has no fs/net/ambient-IO ops + fuel-bounded ⇒ resource-jail only, lighter than Rust's docker-per-run · Lean-to-wasm NON-STARTER 2026 (Mathlib-linked unsupported — the exact blocker) · site/tour/ vocs section, not a second property) | `docs/notes/interactive-tour-design.md` |
| **Copy kit + explainer series** (tagline: "The docs can't lie. They're generated from the proof." · 30s hero · 2-min pitch · the 6-question skeptic FAQ (stratification honesty = the load-bearing answer) · anti-hype rules · series order $-force → handler-swap → row → stratification → replay · logger-silent/counting = the literal cartridge-swap demo · the HELD-BACK claim = replay-by-default, promoted when a runnable demo exists — the highest-leverage content unlock) | `docs/notes/copy-kit.md` + `docs/notes/explainer-series.md` |
| **Formatting-techniques survey** (the canonical formatter #58: three-rung map · exact-vs-canonical · layout engine · zero-config) | `docs/notes/formatting-survey.md` |
| **Handler-surface + unification survey** (Q38/Stage-7: the handler-syntax census · module≟trait≟effect unification attempts + failure modes · grade-as-dial prior art · ADR-inputs) | `docs/notes/q38-handler-surface-survey.md` |
| **God-file seam map** (TypeCheck/AbstractMachine split proposal · cut order · abbrev-risk register) | `docs/notes/god-file-seams.md` |
| **Spanned-Surf design** (#52: located errors + hover · Q1-Q4 verdicts (no `Surf`/`P` change) · decl-granularity hover LANDED as `bang query hover`, slice 5) | `docs/notes/spanned-surf-design.md` |
| **All design notes** (the exhaustive map of `docs/notes/`, grouped by status — generated) | `docs/notes/README.md` |
| **Categorical reading** (objects/morphisms: graded `F⊣U` adjunction · graded monad = paradigm · handler-algebra · the two-hop functor) | `docs/notes/categorical-architecture.md` |
| **Proof discipline** (PROOF_ORDER, sorry rules, axiom hygiene) | `docs/notes/spec-proof-discipline.md` |
| **Why the wasmfx spec is engineer-ready** | `docs/notes/spec-handover.md` |
| **Lean 4 tactics for this work** | `docs/notes/tactics-survey.md` |
| **K2/K3 calculation proof patterns** (legacy) | `docs/notes/k2-calculation-playbook.md` |
| **K3 historical status** (pre-pivot narrative + composition-mechanism map) | `docs/notes/k3-historical-status.md` |
| **Dev environment** (Nix flake, scripts, gotchas) | `docs/notes/dev-env.md` |
| **Comment/doc convention** (Mathlib-grounded; `just symbols` for navigation) | `docs/notes/lean-comment-style.md` |
| **Original design thesis** (v0/v1; partially superseded by ADR-0016) | `docs/spec/bang-lang-design.md`, `docs/spec/bang-lang-description-value.md` |
| **K-keyframe research roadmap** (complementary to ROADMAP.md) | `docs/roadmap/bang-northstar-roadmap.md` |
| **References library** (cited papers + refs.bib) | `references/README.md` |
| **Subagent roles** (models pinned in frontmatter) | `.claude/agents/{kernel,proof,compiler,surface}-engineer.md` + `lean-proof-auditor.md` |
| **Run any task** | `just` (lists recipes); see `justfile` |

## Architecture in force (third design revision)

Two-hop verified compilation per **ADR-0016 as revised by ADR-0059**:

```
  source → graded-CBPV semantics → CalcVM (Bahr-Hutton) → Wasm 3.0 (annotated simulation)
```

The CalcVM is the executable spec; **Wasm 3.0 is the verified compiler target** (ADR-0059:
grade-directed lowering — pure→native, abort→exceptions, tail→direct call, general→the
GC-frame-chain runtime, the one pluggable slot where WasmFX `switch`/`resume` becomes a
fast-path once standardized; stack switching did NOT land in Wasm 3.0). The CalcVM→Wasm hop
is proven by **annotated forward simulation** (`compile_forward_sim`, ADR-0035) against the
GC-frame abstract machine — NOT the biorthogonal/Benton–Hur LR, which proves ◊4 *contextual
equivalence* (a separate theorem, the binary LR).
ADRs 0003 and 0004 were deleted, subsumed by 0016. See `CONTEXT.md` for
where the implementation stands; `docs/notes/k3-historical-status.md` for
what the K3 work taught (preserved as input to the graded-CBPV port at ◊3).

## The stratification principle (the load-bearing mental model)

One shape governs the whole project: a **verified core + a tested superset, separated by an
explicit, type-visible seam.** It recurs at three levels (ADR-0026 / ADR-0028):

```
level         verified core              tested superset             seam
──────────────────────────────────────────────────────────────────────────────────
correctness   verified (proof)           tested · unsafe             the ADR-0026 ladder
tooling       Lean (kernel·CalcVM·       surface · runtime           typed AST + differential test
              compiler·LR)               (diff-tested vs Lean)
language      total fragment             Div fragment                the EFFECT ROW (Div = descent)
              (⊥-row, System F)          (fuel-bounded, Turing-compl.)
```

Descent (verified → tested) is **always explicit and marked, never silent**. The expensive proof
budget is spent only on the verified core; the superset rides differential-testing + fuel.
(`Source.eval`'s fuel-bounded interpretation of the partial `Comp` already demonstrates the
language-level seam — a total prover interpreting a Turing-complete object language.)

## Invariants — never break these

1. **Proof rides the reference.** Anything that runs is either `exec` itself or differential-tested against it. Never ship an execution path with no oracle behind it.
2. **Effect rows are sets** — idempotent, union = join. Never ordered, never a multiset. (ADR-0001) Post-Q1: `[Lattice Eff] [OrderBot Eff]` (ADR-0018).
3. **STM is the *only* privileged kernel primitive.** Everything else is effect + handler. (design doc; preserved by ADR-0016.) **ADR-0030**: privilege is *concurrency-only* — single-threaded STM **is** a transactional handler, so **v1 ships STM as a handler**; the privileged shared-heap form returns with concurrency (post-v1). STM stays a *named* member of the five (below), unused-as-privileged in v1.
4. **The machine is an *output* of the calculation**, never hand-designed. Calculate, don't verify-after-the-fact. (ADR-0016, formerly ADR-0004)
5. **Kernel stays at five primitives:** thunk · force · effect rows · handlers · STM. Adding a sixth is a spec change requiring an ADR.
6. **No implicit capture; reactivity is the operator, not a keyword.** (ADR-0005, ADR-0006)
7. **Performance is second-class.** Optimize only where it touches the user; a slow correct path beats a fast unverified one.
8. **Effect TS is not the target.** The calculated VM is canonical; the WasmFX backend is the verified compiler target. (ADR-0016, formerly ADR-0004; supersedes ADR-0003)

## Do NOT

- add a kernel primitive · make rows ordered · reintroduce `sig` · add implicit lexical capture
- hand-design the VM, then justify a compiler against it
- optimize speculatively, or add a feature the spec's Non-Features section forbids
- prove most-generality (MGU) for unification — soundness is the contract; MGU goes to the differential test

## Ubiquitous language (glossary)

| term | meaning |
|------|---------|
| **thunk** | a deferred computation; every value is one until forced |
| **force** `$` | evaluate a thunk to WHNF; the only way to observe a value (ADR-0007). bare `name` = description, `$name` = value. `(e)` *groups* without forcing; `$(e)` groups then forces. `!` is **not** force — it's actor-send |
| **`:` / `=`** | `:` introduces a binding (silent); `=` equates (live sync if RHS is a live description, sampled if `$`-forced). reactivity = equality over thunks (ADR-0005) |
| **effect row** | the set of effects a function may perform, carried in its type after `with`. composes by union (join) |
| **handler** | a value implementing an effect's operations; installed with a `with` block; runtimes are handlers |
| **capability** (cap) `vcap n ℓ` | a value naming ONE specific handler *instance* — carries both its **identity** `n` and **label** `ℓ`; the selector a `perform` dispatches on |
| **label** `ℓ` | an effect's *name* — the type-level tag the **effect row** tracks. Many handler instances can share a label |
| **identity** `n` / `g` | a handler instance's *generative, globally-fresh* id (ADR-0055); what `idDispatch` matches at runtime (`g` = the fresh-id counter) |
| **dispatch** | **identity-keyed** (runtime: match the cap's identity `n`), realizing **lexical** semantics (the cap names its lexically-enclosing handler) — NOT dynamic/nearest-label (the rejected stale `evalD`, ADR-0052). **Core principle: typing is by *label*, dispatch is by *identity*** — the gap the cap-escape soundness work turned on |
| **escape** / `escapedCap` | a capability dispatched *after its handler popped* (e.g. captured in a thunk, forced past the handler). v1: a **defined fail-loud** terminal `escapedCap`, not `stuck` (ADR-0063); post-v1 made untypeable by scoped capability types |
| **STM / TVar** | the one privileged primitive (its *concurrent* form; **v1 STM is a transactional handler** — ADR-0030, journal/retry/validation deferred to concurrency). transactional memory; TVars usable only inside `atomically` |
| **oracle** | the verified reference an implementation is checked against |
| **`Source.eval`** | the KERNEL — the handler-based CK semantics; the hop-1 oracle every other eval is checked against |
| **`evalD`** (CalcVM reference) | the *middle* reference: the kernel's semantics with effects realized as explicit STATE (`SStore`+`THeap`), the Bahr–Hutton starting point. A stateful *lowering* of `Source.eval`; must agree with it (`evalD_agrees_source`). route-B re-derives it **cap-keyed** so it dispatches by identity, not nearest-label (ADR-0052) |
| **calculated VM** | the `(compile, Code, exec)` triple *derived from `evalD`* by Bahr–Hutton equational reasoning (= the **executable spec**). The end-to-end `Agree` diff-test ties `exec∘compile` back to the kernel `Source.eval` |
| **checkpoint (◊)** | a stable pose in the project map; see `ROADMAP.md` |
| **PATH** | a unit of in-flight work between two checkpoints; see `paths/` |
| **ADR** | architecture decision record; see `docs/decisions/` |

## Doc discipline

- **History lives in git, not in docs.** When a fact is no longer current
  (e.g., "K3 was in progress until the pivot"), the commit history preserves it.
  Docs describe present state. Past-tense narrative belongs in commit messages
  or `docs/notes/<topic>-historical-*.md` for genuine archival value.
- **Genuine design decisions** that future sessions might reverse → **ADR**
  in `docs/decisions/`. ADRs record the alternative considered AND rejected
  with rationale (not just the chosen path). ADRs are forks-in-the-road,
  not changelogs.
- **Volatile state** (current position, active path, blockers) → `CONTEXT.md`
  or `paths/PATH-*.md`.
- **Always-useful** (invariants, glossary, architecture-in-force) → here
  (CLAUDE.md). Every token in this file is loaded into every session;
  bloat is expensive.
- **On-demand reference** → `docs/notes/*` indexed in the Reference Index above.
- **Before grilling or opening a design question, read the generated decided-ledger**
  (`docs/decisions/README.md`) — a question with an ADR is **closed**, not open.
  `grep docs/decisions/` first. The ledger is generated from each ADR's frontmatter
  (`just adr-index`); `just adr-check` keeps it ≡ the ADRs + OPEN_QUESTIONS (ADR-0042).

## How to verify (the cheapest orientation)

```
nix develop          # ENTER THE DEV SHELL FIRST — bare `lake`/`just`/`node` are NOT on PATH
just verify          # selfcheck (Node) + lake build + tools/audit.sh
# or piecemeal:
just check FILE      # fast single-file Lean error check
just build           # lake exe cache get && lake build  (cold first time: minutes)
just audit           # bash tools/audit.sh
just burndown        # Phase B sorry/axiom counts per module
just axioms          # lake env lean Bang/Audit.lean — #print axioms per theorem
```

First `lake` build pulls Mathlib via `lake exe cache get` (network; minutes).
Green means: lake build clean, axiom set per headline theorem ⊆ {`propext`,
`Classical.choice`, `Quot.sound`}. If you can express a new invariant as a
runnable check, do that instead of writing it in prose — checkable beats described.

**Gate-traps (cause false-greens):** read errors via `lake build` exit code or
`grep -E "error"` — plain `grep "error:"` MISSES `error(lean.unknownIdentifier):`;
gate sorries via `#print axioms` / `just axioms`, NEVER `grep sorry` (false-positive on
comment prose, false-negative on transitive deps). Gate the COMMITTED sha on a clean
tree — never an agent's summary or a dirty worktree.

## When you make a decision

If you make a choice that a future session could reasonably reverse or relitigate, **write an ADR** in `docs/decisions/` (copy the format of an existing one; `0016` is a good exemplar). Record the *rationale* and the *rejected alternatives*, not just the choice. Anti-drift is mostly anti-reversion, and reversion happens when the "why" is missing.
