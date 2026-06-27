# bang-lang CONTEXT

> Where we are on the map RIGHT NOW. Volatile. Updated as paths complete and
> new ones begin. **Read this first on every fresh session**, after `CLAUDE.md`.
>
> For the long-term map, see `ROADMAP.md`. For research-grade keyframes, see
> `docs/roadmap/bang-northstar-roadmap.md`.

## Position

> **★ ACTIVE DIRECTION (2026-06-27, late³) — SOUNDNESS: the coherence ENGINE is LANDED; the keystone CORE remains.**
> Proof on `inc5-lr-reindex` @ `798f04e` (PUSHED, build green, INDEPENDENTLY gate-verified); docs/design on `typed-static-r1`.
> **The arc:** typeless `wsCfg_step` POP walled (`escapeB_app` refuted ⊥-row/B-occ — escape is grade-`q=0`-dead, not row-absent),
> so `WScfg` was REGRADED (ADR-0061): typeless → graded `LWSCg/LWSKg` + stratified freshness. The v1-close grind closed **#1
> `freshCfg_step`** (axiom-clean; FreshCfg gained the flat `∀p∈capsK K, p.1<g` freshness-completeness conjunct) + **#2
> `lwskg_pop_fresh`**, and **REFUTED #3 `lwsvg_closed_regrade`** (scale-gates couple grade↔liveness even for closed values — kept
> witness `d81515c`). Then the keystone landed its FOUNDATION: the carried `LWSCg` was DECOUPLED from the bundled `HasCTy` (⇒
> spurious-live caps only the grade catches), so **WScfg now carries `LiveCapsResolveC`+typing and DERIVES a coherent `LWSCg` by
> construction** — the `of_typed_live` engine (grades=typing-grades; dead values route to `vcap_dormant`, no resolution). ENGINE +
> RESHAPE are LANDED axiom-clean (`798f04e`): seed (`wellScoped_initial`) + positive (`focusResolves_of_wscfg`) SORRY-FREE over the
> new carrier, #1/#2 survived (gate-verified `e64d80f`).
> **THE REMAINING KEYSTONE CORE (task #51), TWO scoped pieces:** (1) **stack coherence** — `LiveCapsResolveK` mirroring the focus
> carrier (option 1 APPROVED; PUSH maintains focus→stack, REDUCE/POP consume): coherence was missing its stack half (every other
> layer — typing/liveness/freshness — is symmetric focus+stack); (2) **the SHARED grade-coupling re-homing lemma** closing BOTH the
> `lwscg_returnEscape` letC/app/case/split walls (#4) AND the subst arm (#5) — they UNIFY into ONE (coherent grade-flow through
> binders: `q=0`⇒dormant-omitted, `q≠0`⇒cap flows to the body var-0 ⇒ B-occ/row kills). De-risk: UNARY grade-threading (Torczon Cor
> 4.4), NOT a ⊤⊤-LR. → then `lwsg_step_nonperform` closes → `type_safety` sorryAx-on-DISPATCH(#35)-only. Checkpoint `798f04e`:
> 4 sorries, `diagonal`=`[propext, sorryAx, Classical.choice, Quot.sound]` (from #4/#5/#35). Tasks: **#51** (keystone core, NEXT
> UNIT) · #47/#46. Kept guards: `CohSubstRefute`/`LwscgLengthRefute`/`LwscgOfTypedRefute`/`BoccRegress`/`StateEscapeWitness`/`d81515c`.
> **★ STATE-ESCAPE = NO HOLE (this session):** a capability-via-state-cell escape is behaviourally real but HasCTy-UNTYPEABLE
> (closed-state `HasVTy [] [] s₀ S` + VcapFree block it; witness `StateEscapeWitness`, axiom-clean) → `type_safety` true as stated.
> Scoped capabilities (arXiv:2207.03402) is the POST-VcapFree (#18) generalization, costed in
> `docs/notes/scoped-capabilities-for-vcapfree-drop.md` (cap-free-cell ADDITION ~1 session; full CC<:□ REPLACEMENT post-v1).
> **⚠ ENV/INCIDENT (2026-06-27):** a shared-worktree **auto-gc corrupted `.git/objects`** (pruned ~8922 UNREACHABLE cruft; ZERO
> live-work loss — WIP pushed to origin, `gc.auto` disabled). Triggered by the pre-commit `lake exe cache get` re-clone (#40),
> which also left inc5's mathlib at the WRONG rev → re-pinned via symlink to main's clean `c5ea0035`. **Commit `--no-verify`
> ONLY** until #40 is fixed. Memory: `shared-worktree-git-autogc-corruption`. Also shipped: the **counterexamples registry**
> (`cex-registry` branch — aggregator + generated index + a refs≡files ADR fitness check, task #49). The soundness arc that led
> here (inc-4 → ADR-0055 global-fresh → ADR-0056 diagonal-FALSE → ADR-0057 B-occ → ADR-0060 grade-driven liveness → ADR-0061
> regrade) lives in those ADRs + the SOUNDNESS-FINDING block below.
> **COMPILER (Lexa comparison + Wasm-3.0): ADR-0058** (the binary-LR Canonical wall is a frozen-signature
> artifact → route 1 deletes it; build-confirmable, task #33→inc-6) **+ ADR-0059** (Wasm 3.0 + grade-directed
> pluggable backend; v1 = `throws`→exn + `state`/`transaction`→tail-call, the GC-machine general leg is the
> post-v1 ADR-0015 frontier). Both backed by a machine-checked GC-simulation relation (identity-keyed,
> axiom-clean). Two OPEN clauses are task-linked + build-gated (task #33 the re-key compiling; task #36 the
> cross-step partition). **NEXT:** finish the port (tasks #42/#43) → `wsCfg_step` closes save DISPATCH → then the
> DISPATCH arm (#35, resumption-grade) for full `type_safety` sorryAx-clean; then inc-6 (CalcVM route-B + the
> ADR-0058 re-key + the Wasm-3.0 backend). Detail in the SOUNDNESS-FINDING block below + ADR-0060 + tasks
> #35/#41/#42/#43 (soundness) and #33/#36 (compiler).
> **★ SOUNDNESS FINDING (2026-06-26, ADR-0056) — the inc-5 diagonal is machine-checked FALSE.** A cap can
> escape its handler and get STUCK in a well-typed-at-⊥ program (`progB`: the ⊥-row gate is label-based,
> escape is identity-based; ADR-0054's "escape ruled out by the gate" REFUTED — the WC keystone-2c escape,
> half of which global-fresh did NOT fix). **The diagonal + A2's value-cap arms are HELD.** EXPLORATION DONE →
> **ADR-0057 ACCEPTED** (build-confirmed GO): **B-occ** — kernel answer-type label-freedom
> (`¬LabelOccurs ℓ A` on the 3 handle typing rules). KEY INSIGHT: in v1 the answer type is the ONLY escape
> channel (state/transaction cells are closed `int`), so a one-premise kernel fix closes the diagonal BY
> CONSTRUCTION + may DISSOLVE NonEscape entirely (the false diagonal sorry → a corollary of preservation, net
> LOC negative). **Operator ratified B-occ (build-confirm first); `bocc-spike` build-confirmed GO on all four
> claims → ADR-0057 ACCEPTED `dfe8e3d`, 2026-06-26.** (only-channel — corrected to DISCARD-ON-POP, not int-cells;
> discrimination built; dissolution sketchable via one liveness lemma; LR blast ~55 mostly-mechanical.) **B-occ PHASE 1 LANDED**
> axiom-clean (`bocc-spike` `075f894`): premise + `LabelOccurs` + regression (`escapeB_not_typeable` — bug
> untypeable for ANY EffSig). The standalone dissolution WALLS (a `vthunk` can carry-then-DROP a label-free-typed
> cap → `NonEscape` is NOT a structural value predicate) → B-occ is the ENABLER for inc-5's diagonal (NonEscape
> stays the reachability/Shape-B LR projection), NOT a free corollary. **B-occ INTEGRATED** into inc5-lr-reindex
> (`4178ed9`, green except Compat — the diagonal `Bang.Model` STILL CLOSES under the premise). **★ KEY REFRAME
> (inc5-endgame, build-grounded): the SOUNDNESS payoff (`type_safety`) goes through the DIAGONAL (`Bang.Model`),
> NOT the binary LR.** The diagonal is axiom-CLEAN except 2 B-occ-shaped sorries: `handlesOp_of_hasConfigTy`
> (Model:147 — needs `concat_*_interface` infra) + `wsCfg_step` pop-escape (Model:170 — the `¬LabelOccurs`
> NON-PERFORMABILITY lemma: caps INERT past the handler, NOT syntactic absence per bocc-impl's carry-drop).
> Closing both → diagonal/NonEscape/`type_safety` **sorryAx-clean** = THE soundness payoff. **`handlesOp_of_hasConfigTy` CLOSED axiom-clean (`6dab05c`, via
> `HasStack.handlesOp_of_split`)** — `#print axioms diagonal` now traces sorryAx to ONLY `wsCfg_step`. **The
> diagonal's LAST sorry = `wsCfg_step` (Model:185), the WellScoped RESHAPE crux (task #34):** current WellScoped
> collects caps syntactically THROUGH thunks (`capsV (.vthunk c) = capsC c`) → NOT preserved under handleF-pop
> (a dormant cap in a never-forced thunk is carried past the handler yet unresolvable = carry-drop). Fix =
> reshape to SHALLOW/PERFORMABILITY (only PERFORMABLE caps must resolve; a dormant thunk cap is INERT via B-occ
> non-performability + re-resolves dynamically when FORCED — the force-case re-establishment is the de-risk
> crux). WellScoped is the PROOF INVARIANT (not frozen) → reshape freely if step-preserved + implies
> FocusResolves. A multi-session research unit; closing it = `type_safety` sorryAx-clean. **DEFERRED — the binary LR** (`crelK_fund`/`lr_sound` contextual equivalence, for
> the inc-6 compiler path): Units 1+2 decomp banked green (`285338a`); the `crelK_fund` resume reshape + the
> obligation-2 CapsBelow/Canonical question is multi-session — first build-confirm whether `crelK_ret`'s guard is
> over-strong (route 4) before any frozen change. cap-resolution is NOT the blocker (rides stuck-stuck vacuity;
> B-occ doesn't reach that premise-free node). Right-answer-absolute
> = System-C rank-2 (post-v1, needs polymorphism, contradicts ADR-0027); fallback = surface-enforced. B-occ pairs
> with task #18 (untypeable raw vcap → drop VcapFree). Non-escape-INDEPENDENT inc-5 (LR re-key — guarded crelK_ret
> `8c30f06`, LR green/1 sorry; the splitAtId `krelS_staticSplit_decomp` re-derivation = build-ready spec in the
> PATH, best AFTER ADR-0057) PROCEEDS. Witness oracle: progB (DiagonalFalsifyProbe + IdentityCollisionProbe + CapEscapeWitness).
> SoT = ADR-0054/0055 (the cap rep, done) + ADR-0052 (CalcVM route-B, inc 6). inc 1-4 + the global-fresh
> rework are LANDED; the STD block (preservation/progress/type_safety) is axiom-clean over the final kernel.
>
> **inc 4 landed (merged `6cadd6b`):** `NonEscape` frozen as Shape B — an LR-FREE operational closure
> `∀ cfg', StepStar cfg cfg' → FocusResolves cfg'` (Operational sits below LR, so a KrelS projection would
> be an import cycle; Shape B is the proof STRATEGY, the def is operational). The STD block
> (`preservation`/`progress`/`type_safety`) RE-PROVEN over identity dispatch + NonEscape, **ALL axiom-clean**
> `⊆ {propext, Classical.choice, Quot.sound}`, zero sorries; ~1225 lines positional machinery deleted; the
> perform-dispatch re-typing DISCHARGED (`splitAtId_decomp` + re-keyed concat); `type_safety` unified under
> `HasConfig` (Option X — all 3 STD theorems now HasConfig-stated). The sole carried obligation is the
> initial-config NonEscape premise (rides the LR diagonal at inc 5). Green subset: `lake build Bang.Operational
> Bang.Metatheory` (both green); full build RED by design (LR/Compile/Compat/CalcVM unported — inc 5-6).
>
> **★ THE LOAD-BEARING FINDING (this session) — the WC keystone-2c is NOT moot; it is CONCRETELY WITNESSED.**
> The witness port surfaced (verified, reproduced independently on main — `scratch/IdentityCollisionProbe.lean`):
> Fork-ii's `handlerCount` is a DEPTH; a popped-then-reused depth lets an escaped capability re-resolve to a
> WRONG same-depth handler (a CROSS-EXTENT COLLISION). `progB` (re-handled escape) → `done` reading the
> impostor's state; `progB'` (direct-force escape) → `stuck`. `NonEscape`-as-`FocusResolves` ("resolves to
> something") is TOO WEAK — it admits the collision (resolves-to-something ≠ -to-the-right-one). The merged
> inc-4 theorems stay SOUND (they prove no-stuck, not resolution-transparency; `progB` is `done` not stuck),
> but capability resolution-transparency is NOT yet achieved.
>
> **★ GLOBAL-FRESH DONE (ADR-0055, merged `6041bea`):** identity now mints from a MONOTONIC Config counter
> (`Config := Nat × EvalCtx × Comp`), never reused → no two handlers share an id → an escaped cap resolves
> to ITS handler or to NOTHING (stuck) → collisions UNREPRESENTABLE, `NonEscape` ADEQUATE. **`progB` → STUCK**
> (was done-via-impostor; independently gated on the real reworked kernel). `WellCounted` (live ids < counter)
> added as a SEPARATE reachability invariant (sibling to `NonEscape`, NOT in `HasConfig` — the STD block never
> touches it; confirmed by the isolated-sorry milestone); STD block re-established axiom-clean,
> `stackBelow_idDispatch` discharged sorry-free; `type_safety` literal `(0,[],c)` (blessed STATEMENT_CHANGE_OK).
> `wellCounted_reachable`/`splitAtId_fresh` feed the inc-5 diagonal.
> **★ NEXT = inc 5 (LR/Compat):** re-key the LR to the new Config + identity dispatch; the initial-config
> NonEscape obligation (the LR diagonal) becomes PROVABLE under global-fresh (was the inc-4 carried obligation).
> First whole-LR green. Then inc 6 CalcVM route-B (ADR-0052) · inc 7 Surface.
>
> **Parallel this session — improve hygiene (4/5 landed on main):** audit-gate sync lifted convention→tested
> (`tools/check-audit-sync.sh` in `just fitness`) · 4 superseded probes → `scratch/archive/` · Distribution
> conjectures gated · CONTEXT SHA-discipline note. #1 (wire the behavioral witnesses into the Audit gate) —
> the witnesses are now ported + green (`CapEscapeWitness`/`LWRegress`, 3-arg AST), wire them into `Audit.lean`
> when inc-6 greens the Audit gate (it imports CalcVM, red until route-B).
>
> **This session's commits (`typed-static-r1`):** inc-4 metatheory `0d5e7c9`→`2193d31` (merge `6cadd6b`) ·
> witnesses + collision probe `f1d962a`/`184846d` (merge `a43f9ca`) · improve `172a02f`/`51e6da3`/`cd10446`/
> `1146a02` · guard+de-risk `eacd7b8` · ADR-0055 `2a7f5c1`. Detail: `paths/PATH-identity-representation.md`.
>
> **Deferred units:**
> - **CalcVM route B** — re-derive `evalD` to match the lexical kernel (ADR-0052), now keyed to the identity
>   representation; multi-session. Whole-tree green returns when this lands.
> - **`hcatch` + `:1801`** — the 2 remaining ADR-0043 LR descents (Compat).
> - **~~`preservation_returnEscape_TODO`~~ — DONE (inc 4):** now PROVEN by construction (NonEscape's
>   forward-closure, `StepStar.head`). The remaining escape-safety obligations are (a) the initial-config
>   NonEscape premise (rides the LR diagonal, inc 5) and (b) the GLOBAL-FRESH rework (ADR-0055) that makes
>   NonEscape adequate against the witnessed `handlerCount` collision — the NEXT unit (see ★ above).
> - **Restructuring** (recorded, `core-overview.md §6`): split the Operational hub (the dispatch⟂subst seam),
>   relocate `plug` LR→machine, reorg LR/Compat, prune legacy `splitAt` + the orphaned WC helpers. GATED on
>   the tree gating green (the moves touch red CalcVM/Compile/Surface imports — unverifiable until route-B lands).
>
> **Earlier landings (surface/tooling spine, committed + gated):** `Bang.Frontend.NamedCore` (ADR-0046 ①,
> the writable S-expr core, `9452660`) · `arch-check` import-direction fitness fn (ADR-0048, the Frontend/Core/Backend
> V) · `check-refs` stale-reference fitness fn + `archive/` removed (`053b79c`) · `just symbols` Lean symbol index +
> ADR-0049 (capability diagnostics via the LW pass, NOT HasCTy fusion) · the pre-commit hook now runs `just fitness`
> on EVERY commit · the Lean comment convention (`docs/notes/lean-comment-style.md`) · kernel/proof-engineer prompts
> re-pointed at the real Lean nav tools. **Lean MCP (`lean-lsp`): DEFERRED operator action** — `.mcp.json` committed,
> homelab allowlist edit UNCOMMITTED (in the homelab repo's `modules/home/claude-code/` claude-code module); needs `just rebuild` in homelab + a
> Claude Code restart to activate.
>
> **Branch:** `typed-static-r1` ← main (the dynamic-dispatch LR, green-1-sorry, is on `main` @ `4c77ba8`/`0e5e28d`).
> Whole tree RED downstream until the LR re-index + ◊5 CalcVM re-run land. **Surface design SETTLED:** ADRs 0046/0047/0048/0049.
> **Surface IMPLEMENTATION — landing (2026-06-25, parallel to the LR pivot; ADR-0048 = the library tiering):**
> - **`Bang.Frontend.NamedCore` (ADR-0046 ① — the writable IR) LANDED** (`9452660`, gated GREEN in isolation, 709 jobs):
>   named-explicit S-expr core 1:1 with the kernel AST (NVal/NComp/NHandler) + `print`/`readC` round-trip gate
>   (`read∘print=id`, #guard×3) + `elab` (name→de-Bruijn) + end-to-end `elab→Source.eval` by rfl (state-get⟶5,
>   reactive-cell⟶5, STM-abort⟶(100,0)). Notably RUNS the explicit-`cap 1` abort that hardcoded-`cap 0` Surface
>   can't emit under static dispatch (a live argument for candidate ②, the cap-inference stage).
> - **`tools/arch-check.sh` (ADR-0046/0047 ② — the import-direction fitness function) LANDED** (`20cedc2`, in
>   `just fitness`/`audit`): the V holds (Core imports neither edge; Frontend/Backend meet only at Core); apex
>   (Spec/Audit/Distribution) exempt. Mutation-tested (catches a synthetic Core→Frontend import). Pure grep, gates
>   pre-build (runs even on the mid-pivot-red tree).
> - **DEFERRED (seam-first, ADR-0048):** the physical `git mv` of Surface/Trait→Frontend, CalcVM/Compile→Backend
>   waits until each is green again (pivot collateral red); the Core-internal sweep + candidates ②(cap stage)/③(split
>   Compat) wait for `lr_sound`. ④ (EffSig fixture dedup) is low-priority.

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
◊3 ✓ CalcVM ported (GATE MET)     ── 2026-06-23. K2 Calc* matrix collapsed into ONE
                                     graded-CBPV calculated machine `Bang/CalcVM.lean`
                                     (Bahr–Hutton, invariant #4): pure CBPV + deep
                                     handlers/throws + resumptive state + transaction
                                     + ADT elims. `exec ∘ compile ≡ eval` proven via
                                     `compile_correct` + the `evalD ≡ Source.eval`
                                     bridge (`evalD_agrees_source`/`sim`/`run_evalD`),
                                     all axiom-clean ⊆ {propext, Classical.choice,
                                     Quot.sound}. K2 matrix (8 Calc* + Eval) archived →
                                     git history (ADR-0017; `archive/` removed 2026-06-25); CalcReify*
                                     reification frontier KEPT live (ADR-0015). 16-case
                                     5-axis diff-test battery (`Agree`: exec∘compile =
                                     Source.eval on ONE observable Val ⇒ false agreement
                                     unrepresentable; all `rfl`, 0-axiom). `just verify`
                                     723 jobs (732→723 = archive took). ◊2 gate held
                                     0-axiom throughout. Built across Units 1–7 (ADR-0031
                                     D4 for state/transaction resume; UNFOLD erases onto
                                     RET, not an instr — calc-derived).
◊4 ✓ LR foundation — NON-▷ FRAGMENT ── 2026-06-24 (GATE ✓ scoped, ADR-0039). `lr_fundamental`
     (GATE ✓ scoped)                 PROVEN for the non-▷ fragment (pure CBPV · functions ·
                                     non-recursive ADTs · throws): all value cases +
                                     ret/letC/force/case/split/lam/app + handleThrows, sorry-free,
                                     wired `lr_fundamental := crel_fund` (Compat now UPSTREAM of Spec).
                                     Reads the REAL proof [propext, sorryAx, Classical.choice, Quot.sound]
                                     — sorryAx ONLY from the documented ▷-subsystem. ◊2 (no_accidental_
                                     handling 0-axiom, STD trusted-three) + ◊3 (CalcVM trusted-three) HELD
                                     throughout. KEY forks, BUILD-ARBITRATED (not guessed): closed-value
                                     carrier on Krel/Srel/EnvRel (ADR-0036); arrow clause = PEELING +
                                     krel_nil_succ F-restriction (ADR-0038 — both pure forms refuted by
                                     the build). 16 proof commits f6d0ce2…69d70b1, 723 jobs green.
◊4.5 ✓ LR rebuild — lr_sound + all 3 handler kinds END-TO-END; SCOPED-SEAM **LANDED + MERGED into main @ `4c77ba8`** (gated green, 724 jobs; ◊5 `compile_correct` + ◊2 `no_accidental` HELD) → **BROAD moat** (ALL contexts incl. state-over-throws + legit handler stacking) + **ONE documented resume-edge sorry** (`krelS_splitAt_decomp` handleF-MISS = resume-through-a-wrap only, ADR-0026 descent; ADR-0043). **NOT sorryAx-zero, and now PROBED NO-GO:** the cheap typed-CrelK close (Architecture D, design-panel rec) was build-probed (`typed-crelk-probe@ffac1b0`) and REFUTED — `HasStack` pins the BOTTOM junction answer (`hasStack_append_handleF_split`, `[propext]`) but the strip's `letF` recursion needs the INTERMEDIATE `KrelS` hole typed, and there's no `KrelS⇒HasStack` bridge (the LR is one-way) → D only RELOCATES the leak. sorryAx-zero would need typing `KrelS`'s intermediate holes = the heavy index-everything reshape (4–7 sessions + frozen break), not worth one tested-descent edge. **The ADR-0043 seam is the verified-FINAL answer** (`paths/archive/PATH-cap45-finish.md`). `NoWrapMiss` predicate banked = the right primitive. (2026-06-24) ── ◊4.5a banked (main `773c5e6`): the IxFree reshape — non-▷ spine
                                     re-green sorry-free (Srel 0:=False + Vrel-U ∀j≤n + Kripke IHs, `22e1684`),
                                     `Crel_mono` ▷-anti-reduction primitive + μ intro/elim (`8513fd3`), resume
                                     infra krel_handleF* (`1af79f8`), ▷-guarded Vrel μ-clause strict-< (`642d335`,
                                     fixes the open-μ soundness hole). ◊4.5b NEARLY DONE on branch
                                     `cap45-modality` (`3345375`, NOT yet merged): the ▷ IS the CONFIG-LEVEL
                                     METERED OBSERVATION (`ConvergesC_le`; `Crel_head_step` pays the index-lift with
                                     a real machine step) — which OVERTURNED ADR-0041's "step-bounded-obs is dead":
                                     the prior explosion was eval-fuel metering; CONFIG-level localizes it (the
                                     `+K.length` refocus confines to the one adequacy bridge). CLOSED: μ-floor + ALL
                                     handler-consumer cases + krel_refl. the last sorry (handled-`up`) RESOLVED to a
                                     CORE RE-ARCHITECTURE (operator chose REBUILD over seam): the handled-`up`
                                     "designed" fix (drop splitAt=none) was BUILD-REFUTED (polarity-inverted);
                                     ~25 probes found the ROOT — our flat-CoApprox Krel ERASED Biernacki's answer
                                     type. FIX = the standard biorthogonal answer-typed KrelS (Crel⊸Crel);
                                     composition (Lemma 2) free, producer-resume one line. TERMINATION GREEN
                                     (stack-structural recursion + ▷-guarded frame bodies = existing metered-▷;
                                     lex (n,role,stackLen); NO Iris). Frozen-safe (2a, Crel sig unchanged). STEP 2
                                     = multi-session re-prove-all-of-Compat at the mutual relation (IC `krels` in
                                     flight); plan in `paths/archive/PATH-cap45-rebuild.md`, decision ADR-0041 (last amend).
                                     Prior CLOSED work (μ-floor/handler-consumer/krel_refl) re-proves at KrelS.
                                     RESOLVED 2026-06-24: the answer-typed KrelS rebuild + ALL handler-consumer cases + THROWS-producer CLOSED
                                     end-to-end (`a75f887`); (g) migration DONE (frozen Crel:=CrelK, old Krel/Srel/crel_fund
                                     DELETED, lr_fundamental:=crelK_fund); lr_sound CLOSED over a TYPED ⊑ (ctxApprox restricted to
                                     WELL-TYPED observation contexts — decision (a); the untyped form made lr_sound FALSE), on
                                     `cap45-final` (`21fecd9`), append-crux-only. LAST sorry = state/txn RESUMPTIVE composition
                                     (the resume-conjunct RELATION reshape — NOT the metering, which composes cleanly; build-grounded by
                                     `append` 2026-06-24, 6 Compat spots) — RESEARCH COMPLETE — `append` banked 9 green checkpoints (`b40981c`, branch `cap45-append2`) — throws+state+transaction ALL closed END-TO-END + STOOD
                                     DOWN at a Lean-TOOLING wall. Resumptive handlers COMPOSE in the step-indexed LR:
                                     throws + state proven END-TO-END (krelS_state_reinstall, guarded recursion on the index),
                                     transaction MATH proven (krelS_transaction_reinstall, all 3 TVar ops). That was the entire
                                     ◊4.5b research risk — DONE. REMAINING (per b431247) = ONLY 2 rare nested-handler sorrys (Compat 1131/1483: krelS_append handleF-in-Kᵢ +
                                     decomp handleF-MISS), behind a bounded `dispatch-relates-under-append` sub-lemma → sorryAx-gone =
                                     COMPLETE moat. TOOLING BLOCK SOLVED (producer up-arm → standalone crelK_fund_up; real root =
                                     vrelK_fund-inside-crelK_fund, fixed via heapRel canonical-forms inversion; Path-B GetD-free; all committed).
                                     [Historical — how the tooling block was solved:] txn
                                     integration hits the `import Mathlib.Data.List.GetD` → tips crelK_fund/vrelK_fund mutual-block
                                     termination auto-inference → timeout wall. Fix via PATH A (per-function mutual `termination_by`
                                     on HasCTy/HasVTy) or PATH B (GetD-free: prove the 4 heap facts inline / reformulate HeapRel via
                                     getElem? — lower-risk, block untouched), then RE-APPLY append's already-written txn wirings +
                                     close 2 rare nested-handler sorrys → sorryAx-gone. Fresh-context unit; resume base `cap45-append2
                                     @ b431247`; spec = task #10 + `paths/archive/PATH-cap45-resume-composition.md` + append's post-exec report. [SUPERSEDED by the SCOPED-SEAM landing — see header.]
                                     FINAL 2026-06-24: landed on `cap45-answertrack` (`39f29ff` + docs) — answer-typed KrelS
                                     rebuild + (g) migration (frozen Crel:=CrelK) + lr_sound over typed ⊑ + throws/state/txn
                                     resumptive composition ALL closed end-to-end; the resume-through-a-wrap edge is the ONE
                                     documented `krelS_splitAt_decomp` sorry (ADR-0026 descent, ADR-0043). sorryAx-zero needs
                                     typed-CrelK (build-pinned, deferred → `paths/archive/PATH-cap45-finish.md`). NOT merged: forks
                                     pre-ADR-0042 (ADR-0043 needs re-frontmatter + adr-index) and diverges from ◊5 on Spec.lean.
◊5 ✓ Compiler v0 — DONE, IN MAIN  ── `0e5e28d` (2026-06-24). source→WASM verified trusted-three over the
                                     WHOLE effect language — effect-free + ALL handlers, ungated. EFFECT-FREE
                                     (pure CBPV + ADT) compiler verified end-to-end source→WASM, AXIOM-CLEAN
                                     (`compile_forward_sim_pure` ⊆ trusted-three; zero_grade_no_code +
                                     compile_well_typed [propext]) — UNCHANGED + solid. Two-hop via the proven
                                     CalcVM (machine = the calculation's output, inv #4). ENGINE PROBE GREEN —
                                     released wasmtime 44.0.1 runs suspend/resume (Q9 RESOLVED on branch).
                                     ⚠ HANDLER EXTENSION BLOCKED — MODEL DEFECT (not proof-only): `wexec` is
                                     UNSOUND for handlers from a β/let-RESIDUAL re-compile with a non-trivial abort
                                     cont — `lowerCode (compile body []) ++ c` bakes markH savedCode=[] so a
                                     zero-shot abort stops early, bypassing `c`. Counterexample PINNED as a
                                     fail-loud rfl (`d44d90a`): `letC ((λ.handle(throws 0)(letC(raise 7)(ret 99)))())
                                     (force(thunk(ret 100)))` → Source.eval=100, Wasmfx.run=7 (WRONG). The "small
                                     run-equivalence FIX" is DEAD (general lemma FALSE — flag-before-build caught
                                     it). fix-vs-seam RE-OPENS: (FIX) thread CalcVM cont `c_cvm` into the 4 residual
                                     arms (`compile (subst v N) c_cvm` whole, inner markH captures real cont) —
                                     bounded redesign, keeps verified handlers; or (SEAM) draw v1's verified line at
                                     effect-free, handlers tested-not-verified (ADR-0026 ladder). Operator's call;
                                     RESOLVED 2026-06-24: FIX chosen + DONE — threaded the CalcVM cont `c_cvm` whole (markH captures the real
                                     cont); GAP-2 closed via a BOUNDED RE-WIRE (`evalD_complete_gen` total + `exec_wexec_sim_ok`
                                     handler-complete → compile_correct → run); `compile_forward_sim` trusted-three, all handlers,
                                     MERGED to main `0e5e28d`, independently gated. Task #40 CLOSED.
◊6   Release v0
```

> **Product-spine note (2026-06-24):** the surface **trait/law loop** (`Bang/Surface/Trait.lean`) is
> verified + GATED in the build graph (`3dbf819`) — eq→preorder→order + Int:Order proof-first, run via
> `Source.eval` (ADR-0040). The TESTED rung now BINDS its check BY CONSTRUCTION (`39c7fbd`): a law false on
> its sample is unconstructible (evidence = sample + kernel-checked `holds`), teeth mutation-tested.
> The **ADR decided-ledger is GENERATED** from frontmatter (`a496eb2`, ADR-0042; `just adr-check` = README
> current + Q⟺ADR + Status cross-refs) — ADR-currency drift is now a build failure, not a silent re-derivation.

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
- Commit `33e5349`.

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

**Product spine (surface — the rungs; PRD §3.1):**
- **rung 0 ✓ DONE** (`paths/archive/PATH-tracer-bullet.md`) — surface → graded-CBPV `Comp` → `Source.eval` → a
  VALUE. The language RUNS (pure + throws). `Bang/Surface.lean`: named AST + name→de-Bruijn lowering +
  fuel-total parser + `#guard`/`rfl` demos.
- **rung 1 ✓ DONE** (`paths/archive/PATH-rung1-state.md`) — first resumptive paradigm: State. `dispatch`
  RESUMES (ADR-0025; the closed CK focus dissolved Q12's grade tension — **no `ω`-restriction on `S`**).
  `preservation`/`type_safety` **AXIOM-CLEAN** (the 2 obligations closed: `dispatch_state_typed` keeps
  `Kᵢ`); `no_accidental_handling` 0-axiom held; State runs **from source text**
  (`state 0 in (let z = put 7 in get) ⟶ 7`).
- **rung 2 ✓ DONE** (`paths/archive/PATH-rung2-stack.md`) — verified `Stack Int` (monomorphic, ADR-0027); the
  **first concrete moat demo**. Iso-recursive ADTs (ADR-0029: sum/product/μ + fold/unfold) landed as the
  kernel data layer (`3738556` K1), metatheory **axiom-clean** (`b4adc42` K2 — preservation/progress for
  case/split/unfold via new canonical-forms inversions), Stack surface + push/pop laws **property-tested
  green via `plausible`** (`6883b61` L — the FIRST ADR-0026 *tested*-rung use; mutation-verified
  non-vacuous). ◊2 gate held on every commit (`no_accidental_handling` 0-axiom). The biggest rung yet
  (a whole ADT layer + metatheory), and it **confirmed the ADR-0029 bet**: iso-recursive made the
  metatheory cheap (syntactic type-matching, no coinduction). Q19 (laws *surface* syntax) stays partial —
  laws stated in Lean for now; the *discharge mechanism* (plausible) is now demonstrated.
- **rung 3 ✓ DONE (kernel + verified law)** (`paths/archive/PATH-rung3-ledger.md`) — verified ledger; **STM as a
  transactional handler** (ADR-0030: `state ⊗ exception`, NO new kernel primitive; privilege =
  concurrency-only, deferred). `Handler.transaction` = rung 1's state handler generalized to a heap;
  rollback is **by construction** (abort = `throws` escaping the frame, dropping the heap with it).
  Commits: `ff13252` K1 (handler + ledger runs) · `df9f9ff`/`1042540` K2 (TVarRef=int + total store fix,
  metatheory closed). **The moat CLIMBS the ladder**: `all_or_nothing_abort` is **PROVEN** (axiom-clean
  `[propext, Quot.sound]`, in `Audit.lean`) — a *verified* law, above rung 2's *tested* one. ◊2 gate held
  every commit. **Follow-ons (not blocking the GOAL, which is met):** `orElse` needs a *recovery handler*
  (the ADR's "costs nothing" was optimistic — `throws` discards, doesn't run an alternative); a
  from-source-text `atomically {…}` surface (parity with rung 1's `state … in`); general-`S` TVars
  (default-witness, ADR-0030 amendment). TVar reps are v1 simplifications (TVarRef=int, S=int, total
  default-initialized store) — see ADR-0030.
- **rung 4 ✓ DONE** (`paths/archive/PATH-rung4-reactive.md`) — reactive cell; the LAST v1 MVP rung. **Reactivity
  is EMERGENT, not a new kernel form** (ADR-0005, now empirically + formally validated): a reactive cell
  is an *unmemoized thunk over a State cell*; each `force` re-samples = pull-based reactivity. **ZERO
  kernel edits** — the rung validates the thesis rather than adding a capability. Liveness law **PROVEN**
  (`Bang.Surface.cell_reflects_latest`, axioms `[propext]`, in `Audit.lean`) — the third ladder-climb.
  Commit `1208b45`. FINDING → ADR-0005: reactivity is **load-bearing on thunk non-memoization** (now an
  asserted invariant). Push-based/glitch-free reactivity = the deferred dial. ◊2 gate held (surface-only).

> **✓✓ v1 MVP PRODUCT SPINE COMPLETE (rungs 0–4, 2026-06-23).** Four paradigms — imperative/State,
> transactional/STM, user-data, reactive — on ONE five-primitive verified kernel. The moat is demonstrated
> at BOTH ADR-0026 ladder rungs: *tested* (rung 2, `plausible`) and *verified* (rung 3 `all_or_nothing_abort`,
> rung 4 `cell_reflects_latest`, proven). The multi-paradigm thesis is shipped. Post-v1: rungs 5–8
> (systems frontier — QTT-surfaced allocator, cooperative scheduler, fs, driver) → rung 9 (xv6, the golden
> test). STM is now **writable from source** (`atomically`/`new`/`read`/`write` parse + run incl.
> abort-rollback, `06e3076`). Rung-3/4 follow-ons: **orElse** (needs *nested-transaction* semantics —
> discard the alternative's writes, Harris OR3; bigger than a "recovery handler") · general-`S` TVars ·
> push-based reactivity.

**Verification spine (kernel/compiler — the ◊ march):**
- **`paths/archive/PATH-graded-cbpv-eval.md`** — **◊2 GATE MET**: STD block + `no_accidental_handling`
  axiom-clean over the CK machine (ADR-0023/0024). Residual: `effect_sound` (Q14), `zero_usage` (→◊4).
- **`paths/archive/PATH-calcvm-port.md`** — **◊3 GATE MET (2026-06-23); path COMPLETE.** Collapsed the K3 Calc*
  matrix into one graded-CBPV calculated machine. D1=A (calculate from denotational
  `evalD`). Landed axiom-clean: pure CBPV spine (`1d15437`) + `evalD ≡ Source.eval` bridge (`a777ffa`) +
  **deep handlers throws-only** (O1 INSTALL `d995cd0`, O2 THROW abort `8780be6`) + **resumptive state —
  handlers RESUME** (ADR-0031, Unit 4, `fd2bc3d`): `evalD` threads a label-keyed `SStore` servicing get/put
  inline; the machine RESUMES via a non-discarding `OP` (shape-A, one-shot, `c` IS Kᵢ); the throws⊗state
  nesting is handled (outer `put` persists past an inner caught throw) + **resumptive transaction — Unit 5,
  `9b2d531`** (ADR-0031 D4 LANDED): `new`/`read`/`write` RESUME over a list-heap, folded in as a **parallel**
  `THeap` store (op-disjoint from state ⇒ correct-by-construction, NOT a unified sum-cell — see ADR-0031 D4).
  Two build-forced shapes: `evalD`'s op-arm is **OP-FIRST** (matches the kernel's `handlesOp` op-gating);
  the net-HStack-effect is a **two-pass composition** `netEffect = updateTxns ∘ updateStates`. Rollback is
  free (inner txn frame pops its heap on a forwarded raise; outer write persists past a caught throw).
  `compile_correct`, `evalD_agrees_source`, `sim`, `run_evalD` all ⊆ {propext, Classical.choice, Quot.sound}
  over BOTH arms; ◊2 gate still 0-axiom (independently gated on the committed tree) + **ADT eliminators —
  Unit 6, `505cf53`+`498bceb`**: `case`/`split` via runtime `CASE`/`SPLIT` instructions (non-structural
  erasure ⇒ defer to a fuel-bounded re-`compile` in `exec`, the `SUBST`/`APP` shape; resolves the Unit-2
  defer); **`unfold` ERASES onto `RET` — no instruction** (structural, the `force` precedent; an UNFOLD instr
  would be hand-added redundancy). The split is the calculation's OUTPUT, re-derived per invariant #4
  (`498bceb`). PURE reductions, `evalD` mirrors kernel `Source.step` byte-for-byte; axiom-clean, ◊2 held.
  **✓ Unit 7 — K3 COLLAPSE DONE (`87d5aeb`), ◊3 MET:** the K2 matrix (8 Calc* + `Eval`) retired to git history (`87d5aeb`)
  (ADR-0017; `archive/` removed 2026-06-25 — git is the corpus); CalcReify* reification frontier KEPT
  live (ADR-0015); 16-case 5-axis diff-test battery (`Agree M v := exec(compile M)=some[ret v] ∧ Source.eval
  M=done v` — both reps to ONE observable Val ⇒ false agreement unrepresentable; all `rfl`, 0-axiom);
  `just verify` 723 jobs (732→723 = archive took); independently gated on the committed tree.
- **`paths/archive/PATH-lr-foundation.md`** — **◊4 (ACTIVE; STATEMENTS + INFRA landed, proof BODIES remain).** Done:
  U1 helpers (`0f5891d`) · U2 `Vrel/Srel/Krel/Crel` WF defs (`25a2fdd`, THE CRUX, row-indexed ADR-0033) ·
  `group_recovers` RETIRED (`eca7587`, ADR-0032) · U4 `seq_unit` PROVEN + `NotEvaluated` def (`5042754`) ·
  U5 closed adequacy `lr_sound_closed` (`187be29`) · U6 statement+infra (`7928f02`/`b2c3c10`): `lr_fundamental`
  amended to env-closed form (ADR-0034) + `lr_fundamental_closed`/`krel_refl`/`closeC`/`EnvRel` + the
  non-binding compat cores. **THREE ◊4 frozen-statement corrections (ADR-0033/0034 + sig catches) — the LR
  headlines were Phase-A STUBS being finalised through the proofs.** **RESUME (see the PATH's resume-point
  section):** binding-former `closeC` commutation (the crux) → mutual fundamental induction → `compat_handle`
  → **Blocker 2** (the μ/▷ off-by-one at recursive types — route to the LR-relation thread) → `lr_sound`
  capstone + `zero_usage` corollary. `effect_sound` → ◊5.

**Design corpus settled (2026-06-22/23):** **ADR-0026** (correctness = ONE dispatched ladder
verified>tested>unsafe; kernel=semantics, checkers=pluggable; moat = sound floor + laddered specs;
descent explicit) · **ADR-0027** (polymorphism staged: monomorphic v1 → HM → System F) · the
design-space map (`docs/notes/design-space-map.md`) + Q15–Q20.

## Next stable checkpoint we are paving toward

**◊4 — LR foundation.** (◊3 gate met 2026-06-23; see Position block.)

Definition of stable per `ROADMAP.md`: `lr_sound`, `lr_fundamental`,
`zero_usage_erasable` proven; `Audit.lean` reports axioms ⊆ {propext,
Classical.choice, Quot.sound} for these. (`group_recovers` RETIRED — ADR-0032;
it was false-as-stated + vacuous, and v1 rollback is the txn handler. `effect_sound`
→ ◊5.) **Foundation already landed (2026-06-23):** the LR relations are real
WF defs (U1/U2), row-indexed (ADR-0033); only the proof bodies remain. Input:
the now-ported CalcVM (◊3) + the step-indexed LR machinery sketched in
`Bang/LR.lean` + the references (`references/papers/3-lr/`). The `zero_usage_erasable`
and `effect_sound` residuals deferred from ◊2 also live here (LR-flavored).

**◊3 — CalcVM ported — GATE MET (2026-06-23).** K2 Calc* matrix collapsed into one
graded-CBPV calculated machine `Bang/CalcVM.lean` (Bahr–Hutton); `exec ∘ compile ≡ eval`
proven (`compile_correct` + the `evalD ≡ Source.eval` bridge); K2 matrix archived
(ADR-0017); 16-case diff-test battery green; all axiom-clean. See Position block + the
(now-complete) `paths/archive/PATH-calcvm-port.md`.

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

DONE — de Bruijn rewrite (ADR-0020, `411ed08`) + first STD theorem:
[x] Core/Operational/Syntax/Spec rewritten to de Bruijn; 5 side-conditions GONE
[x] subst_value PROVEN (`d72199e`) — axiom-clean, zero sorry; List carrier held
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
- **`tools/check.sh` follow-up**: the grep false-green is fixed (`d72199e`), but the
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
| Q6 | Source.step deep-handler resumption | ✓ resolved — throws (ADR-0023) + state (ADR-0025) |
| Q7 | Op names string vs enum | defer (cosmetic) |
| Q8 | `group_recovers` H-K bridge | ✓ resolved — ADR-0032 (RETIRED; H-K needs Frobenius ≫ group; bounded) |
| Q9 | WasmFX target drift | recorded — ◊5 obligation (pin-to-engine) |
| Q10 | Typing rules must enforce grades | rules landed (ADR-0019); proof bodies remain |
| Q12 | Graded state handlers | ✓ resolved — ADR-0025 (closed focus, no ω-restriction) |
| Q13 | Op-granularity progress wall | ✓ resolved — CK machine + op-partial sigs (ADR-0023) |
| Q14 | `effect_sound` trace semantics | open — ◊2 non-gate residual |
| Q15 | Thunk strictness (lazy vs eager fold) | open — uniform-lazy + effect-row-gated fold pass |
| Q16 | Undecidable + unsafe = effects-with-oracles | open — Div effect + privileged prims; ◊4/◊5 |
| Q17 | Polymorphism + effect-row poly | ✓ resolved — ADR-0027 (staged: monomorphic v1 → HM → System F) |
| Q18 | Data types: ADTs, ind/coind, law attach | ✓ resolved — ADR-0029 (iso-recursive sum/product/μ) |
| Q19 | Typeclasses/traits with laws (laws surface) | partial — discharge via `plausible` (ADR-0026 tested rung) DEMONSTRATED at rung 2; surface law-syntax open |
| Q20 | Surface extensibility (pseudoinstructions/macros) | open — no primitive if composite (invariant #5) |
| Q21 | Concurrent STM (privileged shared-heap upgrade) | open — deferred (ADR-0030); privilege returns with concurrency, ◊5+ |

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

**On position SHAs.** An `@ <sha>` in the Position block marks a STABLE
conceptual waypoint — the commit where a milestone settled — NOT a live HEAD
pointer. Mid-port, HEAD legitimately runs a few commits ahead of the recorded
SHA; that is normal in-path progress, not drift. The SHA is updated when a new
checkpoint settles (the bullets above), not on every commit.
