# PATH — inc-5: the LR/Compat re-index (ADR-0054/0055 → identity + counter)

> Re-key the step-indexed LR (`Bang/LR.lean` + `Bang/Compat.lean`) to the identity-dispatch + global-fresh
> counter kernel, and close the initial-config NonEscape **diagonal**. First whole-LR green.
> SoT = ADR-0054/0055/0058 + this PATH. (Supersedes the archived `PATH-typed-lr-reindex`, the reverted
> ADR-0053 absolute-caps era.)

> **★★ CURRENT STATE (2026-06-29) — ROUTE-1 LANDED; the body below is SUPERSEDED HISTORY (kept for resume detail / git).** The detailed live state leads in `CONTEXT.md` + tasks #14 (done-arc) / #72 (the one open seam). One-screen:
> - **ADR-0058 route-1 IMPLEMENTED** (un-freeze `CrelK`/`KrelS` → carry the real counter `g` INTERNALLY → `Crel`/`Spec` frozen-safe; `Canonical`/`CapsBelow`/`run_bump` DELETED; wall-halves `pop_route1`+`perform_escape_vacuous` axiom-clean). The dead `inc5-lr-reindex`/`inc5-comp-grind` branches are superseded; route-1 lives on the inc-6 line.
> - **Bang.LR green+sorry-free (`7aa5ee1`) → Bang.Compat green (`89c8c08`, cap-binding `compatK_handle*` + novel `KrelS_g_cast` axiom-clean) → Bang.Spec green (`7574a5b`)** — all PUSHED, off `fd7a8d2`.
> - **v1 SOUNDNESS HEADLINES CLEAN:** `progress` `[propext, Quot.sound]` + `type_safety` `[propext, Classical.choice, Quot.sound]` — sorryAx-FREE, #35-FREE (ADR-0063 re-point onto `progress'_proof`/`type_safety'_proof`).
> - **THE ONE OPEN SEAM = `lr_sound`** (◊4 binary-LR contextual-equiv, SEPARATE from v1 soundness) = task #72: the labelling-vs-closure cap-rep seam (Q22) — route-1 `CrelK` raw-focus vs the correct reshaped `converges_plug_iff` (build-witness `scratch/AdequacySpike.lean`); design-first (CrelK-reshape vs plug-congruence); + a #35 post-v1 boundary.
> - `Bang.Audit` still RED — blocked SOLELY by `Bang.Surface` (inc-7), NOT the soundness spine.

## Decisions — ALL build-arbitrated in de-risk (don't relitigate)
- **Diagonal route β** (unary `WellScoped` reachability invariant; `nonEscape_of_fwd_invariant` proven green) —
  NOT the binary-LR α path. The diagonal is a UNARY reachability fact (every reachable `perform` resolves).
- **Machine-shaped KrelS** — observes `(counter, K, c)` with cap-substituted focus + canonical ids (what the
  machine reaches), NOT source-shaped. `krelS_refl` from id-agnostic `HasStack` adapts cleanly.
- **id-renaming invariance** for the `plug`/`run_plug` bridge (over re-base [reopens the ADR-0041 +K.length wall]
  / restrict [bakes normalization]). Primitives `plug_reId` (§2) + `splitAtId_rename` (§3) proven green.
- **`VcapFree c` side-condition** on the diagonal: `HasConfigTy (0,[],c) ⊥ (F q A) ∧ VcapFree c → NonEscape`.
  The bare form is FALSE (a hand-written `vcap 5` literal types but runs stuck); VcapFree is true-by-construction
  (elaborator emits `vvar` not `vcap`, Core:86), discharged by the elaborator at inc-7. (Operator-deferred (b):
  make raw source `vcap` untypeable so the precondition vanishes — task #18, post-(a), likely inc-7.)
- **`closeC_handle*` → lam-shape binder-descent** (the ADR-0054 no-shift win materializes; de-risked in DiagonalProbe).

## State @ `19798fb` (red-WIP by design; LR builds RED, 41 errors)
- De-risk probes (committed): `2282ac2` DiagonalProbe (route β · closeC_handle · VcapFree) · `4005e52`
  PlugMintWall + RenameInvarianceProbe (renaming primitives §2/§3).
- DONE + CLEAN: form-(b) machine-shaped KrelS def core (LR 433–647) + metering-spine re-key (`2ed9078`) ·
  downstream `KrelS_mono`/eff handleF lemmas (`19798fb`). Nice simplification: `dispatchOn` outputs stay the
  2-tuple `EvalCtx × Comp`, so the counter lives only in the nil/CrelK metering configs.
- **run_plug DONE** (`f88879a`, kernel-engineer `runplug`, worktree `/srv/share/projects/lang-bang-runplug`):
  `run_plug_reshape` PROVEN axiom-clean ⊆ {propext, Quot.sound}, zero sorry — TRANSCRIBE into `Bang/LR.lean`.
  §4 RESOLVED: plug+reshape erase frame ids → KrelS observes the CANONICAL config (the one remaining LR-side
  step = KrelS stack-id-agnosticism, HasStack-id-irrelevance). Its `RunPlugReshapeProbe` probe. Contract:
  `Config.run (n + C.length) (0,[],plug C c) = Config.run n (handlerCount C, canonStack C, capSubstInto C c)`
  + renaming-invariance bridging `canonStack C ↔ C`. When it delivers, transcribe `canonStack`/`capSubstInto`/
  `run_plug_reshape` into LR.lean's `run_plug` (~207), discharging the `run_plug`/`converges_plug_iff` sorries.

## Remaining surface (41 errors — the continuation worklist)
1. **Mechanical config-tuple re-keys** (quick): `crelK_ret` (~791), `not_convergesC_le_of_stuck` (782),
   `lr_sound_closed` (1042, the adequacy capstone) — thread `([],c)`/`(K,c)` → 3-tuples (counter = `handlerCount K`
   or `0` for nil).
2. **Positional-cap stuck-half cluster** (~952–1019: `not_converges_up_nil`, `config_stuck_up_splitNone`,
   `not_convergesC_le_up_splitNone`): use old `cap : Nat` + DELETED `absSplit` → NAMED-SORRY them (they reconnect
   via the diagonal's WellScoped/`splitAtId` story, not the core LR — don't re-key the dead `absSplit`).
3. **`crelK_fund` + `krelS_refl` handleF arms** (deepest downstream): re-key to the machine-shaped handleF clause
   (id binder · `n₁=n₂` · `dispatchOn n` · the resume conjunct's new shape). `krelS_refl` supplies `nh=nh'` (rfl,
   self-relation). `crelK_fund` up/perform case is reshape-adjacent → named-sorry until run_plug + diagonal land.

## Finish line
integrate `run_plug` → `lake build Bang.LR` green-with-named-sorries → `Bang.Compat` re-key (incl. the
`closeC_handle` lam-shape rewrite) → **diagonal Phase 3** (`HasConfigTy ∧ VcapFree → NonEscape` via WellScoped
[DiagonalProbe §B] + the run_plug bridge) → ADR cluster (renaming-invariance over re-base/restrict + machine-shaped
KrelS + VcapFree side-condition). Whole-LR-green = builds + the 2 seamed `:1741`/`:1809` (ADR-0043 descents, stay
seamed) + the diagonal CLOSED. Then inc-6 (CalcVM route-B → whole-tree green) · inc-7 (Surface).

## ★ STATE UPDATE (2026-06-26) — run_plug integrated · Bang.LR GREEN · diagonal ASSEMBLED (~80%)

Commits on `inc5-lr-reindex`: `fa3046a` · `56a2e1a` · `c3e4aed` (+ the new `the new `Bang.Model` module` diagonal).
- **Bang.LR GREEN** (41 errors → 0), 2 named sorries: `seq_unit_proof` (cap-subst-commutes residual, OFF the
  critical path) + `crelK_ret` handleF arm (the run-renaming gap below). `run_plug`/`converges_plug_iff` PROVEN
  (converges_plug_iff was a STATEMENT FIX — old RHS `(handlerCount C, C, x)` is FALSE for a cap-using focus
  [raw `vvar 0` cap is stuck, only `vcap` fires]; faithful RHS = the canonical reshape config).
- **THE DIAGONAL ASSEMBLED** in NEW `the new `Bang.Model` module` (route β): `diagonal : HasConfigTy (0,[],c) ⊥ (F q A) ∧
  VcapFree c → NonEscape (0,[],c)` closes with NO own sorry → reduces the soundness payoff to exactly 2
  obligations. Architecture lemmas axiom-clean. `preservation_returnEscape` ALREADY proven (NonEscape-preservation free).

★ **THE RUN-RENAMING KEYSTONE** (one lemma unblocks much): the DYNAMIC half — `Config.run` commutes with an
injective id-renaming (the handlerCount counter-shift) — is the keystone for `crelK_ret` handleF + `crelK_fund`
up/perform + the `converges_plug_iff → krelS_refl` bridge in `lr_sound`. RunPlugReshape gave only the STATIC
halves (plug/splitAtId). This is the dynamic-half MIRROR of runplug's work.

## ★ NEXT DISPATCH PLAN (turn-key — 3 units, fresh ICs, full budget)
- **(B1) run-renaming keystone → KERNEL-ENGINEER** (dynamic-half mirror of runplug; de-risk in scratch then
  the IC integrates). Unblocks the most — do FIRST / in parallel.
- **(A) Bang.Compat re-key → PROOF-ENGINEER** (103 errors: mechanical config-tuples + `closeC_handle` lam-shape;
  named-sorry the `crelK_fund` deep arms pending B1, integrate B1 when it lands). Largely mechanical.
- **(B2) close the diagonal's 2 obligations**: `wsCfg_step` (the MUTUAL `WellScoped∧HasConfigTy` preservation;
  pop-escape arm = the ⊥-row return-escape — a research-grade PROOF, not a design fork [effect_sound at ⊥];
  the 2 obligations ride TOGETHER, `preservation_proof`'s NonEscape-bundling makes it circular) +
  `handlesOp_of_hasConfigTy` (typing inversion, smaller). Closes the soundness payoff.
- THEN the ADR cluster (renaming-invariance + machine-shaped KrelS + VcapFree) → inc-6.
Worktrees live: `lang-bang-inc5` @ inc5-lr-reindex (the LR work), `lang-bang-runplug` @ kernel-runplug
(runplug's probe — keep until B1/Compat confirm run_plug is fully integrated, then teardown).

## ★ UPDATE (2026-06-26) — unit A re-scoped: mechanical banked, deep block is KEYSTONE-GATED
compat (unit A) banked the MECHANICAL Compat surface (≤1090): `dd6b297` (swept dead cap-shift theory, −99 LOC)
+ `d56f471` (3-tuple Config + vcap/perform/handle-binds-at-0 + closeC_handle lam-shape + the compatK_* frame
cores). But the DEEP BLOCK (Compat 1091-2080) is NOT mechanical — it's the **keystone-gated fundamental-theorem
re-derivation**: `staticSplit`/`krelS_staticSplit_decomp` (the positional cap-countdown decomposition that
`crelK_fund`/`crelK_fund_up`/`krelS_refl` all consume) are GONE; `splitAtId` is identity-keyed, so the whole
decomposition needs **re-derivation around `splitAtId`** — exactly what B1's run-renaming keystone underpins.
NB `krelS_staticSplit_decomp`/`crelK_fund`/`krelS_refl` live ONLY in Compat (no LR analogue to transcribe).
- **Revised dispatch:** (B1) run-renaming keystone [in flight, `rename`] → THEN (A2) the Compat deep-block
  re-derivation [post-B1 PROOF-ENGINEER: re-derive the `splitAtId`-decomposition + crelK_fund/krelS_refl using
  the keystone; compat's STOP-and-SHOW characterization is the map] alongside (B2) the diagonal's 2 obligations.
- **arch-check gap (fold into inc-5 merge):** `tools/arch-check.sh` doesn't classify the new `Bang.Model`
  module (fitness fails → branch ICs use --no-verify). Classify Model as the backend/LR edge at merge.

## ★ B1 DONE (2026-06-26) — the run-renaming keystone, axiom-clean
kernel-engineer `rename`, `1ff9a60` on `kernel-rename` (worktree `/srv/share/projects/lang-bang-rename`),
its `RunRenameProbe` scratch probe. The DYNAMIC half (Config.run id-renaming invariance) PROVEN — unblocks A2 + B2 + the 2 LR sorries. CONTRACT to integrate (all defs in-probe):
- `renameCfg σ (g,K,c) = (σ g, renameK σ K, renameC σ c)`; `renameR σ` on Result.
- `run_rename (σ inj) (n cfg) (shift hyp: ∀ k≥cfg.1, σ(k+1)=σk+1) : Config.run n (renameCfg σ cfg) = renameR σ (Config.run n cfg)`.
- `run_rename_converges (…)` : renamed-cfg co-converges with cfg — THE form the 3 sites read off
  (crelK_ret handleF · crelK_fund up/perform · converges_plug_iff→krelS_refl bridge).
- σ HYPOTHESIS (cleaner than feared): ONLY injectivity + shift-on-fresh-region. WellCounted NOT needed for the
  lemma — it's the CONSUMER's job to supply such a σ (canonical↔original perm + tail shift IS one).
- Supporting: `splitAtId_rename`/`dispatchOn_rename`/`idDispatch_rename`/`renameC_subst`/`renameC_shiftFrom`/
  `renameC_substFrom`/`renameH_label`/`handlesOp_renameH`/`step_counter_le`.

## ★ REMAINING — the inc-5 home stretch (ALL unblocked by B1)
- **A2 — Compat deep-block re-derivation** [PROOF-ENGINEER on inc5-lr-reindex]: re-derive `krelS_staticSplit_decomp`
  around `splitAtId` (was positional `staticSplit`) + close `crelK_fund`/`krelS_refl` + the 2 LR sorries
  (crelK_ret handleF arm) USING `run_rename_converges` + the supporting lemmas. compat's STOP-and-SHOW is the map.
- **B2 — the diagonal's 2 obligations** [PROOF-ENGINEER, Bang.Model]: `wsCfg_step` (mutual WellScoped∧HasConfigTy
  preservation, the ⊥-row return-escape) + `handlesOp_of_hasConfigTy` (typing inversion).
- THEN: integrate run_rename + run_plug from their scratch probes into LR/Compat · classify Bang.Model in
  arch-check · the ADR cluster (renaming-invariance + machine-shaped KrelS + VcapFree) · whole-LR green = inc-5 DONE.

## ★ A2 DESIGN FORK RESOLVED (2026-06-26) — the sparse-stack counter, route (a)
A2 found that global-fresh makes the machine reach SPARSE stacks (gensym ids, handlers pop leaving gaps), so
form-(b)'s `CrelK` observing `(handlerCount K, K, c)` is a latent inconsistency: `handlerCount K` (a dense
count) can collide with a live sparse id, exposed by the `crelK_ret` handleF pop (lands at `handlerCount K'+1`,
IH observes `handlerCount K'`). RESOLUTION = **(a)**: thread a `StackBelow (handlerCount K) K` density +
LR-local value-cap-scopedness invariant through `crelK_ret`/`crelK_fund`/`krelS_staticSplit_decomp` (CrelK/KrelS
FROZEN; invariant = consumer-supplied hypothesis, STATEMENT_CHANGE_OK on the supporting lemmas). This is NOT a
new design — it's **runplug's §4 canonical-observation made explicit** (the LR observes the dense canonical
config; consumers build it via canonStack/reshape, dispatch-reinstall preserves density). GUARDS: if it forces
a premise onto the FROZEN `lr_sound`/`lr_fundamental` → STOP-and-SHOW (shouldn't — density is internal). RESERVE
= **(b)** [change CrelK/KrelS def to a fresh-id counter — re-does form b, OPERATOR-level] only if (a) walls. run_rename
banked into LR §5.0a′ (`0b739db`, axiom-clean). A2 is a multi-session re-derivation.

## ★ A2 STAND-DOWN (2026-06-26) — LR re-key BANKED; Compat deep block handed off
compat2 banked (inc5-lr-reindex, LR GREEN, axiom-clean): `0b739db` run_rename integrated · `d91ef1c` density-(a)
machinery (`bumpσ`/`CapsBelow`/`run_bump_converges`/`Canonical` — the counter-bump bridge, non-escape-independent,
KEPT as prepared tooling) · `8c30f06` crelK_ret RESTORED to the GUARDED explicit-premise form (axiom-clean; explicit `CapsBelow 0 v`
premise = the VISIBLE non-escape obligation, NOT a sorry — discharged when B-occ is IMPLEMENTED (task #23);
ADR-0057 ACCEPTED `dfe8e3d` decides the discipline, likely making it a corollary via the dissolution lemma) ·
`8abda91` `krelS_handlerCount_eq` handleF-tail re-key (`.2.1`→`.2.2.1` for the new `krelS_handleF` shape).
**LR GREEN, exactly 1 sorry (seq_unit_proof, LR:1243, pre-existing off-critical-path).** Density-(a) machinery
in use. Compat red-WIP @ `8abda91`.
**Compat deep block is a SINGLE RED FILE** (103 errs) — NOT incrementally build-verifiable (clearing one error
unmasks a cascade); needs CONTIGUOUS chunks landed before the count moves. Don't scatter unverifiable edits.
**NEXT LR UNIT — the splitAtId decomp** (build-ready design, compat2): re-derive `krelS_staticSplit_decomp` around
`splitAtId` (identity-keyed; structurally CLEANER than the old positional countdown). Induct on K₁, parallel K₂
via KrelS (handleF forces nh₁=nh₂). **letF/appF**: `splitAtId (fr::K') cap = (splitAtId K' cap).map (prepend fr)`,
recurse + rebuild via `krelS_letF`/`krelS_appF`. **handleF/handleF**: cap-countdown → ID TEST. HIT (nh=cap):
`splitAtId = some([],h,K')`, resume conjunct = the clause's `hres` directly. SKIP (nh≠cap): recurse, rebuild via
`krelS_handleF_intro` — **the old 1628 sorry lives here** (skipped handler's resume must RELOCATE to the recursed
prefix; residual = the `dispatchOn_append_outer` + `krelS_append` nested-handleF pattern, likely closeable or a
documented residual). **The old MISS arm (answer-type-determinism wall) DISSOLVES** — `splitAtId` never tests
`handlesOp`, pure id match. Order: #3 cluster (1091-1500) → the decomp → `crelK_fund`.
**THE FROZEN-lr_sound GUARD bites at `crelK_fund`** (NOT the decomp — that's stack-structural, no CapsBelow): its
up/perform arms produce the resume `r₁`/`r₂` that feed crelK_ret's `CapsBelow 0 v` premise. If crelK_fund discharges
it internally (observation contexts canonical-by-construction) → clean, NOTE it. If it must propagate UP to frozen
`lr_sound`/`lr_fundamental` → **STOP-and-SHOW** (lr_sound sound only for non-escaping contexts = the ADR-0056
question). **DISPATCH TIMING**: best AFTER ADR-0057, so the crelK_fund value-cap premises close in one pass.

## ★ COMPAT DEEP BLOCK (2026-06-26) — Units 1+2 GREEN; Unit 3 = the crelK_fund crux (B-occ convergence)
compat-decomp banked `285338a` (inc5-lr-reindex, **Compat.lean only — Spec.lean byte-untouched, verified**).
Error count 85→36; the ENTIRE KrelS-relational layer + decomp (1067-1665) GREEN.
- **Unit 1 (mechanical id-threading) DONE green**: handleF 1→2-arg (id nh), dispatchOn 4→5-arg (id n),
  resume-cfg `Config`→`EvalCtx×Comp`, `krelS_handleF` `.2.2`→`.2.2.2`, threaded through all the `krelS_*` lemmas.
- **Unit 2 (THE CORE — `krelS_splitAtId_decomp`) DONE green** except ONE documented residual: the SKIP
  resume-conjunct relocation (= the old 1628 sorry, identity-keyed; the inverse of `dispatchOn_append_outer`,
  doesn't factor in general — the SAME single residual the positional version carried). **The MISS answer-type-
  determinism wall DISSOLVED as designed** (splitAtId never tests handlesOp).
- **Unit 3 — WALLED at frozen lr_sound (the guard fired, STOP-and-SHOW).** The 36 remaining errors = the Unit-3
  consumer block (≥1677) + pre-existing :896. `crelK_fund`'s 3 obligations all propagate up: (1) cap-RESOLUTION
  (perform arm) = `splitAtId K₁ m = some` ∧ handlesOp = `CapResolves K₁ m ℓ op` = NonEscape; (2) value
  `CapsBelow 0` + counter-bridge (resume→guarded crelK_ret, via run_bump); (3) cap-BINDING subst (compatK_handle*
  substitutes `vcap g ℓ`, g=handlerCount K — needs the cap-substituted body parameterized by the minted id =
  crelK_fund handle-case reshape + EnvRelK). Held as named sorries.

**THE CONVERGENCE + THE INC-5 ENDGAME**: all 3 obligations = the ADR-0056/0057 escape discipline (B-occ). They
propagate to frozen lr_sound ONLY because inc5-lr-reindex's HasCTy lacks B-occ's `¬LabelOccurs` premise (it's on
`bocc-spike` @ `075f894`, phase 1). bocc-impl independently found NonEscape IS the typed-LR fundamental theorem
(Shape B), B-occ the enabler. So the **ENDGAME** = (i) integrate B-occ phase 1 (bocc-spike: Syntax premise +
`LabelOccurs` + Metatheory fixups) into inc5-lr-reindex; (ii) retry Unit 3 — cap-resolution discharges via B-occ
(perform-after-pop contradictory inside the crelK_fund induction), CapsBelow via run_bump, cap-binding via the
EnvRelK reshape. **OPEN QUESTION (build-confirmable)**: does Unit 3 close WITHOUT a frozen lr_sound change
(hypothesis: the B-occ-strengthened HasCTy hypothesis carries it), or does it need a NonEscape premise on
lr_sound (operator-level STOP-and-SHOW)? Units 1+2 are banked + won't need redoing. (Integration note: bocc-spike
+ inc5-lr-reindex both touched Compat.lean — the merge reconciles bocc-spike's 5 pre-threaded arms into inc5's
re-derived decomp; the kernel premise is additive.)

### ★★ SHARPER VERDICT (compat-decomp, VERIFIED by attempting Unit 3) — the real wall is DENSITY, not cap-escape
The upstream wall is the **`ret` case**, not perform: guarded `crelK_ret` (LR:1816) needs `Canonical K₁ K₂`
(dense ids), but `CrelK` (FROZEN — the `Crel` target `lr_sound` consumes) = `∀ D K₁ K₂, KrelS … → CoApproxC_le`,
so crelK_fund's arms (after `rw[CrelK]; intro D K₁ K₂ hK`) get ARBITRARY KrelS-related stacks — and **KrelS does
NOT imply Canonical** (sparse gensym ids: a KrelS stack can carry id 5 where handlerCount=2; KrelS forces nh₁=nh₂
+ kinds, not density). Even the SIMPLEST (`ret`) case can't supply Canonical; `crelK_ret` has ZERO green
consumers (the density-supply pattern was introduced by the guarded-form decision, never established). **This is
a DENSITY problem SEPARATE from cap-escape — B-occ (`¬LabelOccurs` on answer types) does NOT make a sparse stack
dense, so route-(a)'s "consumer supplies density" bet is in doubt.** Routes (compat-decomp's, verified): (1)
`CrelK` quantifies over Canonical = FROZEN Crel/Spec.lean change → ADR + STATEMENT_CHANGE_OK; (2) a
Canonical-reachability lemma (the stacks lr_sound actually instantiates CrelK at are Canonical — hard, the mutual
block re-instantiates at handleF::K sub-stacks); (3) B-occ/dissolution makes Canonical derivable at use sites
(the density-(a) hope, cast in doubt). Possible (4): re-derive crelK_ret WITHOUT the Canonical premise (the
guarded form may be over-strong — handle the +1 shift locally via run_bump, not global density). **inc5-endgame BUILD-CONFIRMED (`e909e73` scratch/CanonicalWallProbe.lean): routes 3 + 4 BOTH FAIL.** Route 3 —
`density_bites` (green): `¬Canonical [handleF 5 (throws ℓ)]` (Canonical needs `n<handlerCount`); `krelS_handleF`
(LR:1589) places NO `n<handlerCount` bound, so a KrelS-related sparse stack is self-relatable yet NOT Canonical —
B-occ is orthogonal to id-density. Route 4 — `crelK_ret`'s `hcan` is LOAD-BEARING at the handleF-pop `+1` bridge
(LR:1869-1895: pop keeps `g=handlerCount K'+1`, tail IH at `handlerCount K'`; bridge = `Canonical.capsBelow →
run_bump_converges`); drop it ⇒ the pop breaks. Necessary, NOT defensive. ⇒ closing binary-LR `lr_fundamental`
needs `Canonical` for arbitrary KrelS stacks, neither derivable (3) nor removable (4). **OPERATOR-LEVEL decision,
route 1 or 2, DEFERRED to inc-6** (binary LR = contextual equivalence, not the soundness payoff): (1) CrelK/KrelS
quantify over Canonical = FROZEN Crel/Spec.lean change + ADR + STATEMENT_CHANGE_OK; (2) a Canonical-reachability
lemma (hard — `lr_sound` Spec:192 instantiates CrelK at the observation context `C C` via `krelS_refl`, needing
its own Canonical-supply). inc5-endgame parked it + moved to the diagonal soundness path.

### ★★★ REFRAME (inc5-endgame, build-grounded `4178ed9`) — soundness is the DIAGONAL, not the binary LR
inc5-endgame integrated B-occ (`4178ed9`: `git checkout 075f894 -- Bang/{Syntax,Metatheory,BoccRegress}.lean` —
green except Compat; **Bang.Model still closes**, the additive premise didn't break the diagonal) and verified:
the SOUNDNESS payoff (`type_safety`) goes through the DIAGONAL (`Bang.Model`), SEPARATE from the binary LR
(`crelK_fund`/`lr_sound` = contextual equivalence). cap-resolution is NOT the binary-LR blocker — it rides
stuck-stuck vacuity (`not_convergesC_le_of_stuck`, LR:1799); B-occ isn't even present at the premise-free
`crelK_fund_up` node. **So the entire SHARPER-VERDICT crelK_ret↔CrelK density wall is on the BINARY-LR path, now
DEFERRED** (a separate inc-6-compiler-path deliverable; Units 1+2 decomp banked + load-bearing).
**THE SOUNDNESS PATH = the diagonal's 2 sorries** (`handlesOp_of_hasConfigTy` Model:147 [needs `concat_*_interface`
infra mirroring `concat_throws_typed`, returning the `hiface` premise discarded at Metatheory:1789] + `wsCfg_step`
pop-escape Model:170), both B-occ-shaped + axiom-clean-adjacent (`#print axioms`: only `diagonal` carries sorryAx,
from these 2). Closing them = diagonal/NonEscape/`type_safety` **sorryAx-clean**. wsCfg_step's lemma is
NON-PERFORMABILITY (`¬LabelOccurs ℓ A ⟹` a type-A value can't PERFORM ℓ ⟹ cap inert past the handler), NOT
syntactic vcap absence (FALSE — bocc-impl's carry-drop). When the binary LR is eventually resumed: FIRST
build-confirm whether `crelK_ret`'s guard (Canonical+CapsBelow, added defensively at `8c30f06`) is over-strong
(route 4) before any frozen change.

## ★★★★ REGRADE + KEYSTONE (2026-06-27) — the "2 sorries" collapsed to ONE coherence keystone; PIECE 1 banked, PIECE 2 pinned

The "★★★ REFRAME — 2 sorries" framing above is SUPERSEDED. `handlesOp_of_hasConfigTy` closed; `wsCfg_step`'s
typeless POP arm was machine-WALLED (`escapeB_app` refuted the ⊥-row/B-occ approach — **escape is grade-`q=0`-dead,
not row-absent**). So `WScfg` was **REGRADED (ADR-0061)**: typeless `LWSC/LWSK` → graded `LWSCg/LWSKg` +
stratified freshness (`CapsBelow`/`StratFresh`/`FreshCfg`). The v1-close grind on the regraded invariant:
- **#1 `freshCfg_step` DONE** axiom-clean — FreshCfg gained the flat `∀p∈capsK K, p.1<g` freshness-completeness conjunct.
- **#2 `lwskg_pop_fresh` DONE.**
- **#3 `lwsvg_closed_regrade` REFUTED** (scale-gates couple grade↔liveness even for closed values — kept witness `d81515c`).
- **THE KEYSTONE (#51):** the carried `LWSCg` was DECOUPLED from the bundled `HasCTy` ⟹ spurious-live caps only the
  grade catches. FIX = WScfg carries `LiveCapsResolveC`+typing and **DERIVES a coherent `LWSCg` by construction**
  (the `of_typed_live` engine: grades=typing-grades; dead values route to `vcap_dormant`, no resolution). Symmetric
  stack carrier `LiveCapsResolveK`. ENGINE + RESHAPE landed axiom-clean (`798f04e`).

### PIECE 1 — DONE, GATED, SECURED (`0acfd6b` on inc5-lr-reindex)
`LiveCapsResolveK` threaded through `WScfg` (`ab6ffd2`) + the POP-tail ripple (`0acfd6b`): `liveCapsResolve{V,C}_pop`
+ `liveCapsResolveK_rehome` REPLACE `lwskg_pop_fresh` as the POP building block. Build green (710 jobs), diagonal
`[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx = PIECE 2 + #35 DISPATCH, accounted), pushed to origin.

### PIECE 2 — the remainder = #4 (`lwscg_returnEscape`) + #5 (`lwsg_step_nonperform`) UNIFIED. Pinned, de-risked, NOT yet ground.
- **Statement TRUE** (refute-tested): both escape attempts — var0-drop and destructure-drop — die because the drop
  propagates grade `0` back to M's returner (via `NoZeroDivisors` + `q_or_1 ≠ 0`). The coupling is tight.
- **Axis = CARRIER (term cap-liveness), NOT type-occurrence.** WHY (load-bearing — do not relitigate): a live binder
  of type `U {ℓ} Int` is SOUND (a dormant thunk-cap, guarded from escape by B-occ on the *answer* type) yet has
  `labelOccurs ℓ (U {ℓ} Int) = true` — so it REFUTES any type-occurrence Γ-premise (`γ[i]≠0 → ¬labelOccurs ℓ Γ[i]`).
  The carrier only sees vcap LITERALS; var-0's thunk materializes only at REDUCE ⟹ var-0 is NO carrier obligation,
  so the carrier handles the `U {ℓ} Int` case for FREE where type-occurrence chokes. (This `U {ℓ} Int` case is
  "exactly the place the two prior refutations lived" — stay on the carrier, never touch `labelOccurs A` for the intermediate.)
- **The pinned IH = a CARRIER-SUBST preservation lemma** (the shared #4+#5 core): the returnEscape walls
  (letC/app/case/split) all reduce to re-homing the closed LET-HEAD `M : F q1 A`; `N` re-homes structurally (own
  vcap literals; var-0 a vvar = no obligation). M-coupling: `M`'s value substituting into a grade-live var-0 of a
  `(¬ℓ≤φ, ¬labelOccurs ℓ B)`-clean `N` is impossible — the cap must surface in N's result/row (B-occ/row kills) or
  force the grade to `0` (dormant). Candidate, refute-tested clean: **"carrier-K + w-carrier-clean → carrier of
  `d[w/k]`; dead positions discard `w`"** (dead vacuous via the grade gate; live discharged by w's carrier).
- **NO kernel dependency** (the big de-risk): the carrier-subst rides EXISTING `Bang/Metatheory.lean` substitution
  infra — `HasCTy.subst_closed` :483, `HasCTy.subst_gen` :1286, per-case `subst_{letC,app,case,split}_case`
  :1052-1232. Model-level, no kernel-engineer, no frozen-change ADR gate.
- **REMAINING = the multi-session GRIND**: the carrier-subst lemma over `subst_gen` + threading it through the ~21
  `returnEscape`/`REDUCE` cases. Closing it ⟹ `lwsg_step_nonperform` closes ⟹ `type_safety` is sorryAx-on-DISPATCH(#35)-ONLY.

### Resume protocol
- **Sole inc5 writer = pe-coh-core (STOOD DOWN at `0acfd6b`).** Next writer needs explicit ack-before-spawn.
- Resume EITHER by re-activating pe-coh-core (thread; carrier-axis context compounds) OR re-ground a fresh
  proof-engineer from THIS section + ADR-0061 + the `of_typed_live` engine + `LiveCapsResolveC/K` in `Bang.Model` (inc5-only module).
- **Before the grind: refute-test the pinned carrier-subst IH** (the prior refutations lived on this axis). Flag
  kernel-engineer ONLY if a genuine HasCTy-grade-structure lemma surfaces (not expected — infra is present).
- Worktree `lang-bang-inc5` @ `inc5-lr-reindex`. Deferred-on-inc5: the ADR-0061 invariant-evolution update (do at the keystone checkpoint).

### PHASE A progress (2026-06-27, `ce69954`) — signature PINNED + shape-confirmed; PROVE mapped, grind in flight
The carrier-subst lemma is **stated, refute-tested, and both shape choices confirmed** (banked `ce69954`, build green,
the 2 new sorries unconsumed so the diagonal axiom set is unchanged). PROVE is the multi-session grind.
- **Signature** `liveCapsResolveC_subst_gen` (in `Bang.Model`): `(hzsf : ZeroSumFree Mult)` + closed-`v` `hcl` +
  `hgate : slotGrade γ_full |Δ| ≠ 0 → LiveCapsResolveV K hv` + `hcres : LiveCapsResolveC K hc` →
  `∃ d' : HasCTy (Sgrade …) … , LiveCapsResolveC K d'`. Plus the mutual VALUE twin (`hvres` unconditional).
  - **(A) GATE** (not unconditional v-clean): dead binder (slotGrade 0, via ZeroSumFree) discharges with no v, once, inside the lemma.
  - **(B) EXISTENTIAL** (not indexing `subst_gen`'s opaque output): FORCED — emitting the carrier from `subst_gen` would
    invert the import direction (`Bang.Metatheory` must stay carrier-agnostic; arch-check guards it). Consumer is `∃ d'` anyway.
  - Refute-first found the `ZeroSumFree` need (without it, two live occs with cancelling grades fake a dead slot).
- **PROVE structure** = port `lwscg_subst_gen` (`Bang/Model.lean :2575`) + carry typing existentially (obtain the recursive
  `∃ d'`, repack via the HasVTy/HasCTy ctor + the carrier ctor). The typing-rebuild ~doubles the ~110-line template.
- **Helper inventory** (most EXIST, reusable): `Sgrade_vvar_ne` (surviving-var leaf, hzsf) · `Sgrade_cons` (binder reshape) ·
  `cov_add_*`/`cov_cons`/`cov_smul` (coverage threading) · `Sgrade_hadd`/`Sgrade_hsmul` (binary formers).
  **ONE missing:** `Sgrade_zeros` (inert leaves vunit/vint/vcap, grade `zeros`) — pure `List.replicate`/`eraseIdx` plumbing,
  needs the exact `List.eraseIdx_replicate`/`getElem?_replicate` names (loogle, ~10 min; NOT a design issue). Land it FIRST.
- **Gated-position discharge (the crux, confirmed on paper):** at ret/app/case/split split on the LOCAL `q`. `q=0` → dormant
  builder, no v. `q≠0` → derive `slotGrade γ_full |Δ| ≠ 0` from the local contribution via `hzsf` → fire `hgate` → v-clean.
- **SCOPE:** value layer 9 cases + comp layer 12, each an existential repack + grade plumbing. **Grind value-layer-first.**
- **hcl watch-item** (refute-test in PHASE B threading): `v` closed should discharge via "reachable machine values are closed"
  at the live re-home sites; if a live site has non-closed `v`, the closedness hypothesis is too strong → revisit the signature.

### PHASE A grind state (2026-06-27, `b8bb04b`) — recursor harness + 9 value arms + 2 comp arms; build-corrected twice
The `cases hwres`+recursion approach is BUILD-PROVED IMPOSSIBLE (`4a4bb9a`): the carrier is indexed by a PROOF (`hw`),
so the structural-recursion compiler can't extract a sub-derivation from a Prop-indexed sub-carrier. FIX = explicit recursor
+ motives (the `subst_gen` pattern). Lineage `4a4bb9a → 5d5c795 (VcarrierSubstMotive/CcarrierSubstMotive) → e2a8a86 (recursor wired, 21 sorried) → 83d6ce7/7a9414d/88e7a2a (9 value arms real) → 139b3af (gating fix) → b8bb04b (force/unfold comp arms)`.
- **TWO build-corrections of shapes review missed** (the system working): (1) `hv` context was `Γ`, must be `Δ++Γ` to recurse
  (`5b8be87`; consumer-identical at Δ=[]); (2) the value motive's `hvres` was UNCONDITIONAL but `force`/`unfold` enter the
  value layer at `slotGrade=0` where the value is dormant ⟹ unconditional `hvres` is UNSATISFIABLE there ⟹ **gate the value
  motive symmetric with comp** (`slotGrade γ₀ |Δ| ≠ 0 → hvres`, `139b3af`). vvar i=k still fires the gate (slotGrade(basis k)=1).
- **State @ `b8bb04b`:** 9 gated value arms real + force/unfold comp arms compose (no probe-sorry). `#print axioms liveCapsResolveV_subst_gen` = `[propext, sorryAx, Classical.choice, Quot.sound]`, sorryAx from the **10 remaining comp arms** only. Independently gated (built + read the value arms).
- **`liveCapsResolveV_weaken`** (needed for the BINDER comp arms — letC/lam/case/split/handle reshift `hv`→`A₀::Δ++Γ`):
  refute-tested SOUND. Carrier-transfer-under-`HasVTy.weaken` is **closedness-INDEPENDENT** (weaken only shifts vvar indices
  [carrier vvar leaf is obligation-free] + leaves caps untouched [closed → shiftFrom = id] ⟹ same `ResolvesLabel`). `hcl` is
  needed for a DIFFERENT role (align the binder IH on `v` not `shift v`). Likely needs its own recursor/`∃ d'` (same Prop-index wall).
- **Remaining → full carrier-subst lemma:** gated comp arms (ret/app/perform) · `liveCapsResolveV_weaken` · binders via it · the
  comp twin via `LiveCapsResolveC.rec` (factor the 21 handlers). Then thread into `lwscg_returnEscape` + `lwsg_step_nonperform` (#4+#5)
  → `type_safety` sorryAx-on-DISPATCH(#35)-only.

### Comp-half routing + findings (2026-06-27, `ff4109f`; grind handed to a fresh IC on branch `inc5-comp-grind`)
PREREQ #1 DONE: **`HasVTy.subst_gen`** (value-subst, for dormant value positions / perform's arg) — proven `ff4109f` axiom-clean
via the **ret-wrap** (subst into `ret w` through `HasCTy.subst_gen`, `generalize` the Sgrade index past the dependent-elim wall,
invert the `ret`; single-source — reuses subst_gen as a black box). Eventual cleaner home = expose Metatheory's `motive_1` as a
public `HasVTy.subst_gen` (option b) if value-subst gets reused.
- **PREREQ #2 `liveCapsResolveV_weaken` — the one novel decision left.** The INDEXED form over `hv.weaken k hk A'` FAILS: `HasVTy.weaken`
  is a THEOREM (opaque output, no constructor reduction), so recursor arms can't pattern-match it. RESOLUTION = **existential-controlled-output**
  form (build a fresh weakened typing+carrier YOU control) — needs `insG`/`insT` (shifted grade/context ctors), currently `private` in
  `Bang/Metatheory.lean` → expose them (~2-line private-removal, pure typing infra, carrier-agnostic-safe). Then the mutual V/C weaken recursor.
- **FACTORING (fresh-IC finding, build-confirmed convergent review):** the comp twin `liveCapsResolveC_subst_gen` is NOT independent — the
  mutual recursor's `motive_2` proves every comp arm. Factor the 21 arm-proofs as `private` lemmas; BOTH public theorems become one-liners
  differing ONLY in the gate arg (V: `fun _ => hvres`; C: `hgate`). Avoids writing the 21 arms twice.
- **In-file comp-arm template:** `lwscg_subst_gen` (`Bang/Model.lean:2632-2722`), the grade-indexed sibling — exact grade-reshaping skeleton
  (Sgrade_hsmul/hadd/cons, cov_*, binder descent `(0::γ,k+1)`, split `(0::0::γ,k+2)`); helpers PUBLIC in Model. Comp arms = port ITS arms +
  the `∃d'` typing-pairing (per the value `pair` arm) + gate-split. Hardest arm = `split` (double binder ⇒ weaken composed twice).
- **Routing:** pe-coh-core (built the value half + prereq #1 + the map) STOOD DOWN; the fresh IC grinds `compfresh`/`inc5-comp-grind` off `ff4109f`
  (inherits the value half + prereq #1) with the weaken-resolution + factoring. inc5-lr-reindex parked at `ff4109f`. Whichever branch closes the
  full lemma (both twins real, axiom-clean) is gated + becomes the mainline; the other is the fallback.

### ★★★★★ KEYSTONE CLOSED + reconciled (2026-06-28, `inc5-lr-reindex` @ `bf15fe7`, PUSHED) — type_safety is NOT one step away
The fresh IC (aa10) **won the survey-wide race** and closed the carrier-subst keystone *cleaner* than the relayed plan (Prop proof-irrelevance for weaken; a 3-line thunk-wrap C-twin instead of 21 duplicated arms). **`liveCapsResolve{V,C}_subst_gen` + `…_weaken` are axiom-clean** (independently gate-verified at `da67c2d`: `[propext, Classical.choice, Quot.sound]` / `[propext, Quot.sound]`). Also landed: `HasVTy.subst_gen` (value-subst prereq, ret-wrap, `ff4109f`) + de-privatized `insG`/`insT`/`insG_smul/add` in `Bang/Metatheory.lean` (pure grade infra). The canonical `inc5-lr-reindex` was fast-forwarded onto it and **pushed to origin** (was local-only). *(`Bang.Surface` is pre-broken at `ff4109f` — imports only `Operational`, unrelated; a full-build red on Surface is NOT a regression.)*

**CORRECTION (build-refuted twice by aa10):** the keystone is the reusable CORE (covers every REDUCE/MINT-subst case) but `type_safety` is NOT one consumer-step away. `lwsg_step_nonperform` additionally needs POP/PUSH carrier-native machinery that does not exist. The doc comment at `Model.lean:~4123` naming `LWSCg`/`LWSKg` is STALE (pre-ADR-0061); the actual lemma is carrier-typed.

**The remaining grind — the POP-focus phase (scoped as a fresh-budget effort):**
- **`liveCapsResolve{V,C}_returnEscape`** (STATED `bf15fe7`, `Model.lean §3.7c`, refute-first-SOUND, sorried) — the bulk. Recurse via `LiveCapsResolveV.rec` (K is a PARAMETER not an index → clean structural recursion, unlike subst).
  - **(c) lazy-vthunk RULED OUT** (kernel-engineer, build-arbitrated): relaxing the carrier's eager-`vthunk` clause dissolves this wall but **relocates the cost to FORCE, where it's UNDERIVABLE** (`force (vthunk M)→M` needs `LiveCapsResolveC K M` post-step; typing can't reconstruct runtime cap-resolution; reachable refutation: a thunk holding a minted cap forced while its handler is live). **Eager-vthunk is load-bearing for force-preservation. Keep it.**
  - **The fix (a):** a **combined carrier(caps)+grade-live-var invariant**, IH-chaining. Two gifts from the kernel-engineer: (i) the **V→C thunk crossing is SELF-SUPPLYING** — `¬labelOccurs ℓ (U φ C)` decomposes to EXACTLY `(¬ℓ≤φ, ¬labelOccurs ℓ C)` (`labelOccurs ℓ (U φ C) = ℓ≤φ ∨ labelOccurs ℓ C`), so the crossing isn't the wall; (ii) **carrier-subst is NOT the tool** (its conclusion is a carrier; the invariant's goal is a Prop label-membership disjunction — categorically different). The real work = the **comp-binder LIVE sub-case** (`letC`/`app`/`case`/`split`, q1≠0): the body consumes the escaped cap ⟹ performs it (contradicts `hrow`) or re-escapes it (contradicts `hres`) — the cross-term head↔body argument. (The grade-coupling covers only the DEAD sub-case, q1=0.)
- THEN: `liveCapsResolveK_restack` (PUSH/MINT) · `liveCapsResolveK_pop` (POP-tail, mirror the closed `lwskg_pop_fresh` over the carrier) · stack-carrier inversions · the `Source.step` case analysis → `lwsg_step_nonperform`.
- **Endpoint:** `type_safety` = sorryAx-on-`lwsg_step_dispatch`(#35)-only. #35 is the recorded honest boundary (**ADR-0062**: multi-shot resumption provably-ω; the affine fragment — bang's actual handlers — gradeable, inc-6). NOT debt.

### ★★★★★★ POP-FOCUS REFUTED → SOUNDNESS HOLE → RECLASSIFY (2026-06-28, `inc5-comp-grind`) — the grind above is SUPERSEDED
**`liveCapsResolveC_returnEscape` is FALSE as stated** (the "remaining grind" above is build-refuted; do NOT pursue the carrier+grade-live-var invariant). The comp-binder LIVE sub-case is not a provable cross-term — it's a genuine **soundness hole**. A typeable, **VcapFree** program (`progComp`) launders a **state** handler's cap into a returned **thunk** via an inner re-handle of the same label (the re-handle discharges ℓ from the thunk's external type BY LABEL — identity-blind — so the answer-type B-occ from ADR-0057 passes), then `force`s it after the handler pops ⟹ the cap dispatches by identity to the dead handler ⟹ STUCK. SEALED + manager-gated: `Bang/ReturnEscapeReach.lean` (`progComp_typeable` HasCTy axiom-clean **∧** `#guard Source.eval = .escapedCap`) + `Bang/ReturnEscapeRefute.lean` (lemma-false). **Reopens #50; amends ADR-0057** (B-occ guards direct-perform, NOT laundered-re-handle). `throws` is untypeable here (answer-type pinned) — the hole is **state/transaction** only.

**DECISION — ADR-0063 (operator):** reclassify the escape as a DEFINED fail-loud for v1. **LANDED + gated:** kernel `Result.escapedCap` (`d745253`) + Model-side `NonEscape'`/`FocusResolves'`/`diagonal'` SORRY-FREE `[propext, Quot.sound]` (`7d7ebf9`, green set 716 jobs). `diagonal'` = the `NonEscape'` **tautology** (escape now a defined terminal) = a correct BUILDING BLOCK, **NOT** `type_safety` closure.

**REMAINING = inc-6 (task #15):** `Spec.lean` untouched — swap `HasConfig`→`NonEscape'`, **RESTATE `progress`** (gains a `∨ escapedCap` disjunct — the obligation RELOCATES there, and is now *provable*, unlike the false `returnEscape`), re-prove `type_safety`; + CalcVM `.escapedCap` accounting (inv #1). The vestigial `WScfg`/`liveCapsResolve*_returnEscape`/`lwsg_step_*`/`#35` machinery is **PARKED off-path** (not deleted). The carrier-subst **keystone** (`…_subst_gen`/`…_weaken`, `da67c2d`) remains axiom-clean + real but is now off the critical path. SoT: **ADR-0063** + `CONTEXT.md`. Phase-1 gate lesson: a kernel-*type* change (new `Result` ctor) must be gated against the WHOLE lib (an LR exhaustiveness ripple was missed by a subset build).

**UPDATE (same session) — the v1 soundness PROOF CONTENT is now DONE, axiom-clean, #35-FREE.** `progress'_proof` `[propext, Quot.sound]` + `type_safety'_proof` `[propext, Classical.choice, Quot.sound]` close in green Metatheory (`ef71972`, manager-gated on a fresh olean). NO `sorryAx`, NO #35 — the reclassification dissolved the dispatch dependency (`type_safety'` rides `hasConfigTy_step` PURE typing-preservation, NOT the WScfg/`lwsg_step` route, so #35 was never a real type-safety obligation — it's a separate post-v1 resumption-grading refinement). MEANINGFUL: `progComp` (the refuting witness) now SATISFIES `type_safety'`. Additive (Spec + old proofs untouched). **REMAINING = inc-6/#15, purely MECHANICAL:** re-point `Spec.lean` onto the primed proofs (CalcVM-blocked) + CalcVM `.escapedCap` accounting. **#54 CLOSED.**
