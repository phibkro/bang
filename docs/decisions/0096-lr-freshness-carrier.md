# ADR-0096 · The LR id-uniqueness (freshness) carrier — the item-1 SKIP-relocation wall

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The last proof-layer wall gating `lr_fundamental`/`lr_fundamental_closed` (and one of `lr_sound`'s two residuals) is the `krelS_splitAtId_decomp` SKIP-arm resume relocation (`BinaryLR.lean:1030`, task #29 item 1). Machine-characterized on krnl3's `feat-lr-final-wall @ 2b0948e`: the relocation is a config-append INVERSE that needs `splitAtId cfg₁.1 nid = none` — an **id-uniqueness/freshness** fact — where the captured continuation `cfg₁.1 = Kᵢ ++ reinstall :: Ki'` has `Kᵢ` UNIVERSALLY quantified (any captured continuation). Both viable routes need it: the self-recursive strip (route B) and the un-append (route A). Route A **elaborates and terminates** (`AppendInvWF.lean`) but is **answer-type-refuted** at its last obligation (`Dⱼ = Dᵢ` fails at `P=[]`: `Dᵢ=X` vs `Dⱼ=F qᵣ Aᵣ`); the caller-discharge of a uniqueness *premise* (route B′) is **refuted** because the LR is freshness-free BY DESIGN — ADR-0058 route-1 dissolved `Canonical`/`CapsBelow`/`run_bump`, so no `WellCounted`/`FreshCfg` carrier is in scope to discharge it. **The carrier that must be RE-INTRODUCED already half-exists**: `CrelK`/`KrelS` ALREADY thread the real fresh-id counter `g` internally (ADR-0058 route-1 landed), and the kernel ALREADY has the exact well-formedness predicate (`StackBelow g K`, `Invariants.lean:39`, axiom-clean) and its consequences (`splitAtId_fresh`, `stackBelow_splitAtId`, `wellCounted_reachable`). What is MISSING is the assertion tying `g` to the stacks: `StackBelow g K₁ ∧ StackBelow g K₂`. **THE REACHING TEST (machine-decided, `da03e68` witness pair `BWitnessUniqueInResume.lean`, axiom-clean `[propext]`) narrows the shape space to a def-change**: the strip's needed fact lives on the resume conjunct's captured continuation `Kᵢ`, which `KrelS` binds UNIVERSALLY — `strip_mislocates_when_nid_in_prefix` refutes reaching it from a top-level premise (a concrete `Kᵢ = [handleF nid _]` mislocates the split), while `strip_with_fact` confirms the strip closes once the fact IS on `Kᵢ`. So the pure top-level shapes are REFUTED: **(ii) a lemma-chain premise and (iii) a consumer-side side judgment both CANNOT reach the bound `Kᵢ`** and are struck. The surviving shapes both put the fact inside `KrelS`: **(i′) a `KrelS` def-invariant on the two stack args** (the recursive resume-conjunct hyp `KrelS m … g Kᵢ Kᵢ'` then propagates `StackBelow g Kᵢ` for free — self-propagating, matches the `WellCounted` precedent), or **(i″) a fresh premise directly on the resume conjunct** (surgical, but the discharge threads at every producer). **RECOMMEND shape (i′)** for its self-propagation — re-introduces only the *fact*, not the *machinery* (no `Canonical`, no `run_bump`, no faked counter), and forces **no frozen-statement change** (the `Spec.lean` `lr_*` statements never mention `g`/`KrelS`/the carrier). The proof-layer close is ready to consume (`strip_with_fact` + the banked `KrelS_length_eq`); the cost is the FROZEN DEF-block change (`LR.lean:1131`) rippling to the ~20 `krelS_*` eq-lemmas, self-propagating so each intro maintains it inductively. **Load-bearing honest correction to the task-#29 census claim**: the carrier closes `lr_fundamental` + `lr_fundamental_closed` (census **18→20**), NOT `lr_sound` — `lr_sound` carries a SECOND, independent residual (the Q22 reshape↔raw-focus bridge, `Spec.lean:252`), and the `stackBelow_handlerCount_of_hasStack` obligation the carrier would impose on `krelS_refl` at `lr_sound`'s `g := handlerCount C` instantiation is UNPROVABLE from `HasStack` alone (`FreshCarrierDischargeProbe.lean`) — that IS the Q22 seam. So `lr_sound`'s third shed needs Q22 co-resolved; **18→21 is only reachable if this ADR is landed together with the Q22 bridge**, not by the carrier alone. **PARK priced**: ship v1 with the three `lr_*` flagged; the ◊4 binary-LR paper (`docs/papers/binary-lr-skeleton.md`) becomes a CPP-framed "machine-checked LR construction + the seam analysis" with `lr_fundamental` a single named residual — honest, publishable now, but the POPL/ICFP "closed contextual-equivalence result" claim stays out of reach.
- **Depends-on**: 0058 (route-1 dissolved the freshness machinery this partially reverses — the reversal SCOPE turns on this), 0055 (global-fresh identity + `WellCounted`/`splitAtId_fresh` — the precedent the carrier re-uses), 0057 (the cap-escape half of task #29, item 2, resolved vacuously — orthogonal), 0016 (the LR is the ◊4 contextual-equivalence path, not the soundness diagonal)
- **Relates-to**: #29 (the unit this ADR is the design consult for — item 1), Q22 (labelling-vs-closure cap-rep — the SECOND `lr_sound` residual, `docs/papers/binary-lr-skeleton.md` §8.1), `docs/notes/stage5-lr-design.md` (the sibling residual-map; the `_at`-twin shape precedent), `scratch/SkipRelocateProbe.lean` / `scratch/AppendInvWF.lean` / `scratch/KrelSUnappendProbe.lean` / `scratch/DecompFreshStrip.lean` / `scratch/BWitnessUniqueInResume.lean` (krnl3's wall witnesses + the (a)-vs-(b) reaching-test pair, `feat-lr-final-wall @ da03e68`), `scratch/FreshCarrierDischargeProbe.lean` (this lane's `krelS_refl`-discharge probe)

## Status

Accepted (2026-07-10, operator re-ruling: shape **(i′)** — the `KrelS` def-invariant conjunct,
self-propagating via the recursive conjuncts; Q22 stays HELD, the implementation targets the
18→20 shed). **Decision history, honestly:** the first draft recommended shape (iii) and the
operator approved it; the reaching test (krnl3's `strip_mislocates_when_nid_in_prefix` witness)
REFUTED (iii) along with (ii) — the freshness fact must land on the resume conjunct's
universally-bound `Kᵢ`, which no construct outside `KrelS`'s definition can bind — so that
acceptance was vacated and the operator re-ruled shape (i′). (i″) (premise on the resume
conjunct) remains the build-arbitrated fallback if (i′)'s self-propagation walls.

**AMENDMENT (2026-07-10, the predicate correction — lane lrcarry, machine-arbitrated):** the
ruled conjunct's PREDICATE is **`StackInc`** (ids strictly increase up the stack;
StackBelow-DERIVED: head clause = `StackInc K ∧ StackBelow n K` on the tail), NOT this ADR's
original `StackBelow g`. DO-NOT-RETRY: `StackBelow g` is machine-INSUFFICIENT for the strip —
`splitAtId_fresh` fires only when the searched id EQUALS the counter `g`, but the strip
searches for the LIVE deep-catcher id `nid < g`, and `StackBelow g Kᵢ` does not exclude a live
`nid` from `Kᵢ` (concrete counterexample `stackBelow_does_not_give_fresh_for_live_id` in
`StackBelowInsufficientProbe.lean`, riding branch `lrcarry-probes`). The corrected carrier is fully de-risked
axiom-clean (`lrcarry-probes @ e875881`): mint preserves it (`stackInc_mint`, co-travels with
`WellCounted`), resume preserves it (`stackInc_reinstall` — the hard arm), delivery yields
`StackAbove nid` on the captured region (`stackInc_gives_above`), which gives the strip's
freshness (`splitAtId_above`) and closes the composite boundary-location
(`skip_strip_locates`). Cost delta vs this ADR's budget: the same ~20-lemma ripple slot, plus
the `StackInc` def + five drafted lemmas + a ~10-line `stackInc_reachable` companion to
`wellCounted_reachable` in `Invariants.lean`. No new machinery; the `Spec.lean` lr_*
statements stay byte-identical; the frozen-DEF-block change is sanctioned for the StackInc
conjunct ONLY. Census unchanged: carrier → `lr_fundamental` + `lr_fundamental_closed` shed
(18→20); `lr_sound`'s third shed needs Q22 (held).

## PROPOSED AMENDMENT — the class-2/class-1 carrier FORK (lane carrierprobe, 2026-07-10, AWAITING OPERATOR RULING)

**Context.** The `StackInc` carrier landed and threaded through ~28 `BinaryLR` sites (`feat-lr-carrier-stackinc-wip @ 683a7448`, GREEN build), leaving TWO machine-characterized residual sorry-classes:

- **class-1 (reinstall/append `StackInc`)** — 14 sites (671/672, 736/737, 755/756, 876/877, 907/908, 941/942, 1432/1433): the reinstall lemmas must feed `krelS_append` its explicit `StackInc (Kᵢ ++ handleF nh h :: K₁)` premise, where `Kᵢ` is the resume conjunct's UNIVERSALLY-bound captured continuation.
- **class-2 (MINT `StackBelow g`)** — 8 sites (1196/1197, 1242/1243, 1278/1279, 1475/1476) at the `compatK_handle*` cores: the freshly-minted `handleF g` frame needs `StackBelow g K₁/K₂` (the current-counter domination) for `krelS_handleF_intro`. Plus 4 `krelS_refl` sites (1893/1922/1932/1948) which are the **Q22 seam** (`StackBelow nh K` unprovable from `HasStack` alone), already carved out by the ruling above — OUT of the fork's scope.

The class-2 MINT `StackBelow g` collides with `KrelS_g_cast`'s g-independence (`BinaryLR.lean:1195` names it). Two forks resolve class-2:

- **(a) Monotone cast** — carry `StackBelow g K` IN the `KrelS` def-invariant (beside `StackInc`), and weaken `KrelS_g_cast` to `g ≤ g'` only.
- **(b) WellCounted premise** — leave `KrelS`/`KrelS_g_cast` byte-identical; add a `WellCounted (g,K) = StackBelow g K` PREMISE inside `CrelK`'s def, discharged at the top-level call sites from the machine invariant.

**VERDICT: fork (a) REFUTED (both horns); fork (b) VIABLE. RECOMMEND (b). Class-1 needs its OWN per-frame conjunct regardless (surfaced by the probe).**

### Q1 — fork (a) refutation (`Bang/Witness/CarrierForkA.lean`, axiom-clean)

The full caller census of `KrelS_g_cast` (`BinaryLR.lean:1139/1143/1147/1151/1153` internal + 1201/1214/1247/1283/1480 MINT): every EXTERNAL caller is monotone (`g → g+1`), BUT the resume-conjunct internal recursion at **`:1151` casts `m g' g` — the REVERSE direction** (the captured continuation `Kᵢ` sits in contravariant/hypothesis position). Fork (a) is refuted on both horns:
- `gcast_full_kills_stackBelow_invariant` — a `StackBelow g` def-invariant makes the FULL-general cast unprovable (at `g' := 0` on any live `handleF` frame, `StackBelow 0 K = False`). So fork (a) is FORCED to weaken the cast.
- `monotone_gcast_cannot_serve_contravariant_resume` — but a `g ≤ g'`-only cast CANNOT serve the contravariant `:1151` recursion (it needs `g+1 → g`, the wrong direction). Refuted.

### Q2 — fork (b) viability (`Bang/Witness/CarrierForkB.lean` + `CarrierForkBSkeleton.lean`, axiom-clean)

The MINT obligation `StackBelow g K₁` arises INSIDE the compat cores after `CrelK`'s `intro g D K₁ K₂ hK`, so `g,K₁` are universally bound by `CrelK`. The reaching test (mirroring the ADR's `strip_mislocates`):
- `crelK_stmt_premise_cannot_reach_mint` — a premise on `crelK_fund`/`crelK_fund_up`'s STATEMENT is OUTSIDE `∀ g K₁` → UNREACHABLE (same failure as shapes ii/iii). So "premise on the fund lemma" fails.
- `crelK_def_premise_reaches_and_is_gcast_free` — a `StackBelow g K₁` hypothesis inside `CrelK`'s DEF (BESIDE `KrelS`, not folded in) DOES reach the MINT point AND is `KrelS_g_cast`-free (the cast stays full-general; the two facts never mix). This is precisely what fork (a) cannot do.

The discharge chain elaborates (`CarrierForkBSkeleton.lean`, all `sorry`-free except the held Q22):
- MINT-site: `StackBelow g K₁` IS the intro'd hypothesis (`mint_site_has_freshness`).
- body re-application at `(g+1, handleF g :: K₁)`: needs `StackBelow (g+1) (handleF g :: K₁)`, discharged from the outer `StackBelow g K₁` by monotonicity + `g < g+1` (`body_reapply_discharges`) — the step fork (a) cannot do because its `StackBelow g` is cast-coupled.
- root: `lr_fundamental`/`crelK_adequacy_nil` at `(0,[])` → `StackBelow 0 [] = True` (`root_nil_discharges`, 18→20 shed); `lr_sound` at `(handlerCount C, C)` → the Q22 seam (`lr_sound_root_needs_Q22`, held) — census UNCHANGED.

### Q3 — class-1 needs its OWN per-frame conjunct (`Bang/Witness/CarrierClass1.lean`, axiom-clean)

Class-1 is INDEPENDENT of the (a)/(b) ruling — it concerns the resume conjunct's `Kᵢ`, not the ambient MINT tail. The `stackInc_append_of_above` combinator (BANKED, `Invariants.lean:357`) closes class-1 from four antecedents; three are in scope (`StackInc Kᵢ`, `StackInc K₁`, `StackBelow nh K₁`) but the fourth — `StackAbove nh Kᵢ` (the captured continuation's ids all exceed the reinstalled catcher) — is MISSING:
- `stackInc_not_above` — `StackInc Kᵢ ⇏ StackAbove nh Kᵢ` (independent). The current carrier is insufficient for class-1.
- `class1_closes_given_above` — GIVEN `StackAbove nh Kᵢ`, class-1 closes via the banked combinator, no new infrastructure.

So class-1 needs **a per-frame `StackAbove nh Kᵢ` conjunct ADDED to `KrelS`'s handleF resume clause** (the shape-(i″) per-frame conjunct). It is SELF-PROPAGATING (the recursive resume `KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ'` carries it for the nested `krelS_append` arm at 671, matching `stackInc_gives_above`'s delivery from a machine-reached `StackInc`). This is a SECOND, orthogonal def-change, sanctioned by the (i′) frozen-DEF-block precedent (Spec.lean untouched).

### Recommendation + cost estimate (sites-to-reprove)

**Adopt fork (b) for class-2 + the per-frame `StackAbove nh` resume conjunct for class-1.** Together they replace all 22 in-scope sorries with in-scope hypotheses / the banked combinator.

| change | edit surface | sites re-proved |
|---|---|---|
| (b) `StackBelow g K₁/K₂` premise on `CrelK` def | `LR.lean:1116` (CrelK def) + the 8 MINT sites drop their `sorry` + every `CrelK` CONSUMER discharges the premise (root `crelK_adequacy_nil`/`lr_fundamental` trivially; `lr_sound` → Q22) + the recursive-body re-applications inside compat cores (monotone-lift) | ~8 MINT + ~6 CrelK-application sites (letC/handle-body re-applies) ≈ **14** |
| class-1 per-frame `StackAbove nh Kᵢ` resume conjunct | `LR.lean:1131` (KrelS handleF resume clause) + the 14 class-1 sites use `stackInc_append_of_above` + `krelS_handleF_intro`/`krelS_*_reinstall` thread the new conjunct | ~14 class-1 + the ~6 `krelS_*` intros/reinstalls that maintain it ≈ **20** |

Rejected: **fork (a)** — refuted (Q1). The monotone-cast is structurally incompatible with the resume conjunct's contravariance; no restructuring of the resume clause avoids it without a deeper reshape (a shape (c) below).

### The census consequence (honest)

The winner (b + class-1 conjunct) still delivers **18→20** (`lr_fundamental` + `lr_fundamental_closed`), NOT more — `lr_sound`'s third shed (18→21) still needs Q22 (surfaced crisply as `StackBelow (handlerCount C) C` on the `krelS_refl` sites, unchanged from the (i′) ruling). **New debt surfaced:** class-1 is NOT closed by the class-2 carrier alone — it needs its own `StackAbove nh` resume-conjunct addition (Q3). This is additional work vs the ADR's original "the StackInc carrier closes it" framing, but it is a BANKED-combinator discharge (`stackInc_append_of_above` already exists), not new infrastructure.

### What a shape (c) would need (if the operator rejects both forks' def-changes)

If neither `CrelK`-def-premise (b) nor per-frame resume conjunct is acceptable, shape (c) would have to make the resume conjunct's `Kᵢ` COVARIANT — e.g. re-index the whole LR by a fuel-bounded/step-indexed judgment where the counter monotonicity is structural (memory `lr-crelk-custom-arm-termination-wall` fallback C). That is a full LR re-index — far larger than (b) — and is out of scope for this probe. The (b)+conjunct route is the minimal machine-arbitrated answer.

### Ground (lane carrierprobe, `design-lr-carrier-fork`)

`Bang/Witness/CarrierForkA.lean` (Q1 refutation, `[]`/`[propext,Quot.sound]`) · `Bang/Witness/CarrierForkB.lean` (Q2 reaching test, `[]`) · `Bang/Witness/CarrierForkBSkeleton.lean` (Q2 discharge-chain skeleton, `[]`/`[propext,Quot.sound]` + held Q22 `sorry`) · `Bang/Witness/CarrierClass1.lean` (Q3, `[]`/`[propext,Classical.choice,Quot.sound]`) · `BinaryLR.lean:1131/1151` (`KrelS_g_cast` contravariant recursion) · `BinaryLR.lean:1196-1197/1242-1243/1278-1279/1475-1476` (class-2 MINT sorries) · `BinaryLR.lean:736-737/…` (class-1 sorries) · `Invariants.lean:357` (`stackInc_append_of_above`, the class-1 combinator).

## PROPOSED AMENDMENT ② — the ANSWER-TYPE fork (lane answerfork, 2026-07-10, AWAITING OPERATOR RULING)

**Context.** With the `StackInc`+class-1+class-2 carrier LANDED (`feat-lr-carrier-stackinc-wip @ def27451`),
the LOCATION-determinacy residual is closed (`skip_strip_from_stackInc`, banked). The `crelK_fund_up`
wall (`BinaryLR.lean:1231`, census3-sharpened) names the REMAINING residual: the resume arm's inner
relation must be supplied at the DEEP catcher's answer `Dᵢ`, and the only source re-answers `D → Dᵢ`
(the route-A `Dⱼ = Dᵢ` refutation, `c8b5909`). Two forks were tabled to close it:

- **(a) answer-type-pinning CARRIER** — carry each frame's catcher answer as DATA (an answer-indexed
  frame relation / def-invariant), NOT as an equation `Dⱼ = Dᵢ` (which route-A pre-refutes).
- **(b) combined index-WF LEMMA** (no def change) — a single WF induction producing (inner relation +
  resume conjunct) at a consistently-threaded existential answer.

**VERDICT (machine-arbitrated, lane `design-lr-answer-fork` off `def27451`):**

> **The census "answer-type wall" is RE-LOCATED, not at `crelK_fund_up` but ONE LEVEL DEEPER — inside
> `krelS_splitAtId_decomp`'s SKIP arm.** The `crelK_fund_up` resume arm itself has **NO** `D → Dᵢ`
> re-answering: routed through the FULL decomp (which delivers `hin` at answer `Dᵢ` AND the resume
> conjunct's inner premise at the SAME `Dᵢ`), it fires by construction, mod tractable index/row/grade
> casts (`AnswerForkCompose.decomp_route_fires_no_reanswer`, axiom-clean `[propext,Quot.sound]`). The
> `D → Dᵢ` re-answering the census names lives ONLY on the `krelS_dispatch_resume` route (which delivers
> the resume conjunct WITHOUT `hin`, forcing reconstruction from `hres` at answer `D`) — and, transitively,
> in the decomp's own SKIP arm (whose reconstructed frame outputs at `Dᵢ` while its source `hres`
> outputs at `D`, `AnswerForkSkipReanswer.skip_reanswer_D_ne_Di`). So the decision is:
> **fork (a) is the viable frame; fork (b) alone cannot pin the answer.** But the required DATA is
> ALREADY present — it is `krelS_splitAtId_decomp`'s existential `Dᵢ`. No NEW carrier field is needed;
> the answer just must be threaded consistently through the SKIP relocation, which the LANDED
> `StackInc` carrier's location determinacy makes a boundary-decomp (a `Dstrip`-existential), not a
> cross-answer equation.**

### Why (b) alone cannot close it — the answer is not location-determined

`splitAtId : EvalCtx → Nat → Option (EvalCtx × Handler × EvalCtx)` returns **no `CTy`** — the answer
type is ABSENT from the location data. `krelS_splitAtId_decomp`'s `Dᵢ` is `∃`-bound, and the same nil
prefix `[]` self-relates at MANY answers (`AnswerForkSkipReanswer.boundary_answer_not_location_determined`,
axiom-clean `[propext]`: `[]` relates at answer `F q A` AND at `F q unit`). So a WF LEMMA (fork b) with
no carrier storing the answer has nothing forcing two decomps at the same `nid` to agree on `Dᵢ` — the
existential threading census3 hoped for is UNAVAILABLE without a DATA carrier. Fork (b) is refuted AS A
STANDALONE.

### Why the answer-as-DATA is already in scope (the (a)-realized-through-existing-existential refinement)

The `krelS_splitAtId_decomp` output ALREADY carries the answer as data: its inner `hin : KrelS n C Dᵢ
e g K₁ᵢ K₂ᵢ` and its resume conjunct's inner premise `KrelS m Cᵢ' Dᵢ εᵢ' g Kᵢ Kᵢ'` share the SAME
existential `Dᵢ`. So on the DECOMP route the answer unifies BY CONSTRUCTION — no equation, no re-answer
(`AnswerForkCompose.decomp_route_fires_no_reanswer`). Fork (a)'s "carry the answer as DATA, not an
equation" is thus realized THROUGH the decomp's existing existential — NOT a new frame field. The
`nil_forces_grade_equality` witness confirms the only nil-forced obstruction is a returner-GRADE
equality `q = qᵣ` (caller-choosable, `qᵣ := q`), in the tractability class of state/txn reinstall
(`rfl`), NOT the refuted cross-answer.

### The remaining residual, honestly

The decomp's SKIP-arm sorry (`BinaryLR.lean:1138`) is NOT closed by this probe — its reconstructed
frame outputs at `Dᵢ` while `hres` outputs at `D`. My `AnswerForkSkip.skip_strip_answer_is_decomp_existential`
shows the STRIP's answer comes from a boundary-decomp existential (DATA, not a re-answer equation) — but
it RIDES the decomp's own sorry (transitive `sorryAx`, HONESTLY flagged), so it is a SHAPE confirmation,
not an independent close. The path to close it: complete the SKIP relocation by (i) LIFT the inner
dispatch over `Ki'` to `K₁'` (`dispatchOn_append_outer`, `AnswerForkSkip.skip_lift_direct` axiom-clean),
(ii) apply `hres`, (iii) STRIP the appended tail via a boundary-decomp at `nid` (located by
`skip_strip_from_stackInc`), reading the deep answer `Dᵢ` off the boundary decomp's existential. Step
(iii) is a self-referential decomp (the SKIP arm calling the decomp on the RESULT relation); it needs a
WELL-FOUNDED measure so the recursion terminates — the fork-(b) WF SHAPE is right FOR THE STRIP, but
CONSUMING the fork-(a) answer-as-data (the decomp existential), not producing it from nothing. **So the
true answer is a HYBRID: (a)'s answer-as-data (already in the decomp existential) + (b)'s WF induction
(for the SKIP self-recursion), NEITHER as a NEW `KrelS`-def field.**

### Recommendation + sites-to-reprove

**Adopt NEITHER (a) as a new def-field NOR (b) as a standalone lemma. Complete `krelS_splitAtId_decomp`'s
SKIP arm (`BinaryLR.lean:1138`) via the LANDED carrier's boundary-decomp** — the answer threads as the
decomp's existential `Dᵢ`, the location by `skip_strip_from_stackInc`, the WF measure on `(index,
Ki'.length)` for the self-referential strip. `crelK_fund_up` (`:1263`) then routes through the FULL
decomp (`decomp_route_fires_no_reanswer` is the ready composition). NO frozen-DEF change; NO `Spec.lean`
change.

| change | edit surface | sites |
|---|---|---|
| close `krelS_splitAtId_decomp` SKIP sorry (`:1138`) | ONE arm: lift (`dispatchOn_append_outer`) + apply `hres` + strip (`skip_strip_from_stackInc` + boundary-decomp at `nid`) + WF measure | **1 sorry** |
| wire `crelK_fund_up` (`:1263`) through the FULL decomp | the resume arm consumes the decomp's `hin`+conjunct via `decomp_route_fires_no_reanswer`'s composition (index/row/grade casts) | **1 sorry** |

### Census math (corrected under the winner)

Closing the decomp SKIP sorry (`:1138`) + `crelK_fund_up` (`:1263`) sheds `lr_fundamental` +
`lr_fundamental_closed` → **census 18→20**, IDENTICAL to the first amendment's target — because
`lr_fundamental := crelK_fund` routes only through the mutual block → `crelK_fund_up` → the decomp, and
the decomp's answer-coherence is the LAST residual on that path. `lr_sound`'s third shed (18→21) STILL
needs Q22 (the `krelS_refl` reshape seam, held) — unchanged. **The answer-type fork does NOT reopen the
census; it identifies the LAST proof-only obligation on the 18→20 path.** No genuinely-FALSE statement
was found (nothing needs a hypothesis added / reshape): the wall is HARD (a WF self-recursion consuming
an existential), not a refutable statement. The `Spec.lean` `lr_*` statements stay byte-identical.

### Ground (lane answerfork, `design-lr-answer-fork` off `def27451`)

`scratch/AnswerForkProbe.lean` (fork-(a) equation-refutation + data-survives-gcast + hole/answer
separations, `[propext]`) · `scratch/AnswerForkDecomp.lean` (`nil_forces_grade_equality` grade-not-answer,
`[propext]`) · `scratch/AnswerForkCompose.lean` (`decomp_route_fires_no_reanswer` — the SUCCESS skeleton,
axiom-clean `[propext,Quot.sound]`) · `scratch/AnswerForkSkip.lean` (`skip_lift_direct` `[propext]` +
`skip_strip_answer_is_decomp_existential` — SHAPE, rides decomp `sorryAx`, flagged) ·
`scratch/AnswerForkSkipReanswer.lean` (`skip_reanswer_D_ne_Di` + `boundary_answer_not_location_determined`,
`[propext]`) · `BinaryLR.lean:1138` (decomp SKIP sorry), `:1263` (`crelK_fund_up` sorry), `:1231` (the
census3 wall comment) · `krelS_dispatch_resume` (axiom-clean, the no-`hin` route) vs
`krelS_splitAtId_decomp` (`sorryAx`, the `hin`+conjunct route).

### CENSUS4 IMPLEMENTATION ATTEMPT — the hybrid built, ONE sub-obligation WALLED (lane census4, build-grounded)

The RULED hybrid (amendment ② recommendation) was IMPLEMENTED to its wall on `feat-lr-carrier-stackinc-wip`.
Banked GREEN (`just verify` exit 0):

- **Binop LR arm CLOSED** (`crelK_binop` + helpers, `BinaryLR.lean` after `crelK_unfold`, axiom-clean
  `[propext,Classical.choice,Quot.sound]`). LOAD-BEARING census correction: `lr_fundamental := crelK_fund
  := crelK_fund_at` — and `crelK_fund_at`'s **`Comp.binop` arm** (formerly `BinaryLR.lean:1794`) was ALSO
  `sorryAx`, on the `lr_fundamental` path. So the amendment's "the decomp's answer-coherence is the LAST
  residual on the 18→20 path" was INCOMPLETE — the binop arm was a THIRD residual. It is now closed (the
  twin of `crelK_unfold`: `VrelK int` literal-equality forces equal `vint` operands ⇒ equal δ-reducts ⇒
  `CrelK_head_step`+`crelK_ret`). Sorry count 63→61.
- **`Dᵢ = C'` answer-coherence conjunct ADDED to `krelS_splitAtId_decomp`'s OUTPUT** (the inner answer =
  outer boundary hole; threads trivially — HIT `rfl`, SKIP inherits from `ih`). This is the fork-(a)
  answer-as-DATA the amendment names, now a real output field. Builds clean.
- **The WF `(n, K₁.length)` recursion + lift+strip skeleton** elaborates: `dispatchOn_append_outer` lifts
  the goal dispatch to `K₁'`, `hres` fires, `skip_strip_from_stackInc` locates the boundary, the strip
  self-recurses at `m < n` (index-decreasing). ALL of this composes.

**THE WALL (the ONE remaining sub-obligation, `BinaryLR.lean` SKIP arm):** the strip's boundary-decomp
delivers the inner relation at answer `Db` with `Db = Cb'` (its OWN `Dᵢ=C'` conjunct), where `Cb'` is the
strip's outer hole over the SHARED tail `Ko'`/`K₂ₒ`. Closing needs `Cb' = C'` (the ORIGINAL outer hole over
the SAME `Ko'`/`K₂ₒ` at the SAME answer `D`) — i.e. **"a `KrelS` hole is determined by (stack pair, answer)"
(`krelS_hole_det`). This is REFUTED for a `letF`/`appF`-headed `Ko'`:** the hole `F q A` / `arr q A B` carries
a value-type `A` the frame body does NOT pin, so two decomps of the same tail may relate at different `A`
(the `letF` clause existentially binds `A`). So the amendment's "answer-as-data through the existential" is
NECESSARY but NOT SUFFICIENT — the strip's `Db` must additionally be TIED to the original `Dᵢ`, and that tie
needs hole-determinacy which is false. **Census4 verdict: the 18→20 shed is NOT reached; `lr_fundamental` +
`lr_fundamental_closed` still `sorryAx` (SKIP + `crelK_fund_up`). The amendment stays PROPOSED.** The
surviving route is a `KrelS`-def-CONCLUSION strengthening (carry hole-determinacy on the resume conjunct's
conclusion, ~28 sites) OR a `shape (c)` fuel-indexed re-index — BOTH beyond the "no def-change" envelope the
hybrid promised. NEXT: operator ruling on whether to pay a def-CONCLUSION change (larger than the amendment
priced) or PARK the `lr_*` cluster (ship v1 flagged, per the PARK section above).

## PROPOSED AMENDMENT ③ — route (α) hole-determinacy probe: (α) REFUTED-at-delivery; RECOMMEND PARK or (β) (lane hole-det, 2026-07-10, RULED — see below)

**RULED (operator, 2026-07-10 night): (α) STRUCK; the census unit stays PARKED; (β) adopted as a
BACKGROUND lane.** The fuel-indexed re-index (β) proceeds as a long-running IC lane (branch
`feat-lr-fuel-reindex`, sliced — slice 1 de-risks the load-bearing claim: the fuel-indexed def block +
the SKIP-strip crux + the `KrelS ↔ ∃n, KrelSN n` bridge shape, gated before any 37-decl grind) in
parallel with the emission arc, which keeps the momentum. This amendment (like ①/②) flips
PROPOSED→Accepted only in a real 18→20 landing commit; the ruling here fixes DIRECTION, not status.

**Context.** The census4 wall (above) names TWO surviving routes past the `Cb' = C'` SKIP tie: **(α)**
a `KrelS`-def-CONCLUSION strengthening (carry hole-determinacy on the resume conjunct's conclusion,
~28 sites), and **(β)** a `shape (c)` fuel-indexed LR re-index. This amendment is the machine-arbitrated
refute-first probe of (α), with (β) priced (not built), off `feat-lr-carrier-stackinc-wip @ 1e5656c5`.

**VERDICT (three sentences):** The census4 wall is a genuinely-FALSE statement — `krelS_hole_det` ("a
`KrelS` hole is determined by (stack pair, answer)") is machine-REFUTED axiom-clean, so the tie must be
carried as DATA, not re-derived. Route (α) survives the g-cast obstruction that killed fork (a) (the
strengthening is on the COVARIANT conclusion, cast forward, unlike fork (a)'s def-invariant that lands
in the contravariant hypothesis too), but it is **REFUTED AT DELIVERY (step 4)**: the tie `Cb' = C'` is
INTER-DERIVATION — `Cb'` is the resume result `hres`'s OWN re-decomp hole, `C'` is `ih`'s INDEPENDENT
decomposition of the same `Ko'`, and no conclusion datum LOCAL to `hres`'s derivation can reach `ih`'s
independently-chosen `C'` (whose value-type is genuinely free over a `letF`/`appF`-headed `Ko'`). So
**(α) does not close the wall**; the minimal machine-arbitrated answer is **PARK the `lr_*` cluster**
(ship v1 flagged) or pay **(β)**'s full re-index.

### The refute-first ladder (machine-checked, `Bang/Witness/HoleDet*.lean`)

- **Step 0 — the falsifier (`HoleDetRefute.krelS_hole_det_refuted`, axiom-clean `[propext,Quot.sound]`,
  `sorry`-FREE, KEPT as a do-not-weaken regression witness).** Taken as a hypothesis `H`,
  `krelS_hole_det` forces `F 0 unit = F 0 int` on the witness `K = [letF (ret vunit), appF vunit]` —
  which relates at BOTH holes over the SAME stacks + SAME answer `D = F 0 unit` (a `letF` head at
  index `n = 0` binds `A` VACUOUSLY; the `appF` tail fixes the answer). Absurd. Confirms the census4
  wall names a genuinely-FALSE statement (separates on the value-type `unit` vs `int`, so it does NOT
  rely on `0 ≠ 1` in the abstract `Mult`).
- **Step 1 — statability REFUTED for the generic form (`HoleDetAlphaStatability`, axiom-clean).** The
  resume conjunct has NEITHER `nid` NOR `C'` in scope (`Kᵢ` universally bound; the deep catcher lives
  inside it). The only SCOPE-RESPECTING generic tie is "the resume result is hole-determined", which
  `alpha_conclusion_conjunct_is_hole_det_on_Si` shows IS `krelS_hole_det` restricted to `Sᵢ` — refuted;
  and `alpha_conjunct_shrinks_out_letF_producer` shows it SHRINKS `KrelS` out of the free-`A`
  `letF`/`appF` producers' range. The SURGICAL form (carry `nid`/`C'` literally) is UNSTATABLE.
- **Step 2 — g-cast PASSES for a conclusion strengthening (`HoleDetAlphaGCast`, axiom-clean).** UNLIKE
  fork (a): `KrelS_g_cast`'s resume recursion (`BinaryLR.lean:1373-1378`) casts the HYPOTHESIS `Kᵢ` in
  REVERSE (`m g' g`, the fork-(a) killer) but the CONCLUSION `Sᵢ` FORWARD (`m g g'`). Any conclusion
  datum forward-casts by the SAME `KrelS_g_cast` the existing `hSk` already uses
  (`krelS_gcast_conclusion_is_forward`); the polarity split (`conclusion_side_casts_forward` vs
  `CarrierForkA.monotone_gcast_cannot_serve_contravariant_resume`) is decisive. So g-cast is NOT (α)'s
  obstruction.
- **Step 4 — delivery REFUTED (`HoleDetAlphaDelivery`).**
  `two_independent_decomps_over_shared_tail_can_disagree` (axiom-clean) shows two `KrelS` derivations
  over the same `Ko'` at the same answer carry DIFFERENT outer holes. The delivery skeleton
  `alpha_delivery_skeleton` reduces the SKIP close to `<hres-result's own hole> = C'` — the
  inter-derivation tie — discharged only by a FLAGGED `sorry` (the surviving wall). Even the ADR's
  strongest "inner-relation extractor" (hand back the result's own decomp) delivers `hres`'s hole, NOT
  `ih`'s `C'`: the two are holes of DISTINCT derivations, unreachable by any single-derivation datum.

**Net on (α): REFUTED-at-step-4.** It clears statability-generic-refute (step 1) only into
unstatability, clears g-cast (step 2, genuine — corrects any assumption that g-cast blocks it), and
DIES at delivery (step 4): the tie is inter-derivation and no conclusion strengthening reaches it. The
~28-site cost the census4 wall priced would buy a strengthening that STILL cannot close the wall.

### (β) price comparison — shape (c) fuel-indexed re-index (PRICED, not built)

(β) = the memory `lr-crelk-custom-arm-termination-wall` fallback **(C)**: a fuel-indexed judgment copy
(`KrelSN : Nat → …`, `CrelKN`, `VrelKN`) where the counter/index monotonicity is STRUCTURAL, so the
resume conjunct's `Kᵢ` becomes COVARIANT (the step-index descends, no reverse cast) and the boundary
tie threads through the fuel index rather than an existential answer. **KNOWN-VIABLE** (that memory:
Prop-to-Prop everywhere, zero large-elimination risk — the DEF block is `Prop`-valued so a Nat-height
is refuted, but a fuel-INDEX judgment copy is not a height over a derivation). **Price:** a FULL LR
re-index — the ~310-line `VrelK`/`CrelK`/`KrelS` mutual DEF block (`LR.lean:1091-1400`) duplicated
fuel-indexed, the 18 `krelS_*` + 19 `crelK_/vrelK_/compatK_*` decls re-proved against the indexed copy
(~570 `KrelS`/`CrelK`/`VrelK` references in `BinaryLR.lean` alone), plus the `HasCTy ↔ ∃ n, HasCTyN n`
collapse to recover the frozen `Spec.lean` `lr_*` statements byte-identical. What it BUYS: the SKIP
strip's self-recursion becomes structurally-terminating on the index and the boundary tie threads
covariantly — the wall closes. What it COSTS vs (α): (α) was ~28 sites on ONE conjunct; (β) is a
whole-relation duplication (~40 decls + the def block) — an order of magnitude larger, and it re-opens
every LR proof to the indexed form. **(β) is the ONLY route that closes the wall, but it is the big
hammer.**

### Recommendation FOR OPERATOR RULING

**RECOMMEND: PARK the `lr_*` cluster (ship v1 flagged, per the PARK section above), OR — if the
◊4 closed contextual-equivalence result is a hard v1 goal — pay (β)'s full re-index.** Do NOT pay
(α): it is machine-refuted at delivery (~28 sites that still leave the wall open). The census is
UNCHANGED under every option: PARK keeps the 3-headline `lr_*` cluster flagged (18 clean / 7 flagged),
(β) sheds `lr_fundamental` + `lr_fundamental_closed` (18→20; `lr_sound`'s third shed still needs Q22,
held). No frozen `Spec.lean` change under any option (all indices/carriers are internal to
`CrelK`/`KrelS`). The soundness diagonal (`type_safety`, `custom_program_safe`, the compiler
`compile_forward_sim`) is `Crel`-free and stays axiom-clean, so nothing user-facing regresses under
PARK. **No genuinely-FALSE frozen statement was found** — the `Spec.lean` `lr_*` are provable in
principle (via (β)); the wall is that (α) is the wrong-shaped fix, not that the theorem is false.

### Ground (lane hole-det, `probe-lr-hole-det` off `1e5656c5`)

`Bang/Witness/HoleDetRefute.lean` (`krelS_hole_det_refuted` — the do-not-weaken falsifier, axiom-clean
`[propext,Quot.sound]`, `sorry`-free) · `Bang/Witness/HoleDetAlphaStatability.lean` (step 1:
`alpha_conclusion_conjunct_is_hole_det_on_Si` + `alpha_conjunct_shrinks_out_letF_producer`, axiom-clean)
· `Bang/Witness/HoleDetAlphaGCast.lean` (step 2: `conclusion_side_casts_forward` +
`krelS_gcast_conclusion_is_forward`, axiom-clean — the polarity that DISTINGUISHES (α) from fork (a)) ·
`Bang/Witness/HoleDetAlphaDelivery.lean` (step 4: `two_independent_decomps_over_shared_tail_can_disagree`
axiom-clean + `alpha_delivery_skeleton` FLAGGED `sorry` = the surviving wall) ·
`BinaryLR.lean:1203-1223` (the SKIP arm + wall comment) · `BinaryLR.lean:1373-1378`
(`KrelS_g_cast` contravariant resume recursion) · `LR.lean:1212-1250` (the `KrelS` handleF resume
conjunct — `nid`/`C'` NOT in scope) · memory `lr-crelk-custom-arm-termination-wall` fallback (C) (the
(β) viability precedent).

## Context

### The wall (task #29, item 1), machine-characterized

`krelS_splitAtId_decomp` (`BinaryLR.lean:929`) decomposes a `KrelS`-related stack pair at a split
point located by `splitAtId K₁ nid`. Its HIT arm (`nid` = the top frame's id) closes cleanly. Its
**SKIP arm** (`nid ≠ mh₁`, recurse past the top `handleF mh₁ hh₁`) carries the last `sorry`
(`:1030`). The obligation: the recursed inner prefix `Ki'` (where `splitAtId` placed the deeper
catcher) must carry `hh₁`'s **resume conjunct**, but the hypothesis `hres` supplies that resume over
the LONGER original tail `K₁' = Ki' ++ handleF nid hh :: Ko'` (`splitAtId_decomp`). Relocating it to
`Ki'` is a **config-append inverse**: strip the appended `handleF nid hh :: Ko'` off a `KrelS`
decomposition over the longer stack.

Two routes, both probed to their wall on the branch:

- **Route A — un-append** (`KrelSUnappendProbe.lean` → `AppendInvWF.lean`). `krelS_append_inv`:
  from `KrelS m X D (P ++ handleF nid hh :: Ko') (P' ++ handleF nid h' :: K₂ₒ)` and
  `P.length = P'.length`, derive `∃ Dᵢ, KrelS m X Dᵢ P P'`. The **structure elaborates and
  terminates** (strong-induction on the index `m` + structural on the prefix `P`; the letF/appF
  prefix cases close via the inner IH; the handleF-in-prefix case is broken by lifting the goal
  dispatch through `dispatchOn_append_outer`, feeding `hresp`, and stripping via the OUTER `ihm` at
  `m₁ < m`). The **single remaining obligation is answer-type coherence** `Dⱼ = Dᵢ` — and it is
  **REFUTED as structured**: `hrec : KrelS m X Dᵢ P P'` (answer of the structural prefix) and
  `hstrip : KrelS m₁ (F qᵣ Aᵣ) Dⱼ cfg₁.1 cfg₂.1` (answer of the resume-result prefix) have DIFFERENT
  holes (`X` vs `F qᵣ Aᵣ`), and at `P = []` give `Dᵢ = X` vs `Dⱼ = F qᵣ Aᵣ` — not equal
  (`c8b5909`). The `krelS_handleF` resume clause pins the resume answer to the WRAPPER answer, but
  the strip yields the prefix's own answer; the reconstruction mis-threads the answer type.

- **Route B′ — uniqueness as a lemma HYPOTHESIS** (`DecompFreshStrip.lean`). If the caller could
  supply `splitAtId cfg₁.1 nid = none` (freshness), `splitAtId_append_boundary` (BANKED, axiom-clean)
  lands the split on the appended boundary and the strip goes through. **REFUTED at caller-discharge**:
  the future caller is `crelK_fund_up`'s resolved arm, but the LR (`KrelS`/`CrelK`/`crelK_fund_up`/
  `lr_sound`) is **freshness-free by design** — ADR-0058 route-1 DISSOLVED the
  `CapsBelow`/`Canonical`/`run_bump` counter machinery (`LR.lean:515`), so no `FreshCfg`/`WellCounted`
  is threaded into the LR. The caller cannot discharge a uniqueness premise **without re-introducing
  the dissolved machinery** — which is a def/statement-shape change, not a free discharge.

**The convergent diagnosis** (both routes): the boundary-location genuinely needs `nid ∉ cfg₁.1`
because `cfg₁.1 = Kᵢ ++ reinstall :: Ki'` has `Kᵢ` **universally quantified** (the resume conjunct
threads an ARBITRARY captured continuation). Under a fresh, never-reused `nid`, `nid` cannot appear
in `Kᵢ` — but the relation carries no fact saying so. **Item 1 needs id-uniqueness re-introduced
into the LR.** (Item 2, the cap-escape half, is orthogonal and already resolved vacuously —
`convergesC_le_escape_false`, axiom-clean — so this ADR concerns item 1 only.)

### What already exists (the reversal is PARTIAL, not full)

The reversal ADR-0058 route-1 performed is smaller than it looks, because route-1 already carried
the counter it needs:

| asset | where | status | role for the carrier |
|---|---|---|---|
| `g` threaded in `CrelK`/`KrelS` | `LR.lean:1116/1131` (frozen DEF block) | **LANDED** (route-1) | the counter is ALREADY a def parameter — no signature growth needed to name it |
| `StackBelow g K` | `Invariants.lean:39` | axiom-clean | the exact well-formedness predicate the carrier asserts |
| `splitAtId_fresh` | `Invariants.lean:65` | axiom-clean | `StackBelow g K → splitAtId K g = none` (the freshness the strip needs) |
| `stackBelow_splitAtId` | `Invariants.lean:94` | axiom-clean | `StackBelow` passes to split sub-stacks (reconstruction) |
| `wellCounted_reachable` | `Invariants.lean:251` | axiom-clean | every machine-reachable config is `WellCounted` (the DISCHARGE at the consumer) |
| `KrelS_length_eq` | banked, `2b0948e` | axiom-clean | length alignment for the two append boundaries |
| `splitAtId_append_boundary` | banked, `2b0948e` | axiom-clean | `nid ∉ Q → split (Q ++ handleF nid hh :: Ko') nid = some (Q, hh, Ko')` |
| `strip_with_fact` | banked, `da03e68` | axiom-clean `[propext]` | the strip CLOSES given `splitAtId Q nid = none` on the resume-result inner prefix — the ready-to-consume proof-layer close for whichever carrier reaches `Kᵢ` |
| `strip_mislocates_when_nid_in_prefix` | banked, `da03e68` | axiom-clean `[propext]` | the REFUTATION: a concrete `Kᵢ = [handleF nid _]` mislocates the split — the fact is NOT reachable from the resume conjunct's hypotheses unless carried ON the conjunct |

So the carrier does **not** re-introduce `Canonical`/`CapsBelow`/`run_bump` (the FAKED-counter
reconciliation route-1 deleted). It re-introduces only the **FACT** that the real counter `g`
dominates the stack ids — which the kernel already proves reachable configs satisfy. This is the
distinction that keeps the reversal minimal: route-1 deleted *bookkeeping for a faked counter*; the
carrier asserts *a true property of the real counter*.

## Decision (RECOMMENDATION — pending operator ratification)

**Adopt carrier shape (i′): enrich the `KrelS` resume conjunct so its universally-bound captured
continuation `Kᵢ` carries `StackBelow g Kᵢ`** — either as a `KrelS` def-invariant on the two stack
args (which the recursive `KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ'` hypothesis then propagates to `Kᵢ` for free)
or as a fresh premise on the resume conjunct itself. Both are `KrelS`-def changes; **the pure
top-level shapes (ii) and the consumer-side (iii) are REFUTED by the reaching test** (below). The
frozen `Spec.lean` `lr_*` statements stay byte-identical (`g`/`KrelS`/the invariant are all internal
to `CrelK`/`KrelS`).

### THE REACHING TEST — the load-bearing narrowing (`da03e68` witness pair)

The strip's needed fact is `splitAtId <inner prefix> nid = none`, where the inner prefix is the
resume-result stack `cfg₁.1`, built from the **captured continuation `Kᵢ`** that the `KrelS` resume
conjunct binds **universally** (`LR.lean:1196-1204`: `∀ … (Kᵢ Kᵢ' : Stack) …, KrelS m Cᵢ C εᵢ g Kᵢ
Kᵢ' → …`). The witness pair `BWitnessUniqueInResume.lean` (axiom-clean `[propext]`, re-verified green
on this branch) decides WHERE the carrier must sit:

- `strip_with_fact` (GREEN): the strip CLOSES given `splitAtId Q nid = none` on the inner prefix `Q`.
  So IF the fact reaches `Kᵢ`, the proof-layer close is ready (this is `splitAtId_append_boundary`
  under a new name; ready to consume).
- `strip_mislocates_when_nid_in_prefix` (GREEN refutation): but the fact is NOT reachable from the
  conjunct's hypotheses. A concrete `Kᵢ = [handleF nid _]` makes `splitAtId` land on `Kᵢ`'s frame,
  NOT the appended boundary — and the conjunct's ONLY constraint on `Kᵢ` is the plain `KrelS m Cᵢ C
  εᵢ g Kᵢ Kᵢ'`, which carries no uniqueness. **A premise on the LEMMA (`krelS_splitAtId_decomp`,
  `crelK_fund_up`) cannot reach a `∀ Kᵢ` bound inside `KrelS`.**

**Verdict: (b) — the uniqueness must ride INSIDE `KrelS`, on the resume conjunct's `Kᵢ`.** This is a
def-shape enrichment, forced. It kills two of my three originally-tabled shapes.

### The option table (updated — the strike is machine-witnessed)

| shape | reaches `Kᵢ`? | forces frozen-statement change? | reversal scope (vs route-1) | size |
|---|---|---|---|---|
| **(i′) `KrelS` def-invariant on stacks (RECOMMEND)** — add `StackBelow g K₁ ∧ StackBelow g K₂` to `KrelS`; the recursive resume-conjunct hyp `KrelS m … g Kᵢ Kᵢ'` then SUPPLIES `StackBelow g Kᵢ` | **YES** (via the recursive `KrelS` hyp) | **NO** to `Spec.lean` (`g`/`KrelS`/invariant all internal to `CrelK`) | re-introduces ONLY the FACT on `KrelS`'s stacks; no `Canonical`/`run_bump` | **medium** — FROZEN DEF-block change (`LR.lean:1131`) rippling to the ~20 `krelS_*` eq-lemmas + `krelS_refl`; but the invariant is self-propagating (each `krelS_*` intro carries it inductively) |
| **(i″) fresh premise ON the resume conjunct** — add `StackBelow g Kᵢ →` alongside the existing `KrelS m … g Kᵢ Kᵢ'` | **YES** (it IS on `Kᵢ`) | **NO** to `Spec.lean` (internal to `KrelS`) | narrower than (i′): touches only the handleF resume clause, not every `krelS_*` | **medium** — one clause of the DEF block + the resume-conjunct consumers (`krelS_state/txn_reinstall`, `compatK_handle*`); does NOT ripple to letF/appF eq-lemmas |
| **(ii) top-level premise on `krelS_splitAtId_decomp`/the chain** | **NO — REFUTED** (`strip_mislocates`) | n/a | n/a | STRUCK |
| **(iii) side judgment on the CONSUMER (`crelK_fund_up`)** — my original recommendation | **NO — REFUTED** (a consumer-side `StackBelow g` cannot constrain the `∀ Kᵢ` bound in `KrelS`; same failure as (ii)) | n/a | n/a | STRUCK — unless threaded THROUGH the resume conjunct, at which point it IS (i″) |

### Why (i′) over (i″) — the discrimination between the two survivors

Both survivors put the fact where it reaches `Kᵢ`. The choice is ripple vs precision:

- **(i″)** is more surgical — it adds `StackBelow g Kᵢ` only on the handleF resume clause, so the
  letF/appF `krelS_*` eq-lemmas are untouched. But it makes the resume conjunct's obligation heavier
  at every producer that DISCHARGES the conjunct (`krelS_refl`'s handleF arm, `krelS_state_reinstall`,
  `compatK_handle*`): each must now PROVE `StackBelow g Kᵢ` for the `Kᵢ` it supplies. For the
  self-relation (`krelS_refl`) that `Kᵢ` is a machine-reached continuation (dischargeable via
  `wellCounted_reachable`), but the discharge must be threaded at each producer.
- **(i′)** carries the invariant on the whole `KrelS`, so it is **self-propagating**: `krelS_handleF`
  reduces to `KrelS n C D ε g K₁' K₂'` at the tail, which already carries `StackBelow g (K₁'/K₂')`;
  the intro lemmas maintain it inductively (a `handleF nid h :: K` extends `StackBelow g` iff
  `nid < g ∧ StackBelow g K`). The producer discharges it ONCE at the root (the machine-reached
  config), not at every resume conjunct. This matches the `WellCounted`/`StackBelow` kernel precedent
  exactly (`Invariants.lean` proves `StackBelow` distributes over `++` and survives split — the
  reconstruction lemmas are already banked). **RECOMMEND (i′)** for that self-propagation; it is the
  cleaner invariant even though its edit surface (every `krelS_*` lemma) is wider than (i″)'s.

### Reversal scope (both survivors)

What route-1 dissolved and STAYS dissolved: `Canonical`, `Val.CapsBelow`, `run_bump_converges`, the
faked `handlerCount`-as-counter, the density reconciliation. What comes back: **only** the assertion
`StackBelow g K` (already defined, `Invariants.lean:39`) inside `KrelS`, plus the banked strip
lemmas. Route-1's core win — the observed config IS the actual config, the pop shift is the actual
`g → g+1` — is preserved; the carrier adds the missing "and the ids are below `g`" that route-1 left
implicit on the LR side (the kernel side always had it, `WellCounted`). The `StoresGood`/`WellCounted`
precedent (`EnvMachine.lean:1871`, `Invariants.lean:46`) and the id-first sim's `UniqueHId`-from-
`FreshCfg` threading (memory `idfirst-sim-needs-hs-id-uniqueness`) are the same move; the difference
this ADR establishes is that on the LR the fact must ride INSIDE the relation (the resume conjunct),
not alongside it as a consumer-side judgment — the reaching test is what forces that.

## Consequences

### The census honesty (load-bearing — corrects task #29's "18→21")

`lr_sound` carries **TWO independent `sorry`s**:
1. the item-1 SKIP relocation (this ADR's carrier target), reached transitively via `crelK_fund_up`
   (the trace is deliberately kept, `Spec.lean:233-235`);
2. the **Q22 reshape↔raw-focus bridge** (`Spec.lean:252`) — the biorthogonal closure observes the
   RAW focus `(g, C, cᵢ)`, but `converges_plug_iff` observes the CAP-SUBSTITUTED reshaped config
   `(handlerCount C, canonStack C cᵢ, capSubstInto C cᵢ)`; `AdequacySpike` build-confirms the bridge
   closes IFF `capSubstInto C cᵢ = cᵢ`, excluding the effectful case. This is the labelling-vs-closure
   cap-rep seam (Q22 / `docs/papers/binary-lr-skeleton.md` §8.1).

`lr_fundamental := crelK_fund` and `lr_fundamental_closed` route **only** through the mutual block
→ `crelK_fund_up` → item 1; they do NOT touch the reshape bridge NOR `krelS_refl`. Therefore:

- **The carrier alone closes `lr_fundamental` + `lr_fundamental_closed` → census 18→20.**
- **`lr_sound`'s third shed needs Q22 co-resolved** (18→21 requires BOTH this ADR AND the Q22 bridge).

**The reaching-test verdict TIGHTENS this coupling — assess honestly.** Because the recommended
shape puts `StackBelow g` INSIDE `KrelS` (the only way to reach `Kᵢ`), the `KrelS`-def invariant must
now be established at EVERY `KrelS` construction — including `krelS_refl`, which `lr_sound` calls at
`g := handlerCount C`. Under (i′), `krelS_refl` acquires a `StackBelow g C` obligation for its free
`g`; the caller discharges it. And `lr_sound`'s caller-instantiation `g := handlerCount C` needs
`StackBelow (handlerCount C) C` — which is **UNPROVABLE from `HasStack C …` alone** (`HasStack.handleF`,
`Typing.lean:378`, binds the frame id `n` FREE — no density premise; a source observation context is
NOT machine-reached). Probed and recorded as `stackBelow_handlerCount_of_hasStack` in
`scratch/FreshCarrierDischargeProbe.lean` (green with the `sorry`, the do-not-retry witness that this
discharge is not free). **This IS the Q22 seam surfacing on `krelS_refl`.** So the honest picture:
- The invariant threads FINE through the `crelK_fund` path (machine-reached configs; `g` = the real
  counter; `wellCounted_reachable` discharges it) — so `lr_fundamental`/`_closed` close cleanly.
- The invariant does NOT discharge at `lr_sound`'s `krelS_refl` instantiation without Q22 — i.e. the
  carrier makes `lr_sound`'s dependence on Q22 *structural and visible* (a `StackBelow (handlerCount C) C`
  hole) rather than hidden inside the reshape bridge. It does NOT make `lr_sound` worse (it was already
  blocked on Q22 via the reshape sorry); it relocates one of `lr_sound`'s two holes onto `krelS_refl`
  as a clean, named `StackBelow`-shaped obligation — arguably a BETTER-scoped statement of the same
  Q22 dependency.

**Net:** the carrier closes `lr_fundamental` + `lr_fundamental_closed` (18→20) unconditionally; the
third shed (`lr_sound`, 18→21) requires Q22, and under the recommended shape that requirement is now a
crisp `StackBelow (handlerCount C) C` obligation on `krelS_refl`, not a diffuse reshape mismatch. There
is no carrier shape that closes `lr_sound` without Q22 — the earlier idea that a consumer-side (iii)
"sidesteps" the `krelS_refl` obligation is WRONG (it fails the reaching test and never closes item 1
at all).

### Containment (VERIFIED, not assumed)

The claim "BinaryLR feeds only the flagged `lr_*` cluster; the 18 clean headlines untouched" is
**confirmed** by reference: `Crel`/`CrelK`/`KrelS`/`crelK_fund` appear in `Spec.lean` ONLY in
`lr_sound` (`:236`), `lr_fundamental` (`:267`), `lr_fundamental_closed` (`:277`). The clean
headlines — `type_safety`/`preservation`/`progress`/`no_accidental_handling`/`custom_program_safe`/
`subst_value`/`rowinst_requires_disjoint` and the whole compiler cluster
(`compile_forward_sim`/`compile_correct`/…) — go through the **soundness diagonal**
(Metatheory/Soundness), which ADR-0058 §Scope-boundary states is `Crel`-free
(`type_safety`/`NonEscape` close via ADR-0056/0057 independently of the LR). The other flagged
headlines (`seq_unit`, `effect_sound`, `zero_usage_erasable`, `handler_compiles`) are flagged for
UNRELATED reasons (`seq_unit_proof`, bare-`sorry` carriers, downstream-of-`lr_fundamental`
respectively) and the carrier changes none of them except `zero_usage_erasable` transitively
(it blocks on `lr_fundamental`, so closing item 1 helps it iff its own reshape is also clear —
out of scope here). **The carrier touches only the 3-headline `lr_*` cluster.**

### The banked work carries over

`KrelS_length_eq` + `splitAtId_append_boundary` (`2b0948e`) and `strip_with_fact` (`da03e68`), all
axiom-clean, are consumed directly once the `StackBelow g Kᵢ` fact reaches the resume conjunct:
`strip_with_fact`/`splitAtId_append_boundary` supply the boundary-location from
`splitAtId cfg₁.1 nid = none` (= `splitAtId_fresh` applied to `StackBelow g cfg₁.1`), and
`KrelS_length_eq` aligns the two append boundaries. `AppendInvWF`'s proven WF STRUCTURE
(strong-induction + `dispatchOn_append_outer` lift) is the skeleton; only its answer-type obligation
changes — with `StackBelow g` in hand the strip locates the boundary determinately, so the
`Dⱼ = Dᵢ` refutation dissolves (the boundary is the SAME frame both strips hit, fixing the answer by
`rfl` rather than the refuted cross-hole equality). The `da03e68` witness confirms the strip's
proof-layer close is READY the moment the carrier reaches `Kᵢ` — the remaining work is the
def-enrichment + the self-propagation through the `krelS_*` intros, not new strip infrastructure.

### No invariant breach

Rows stay `Finset` sets (the carrier is on stack ids, not the row); five primitives unchanged; STM
privilege untouched; performance second-class respected (a proof-layer fact, zero runtime cost). The
carrier is the ADR-0055 `WellCounted` invariant, re-used at the LR — not a new construct.

## Alternatives considered (rejected / deferred)

- **Shape (i″) — fresh premise directly ON the resume conjunct.** The surviving alternative to the
  recommended (i′). Surgical (touches only the handleF clause, not the letF/appF `krelS_*`), but the
  `StackBelow g Kᵢ` obligation must be discharged at every producer that supplies the conjunct
  (`krelS_refl`/`krelS_state_reinstall`/`compatK_handle*`), rather than once at the root. Kept as the
  build-arbitrated alternative if (i′)'s `krelS_*` ripple proves heavier than the per-producer
  discharge — the operator (or the implementing kernel-engineer) picks on the measured edit surface.
- **Shape (ii) — top-level premise on the lemma chain (`krelS_splitAtId_decomp`/`crelK_fund_up`).**
  **REFUTED by the reaching test** (`strip_mislocates_when_nid_in_prefix`, `da03e68`): a premise on
  the LEMMA cannot constrain the `∀ Kᵢ` bound inside `KrelS`'s resume conjunct; a concrete
  `Kᵢ = [handleF nid _]` mislocates the split regardless. Struck — the witness is the strike's
  evidence.
- **Shape (iii) — side judgment on the CONSUMER (`crelK_fund_up`), my original recommendation.**
  **REFUTED by the same reaching test**: a `StackBelow g` carried on the consumer is a top-level fact,
  so it cannot reach the bound `Kᵢ` any more than (ii) can. It closes item 1 only if threaded THROUGH
  the resume conjunct — at which point it is no longer consumer-side, it is (i″). The "sidesteps the
  `krelS_refl` obligation" claim in the first draft was wrong: it does not close item 1 at all.
- **Route A un-append WITHOUT a carrier.** Answer-type-refuted (`c8b5909`, `AppendInvWF.lean`): the
  `Dⱼ = Dᵢ` obligation is false at `P = []`. The carrier is what makes the boundary determinate; the
  un-append is not a carrier-free path.
- **Route B′ uniqueness-as-premise WITHOUT re-introducing the carrier.** Refuted at caller-discharge
  (`2b0948e`, `DecompFreshStrip.lean`): the freshness-free LR has nothing to discharge it with.
- **PARK — ship v1 with the three `lr_*` flagged.** Priced honestly below. A legitimate operator
  choice, not a failure.

## The PARK alternative — priced honestly

If the operator defers the carrier: v1 ships with `lr_sound`/`lr_fundamental`/`lr_fundamental_closed`
carrying `sorryAx` (the status quo; the census stays 18 clean / 7 flagged). The impact is confined
to the ◊4 **binary-LR / contextual-equivalence** deliverable — the soundness diagonal
(`type_safety`, `custom_program_safe`, the compiler `compile_forward_sim`) is `Crel`-free and stays
axiom-clean, so **nothing user-facing regresses** (v1 executes and type-checks on the verified
diagonal; the LR is the *equational-reasoning / optimization-licensing* theorem, not the
execution-safety one).

What the ◊4 binary-LR paper claim becomes (`docs/papers/binary-lr-skeleton.md`):
- The paper CANNOT lead with "a closed contextual-equivalence result" — its two title theorems stay
  flagged (§8 already states this). POPL/ICFP, which want the LR closed (§10), stay **premature**.
- It CAN be framed for **CPP now** as "a machine-checked LR construction + the seam analysis" (the
  build-as-arbiter methodology — the refuted arrow forms §3.2, the refuted carrier routes here — is
  itself a CPP-shaped contribution), with `lr_fundamental` a single **named** residual (§8.2) and
  `lr_sound` carrying two named residuals (item 1 + Q22, §8.1). This is publishable and honest; it
  is not the flagship equivalence result.
- The carrier (this ADR) closes ONE of the three named residuals (`lr_fundamental` +
  `lr_fundamental_closed`), leaving Q22 as `lr_sound`'s sole remaining architectural residual —
  which is the cleaner story to submit (one open seam, clearly scoped) than three.

**Recommendation on PARK vs proceed:** proceed with shape (i′) — it forces no frozen `Spec.lean`
change, re-introduces only a true fact the kernel already proves reachable, and it collapses the
◊4 residual set from three to one (the Q22 seam), materially improving the paper's honesty-to-claim
ratio. But it does NOT on its own deliver `lr_sound`; if the operator's goal is the FULL closed
equivalence result, this ADR must be sequenced WITH the Q22 bridge, and the two together are the
"18→21" the census target names. The operator rules on: (a) carrier shape — recommend (i′), with
(i″) the build-arbitrated surgical alternative (both are `KrelS`-def changes → kernel-engineer
consult per invariant #4/#5 discipline; the reaching test refuted every non-def shape), and
(b) whether to sequence it with Q22 now or land the `lr_fundamental` shed alone (18→20) and hold Q22.

## Ground

`scratch/SkipRelocateProbe.lean` · `scratch/AppendInvWF.lean` · `scratch/KrelSUnappendProbe.lean` ·
`scratch/DecompFreshStrip.lean` · `scratch/KrelSLengthProbe.lean` · `scratch/CrelKUpVacuityProbe.lean` ·
`scratch/BWitnessUniqueInResume.lean` (the (a)-vs-(b) reaching-test witness pair, `[propext]`)
(krnl3, `feat-lr-final-wall @ da03e68`) · `scratch/FreshCarrierDischargeProbe.lean` (this lane) ·
`Bang/Meta/LR.lean:1116/1131` (frozen `CrelK`/`KrelS` DEF block, `g` threaded) ·
`Bang/Meta/BinaryLR.lean:929/1018/1038` (`krelS_splitAtId_decomp` SKIP sorry, `crelK_fund_up`) ·
`Bang/Core/Semantics/Invariants.lean:39/65/94/251` (`StackBelow`/`splitAtId_fresh`/
`stackBelow_splitAtId`/`wellCounted_reachable`) · `Bang/Core/Typing.lean:378` (`HasStack.handleF`,
free id) · `Bang/Spec.lean:236/252/267/277` (the frozen `lr_*` statements + the Q22 residual) ·
ADR-0058 (route-1 dissolution) · ADR-0055 (`WellCounted` precedent) ·
`docs/papers/binary-lr-skeleton.md` §8 (the paper's honest-scope section).
