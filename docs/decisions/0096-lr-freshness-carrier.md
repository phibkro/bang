# ADR-0096 · The LR id-uniqueness (freshness) carrier — the item-1 SKIP-relocation wall

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The last proof-layer wall gating `lr_fundamental`/`lr_fundamental_closed` (and one of `lr_sound`'s two residuals) is the `krelS_splitAtId_decomp` SKIP-arm resume relocation (`BinaryLR.lean:1030`, task #29 item 1). Machine-characterized on krnl3's `feat-lr-final-wall @ 2b0948e`: the relocation is a config-append INVERSE that needs `splitAtId cfg₁.1 nid = none` — an **id-uniqueness/freshness** fact — where the captured continuation `cfg₁.1 = Kᵢ ++ reinstall :: Ki'` has `Kᵢ` UNIVERSALLY quantified (any captured continuation). Both viable routes need it: the self-recursive strip (route B) and the un-append (route A). Route A **elaborates and terminates** (`AppendInvWF.lean`) but is **answer-type-refuted** at its last obligation (`Dⱼ = Dᵢ` fails at `P=[]`: `Dᵢ=X` vs `Dⱼ=F qᵣ Aᵣ`); the caller-discharge of a uniqueness *premise* (route B′) is **refuted** because the LR is freshness-free BY DESIGN — ADR-0058 route-1 dissolved `Canonical`/`CapsBelow`/`run_bump`, so no `WellCounted`/`FreshCfg` carrier is in scope to discharge it. **The carrier that must be RE-INTRODUCED already half-exists**: `CrelK`/`KrelS` ALREADY thread the real fresh-id counter `g` internally (ADR-0058 route-1 landed), and the kernel ALREADY has the exact well-formedness predicate (`StackBelow g K`, `Invariants.lean:39`, axiom-clean) and its consequences (`splitAtId_fresh`, `stackBelow_splitAtId`, `wellCounted_reachable`). What is MISSING is the assertion tying `g` to the stacks: `StackBelow g K₁ ∧ StackBelow g K₂`. **THE REACHING TEST (machine-decided, `da03e68` witness pair `BWitnessUniqueInResume.lean`, axiom-clean `[propext]`) narrows the shape space to a def-change**: the strip's needed fact lives on the resume conjunct's captured continuation `Kᵢ`, which `KrelS` binds UNIVERSALLY — `strip_mislocates_when_nid_in_prefix` refutes reaching it from a top-level premise (a concrete `Kᵢ = [handleF nid _]` mislocates the split), while `strip_with_fact` confirms the strip closes once the fact IS on `Kᵢ`. So the pure top-level shapes are REFUTED: **(ii) a lemma-chain premise and (iii) a consumer-side side judgment both CANNOT reach the bound `Kᵢ`** and are struck. The surviving shapes both put the fact inside `KrelS`: **(i′) a `KrelS` def-invariant on the two stack args** (the recursive resume-conjunct hyp `KrelS m … g Kᵢ Kᵢ'` then propagates `StackBelow g Kᵢ` for free — self-propagating, matches the `WellCounted` precedent), or **(i″) a fresh premise directly on the resume conjunct** (surgical, but the discharge threads at every producer). **RECOMMEND shape (i′)** for its self-propagation — re-introduces only the *fact*, not the *machinery* (no `Canonical`, no `run_bump`, no faked counter), and forces **no frozen-statement change** (the `Spec.lean` `lr_*` statements never mention `g`/`KrelS`/the carrier). The proof-layer close is ready to consume (`strip_with_fact` + the banked `KrelS_length_eq`); the cost is the FROZEN DEF-block change (`LR.lean:1131`) rippling to the ~20 `krelS_*` eq-lemmas, self-propagating so each intro maintains it inductively. **Load-bearing honest correction to the task-#29 census claim**: the carrier closes `lr_fundamental` + `lr_fundamental_closed` (census **18→20**), NOT `lr_sound` — `lr_sound` carries a SECOND, independent residual (the Q22 reshape↔raw-focus bridge, `Spec.lean:252`), and the `stackBelow_handlerCount_of_hasStack` obligation the carrier would impose on `krelS_refl` at `lr_sound`'s `g := handlerCount C` instantiation is UNPROVABLE from `HasStack` alone (`FreshCarrierDischargeProbe.lean`) — that IS the Q22 seam. So `lr_sound`'s third shed needs Q22 co-resolved; **18→21 is only reachable if this ADR is landed together with the Q22 bridge**, not by the carrier alone. **PARK priced**: ship v1 with the three `lr_*` flagged; the ◊4 binary-LR paper (`docs/papers/binary-lr-skeleton.md`) becomes a CPP-framed "machine-checked LR construction + the seam analysis" with `lr_fundamental` a single named residual — honest, publishable now, but the POPL/ICFP "closed contextual-equivalence result" claim stays out of reach.
- **Depends-on**: 0058 (route-1 dissolved the freshness machinery this partially reverses — the reversal SCOPE turns on this), 0055 (global-fresh identity + `WellCounted`/`splitAtId_fresh` — the precedent the carrier re-uses), 0057 (the cap-escape half of task #29, item 2, resolved vacuously — orthogonal), 0016 (the LR is the ◊4 contextual-equivalence path, not the soundness diagonal)
- **Relates-to**: #29 (the unit this ADR is the design consult for — item 1), Q22 (labelling-vs-closure cap-rep — the SECOND `lr_sound` residual, `docs/papers/binary-lr-skeleton.md` §8.1), `docs/notes/stage5-lr-design.md` (the sibling residual-map; the `_at`-twin shape precedent), `scratch/SkipRelocateProbe.lean` / `scratch/AppendInvWF.lean` / `scratch/KrelSUnappendProbe.lean` / `scratch/DecompFreshStrip.lean` / `scratch/BWitnessUniqueInResume.lean` (krnl3's wall witnesses + the (a)-vs-(b) reaching-test pair, `feat-lr-final-wall @ da03e68`), `scratch/FreshCarrierDischargeProbe.lean` (this lane's `krelS_refl`-discharge probe)

## Status

Accepted (2026-07-10, operator re-ruling: shape **(i′)** — the `KrelS` def-invariant
`StackBelow g` on the two stacks, self-propagating via the recursive conjuncts; Q22 stays HELD,
the implementation targets the 18→20 shed). **Decision history, honestly:** the first draft
recommended shape (iii) and the operator approved it; the reaching test (krnl3's
`strip_mislocates_when_nid_in_prefix` witness) then REFUTED (iii) along with (ii) — the
freshness fact must land on the resume conjunct's universally-bound `Kᵢ`, which no construct
outside `KrelS`'s definition can bind — so that acceptance was vacated and the operator
re-ruled on the surviving pair, taking the recommendation. (i″) (premise on the resume
conjunct) remains the build-arbitrated fallback if (i′)'s self-propagation walls. The
`Spec.lean` lr_* statements stay byte-identical; the frozen-DEF-block change is sanctioned BY
THIS RULING for the invariant conjunct ONLY. Census: carrier → `lr_fundamental` +
`lr_fundamental_closed` shed (18→20); `lr_sound`'s third shed needs Q22 (held).

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
