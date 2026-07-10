# ADR-0096 · The LR id-uniqueness (freshness) carrier — the item-1 SKIP-relocation wall

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The last proof-layer wall gating `lr_fundamental`/`lr_fundamental_closed` (and one of `lr_sound`'s two residuals) is the `krelS_splitAtId_decomp` SKIP-arm resume relocation (`BinaryLR.lean:1030`, task #29 item 1). Machine-characterized on krnl3's `feat-lr-final-wall @ 2b0948e`: the relocation is a config-append INVERSE that needs `splitAtId cfg₁.1 nid = none` — an **id-uniqueness/freshness** fact — where the captured continuation `cfg₁.1 = Kᵢ ++ reinstall :: Ki'` has `Kᵢ` UNIVERSALLY quantified (any captured continuation). Both viable routes need it: the self-recursive strip (route B) and the un-append (route A). Route A **elaborates and terminates** (`AppendInvWF.lean`) but is **answer-type-refuted** at its last obligation (`Dⱼ = Dᵢ` fails at `P=[]`: `Dᵢ=X` vs `Dⱼ=F qᵣ Aᵣ`); the caller-discharge of a uniqueness *premise* (route B′) is **refuted** because the LR is freshness-free BY DESIGN — ADR-0058 route-1 dissolved `Canonical`/`CapsBelow`/`run_bump`, so no `WellCounted`/`FreshCfg` carrier is in scope to discharge it. **The carrier that must be RE-INTRODUCED already half-exists**: `CrelK`/`KrelS` ALREADY thread the real fresh-id counter `g` internally (ADR-0058 route-1 landed), and the kernel ALREADY has the exact well-formedness predicate (`StackBelow g K`, `Invariants.lean:39`, axiom-clean) and its consequences (`splitAtId_fresh`, `stackBelow_splitAtId`, `wellCounted_reachable`). What is MISSING is the assertion tying `g` to the stacks: `StackBelow g K₁ ∧ StackBelow g K₂`. **Three carrier shapes weighed**: (i) a `KrelS` def-invariant conjunct, (ii) a freshness premise on the lemma chain up to the headlines, (iii) a threaded side well-formedness judgment `WFIds g K` (the `StoresGood`/`WellCounted` precedent). **RECOMMEND shape (iii)**, threaded as a `StackBelow g`-shaped side judgment discharged from `wellCounted_reachable` at the `crelK_fund_up` consumer — it is the smallest reversal of route-1 (re-introduces the *fact*, not the *machinery*: no `Canonical`, no `run_bump`, no faked counter), forces **no frozen-statement change** (the `Spec.lean` `lr_*` statements never mention `g`/`KrelS`/the carrier), and its cost is bounded by the ~2 banked lemmas already axiom-clean on the branch (`KrelS_length_eq`, `splitAtId_append_boundary`) plus the thread-through. **Load-bearing honest correction to the task-#29 census claim**: the carrier closes `lr_fundamental` + `lr_fundamental_closed` (census **18→20**), NOT `lr_sound` — `lr_sound` carries a SECOND, independent residual (the Q22 reshape↔raw-focus bridge, `Spec.lean:252`), and the `stackBelow_handlerCount_of_hasStack` obligation the carrier would impose on `krelS_refl` at `lr_sound`'s `g := handlerCount C` instantiation is UNPROVABLE from `HasStack` alone (`FreshCarrierDischargeProbe.lean`) — that IS the Q22 seam. So `lr_sound`'s third shed needs Q22 co-resolved; **18→21 is only reachable if this ADR is landed together with the Q22 bridge**, not by the carrier alone. **PARK priced**: ship v1 with the three `lr_*` flagged; the ◊4 binary-LR paper (`docs/papers/binary-lr-skeleton.md`) becomes a CPP-framed "machine-checked LR construction + the seam analysis" with `lr_fundamental` a single named residual — honest, publishable now, but the POPL/ICFP "closed contextual-equivalence result" claim stays out of reach.
- **Depends-on**: 0058 (route-1 dissolved the freshness machinery this partially reverses — the reversal SCOPE turns on this), 0055 (global-fresh identity + `WellCounted`/`splitAtId_fresh` — the precedent the carrier re-uses), 0057 (the cap-escape half of task #29, item 2, resolved vacuously — orthogonal), 0016 (the LR is the ◊4 contextual-equivalence path, not the soundness diagonal)
- **Relates-to**: #29 (the unit this ADR is the design consult for — item 1), Q22 (labelling-vs-closure cap-rep — the SECOND `lr_sound` residual, `docs/papers/binary-lr-skeleton.md` §8.1), `docs/notes/stage5-lr-design.md` (the sibling residual-map; the `_at`-twin shape precedent), `scratch/SkipRelocateProbe.lean` / `scratch/AppendInvWF.lean` / `scratch/KrelSUnappendProbe.lean` / `scratch/DecompFreshStrip.lean` (krnl3's four wall witnesses, `feat-lr-final-wall @ 2b0948e`), `scratch/FreshCarrierDischargeProbe.lean` (this lane's `krelS_refl`-discharge probe)

## Status

Accepted (2026-07-10, operator ruling: "iii approved" — shape (iii), the threaded `StackBelow g`
side judgment, with the Q22 co-resolution HELD: the implementation targets the 18→20 shed
(`lr_fundamental` + `lr_fundamental_closed`); `lr_sound`'s Q22 residual stays the single named
◊4 residual per the recommendation). Implementation = a proof-layer unit consuming krnl3's
banked lemmas (`KrelS_length_eq`, `splitAtId_append_boundary`, `strip_with_fact`) + this lane's
discharge probe. Originally Proposed same day (lane lrfresh design consult); the evidence base
is krnl3's four machine-checked wall witnesses + this lane's code-read of the frozen DEF block.

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

So the carrier does **not** re-introduce `Canonical`/`CapsBelow`/`run_bump` (the FAKED-counter
reconciliation route-1 deleted). It re-introduces only the **FACT** that the real counter `g`
dominates the stack ids — which the kernel already proves reachable configs satisfy. This is the
distinction that keeps the reversal minimal: route-1 deleted *bookkeeping for a faked counter*; the
carrier asserts *a true property of the real counter*.

## Decision (RECOMMENDATION — pending operator ratification)

**Adopt carrier shape (iii): a threaded side well-formedness judgment `StackBelow g` on the LR
stacks, discharged at the `crelK_fund_up` consumer from `wellCounted_reachable`.** Below: the three
shapes, each with ripple map + reversal scope + size; then the census honesty and the PARK price.

### The option table

| shape | forces frozen-statement change? | reversal scope (vs route-1) | size |
|---|---|---|---|
| **(i) `KrelS` def-invariant conjunct** — add `StackBelow g K₁ ∧ StackBelow g K₂` to `KrelS` | **NO** to `Spec.lean` (`g`/`KrelS` internal); **YES** to the FROZEN DEF block (`LR.lean:1131`) — meaning shifts, every `krelS_*` eq-lemma + `krelS_refl` re-touched | re-introduces the FACT (not the machinery); but the invariant must hold at `krelS_refl` (`g:=handlerCount C`) — **UNDISCHARGEABLE from `HasStack`** (Q22, see below) | **large** — the DEF-block change ripples to ~20 `krelS_*` lemmas + `krelS_refl` blocks on Q22 |
| **(ii) freshness premise on the lemma chain** — add `StackBelow g K₁ →` to `krelS_splitAtId_decomp`, `crelK_fund_up`, … up to `crelK_fund` | depends how far it rides: if it reaches `crelK_fund` → the `Spec.lean:271` `lr_fundamental` wiring `fun h => crelK_fund h` needs the premise → **YES, frozen change** | re-introduces the fact as a hypothesis; but threads through the term-measured mutual block (the s5grind rebuild) — wide | **medium-large** — premise-threading through the mutual block; risks a frozen change if it can't be discharged before `crelK_fund` |
| **(iii) side judgment `WFIds g K`, discharged at the consumer** — carry `StackBelow g` as a SEPARATE hypothesis on `crelK_fund_up`/`krelS_splitAtId_decomp` ONLY, discharge from `wellCounted_reachable` where the config is machine-reached | **NO** — the judgment lives on the proof-internal lemmas below `crelK_fund`; the consumer discharges it, so it never surfaces on `crelK_fund`'s type nor `Spec.lean` | re-introduces ONLY the fact, ONLY on the two lemmas that need it, discharged locally — the narrowest reversal | **small-medium** — thread `StackBelow g` through `krelS_splitAtId_decomp` + its `crelK_fund_up` call; discharge from the banked lemmas + `wellCounted_reachable` |

### Why (iii) — the discrimination

The `StoresGood`/`WellCounted` precedent (`EnvMachine.lean:1871`, `Invariants.lean:46`) is exactly
this shape: a well-formedness fact carried alongside the config, discharged from reachability where
consumed, never surfacing on a headline. The id-first sim's `UniqueHId` threading from `FreshCfg`
(memory `idfirst-sim-needs-hs-id-uniqueness`) is the same move on the machine side. The carrier
`StackBelow g` is the LR-side twin.

Crucially, (iii) **localizes the discharge to where it is TRUE**: `crelK_fund_up` observes configs
reached by REAL machine runs (`Source.step` from a fresh counter), so `wellCounted_reachable` gives
`StackBelow g K` for free there. The universally-quantified `Kᵢ` in the resume conjunct is a
captured continuation of such a run, so it too inherits `StackBelow g` — killing the "`nid` might be
in `Kᵢ`" case by construction. No faked counter, no density reconciliation, no `Canonical`.

(i) is rejected because the DEF-block invariant must hold at EVERY `KrelS` instantiation, including
`krelS_refl` at `lr_sound`'s `g := handlerCount C` — which is NOT a machine-reached config (see the
census honesty). (ii) is rejected because the premise risks riding all the way to `crelK_fund` and
forcing a frozen change; (iii) discharges it one level below, keeping `crelK_fund`'s type — hence
`Spec.lean` — byte-identical.

### Reversal scope (all three)

What route-1 dissolved and STAYS dissolved under (iii): `Canonical`, `Val.CapsBelow`,
`run_bump_converges`, the faked `handlerCount`-as-counter, the density reconciliation. What comes
back: **only** the assertion `StackBelow g K` (already defined) on the two proof-internal lemmas,
plus the two banked strip lemmas. Route-1's core win — the observed config IS the actual config, the
pop shift is the actual `g → g+1` — is preserved; the carrier adds the missing "and the ids are
below `g`" that route-1 left implicit.

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
→ `crelK_fund_up` → item 1; they do NOT touch the reshape bridge. Therefore:

- **The carrier alone closes `lr_fundamental` + `lr_fundamental_closed` → census 18→20.**
- **`lr_sound`'s third shed needs Q22 co-resolved** (18→21 requires BOTH this ADR AND the Q22 bridge).

Moreover, the carrier's discharge at `lr_sound`'s `krelS_refl` instantiation (`g := handlerCount C`)
is **itself the Q22 seam**: `StackBelow (handlerCount C) C` is UNPROVABLE from `HasStack C …` alone
(`HasStack.handleF`, `Typing.lean:378`, binds the frame id `n` FREE — no density premise; a source
observation context is not machine-reached). Probed and recorded as
`stackBelow_handlerCount_of_hasStack` in `scratch/FreshCarrierDischargeProbe.lean` (kept as the
do-not-retry witness that this discharge is NOT free). Shape (iii) sidesteps this by NOT putting the
invariant on `KrelS` — it discharges only at the machine-reached `crelK_fund_up`, leaving `lr_sound`'s
`krelS_refl` untouched; `lr_sound`'s closure then still awaits Q22, exactly as today.

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

`KrelS_length_eq` and `splitAtId_append_boundary` (branch `2b0948e`, axiom-clean) are consumed
directly once the `StackBelow g` fact is in scope: `splitAtId_append_boundary` supplies the
boundary-location from `splitAtId cfg₁.1 nid = none` (= `splitAtId_fresh` applied to
`StackBelow g cfg₁.1`), and `KrelS_length_eq` aligns the two append boundaries. `AppendInvWF`'s
proven WF STRUCTURE (strong-induction + `dispatchOn_append_outer` lift) is the skeleton; only its
answer-type obligation changes — with `StackBelow g` in hand, the strip locates the boundary
determinately, so the `Dⱼ = Dᵢ` refutation dissolves (the boundary is the SAME frame both strips
hit, fixing the answer by `rfl` rather than requiring the refuted cross-hole equality).

### No invariant breach

Rows stay `Finset` sets (the carrier is on stack ids, not the row); five primitives unchanged; STM
privilege untouched; performance second-class respected (a proof-layer fact, zero runtime cost). The
carrier is the ADR-0055 `WellCounted` invariant, re-used at the LR — not a new construct.

## Alternatives considered (rejected / deferred)

- **Shape (i) — `KrelS` def-invariant.** Rejected: forces the FROZEN DEF-block change with the widest
  ripple (~20 `krelS_*` lemmas) AND blocks at `krelS_refl` on the Q22-shaped
  `StackBelow (handlerCount C) C` obligation that `HasStack` cannot discharge. It couples the carrier
  to Q22 in the worst way (the invariant must hold at a non-machine-reached instantiation). Deferred
  as the shape a future Q22 resolution might revisit (if the reshape makes `handlerCount C` the real
  counter, (i) becomes discharge­able — but that is Q22's call, not this one's).
- **Shape (ii) — premise on the lemma chain up to the headlines.** Rejected for v1: risks riding to
  `crelK_fund` and forcing a frozen `lr_fundamental` change (a `STATEMENT_CHANGE_OK` event +
  kernel-engineer review). (iii) achieves the same discharge one level lower with no frozen touch.
  Keep as the fallback if (iii)'s local discharge does not close (build-arbitrate).
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

**Recommendation on PARK vs proceed:** proceed with shape (iii) — it is small, forces no frozen
change, re-introduces only a true fact the kernel already proves reachable, and it collapses the
◊4 residual set from three to one (the Q22 seam), materially improving the paper's honesty-to-claim
ratio. But it does NOT on its own deliver `lr_sound`; if the operator's goal is the FULL closed
equivalence result, this ADR must be sequenced WITH the Q22 bridge, and the two together are the
"18→21" the census target names. The operator rules on: (a) carrier shape (recommend iii), and
(b) whether to sequence it with Q22 now or land the `lr_fundamental` shed alone (18→20) and hold Q22.

## Ground

`scratch/SkipRelocateProbe.lean` · `scratch/AppendInvWF.lean` · `scratch/KrelSUnappendProbe.lean` ·
`scratch/DecompFreshStrip.lean` · `scratch/KrelSLengthProbe.lean` · `scratch/CrelKUpVacuityProbe.lean`
(krnl3, `feat-lr-final-wall @ 2b0948e`) · `scratch/FreshCarrierDischargeProbe.lean` (this lane) ·
`Bang/Meta/LR.lean:1116/1131` (frozen `CrelK`/`KrelS` DEF block, `g` threaded) ·
`Bang/Meta/BinaryLR.lean:929/1018/1038` (`krelS_splitAtId_decomp` SKIP sorry, `crelK_fund_up`) ·
`Bang/Core/Semantics/Invariants.lean:39/65/94/251` (`StackBelow`/`splitAtId_fresh`/
`stackBelow_splitAtId`/`wellCounted_reachable`) · `Bang/Core/Typing.lean:378` (`HasStack.handleF`,
free id) · `Bang/Spec.lean:236/252/267/277` (the frozen `lr_*` statements + the Q22 residual) ·
ADR-0058 (route-1 dissolution) · ADR-0055 (`WellCounted` precedent) ·
`docs/papers/binary-lr-skeleton.md` §8 (the paper's honest-scope section).
