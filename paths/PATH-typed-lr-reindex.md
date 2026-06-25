# PATH — the typed LR re-index (ADR-0045 step 2) — really a DISPATCH RE-KEY

> The pivot's payoff phase: close the last kernel sorry (`preservation_returnEscape_TODO`) AND dissolve the
> ◊4.5b resume-edge (`sorryAx`-zero `lr_sound`/`lr_fundamental`). Scoped 2026-06-25 (`lrscope`), reframe
> verified on the defs. Branch `typed-static-r1` (kernel STD block gated to 1 sorry @ `91e7444`).

## The reframe (verified) — it's a RE-KEY, not a re-index

"Typed LR re-index" is a misnomer. The ◊4.5b rebuild ALREADY made the LR answer-typed + type-indexed:
- `VrelK : Nat → VTy → Val → Val → Prop` (LR.lean:448) — `U φ B` clause already forces `vthunk` + `CrelK j B φ`; `int`/`unit` use `BaseRel` (escape free). **The type-gate is already encoded here.**
- `CrelK : Nat → CTy → Eff → …` (465); `KrelS : Nat → CTy(hole) → CTy(answer) → Eff → Stack → Stack → …` (473).
- The Nat-step + `▷` substrate (`ConvergesC_le`, `coApproxC_le_anti_step`) is reused VERBATIM.

So the index is already there. The REAL work is two things:
1. **DISPATCH RE-KEY** — the LR resume machinery is keyed to `splitAt`/`dispatch`/`dispatchOn` (label search); the kernel now routes `perform` through `staticDispatch K cap` (Operational.lean:1091). Re-key the spine to `staticSplit`/`staticDispatch` (cap). **This is the bulk AND where the edge dissolves.**
2. **The return-escape type-gate** — close `preservation_returnEscape_TODO` (Operational.lean:1150) via the type `A` in `VrelK n A` (the (D) type-directed resolution). Possibly a `HasConfigTy` φ≠⊥ premise on `ret`/`letC` — a frozen-statement risk (below).

## The edge dissolution (verified on `staticSplit`)

The ◊4.5b edge = the sorry at `Compat.lean:1590`, the handleF-MISS case of `krelS_splitAt_decomp`. It exists ONLY because dynamic `splitAt` WALKS PAST a non-matching handler (prepending it into `Kᵢ`), which is the only thing that puts a non-catching `handleF` into the captured continuation. `staticSplit` (Operational.lean:325) NEVER tests `handlesOp` to decide skipping — cap=0 ⇒ `Kᵢ=[]` (handler-free by construction, MISS unreachable); cap>0 ⇒ cap-pinned answer type (no existential search ⇒ no `D2≠Dᵢ` non-determinism). **The MISS case literally ceases to exist** — `NoWrapMiss` becomes vacuous. The hardest historical risk dissolves by construction.

## The CRUX
Re-keying `crelK_fund_up` (Compat.lean:1628) + `krelS_splitAt_decomp` (Compat.lean:1474) + threading `cap` through `KrelS`'s handleF resume conjunct (LR.lean:527-555), from label-dispatch to `staticSplit`/`staticDispatch`. The concrete current RED: `crelK_fund_up` proves the step via the `dispatch`/`dispatchOn` shape, which fails against `staticDispatch`. NOT the mutual fundamental, NOT ▷-metering, NOT `closeC` (all DONE, byte-identical). Secondary: the LR `closeC`/`EnvRel` substitution-descent must commute with the lexical cap-shift (`Comp.shiftFrom`/`substFrom`) — check in Increment 0.

## Staged increments (build-gated)

- **Inc 0 (DECISIVE FIRST — the dispatch re-key surface):** re-key `crelK_fund_up` + the up-none lemmas (LR.lean:972-1036) from `splitAt`/`dispatch` to `staticSplit`/`staticDispatch`. Smallest closable unit = `crelK_fund_up`'s **THROWS arm** (throws discards `Kᵢ`, so `cap` only selects the handler — cleanest). **Gate:** build reaches/passes the throws arm over `staticDispatch`; up-none lemmas re-green over `staticSplit … = none`. This surfaces every moved kernel-LR dispatch seam = the map of the rest.
- **Inc 1 (the dissolve):** re-key `krelS_splitAt_decomp` to `staticSplit`. letF/appF arms port mechanically; handleF splits into cap=0 (HIT, `Kᵢ=[]`, old MISS arm GONE) + cap>0 (countdown, cap-pinned). **Gate:** `Compat.lean` builds with the `:1590` sorry DELETED; `#print axioms krelS_splitAt_decomp` no `sorryAx`.
- **Inc 2 (resume conjunct + state/txn):** re-express `KrelS`'s handleF resume conjunct over `cap`/`staticSplit`; re-green `crelK_fund_up`'s state/txn arms over the cap-determined `Kᵢ`. **Gate:** `crelK_fund`/`krelS_refl` handler arms close or are cap-witnessed.
- **Inc 3 (the return-escape type-gate):** close `preservation_returnEscape_TODO` via the type-premise (φ≠⊥ on `U φ C` escapes), routed through `VrelK n A`. May need a `HasConfigTy` amendment. **Gate:** `preservation`/`type_safety` `sorryAx`-gone.
- **Inc 4 (payoff):** `#print axioms lr_sound`/`lr_fundamental` ⊆ {propext, Classical.choice, Quot.sound} — `sorryAx` GONE. The ◊4.5b edge closed.

## Frozen-statement + risk
- `lr_sound`/`lr_fundamental` (Spec.lean:188,216): **NO statement change** — the types are already in the statements (`Crel n B e c₁ c₂`). Only the AXIOM SET changes (`sorryAx` vanishes): statement-stable, axiom-strengthened. (The PATH/ADR called it a STATEMENT_CHANGE; on the actual frozen text it is NOT.)
- `preservation`/`type_safety`/`progress` (Spec.lean:93,116,104): the REAL frozen-statement risk, via Inc 3 — a φ≠⊥ premise on `ret`/`letC` in `HasConfigTy` would change the `HasConfig` premise shape. STATEMENT_CHANGE_OK against ADR-0045 (same envelope as the existing `LWConfig` fold).
- "Only the index moves" is OPTIMISTIC (the index already moved; the dispatch re-key is the bulk — multi-session, ~the ◊4.5b sub-block-(f) surface area) and the return-escape gate (Inc 3) is genuinely NEW machinery, not a re-index.

## ★★★ RESOLVED — A is BUILD-REFUTED; v1 ships LR seam-5 (2026-06-25, operator ruling → ADR-0050). READ FIRST.

**Outcome:** route A (Biernacki `n-free`/`LWStack` in `KrelS`, the committed "5→2 win") is **build-refuted.**
De-risked in scratch (no frozen-def edits) BEFORE the 60-site spread; walled at the crux; operator ruled
**seam to green now**, representation fix → a separate feasibility spike. **The 5→2 did NOT materialize.**

**Why (corrects the diagnosis below):** the obstacle is NOT a "dropped Biernacki `n-free`" — it's the
**de-Bruijn cap SHIFT** (ADR-0046): crossing a `handle` bumps caps (`Val.shiftCap`), so the 3 handler arms'
IH (at env `δ`) doesn't match the goal (at `δ.map shiftCap`). The bridge `EnvRelK_shiftCap` reduces (U-clause)
to a config-simulation `(handleF h :: K, shiftCap c) ≈ (K, c)` that **walls at the state/txn resume** (resumed
focus `ret s` is unshifted while the insertion depth moves → needs `s` cap-closed, FALSE). Stack-side `LWStack`
can't force the handleF-headed stack the cancellation needs; a focus-side `WCComp` premise is a FALSE FLOOR
(static well-cappedness ✓ via `WCComp.shiftCap_insert`, dynamic residual ✗). Routes A (LR-fold) and B
(config-sim) **share this one wall.** Biernacki uses NAMED handlers (no shift) → **no proof to inherit.**

**Landed (this session):**
- `staticSplit_insert_ge` (`Metatheory.lean`, commit `7c781cf`, axiom-clean) — the cancellation building
  block (dynamic sibling of `CapResolvesKind.insert`). Reusable for the representation spike.
- The 3 `crelK_fund` handler arms SEAMED as ADR-0043/0050 descents (documented `sorry` citing the refutation).
- ADR-0050 records the refutation + the seam-5 v1 scope + the deferred representation path.

**v1 SCOPE = LR seam-5:** the 3 handler arms + `hcatch` (ADR-0043) + `:1801` ride as documented descents.
LR layer (LR/Compat/Metatheory) builds GREEN. `#print axioms` traces `sorryAx` only to the descent set.
(CalcVM/Surface are separately RED pending the ◊5 re-run — unrelated to this seam.)

**The real 5→2/full-close path (deferred to a feasibility spike):** a REPRESENTATION change — **absolute/level
caps** (no shift → no cancellation obligation; but balloons into the axiom-clean STD block) or **named handlers**
(ADR-0044, post-v1; the representation where this is a non-problem). Both are kernel-engineer-paired.

---

## (HISTORICAL — superseded by the RESOLVED banner above) ★★ THE CROSSROADS — resting at `5295ec4`.

**Where we stand:** the static-dispatch LR re-key dissolved the ◊4.5b MISS edge (banked) but exposed TWO
cap-resolution obligations that the LR can't discharge cheaply. A full build-grounded de-risk chain (4 rounds,
each "looks closeable" refuted by evidence) + representation research (Biernacki POPL18 / Effekt / Koka) settled
the decision tree. **Operator decision: take the ADR-0043 seam now; implement A (5→2) when resumed; full-close
deferred.** Nothing below this is research-uncertain — it's all build-grounded.

**The insight (prong-2 research):** bang transcribed Biernacki's `Vrel/Srel/Krel/Crel` but DROPPED Biernacki's
**`n-free`** predicate when it swapped labels for de-Bruijn caps. `n-free` = the well-bracketing predicate (carrying
per-name maps `ρ`) that ties the runtime context to the typing context. Putting it back = carry `WCStack`/`ρ-free`
in `KrelS` (the "typed-KrelS reshape" the code comments already prescribe). It's the CORRECT `lr_sound` (over
well-capped contexts — the unrestricted form is FALSE), in-envelope with the existing typed-`⊑`.

**The two obligations split (VERIFIED def-counterexample, NOT estimate):**
- **Obligation 2 — the 3 handler arms (env cap-shift cancellation, `crelK_fund` `compatK_handle*` @ Compat:2204/2220/2231).**
  = Biernacki's `Q↑l` lockstep. **CLOSED by A (n-free/`WCStack` in `KrelS`)** — LR-only, the `WCComp.shiftCap_insert`
  keystone makes the shift the natural form. ✓ This is the 5→2 win.
- **Obligation 1 — `hcatch` (cap-resolution, Compat:1867) + `:1801`.** **A does NOT close these.** Verified
  counterexample: `WCStack [handleF (throws ℓ')] = True` but `CapResolvesKind (handlersOf …) 0 ℓ op = handlesOp
  (throws ℓ') ℓ op = False` for `ℓ≠ℓ'`. Root: bang's cap is **term-side + `HasCTy.perform`-1a-unconstrained**
  (Syntax:163), whereas Biernacki's label is context-only — a stack predicate can't pin a free term-cap. The
  research/synthesis "one carry closes 4/5" was an OVERCLAIM; lrscope's def-check corrected it.

**Closing hcatch needs the term-cap PINNED context-side — a KERNEL change (both build-refuted as STD-block-touching):**
- **B — absolute/level caps** (cap from root, not de-Bruijn from use-site): DOES dissolve obligation 2 definitionally
  + makes hcatch tractable, BUT **BALLOONS** — `preservation`'s handle arms are woven through `Val.shiftCap`
  (Metatheory:510/513/517 + `HasVTy.shiftCap`), so removing the shift re-derives the **axiom-clean STD block**;
  + `staticSplit` rewrite (bottom-counting), migration-soundness, CalcVM/Compile cascade (~205 Operational /
  ~140 Metatheory cap touch-points). NOT the "small retag" the research hoped.
- **1b — `CapResolves` premise on `HasCTy.perform`**: also an STD-block cascade (~200-300 LOC, ADR-0049's declined
  Route A), but a premise-add (lighter than B's rep-rewrite). **Both need a kernel-engineer + a frozen-Spec decision.**
- C — capability-as-value (Effekt): dissolves both but a DIFFERENT kernel (re-derive VM/compiler) → post-v1, named handlers.

### RESUME POINT (the next implementation unit — A, the 5→2 win, LR-only)
Implement **A = `n-free`/`WCStack` carried in `KrelS`** (restrict `CrelK`'s `K₁` quantifier to well-capped stacks)
→ closes the 3 handler arms (obligation 2) → seam shrinks **5→2** (only `hcatch` + `:1801` remain as ADR-0043
descents). It is LR-only (kernel/STD-block UNTOUCHED) but touches the **FROZEN** `lr_sound`/`lr_fundamental`
statements (the well-capped restriction) → **STOP-and-SHOW the exact post-restriction statement before any
`Spec.lean` edit** (in-envelope with typed-`⊑`; operator pre-approved the shape, needs exact-text sign-off).
Ripple est. ~52 LR / 113 Compat / 7 Spec sites (mechanical-vs-hard not yet measured — first prototype non-committing).
Biernacki guide: `references/papers/3-lr/biernacki-popl18-handle-with-care.pdf` pp.13-16 (`n-free` Fig 2, `ρ`-quintuple
Fig 8, compat Lemmas 3-4). **Then** `hcatch`+`:1801` full-close (B/1b) is the deferred kernel-engineer-paired decision.

### Resting state (committed)
- Bank `5295ec4`: item-1 dispatch re-key (`crelK_fund_up` → `staticDispatch`) + `hcatch` documented as the ADR-0043
  descent + dup-deleted. **Compat builds RED** — item-2's 3 handler arms are type-errors (2204/2220/2231) awaiting A.
  (NOT a clean buildable state: A closes them, deferred. A future session lands A or, if dropping the LR re-key,
  seams the 3 arms too for a buildable 5-descent state.)
- `lr_sound`/`lr_fundamental` frozen statements UNTOUCHED. Kernel STD block (`91e7444`) + CalcVM + compiler unaffected.

### Earlier de-risk audit trail (don't re-derive — all build-refuted)


- **Banked `a771cc1` (LR-green, 709):** route-B `KrelS`/`EnvRelK` strip (`Val.CapClosed` GONE — route A was
  over-strong) + `closeC` route-B shapes + **the MISS dissolution** (`krelS_staticSplit_decomp` — the ◊4.5b edge
  GONE by construction; ONE documented bounded cap>0 resume-relocation sorry at `Compat.lean:1801`). Commutation
  lemmas banked. Kernel STD block at `91e7444` (1 sorry = the type-gate return-escape).
- **Re-grounding:** the LR cap-discipline is CONTEXTUAL (shift↔handleF-extension cancellation) — ADR-0045
  "Re-grounding". Routes A (CapClosed) and B-naive (shiftCap-stability) both build-REFUTED; don't re-derive them.
- **✓ (b) + (a) DONE — banked `26f4373` (build-gated: `lake build Bang.Compat` 55 errors → 6, all
  next-increment; zero new sorries; only `:1801`).**
  - **(b) swap-layer reproof:** new helper `Val.Closed.shiftCap` (from `shiftCapFrom_shiftFrom` orthogonality),
    HOISTED above the `_closed` blocks. `shiftFrom_substFrom_closed`/`substFrom_swap_closed`/`_swap_closed_ge`
    quantify `{v w}` into the ∀-motive and DROP `CapClosed`; handle arms recurse at `shiftCap u` via
    `Val.Closed.shiftCap`. Gated `closeV_closed_scoped` → `closeC_subst_comm`.
  - **(a) mechanical strip (~30 sites):** `CapClosed` removed from the `closeC_subst_comm` family,
    `crelK_unfold`, `krelS_*_intro`, `compatK_letC/app/lam/case/split`, `krelS_append`, `*_reinstall`,
    `krelS_staticSplit_decomp`, and the ~14 `crelK_fund` body sites (`EnvRelK.capClosed_*` projections gone).
- **✓ Item 1 — `crelK_fund_up` dispatch RE-KEY DONE — banked `c105904`.** none-half + all arms →
  `staticDispatch`/`staticSplit`; `krelS_splitAt_decomp`→`krelS_staticSplit_decomp`. Reduced to ONE labeled sorry
  `hcatch : handlesOp h ℓ op = true` (`Compat:1857`) — the cap-resolution obligation. Build: errors only at item-2
  (`2194/2210/2221`); sorries `:1801` + `:1857`.
- **✓ DE-RISK DONE (throwaway, reverted to `c105904`) — DECISIVE:**
  - cap=0 does NOT close on existing `KrelS` (`exact?`-refuted); cap>0 does NOT fold into `:1801` (distinct). Cheap path dead.
  - **`hcatch` CLOSES sorry-free, cap-UNIFORM, GIVEN `CapResolvesKind K₁ cap ℓ op`** — via the new helper
    `handlesOp_of_resolvesKind_staticSplit` (mirrors `staticSplit_isSome_of_resolvesKind`) + `handlesOp_label`. The
    hardest unknown is PROVEN; `crelK_fund_up` goes sorry-free given the hypothesis.
  - **cap-in-`KrelS` alone is INSUFFICIENT:** `CrelK`/`KrelS` quantify over ALL related stacks incl. cap-NON-resolving
    ones; `KrelS` has no `(cap,ℓ,op)` to key a conjunct. The cap-resolution must be SEEDED from the well-capped term
    → the FROZEN `lr_fundamental` premise IS needed, bridged through an `LWStack`-carrying `KrelS`. The full R1
    `LWConfig`+`LWStack` bridge (PATH line ~63) — genuinely new but BOUNDED machinery.
- **★ OPERATOR COMMITTED (2026-06-25) — the staged Inc 2 (NOT the ADR-0043 seam).** The de-risked path to
  `sorryAx`-zero `lr_sound`. Staged, each build-gated + banked (lrscope; manager gates per stage):
  1. helper `handlesOp_of_resolvesKind_staticSplit` (✓ proven in prototype) — IN FLIGHT.
  2. `LWStack` into `KrelS`'s handleF clause + re-prove the ~7 handleF-clause consumers (`krelS_handleF`/`_intro`,
     `krelS_append`, `krelS_state`/`transaction_reinstall`, `krelS_staticSplit_decomp`, `krelS_refl` handleF arm, `*_mono`).
  3. `krelS_refl` establishes `LWStack` from `HasStack`.
  4. **STOP-and-SHOW the exact frozen `lr_fundamental` premise** (`WellCapped`/`LWConfig`-open-analogue, shape
     pre-approved) before editing `Spec.lean`; then wire premise → `crelK_fund_up`, close `hcatch`, confirm
     `#print axioms lr_sound` `sorryAx`-GONE.
- **Item 2 — the contextual cancellation gate (`Compat:2188/…`, `crelK_fund` handler arms) — HELD** until Inc 2 lands
  (the `KrelS` change may shift its errors). Design pre-approved: refocus-restructure first (push `handleF` before
  closing the body), fall back to the contextual cancellation lemma.
- **End state (the payoff):** `#print axioms lr_sound`/`lr_fundamental` ⊆ {propext, Classical.choice, Quot.sound},
  `sorryAx` GONE — the ◊4.5b edge closed.

### Refinement (2026-06-25, lrscope) — the cancellation gate is localized; try the refocus-restructure FIRST

The cancellation reduces (build-traced through `crelK_fund @handleThrows`, `Compat:2188`) to **`CrelK`-shiftCap-stability**:
`crelK_fund` over `δ.map shiftCap` ⟹ `EnvRelK (δ.map shiftCap)` ⟹ per-element `VrelK n A v v → VrelK n A (shiftCap v)`
⟹ at `U φ B` ⟹ **`CrelK j B φ c c → CrelK j B φ (shiftCap c)`**. The FREE form is FALSE (bumped caps dispatch
differently in the same `K₁`). The TRUE form is **CONTEXTUAL** — `CrelK` against stacks carrying the absorbing
`handleF` (which `compatK_handleThrows` pushes, but the bare `CrelK` quantifier doesn't). So the cancellation is a
**contextual `CrelK`-stability** indexed by the absorbing-handler context, NOT a free stability lemma.

**Cleaner alternative — TRY THIS FIRST:** restructure `compatK_handle*` to **push `handleF` BEFORE closing the body**,
so the env is naturally at the +1-handler context and `δ.map shiftCap` is the correct env there — **no cancellation
lemma needed** (the shift is absorbed structurally by where the refocus happens). Matches "the shift mirrors the
handleF-push" most directly and may dissolve the gate entirely. If the restructure works, skip the contextual mutual.
