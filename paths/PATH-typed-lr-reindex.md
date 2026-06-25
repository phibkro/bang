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

## Status + remaining work — at `c105904`/`8b6deeb` (2026-06-25)

> **★★ DECISIVE REFRAME (2026-06-25, two-prong de-risk + representation research) — the obstacle is SELF-INFLICTED;
> the fix is a published technique bang HALF-BUILT. Operator COMMITTED to PATH A.**
> bang transcribed Biernacki POPL18's `Vrel/Srel/Krel/Crel` (the LR template) but DROPPED Biernacki's **`n-free`**
> predicate when it swapped labels for de-Bruijn caps — and never put back an equivalent. That single omission IS
> both LR obligations: `hcatch` (cap-resolution) = missing `n-free`; the env cap-shift cancellation (3 handler arms)
> = Biernacki's `Q ↑ l`, which cancels because crossing a handler shifts `ρ` +1 in LOCKSTEP. **Both fall out of ONE
> carry** (confirmed by prong-1's cascade + prong-2's literature). The fix = carry `ρ-free`/`HasStack`-compatibility
> in `KrelS` (= the "typed-KrelS reshape" the code comments already prescribe = restrict `CrelK`'s `K₁` to
> well-capped stacks). It is the CORRECT statement, not a compromise: `lr_sound` over well-capped contexts (the
> unrestricted form is FALSE — same reason the typed-`⊑` restriction exists). **In-envelope with typed-`⊑`.**
> - **De-risk findings (build-grounded):** cheap paths CLOSED — the invariant MUST live in `CrelK`/`KrelS` (touches
>   frozen `lr_sound`/`lr_fundamental`); `closeC`-restructure is kernel-FORCED (off the table); the `WellCapped Γ c`
>   term-premise can't reach `CrelK`-internal `K₁`. Cost = index-everything ripple (est. ~52 LR / 113 Compat / 7 Spec).
> - **Alternatives (rep research, `references/papers/3-lr/biernacki-popl18`; Effekt; Koka):** B = absolute/level caps
>   (cap from root, not de-Bruijn from use-site) → obligation 2 vanishes DEFINITIONALLY (no shift under binders);
>   small kernel retag, complements A. C = capability-as-value (Effekt) → dissolves both but a DIFFERENT kernel
>   (re-derive VM/compiler) → reserve for named handlers, post-v1.
> - **IN FLIGHT:** lrscope prototyping A NON-COMMITTING — confirm (i) the 4/5 cascade, (ii) real ripple, (iii) the
>   exact frozen `lr_sound` statement → **STOP-and-show before any committed `Spec.lean` edit**. Bank `8b6deeb`
>   (item-1 dispatch re-key + `hcatch` documented + dup-deleted). The seam is now the FALLBACK, not the destination.


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
