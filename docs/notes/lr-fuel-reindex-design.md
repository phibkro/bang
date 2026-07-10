# LR fuel-reindex design map (ADR-0096 (β), slice 1)

**Status**: slice-1 de-risk LANDED. The fuel-indexed twin def block + the two obstruction analogs +
the SKIP-strip crux SHAPE all build; the crux composition typechecks end-to-end and does NOT invoke
`krelSN_hole_det`. What remains is characterized and sliced. Branch `feat-lr-fuel-reindex`; module
`Bang/Meta/LRFuel.lean` (beside LR/BinaryLR, neither modified).

## What (β) is

Re-index the LR family by an explicit FUEL index `f : Nat` as a JUDGMENT INDEX (Prop-valued, index
descends by construction at each constructor) — NOT a derivation-height OVER the Prop (machine-refuted:
Prop large-elim, see ADR-0096 amendment ③). The twin `KrelSN n f`/`CrelKN n f`/`VrelKN n f` carries the
metering index `n` UNCHANGED (thunk/letF-body ▷-guards, `CoApproxC_le n`) plus a SECOND fuel `f` that
DESCENDS at the handleF resume conjunct: the captured continuation `Kᵢ` and its result `Sᵢ` sit at
`KrelSN m fᵢ … Kᵢ Kᵢ'` with `fᵢ < f`. That makes the SKIP-strip self-recursion structurally descending
on `f` — the termination the LR `krelS_append_inv` lacked.

## Index-placement decisions (the load-bearing choices)

| conjunct | fuel behaviour | why |
|---|---|---|
| nil return-half | inert (threaded) | no stack recursion |
| letF body / tail | KEEP `f` | doesn't cross the resume seam |
| appF cap / tail | KEEP `f` | same |
| handleF tail | KEEP `f` | tail is same-depth |
| **handleF resume conjunct** | **DESCEND `fᵢ < f`** on `Kᵢ` AND on the result `Sᵢ` | the resume seam — the crux |

Termination: lex `(n, role, f, stackLen, sizeOf)` — the fuel `f` slots between `role` and `stackLen`,
so a fuel drop at the resume conjunct decreases even when `n`/`role`/`stackLen` hold. Builds clean.

## Slice-1 deliverables — status (per the axiom gate, real output)

CLEAN (⊆ `{propext, Classical.choice, Quot.sound}`, sorry-FREE):
- `KrelSN` def block + `krelSN_nil/letF/appF/handleF` eq-lemmas — `[propext, Quot.sound]`
- **`KrelSN_g_cast`** (obstruction analog i) — `[propext, Quot.sound]`. **THE KEY POSITIVE**: the
  reverse `g'→g` cast on the captured continuation `Kᵢ` (which KILLED fork (a)'s monotone cast,
  `CarrierForkA.monotone_gcast_cannot_serve_contravariant_resume`) is now a call at fuel `fᵢ < f` —
  STRUCTURALLY DESCENDING, so the cast stays FULL-GENERAL. The fuel index does NOT reintroduce the
  contravariance kill. Termination `(f, K₁.length)`.
- `krelSN_stackInc`, `krelSN_handleF_intro` helpers — `[propext, Quot.sound]`

FLAGGED (carry `sorryAx` — the honest slice-2 residual, each named):
- `KrelSN_fuel_mono` — fuel-DOWN monotonicity. FINDING: fuel-DOWN is the FREE direction (the resume
  conjunct's `∀ fᵢ < f'` is a sub-range of `∀ fᵢ < f` when `f' ≤ f`, fires directly — the crux arm is
  structurally correct, sorry-free in that arm). Fuel-UP is NOT free (needs a resume witness at `fᵢ = f`
  the derivation lacks). The letF/appF/state arms sorry ONLY on the `VrelKN`/`CrelKN` mutual fuel-mono
  (slice-2 mutual block). Consumers need fuel-DOWN (a producer synthesizes high, a consumer at `f' ≤ f`
  accepts) = the free direction. NEITHER-direction would have refuted (β); fuel-DOWN holding is the pass.
- `krelSN_append_inv` — the fuel-descending STRIP. WF on the fuel: the handleF-in-prefix self-recursion
  re-strips at fuel `< fₒ`, terminating (the IH the LR's `AppendInvWF` lacked; the `Dⱼ=Dᵢ` refutation
  `c8b5909` IS that missing IH surfacing as a false cross-answer). Answer = OUTPUT existential (carried).
- `krelSN_splitAtId_decomp` — THE CRUX. HIT + letF/appF-SKIP arms CLOSE sorry-free. The handleF-SKIP arm
  COMPOSES end-to-end (lift `dispatchOn_append_outer` → fire `hres` at `fᵢ` → strip `krelSN_append_inv`
  at `fᵢ-1` → reassemble), reduced to ONE named residual + a fuel-floor sub-sorry.

## THE CRUX — what slice 1 established, honestly

**The fuel design's SKIP-arm composition typechecks WITHOUT `krelSN_hole_det`.** The LR wall was
`Cb' = C'`: a tie between `hres`'s RE-DERIVED hole and `ih`'s independent `C'`, needing the machine-FALSE
`krelS_hole_det` (`HoleDetRefute`, do-not-weaken). The fuel twin replaces that with a tie between TWO
FUEL-CARRIED DECOMP OUTPUTS (the strip's `Dstrip` existential + `ih`'s `Dᵢ`) — both carried, both
fuel-indexed, NEITHER re-derived. This is the reduction (β) promised: the wall is no longer a false
statement, it is a well-founded strip + an existential-coincidence.

**The remaining crux obligation (the ONE named residual, `krelSN_splitAtId_decomp` handleF-SKIP):**
1. `Dstrip = Dᵢ` — the two carried decomp existentials coincide. NOT `krelS_hole_det` (that tied a
   re-derived hole to `ih`); this ties two OUTPUT existentials the fuel-descent threads. slice-2.
2. fuel-align: the strip produces at `fᵢ-1`, the OUTPUT conjunct demands `fᵢ` — a fuel-UP the design
   must absorb (candidate: state the OUTPUT resume conjunct's result at `< fᵢ` too, so no up-cast; OR
   the fuel-synthesis bridge picks a fuel high enough. A slice-2 def-shape decision, flagged).
3. fuel-floor: `fᵢ > 0` (else the resume supply is vacuous) — a `crelKN 0`-style def-vacuity lemma.

**Honest deviation from amendment ③'s (β) price.** ③ priced (β) as "the wall closes" once the re-index
lands. Slice 1 SHARPENS this: the re-index closes the LOCATION + TERMINATION halves (the g-cast survives
full-general; the strip self-recursion is WF on fuel), and REDUCES the answer-coherence from a FALSE
`hole_det` to an existential-coincidence between two fuel-carried outputs — but that coincidence + the
fuel-UP/floor are NOT free; they are the slice-2 substance. (β) is NOT refuted (no false statement
surfaced in the twin) — it is confirmed VIABLE with the crux reduced to a characterized, non-false
obligation. This is the de-risk slice 1 existed to deliver: (β) as priced is SOUND; the grind is real.

## Slice-2 map (the 37-decl grind, sliced)

1. `VrelKN`/`CrelKN` fuel-mono mutual block → closes `KrelSN_fuel_mono` fully (unblocks the strip's
   fuel-align + the appF/letF/state arms). ~6 decls.
2. `krelSN_append_inv` proper — the fuel-WF self-recursive strip (mirror `AppendInvWF`, fuel as measure).
   Closes the crux's `Dstrip`-side. ~8 decls.
3. The crux's `Dstrip = Dᵢ` coincidence + fuel-floor vacuity + fuel-UP resolution → `krelSN_splitAtId_decomp`
   sorry-free. ~4 decls.
4. Re-prove the ~19 `crelKN_/vrelKN_/compatK_*` compat decls against the twin (mechanical once 1–3 hold).
5. The bridge `krelS_iff_exists_fuel` (fuel-synthesis ⟹ + fuel-erasure ⟸) — the LAST step, recovers the
   frozen `Spec.lean` `lr_*` byte-identical. ~6 decls incl. the `HasCTy` collapse.

Census unchanged: (β) sheds `lr_fundamental` + `lr_fundamental_closed` (18→20); `lr_sound`'s third shed
still needs Q22 (held). No frozen `Spec.lean` change — the fuel index is internal to `CrelKN`/`KrelSN`.

## Ground

`Bang/Meta/LRFuel.lean` (the twin; def block + eq-lemmas + `KrelSN_g_cast` + helpers CLEAN; the three
flagged decls) · `Bang/Witness/HoleDetRefute.lean` (`krelS_hole_det_refuted` — the do-not-weaken falsifier
the fuel design DODGES, never invokes) · ADR-0096 amendment ③ (the (β) ruling + price) · memory
`lr-crelk-custom-arm-termination-wall` fallback (C) (the (β) viability precedent).
