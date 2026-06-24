# PATH — ◊4.5b finish: the append crux + the (g) re-point

**Status:** THROWS CLOSED end-to-end in the new arch (cap45-modality @ 3eca3ce, build GREEN,
axiom set clean: no_accidental 0-axiom, compile_correct trusted-three). The whole ◊4.5b moat is
reduced to ONE research crux + the (g) mechanical migration. Two INDEPENDENT remaining pieces.

## What is DONE (committed 86a906f → 3eca3ce, all green + axiom-gated)

- **`h₁=h₂` handleF clause** (`LR.lean` KrelS) — equal handlers ⇒ `splitAt` fires identically.
- **RESUME CONJUNCT** in KrelS's handleF clause — op-arg-keyed (`opArg h.label op`) under a
  `handlesOp h h.label op` guard, so suppliers pin the resume value's type from the handler
  interface. (The producer lacks `HasStack`; the conjunct CARRIES the typed resume.)
- **`krelS_splitAt_decomp`** (Compat) — extracts same-handler split + related outer tails +
  the resume conjunct at the catching frame.
- **`Handler.label`, `handlesOp_label`, `splitAt_some_handlesOp`** (helpers).
- **THROWS supplies SORRY-FREE**: `compatK_handleThrows` + `krelS_refl` handleF arm (via `crelK_ret`).
- **Producer `up` THROWS sub-case CLOSED** in `crelK_fund` (decompose → []-prefix dispatch agrees
  for throws → `coApproxC_le_anti_step` + extracted `hres`; type alignment from `hArg`+`handlesOp_label`).
- mono/eff lemmas thread the conjunct; WF intact.

## REMAINING PIECE 1 — the `krelS_append` crux (RESEARCH or SEAM; operator decision)

The ONE research question, in 6 new-arch spots that are all THE SAME: `compatK_handleState`,
`compatK_handleTransaction`, `krelS_refl` state/txn arms, `crelK_fund` producer state/txn arms.
- **The crux:** state/txn dispatch KEEPS `Kᵢ` and reinstalls the handler:
  `dispatchOn op v (Kᵢ, state ℓ s, Kₒ) = (Kᵢ ++ handleF (state ℓ s')::Kₒ, ret r)`. The `[]`-prefix
  resume conjunct must bridge to the producer's `Kᵢ`-prefix via **`krelS_append`** (compose the
  kept `Kᵢ` + reinstalled handler + `Kₒ`), AND the **▷-metering** must compose so the 1 dispatch
  step stays payable (likely the resume conjunct at `m<n` per `coApproxC_le_anti_step`, LR:140).
- **Throws needs NONE of this** (`Kᵢ` discarded regardless of length) — hence throws closed cleanly.
- **SEAM fallback (ADR-0026):** if the metering walls after a real attempt, the state/txn-resume
  producer is the tested-superset descent (throws-handlers verified, state/txn-resume diff-tested).

## REMAINING PIECE 2 — sub-block (g), the re-point (MECHANICAL, ~147 old-arch lemmas)

`lr_fundamental` is still wired to the OLD `crel_fund` (over `Crel`/`Krel`/`Srel`); `lr_sound`
(Spec:174) is still `sorry`. (g) wires the headline theorems onto the new arch:
- Redefine frozen `Crel := CrelK`, `Vrel := VrelK`, `EnvRel := EnvRelK` (body swap, **signature
  byte-identical** — the frozen statements don't change).
- Delete old `Krel`/`Srel` + their lemma blocks + old `vrel_fund`/`crel_fund`/`krel_refl`
  (~147 lemmas reference the old bodies; ~218 mentions in Compat). This is the bulk.
- Rewire `lr_fundamental := crelK_fund`; prove `lr_sound` via `lr_sound_closed ∘ krelS_refl`.
- **This is careful REFACTORING, not research.** Best done in a FRESH context (Context-Rot risk on
  a 147-lemma body-swap in a long session). Build-gate incrementally; the gate cannot pass
  mid-migration (the additive-then-migrate sequencing note in PATH-cap45-rebuild applies).

When (g) lands AND the append crux resolves (research or seam): `lr_sound`/`lr_fundamental` →
trusted-three = the full contextual-equivalence moat.

## Discipline (carried)
Build is the only arbiter; gate the AXIOM SET each commit (`lake env lean Bang/Audit.lean`).
flag-before-build the metering. Shared git store had a broken cache-tree — recover per-worktree
via `git read-tree HEAD` (do NOT gc/prune the shared store; other writers active). Backup +
validated probes at `/tmp/cap45-backup/`.
