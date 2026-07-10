<!-- note-status: active -->
# Stage-5 LR design map — the user-effect binary LR (#44 Stage 5)

> **Verdict (one sentence).** Stage 5 is **ONE grind session, not more**: the ADR-0092
> §D3-as-landed **ret-shape** clause restriction makes the custom resume focus
> definitionally a `ret`-of-closed-value (build-checked, `custom_resume_is_ret`), so the
> three debts are **mechanical transcriptions of the already-proven state/txn arms** —
> the hard continuation-capture case D3 was designed to exclude *does not arise in v1*.
> The riskiest arm is `krelS_custom_reinstall` (debt 2), whose only genuinely new
> sub-proof is a `HandlerRel`-custom relation + a substituted-clause-value `VrelK` helper;
> the rest is a copy of `krelS_state_reinstall`, and it is **strictly simpler** (read-only
> param ⟹ the reinstall diagonal is `p=p`, where state's `put` reinstalls a *changed* value).

Probe branch `probe-stage5-lr`, witness `scratch/Stage5LRProbe.lean` (all three statements
compile with `sorry` against main; `custom_resume_is_ret`/`ClauseRel` fully elaborate).
Census: the probe is scratch (not imported by `Bang/Audit.lean`) → feeds NOTHING in
`just axioms`. The three real debts are the four already-flagged `lr_*` stubs
(`crelK_fund`/`krelS_refl` custom arms, `BinaryLR.lean`; `dispatchOn_rename` custom arm,
`LR.lean`) — all inside the flagged-7 `lr_sound`/`lr_fundamental` set; Stage 5 adds NO new
flagged headline and, when done, un-flags nothing new (it closes the custom slice *within*
the still-deferred `lr_sound` cluster — see the PATH W1/W2 walls, orthogonal to these debts).

## The ret-shape tractability answer (the probe's most valuable output)

ADR-0092 §D3-as-landed pins each v1 clause body to `Comp.ret w` (`HasClauses.cons`, with
`w : opRes ℓ op` under `[arg@0, param@1]`). The machine's custom resume focus
(`Dispatch.dispatchOn` custom arm) is

```
  Comp.subst p (Comp.subst (Val.shift v) clause.2)
```

With `clause.2 = Comp.ret w` and `Comp.substFrom k _ (.ret w) = .ret (Val.substFrom k _ w)`:

```
  = Comp.ret (Val.subst p (Val.subst (Val.shift v) w))        -- a `ret` of a CLOSED value.
```

This is **exactly** what `state`/`throws`/`transaction` resume produce (`ret <closed val>`).
So `krelS_append`'s resume conjunct — which demands the dispatched config be
`(Sᵢ, Comp.ret r)` with `r₁ ~ r₂` at the perform's returner type — is satisfied with **no
new convergence infrastructure**. The design intent of the ret-shape (make the LR arms
tractable) is **CONFIRMED, not refuted**.

## The three debts

| # | debt | rides | difficulty | new sub-proofs |
|---|------|-------|-----------|----------------|
| 1 | `compatK_handleCustom` | (delegates to debt 2) | LOW — transcribe `compatK_handleState` | none |
| 2 | `krelS_custom_reinstall` | `Nat.strong_induction_on` on the index | MED — the riskiest arm | `HandlerRel` custom arm (`ClauseRel`) · `dispatchOn_custom_isSome` ×2 · `clause_resume_vrel` |
| 3 | `dispatchOn_rename` custom | structural | LOW-MED — a fork | `Val/Comp.VcapFree` (R-1) *or* the `renameH`/`renameCls` cascade (R-2) |

### Debt 1 — `compatK_handleCustom` (`crelK_fund` custom arm, `BinaryLR.lean:2089`)

The direct analogue of `compatK_handleState`/`compatK_handleTransaction`. It is a CONGRUENCE
with no induction of its own: MINT
`(g, K, handle (custom ℓ p cl) M) ↦ (g+1, handleF g (custom ℓ p cl)::K, subst (vcap g ℓ) M)`,
run the cap-quantified body (`hbody g`) through the reinstalling stack (debt 2), tail re-cast
`g→g+1` via `KrelS_g_cast`/`KrelS_eff_cast`.

- **Induction:** none (delegated).
- **Lemmas exist:** `coApproxC_le_reduce`, `KrelS_g_cast`, `KrelS_eff_cast`.
- **Lemmas to build:** `krelS_custom_reinstall` (debt 2).
- **Typing threading:** `HasClauses`/coverage/`HasVTy [] [] p P` come straight off
  `HasCTy.handleCustom` — mirror the state arm's `hgr/hp/hpr/hrestrict/hcs/hsv`.
- **Walls:** NONE structural. Risk is entirely in debt 2. Once debt 2 exists this is a ~20-line
  copy of `compatK_handleState` (`BinaryLR.lean:1768`).

### Debt 2 — `krelS_custom_reinstall` (`krelS_refl` custom arm, `BinaryLR.lean:2180`) — THE RISKIEST ARM

A `custom ℓ p cl` frame over a `KrelS`-related tail self-relates at every index; the resume
conjunct is supplied by GUARDED RECURSION on the index — the **exact skeleton** of
`krelS_state_reinstall` (`BinaryLR.lean:1281`).

- **Induction:** `Nat.strong_induction_on` on the step index. The resume dispatch reinstalls
  `handleF nh (custom ℓ p cl)` (SAME `p`, SAME `cl`: v1 read-only param ⟹ the reinstall
  diagonal is `p=p` — **strictly simpler** than state's `put`, which reinstalls a *different*
  stored value), resumes `ret r`, and `krelS_append`s onto the reinstalled frame at the dropped
  index `m' < m` (the IH).
- **Lemmas exist:** `krelS_handleF_intro`, `krelS_append` (its custom cases currently
  `absurd hHRtop` — see W-a), `KrelS_mono`, `VrelK_mono`.
- **Lemmas to build (three, all mechanical):**
  1. **`HandlerRel` custom arm** — currently `False` (`LR.lean:1655`). Replace with the
     `ClauseRel` shape (sketched in the probe): `ℓ₁=ℓ₂ ∧ cl₁=cl₂ ∧ VrelK n P p₁ p₂` (+ the
     `HasClauses` carrier). Custom analogue of state's `∃ S, VrelK n S s₁ s₂`.
  2. **`dispatchOn_custom_isSome`** ×2 — one-liners like `dispatchOn_state_isSome`
     (`BinaryLR.lean:1388`), un-refuting `krelS_append`'s nested-handleF custom branch.
  3. **`clause_resume_vrel`** — turn `HasClauses.cons`'s `HasVTy [qa,qp] [opA,P] w opR` into
     `VrelK m' (opRes ℓ op) (subst p (subst (shift arg) w))₁ …₂`. The clause value is OPEN under
     two binders; filling the CLOSED param + CLOSED arg makes it closed, then `vrelK_fund`
     applies. The double-subst is the `split`-shape (idx1-then-idx0) already used by the machine.
- **Walls (named honestly):**
  - **(W-a)** `HandlerRel` custom = `False` today. Making it real is a DEFN change in `LR.lean`
    (NOT a frozen statement) that RIPPLES to every `HandlerRel` case-split — mainly
    `krelS_append`'s `| custom => absurd` arms (~4 sites, `grep "HandlerRel"` + the append custom
    branches). MECHANICAL but WIDE — this is the bulk of the session's edit surface.
  - **(W-b)** `krelS_append`'s nested-handleF custom branch needs the `dispatchOn_custom_isSome`
    totality arms (currently `absurd hHRtop`). Trivial once W-a lands.
  - **(W-c)** `clause_resume_vrel`'s binder-fill commutation — `closeC_subst_comm`-style, MECHANICAL.
  - **NO continuation-capture wall** — the ret-shape (above) means resume is `ret r`, never an
    effectful clause needing a first-class `k`. This is the whole tractability payoff.

### Debt 3 — `dispatchOn_rename` custom arm (`LR.lean:791`)

The ONE `sorry` in `dispatchOn_rename`'s custom `some clause` case. `renameH` is IDENTITY on
custom (`LR.lean:480`) but the resume focus contains `p`/`clause.2`, which the RHS `renameC σ`
would rename. The commutation holds **iff** `renameV σ p = p` and `renameC σ clause.2 = clause.2`
— i.e. `p` and every clause body are **`vcap`-free** (rename only touches `vcap`). Every
*elaborated* custom clause IS vcap-free (params/clauses are closed source values; caps enter only
via `handle`-mint at runtime, never inside a clause literal).

- **Rename family:** joins `renameV`/`renameC`/`renameH`/`renameK` (`LR.lean:452-488`) + the
  `renameC σ (Comp.subst …) = Comp.subst (renameV σ …) …` commutation family.
- **THE FORK (ADR-input):**
  - **(R-1)** `VcapFree` side condition. Define `Val.VcapFree`/`Comp.VcapFree`, prove
    `VcapFree t → renameV/C σ t = t`, thread `VcapFree p ∧ ∀ c ∈ cl, VcapFree c.2` through
    `dispatchOn_rename` and its callers (`idDispatch_rename`, the `step`-rename keystone). SMALL
    (~2 defs + 2 identity lemmas) but the side condition ripples up to the keystone's callers.
  - **(R-2)** Make `renameH` TRAVERSE custom (rename `p` + map-rename clause bodies). Then the
    commutation is the structural `renameC_subst` twin — but costs the ~15-lemma
    `renameH`/`renameCls` mutual cascade (nested-inductive termination, the `capsCls` twin) the
    PATH ledger (line 76-79) already names as "this path's re-index shape".
  - **RECOMMENDATION:** R-1 for Stage 5 (true by elaboration, small); R-2 is the ◊5+ clean-up the
    PATH already banks as the eventual shape.

## Slice plan (the grind unit executes in this order)

1. **`HandlerRel` custom arm → `ClauseRel`** (W-a) + un-refute the ~4 `krelS_append` custom
   branches with `dispatchOn_custom_isSome` (W-b). *Green build gate here — this is the widest
   edit; land it first and isolated.*
2. **`clause_resume_vrel`** (W-c) — the substituted-clause-value `VrelK` helper.
3. **`krelS_custom_reinstall`** (debt 2) — strong-induction copy of `krelS_state_reinstall`,
   using 1+2. *Un-`sorry`s the `krelS_refl` custom arm.*
4. **`compatK_handleCustom`** (debt 1) — copy of `compatK_handleState` over debt 2.
   *Un-`sorry`s the `crelK_fund` custom arm.*
5. **`dispatchOn_rename` custom** (debt 3, route R-1) — `VcapFree` + thread the side condition.
   *Un-`sorry`s the `LR.lean` custom arm.*
6. Gate: `just axioms` still 7-flagged (no new headline); `lr_sound`/`lr_fundamental` axiom set
   UNCHANGED (the W1/W2 cluster sorries remain — those are orthogonal, PATH-inc5).

Steps 1–4 are `BinaryLR.lean`/`LR.lean` `HandlerRel`; step 5 is `LR.lean` `dispatchOn`. All one
writer, one session. Estimated: one focused grind session (the edit surface is W-a's ripple; the
proofs are transcriptions).

## ADR-inputs

- **Riskiest arm:** debt 2 (`krelS_custom_reinstall`) — specifically W-a's `HandlerRel`-custom
  ripple (the edit surface), not the proof (a transcription).
- **Is Stage 5 one grind session or more?** ONE, contingent on the ret-shape holding — which the
  probe CONFIRMS (`custom_resume_is_ret` builds). If a future D5 lifts the ret-shape (effectful
  clause bodies), THIS map is void: the continuation-capture case returns and Stage 5 becomes a
  multi-session first-class-`k` problem. The ret-shape is load-bearing for the one-session estimate.
- **Debt-3 fork** (R-1 vs R-2) is a real decision the grind must record — recommend R-1 now, R-2 at ◊5+.
- **No frozen-statement change** is needed for any debt (`HandlerRel` is a proof-layer DEFN, not a
  Spec statement). Stage 5 does NOT touch the W1/W2 `lr_sound`/`lr_fundamental` deferral (#15).

## Ground

`scratch/Stage5LRProbe.lean` (this probe) · `paths/PATH-inc5-lr-reindex.md` (banked debts,
W1/W2) · ADR-0092 §D3-as-landed (ret-shape) · ADR-0085/0087 (custom rep) ·
`BinaryLR.lean:1281` (`krelS_state_reinstall` = the exemplar) · `BinaryLR.lean:1768`
(`compatK_handleState`) · `Dispatch.lean:177` (the custom resume focus) ·
`Typing.lean:317,344,428` (`HasCTy.handleCustom`/`HasClauses`/`HasStack.customF`).
