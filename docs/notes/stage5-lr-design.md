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

---

## RESOLUTION (krnl lane, 2026-07-10) — the two residuals after s5grind, machine-checked

s5grind landed the compat cores (`compatK_handleCustom`, `krelS_custom_reinstall`,
`custom_clause_resume`/`_of` — all PROVEN, clean). What remained were TWO residuals; this
section is the DEFINITIVE map (supersedes the "LOW/SMALL" estimates above for these two).

### Debt-1 residual — the `crelK_fund` handleCustom in-block delegation (the DESIGN PIN)

**The wall (machine-checked, not budget).** The `crelK_fund`/`vrelK_fund` PROOF mutual block
(`BinaryLR.lean:1405`, SEPARATE from the frozen `VrelK/CrelK/KrelS` DEF block at `~1537`) is
**structural recursion over the typing derivation** (`cases h with` on `HasCTy`). The custom
arm needs `vrelK_fund` on the CLAUSE param/body, which come from the SEPARATE `HasClauses`
hypothesis `hcl` (via `hasClauses_find?_typed hcl hf`), NOT a sub-derivation of the scrutinee
`h`. The structural-recursion checker only credits recursion on sub-terms of the SCRUTINEE, so
it can NEVER see this call as decreasing.

**Do-not-retry ledger (all machine-checked this session):**
- **(a) in-block via `custom_clause_resume_of (vf := @vrelK_fund)`** — REFUTED. Default budget →
  `isDefEq` timeout (200k); `set_option maxHeartbeats 1000000` → `fail to show termination …
  failed to infer structural recursion`.
- **(c) standalone closed-value lemma** — REFUTED (s5grind): `VrelK`'s U-clause routes
  thunk-typed values through `CrelK`, and `opR` can be `U φ B`, so no block-free specialization.
- **Fix 1 (inline `custom_clause_resume_of`'s body so `vrelK_fund hw` is syntactic)** — REFUTED.
  Same `fail to show termination … Please use termination_by`: `hw` is still from `hcl`, not the
  scrutinee. Inlining does not change what the checker credits.

**THE FIX — Fix-2b, height-indexed (the ONLY viable shape; keeps the frozen type):**

1. **Height functions** over the mutual `HasVTy`/`HasCTy`/`HasClauses` derivation:
   `htV : HasVTy … → Nat`, `htC : HasCTy … → Nat`, `htCl : HasClauses … → Nat`, each
   `= 1 + max(children heights)`. CRUX: `htC (handleCustom hcl … hM …)` must strictly exceed
   `htCl hcl` (so the clause derivations `hasClauses_find?_typed` extracts are at strictly
   smaller height) AND `htC hM`. (Lean's auto-`sizeOf` on the mutual inductive may already give
   this — TRY `sizeOf` first; only hand-roll `htC` if `sizeOf`'s cross-mutual accounting doesn't
   credit `HasClauses` sub-derivations. Build-arbitrate which.)
2. **Height-indexed twins** proven by `induction k` (well-founded on `k : Nat`, NOT structural on
   the derivation — this is what dodges the wall):
   ```
   vrelK_fund_at : ∀ k, HasVTy γ Γ v A → htV h ≤ k → ∀ n δ₁ δ₂, EnvRelK n Γ δ₁ δ₂ → VrelK n A (closeV δ₁ v) (closeV δ₂ v)
   crelK_fund_at : ∀ k, HasCTy γ Γ c e B → htC h ≤ k → ∀ n δ₁ δ₂, EnvRelK n Γ δ₁ δ₂ → CrelK n B e (closeC δ₁ c) (closeC δ₂ c)
   ```
   In the `handleCustom` arm, the `vrelK_fund` calls on the clause param/body invoke
   `vrelK_fund_at (k-1)` at their strictly-smaller heights (`htV hp < htC h`, `htV hw < htC h`
   through `htCl`), and the recursive body call is `crelK_fund_at (k-1) hM`. The `k=0` base is
   vacuous (`htC h ≤ 0` is impossible since every `htC ≥ 1`).
3. **Post-block, the FROZEN twins recover byte-identically** (this is what keeps `Spec.lean:248`
   `lr_fundamental h := crelK_fund h` untouched):
   ```
   theorem crelK_fund (h : HasCTy γ Γ c e B) : ∀ n δ₁ δ₂, EnvRelK n Γ δ₁ δ₂ → CrelK n B e (closeC δ₁ c) (closeC δ₂ c) :=
     crelK_fund_at (htC h) h (le_refl _)
   -- and likewise vrelK_fund := vrelK_fund_at (htV h) h (le_refl _)
   ```
   The type of `crelK_fund` is BYTE-IDENTICAL to the current one (`BinaryLR.lean:1453`), so
   Spec.lean:248, `custom_clause_resume` (`:1669`), and `krelS_refl` are all untouched.

**Which arms recurse at strictly-smaller height:** every arm that today calls `vrelK_fund`/
`crelK_fund` recursively — `vthunk` (`crelK_fund` on the thunk body), `inl`/`inr`/`pair`/`fold`
(`vrelK_fund` on payloads), the `handle*` arms (`crelK_fund hM`), and the NEW custom arm
(`vrelK_fund` on `hp`/`hw` via `htCl`, `crelK_fund hM`). All are structural children ⟹ strictly
smaller `htC`/`htV`/`htCl` ⟹ within `k-1`.

**Frozen-DEF-block untouched:** the `VrelK/CrelK/KrelS` DEF block (`:1537`, measure
`(n,_,_,sizeOf _)`) is NOT touched — Fix-2b only restructures the PROOF block's recursion from
implicit-structural to explicit-`k`-induction. No `set_option` on the frozen block; the frozen
block's 200k-budget heartbeat inference is not perturbed (a separate block).

**Slice plan for the grind (fresh unit):**
1. Define `htV`/`htC`/`htCl` (or confirm `sizeOf` suffices) + the `htC (handleCustom) > htCl hcl`
   lemma. *Green gate.*
2. State `vrelK_fund_at`/`crelK_fund_at`; port the NON-custom arms verbatim (they're the current
   arms with `_at (k-1)` on recursive calls + the `htX child < htX h ≤ k` side-goals by `omega`).
   *Green gate — this is the bulk, mechanical.*
3. Add the custom arm using the (proven) `compatK_handleCustom` + an inline/`_of` `hclause` now
   calling `vrelK_fund_at (k-1)` on the clause derivations. *Un-sorries the custom arm.*
4. Post-block: `crelK_fund`/`vrelK_fund` = `_at (htX h) h (le_refl _)`. *Byte-identical type;
   Spec.lean:248 rebuilds unchanged.*
5. Gate: `just axioms` — `lr_fundamental`/`lr_sound` LOSE nothing but the custom-arm `sorryAx`
   contribution (the W1/W2 cluster sorries remain, orthogonal); 16 clean headlines byte-unchanged.

**Budget note:** this is a multi-session grind (the `_at` port + the height lemmas). The manager's
call is whether it runs on the current unit's budget or a fresh unit — this pin is written so a
FRESH unit can grind it cold.

### Debt-3 residual — the R-1 `dispatchOn_rename` custom sorry is in DEAD CODE

The Debt-3 R-1 plan above ("thread `VcapFree` through `dispatchOn_rename` → `idDispatch_rename`
→ the step-rename keystone") is **VOID**: that keystone chain is **dead code**. Ref-verified
(krnl, 2026-07-10, clean tree): the chain `dispatchOn_rename → idDispatch_rename → step_rename
→ run_rename → run_rename_converges → run_bump_converges` has ZERO live callers — 0 refs outside
`LR.lean`; the terminus `run_bump_converges` has no caller at all (only its def + one prose
comment at `:1961` that says "the OLD frozen-counter form"). The route-1 `crelK_ret` refactor
orphaned it (`LR.lean:515`: "crelK_ret (route-1 form) bridges … no Canonical/CapsBelow/run_bump").
The `by sorry` at `LR.lean:1018` sits inside this dead chain. **Correct move: DELETE the 6 dead
chain lemmas** (removes the sorry + dead code) rather than thread a premise into lemmas nothing
consumes. Deletion is surgical (the 6 are interleaved with the LIVE `renameCfg`/`bumpσ`/
`CapsBelow`/`renameK_capsBelow` machinery — 102 live refs outside LR — so delete ONLY the 6
theorems + any helper uniquely consumed by them; build + axiom-diff arbitrates). Gated behind an
operator delete-vs-thread ruling (census-adjacent: the deletion may remove a `sorryAx` from a
flagged headline, which shrinks the flagged set — a ledger event).
