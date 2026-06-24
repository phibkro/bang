# PATH — ◊4.5b: the config-level resume-composition (the research-grade up-producer close)

**Status (2026-06-24, BUILD-GROUNDED — the ready spec):** the FINAL obligation of ◊4.5b — the
resumptive-handler PRODUCER equivalence (state/txn). `lr_sound` is CLOSED modulo exactly this (the
6 Compat sorrys 1224/1247/1485/1488/1575/1581) on **`cap45-final @ a5464da`**. Operator decision:
**wrap now, PURSUE this reshape next session.** Interim honest state = the SEAM (ADR-0026 descent:
throws-handlers VERIFIED end-to-end + state/txn-resume TESTED); this PATH is the ready spec to LIFT
it. Fresh-context job (Context-Rot risk on a relation-def reshape).

> ⚠ **THE METERING WAS A MISDIAGNOSIS** (build-confirmed by the `append` IC, 2026-06-24). The ▷-budget
> composes CLEANLY — the reinstalled-handler config takes ONE handleF-discard step (`(handleF h::K, ret r)
> ↦ (K, ret r)`, Operational:339), discharged by `coApproxC_le_anti_step` + `crelK_ret`; NO metering crux.
> The `krelS_append`/metering framing in the design sketch BELOW is superseded. The REAL wall is the
> resume-conjunct SHAPE — a structural relation-def reshape, three coupled defects:
>
> 1. **Conjunct loses Kᵢ.** The conjunct (LR:516-522) dispatches at `([], h, K')` — Kᵢ baked to `[]`. But
>    state/txn dispatch KEEPS Kᵢ (`dispatchOn` Operational:295 → `Kᵢ ++ handleF(state ℓ s')::Kₒ`). The
>    producer splits at NON-empty K₁ᵢ; `krelS_splitAt_decomp` (Compat:1072) returns only the OUTER-tail
>    relation, NOT the inner-prefix `K₁ᵢ ~ K₂ᵢ` the bridge needs.
> 2. **h₁=h₂ too strong for `put`.** The handleF clause (LR:505-506) forces equal handlers; `put w`
>    reinstalls `state ℓ w₁` vs `w₂` with `w₁ ~ w₂` VrelK-RELATED (not equal). splitAt/handlesOp/
>    Handler.label IGNORE stored state (Operational:230-242) — equal split positions need same label+kind,
>    NOT equal state.
> 3. **Type mediation.** With Kᵢ=[] the resume value `r` (op-result-typed: get→S, put→unit) hits Kₒ
>    (body-typed `F q A`) directly → unprovable `VrelK k A s s` (state at the wrong type, no VrelK_refl).
>    The captured Kᵢ is exactly what transforms `r:opRes` into `A` before Kₒ; dropping it is unsound.

## THE READY PROGRAM — append's (a)-(d), ~68 refs, multi-session, fresh-context

- **(a) Relax the handleF clause** (LR:505-506) — **build-CONFIRMED viable by append** (the def + the
  reshaped `krelS_handleF` simp-lemma COMPILED cleanly): replace `h₁=h₂` with a `HandlerRel` condition —
  throws = label-eq; state = label-eq + `∃ S, VrelK n S s₁ s₂`; txn = label-eq + heap-len-eq + pointwise
  `VrelK`. WF-SAFE: `VrelK n` here is a role-1→role-0 drop, identical to the existing appF cap (checked
  against the `(n,role,stackLen,sizeOf)` metric). The simp-lemma proves via `cases h <;> cases h' <;>
  simp only [KrelS, HandlerRel]`. [task #12 — designed + compile-checked]
- **(b) Extend `krelS_splitAt_decomp`** (Compat:1072) to ALSO return the inner-prefix relation
  `K₁ᵢ ~ K₂ᵢ` (+ anti-handler side-cond: Kᵢ has no catching frame — structurally true from splitAt).
- **(c) Reshape the resume conjunct** to quantify over related captured continuations `Kᵢ ~ Kᵢ'` and
  relate the FULL reinstalled configs (this IS the real `krelS_append`: compose the relational-state
  handler onto related-Kᵢ + related-Kₒ).
- **(d) Re-prove** `KrelS_mono` / `KrelS_eff_{cast,anti,mono}` handleF cases (the state-relation threads
  like VrelK in appF) + the 6 consumer sites.

Closing (a)-(d) → the 6 Compat sorrys close → `lr_sound` FULL trusted-three = **THE MOAT** (contextual
equiv incl. resumptive handlers). Base `cap45-final @ a5464da`. SEAM (ADR-0026) is the interim state.

---
*Below: the original metering-framed sketch (by cap45f), SUPERSEDED by the build-grounded program above —
kept for the `krelS_append` shape intuition, but the inner-prefix relation (not the metering) is the missing piece.*

> Two cheap routes are DEAD (build-arbitrated): discharge-vacuity (`krelS_splitNone`) is FALSE —
> `HasStack.splitAt_fires` (Metatheory:1877) proves a φ-stack with `ℓ≤φ` not-escaping-`ℓ` DOES
> handle `ℓ`, so the some-half is real, not vacuous. Resume-composition is the ONLY sound route.

## The precise obligation
After `rw [CrelK]; intro D K₁ K₂ hK`, the up case is `CoApproxC_le n (K₁, up ℓ op v₁) (K₂, up ℓ op v₂)`
with `hK : KrelS n (F q B) D φ K₁ K₂`, `ℓ ≤ φ`, `hv` (v₁,v₂ VrelK-related at opArg). `step (Kᵢ, up ℓ op vᵢ)
= (splitAt Kᵢ ℓ op).bind (dispatchOn op vᵢ)`. Two halves:
- **NONE half** (`splitAt=none`): DONE — `not_convergesC_le_up_splitNone` (stuck ⇒ premise False).
- **SOME half** (`splitAt=some`, the research piece): the φ-stack HANDLES `ℓ` (splitAt_fires). Must
  relate the DISPATCHED configs.

## Dispatched-config shapes (Operational.lean:280-312)
`splitAt Kᵢ ℓ op = some (Kᵢⁱⁿ, h, Kᵢᵒᵘᵗ)`; `dispatchOn`:
- **throws:** `(Kᵢᵒᵘᵗ, ret vᵢ)` — ZERO-shot abort: Kᵢⁱⁿ + handler DISCARDED. **Simplest — close FIRST.**
- **state:** `(Kᵢⁱⁿ ++ handleF(state ℓ s')::Kᵢᵒᵘᵗ, ret s)` — ONE-shot resume: Kᵢⁱⁿ KEPT, handler REINSTALLED.
- **txn:** as state, heap threaded.

## Why CrelCtx-over-plug does NOT port (the config-level crux)
The scratch `CrelCtx … → Crel n D ε (plug K₁ c₁) (plug K₂ c₂)` observes `plug K c`. The current
`CrelK` observes the FOCUSED config `(K,c)` via `CoApproxC_le`, NEVER `plug K c` (LR:482-487) — the
deliberate move that killed the `+K.length` run_plug refocus offset (the lr45 wall). Re-introducing
`plug` at the compose seam re-introduces that offset INSIDE the metering (`CoApproxC_le` counts LEFT
machine steps; the `K.length` push-to-refocus steps would be charged against the n-budget, breaking
the ▷-accounting). So Lemma-2 must be re-expressed **config-level**.

## The config-level KrelS-APPEND (the replacement for Biernacki Lemma 2)
```
krelS_append : KrelS n C D ε Kₐ Kₐ' → KrelS n D E ε' K_b K_b'
             → [anti-handler side-cond] → KrelS n C E ε'' (Kₐ ++ K_b) (Kₐ' ++ K_b')
```
(inner stack's answer type D = outer stack's hole type). KrelS clauses recurse stack-structurally
(frames peel) ⇒ append threads by induction on Kₐ — BUT **the metering interaction is the research
crux**, NOT the structural append: KrelS's frame-body Crel calls are ▷-guarded (`∀m<n`); appending
composes two ▷-budgets, and whether the budget ADDS (n+n') or stays n at the seam determines if the
resume's one machine step (the dispatch) is payable (likely needs the resume conjunct at `m<n`,
matching `coApproxC_le_anti_step`'s drop, LR:140).

## The def change — handler-relatedness + resume clause on handleF
```
| handleF h::K₁', handleF h'::K₂' =>
    ∃ ℓ_h φ', h = h' ∧ (h handles ℓ_h) ∧ ε ≤ labelEff ℓ_h ⊔ φ' ∧ KrelS n C D φ' K₁' K₂'
    ∧ (RESUME: ∀ related resume-values u₁ u₂ at opRes ℓ_h, the dispatched configs relate at ▷ (m<n))
```
The resume conjunct is the OLD Srel output clause (LR:554-555) re-expressed config-level + answer-typed.
- **throws** degenerates: abort discards Kᵢⁱⁿ ⇒ resume = `CoApproxC_le (Kᵢᵒᵘᵗ, ret v) …` = KrelS's
  return-half at Kᵢᵒᵘᵗ — NO append. Close first (feasibility gate).
- **state/txn**: reinstall + continue ⇒ needs `krelS_append` (Kᵢⁱⁿ ++ reinstalled-handler :: Kᵢᵒᵘᵗ) +
  the metering. The hard part.

## Anti-handler side-condition (blaze §2.3)
`krelS_append` crossing a handleF frame for a THREADED effect (state/txn — Kᵢⁱⁿ captured + reinstalled)
is UNSOUND without the `0-free`/`n-free`/traversable condition (the inner captured Kᵢⁱⁿ must not itself
handle the threaded `ℓ`, else the reinstall double-handles). **Bake into `krelS_append`'s premise.**

## Plug-in + consumer interaction
up some-half: `splitAt_fires` → `some (Kᵢⁱⁿ,h,Kᵢᵒᵘᵗ)`; a new `splitAt`-decomposition lemma extracts
the handleF resume conjunct from `hK`; that feeds the dispatched-config relatedness; `coApproxC_le_anti_step`
bridges the one dispatch step. The 6 CLOSED consumer cases (compatK_handle*/krelS_refl) make
EQUAL-handler stacks (trivially `h=h'`) but now must SUPPLY the resume conjunct — for `krelS_refl` it
self-relates via `crelK_fund` recursion (the ▷-guarded continuation pattern already in `krelS_letF_intro`);
for `compatK_handle*` from the body. So the 6 cases get heavier, along a known pattern.

## The research crux (for the pair)
NOT the structural append (mechanical). It's: **(1) the METERING at the append seam** — does the
▷-budget compose so the dispatch's machine step is payable; **(2) WF termination of `krelS_append`**
in the mutual block (answer-type inert, but append changes `stackLen` non-trivially — the
`(n,role,stackLen,sizeOf)` metric must still decrease); **(3) `plug_append`** is NOT in the tree (PATH
"banked" it but unproven) — needed if any `plug` survives the adequacy bridge.

## Plan
1. **THROWS first** (return-half only, NO append) — the feasibility gate. If even this doesn't close,
   the resume-clause shape is wrong; STOP+report.
2. Then **state/txn** with `krelS_append` + the metering (the research crux).
3. Re-supply the resume conjunct in the 6 closed consumer cases (known pattern).
4. Close the up some-half; (g) re-point → `lr_sound`/`lr_fundamental` clean trusted-three = the FULL moat.

Fallback: SEAM (one documented up-producer sorry, ADR-0026) stays available if the research walls —
`c26c4c9` (spine + 6/7, green) banked. Gate the AXIOM SET each commit; flag-before-build the metering.
This is a kernel-engineer + proof-engineer-grade effort (config-level relation architecture + metering).
