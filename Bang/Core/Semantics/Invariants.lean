/-
  Bang/Operational/Invariants.lean — the WellCounted freshness invariant (ADR-0055).
  ─────────────────────────────────────────────────────────────────────────
    StackBelow · WellCounted · the global-fresh-counter freshness theory
    splitAtId_fresh · stackBelow_splitAtId · stackBelow_idDispatch
    wellCounted_step · wellCounted_reachable · wellCounted_initial

  The freshness-invariant concern of the operational hub (the cluster with no
  external consumers beyond the LR diagonal). Imports Eval (the invariant is
  preserved by Source.step). Split out of Bang/Operational.lean per
  core-overview.md §6; behavior-preserving MOVE.
-/

module

public import Bang.Core.Semantics.Eval

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]

@[expose] public section

/-! ### `WellCounted` — the global-fresh freshness invariant (ADR-0055)

A SEPARATE reachability invariant (sibling to `NonEscape`, NOT folded into `HasConfig` — it is a
property of reachability-from-a-fresh-start, not of typing; the STD block is counter-insensitive and
needs no extra conjunct). `WellCounted (g, K, _)` = every live handler identity on `K` is `< g`, so the
minted `g` is FRESH (`splitAtId K g = none`): an escaped capability resolves to ITS handler or to
NOTHING (stuck, fail-loud), never to a same-depth impostor. This is what makes `NonEscape` ADEQUATE
under global-fresh minting; the inc-5 LR diagonal consumes it via `wellCounted_reachable`.
shape: scratch/GlobalFreshProbe.lean §3 (build-validated). -/

/-- Every `handleF` identity on the stack is `< g` (the cap-transparent `letF`/`appF` frames impose
nothing). -/
def StackBelow (g : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => n < g ∧ StackBelow g K
  | .letF _ :: K => StackBelow g K
  | .appF _ :: K => StackBelow g K

/-- The config-level invariant: the carried counter dominates every live handler identity. -/
def WellCounted : Config → Prop
  | (g, K, _) => StackBelow g K

/-- `StackBelow` is monotone in the counter — a larger counter still dominates. Lets the incremented
`g+1` bound the OLD frames after a mint. -/
private theorem StackBelow_mono {g g' : Nat} (hle : g ≤ g') :
    ∀ K, StackBelow g K → StackBelow g' K := by
  intro K hK
  induction K with
  | nil => trivial
  | cons fr K ih =>
    cases fr with
    | handleF n hd => obtain ⟨hlt, hrest⟩ := hK; exact ⟨by omega, ih hrest⟩
    | letF N => exact ih hK
    | appF v => exact ih hK

/-- **Freshness**: if every id on `K` is `< g`, then `splitAtId K g = none` — the fresh id `g` matches
NO live frame. This kills the ADR-0054 collision: minting `g` then later resolving a cap named `g`
finds ITS handler or nothing, never a same-depth impostor. shape: scratch/GlobalFreshProbe.lean. -/
private theorem splitAtId_fresh (g : Nat) (K : EvalCtx) (h : StackBelow g K) :
    splitAtId K g = none := by
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF n hd =>
      obtain ⟨hlt, hrest⟩ := h
      simp only [splitAtId]
      rw [if_neg (by omega : ¬ n = g), ih hrest]; rfl
    | letF N => simp only [splitAtId]; rw [ih h]; rfl
    | appF v => simp only [splitAtId]; rw [ih h]; rfl

/-- `StackBelow` distributes over `++` (every frame independently dominated). The reconstruction
direction (`mpr`) is what rebuilds the resumed stack `Kᵢ ++ handleF n h' :: Kₒ` after a resume. -/
private theorem StackBelow_append (g : Nat) : ∀ (K1 K2 : EvalCtx),
    StackBelow g (K1 ++ K2) ↔ (StackBelow g K1 ∧ StackBelow g K2) := by
  intro K1 K2
  induction K1 with
  | nil => simp only [List.nil_append, StackBelow, true_and]
  | cons fr K1 ih =>
    cases fr with
    | handleF n hd => simp only [List.cons_append, StackBelow, ih]; tauto
    | letF N => simp only [List.cons_append, StackBelow]; exact ih
    | appF w => simp only [List.cons_append, StackBelow]; exact ih

/-- `splitAtId` returns sub-stacks of `K`, so `StackBelow g K` passes to BOTH the captured prefix `Kᵢ`
and the outer `Kₒ`, and the matched frame's identity `n` is `< g`. The freshness companion to
`splitAtId_fresh`: it bounds what a SUCCESSFUL split yields. -/
theorem stackBelow_splitAtId {g n : Nat} : ∀ {K Kᵢ Kₒ : EvalCtx} {h : Handler},
    StackBelow g K → splitAtId K n = some (Kᵢ, h, Kₒ) →
    StackBelow g Kᵢ ∧ n < g ∧ StackBelow g Kₒ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hsb hsp; simp [splitAtId] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ hh hsb hsp
    cases fr with
    | handleF m hd =>
      simp only [splitAtId] at hsp
      by_cases hmn : m = n
      · rw [if_pos hmn] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨rfl, _, rfl⟩ := hsp; subst hmn
        obtain ⟨hlt, hrest⟩ := hsb
        exact ⟨trivial, hlt, hrest⟩
      · rw [if_neg hmn, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨hlt, hrest⟩ := hsb
        obtain ⟨hsbi, hng, hsbo⟩ := ih hrest hsp'
        exact ⟨⟨hlt, hsbi⟩, hng, hsbo⟩
    | letF N =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨hsbi, hng, hsbo⟩ := ih hsb hsp'
      exact ⟨hsbi, hng, hsbo⟩
    | appF w =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨hsbi, hng, hsbo⟩ := ih hsb hsp'
      exact ⟨hsbi, hng, hsbo⟩

/-- **DISPATCH-arm `WellCounted` preservation (ADR-0055).** `idDispatch` reinstalls `handleF n` (the
matched id `n < g`, by `stackBelow_splitAtId`) on a state/transaction RESUME; the resumed stack
`Kᵢ ++ handleF n h' :: Kₒ` re-assembles sub-stacks of `K` with the SAME id `n`, so every id stays `< g`
(`StackBelow_append`). The `throws` abort yields `Kₒ` directly. This is the freshness obligation the
ADR predicted — what makes a resume never break `WellCounted`. -/
theorem stackBelow_idDispatch {g : Nat} {K K' : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId}
    {v : Val} {c' : Comp} (hwc : StackBelow g K)
    (hd : idDispatch K n ℓ op v = some (K', c')) : StackBelow g K' := by
  unfold idDispatch at hd
  obtain ⟨⟨Kᵢ, h, Kₒ⟩, hsplit, hd2⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨hsbi, hng, hsbo⟩ := stackBelow_splitAtId hwc hsplit
  dsimp only at hd2  -- iota-reduce the destructuring-lambda `match (Kᵢ,h,Kₒ) with …` to the bare `if`
  by_cases hk : handlesOp h ℓ op = true
  · rw [if_pos hk] at hd2
    cases h with
    | throws ℓ' =>
      simp only [dispatchOn, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, _⟩ := hd2; exact hsbo
    | state ℓ' s =>
      simp only [dispatchOn] at hd2
      split at hd2 <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, _⟩ := hd2
          exact (StackBelow_append g Kᵢ _).mpr ⟨hsbi, hng, hsbo⟩
    | transaction ℓ' Θ =>
      simp only [dispatchOn] at hd2
      (repeat' split at hd2) <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, _⟩ := hd2
          exact (StackBelow_append g Kᵢ _).mpr ⟨hsbi, hng, hsbo⟩
    | custom ℓ' p cl =>
      -- custom (ADR-0085 stage 2, ADR-0087 finite rep): ONE-SHOT resume — dispatchOn reinstalls the deep
      -- frame over the SAME `Kᵢ`/`Kₒ` (`Kᵢ ++ handleF n (custom …) :: Kₒ`), the ADR-0025 state stack shape.
      -- StackBelow is preserved EXACTLY as for `state`: the reassembled stack's every id is `< g`. Real
      -- (non-vacuous), additive, mirrors the state arm.
      simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨_, hsome⟩ := hk
      obtain ⟨clause, hcl⟩ := Option.isSome_iff_exists.mp hsome
      simp only [dispatchOn, hcl, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, _⟩ := hd2
      exact (StackBelow_append g Kᵢ _).mpr ⟨hsbi, hng, hsbo⟩
  · rw [if_neg hk] at hd2; exact absurd hd2 (by simp)

/-- **`WellCounted` is preserved by `cstep`.** The mint arm pushes `handleF g` with counter `g+1` (old
frames stay `< g < g+1` by mono; the new frame is `g < g+1`); every other arm keeps/shrinks the stack
with an unchanged counter, or (dispatch) reinstalls an existing id (`stackBelow_idDispatch`). -/
private theorem wellCounted_step {cfg cfg' : Config}
    (hwc : WellCounted cfg) (hstep : Source.step cfg = some cfg') : WellCounted cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  have hwc' : StackBelow g K := hwc
  cases c with
  | letC M N =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc'
  | app M v =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc'
  | handle h M =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    exact ⟨Nat.lt_succ_self g, StackBelow_mono (Nat.le_succ g) K hwc'⟩
  | force w =>
    cases w <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc')
        | (simp [Source.step] at hstep)
  | ret v =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc'
      | appF w => simp [Source.step] at hstep
      | handleF n h =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc'.2
  | lam M =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | appF w =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc'
      | letF N => simp [Source.step] at hstep
      | handleF n h => simp [Source.step] at hstep
  | perform cap op v =>
    cases cap with
    | vcap n ℓ =>
      simp only [Source.step, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨K', c'⟩, hd, hcfg⟩ := hstep
      subst hcfg
      exact stackBelow_idDispatch hwc' hd
    | _ => simp [Source.step] at hstep
  | case v N₁ N₂ =>
    cases v <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc')
        | (simp [Source.step] at hstep)
  | split v N =>
    cases v <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc')
        | (simp [Source.step] at hstep)
  | unfold v =>
    cases v <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc')
        | (simp [Source.step] at hstep)
  | binop op v₁ v₂ =>
    -- δ-rule: steps to `(g, K, ret …)` only when both operands are `vint` (same stack/counter);
    -- every other operand shape is stuck, contradicting `hstep`.
    cases v₁ <;> cases v₂ <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hwc')
        | (simp [Source.step] at hstep)
  | oom => simp [Source.step] at hstep
  | wrong s => simp [Source.step] at hstep

/-- `WellCounted` propagates along reachability (`StepStar`) — the forward closure, by induction on
the path through the single-step `wellCounted_step`. This is what hands the inc-5 LR diagonal a fresh
`WellCounted` at any reachable config (it does NOT need to ride in `HasConfig`). -/
theorem wellCounted_reachable {cfg cfg' : Config}
    (hwc : WellCounted cfg) (hreach : StepStar cfg cfg') : WellCounted cfg' := by
  induction hreach with
  | refl => exact hwc
  | tail _ hstep ih => exact wellCounted_step ih hstep

/-- The initial config `(0, [], c)` is `WellCounted` trivially (empty stack). The fresh-start seed. -/
private theorem wellCounted_initial (c : Comp) : WellCounted (0, [], c) := trivial

/-! ### `StackInc` — the id-ORDERING invariant (ADR-0096, the LR freshness carrier)

`WellCounted`/`StackBelow g` bounds ids from ABOVE (all `< g`); it cannot exclude a *live* id
`nid < g` from a captured continuation. The LR SKIP-arm strip (`krelS_splitAtId_decomp`) needs exactly
that — `splitAtId Kᵢ nid = none` for a live deep-catcher id — so it needs the DUAL, lower-bound fact.
`StackInc` records that ids strictly INCREASE up the stack (the mint pushes `handleF g` on top as the
largest id, `Eval.lean:89`), so every frame ABOVE a `handleF nid` has id `> nid`. This is the true
property of the real counter that ADR-0058 route-1 left implicit on the LR side; it co-travels with
`WellCounted` and is discharged from reachability at the machine-reached `crelK_fund_up` consumer.
(ADR-0096 amendment: `StackBelow g` was machine-refuted for this — `scratch/StackBelowInsufficientProbe`.) -/

/-- Every `handleF` identity on `K` is strictly `> nid` (the dual of `StackBelow`; cap-transparent
`letF`/`appF` frames impose nothing). This is what a captured continuation ABOVE a `handleF nid`
frame satisfies — it excludes `nid` from the split (`splitAtId_above`). -/
def StackAbove (nid : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => nid < n ∧ StackAbove nid K
  | .letF _ :: K => StackAbove nid K
  | .appF _ :: K => StackAbove nid K

/-- Ids strictly increase up the stack: the head (top) `handleF` id exceeds every id in the tail
(`StackBelow n K`), and the tail is itself increasing. The head clause REUSES `StackBelow`, so
`StackInc` is `StackBelow`-derived, not a new predicate family. -/
def StackInc : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => StackInc K ∧ StackBelow n K
  | .letF _ :: K => StackInc K
  | .appF _ :: K => StackInc K

/-- `StackAbove` is antitone in the threshold — a smaller `nid` is still exceeded. Lifts
`StackAbove mh₁` to `StackAbove nid` when `nid < mh₁` (the SKIP-arm's captured-above region). -/
theorem StackAbove_anti {nid nid' : Nat} (hle : nid ≤ nid') :
    ∀ K, StackAbove nid' K → StackAbove nid K := by
  intro K h
  induction K with
  | nil => trivial
  | cons fr K ih =>
    cases fr with
    | handleF n hd => obtain ⟨hlt, hr⟩ := h; exact ⟨by omega, ih hr⟩
    | letF N => exact ih h
    | appF w => exact ih h

/-- `StackAbove` distributes over `++` (every frame independently exceeds `nid`). -/
theorem StackAbove_append (nid : Nat) : ∀ (K1 K2 : EvalCtx),
    StackAbove nid (K1 ++ K2) ↔ (StackAbove nid K1 ∧ StackAbove nid K2) := by
  intro K1 K2
  induction K1 with
  | nil => simp only [List.nil_append, StackAbove, true_and]
  | cons fr K1 ih =>
    cases fr with
    | handleF n hd => simp only [List.cons_append, StackAbove, ih]; tauto
    | letF N => simp only [List.cons_append, StackAbove]; exact ih
    | appF w => simp only [List.cons_append, StackAbove]; exact ih

/-- **Above-freshness**: `StackAbove nid K → splitAtId K nid = none`. The dual of `splitAtId_fresh`:
where `splitAtId_fresh` excludes the FRESH counter `g` (upper bound), this excludes a LIVE id `nid`
that every frame strictly exceeds (lower bound). This is the fact the LR strip actually consumes. -/
theorem splitAtId_above (nid : Nat) (K : EvalCtx) (h : StackAbove nid K) :
    splitAtId K nid = none := by
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF n hd =>
      obtain ⟨hlt, hrest⟩ := h
      simp only [splitAtId]; rw [if_neg (by omega : ¬ n = nid), ih hrest]; rfl
    | letF N => simp only [splitAtId]; rw [ih h]; rfl
    | appF v => simp only [splitAtId]; rw [ih h]; rfl

/-- `StackInc` on a stack that DECOMPOSES at `nid` as `Kᵢ ++ handleF nid _ :: Kₒ` gives `StackAbove nid`
on the captured-above region `Kᵢ` — the frames above the catcher all have larger ids. This is the LR
strip's delivery: from the machine-reached `StackInc`, the strip's `StackAbove nid` premise. -/
theorem stackInc_gives_above {nid : Nat} {Kᵢ Kₒ : EvalCtx} {hh : Handler}
    (h : StackInc (Kᵢ ++ Frame.handleF nid hh :: Kₒ)) : StackAbove nid Kᵢ := by
  induction Kᵢ with
  | nil => trivial
  | cons fr Kᵢ' ih =>
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StackInc] at h
      obtain ⟨hincrest, hbelow⟩ := h
      have hnm : nid < m := ((StackBelow_append m Kᵢ' (Frame.handleF nid hh :: Kₒ)).mp hbelow).2.1
      exact ⟨hnm, ih hincrest⟩
    | letF N => simp only [List.cons_append, StackInc] at h; exact ih h
    | appF w => simp only [List.cons_append, StackInc] at h; exact ih h

/-- `splitAtId` locates a `handleF n` frame, so `K = Kᵢ ++ handleF n h :: Kₒ`. (Re-proven locally from
`splitAtId`: the `Soundness.lean` copy imports THIS module, so it cannot be imported back.) -/
private theorem splitAtId_decomp_inv : ∀ (K : EvalCtx) (n : Nat) {Kᵢ Kₒ : EvalCtx} {h : Handler},
    splitAtId K n = some (Kᵢ, h, Kₒ) → K = Kᵢ ++ Frame.handleF n h :: Kₒ := by
  intro K n
  induction K with
  | nil => intro Kᵢ Kₒ h hsp; simp [splitAtId] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ h hsp
    cases fr with
    | handleF m h₀ =>
      simp only [splitAtId] at hsp
      by_cases hmn : m = n
      · rw [if_pos hmn] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨hKi, hh, hKo⟩ := hsp
        subst hKi; subst hh; subst hKo; subst hmn; rfl
      · rw [if_neg hmn, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hKi, hh, hKo⟩ := heq
        subst hKi; subst hh; subst hKo
        rw [ih hsp']; rfl
    | letF N =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hKi, hh, hKo⟩ := heq
      subst hKi; subst hh; subst hKo
      rw [ih hsp']; rfl
    | appF w =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hKi, hh, hKo⟩ := heq
      subst hKi; subst hh; subst hKo
      rw [ih hsp']; rfl

/-- `StackInc` splits: a successful `splitAtId` yields `StackInc` on both sub-stacks AND on the
reassembled `Kᵢ ++ handleF n h :: Kₒ` (= the original `K`, `splitAtId_decomp`). Feeds the resume arm. -/
theorem stackInc_split {n : Nat} {K Kᵢ Kₒ : EvalCtx} {h : Handler}
    (hinc : StackInc K) (hsp : splitAtId K n = some (Kᵢ, h, Kₒ)) :
    StackInc Kᵢ ∧ StackInc Kₒ ∧ StackInc (Kᵢ ++ Frame.handleF n h :: Kₒ) := by
  have hdec : K = Kᵢ ++ Frame.handleF n h :: Kₒ := splitAtId_decomp_inv K n hsp
  subst hdec
  refine ⟨?_, ?_, hinc⟩
  · clear hsp
    induction Kᵢ with
    | nil => trivial
    | cons fr Kᵢ' ih =>
      cases fr with
      | handleF m hd => simp only [List.cons_append, StackInc] at hinc ⊢
                        exact ⟨ih hinc.1, (StackBelow_append m Kᵢ' _).mp hinc.2 |>.1⟩
      | letF N => simp only [List.cons_append, StackInc] at hinc ⊢; exact ih hinc
      | appF w => simp only [List.cons_append, StackInc] at hinc ⊢; exact ih hinc
  · clear hsp
    induction Kᵢ with
    | nil => simp only [List.nil_append, StackInc] at hinc; exact hinc.1
    | cons fr Kᵢ' ih =>
      cases fr with
      | handleF m hd => simp only [List.cons_append, StackInc] at hinc; exact ih hinc.1
      | letF N => simp only [List.cons_append, StackInc] at hinc; exact ih hinc
      | appF w => simp only [List.cons_append, StackInc] at hinc; exact ih hinc

/-- A resume reinstalls `handleF n` with the SAME id (payload changed) — `StackInc` is id-only,
payload-blind, so it survives verbatim. The resume-arm companion to `stackBelow`'s append. -/
theorem stackInc_reinstall {n : Nat} {Kᵢ Kₒ : EvalCtx} {h reinstall : Handler}
    (h0 : StackInc (Kᵢ ++ Frame.handleF n h :: Kₒ)) :
    StackInc (Kᵢ ++ Frame.handleF n reinstall :: Kₒ) := by
  induction Kᵢ with
  | nil => simp only [List.nil_append, StackInc] at h0 ⊢; exact h0
  | cons fr Kᵢ' ih =>
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StackInc] at h0 ⊢
      refine ⟨ih h0.1, ?_⟩
      rw [StackBelow_append] at h0 ⊢; simp only [StackBelow] at h0 ⊢; exact h0.2
    | letF N => simp only [List.cons_append, StackInc] at h0 ⊢; exact ih h0
    | appF w => simp only [List.cons_append, StackInc] at h0 ⊢; exact ih h0

/-- **`StackInc` DISPATCH-arm preservation.** `idDispatch` resume/abort preserves `StackInc`: the
reinstalled `Kᵢ ++ handleF n _ :: Kₒ` is `stackInc_reinstall` of the split `K`; the `throws` abort
yields `Kₒ` (a `StackInc` sub-stack). Mirrors `stackBelow_idDispatch`. -/
theorem stackInc_idDispatch {K K' : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId}
    {v : Val} {c' : Comp} (hinc : StackInc K)
    (hd : idDispatch K n ℓ op v = some (K', c')) : StackInc K' := by
  unfold idDispatch at hd
  obtain ⟨⟨Kᵢ, h, Kₒ⟩, hsplit, hd2⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨_, hinco, hincfull⟩ := stackInc_split hinc hsplit
  dsimp only at hd2
  by_cases hk : handlesOp h ℓ op = true
  · rw [if_pos hk] at hd2
    cases h with
    | throws ℓ' =>
      simp only [dispatchOn, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, _⟩ := hd2; exact hinco
    | state ℓ' s =>
      simp only [dispatchOn] at hd2
      split at hd2 <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, _⟩ := hd2; exact stackInc_reinstall hincfull
    | transaction ℓ' Θ =>
      simp only [dispatchOn] at hd2
      (repeat' split at hd2) <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, _⟩ := hd2; exact stackInc_reinstall hincfull
    | custom ℓ' p cl =>
      simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨_, hsome⟩ := hk
      obtain ⟨clause, hcl⟩ := Option.isSome_iff_exists.mp hsome
      simp only [dispatchOn, hcl, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, _⟩ := hd2; exact stackInc_reinstall hincfull
  · rw [if_neg hk] at hd2; exact absurd hd2 (by simp)

/-- **`StackInc ∧ WellCounted` jointly preserved by `Source.step`.** They co-travel: the MINT arm needs
`StackBelow g K` (from `WellCounted`) to place `handleF g` as the new top (largest) id; the DISPATCH arm
routes through `stackInc_idDispatch`; every other arm keeps/shrinks the stack. -/
theorem stackIncWC_step {cfg cfg' : Config}
    (hinc : StackInc cfg.2.1) (hwc : WellCounted cfg)
    (hstep : Source.step cfg = some cfg') :
    StackInc cfg'.2.1 ∧ WellCounted cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  have hwc' : StackBelow g K := hwc
  have hwcstep : WellCounted cfg' := wellCounted_reachable hwc (StepStar.tail StepStar.refl hstep)
  refine ⟨?_, hwcstep⟩
  cases c with
  | letC M N => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
  | app M v => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
  | handle h M =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact ⟨hinc, hwc'⟩
  | force w =>
    cases w <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
        | (simp [Source.step] at hstep)
  | ret v =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
      | appF w => simp [Source.step] at hstep
      | handleF n h => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc.1
  | lam M =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | appF w => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
      | letF N => simp [Source.step] at hstep
      | handleF n h => simp [Source.step] at hstep
  | perform cap op v =>
    cases cap with
    | vcap n ℓ =>
      simp only [Source.step, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨K', c'⟩, hd, hcfg⟩ := hstep; subst hcfg
      exact stackInc_idDispatch hinc hd
    | _ => simp [Source.step] at hstep
  | case v N₁ N₂ =>
    cases v <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
        | (simp [Source.step] at hstep)
  | split v N =>
    cases v <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
        | (simp [Source.step] at hstep)
  | unfold v =>
    cases v <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
        | (simp [Source.step] at hstep)
  | binop op v₁ v₂ =>
    cases v₁ <;> cases v₂ <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
        | (simp [Source.step] at hstep)
  | oom => simp [Source.step] at hstep
  | wrong s => simp [Source.step] at hstep

/-- `StackInc` propagates along reachability (co-traveling with `WellCounted`). The LR-diagonal
discharge: at any machine-reached config, `StackInc` holds — so the resume conjunct's captured
continuation inherits it, killing the "`nid` might be in `Kᵢ`" case by construction (ADR-0096). -/
theorem stackInc_reachable {cfg cfg' : Config}
    (hinc : StackInc cfg.2.1) (hwc : WellCounted cfg) (hreach : StepStar cfg cfg') :
    StackInc cfg'.2.1 := by
  induction hreach with
  | refl => exact hinc
  | tail hpath hstep ih => exact (stackIncWC_step ih (wellCounted_reachable hwc hpath) hstep).1

/-- The initial config `(0, [], c)` is `StackInc` trivially (empty stack). -/
private theorem stackInc_initial (_c : Comp) : StackInc [] := trivial


end -- public section

end Bang
