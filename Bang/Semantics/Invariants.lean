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

public import Bang.Semantics.Eval

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


end -- public section

end Bang
