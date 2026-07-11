module

public import Bang.Core.Soundness
-- (was Model's transitive Mathlib dep; now explicit across the module boundary.)
public import Mathlib.Data.Option.NAry

/-!
  Bang/Freshness.lean — the LIVE caps / generative-freshness layer (extracted from
  Bang/Model.lean, task #82 Phase 1b).
  ───────────────────────────────────────────────────────────────────────────────
  The capability-collection (`capsV`/`capsC`/`capsH`/`capsK`, `ResolvesLabel`) and the
  generative-freshness invariant (`CapsBelow`, `StratFresh`, `FreshCfg`) + its `Source.step`
  preservation `freshCfg_step`. This is the half of the old `Bang/Model.lean` that is LIVE:
  consumed by `Bang/CapCoh.lean`'s label-coherence forward-invariant (`capLabelCoh_step`),
  hence transitively by the gated `Bang.CalcVM` bridge. It rides ONLY gensym freshness
  (ADR-0055) + `splitAtId` structural lemmas — NO grades — so it is engine-FREE and carries
  no `sorryAx`.

  SPLIT RATIONALE (task #82): the rest of `Bang/Model.lean` (the typeless/graded `LWS*`
  liveness engine + the route-β `NonEscape` diagonal) is OFF the v1 soundness path — ADR-0063
  routed v1 soundness through pure typing-preservation (`type_safety'`), not the diagonal — and
  is reached by no gated headline. Extracting this layer SEVERS the `Audit→CalcVM→CapCoh→Model`
  edge: `CapCoh` now imports `Bang.Freshness`, and `Bang.Model` leaves the gated closure.

  Namespace `Bang.Model` is PRESERVED so downstream `open Bang.Model` keeps resolving these
  names; the symbols simply have a new home.
-/

namespace Bang.Model
open Bang
open Bang.EffectRow (Label)

-- Module reveal (Phase 1a): CapCoh unfolds the caps/freshness bodies, so they cross the
-- public boundary.
@[expose] public section

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
  [NoZeroDivisors Mult] [Nontrivial Mult]

/-! ## §1 — capability collection (`capsV`/`capsC`/`capsH`/`capsK`) + `ResolvesLabel`. -/

mutual
/-- collect every `(identity, label)` of a `vcap` node in a value. -/
def capsV : Val → List (Nat × Label)
  | .vcap n ℓ   => [(n, ℓ)]
  | .vthunk c   => capsC c
  | .inl v      => capsV v
  | .inr v      => capsV v
  | .pair a b   => capsV a ++ capsV b
  | .fold v     => capsV v
  | _           => []
  termination_by v => sizeOf v
/-- Collect every `(identity, label)` of a `vcap` node in a computation. -/
def capsC : Comp → List (Nat × Label)
  | .ret v        => capsV v
  | .letC M N     => capsC M ++ capsC N
  | .force v      => capsV v
  | .lam M        => capsC M
  | .app M v      => capsC M ++ capsV v
  | .perform c _ v => capsV c ++ capsV v
  | .handle h M   => capsH h ++ capsC M
  | .case v N₁ N₂ => capsV v ++ capsC N₁ ++ capsC N₂
  | .split v N    => capsV v ++ capsC N
  | .unfold v     => capsV v
  | .binop _ v w  => capsV v ++ capsV w   -- δ-rule: caps of both operands (like perform)
  -- ENUMERATE the no-cap leaves (no `| _ => []`): a future sub-term-bearing constructor must break
  -- LOUDLY here, not silently drop its operands' caps (the latent default binop would have inherited).
  | .oom          => []
  | .wrong _      => []
  termination_by c => sizeOf c
/-- Collect every `(identity, label)` of a `vcap` node in a handler. -/
def capsH : Handler → List (Nat × Label)
  | .state _ s  => capsV s
  | .throws _   => []
  | .transaction _ Θ => Θ.flatMap capsV
  -- custom (ADR-0087 finite rep): the caps are STRUCTURAL — the carried param's caps ++ every clause
  -- body's caps. Honest and total, the sibling of `state`'s `capsV s` and `transaction`'s `Θ.flatMap capsV`.
  -- This is the D2 bet: with clauses enumerable, `CapLabelCoh`/`FreshCfg` bound custom's caps by the SAME
  -- per-step machinery as the built-ins — no threaded well-formedness premise (the ADR-0085 wall dissolved).
  -- The clause bodies are traversed via `capsCls` (a separate mutual member recursing on the list spine)
  -- because `List (OpId × Comp)` is a nested-inductive occurrence of `Comp` the structural checker cannot
  -- thread automatically; the `sizeOf` measure justifies the descent. Equation lemmas
  -- (`simp only [capsH]`/`[capsCls]`) are still generated.
  | .custom _ p cls => capsV p ++ capsCls cls
  termination_by h => sizeOf h
/-- Caps of a custom handler's clause list — recurses on the list spine; each body `c.2` is a
`sizeOf`-subterm of the clause list (ADR-0087). -/
def capsCls : List (OpId × Comp) → List (Nat × Label)
  | [] => []
  | c :: rest => capsC c.2 ++ capsCls rest
  termination_by cls => sizeOf cls
  decreasing_by
    · simp_wf; cases c with | mk op body => simp only [Prod.mk.sizeOf_spec]; omega
    · simp_wf; omega
end

/-- Every cap of a clause `c ∈ cls` is a cap of the whole clause list (ADR-0087: the enumerability that
dissolves the clause-cap blocker — the gh44s2 `sorry` on `q ∈ capsC clause` closes through this). -/
theorem capsCls_mem {cls : List (OpId × Comp)} {c : OpId × Comp} (hc : c ∈ cls) :
    ∀ q ∈ capsC c.2, q ∈ capsCls cls := by
  induction cls with
  | nil => simp at hc
  | cons hd rest ih =>
    intro q hq
    rcases List.mem_cons.mp hc with h' | h'
    · subst h'; exact (by simp only [capsCls]; exact List.mem_append_left _ hq)
    · exact (by simp only [capsCls]; exact List.mem_append_right _ (ih h' q hq))

/-- A `find?`-matched clause's caps land in `capsCls` (the honest custom `capsH` bounds them). -/
theorem capsCls_find? {cls : List (OpId × Comp)} {op : OpId} {c : OpId × Comp}
    (hf : cls.find? (·.1 == op) = some c) : ∀ q ∈ capsC c.2, q ∈ capsCls cls :=
  capsCls_mem (List.mem_of_find?_eq_some hf)

/-- Collect every `(identity, label)` of a `vcap` node in an evaluation context. -/
def capsK : EvalCtx → List (Nat × Label)
  | []                  => []
  | .letF N :: K        => capsC N ++ capsK K
  | .appF v :: K        => capsV v ++ capsK K
  | .handleF _ h :: K   => capsH h ++ capsK K

/-- the cap `(n,ℓ)` lands on a same-LABEL handler frame on `K` (the op-in-interface check is the
secondary typing dependency, `handlesOp_of_hasConfigTy`). -/
def ResolvesLabel (K : EvalCtx) (n : Nat) (ℓ : Label) : Prop :=
  ∃ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) ∧ Handler.label h = ℓ

/-- A source program is `VcapFree` when it contains NO raw `vcap` literal — the elaborator invariant
(`vcap`s arise only by minting). The diagonal's side-condition (the bare form is FALSE: a hand-written
`vcap 5` types but runs stuck — DiagonalProbe §B). -/
def VcapFree (c : Comp) : Prop := capsC c = []

/-! ## §2 — the STRATIFIED capability-freshness invariant (`CapsBelow`/`FreshCfg`) + its
    `Source.step` preservation `freshCfg_step`. (Was Model §3.0/§3.0a/§3.0b.) -/

/-! ### §3.0 — the STRATIFIED capability-freshness predicates (ADR-0061, the regrade's freshness half).

The typeless `LWSC`/`LWSK` discard the cap-id freshness the POP arm needs: popping `handleF g'` must
leave the TAIL's stored caps un-broken (i.e. `≠ g'`). `StackBelow` (Operational) bounds only the
`handleF` FRAME ids `< g`; it never bounds the caps STORED inside `letF`/`appF` frames or the focus.
`CapsBelow` extends the bound to ids AND stored caps; `StratFresh` records the per-frame stratification —
everything strictly below a `handleF n` frame predates the mint of `n`, hence is `< n` (TRUE by
global-fresh monotone minting, ADR-0055, previously untracked). The POP arm reads
`StratFresh (handleF g' hd :: K') ⟹ CapsBelow g' K' ⟹ tail caps < g' ⟹ ≠ g'`. -/

/-- Every `handleF` identity AND every STORED capability id on the stack is `< g`. Strengthens
`StackBelow` (ids-only, `Operational`) with the `letF`/`appF` stored-cap bound. -/
def CapsBelow (g : Nat) : EvalCtx → Prop
  | [] => True
  | Frame.handleF n _ :: K => n < g ∧ CapsBelow g K
  | Frame.letF N :: K => (∀ p ∈ capsC N, p.1 < g) ∧ CapsBelow g K
  | Frame.appF v :: K => (∀ p ∈ capsV v, p.1 < g) ∧ CapsBelow g K

/-- `CapsBelow` is monotone in the counter (the MINT arm re-bounds the old frames by `g < g+1`). -/
theorem CapsBelow_mono {g g' : Nat} (hle : g ≤ g') : ∀ K, CapsBelow g K → CapsBelow g' K := by
  intro K hK
  induction K with
  | nil => trivial
  | cons fr K ih =>
    cases fr with
    | handleF n hd => obtain ⟨hlt, hrest⟩ := hK; exact ⟨by omega, ih hrest⟩
    | letF N => obtain ⟨hcaps, hrest⟩ := hK; exact ⟨fun p hp => by have := hcaps p hp; omega, ih hrest⟩
    | appF v => obtain ⟨hcaps, hrest⟩ := hK; exact ⟨fun p hp => by have := hcaps p hp; omega, ih hrest⟩

/-- The stack is fresh-STRATIFIED: everything strictly below each `handleF n` frame is `< n` (it predates
the mint of `n`). The POP arm inverts the head conjunct to bound the popped frame's tail by `g'`. -/
def StratFresh : EvalCtx → Prop
  | [] => True
  | Frame.handleF n _ :: K => CapsBelow n K ∧ StratFresh K
  | Frame.letF _ :: K => StratFresh K
  | Frame.appF _ :: K => StratFresh K

/-- The config-level freshness bundle (self-contained for step-preservation): the stack is `CapsBelow`
the counter and `StratFresh`, the FOCUS's caps are `< g` (the focus-cap bound, needed so MINT — which
injects `vcap g` into the focus and advances the counter to `g+1` — re-establishes `< g+1`), AND every
STORED stack cap is `< g` (`∀ p ∈ capsK K`, descending into `handleF`-stored state/txn values — the
FLAT global bound `CapsBelow` omits). The last conjunct is what the DISPATCH state-`get`/`readTVar`
resume needs: it lifts a handler-stored value into the focus (`ret s`), so its caps must already be
`< g`. It is FLAT (not stratified like `StratFresh`), so a `put` storing a younger cap into an older
state cell keeps it (`caps(w) < g` at put-time) WITHOUT the unsound `StratFresh` coupling that bounding
`capsH` inside `CapsBelow` would impose. Strengthens (subsumes) the old `WellCounted` (`StackBelow`,
ids-only).

The last conjunct is the **freshness-completeness conjunct** (ADR-0061 refinement, lead-approved): it
asserts caps `< g` against the GLOBAL counter (true for everything minted-so-far), NOT `< n` per-handler,
which is exactly what dodges the `StratFresh` coupling that makes the stratified `capsH`-in-`CapsBelow`
form FALSE (a `put` legitimately stores a younger cap into an older state cell). `StratFresh`'s definition
is UNTOUCHED — this is an ADDED conjunct. Preservation: `put w` ⇒ `caps w < g` by the focus-cap bound
(counter unchanged); MINT pushes `handleF g` + `s₀` both `< g < g+1`; the seed `wellScoped_initial` is
vacuous (`capsK [] = ∅`). TODO(ADR-0061): record the gained conjunct in the invariant's ADR. -/
def FreshCfg : Config → Prop
  | (g, K, c) => CapsBelow g K ∧ (∀ p ∈ capsC c, p.1 < g) ∧ StratFresh K
      ∧ (∀ p ∈ capsK K, p.1 < g)  -- freshness-completeness: every STORED cap `< g` (ADR-0061)

/-! ### §3.0a — caps are SHIFT-invariant and SUBST-bounded (the focus-cap-bound mechanics for §3.0). -/

mutual
/-- `shiftFrom` moves only `vvar` indices (cap-free), so it preserves the cap multiset. -/
theorem capsV_shiftFrom (j : Nat) (u : Val) : capsV (Val.shiftFrom j u) = capsV u := by
  match u with
  | .vunit | .vint _ | .vcap _ _ => rfl
  | .vvar i => by_cases h : i < j <;> simp [Val.shiftFrom, capsV, h]
  | .vthunk c => simp only [Val.shiftFrom, capsV]; exact capsC_shiftFrom j c
  | .inl w => simp only [Val.shiftFrom, capsV]; exact capsV_shiftFrom j w
  | .inr w => simp only [Val.shiftFrom, capsV]; exact capsV_shiftFrom j w
  | .pair a b => simp only [Val.shiftFrom, capsV]; rw [capsV_shiftFrom j a, capsV_shiftFrom j b]
  | .fold w => simp only [Val.shiftFrom, capsV]; exact capsV_shiftFrom j w
theorem capsC_shiftFrom (j : Nat) (c : Comp) : capsC (Comp.shiftFrom j c) = capsC c := by
  match c with
  | .ret v => simp only [Comp.shiftFrom, capsC]; exact capsV_shiftFrom j v
  | .letC M N => simp only [Comp.shiftFrom, capsC]; rw [capsC_shiftFrom j M, capsC_shiftFrom (j+1) N]
  | .force v => simp only [Comp.shiftFrom, capsC]; exact capsV_shiftFrom j v
  | .lam M => simp only [Comp.shiftFrom, capsC]; exact capsC_shiftFrom (j+1) M
  | .app M w => simp only [Comp.shiftFrom, capsC]; rw [capsC_shiftFrom j M, capsV_shiftFrom j w]
  | .perform cp _ w =>
      simp only [Comp.shiftFrom, capsC]; rw [capsV_shiftFrom j cp, capsV_shiftFrom j w]
  | .handle h M =>
      simp only [Comp.shiftFrom, capsC]; rw [capsH_shiftFrom j h, capsC_shiftFrom (j+1) M]
  | .case w N₁ N₂ =>
      simp only [Comp.shiftFrom, capsC]
      rw [capsV_shiftFrom j w, capsC_shiftFrom (j+1) N₁, capsC_shiftFrom (j+1) N₂]
  | .split w N => simp only [Comp.shiftFrom, capsC]; rw [capsV_shiftFrom j w, capsC_shiftFrom (j+2) N]
  | .unfold w => simp only [Comp.shiftFrom, capsC]; exact capsV_shiftFrom j w
  | .binop _ w₁ w₂ => simp only [Comp.shiftFrom, capsC]; rw [capsV_shiftFrom j w₁, capsV_shiftFrom j w₂]
  | .oom | .wrong _ => rfl
theorem capsH_shiftFrom (j : Nat) (h : Handler) : capsH (Handler.shiftFrom j h) = capsH h := by
  match h with
  | .state _ s => simp only [Handler.shiftFrom, capsH]; exact capsV_shiftFrom j s
  | .throws _ => rfl
  | .transaction _ _ => rfl
  | .custom _ _ _ => rfl    -- shiftFrom is identity on custom (clauses closed) ⇒ capsH round-trips (ADR-0087)
end

mutual
/-- `substFrom k v` only injects `v` at the `vvar k` leaves, so every cap of the result was already a
cap of `u` or a cap of `v` (the binder cases use `shift v`, cap-equal to `v` by `capsV_shiftFrom`). -/
theorem capsV_substFrom (k : Nat) (v u : Val) :
    ∀ p ∈ capsV (Val.substFrom k v u), p ∈ capsV u ∨ p ∈ capsV v := by
  match u with
  | .vunit | .vint _ => intro p hp; simp [Val.substFrom, capsV] at hp
  | .vcap n ℓ => intro p hp; exact Or.inl hp
  | .vvar i =>
      intro p hp
      simp only [Val.substFrom] at hp
      split at hp
      · exact Or.inr hp
      · split at hp <;> simp [capsV] at hp
  | .vthunk c => intro p hp; simp only [Val.substFrom, capsV] at hp ⊢; exact capsC_substFrom k v c p hp
  | .inl w => intro p hp; simp only [Val.substFrom, capsV] at hp ⊢; exact capsV_substFrom k v w p hp
  | .inr w => intro p hp; simp only [Val.substFrom, capsV] at hp ⊢; exact capsV_substFrom k v w p hp
  | .pair a b =>
      intro p hp; simp only [Val.substFrom, capsV, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsV_substFrom k v a p h with h' | h' <;> tauto
      · rcases capsV_substFrom k v b p h with h' | h' <;> tauto
  | .fold w => intro p hp; simp only [Val.substFrom, capsV] at hp ⊢; exact capsV_substFrom k v w p hp
theorem capsC_substFrom (k : Nat) (v : Val) (c : Comp) :
    ∀ p ∈ capsC (Comp.substFrom k v c), p ∈ capsC c ∨ p ∈ capsV v := by
  match c with
  | .ret w => intro p hp; simp only [Comp.substFrom, capsC] at hp ⊢; exact capsV_substFrom k v w p hp
  | .force w => intro p hp; simp only [Comp.substFrom, capsC] at hp ⊢; exact capsV_substFrom k v w p hp
  | .unfold w => intro p hp; simp only [Comp.substFrom, capsC] at hp ⊢; exact capsV_substFrom k v w p hp
  | .binop _ w₁ w₂ =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsV_substFrom k v w₁ p h with h' | h' <;> tauto
      · rcases capsV_substFrom k v w₂ p h with h' | h' <;> tauto
  | .lam M =>
      intro p hp; simp only [Comp.substFrom, capsC] at hp ⊢
      rcases capsC_substFrom (k+1) (Val.shift v) M p hp with h | h
      · exact Or.inl h
      · exact Or.inr (by rwa [capsV_shiftFrom] at h)
  | .letC M N =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsC_substFrom k v M p h with h' | h' <;> tauto
      · rcases capsC_substFrom (k+1) (Val.shift v) N p h with h' | h'
        · tauto
        · exact Or.inr (by rwa [capsV_shiftFrom] at h')
  | .app M w =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsC_substFrom k v M p h with h' | h' <;> tauto
      · rcases capsV_substFrom k v w p h with h' | h' <;> tauto
  | .perform cp _ w =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsV_substFrom k v cp p h with h' | h' <;> tauto
      · rcases capsV_substFrom k v w p h with h' | h' <;> tauto
  | .handle hd M =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsH_substFrom k v hd p h with h' | h' <;> tauto
      · rcases capsC_substFrom (k+1) (Val.shift v) M p h with h' | h'
        · tauto
        · exact Or.inr (by rwa [capsV_shiftFrom] at h')
  | .case w N₁ N₂ =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with (h | h) | h
      · rcases capsV_substFrom k v w p h with h' | h' <;> tauto
      · rcases capsC_substFrom (k+1) (Val.shift v) N₁ p h with h' | h'
        · tauto
        · exact Or.inr (by rwa [capsV_shiftFrom] at h')
      · rcases capsC_substFrom (k+1) (Val.shift v) N₂ p h with h' | h'
        · tauto
        · exact Or.inr (by rwa [capsV_shiftFrom] at h')
  | .split w N =>
      intro p hp; simp only [Comp.substFrom, capsC, List.mem_append] at hp ⊢
      rcases hp with h | h
      · rcases capsV_substFrom k v w p h with h' | h' <;> tauto
      · rcases capsC_substFrom (k+2) (Val.shift (Val.shift v)) N p h with h' | h'
        · tauto
        · exact Or.inr (by rwa [capsV_shiftFrom, capsV_shiftFrom] at h')
  | .oom | .wrong _ => intro p hp; simp [Comp.substFrom, capsC] at hp
theorem capsH_substFrom (k : Nat) (v : Val) (h : Handler) :
    ∀ p ∈ capsH (Handler.substFrom k v h), p ∈ capsH h ∨ p ∈ capsV v := by
  match h with
  | .state _ s => intro p hp; simp only [Handler.substFrom, capsH] at hp ⊢; exact capsV_substFrom k v s p hp
  | .throws _ => intro p hp; simp [Handler.substFrom, capsH] at hp
  | .transaction _ _ => intro p hp; exact Or.inl hp
  -- custom: `Handler.substFrom` is the IDENTITY (clauses closed, Stage-1), so `capsH (subst …) = capsH h`
  -- ⇒ every cap of the result is already a cap of `h` (ADR-0087: capsH is honest but subst is inert here).
  | .custom _ _ _ => intro p hp; exact Or.inl hp
end

/-! ### §3.0b — DISPATCH-arm freshness: the resumed stack + focus stay `< g`. Richer mirror of
`stackBelow_idDispatch` (it also reassembles `StratFresh` + the FLAT stored-cap bound `capsK`, and
bounds the resumed FOCUS `ret s`/`ret cell` via the MATCHED handler's `capsH`-bound — the piece
`CapsBelow` omits, supplied by `FreshCfg`'s `capsK` conjunct). -/

/-- `capsK` distributes over `++` (collects every frame's caps, `handleF` included). -/
theorem capsK_append : ∀ (K1 K2 : EvalCtx), capsK (K1 ++ K2) = capsK K1 ++ capsK K2
  | [], _ => rfl
  | (Frame.letF N :: K1), K2 => by
      simp only [List.cons_append, capsK, capsK_append K1 K2, List.append_assoc]
  | (Frame.appF v :: K1), K2 => by
      simp only [List.cons_append, capsK, capsK_append K1 K2, List.append_assoc]
  | (Frame.handleF n h :: K1), K2 => by
      simp only [List.cons_append, capsK, capsK_append K1 K2, List.append_assoc]

/-- A successful `splitAtId` reconstructs the stack around the matched frame. -/
theorem splitAtId_reconstruct : ∀ {K : EvalCtx} {n : Nat} {Kᵢ Kₒ : EvalCtx} {h : Handler},
    splitAtId K n = some (Kᵢ, h, Kₒ) → K = Kᵢ ++ Frame.handleF n h :: Kₒ := by
  intro K
  induction K with
  | nil => intro n Kᵢ Kₒ h hsp; simp [splitAtId] at hsp
  | cons fr K ih =>
    intro n Kᵢ Kₒ h hsp
    cases fr with
    | handleF m hd =>
      simp only [splitAtId] at hsp
      by_cases hmn : m = n
      · rw [if_pos hmn] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨rfl, rfl, rfl⟩ := hsp; subst hmn; rfl
      · rw [if_neg hmn, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        rw [ih hsp']; rfl
    | letF N =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [ih hsp']; rfl
    | appF w =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [ih hsp']; rfl

/-- `CapsBelow` distributes over `++` (every frame independently dominated). -/
theorem CapsBelow_append (g : Nat) : ∀ (K1 K2 : EvalCtx),
    CapsBelow g (K1 ++ K2) ↔ CapsBelow g K1 ∧ CapsBelow g K2 := by
  intro K1 K2
  induction K1 with
  | nil => simp only [List.nil_append, CapsBelow, true_and]
  | cons fr K1 ih =>
    cases fr with
    | handleF n hd => simp only [List.cons_append, CapsBelow, ih]; tauto
    | letF N => simp only [List.cons_append, CapsBelow, ih]; tauto
    | appF w => simp only [List.cons_append, CapsBelow, ih]; tauto

/-- `CapsBelow` ignores handler CONTENT — the `handleF n _` clause matches the handler with `_`, so
swapping `h` for `h'` (same id `n`) anywhere in the stack preserves `CapsBelow`. -/
theorem capsBelow_handler_irrel {g n : Nat} {h h' : Handler} : ∀ {Kᵢ Kₒ : EvalCtx},
    CapsBelow g (Kᵢ ++ Frame.handleF n h :: Kₒ) → CapsBelow g (Kᵢ ++ Frame.handleF n h' :: Kₒ) := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro Kₒ hcb; exact hcb
  | cons fr Kᵢ ih =>
    intro Kₒ hcb
    cases fr with
    | handleF m hd => simp only [List.cons_append, CapsBelow] at hcb ⊢; exact ⟨hcb.1, ih hcb.2⟩
    | letF N => simp only [List.cons_append, CapsBelow] at hcb ⊢; exact ⟨hcb.1, ih hcb.2⟩
    | appF w => simp only [List.cons_append, CapsBelow] at hcb ⊢; exact ⟨hcb.1, ih hcb.2⟩

/-- `StratFresh` ignores handler content too (it reads only ids + the handler-irrelevant `CapsBelow`). -/
theorem stratFresh_handler_irrel {n : Nat} {h h' : Handler} : ∀ {Kᵢ Kₒ : EvalCtx},
    StratFresh (Kᵢ ++ Frame.handleF n h :: Kₒ) → StratFresh (Kᵢ ++ Frame.handleF n h' :: Kₒ) := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro Kₒ hsf; exact hsf
  | cons fr Kᵢ ih =>
    intro Kₒ hsf
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StratFresh] at hsf ⊢
      exact ⟨capsBelow_handler_irrel hsf.1, ih hsf.2⟩
    | letF N => simp only [List.cons_append, StratFresh] at hsf ⊢; exact ih hsf
    | appF w => simp only [List.cons_append, StratFresh] at hsf ⊢; exact ih hsf

/-- The outer sub-stack `Kₒ` of a split inherits `StratFresh` (the `throws` ABORT yields it directly). -/
theorem stratFresh_outer {n : Nat} {h : Handler} : ∀ {Kᵢ Kₒ : EvalCtx},
    StratFresh (Kᵢ ++ Frame.handleF n h :: Kₒ) → StratFresh Kₒ := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro Kₒ hsf; simp only [List.nil_append, StratFresh] at hsf; exact hsf.2
  | cons fr Kᵢ ih =>
    intro Kₒ hsf
    cases fr with
    | handleF m hd => simp only [List.cons_append, StratFresh] at hsf; exact ih hsf.2
    | letF N => simp only [List.cons_append, StratFresh] at hsf; exact ih hsf
    | appF w => simp only [List.cons_append, StratFresh] at hsf; exact ih hsf

/-- `getD` reads a list element or the default — its caps are bounded by the list's caps ∪ the default's. -/
theorem capsV_getD_mem {Θ : Store} {i : Nat} {d : Val} {p : Nat × Label}
    (hp : p ∈ capsV (Θ.getD i d)) : p ∈ Θ.flatMap capsV ∨ p ∈ capsV d := by
  rw [List.getD_eq_getElem?_getD] at hp
  rcases lt_or_ge i Θ.length with hlt | hge
  · left; rw [List.getElem?_eq_getElem hlt, Option.getD_some] at hp
    exact List.mem_flatMap.mpr ⟨Θ[i], List.getElem_mem hlt, hp⟩
  · right; rw [List.getElem?_eq_none hge, Option.getD_none] at hp; exact hp

/-- `List.set` replaces one cell — the result's caps are bounded by the old caps ∪ the new value's. -/
theorem capsV_set_mem {Θ : Store} {i : Nat} {w : Val} {p : Nat × Label}
    (hp : p ∈ (List.set Θ i w).flatMap capsV) : p ∈ Θ.flatMap capsV ∨ p ∈ capsV w := by
  rw [List.mem_flatMap] at hp
  obtain ⟨x, hx, hpx⟩ := hp
  rcases List.mem_or_eq_of_mem_set hx with h' | h'
  · exact Or.inl (List.mem_flatMap.mpr ⟨x, h', hpx⟩)
  · exact Or.inr (h' ▸ hpx)

/-- **DISPATCH-arm freshness (the resumed stack + focus stay `< g`).** Given the pre-step `FreshCfg`
components for `K` and the `perform` payload bound (`caps v < g`), a successful `idDispatch` yields a
config whose stack stays `CapsBelow`/`StratFresh`/`capsK`-bounded and whose focus `c'` is cap-`< g`. The
resume's stored-value focus (`get`'s `ret s`, `readTVar`'s `ret cell`) is bounded by the MATCHED
handler's `capsH ⊆ capsK K < g`; reassembly is handler-content-irrelevant (`*_handler_irrel`). -/
theorem freshStack_idDispatch {g : Nat} {K K' : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId}
    {v : Val} {c' : Comp} (hcb : CapsBelow g K) (hsf : StratFresh K)
    (hck : ∀ p ∈ capsK K, p.1 < g) (hv : ∀ p ∈ capsV v, p.1 < g)
    (hd : idDispatch K n ℓ op v = some (K', c')) :
    CapsBelow g K' ∧ (∀ p ∈ capsC c', p.1 < g) ∧ StratFresh K' ∧ (∀ p ∈ capsK K', p.1 < g) := by
  unfold idDispatch at hd
  obtain ⟨⟨Kᵢ, h, Kₒ⟩, hsplit, hd2⟩ := Option.bind_eq_some_iff.mp hd
  have hrec : K = Kᵢ ++ Frame.handleF n h :: Kₒ := splitAtId_reconstruct hsplit
  -- the three FreshCfg components of `K`, split around the matched frame.
  have hcbo : CapsBelow g Kₒ := ((CapsBelow_append g Kᵢ (Frame.handleF n h :: Kₒ)).mp (hrec ▸ hcb)).2.2
  -- the FLAT stored-cap bounds: `capsK Kᵢ`, `capsH h`, `capsK Kₒ` all `< g`.
  have hckmem : ∀ {q : Nat × Label}, q ∈ capsK Kᵢ ∨ q ∈ capsH h ∨ q ∈ capsK Kₒ → q.1 < g := by
    intro q hq; apply hck; rw [hrec, capsK_append]; simp only [capsK]
    rcases hq with h' | h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_append_left _ h')
    · exact List.mem_append_right _ (List.mem_append_right _ h')
  have hcki : ∀ p ∈ capsK Kᵢ, p.1 < g := fun p hp => hckmem (Or.inl hp)
  have hckh : ∀ p ∈ capsH h, p.1 < g := fun p hp => hckmem (Or.inr (Or.inl hp))
  have hcko : ∀ p ∈ capsK Kₒ, p.1 < g := fun p hp => hckmem (Or.inr (Or.inr hp))
  -- `capsK` of a reassembled stack `Kᵢ ++ handleF n h' :: Kₒ`, given the new handler's caps `< g`.
  have hreassemble_capsK : ∀ (h'' : Handler), (∀ p ∈ capsH h'', p.1 < g) →
      ∀ p ∈ capsK (Kᵢ ++ Frame.handleF n h'' :: Kₒ), p.1 < g := by
    intro h'' hch'' p hp
    rw [capsK_append] at hp; simp only [capsK] at hp
    rcases List.mem_append.mp hp with h' | h'
    · exact hcki p h'
    · rcases List.mem_append.mp h' with h'' | h''
      · exact hch'' p h''
      · exact hcko p h''
  dsimp only at hd2  -- iota-reduce the destructuring-lambda `match (Kᵢ,h,Kₒ) with …` to the bare `if`
  by_cases hk : handlesOp h ℓ op = true
  · rw [if_pos hk] at hd2
    cases h with
    | throws ℓ' =>
      simp only [dispatchOn, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, rfl⟩ := hd2
      exact ⟨hcbo, fun p hp => hv p (by simpa only [capsC] using hp),
        stratFresh_outer (hrec ▸ hsf), hcko⟩
    | state ℓ' s =>
      have hch : ∀ p ∈ capsH (Handler.state ℓ' s), p.1 < g := hckh
      simp only [capsH] at hch
      simp only [dispatchOn] at hd2
      split at hd2 <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, rfl⟩ := hd2
          refine ⟨capsBelow_handler_irrel (hrec ▸ hcb), ?_,
            stratFresh_handler_irrel (hrec ▸ hsf), hreassemble_capsK _ ?_⟩
          · intro p hp; simp only [capsC] at hp
            first
            | exact hch p hp                                                   -- `get`: focus `ret s`
            | (simp only [capsV] at hp; exact absurd hp (by simp))  -- `put`: focus `ret unit`
          · intro p hp; simp only [capsH] at hp
            first
            | exact hch p hp                                                   -- `get`: cell `s` unchanged
            | exact hv p hp                                                    -- `put`: cell ← payload `v`
    | transaction ℓ' Θ =>
      have hch : ∀ p ∈ capsH (Handler.transaction ℓ' Θ), p.1 < g := hckh
      simp only [capsH] at hch
      simp only [dispatchOn] at hd2
      (repeat' split at hd2) <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, rfl⟩ := hd2
          refine ⟨capsBelow_handler_irrel (hrec ▸ hcb), ?_,
            stratFresh_handler_irrel (hrec ▸ hsf), hreassemble_capsK _ ?_⟩
          · intro p hp; simp only [capsC] at hp
            first
            | (simp only [capsV] at hp; exact absurd hp (by simp))  -- focus `ret unit`/`ret (vint _)`
            | (rcases capsV_getD_mem hp with h' | h'                           -- `readTVar`: focus `ret cell`
               · exact hch p h'
               · simp only [capsV] at h'; exact absurd h' (by simp))
          · intro p hp; simp only [capsH] at hp
            first
            | exact hch p hp                                                   -- heap unchanged
            | (rw [List.flatMap_append] at hp                                  -- `newTVar`: heap ++ [v]
               rcases List.mem_append.mp hp with h' | h'
               · exact hch p h'
               · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h'; exact hv p h')
            | (rcases capsV_set_mem hp with h' | h'                            -- `writeTVar`: set cell
               · exact hch p h'
               · exact hv p (by simp only [capsV, List.mem_append] at h' ⊢; tauto))
    | custom ℓ' pm cl =>
      -- custom (ADR-0085 stage 2, ADR-0087 finite rep): ONE-SHOT resume (read-only param). Mirrors `state`
      -- — the reassembled stack + the param/arg/CLAUSE focus caps stay `< g`. THE D2 PAYOFF: the resume
      -- focus is the substituted user CLAUSE, whose OWN literal caps ARE now bounded — `capsH custom =
      -- capsV pm ++ capsCls cl` enumerates them, so the gh44s2 clause-cap `sorry` closes via `capsCls_find?`
      -- + `hch` (the enumerability the finite rep buys). No new premise, unlike the ADR-0085 threaded route.
      have hch : ∀ q ∈ capsH (Handler.custom ℓ' pm cl), q.1 < g := hckh
      simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨_, hsome⟩ := hk
      obtain ⟨clause, hcl⟩ := Option.isSome_iff_exists.mp hsome
      simp only [dispatchOn, hcl, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, rfl⟩ := hd2
      refine ⟨capsBelow_handler_irrel (hrec ▸ hcb), ?_,
        stratFresh_handler_irrel (hrec ▸ hsf), hreassemble_capsK _ ?_⟩
      · intro q hq
        rcases capsC_substFrom 0 pm _ q hq with h' | h'
        · rcases capsC_substFrom 0 (Val.shift v) clause.2 q h' with h'' | h''
          · -- q ∈ capsC clause.2: the clause's OWN literal caps, now bounded (ADR-0087 enumerability).
            exact hch q (by simp only [capsH]; exact List.mem_append_right _ (capsCls_find? hcl q h''))
          · rw [capsV_shiftFrom] at h''; exact hv q h''
        · exact hch q (by simp only [capsH]; exact List.mem_append_left _ h')
      · intro q hq; simp only [capsH] at hq; exact hch q (by simp only [capsH]; exact hq)
  · rw [if_neg hk] at hd2; exact absurd hd2 (by simp)

/-- The `Bool=1+1` encoding (ADR-0065) is closed: it carries no capabilities. -/
theorem capsV_boolVal (b : Bool) : capsV (boolVal b) = [] := by cases b <;> simp [boolVal, capsV]
/-- A δ-rule result is a CLOSED value (vint or boolVal), so it carries no capabilities (ADR-0065). -/
theorem capsV_binopEval (op : BinOp) (a b : Int) : capsV (BinOp.eval op a b) = [] := by
  cases op <;> simp [BinOp.eval, capsV, capsV_boolVal]

/-- **FRESHNESS PRESERVATION (Phase 2 — the freshness arm).** `FreshCfg` rides `Source.step`: MINT pushes
`handleF g`, advances the counter to `g+1`, injects `vcap g` (the new focus cap `g < g+1`) and re-bounds
the old frames by monotonicity; POP inverts the `StratFresh` head; PUSH/REDUCE re-home sub-stacks; the
focus-cap bound rides because every reduct's caps are a subset of the redex's. Stack-structural ADR-0055
preservation — mechanical but REAL (mint extends, pop inverts); SORRIED for Phase 2, NOT hand-waved. -/
theorem freshCfg_step (cfg cfg' : Config)
    (h : FreshCfg cfg)
    (hstep : Source.step cfg = some cfg') : FreshCfg cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  obtain ⟨hcb, hfc, hsf, hck⟩ := h
  cases c with
  | letC M N =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    refine ⟨⟨fun p hp => hfc p (by simp only [capsC]; exact List.mem_append_right _ hp), hcb⟩,
      fun p hp => hfc p (by simp only [capsC]; exact List.mem_append_left _ hp), hsf, ?_⟩
    intro p hp; simp only [capsK] at hp
    rcases List.mem_append.mp hp with h' | h'
    · exact hfc p (by simp only [capsC]; exact List.mem_append_right _ h')
    · exact hck p h'
  | app M w =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    refine ⟨⟨fun p hp => hfc p (by simp only [capsC]; exact List.mem_append_right _ hp), hcb⟩,
      fun p hp => hfc p (by simp only [capsC]; exact List.mem_append_left _ hp), hsf, ?_⟩
    intro p hp; simp only [capsK] at hp
    rcases List.mem_append.mp hp with h' | h'
    · exact hfc p (by simp only [capsC]; exact List.mem_append_right _ h')
    · exact hck p h'
  | handle hh M =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    refine ⟨⟨Nat.lt_succ_self g, CapsBelow_mono (Nat.le_succ g) K hcb⟩, ?_,
      ⟨hcb, hsf⟩, ?_⟩
    · intro p hp
      rcases capsC_substFrom 0 (Val.vcap g hh.label) M p hp with h' | h'
      · have := hfc p (by simp only [capsC]; exact List.mem_append_right _ h'); omega
      · simp only [capsV, List.mem_singleton] at h'; subst h'; exact Nat.lt_succ_self g
    · intro p hp; simp only [capsK] at hp
      rcases List.mem_append.mp hp with h' | h'
      · have := hfc p (by simp only [capsC]; exact List.mem_append_left _ h'); omega
      · have := hck p h'; omega
  | force w =>
    cases w with
    | vthunk M =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      exact ⟨hcb, fun p hp => hfc p (by simp only [capsC, capsV]; exact hp), hsf, hck⟩
    | vunit | vint _ | vvar _ | vcap _ _ | inl _ | inr _ | pair _ _ | fold _ =>
      simp [Source.step] at hstep
  | ret v =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        refine ⟨hcb.2, ?_, hsf, fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)⟩
        intro p hp
        rcases capsC_substFrom 0 v N p hp with h' | h'
        · exact hcb.1 p h'
        · exact hfc p (by simp only [capsC]; exact h')
      | appF w => simp [Source.step] at hstep
      | handleF g' hh =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        obtain ⟨_, hsf2⟩ := hsf
        exact ⟨hcb.2, hfc, hsf2, fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)⟩
  | lam M =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N => simp [Source.step] at hstep
      | handleF g' hh => simp [Source.step] at hstep
      | appF w =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        refine ⟨hcb.2, ?_, hsf, fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)⟩
        intro p hp
        rcases capsC_substFrom 0 w M p hp with h' | h'
        · exact hfc p (by simp only [capsC]; exact h')
        · exact hcb.1 p h'
  | case v N₁ N₂ =>
    cases v with
    | inl a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      refine ⟨hcb, ?_, hsf, hck⟩
      intro p hp
      rcases capsC_substFrom 0 a N₁ p hp with h' | h'
      · exact hfc p (by simp only [capsC]; exact List.mem_append_left _ (List.mem_append_right _ h'))
      · exact hfc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_left _ h'))
    | inr a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      refine ⟨hcb, ?_, hsf, hck⟩
      intro p hp
      rcases capsC_substFrom 0 a N₂ p hp with h' | h'
      · exact hfc p (by simp only [capsC]; exact List.mem_append_right _ h')
      · exact hfc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_left _ h'))
    | vunit | vint _ | vvar _ | vcap _ _ | vthunk _ | pair _ _ | fold _ =>
      simp [Source.step] at hstep
  | split v N =>
    cases v with
    | pair a b =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      refine ⟨hcb, ?_, hsf, hck⟩
      intro p hp
      rcases capsC_substFrom 0 a _ p hp with h' | h'
      · rcases capsC_substFrom 0 (Val.shift b) N p h' with h'' | h''
        · exact hfc p (by simp only [capsC]; exact List.mem_append_right _ h'')
        · rw [capsV_shiftFrom] at h''
          exact hfc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_right _ h''))
      · exact hfc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_left _ h'))
    | vunit | vint _ | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | fold _ =>
      simp [Source.step] at hstep
  | unfold v =>
    cases v with
    | fold a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      exact ⟨hcb, fun p hp => hfc p (by simpa only [capsC, capsV] using hp), hsf, hck⟩
    | vunit | vint _ | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | pair _ _ =>
      simp [Source.step] at hstep
  | binop op v w =>
    -- δ-rule: steps (on vint/vint) to `ret (op.eval …)`, a CLOSED reduct (no caps, `capsV_binopEval`);
    -- the stack `K` is unchanged so field-1 (`hcb`) transfers, field-2 is vacuous (mirror case/split).
    cases v with
    | vint a =>
      cases w with
      | vint b =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        refine ⟨hcb, ?_, hsf, hck⟩
        intro p hp; simp only [capsC, capsV_binopEval, List.not_mem_nil] at hp
      | vunit | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | pair _ _ | fold _ =>
        simp [Source.step] at hstep
    | vunit | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | pair _ _ | fold _ =>
      cases w <;> simp [Source.step] at hstep
  | perform cv op v =>
    -- DISPATCH (#freshness): the resumed stack reassembles `CapsBelow`/`StratFresh`/`capsK` and the
    -- resumed focus's caps are `< g` — ALL pure-structural via `freshStack_idDispatch`. The state-`get`
    -- focus `ret s` / `readTVar` focus `ret cell` rides the MATCHED handler's `capsH ⊆ capsK K < g`
    -- (the new `FreshCfg` `capsK` conjunct) — NO typing/`hWSK` needed (the `capsH`-bound subsumes the
    -- abandoned `capFreeStored` route, which couldn't bound dormant thunk-buried caps).
    cases cv with
    | vcap n ℓ =>
      simp only [Source.step, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨K'', c''⟩, hd, rfl⟩ := hstep
      exact freshStack_idDispatch hcb hsf hck
        (fun p hp => hfc p (by simp only [capsC]; exact List.mem_append_right _ hp)) hd
    | vunit | vint _ | vvar _ | vthunk _ | inl _ | inr _ | pair _ _ | fold _ =>
      simp [Source.step] at hstep
  | oom => simp [Source.step] at hstep
  | wrong s => simp [Source.step] at hstep

end -- @[expose] public section
end Bang.Model

/-! # `CustomFree` — no `Handler.custom` node anywhere (the amended-premise predicate, ADR-0086).
Weaker than `Comp.Pure`: allows perform/handle(state/throws/txn), forbids only custom. Threaded
through the converse-of-`run_evalD` completeness spine (`Bang.CalcVM.evalD_complete_gen_full`,
Backend) to discharge the ONLY non-closing arm (custom): `CFHandler (.custom …) = False` makes the
custom `handle` case absurd. Vacuous for every elaborator-produced program (no surface form emits
`custom` until ADR-0085 Stage 7). The store/heap analogues (`CFStore`/`CFHeap`) live in Backend
(they depend on `SStore`/`THeap`/`txnService`, which are `Bang.CalcVM`). -/
namespace Bang.CustomFree
open Bang (Val Comp Handler)

@[expose] public section

mutual
/-- A computation contains no `Handler.custom` node anywhere in it. -/
def CFComp : Comp → Prop
  | .ret v            => CFVal v
  | .letC M N         => CFComp M ∧ CFComp N
  | .force v          => CFVal v
  | .lam M            => CFComp M
  | .app M v          => CFComp M ∧ CFVal v
  | .perform c _ v    => CFVal c ∧ CFVal v
  | .handle h M       => CFHandler h ∧ CFComp M
  | .case v N₁ N₂     => CFVal v ∧ CFComp N₁ ∧ CFComp N₂
  | .split v N        => CFVal v ∧ CFComp N
  | .unfold v         => CFVal v
  | .binop _ a b      => CFVal a ∧ CFVal b
  | .oom              => True
  | .wrong _          => True
/-- A value contains no `Handler.custom` node anywhere in it. -/
def CFVal : Val → Prop
  | .vunit | .vint _ | .vvar _ | .vcap _ _ => True
  | .vthunk c         => CFComp c
  | .inl v | .inr v | .fold v => CFVal v
  | .pair a b         => CFVal a ∧ CFVal b
/-- A handler is not `Handler.custom` and its carried values are `CustomFree`. -/
def CFHandler : Handler → Prop
  | .state _ v        => CFVal v
  | .throws _         => True
  | .transaction _ Θ  => ∀ w ∈ Θ, CFVal w
  | .custom _ _ _     => False
end

/-! ### Shift preservation (CFVal/CFComp survive `shiftFrom`). -/
mutual
theorem CFVal_shiftFrom (k : Nat) : ∀ {t : Val}, CFVal t → CFVal (Val.shiftFrom k t)
  | .vunit, _ => by simp [Val.shiftFrom, CFVal]
  | .vint _, _ => by simp [Val.shiftFrom, CFVal]
  | .vcap _ _, _ => by simp [Val.shiftFrom, CFVal]
  | .vvar i, _ => by by_cases hi : i < k <;> simp [Val.shiftFrom, hi, CFVal]
  | .vthunk M, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFComp_shiftFrom k h
  | .inl w, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFVal_shiftFrom k h
  | .inr w, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFVal_shiftFrom k h
  | .pair a b, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .fold w, h => by simp only [Val.shiftFrom, CFVal] at h ⊢; exact CFVal_shiftFrom k h
theorem CFHandler_shiftFrom (k : Nat) : ∀ {hd : Handler}, CFHandler hd → CFHandler (Handler.shiftFrom k hd)
  | .state ℓ s, h => by simp only [Handler.shiftFrom, CFHandler] at h ⊢; exact CFVal_shiftFrom k h
  | .throws ℓ, _ => by simp [Handler.shiftFrom, CFHandler]
  | .transaction ℓ Θ, h => by simpa only [Handler.shiftFrom, CFHandler] using h
  | .custom ℓ p cl, h => by simp only [CFHandler] at h
theorem CFComp_shiftFrom (k : Nat) : ∀ {t : Comp}, CFComp t → CFComp (Comp.shiftFrom k t)
  | .ret w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFVal_shiftFrom k h
  | .letC M N, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFComp_shiftFrom k h.1, CFComp_shiftFrom (k+1) h.2⟩
  | .force w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFVal_shiftFrom k h
  | .lam M, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFComp_shiftFrom (k+1) h
  | .app M w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFComp_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .perform c op w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .handle hd M, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFHandler_shiftFrom k h.1, CFComp_shiftFrom (k+1) h.2⟩
  | .case w N₁ N₂, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFComp_shiftFrom (k+1) h.2.1, CFComp_shiftFrom (k+1) h.2.2⟩
  | .split w N, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFComp_shiftFrom (k+2) h.2⟩
  | .unfold w, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact CFVal_shiftFrom k h
  | .binop op a b, h => by simp only [Comp.shiftFrom, CFComp] at h ⊢; exact ⟨CFVal_shiftFrom k h.1, CFVal_shiftFrom k h.2⟩
  | .oom, _ => by simp [Comp.shiftFrom, CFComp]
  | .wrong s, _ => by simp [Comp.shiftFrom, CFComp]
end

/-! ### Subst preservation (filler CFVal). -/
mutual
theorem CFVal_substFrom (k : Nat) {v : Val} (hv : CFVal v) : ∀ {t : Val}, CFVal t → CFVal (Val.substFrom k v t)
  | .vunit, _ => by simp [Val.substFrom, CFVal]
  | .vint _, _ => by simp [Val.substFrom, CFVal]
  | .vcap _ _, _ => by simp [Val.substFrom, CFVal]
  | .vvar i, _ => by
      simp only [Val.substFrom]; by_cases h1 : i = k
      · simp [h1, hv]
      · by_cases h2 : i > k <;> simp [h1, h2, CFVal]
  | .vthunk M, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFComp_substFrom k hv h
  | .inl w, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFVal_substFrom k hv h
  | .inr w, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFVal_substFrom k hv h
  | .pair a b, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .fold w, h => by simp only [Val.substFrom, CFVal] at h ⊢; exact CFVal_substFrom k hv h
theorem CFHandler_substFrom (k : Nat) {v : Val} (hv : CFVal v) : ∀ {hd : Handler}, CFHandler hd → CFHandler (Handler.substFrom k v hd)
  | .state ℓ s, h => by simp only [Handler.substFrom, CFHandler] at h ⊢; exact CFVal_substFrom k hv h
  | .throws ℓ, _ => by simp [Handler.substFrom, CFHandler]
  | .transaction ℓ Θ, h => by simpa only [Handler.substFrom, CFHandler] using h
  | .custom ℓ p cl, h => by simp only [CFHandler] at h
theorem CFComp_substFrom (k : Nat) {v : Val} (hv : CFVal v) : ∀ {t : Comp}, CFComp t → CFComp (Comp.substFrom k v t)
  | .ret w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFVal_substFrom k hv h
  | .letC M N, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFComp_substFrom k hv h.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2⟩
  | .force w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFVal_substFrom k hv h
  | .lam M, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h
  | .app M w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFComp_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .perform c op w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .handle hd M, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFHandler_substFrom k hv h.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2⟩
  | .case w N₁ N₂, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2.1, CFComp_substFrom (k+1) (CFVal_shiftFrom 0 hv) h.2.2⟩
  | .split w N, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFComp_substFrom (k+2) (CFVal_shiftFrom 0 (CFVal_shiftFrom 0 hv)) h.2⟩
  | .unfold w, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact CFVal_substFrom k hv h
  | .binop op a b, h => by simp only [Comp.substFrom, CFComp] at h ⊢; exact ⟨CFVal_substFrom k hv h.1, CFVal_substFrom k hv h.2⟩
  | .oom, _ => by simp [Comp.substFrom, CFComp]
  | .wrong s, _ => by simp [Comp.substFrom, CFComp]
end

theorem CFComp_subst {v : Val} {N : Comp} (hv : CFVal v) (hN : CFComp N) : CFComp (Comp.subst v N) :=
  CFComp_substFrom 0 hv hN

/-- `CFComp (ret v) ↔ CFVal v` (definitional; the named bridge avoids relying on the elaborator to
unfold `CFComp` under `And.intro`). -/
theorem CFComp_ret {v : Val} (h : CFVal v) : CFComp (Comp.ret v) := by
  simp only [CFComp]; exact h
theorem CFVal_of_CFComp_ret {v : Val} (h : CFComp (Comp.ret v)) : CFVal v := by
  simp only [CFComp] at h; exact h

end -- @[expose] public section
end Bang.CustomFree
