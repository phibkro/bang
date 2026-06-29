/-
inc-6 U3 route-A — the label-coherence forward-invariant (Bang.CapCoh), build-arbitrated, axiom-clean, #35-FREE.

The label-coherence forward-invariant `CapLabelCoh` + its `Source.step` preservation `capLabelCoh_step`,
the premise `run_evalD` must carry (refuted absent: `CapLabelCohRefute.lean`). Resolves the
identity-vs-label asymmetry: `evalD` dispatches by identity ignoring the cap label, the kernel
`idDispatch` fail-louds on label mismatch — so the bridge term-success arm needs the frame label = cap
label. `CapLabelCoh` carries exactly that (`WeakCoh`, vacuous on escaped caps), and its preservation
rides ONLY gensym freshness (`FreshCfg`/`freshCfg_step`-style) + splitAtId structural lemmas — NO grades,
so it DODGES the #35 (`wsCfg_step` DISPATCH) sorry that makes the strict-NonEscape `Model.diagonal` carry
sorryAx. AXIOM GATE (force-rebuilt olean, `#print axioms` at file end):
  capLabelCoh_step         : [propext, Classical.choice, Quot.sound]   -- the preservation, sorryAx-FREE
  capLabelCoh_initial      : [propext, Quot.sound]                     -- VcapFree seed (vacuous)
  capLabelCoh_perform_label: [propext, Quot.sound]                     -- bridge-facing label extraction

AsmFX §7.1 well-scoping-invariant analog: kernel dispatches by (identity,label), evalD by identity;
the gap is bridged by THREADING this invariant, not by mirroring dispatch. `WeakCoh` is the vacuous-on-
escape LABEL FACTOR of `CapResolves` (Operational:438) — `WeakCoh + store-supplied resolution ⟹
CapResolves`, reassembled at the bridge perform arm. Imports `Bang.Freshness` for the caps/freshness
layer (task #82 Phase 1b extracted it from the old `Bang/Model.lean`; this severs CapCoh→Model). -/
module

-- task #82 Phase 1b: CapCoh consumes ONLY the caps/freshness layer, which now lives in
-- `Bang/Freshness.lean` (extracted from the old `Bang/Model.lean`). Importing Freshness (not
-- Model) SEVERS the `Audit→CalcVM→CapCoh→Model` edge — Model leaves the gated closure.
public import Bang.Freshness
open Bang Bang.Model
open Bang.EffectRow (Label)

namespace Bang.CapCoh

-- Module reveal (Phase 1a). Only CalcVM imports this. `@[expose] public section`: CalcVM
-- threads WeakCoh/CapLabelCoh and the splitAtId/weakCoh lemmas. The ~13-lemma splitAtId
-- freshness theory with zero external refs is a private-able internal cluster (deferred).
@[expose] public section


/-- WeakCoh: vacuous-on-escape label coherence — the frame at identity `p.1`, IF present, has label `p.2`.
Escaped caps (handler popped ⇒ splitAtId=none) impose nothing. This is the route-A premise leaf.

**DO NOT strengthen this toward `CapResolves`.** `WeakCoh` is deliberately the *vacuous-on-escape LABEL
FACTOR* of `CapResolves` (Operational:438): `CapResolves K n ℓ op := ∃ frame ∧ handlesOp` factors as
`(splitAtId finds a live frame) × (that frame's label = ℓ)`, and `WeakCoh` is ONLY the second factor.
The bridge reassembles the FULL `CapResolves` at the perform seam — evalD's `σ.get? n = some` supplies
the existence factor (a live state frame), `WeakCoh` supplies `ℓ'=ℓ` ⟹ `handlesOp` ⟹ `CapResolves` ⟹
`dispatch_state_get`. The reason for the weakening is load-bearing: `CapResolves`' OWN forward-closure
is `NonEscape`/`Model.diagonal`, which carries `sorryAx` (#35 — the existence/non-escape half needs the
grade-dependent preservation). The label factor is grade-FREE, so threading `WeakCoh` (not `CapResolves`)
is what makes `capLabelCoh_step` axiom-clean. Strengthening it back to demand existence reintroduces #35.
(AsmFX §7.1 threads the same *weaker* well-scoping invariant + reassembles the dispatch fact at use.) -/
def WeakCoh (K : EvalCtx) (p : Nat × Label) : Prop :=
  ∀ Kᵢ h Kₒ, splitAtId K p.1 = some (Kᵢ, h, Kₒ) → Handler.label h = p.2

/-- The driving decomposition: a successful split on `fr :: K` is either the head matching (a `handleF`
whose id is `p.1`) or a deeper match in `K` returning the SAME handler. -/
private theorem splitAtId_cons_cases {fr : Frame} {K : EvalCtx} {n : Nat} {Kᵢ : EvalCtx} {h : Handler}
    {Kₒ : EvalCtx} (hs : splitAtId (fr :: K) n = some (Kᵢ, h, Kₒ)) :
    (fr = Frame.handleF n h ∧ Kᵢ = [] ∧ Kₒ = K)
    ∨ (∃ Kᵢ', splitAtId K n = some (Kᵢ', h, Kₒ)) := by
  cases fr with
  | handleF m hd =>
    simp only [splitAtId] at hs
    by_cases hmn : m = n
    · subst hmn; rw [if_pos rfl] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg hmn, Option.map_eq_some_iff] at hs
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hs
      simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
      exact Or.inr ⟨Kᵢ', hsp⟩
  | letF N =>
    simp only [splitAtId, Option.map_eq_some_iff] at hs
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hs
    simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
    exact Or.inr ⟨Kᵢ', hsp⟩
  | appF w =>
    simp only [splitAtId, Option.map_eq_some_iff] at hs
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hs
    simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
    exact Or.inr ⟨Kᵢ', hsp⟩

/-- WeakCoh under a non-matching cons (`p.1 ≠` the head id, or head is letF/appF): equivalent to K. -/
private theorem weakCoh_cons {fr : Frame} {K : EvalCtx} {p : Nat × Label}
    (hhead : ∀ hd, fr = Frame.handleF p.1 hd → Handler.label hd = p.2)
    (hK : WeakCoh K p) : WeakCoh (fr :: K) p := by
  intro Kᵢ h Kₒ hs
  rcases splitAtId_cons_cases hs with ⟨rfl, _, _⟩ | ⟨Kᵢ', hsp⟩
  · exact hhead h rfl
  · exact hK Kᵢ' h Kₒ hsp



/-- `splitAtId` finds only a handleF whose id is `j`, so a successful split bounds `j` by any
`CapsBelow g` on the stack. -/
theorem splitAtId_id_lt {g j : Nat} : ∀ {K : EvalCtx} {Kᵢ Kₒ : EvalCtx} {h : Handler},
    CapsBelow g K → splitAtId K j = some (Kᵢ, h, Kₒ) → j < g := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h _ hs; simp [splitAtId] at hs
  | cons fr K ih =>
    intro Kᵢ Kₒ h hcb hs
    rcases splitAtId_cons_cases hs with ⟨rfl, _, _⟩ | ⟨Kᵢ', hsp⟩
    · simp only [CapsBelow] at hcb; exact hcb.1
    · cases fr <;> (simp only [CapsBelow] at hcb; exact ih hcb.2 hsp)

/-- If `splitAtId Kᵢ j = none` (no live frame `j` in the prefix), a split of `Kᵢ ++ K'` passes to `K'`. -/
private theorem splitAtId_append_left_none {j : Nat} : ∀ {Kᵢ : EvalCtx} (K' : EvalCtx),
    splitAtId Kᵢ j = none →
    splitAtId (Kᵢ ++ K') j = (splitAtId K' j).map (fun t => (Kᵢ ++ t.1, t.2.1, t.2.2)) := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro K' _; simp [splitAtId, Option.map]; cases splitAtId K' j <;> rfl
  | cons fr Kᵢ ih =>
    intro K' hnone
    cases fr with
    | handleF m hd =>
      simp only [splitAtId] at hnone
      by_cases hmj : m = j
      · rw [if_pos hmj] at hnone; simp at hnone
      · rw [if_neg hmj] at hnone
        have hi : splitAtId Kᵢ j = none := Option.map_eq_none_iff.mp hnone
        simp only [List.cons_append, splitAtId, if_neg hmj, ih K' hi, Option.map_map]
        cases splitAtId K' j <;> rfl
    | letF N =>
      simp only [splitAtId, Option.map_eq_none_iff] at hnone
      simp only [List.cons_append, splitAtId, ih K' hnone, Option.map_map]
      cases splitAtId K' j <;> rfl
    | appF w =>
      simp only [splitAtId, Option.map_eq_none_iff] at hnone
      simp only [List.cons_append, splitAtId, ih K' hnone, Option.map_map]
      cases splitAtId K' j <;> rfl



/-- Replacing a frame's handler with a SAME-LABEL one preserves the label `splitAtId` finds at every id. -/
private theorem splitAtId_setHandler {n : Nat} {h h'' : Handler} (hlab : Handler.label h = Handler.label h'') :
    ∀ {Kᵢ Kₒ : EvalCtx} {j : Nat} {Ki' Ko' : EvalCtx} {hr : Handler},
      splitAtId (Kᵢ ++ Frame.handleF n h'' :: Kₒ) j = some (Ki', hr, Ko') →
      ∃ Ki'' Ko'' hr', splitAtId (Kᵢ ++ Frame.handleF n h :: Kₒ) j = some (Ki'', hr', Ko'')
        ∧ Handler.label hr' = Handler.label hr := by
  intro Kᵢ
  induction Kᵢ with
  | nil =>
    intro Kₒ j Ki' Ko' hr hs
    simp only [List.nil_append, splitAtId] at hs ⊢
    by_cases hnj : n = j
    · rw [if_pos hnj] at hs ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact ⟨[], Kₒ, h, rfl, hlab⟩
    · rw [if_neg hnj] at hs ⊢
      rw [Option.map_eq_some_iff] at hs
      obtain ⟨⟨Ki2, hr2, Ko2⟩, hsp, heq⟩ := hs
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨Frame.handleF n h :: Ki2, Ko2, hr2, by rw [hsp, Option.map_some], rfl⟩
  | cons fr Kᵢ ih =>
    intro Kₒ j Ki' Ko' hr hs
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, splitAtId] at hs ⊢
      by_cases hmj : m = j
      · rw [if_pos hmj] at hs ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        exact ⟨[], _, hd, rfl, rfl⟩
      · rw [if_neg hmj] at hs ⊢
        rw [Option.map_eq_some_iff] at hs
        obtain ⟨⟨Ki2, hr2, Ko2⟩, hsp, heq⟩ := hs
        simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨Ki'', Ko'', hr', hsp', hlr⟩ := ih hsp
        exact ⟨Frame.handleF m hd :: Ki'', Ko'', hr', by rw [hsp', Option.map_some], hlr⟩
    | letF N =>
      simp only [List.cons_append, splitAtId] at hs ⊢
      rw [Option.map_eq_some_iff] at hs
      obtain ⟨⟨Ki2, hr2, Ko2⟩, hsp, heq⟩ := hs
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨Ki'', Ko'', hr', hsp', hlr⟩ := ih hsp
      exact ⟨Frame.letF N :: Ki'', Ko'', hr', by rw [hsp', Option.map_some], hlr⟩
    | appF w =>
      simp only [List.cons_append, splitAtId] at hs ⊢
      rw [Option.map_eq_some_iff] at hs
      obtain ⟨⟨Ki2, hr2, Ko2⟩, hsp, heq⟩ := hs
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨Ki'', Ko'', hr', hsp', hlr⟩ := ih hsp
      exact ⟨Frame.appF w :: Ki'', Ko'', hr', by rw [hsp', Option.map_some], hlr⟩

/-- WeakCoh transfers across a same-label handler replacement (the state `put` / txn resume). -/
private theorem weakCoh_replace {Kᵢ Kₒ : EvalCtx} {n : Nat} {h h'' : Handler} {p : Nat × Label}
    (hlab : Handler.label h = Handler.label h'')
    (hw : WeakCoh (Kᵢ ++ Frame.handleF n h :: Kₒ) p) :
    WeakCoh (Kᵢ ++ Frame.handleF n h'' :: Kₒ) p := by
  intro Ki' hr Ko' hs
  obtain ⟨Ki'', Ko'', hr', hsp', hlr⟩ := splitAtId_setHandler hlab hs
  rw [← hlr]; exact hw Ki'' hr' Ko'' hsp'



/-- The outer sub-stack of a stratified split is `CapsBelow` the matched id. -/
private theorem stratFresh_capsBelow_outer {n : Nat} {h : Handler} : ∀ {Kᵢ Kₒ : EvalCtx},
    StratFresh (Kᵢ ++ Frame.handleF n h :: Kₒ) → CapsBelow n Kₒ := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro Kₒ hsf; simp only [List.nil_append, StratFresh] at hsf; exact hsf.1
  | cons fr Kᵢ ih =>
    intro Kₒ hsf
    cases fr with
    | handleF m hd => simp only [List.cons_append, StratFresh] at hsf; exact ih hsf.2
    | letF N => simp only [List.cons_append, StratFresh] at hsf; exact ih hsf
    | appF w => simp only [List.cons_append, StratFresh] at hsf; exact ih hsf

/-- An id `j` below the matched frame `n` does not match any (older-than-`n`-dominating) prefix frame. -/
private theorem splitAtId_prefix_none {j n : Nat} {h : Handler} : ∀ {Kᵢ Kₒ : EvalCtx},
    StratFresh (Kᵢ ++ Frame.handleF n h :: Kₒ) → j < n → splitAtId Kᵢ j = none := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro Kₒ _ _; rfl
  | cons fr Kᵢ ih =>
    intro Kₒ hsf hjn
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StratFresh] at hsf
      have hnm : n < m := (((CapsBelow_append m Kᵢ (Frame.handleF n h :: Kₒ)).mp hsf.1).2).1
      simp only [splitAtId, if_neg (by omega : ¬ m = j), ih hsf.2 hjn, Option.map_none]
    | letF N => simp only [List.cons_append, StratFresh] at hsf
                simp only [splitAtId, ih hsf hjn, Option.map_none]
    | appF w => simp only [List.cons_append, StratFresh] at hsf
                simp only [splitAtId, ih hsf hjn, Option.map_none]

/-- WeakCoh passes to the outer sub-stack on a `throws` ABORT (the inner prefix + matched frame pop). -/
private theorem weakCoh_outer {p : Nat × Label} {Kᵢ Kₒ : EvalCtx} {n : Nat} {h : Handler}
    (hsf : StratFresh (Kᵢ ++ Frame.handleF n h :: Kₒ))
    (hw : WeakCoh (Kᵢ ++ Frame.handleF n h :: Kₒ) p) : WeakCoh Kₒ p := by
  intro Ki' hr Ko' hs
  have hjn : p.1 < n := splitAtId_id_lt (stratFresh_capsBelow_outer hsf) hs
  have hpref : splitAtId Kᵢ p.1 = none := splitAtId_prefix_none hsf hjn
  have e1 : splitAtId (Frame.handleF n h :: Kₒ) p.1
              = some (Frame.handleF n h :: Ki', hr, Ko') := by
    simp only [splitAtId, if_neg (by omega : ¬ n = p.1), hs, Option.map_some]
  have e2 := splitAtId_append_left_none (Frame.handleF n h :: Kₒ) hpref
  rw [e1, Option.map_some] at e2
  exact hw _ hr _ e2



private theorem weakCoh_letF {N : Comp} {K : EvalCtx} {p : Nat × Label}
    (hK : WeakCoh K p) : WeakCoh (Frame.letF N :: K) p := by
  intro Ki h Ko hs
  rcases splitAtId_cons_cases hs with ⟨hc, _, _⟩ | ⟨Ki', hsp⟩
  · exact absurd hc (by simp)
  · exact hK Ki' h Ko hsp

private theorem weakCoh_appF {w : Val} {K : EvalCtx} {p : Nat × Label}
    (hK : WeakCoh K p) : WeakCoh (Frame.appF w :: K) p := by
  intro Ki h Ko hs
  rcases splitAtId_cons_cases hs with ⟨hc, _, _⟩ | ⟨Ki', hsp⟩
  · exact absurd hc (by simp)
  · exact hK Ki' h Ko hsp

theorem weakCoh_letF_inv {N : Comp} {K : EvalCtx} {p : Nat × Label}
    (hw : WeakCoh (Frame.letF N :: K) p) : WeakCoh K p := by
  intro Ki h Ko hs
  exact hw (Frame.letF N :: Ki) h Ko (by simp only [splitAtId, hs, Option.map_some])

theorem weakCoh_appF_inv {w : Val} {K : EvalCtx} {p : Nat × Label}
    (hw : WeakCoh (Frame.appF w :: K) p) : WeakCoh K p := by
  intro Ki h Ko hs
  exact hw (Frame.appF w :: Ki) h Ko (by simp only [splitAtId, hs, Option.map_some])

private theorem weakCoh_handleF_fresh {g : Nat} {K : EvalCtx} {hd : Handler} {p : Nat × Label}
    (hlt : p.1 < g) (hK : WeakCoh K p) : WeakCoh (Frame.handleF g hd :: K) p := by
  intro Ki h Ko hs
  rcases splitAtId_cons_cases hs with ⟨hc, _, _⟩ | ⟨Ki', hsp⟩
  · exact absurd (Frame.handleF.inj hc).1 (by omega)
  · exact hK Ki' h Ko hsp

theorem weakCoh_handleF_inv {g : Nat} {K : EvalCtx} {hd : Handler} {p : Nat × Label}
    (hcb : CapsBelow g K) (hw : WeakCoh (Frame.handleF g hd :: K) p) : WeakCoh K p := by
  intro Ki h Ko hs
  have hlt : p.1 < g := splitAtId_id_lt hcb hs
  exact hw (Frame.handleF g hd :: Ki) h Ko
    (by simp only [splitAtId, if_neg (by omega : ¬ g = p.1), hs, Option.map_some])

private theorem weakCoh_mint_self {g : Nat} {K : EvalCtx} {hd : Handler} :
    WeakCoh (Frame.handleF g hd :: K) (g, Handler.label hd) := by
  intro Ki h Ko hs
  simp only [splitAtId, if_pos rfl, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨_, rfl, _⟩ := hs; rfl



/-- **DISPATCH coherence** (the resume/abort arm, the team-lead-flagged risk). A successful `idDispatch`
preserves WeakCoh of the resumed focus + reassembled stack. Resume = same-LABEL handler replacement
(`weakCoh_replace`); abort = outer-shrink (`weakCoh_outer`). #35-free (no grades). -/
private theorem capCoh_idDispatch {g n : Nat} {ℓ : Label} {op : OpId} {v : Val} {K K' : EvalCtx} {c' : Comp}
    (hsf : StratFresh K) (hcb : CapsBelow g K)
    (hcv : ∀ p ∈ capsV v, WeakCoh K p) (hck : ∀ p ∈ capsK K, WeakCoh K p)
    (hd : idDispatch K n ℓ op v = some (K', c')) :
    (∀ p ∈ capsC c', WeakCoh K' p) ∧ (∀ p ∈ capsK K', WeakCoh K' p) := by
  unfold idDispatch at hd
  obtain ⟨⟨Kᵢ, h, Kₒ⟩, hsplit, hd2⟩ := Option.bind_eq_some_iff.mp hd
  have hrec : K = Kᵢ ++ Frame.handleF n h :: Kₒ := splitAtId_reconstruct hsplit
  -- caps in the matched decomposition are WeakCoh K, repackaged to the explicit append form.
  have wkA : ∀ p, (p ∈ capsK Kᵢ ∨ p ∈ capsH h ∨ p ∈ capsK Kₒ) →
      WeakCoh (Kᵢ ++ Frame.handleF n h :: Kₒ) p := by
    intro p hp; rw [← hrec]; apply hck
    rw [hrec, capsK_append]; simp only [capsK]
    rcases hp with h' | h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_append_left _ h')
    · exact List.mem_append_right _ (List.mem_append_right _ h')
  have wkV : ∀ p ∈ capsV v, WeakCoh (Kᵢ ++ Frame.handleF n h :: Kₒ) p := by
    intro p hp; rw [← hrec]; exact hcv p hp
  have hsf' : StratFresh (Kᵢ ++ Frame.handleF n h :: Kₒ) := hrec ▸ hsf
  dsimp only at hd2
  by_cases hk : handlesOp h ℓ op = true
  · rw [if_pos hk] at hd2
    cases h with
    | throws ℓ' =>
      simp only [dispatchOn, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, rfl⟩ := hd2
      refine ⟨fun p hp => weakCoh_outer hsf' (wkV p (by simpa only [capsC] using hp)), ?_⟩
      intro p hp
      exact weakCoh_outer hsf' (wkA p (Or.inr (Or.inr hp)))
    | state ℓ' s =>
      simp only [dispatchOn] at hd2
      split at hd2 <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, rfl⟩ := hd2
          refine ⟨?_, ?_⟩
          · intro p hp; simp only [capsC] at hp
            first
            | -- get: focus `ret s`, K' = K (same value); s ∈ capsH (state ℓ' s)
              exact weakCoh_replace (h := Handler.state ℓ' s) (by rfl)
                (wkA p (Or.inr (Or.inl (by simpa only [capsH] using hp))))
            | (simp only [capsV] at hp; exact absurd hp (by simp))  -- put: focus `ret unit`
          · intro p hp
            rw [capsK_append] at hp; simp only [capsK, capsH] at hp
            rcases List.mem_append.mp hp with h' | h'
            · exact weakCoh_replace (by rfl) (wkA p (Or.inl h'))
            · rcases List.mem_append.mp h' with h'' | h''
              · first
                | exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inl (by simpa only [capsH] using h''))))  -- get: s
                | exact weakCoh_replace (h := Handler.state ℓ' s) (by rfl) (wkV p h'')  -- put: v
              · exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inr h'')))
    | transaction ℓ' Θ =>
      simp only [dispatchOn] at hd2
      (repeat' split at hd2) <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, rfl⟩ := hd2
          refine ⟨?_, ?_⟩
          · intro p hp; simp only [capsC] at hp
            first
            | (simp only [capsV] at hp; exact absurd hp (by simp))
            | (rcases capsV_getD_mem hp with h' | h'
               · exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inl (by simpa only [capsH] using h'))))
               · simp only [capsV] at h'; exact absurd h' (by simp))
          · intro p hp
            rw [capsK_append] at hp; simp only [capsK, capsH] at hp
            rcases List.mem_append.mp hp with h' | h'
            · exact weakCoh_replace (by rfl) (wkA p (Or.inl h'))
            · rcases List.mem_append.mp h' with h'' | h''
              · first
                | exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inl (by simpa only [capsH] using h''))))
                | (rw [List.flatMap_append] at h''
                   rcases List.mem_append.mp h'' with h3 | h3
                   · exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inl (by simpa only [capsH] using h3))))
                   · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h3
                     exact weakCoh_replace (by rfl) (wkV p h3))
                | (rcases capsV_set_mem h'' with h3 | h3
                   · exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inl (by simpa only [capsH] using h3))))
                   · exact weakCoh_replace (by rfl) (wkV p (by simp only [capsV, List.mem_append] at h3 ⊢; tauto)))
              · exact weakCoh_replace (by rfl) (wkA p (Or.inr (Or.inr h'')))
  · rw [if_neg hk] at hd2; exact absurd hd2 (by simp)



/-- The route-A label-coherence carrier: every cap in the focus AND every stored cap is WeakCoh `K`. -/
def CapLabelCoh : Config → Prop
  | (_, K, c) => (∀ p ∈ capsC c, WeakCoh K p) ∧ (∀ p ∈ capsK K, WeakCoh K p)

/-- **THE ROUTE-A PRESERVATION (stage a deliverable).** `CapLabelCoh` rides `Source.step`, #35-free
(grade-independent): MINT pushes a coherent fresh cap+frame (`weakCoh_mint_self`); PUSH/REDUCE are
splitAtId-transparent; DISPATCH resumes same-label (`weakCoh_replace`) or aborts to the outer stack
(`weakCoh_outer`). FreshCfg supplies the gensym freshness the transfers need. -/
theorem capLabelCoh_step (cfg cfg' : Config)
    (hf : FreshCfg cfg) (h : CapLabelCoh cfg) (hstep : Source.step cfg = some cfg') :
    CapLabelCoh cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  obtain ⟨hcc, hck⟩ := h
  obtain ⟨hcb, hfc, hsf, hckf⟩ := hf
  cases c with
  | letC M N =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    refine ⟨fun p hp => weakCoh_letF (hcc p (by simp only [capsC]; exact List.mem_append_left _ hp)), ?_⟩
    intro p hp; simp only [capsK] at hp
    rcases List.mem_append.mp hp with h' | h'
    · exact weakCoh_letF (hcc p (by simp only [capsC]; exact List.mem_append_right _ h'))
    · exact weakCoh_letF (hck p h')
  | app M w =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    refine ⟨fun p hp => weakCoh_appF (hcc p (by simp only [capsC]; exact List.mem_append_left _ hp)), ?_⟩
    intro p hp; simp only [capsK] at hp
    rcases List.mem_append.mp hp with h' | h'
    · exact weakCoh_appF (hcc p (by simp only [capsC]; exact List.mem_append_right _ h'))
    · exact weakCoh_appF (hck p h')
  | handle hh M =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases capsC_substFrom 0 (Val.vcap g hh.label) M p hp with h' | h'
      · exact weakCoh_handleF_fresh (hfc p (by simp only [capsC]; exact List.mem_append_right _ h'))
          (hcc p (by simp only [capsC]; exact List.mem_append_right _ h'))
      · simp only [capsV, List.mem_singleton] at h'; subst h'; exact weakCoh_mint_self
    · intro p hp; simp only [capsK] at hp
      rcases List.mem_append.mp hp with h' | h'
      · exact weakCoh_handleF_fresh (hfc p (by simp only [capsC]; exact List.mem_append_left _ h'))
          (hcc p (by simp only [capsC]; exact List.mem_append_left _ h'))
      · exact weakCoh_handleF_fresh (hckf p h') (hck p h')
  | force w =>
    cases w with
    | vthunk M =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      exact ⟨fun p hp => hcc p (by simp only [capsC, capsV]; exact hp), hck⟩
    | vunit | vint _ | vvar _ | vcap _ _ | inl _ | inr _ | pair _ _ | fold _ => simp [Source.step] at hstep
  | ret v =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        refine ⟨?_, fun p hp => weakCoh_letF_inv (hck p (by simp only [capsK]; exact List.mem_append_right _ hp))⟩
        intro p hp
        rcases capsC_substFrom 0 v N p hp with h' | h'
        · exact weakCoh_letF_inv (hck p (by simp only [capsK]; exact List.mem_append_left _ h'))
        · exact weakCoh_letF_inv (hcc p (by simp only [capsC]; exact h'))
      | appF w => simp [Source.step] at hstep
      | handleF g' hh =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        simp only [StratFresh] at hsf
        refine ⟨fun p hp => weakCoh_handleF_inv hsf.1 (hcc p (by simpa only [capsC] using hp)), ?_⟩
        intro p hp
        exact weakCoh_handleF_inv hsf.1 (hck p (by simp only [capsK]; exact List.mem_append_right _ hp))
  | lam M =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N => simp [Source.step] at hstep
      | handleF g' hh => simp [Source.step] at hstep
      | appF w =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        refine ⟨?_, fun p hp => weakCoh_appF_inv (hck p (by simp only [capsK]; exact List.mem_append_right _ hp))⟩
        intro p hp
        rcases capsC_substFrom 0 w M p hp with h' | h'
        · exact weakCoh_appF_inv (hcc p (by simp only [capsC]; exact h'))
        · exact weakCoh_appF_inv (hck p (by simp only [capsK]; exact List.mem_append_left _ h'))
  | case v N₁ N₂ =>
    cases v with
    | inl a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      refine ⟨?_, hck⟩
      intro p hp
      rcases capsC_substFrom 0 a N₁ p hp with h' | h'
      · exact hcc p (by simp only [capsC]; exact List.mem_append_left _ (List.mem_append_right _ h'))
      · exact hcc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_left _ h'))
    | inr a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      refine ⟨?_, hck⟩
      intro p hp
      rcases capsC_substFrom 0 a N₂ p hp with h' | h'
      · exact hcc p (by simp only [capsC]; exact List.mem_append_right _ h')
      · exact hcc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_left _ h'))
    | vunit | vint _ | vvar _ | vcap _ _ | vthunk _ | pair _ _ | fold _ => simp [Source.step] at hstep
  | split v N =>
    cases v with
    | pair a b =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      refine ⟨?_, hck⟩
      intro p hp
      rcases capsC_substFrom 0 a _ p hp with h' | h'
      · rcases capsC_substFrom 0 (Val.shift b) N p h' with h'' | h''
        · exact hcc p (by simp only [capsC]; exact List.mem_append_right _ h'')
        · rw [capsV_shiftFrom] at h''
          exact hcc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_right _ h''))
      · exact hcc p (by simp only [capsC, capsV]; exact List.mem_append_left _ (List.mem_append_left _ h'))
    | vunit | vint _ | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | fold _ => simp [Source.step] at hstep
  | unfold v =>
    cases v with
    | fold a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      exact ⟨fun p hp => hcc p (by simpa only [capsC, capsV] using hp), hck⟩
    | vunit | vint _ | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | pair _ _ => simp [Source.step] at hstep
  | perform cv op v =>
    cases cv with
    | vcap n ℓ =>
      simp only [Source.step, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨K', c'⟩, hd, rfl⟩ := hstep
      exact capCoh_idDispatch hsf hcb
        (fun p hp => hcc p (by simp only [capsC]; exact List.mem_append_right _ hp)) hck hd
    | vunit | vint _ | vvar _ | vthunk _ | inl _ | inr _ | pair _ _ | fold _ => simp [Source.step] at hstep
  | oom => simp [Source.step] at hstep
  | wrong s => simp [Source.step] at hstep



/-- A `VcapFree` closed program is `CapLabelCoh` at its initial config (both conjuncts vacuous). -/
theorem capLabelCoh_initial {c : Comp} (hvf : VcapFree c) : CapLabelCoh (0, [], c) := by
  unfold VcapFree at hvf
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [hvf] at hp; simp at hp
  · exact absurd hp (by simp [capsK])

/-- **Bridge-facing extraction.** At a `perform (vcap n ℓ)` focus, `CapLabelCoh` pins the resolved
frame's label to the cap's label — exactly the `CapResolves` ingredient `dispatch_state_get` needs. -/
theorem capLabelCoh_perform_label {g n : Nat} {ℓ : Label} {op : OpId} {v : Val} {K : EvalCtx}
    {Kᵢ Kₒ : EvalCtx} {hh : Handler}
    (h : CapLabelCoh (g, K, Comp.perform (Val.vcap n ℓ) op v))
    (hs : splitAtId K n = some (Kᵢ, hh, Kₒ)) : Handler.label hh = ℓ := by
  have hw : WeakCoh K (n, ℓ) := h.1 (n, ℓ) (by simp [capsC, capsV])
  exact hw Kᵢ hh Kₒ hs

end -- public section
end Bang.CapCoh
