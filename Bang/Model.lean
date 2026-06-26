/-
  Bang/Model.lean — the initial-config NON-ESCAPE diagonal (inc-5 Phase 3, route β).
  ───────────────────────────────────────────────────────────────────────────────
  THE SOUNDNESS PAYOFF. `NonEscape (0,[],c)` for a well-typed `VcapFree` source program,
  established as a UNARY REACHABILITY fact (route β), NOT through the binary LR (route α).

    diagonal : HasConfigTy (0,[],c) ⊥ (F q A) ∧ VcapFree c → NonEscape (0,[],c)

  This discharges the SOLE inc-4 carried obligation: `NonEscape`-PRESERVATION is already free
  (`preservation_returnEscape_TODO`, proven in Operational — NonEscape is a forward closure, so
  `StepStar.head` gives preservation by construction); the one open direction was the INITIAL config
  (`well-typed (0,[],c) → NonEscape`). This file supplies it.

  ARCHITECTURE (`nonEscape_of_fwd_invariant`, GREEN): ANY step-preserved invariant `P` with
  `P ⇒ FocusResolves` gives `NonEscape` by reachability induction. The concrete `P` is the COMBINED
  invariant `WellScoped ∧ HasConfigTy`: `WellScoped` (every `vcap` resolves) gives the cap-resolution
  half of `FocusResolves`; `HasConfigTy` (the focus types at `⊥`) gives the op-in-interface half AND
  the ⊥-row discipline that closes `WellScoped`'s pop-escape preservation arm. The two ride together.

  STATE (◊inc-5 Phase 3, STOP-and-SHOW): the route-β SKELETON is transcribed + GREEN
  (`nonEscape_of_fwd_invariant`, `wellScoped_initial`, `focusResolves_of_wellScoped`), and the diagonal
  is ASSEMBLED — reduced to exactly the two named obligations below:
    · `handlesOp_of_hasConfigTy` — the op-in-interface typing inversion (`hpos`'s residual).
    · `wsCfg_step` — the MUTUAL `WellScoped ∧ HasConfigTy` preservation. Its pop-escape arm is the ⊥-row
      return-escape research crux (a value returned past `handleF n` at `⊥` cannot expose a performable
      `Cap ℓ` for the popped `ℓ`); its dispatch arm re-types the resume via `WellScoped`'s resolution.

  Transcribed from `scratch/DiagonalProbe.lean §B` (route β de-risked there). Standalone (not yet wired
  into `Bang.lean`/`Audit` — those depend on the still-red `Compat`/`Spec`; wire once the diagonal closes).
-/
import Bang.Metatheory

namespace Bang.Model
open Bang
open Bang.EffectRow (Label)

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]

/-! ## §1 — the route-β architecture result (GREEN). -/

/-- ★ ANY step-preserved invariant `P` that implies `FocusResolves` at every config gives `NonEscape`
by reachability induction over `StepStar`. The diagonal lives in the UNARY reachability world (route β),
NOT the relational LR (route α). `wellCounted_reachable`'s shape (Operational). -/
theorem nonEscape_of_fwd_invariant (P : Config → Prop)
    (hpos  : ∀ cfg, P cfg → FocusResolves cfg)
    (hpres : ∀ cfg cfg', P cfg → Source.step cfg = some cfg' → P cfg')
    (cfg : Config) (hP : P cfg) : NonEscape cfg := by
  have hreach : ∀ cfg', StepStar cfg cfg' → P cfg' := by
    intro cfg' h
    induction h with
    | refl => exact hP
    | tail _ hstep ih => exact hpres _ _ ih hstep
  exact fun cfg' hr => hpos _ (hreach cfg' hr)

/-! ## §2 — the concrete invariant `WellScoped`: every `vcap` resolves. -/

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
  | _             => []
def capsH : Handler → List (Nat × Label)
  | .state _ s  => capsV s
  | .throws _   => []
  | .transaction _ Θ => Θ.flatMap capsV
end

def capsK : EvalCtx → List (Nat × Label)
  | []                  => []
  | .letF N :: K        => capsC N ++ capsK K
  | .appF v :: K        => capsV v ++ capsK K
  | .handleF _ h :: K   => capsH h ++ capsK K

/-- the cap `(n,ℓ)` lands on a same-LABEL handler frame on `K` (the op-in-interface check is the
secondary typing dependency, `handlesOp_of_hasConfigTy`). -/
def ResolvesLabel (K : EvalCtx) (n : Nat) (ℓ : Label) : Prop :=
  ∃ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) ∧ Handler.label h = ℓ

/-! ### §2.5 — the TYPED-RELATIVE invariant (ADR-0057, deep-modulo-non-performability).

The naive config-function `WellScoped` (every `vcap`, tracked DEEP through thunks, resolves) is NOT
preserved by `Source.step`: the `handleF`-pop's carry-drop breaks it (a cap of the popped handler can
sit dormant inside a returned thunk). The reshape (de-risked in `scratch/WellScopedReshapeProbe.lean`):
track caps DEEP but require resolution only for caps PERFORMABLE at their position — a cap whose label is
in the row of its nearest-enclosing thunk/focus. A cap under a thunk `U φ B` with label `ℓ ∉ φ` is
inert (the thunk can never perform it without being ill-typed), so it is NOT required to resolve. At a
pop with answer type `A` and `¬LabelOccurs ℓ_f A` (the ADR-0057 B-occ premise), every `ℓ_f`-cap under a
thunk of `A` has its thunk-row exclude `ℓ_f` (since `U φ B ⊆ A` ⇒ `¬(labelEff ℓ_f ≤ φ)`) — non-performable
⇒ not required ⇒ the carry-drop dissolves.

"Performable at position" needs the thunk's row `φ`, which lives in the TYPE `U φ C`, NOT the `vthunk c`
TERM — so the invariant CANNOT be a pure syntactic config-function. It is a TYPED PREDICATE, indexed by
the `HasVTy`/`HasCTy`/`HasStack` derivation, threading an ambient performability row `ρ` (the row of the
nearest enclosing thunk/focus). `WSV`/`WSC` are mutual inductives mirroring the typing rules; the gate
fires only at `vcap` leaves whose label is `≤ ρ`. Resolution is always against the FULL current stack
`K` (`splitAtId` is stable under pushing fresh frames on top, so a cap that resolves in a stack tail
resolves in the whole stack). -/

mutual
/-- `WSV K ρ v A`: every cap in the value `v : A` performable at ambient row `ρ` resolves in `K`.
Indexed by the TERM + TYPE (NOT the `HasVTy` derivation) — keeps it structurally invertible (a
derivation-indexed version is blocked by the non-structural GRADE index: `cases` cannot solve
`[] = (q•γv)+γc`). Crossing a thunk `U φ B` RESETS the ambient to the thunk's own row `φ`. -/
inductive WSV (K : EvalCtx) : Eff → Val → VTy Eff Mult → Prop where
  | vunit {ρ} : WSV K ρ Val.vunit VTy.unit
  | vint {ρ n} : WSV K ρ (Val.vint n) VTy.int
  | vvar {ρ i A} : WSV K ρ (Val.vvar i) A
  -- THE GATE: a bare cap value resolves iff its label is performable at the ambient row.
  | vcap {ρ n ℓ} (h : EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ ρ → ResolvesLabel K n ℓ) :
      WSV K ρ (Val.vcap n ℓ) (VTy.cap ℓ)
  -- THE RESET: inside a thunk `U φ B`, the ambient becomes the thunk's own row `φ`.
  | vthunk {ρ c φ B} (h : WSC K φ c φ B) : WSV K ρ (Val.vthunk c) (VTy.U φ B)
  | inl {ρ v A B} (h : WSV K ρ v A) : WSV K ρ (Val.inl v) (VTy.sum A B)
  | inr {ρ v A B} (h : WSV K ρ v B) : WSV K ρ (Val.inr v) (VTy.sum A B)
  | pair {ρ a b A B} (h1 : WSV K ρ a A) (h2 : WSV K ρ b B) : WSV K ρ (Val.pair a b) (VTy.prod A B)
  | fold {ρ v A} (h : WSV K ρ v (VTy.unrollMu A)) : WSV K ρ (Val.fold v) (VTy.mu A)
/-- `WSC K ρ c φ C`: every performable cap in the computation `c : (φ, C)` resolves. Ambient `ρ` is
threaded UNCHANGED through every former (the gate is purely at thunk boundaries / `vcap` leaves) — a
sub-computation of lower literal row (`ret v : ⊥`) still flows its caps to a consumer at the enclosing
row. The non-cap typing premises (`labelEff ℓ ≤ φ`, `opArg`, …) are NOT carried — they live in the
companion `HasCTy`; `WSC` carries only the cap-resolution obligations. -/
inductive WSC (K : EvalCtx) : Eff → Comp → Eff → CTy Eff Mult → Prop where
  | ret {ρ v A q} (h : WSV K ρ v A) : WSC K ρ (Comp.ret v) ⊥ (CTy.F q A)
  | letC {ρ M N φ₁ φ₂ q1 A B} (h1 : WSC K ρ M φ₁ (CTy.F q1 A)) (h2 : WSC K ρ N φ₂ B) :
      WSC K ρ (Comp.letC M N) (φ₁ ⊔ φ₂) B
  | force {ρ v φ B} (h : WSV K ρ v (VTy.U φ B)) : WSC K ρ (Comp.force v) φ B
  | lam {ρ M φ q A B} (h : WSC K ρ M φ B) : WSC K ρ (Comp.lam M) φ (CTy.arr q A B)
  | app {ρ M v φ q A B} (h1 : WSC K ρ M φ (CTy.arr q A B)) (h2 : WSV K ρ v A) :
      WSC K ρ (Comp.app M v) φ B
  | case {ρ v N₁ N₂ φ A B C} (h1 : WSV K ρ v (VTy.sum A B)) (h2 : WSC K ρ N₁ φ C) (h3 : WSC K ρ N₂ φ C) :
      WSC K ρ (Comp.case v N₁ N₂) φ C
  | split {ρ v N φ A B C} (h1 : WSV K ρ v (VTy.prod A B)) (h2 : WSC K ρ N φ C) :
      WSC K ρ (Comp.split v N) φ C
  | unfold {ρ v A} (h : WSV K ρ v (VTy.mu A)) : WSC K ρ (Comp.unfold v) ⊥ (CTy.F 1 (VTy.unrollMu A))
  | perform {ρ cv op v φ q A B ℓ} (h1 : WSV K ρ cv (VTy.cap ℓ)) (h2 : WSV K ρ v A) :
      WSC K ρ (Comp.perform cv op v) φ (CTy.F q B)
  | handleThrows {ρ ℓ M e φ q A} (h : WSC K ρ M e (CTy.F q A)) :
      WSC K ρ (Comp.handle (Handler.throws ℓ) M) φ (CTy.F q A)
  | handleState {ρ ℓ s M e φ q S A} (h1 : WSV K ρ s S) (h2 : WSC K ρ M e (CTy.F q A)) :
      WSC K ρ (Comp.handle (Handler.state ℓ s) M) φ (CTy.F q A)
  | handleTransaction {ρ ℓ Θ M e φ q A} (h : WSC K ρ M e (CTy.F q A)) :
      WSC K ρ (Comp.handle (Handler.transaction ℓ Θ) M) φ (CTy.F q A)
/-- `WSK Kfull K e C eo Co`: every performable cap stored in the stack frames of `K` resolves in `Kfull`
(the full ambient stack). Indexed by the stack TERM + the `HasStack` effect/type chain. Each frame's
stored term is gated at its hole-effect (the row it runs at when that frame becomes focus). `throws`/
`transaction` frames carry no cap-bearing value (the heap is `int`). In the same `mutual` block as
`WSV`/`WSC` so the `Mult` instance context is shared (a standalone `inductive` leaves `EffSig Eff ?Mult`
stuck). -/
inductive WSK (K : EvalCtx) : EvalCtx → Eff → CTy Eff Mult → Eff → CTy Eff Mult → Prop where
  | nil {e C} : WSK K [] e C e C
  | letF {Sg N e₁ e₂ eo q A B Co} (hN : WSC K e₂ N e₂ B) (hK : WSK K Sg (e₁ ⊔ e₂) B eo Co) :
      WSK K (Frame.letF N :: Sg) e₁ (CTy.F q A) eo Co
  | appF {Sg v e eo q A B Co} (hv : WSV K e v A) (hK : WSK K Sg e B eo Co) :
      WSK K (Frame.appF v :: Sg) e (CTy.arr q A B) eo Co
  | handleF {Sg n ℓ e φ eo q A Co} (hK : WSK K Sg φ (CTy.F q A) eo Co) :
      WSK K (Frame.handleF n (Handler.throws ℓ) :: Sg) e (CTy.F q A) eo Co
  | stateF {Sg n ℓ s e φ eo q A S Co} (hs : WSV K e s S) (hK : WSK K Sg φ (CTy.F q A) eo Co) :
      WSK K (Frame.handleF n (Handler.state ℓ s) :: Sg) e (CTy.F q A) eo Co
  | transactionF {Sg n ℓ Θ e φ eo q A Co} (hK : WSK K Sg φ (CTy.F q A) eo Co) :
      WSK K (Frame.handleF n (Handler.transaction ℓ Θ) :: Sg) e (CTy.F q A) eo Co
end


/-- A source program is `VcapFree` when it contains NO raw `vcap` literal — the elaborator invariant
(`vcap`s arise only by minting). The diagonal's side-condition (the bare form is FALSE: a hand-written
`vcap 5` types but runs stuck — DiagonalProbe §B). -/
def VcapFree (c : Comp) : Prop := capsC c = []

-- cap-free ⇒ `WSV`/`WSC` hold (no `vcap` leaf imposes a gate). Built by recursion on the typing
-- derivation, mapping each typing rule to its `WSV`/`WSC` constructor; cap-freeness kills the `vcap` leaf.
mutual
/-- A cap-free value is `WSV` at any ambient row (no `vcap` to impose a gate). -/
theorem wsv_capFree {γ Γ v A} (K : EvalCtx) (ρ : Eff)
    (d : HasVTy (Eff := Eff) (Mult := Mult) γ Γ v A) (h : capsV v = []) : WSV K ρ v A := by
  cases d with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar _ => exact .vvar
  | vcap => simp only [capsV] at h; exact absurd h (List.cons_ne_nil _ _)
  | vthunk hM => exact .vthunk (wsc_capFree K _ hM (by simpa only [capsV] using h))
  | inl hv => exact .inl (wsv_capFree K ρ hv (by simpa only [capsV] using h))
  | inr hv => exact .inr (wsv_capFree K ρ hv (by simpa only [capsV] using h))
  | pair hv hw _ =>
      simp only [capsV, List.append_eq_nil_iff] at h
      exact .pair (wsv_capFree K ρ hv h.1) (wsv_capFree K ρ hw h.2)
  | fold hv => exact .fold (wsv_capFree K ρ hv (by simpa only [capsV] using h))
/-- A cap-free computation is `WSC` at any ambient row. -/
theorem wsc_capFree {γ Γ c φ C} (K : EvalCtx) (ρ : Eff)
    (d : HasCTy (Eff := Eff) (Mult := Mult) γ Γ c φ C) (h : capsC c = []) : WSC K ρ c φ C := by
  cases d with
  | ret hv _ => exact .ret (wsv_capFree K ρ hv (by simpa only [capsC] using h))
  | letC hM hN _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .letC (wsc_capFree K ρ hM h.1) (wsc_capFree K ρ hN h.2)
  | force hv => exact .force (wsv_capFree K ρ hv (by simpa only [capsC] using h))
  | lam hM => exact .lam (wsc_capFree K ρ hM (by simpa only [capsC] using h))
  | app hM hv _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .app (wsc_capFree K ρ hM h.1) (wsv_capFree K ρ hv h.2)
  | case hv hN₁ hN₂ _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .case (wsv_capFree K ρ hv h.1.1) (wsc_capFree K ρ hN₁ h.1.2) (wsc_capFree K ρ hN₂ h.2)
  | split hv hN _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .split (wsv_capFree K ρ hv h.1) (wsc_capFree K ρ hN h.2)
  | unfold hv => exact .unfold (wsv_capFree K ρ hv (by simpa only [capsC] using h))
  | perform hc _ _ _ hv =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .perform (wsv_capFree K ρ hc h.1) (wsv_capFree K ρ hv h.2)
  | handleThrows _ _ hM _ _ =>
      simp only [capsC, capsH, List.nil_append] at h
      exact .handleThrows (wsc_capFree K ρ hM h)
  | handleState _ _ _ _ _ hs hM _ _ =>
      simp only [capsC, capsH, List.append_eq_nil_iff] at h
      exact .handleState (wsv_capFree K ρ hs h.1) (wsc_capFree K ρ hM h.2)
  | handleTransaction _ _ _ _ _ _ _ _ hM _ _ =>
      simp only [capsC, capsH, List.append_eq_nil_iff] at h
      exact .handleTransaction (wsc_capFree K ρ hM h.2)
end

/-! ## §3 — the combined invariant + the two named obligations. -/

/-- The COMBINED route-β invariant (ADR-0057 typed-relative reshape): there EXIST typing derivations for
the focus + stack such that every PERFORMABLE cap resolves (`WSC` for the focus at its row `e`; `WSK` for
the stack against the full `K`). Bundling the derivations existentially keeps `WScfg : Config → Prop`
(the shape `nonEscape_of_fwd_invariant` consumes); the output effect is `⊥` (the diagonal's target). -/
def WScfg (Co : CTy Eff Mult) (cfg : Config) : Prop :=
  ∃ (e : Eff) (C : CTy Eff Mult), HasCTy [] [] cfg.2.2 e C ∧ HasStack cfg.2.1 e C ⊥ Co
    ∧ WSC cfg.2.1 e cfg.2.2 e C ∧ WSK cfg.2.1 cfg.2.1 e C ⊥ Co

/-- **SEED (GREEN).** A `VcapFree` closed program satisfies the typed-relative invariant at the initial
config — no caps to resolve, the stack is empty. The typing derivations come from `hty`. -/
theorem wellScoped_initial (c : Comp) (hvf : VcapFree c) {Co : CTy Eff Mult}
    (hty : HasConfigTy (0, [], c) ⊥ Co) : WScfg Co (0, [], c) := by
  obtain ⟨e, C, hfocus, hstack⟩ := hty
  -- the stack is `[]`, so `hstack : HasStack [] e C ⊥ Co` must be `nil` (`e = ⊥`, `C = Co`).
  cases hstack
  exact ⟨⊥, Co, hfocus, .nil, wsc_capFree [] ⊥ hfocus hvf, .nil⟩

/-- **OBLIGATION 1 — the op-in-interface typing inversion.** A `WellScoped`-resolved `perform (vcap n ℓ)
op v` focus that types (`HasConfigTy … ⊥ …`) lands on a handler that HANDLES `(ℓ, op)`: `HasCTy.perform`
puts `op` in `ℓ`'s interface (`opArg`/`opRes` some), and the cap's `Cap ℓ` type pins the resolved
ℓ-handler's interface to `ℓ`'s ops. NAMED SORRY: a typing-inversion lemma (`HasCTy` of the focus +
`HasStack` of the resolved frame). -/
theorem handlesOp_of_hasConfigTy {Co : CTy Eff Mult} (cfg : Config)
    (hty : HasConfigTy cfg ⊥ Co) :
    ∀ K n ℓ op v, cfg = (cfg.1, K, Comp.perform (Val.vcap n ℓ) op v) →
      ∀ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) → Handler.label h = ℓ →
      handlesOp h ℓ op = true := by
  intro K n ℓ op v hcfg Kᵢ h Kₒ hsplit hlbl
  obtain ⟨e, C, hfocus, hstack⟩ := hty
  -- project the focus + stack out of the assumed config shape.
  have hK : cfg.2.1 = K := by rw [hcfg]
  have hc : cfg.2.2 = Comp.perform (Val.vcap n ℓ) op v := by rw [hcfg]
  rw [hK] at hstack; rw [hc] at hfocus
  -- the perform's interface: `op ∈ ℓ`'s ops (`opArg ℓ op = some A`); the cap's `Cap ℓ'` pins `ℓ' = ℓ`.
  obtain ⟨ℓ', γ_c, γ_v, q, A, B, hC, hγ, hcap, hle, hopArg, hopRes, hwv⟩ := hfocus.perform_full_inv
  obtain ⟨m, hceq⟩ := hcap.cap_canonical
  simp only [Val.vcap.injEq] at hceq; obtain ⟨_, rfl⟩ := hceq
  -- the resolved handler `h` (id `n`) is the typed split-point frame; its interface forces `handlesOp`.
  have hdecomp : K = Kᵢ ++ Frame.handleF n h :: Kₒ := splitAtId_decomp K n hsplit
  rw [hdecomp] at hstack
  exact HasStack.handlesOp_of_split hstack hlbl hopArg

/-- `WScfg` carries the typing core: project out `HasConfigTy` (drop the `WSC`/`WSK` cap-resolution). -/
theorem hasConfigTy_of_wscfg {Co : CTy Eff Mult} (cfg : Config) (h : WScfg Co cfg) :
    HasConfigTy cfg ⊥ Co := by
  obtain ⟨e, C, dc, dk, _, _⟩ := h; exact ⟨e, C, dc, dk⟩

/-- A `perform (vcap n ℓ)` focus whose `WSC` holds at the focus row `e` resolves its cap's label: the
typing gives `labelEff ℓ ≤ e` (performability), and `WSC`'s `vcap` gate then forces `ResolvesLabel`. -/
theorem resolvesLabel_of_wsc_perform {K : EvalCtx} {e : Eff}
    {n : Nat} {ℓ : Label} {op : OpId} {v : Val} {C : CTy Eff Mult}
    (dc : HasCTy [] [] (Comp.perform (Val.vcap n ℓ) op v) e C)
    (hWSC : WSC K e (Comp.perform (Val.vcap n ℓ) op v) e C) : ResolvesLabel K n ℓ := by
  -- the typing supplies `labelEff ℓ ≤ e` (performability of the focus cap); `WSC`'s `vcap` gate then fires.
  obtain ⟨ℓ', _, _, _, _, _, _, _, hcap, hle, _, _, _⟩ := dc.perform_full_inv
  obtain ⟨m, hceq⟩ := hcap.cap_canonical
  simp only [Val.vcap.injEq] at hceq; obtain ⟨_, rfl⟩ := hceq
  -- invert `WSC` at the perform (term-indexed ⇒ structural); only the `vcap` WSV constructor matches.
  cases hWSC with
  | perform h1 _ => cases h1 with | vcap hgate => exact hgate hle

/-- **POSITIVE (GREEN).** The typed-relative invariant `⇒ FocusResolves`: the cap-resolution comes from
`WSC`'s `vcap` gate (`resolvesLabel_of_wsc_perform`); the op-membership from the typing core (`handlesOp_of_hasConfigTy`). -/
theorem focusResolves_of_wscfg {Co : CTy Eff Mult} (cfg : Config) (hWS : WScfg Co cfg) :
    FocusResolves cfg := by
  obtain ⟨e, C, dc, dk, hWSC, _⟩ := hWS
  obtain ⟨g, K, c⟩ := cfg
  -- now `dc : HasCTy [] [] c e C`, `hWSC : WSC K e dc`; split STRUCTURALLY on the focus `c` (refines
  -- `dc`/`hWSC` without the closed-grade elimination wall).
  cases c with
  | perform cv op v =>
      cases cv with
      | vcap n ℓ =>
          obtain ⟨Kᵢ, h, Kₒ, hsplit, hlbl⟩ := resolvesLabel_of_wsc_perform dc hWSC
          exact ⟨Kᵢ, h, Kₒ, hsplit,
            handlesOp_of_hasConfigTy (g, K, _) ⟨e, C, dc, dk⟩ K n ℓ op v rfl Kᵢ h Kₒ hsplit hlbl⟩
      | vunit | vint | vvar _ | vthunk _ | inl _ | inr _ | pair _ _ | fold _ => trivial
  | ret _ | letC _ _ | force _ | lam _ | app _ _ | handle _ _ | case _ _ _ | split _ _
  | unfold _ | oom | wrong _ => trivial

/-! ### §3.5 — restack lemmas (the shared mechanics of the preservation arms).

`splitAtId` is stable under pushing a frame on top, provided that frame is not a `handleF` capturing the
very identity being resolved (`splitAtId` walks past a non-matching head). So a cap that resolves in `K`
still resolves in `fr :: K`, and `WSV`/`WSC`/`WSK` re-home wholesale. -/

/-- A cap that resolves in `K` resolves in `fr :: K` when `fr` is not the `handleF` for that identity. -/
theorem resolvesLabel_cons (fr : Frame) {K : EvalCtx} {n : Nat} {ℓ : Label}
    (hfr : ∀ m h, fr = Frame.handleF m h → m ≠ n) (h : ResolvesLabel K n ℓ) :
    ResolvesLabel (fr :: K) n ℓ := by
  obtain ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩ := h
  refine ⟨fr :: Kᵢ, hh, Kₒ, ?_, hlbl⟩
  cases fr with
  | letF N => simp only [splitAtId, hsplit, Option.map_some]
  | appF w => simp only [splitAtId, hsplit, Option.map_some]
  | handleF m hd =>
      have hmn : ¬ (m = n) := hfr m hd rfl
      simp only [splitAtId, hmn, if_false, hsplit, Option.map_some]

-- `WSV`/`WSC` re-home under a pushed NON-`handleF` frame (every gate's `ResolvesLabel` survives). The
-- `letF`/`appF` PUSH/REDUCE frames; the `handleF` MINT push needs the freshness-keyed variant separately.
mutual
/-- `WSV` re-homes under a pushed non-`handleF` frame. -/
theorem wsv_restack {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h)
    {ρ : Eff} {v : Val} {A : VTy Eff Mult} (h : WSV K ρ v A) : WSV (fr :: K) ρ v A := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap hg => exact .vcap fun hle => resolvesLabel_cons fr (fun m hd he => absurd he (hfr m hd)) (hg hle)
  | vthunk hM => exact .vthunk (wsc_restack fr hfr hM)
  | inl hv => exact .inl (wsv_restack fr hfr hv)
  | inr hv => exact .inr (wsv_restack fr hfr hv)
  | pair h1 h2 => exact .pair (wsv_restack fr hfr h1) (wsv_restack fr hfr h2)
  | fold hv => exact .fold (wsv_restack fr hfr hv)
/-- `WSC` re-homes under a pushed non-`handleF` frame. -/
theorem wsc_restack {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h)
    {ρ : Eff} {c : Comp} {φ : Eff} {C : CTy Eff Mult} (h : WSC K ρ c φ C) : WSC (fr :: K) ρ c φ C := by
  cases h with
  | ret hv => exact .ret (wsv_restack fr hfr hv)
  | letC h1 h2 => exact .letC (wsc_restack fr hfr h1) (wsc_restack fr hfr h2)
  | force hv => exact .force (wsv_restack fr hfr hv)
  | lam hM => exact .lam (wsc_restack fr hfr hM)
  | app h1 h2 => exact .app (wsc_restack fr hfr h1) (wsv_restack fr hfr h2)
  | case h1 h2 h3 => exact .case (wsv_restack fr hfr h1) (wsc_restack fr hfr h2) (wsc_restack fr hfr h3)
  | split h1 h2 => exact .split (wsv_restack fr hfr h1) (wsc_restack fr hfr h2)
  | unfold hv => exact .unfold (wsv_restack fr hfr hv)
  | perform h1 h2 => exact .perform (wsv_restack fr hfr h1) (wsv_restack fr hfr h2)
  | handleThrows hM => exact .handleThrows (wsc_restack fr hfr hM)
  | handleState h1 h2 => exact .handleState (wsv_restack fr hfr h1) (wsc_restack fr hfr h2)
  | handleTransaction hM => exact .handleTransaction (wsc_restack fr hfr hM)
end

/-- **OBLIGATION 2 — the MUTUAL preservation (the research crux, multi-session).** `WScfg` is preserved
by every `Source.step`. `WScfg` = `HasCTy ∧ HasStack ∧ WSC ∧ WSK`: the TYPING half (`HasCTy`/`HasStack`)
rides EXISTING preservation (`preservation_proof`, Metatheory — NonEscape-free); the NEW content is the
`WSC`/`WSK` cap-resolution half, now invertible/buildable since they are TERM+TYPE indexed.

SUPPORTING LEMMAS the arms need (NOT yet proven — the next units):
  · `ResolvesLabel`-push: `ResolvesLabel K n ℓ → ResolvesLabel (fr :: K) n ℓ` for `fr` a fresh frame
    (`fr`'s id ≠ n, by `WellCounted`/global-fresh `g`). `splitAtId` walks past a non-matching head.
  · `WSV`/`WSC`-restack: under the same push, `WSV K ρ v A → WSV (fr :: K) ρ v A` (every gate's
    `ResolvesLabel` survives the push). Mutual on `WSV`/`WSC`.
  · the B-occ lever (PROBE `scratch/WellScopedReshapeProbe.lean::surfaceCaps_labelOccurs`, promote it):
    a surface `vcap _ ℓ` in `v : A` forces `LabelOccurs ℓ A` — feeds the POP arm + the μ-corner lemma
    `labelOccurs (unrollMu A) → labelOccurs A` (the one seam left in the probe).

THE ARMS (`Source.step`, Operational:455):
  • PUSH (`letC M N ↦ letF N::K, M`, etc.): focus `WSC` splits (the letC `WSC` gives `WSC` of `M`); the
    continuation `N` moves into a new `letF` frame ⇒ rebuild `WSK` with `WSK.letF`. The new frame is
    fresh ⇒ `ResolvesLabel`-push re-homes the OLD caps. Mechanical given the supporting lemmas.
  • REDUCE (`letF N::K, ret v ↦ K, subst v N`, β, etc.): the returned `v`'s `WSV` + the frame's stored
    `WSC`(`N`) combine into the reduct's `WSC` THROUGH `subst` — needs a `WSC`-substitution lemma
    (`WSV K ρ v A → WSC K ρ N … → WSC K ρ (subst v N) …`). The cap-substitution analogue of `subst_value`.
  • MINT (`handle h M ↦ (g+1, handleF g h::K, subst (vcap g ℓ) M)`): the NEW `vcap g` resolves to the
    just-pushed `handleF g` (`splitAtId (handleF g h::K) g = some([],h,K)`, label by construction) ⇒
    `WSV`'s `vcap` gate holds; old caps survive `ResolvesLabel`-push. The handle-body `WSC` re-keys via
    the cap-subst lemma at the new ambient `e` (the body row).
  • DISPATCH (`perform (vcap n ℓ) ↦ idDispatch`): the resume/abort reduct's `WSC` is rebuilt from the
    resolved handler's stored `WSC`/`WSV` (in `WSK`) + the returned value. Uses `WSC` (the cap resolves)
    — why the invariants ride together.
  • POP (`handleF g::K, ret v ↦ K, ret v`): THE crux. After the pop a cap `(g,ℓ_f)` in `v` no longer
    resolves. CLOSED by deep-modulo-non-performability: `v : A` with `¬LabelOccurs ℓ_f A` (the ADR-0057
    B-occ premise on the popped handler's answer type) ⇒ every `ℓ_f`-cap in `v` is under a thunk whose
    row excludes `ℓ_f` (non-performable) ⇒ its `WSV` gate `labelEff ℓ_f ≤ ρ → …` is vacuous at the
    reduced stack. The B-occ lever + a `WSV`-restack-modulo-popped-label lemma.
NAMED SORRY: the mutual `WSC`/`WSK` preservation across all arms (the typing half is `preservation_proof`).
The POP arm is the ⊥-row return-escape crux; the design (deep-modulo-non-performability) is de-risked. -/
theorem wsCfg_step {Co : CTy Eff Mult} (cfg cfg' : Config)
    (hP : WScfg Co cfg) (hstep : Source.step cfg = some cfg') : WScfg Co cfg' := by
  sorry

/-! ## §4 — THE DIAGONAL (assembled). -/

/-- ★ **THE NON-ESCAPE DIAGONAL** (inc-5 Phase 3). A well-typed `VcapFree` source program is
`NonEscape` at its initial config — the SOLE inc-4 carried obligation, discharged via route β
(`WellScoped ∧ HasConfigTy` reachability), NOT the binary LR. Reduces to `handlesOp_of_hasConfigTy`
(op-in-interface) + `wsCfg_step` (the mutual preservation, pop-escape = ⊥-row return-escape crux). -/
theorem diagonal {c : Comp} {q : Mult} {A : VTy Eff Mult}
    (hty : HasConfigTy (0, [], c) ⊥ (CTy.F q A)) (hvf : VcapFree c) :
    NonEscape (0, [], c) := by
  refine nonEscape_of_fwd_invariant (WScfg (CTy.F q A)) ?_ ?_ (0, [], c)
    (wellScoped_initial c hvf hty)
  · -- hpos: WScfg ⇒ FocusResolves (cap-resolution from WSC, op-membership from HasConfigTy).
    exact fun cfg hWS => focusResolves_of_wscfg cfg hWS
  · -- hpres: the mutual preservation.
    rintro cfg cfg' hP hstep
    exact wsCfg_step cfg cfg' hP hstep

end Bang.Model
