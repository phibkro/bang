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
  -- ADR-0060 ratified grade-rig commitment (only the dormant-arm discharge consumes these; QTT/ℕ qualify,
  -- rings fail ZeroSumFree). `[NoZeroDivisors]` for the `•`-scale split; `[Nontrivial]` (`1 ≠ 0`) for q_or_1.
  [NoZeroDivisors Mult] [Nontrivial Mult]

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

/-! ### §2.4 — the μ corner: `labelOccurs` survives `unrollMu` (the POP arm's B-occ μ case).

`tyShiftFrom`/`tySubstFrom` touch only `tvar`s — they leave cap-labels and effect rows fixed — so a
label occurring in the unrolled type `A[μX.A/X]` already occurs in `μX.A` (= occurs in `A`). The B-occ
premise `¬LabelOccurs ℓ A` then propagates through `unfold`/`fold`. -/

-- A label in a shifted type occurs in the original (shift only renumbers `tvar`s).
mutual
/-- value-type half of `labelOccurs`-`tyShiftFrom` invariance. -/
theorem vty_labelOccurs_tyShiftFrom (ℓ : Label) :
    ∀ (c : Nat) (T : VTy Eff Mult), VTy.labelOccurs ℓ (VTy.tyShiftFrom c T) → VTy.labelOccurs ℓ T
  | _, .unit, h => h
  | _, .int, h => h
  | _, .cap _, h => h
  | c, .U φ B, h => by
      simp only [VTy.tyShiftFrom, VTy.labelOccurs] at h ⊢
      exact h.imp id (cty_labelOccurs_tyShiftFrom ℓ c B)
  | c, .sum A B, h => by
      simp only [VTy.tyShiftFrom, VTy.labelOccurs] at h ⊢
      exact h.imp (vty_labelOccurs_tyShiftFrom ℓ c A) (vty_labelOccurs_tyShiftFrom ℓ c B)
  | c, .prod A B, h => by
      simp only [VTy.tyShiftFrom, VTy.labelOccurs] at h ⊢
      exact h.imp (vty_labelOccurs_tyShiftFrom ℓ c A) (vty_labelOccurs_tyShiftFrom ℓ c B)
  | c, .mu A, h => by
      simp only [VTy.tyShiftFrom, VTy.labelOccurs] at h ⊢
      exact vty_labelOccurs_tyShiftFrom ℓ (c + 1) A h
  | c, .tvar i, h => by
      simp only [VTy.tyShiftFrom] at h; split at h <;> simp only [VTy.labelOccurs] at h
theorem cty_labelOccurs_tyShiftFrom (ℓ : Label) :
    ∀ (c : Nat) (T : CTy Eff Mult), CTy.labelOccurs ℓ (CTy.tyShiftFrom c T) → CTy.labelOccurs ℓ T
  | c, .F _ A, h => by
      simp only [CTy.tyShiftFrom, CTy.labelOccurs] at h ⊢
      exact vty_labelOccurs_tyShiftFrom ℓ c A h
  | c, .arr _ A B, h => by
      simp only [CTy.tyShiftFrom, CTy.labelOccurs] at h ⊢
      exact h.imp (vty_labelOccurs_tyShiftFrom ℓ c A) (cty_labelOccurs_tyShiftFrom ℓ c B)
end

-- A label in `B[T/k]` occurs in `B` OR in the substituted `T` (subst touches only `tvar`s).
mutual
/-- value-type half of `labelOccurs`-`tySubstFrom`. -/
theorem vty_labelOccurs_tySubstFrom (ℓ : Label) :
    ∀ (k : Nat) (T : VTy Eff Mult) (B : VTy Eff Mult),
      VTy.labelOccurs ℓ (VTy.tySubstFrom k T B) → VTy.labelOccurs ℓ B ∨ VTy.labelOccurs ℓ T
  | _, _, .unit, h => Or.inl h
  | _, _, .int, h => Or.inl h
  | _, _, .cap _, h => Or.inl h
  | k, T, .U φ B, h => by
      simp only [VTy.tySubstFrom, VTy.labelOccurs] at h ⊢
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact (cty_labelOccurs_tySubstFrom ℓ k T B h).imp Or.inr id
  | k, T, .sum A B, h => by
      simp only [VTy.tySubstFrom, VTy.labelOccurs] at h ⊢
      rcases h with h | h
      · exact (vty_labelOccurs_tySubstFrom ℓ k T A h).imp Or.inl id
      · exact (vty_labelOccurs_tySubstFrom ℓ k T B h).imp Or.inr id
  | k, T, .prod A B, h => by
      simp only [VTy.tySubstFrom, VTy.labelOccurs] at h ⊢
      rcases h with h | h
      · exact (vty_labelOccurs_tySubstFrom ℓ k T A h).imp Or.inl id
      · exact (vty_labelOccurs_tySubstFrom ℓ k T B h).imp Or.inr id
  | k, T, .mu A, h => by
      simp only [VTy.tySubstFrom, VTy.labelOccurs] at h ⊢
      rcases vty_labelOccurs_tySubstFrom ℓ (k + 1) (VTy.tyShiftFrom 0 T) A h with h | h
      · exact Or.inl h
      · exact Or.inr (vty_labelOccurs_tyShiftFrom ℓ 0 T h)
  | k, T, .tvar i, h => by
      simp only [VTy.tySubstFrom] at h
      split at h
      · exact Or.inr h
      · split at h <;> simp only [VTy.labelOccurs] at h
theorem cty_labelOccurs_tySubstFrom (ℓ : Label) :
    ∀ (k : Nat) (T : VTy Eff Mult) (B : CTy Eff Mult),
      CTy.labelOccurs ℓ (CTy.tySubstFrom k T B) → CTy.labelOccurs ℓ B ∨ VTy.labelOccurs ℓ T
  | k, T, .F _ A, h => by
      simp only [CTy.tySubstFrom, CTy.labelOccurs] at h ⊢
      exact vty_labelOccurs_tySubstFrom ℓ k T A h
  | k, T, .arr _ A B, h => by
      simp only [CTy.tySubstFrom, CTy.labelOccurs] at h ⊢
      rcases h with h | h
      · exact (vty_labelOccurs_tySubstFrom ℓ k T A h).imp Or.inl id
      · exact (cty_labelOccurs_tySubstFrom ℓ k T B h).imp Or.inr id
end

/-- **THE μ CORNER.** A label in the μ-unrolling occurs in the rolled type — so `¬LabelOccurs ℓ (mu A)`
(= `¬LabelOccurs ℓ A`) propagates to `¬LabelOccurs ℓ (unrollMu A)`. -/
theorem labelOccurs_unrollMu (ℓ : Label) (A : VTy Eff Mult)
    (h : VTy.labelOccurs ℓ (VTy.unrollMu A)) : VTy.labelOccurs ℓ A := by
  rcases vty_labelOccurs_tySubstFrom ℓ 0 (VTy.mu A) A h with h | h
  · exact h
  · simpa only [VTy.labelOccurs] using h

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

/-! ## §2′ — the TYPELESS grade-driven liveness invariant (ADR-0060, the inc-5 reshape).

`LWSV`/`LWSC`/`LWSK` replace `WSV`/`WSC`/`WSK`: the TYPE/EFFECT indices are DROPPED (a `vcap`'s label
`ℓ` is read from the TERM; the storage grade `q` is a constructor PARAMETER, pinned to the bundled
`HasConfigTy` — not a `WSC` type index). This dissolves the §2.9 obstruction (no intermediate-type
reconciliation at `letC`/`app`; no non-injective `φ₁⊔φ₂` join-elim) and lets the subst bridge close.
The reachability flag `b : Bool` (opt-2): `true` = "the evaluator will force this position" (`vcap_live`
demands resolution); `false` = dormant (no obligation). Storage positions gate liveness on the local
scalar grade: `app`-arg / `ret`-value off `decide (q ≠ 0)`. Ported from the build-confirmed engine
(`scratch/Opt3GradeLiveness.lean`, branch inc5-opt3-gradegate), extended to the full former set. -/

mutual
inductive LWSV (K : EvalCtx) : Bool → Val → Prop where
  | vunit {b} : LWSV K b Val.vunit
  | vint {b n} : LWSV K b (Val.vint n)
  | vvar {b i} : LWSV K b (Val.vvar i)
  | vcap_live {n ℓ} (h : ResolvesLabel K n ℓ) : LWSV K true (Val.vcap n ℓ)
  | vcap_dormant {n ℓ} : LWSV K false (Val.vcap n ℓ)
  | vthunk {b c} (h : LWSC K b c) : LWSV K b (Val.vthunk c)
  | inl {b v} (h : LWSV K b v) : LWSV K b (Val.inl v)
  | inr {b v} (h : LWSV K b v) : LWSV K b (Val.inr v)
  | pair {b a c} (h1 : LWSV K b a) (h2 : LWSV K b c) : LWSV K b (Val.pair a c)
  | fold {b v} (h : LWSV K b v) : LWSV K b (Val.fold v)
inductive LWSC (K : EvalCtx) : Bool → Comp → Prop where
  | ret {b v q} (h : LWSV K (b && decide (q ≠ 0)) v) : LWSC K b (Comp.ret v)
  | letC {b M N} (h1 : LWSC K b M) (h2 : LWSC K b N) : LWSC K b (Comp.letC M N)
  | force {b v} (h : LWSV K b v) : LWSC K b (Comp.force v)
  | lam {b M} (h : LWSC K b M) : LWSC K b (Comp.lam M)
  | app {b M v q} (h1 : LWSC K b M) (h2 : LWSV K (b && decide (q ≠ 0)) v) : LWSC K b (Comp.app M v)
  | case {b v N₁ N₂ q} (h1 : LWSV K (b && decide (q ≠ 0)) v) (h2 : LWSC K b N₁) (h3 : LWSC K b N₂) :
      LWSC K b (Comp.case v N₁ N₂)
  | split {b v N q} (h1 : LWSV K (b && decide (q ≠ 0)) v) (h2 : LWSC K b N) : LWSC K b (Comp.split v N)
  | unfold {b v} (h : LWSV K b v) : LWSC K b (Comp.unfold v)
  | perform {b cv op v} (h1 : LWSV K b cv) (h2 : LWSV K false v) : LWSC K b (Comp.perform cv op v)
  | handleThrows {b ℓ M} (h : LWSC K b M) : LWSC K b (Comp.handle (Handler.throws ℓ) M)
  | handleState {b ℓ s M} (h1 : LWSV K b s) (h2 : LWSC K b M) :
      LWSC K b (Comp.handle (Handler.state ℓ s) M)
  | handleTransaction {b ℓ Θ M} (h : LWSC K b M) :
      LWSC K b (Comp.handle (Handler.transaction ℓ Θ) M)
inductive LWSK (K : EvalCtx) : EvalCtx → Bool → Prop where
  | nil {b} : LWSK K [] b
  | letF {Sg N b} (hN : LWSC K b N) (hK : LWSK K Sg b) : LWSK K (Frame.letF N :: Sg) b
  | appF {Sg v b q} (hv : LWSV K (b && decide (q ≠ 0)) v) (hK : LWSK K Sg b) :
      LWSK K (Frame.appF v :: Sg) b
  | handleF {Sg n ℓ b} (hK : LWSK K Sg b) :
      LWSK K (Frame.handleF n (Handler.throws ℓ) :: Sg) b
  | stateF {Sg n ℓ s b} (hs : LWSV K b s) (hK : LWSK K Sg b) :
      LWSK K (Frame.handleF n (Handler.state ℓ s) :: Sg) b
  | transactionF {Sg n ℓ Θ b} (hK : LWSK K Sg b) :
      LWSK K (Frame.handleF n (Handler.transaction ℓ Θ) :: Sg) b
end

/-! ### §2′.1 — MONOTONICITY: any flag collapses DOWN to dormant.

`true` is the STRONGEST flag (`vcap_live` demands resolution, `vcap_dormant` nothing). So any
`LWSV`/`LWSC` weakens to dormant — the engine for the LIVE subst bridge (a live arg plugs into ANY
occurrence flag). Full former set. -/
mutual
theorem lwsv_to_dormant {K : EvalCtx} {b : Bool} {v : Val} (h : LWSV K b v) : LWSV K false v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap_live _ => exact .vcap_dormant
  | vcap_dormant => exact .vcap_dormant
  | vthunk h => exact .vthunk (lwsc_to_dormant h)
  | inl h => exact .inl (lwsv_to_dormant h)
  | inr h => exact .inr (lwsv_to_dormant h)
  | pair h1 h2 => exact .pair (lwsv_to_dormant h1) (lwsv_to_dormant h2)
  | fold h => exact .fold (lwsv_to_dormant h)
theorem lwsc_to_dormant {K : EvalCtx} {b : Bool} {M : Comp} (h : LWSC K b M) : LWSC K false M := by
  cases h with
  | @ret b v q h => exact .ret (q := q) (by simpa using lwsv_to_dormant h)
  | letC h1 h2 => exact .letC (lwsc_to_dormant h1) (lwsc_to_dormant h2)
  | force h => exact .force (lwsv_to_dormant h)
  | lam h => exact .lam (lwsc_to_dormant h)
  | @app b M' v q h1 h2 => exact .app (q := q) (lwsc_to_dormant h1) (by simpa using lwsv_to_dormant h2)
  | case h1 h2 h3 =>
      exact .case (q := 0) (by simpa using lwsv_to_dormant h1) (lwsc_to_dormant h2) (lwsc_to_dormant h3)
  | split h1 h2 => exact .split (q := 0) (by simpa using lwsv_to_dormant h1) (lwsc_to_dormant h2)
  | unfold h => exact .unfold (lwsv_to_dormant h)
  | perform h1 h2 => exact .perform (lwsv_to_dormant h1) (lwsv_to_dormant h2)
  | handleThrows h => exact .handleThrows (lwsc_to_dormant h)
  | handleState h1 h2 => exact .handleState (lwsv_to_dormant h1) (lwsc_to_dormant h2)
  | handleTransaction h => exact .handleTransaction (lwsc_to_dormant h)
end

/-- A LIVE value plugs into ANY occurrence flag (`b = true` identity; `false` is `lwsv_to_dormant`). -/
theorem lwsv_of_live {K : EvalCtx} (b : Bool) {v : Val} (h : LWSV K true v) : LWSV K b v := by
  cases b with
  | true => exact h
  | false => exact lwsv_to_dormant h

/-! ### §2′.2 — the LIVE subst bridge (REDUCE/β, q≠0): substitute a LIVE closed arg.

`w` closed ⇒ `shift w = w` (kills the under-binder shift); the live arg plugs into every `vvar`-`k`
leaf via `lwsv_of_live`. TYPING-FREE, all cutoffs/binders, full former set. -/
mutual
theorem lwsv_subst {K : EvalCtx} {w : Val} (hwl : LWSV K true w) (hcl : ∀ j, Val.shiftFrom j w = w)
    {u : Val} {bu : Bool} (k : Nat) (hu : LWSV K bu u) : LWSV K bu (Val.substFrom k w u) := by
  cases hu with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar b i =>
    simp only [Val.substFrom]
    by_cases hik : i = k
    · subst hik; simpa using lwsv_of_live bu hwl
    · rw [if_neg hik]; split <;> exact .vvar
  | vcap_live h => simpa only [Val.substFrom] using LWSV.vcap_live h
  | vcap_dormant => simpa only [Val.substFrom] using LWSV.vcap_dormant
  | vthunk h => exact .vthunk (lwsc_subst hwl hcl k h)
  | inl h => exact .inl (lwsv_subst hwl hcl k h)
  | inr h => exact .inr (lwsv_subst hwl hcl k h)
  | pair h1 h2 => exact .pair (lwsv_subst hwl hcl k h1) (lwsv_subst hwl hcl k h2)
  | fold h => exact .fold (lwsv_subst hwl hcl k h)
theorem lwsc_subst {K : EvalCtx} {w : Val} (hwl : LWSV K true w) (hcl : ∀ j, Val.shiftFrom j w = w)
    {M : Comp} {bM : Bool} (k : Nat) (hM : LWSC K bM M) : LWSC K bM (Comp.substFrom k w M) := by
  have hsh : Val.shift w = w := hcl 0
  cases hM with
  | ret h => exact .ret (lwsv_subst hwl hcl k h)
  | letC h1 h2 =>
    refine .letC (lwsc_subst hwl hcl k h1) ?_
    simp only [hsh]; exact lwsc_subst hwl hcl (k + 1) h2
  | force h => exact .force (lwsv_subst hwl hcl k h)
  | lam h => simp only [Comp.substFrom, hsh]; exact .lam (lwsc_subst hwl hcl (k + 1) h)
  | app h1 h2 => exact .app (lwsc_subst hwl hcl k h1) (lwsv_subst hwl hcl k h2)
  | @case b v N₁ N₂ q h1 h2 h3 =>
    simp only [Comp.substFrom, hsh]
    exact .case (q := q) (lwsv_subst hwl hcl k h1) (lwsc_subst hwl hcl (k + 1) h2)
      (lwsc_subst hwl hcl (k + 1) h3)
  | @split b v N q h1 h2 =>
    simp only [Comp.substFrom, hsh]
    exact .split (q := q) (lwsv_subst hwl hcl k h1) (lwsc_subst hwl hcl (k + 2) h2)
  | unfold h => exact .unfold (lwsv_subst hwl hcl k h)
  | perform h1 h2 => exact .perform (lwsv_subst hwl hcl k h1) (lwsv_subst hwl hcl k h2)
  | handleThrows h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]; exact .handleThrows (lwsc_subst hwl hcl (k + 1) h)
  | handleState h1 h2 =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleState (lwsv_subst hwl hcl k h1) (lwsc_subst hwl hcl (k + 1) h2)
  | handleTransaction h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleTransaction (lwsc_subst hwl hcl (k + 1) h)
end

/-! ### §2′.3 — the ALL-DORMANT subst bridge (REDUCE/β, b=false): dormant arg into dormant term. -/
mutual
theorem lwsv_subst_dormant {K : EvalCtx} {w : Val} (hwd : LWSV K false w)
    (hcl : ∀ j, Val.shiftFrom j w = w) {u : Val} (k : Nat) (hu : LWSV K false u) :
    LWSV K false (Val.substFrom k w u) := by
  cases hu with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar b i =>
    simp only [Val.substFrom]
    by_cases hik : i = k
    · subst hik; simpa using hwd
    · rw [if_neg hik]; split <;> exact .vvar
  | vcap_dormant => simpa only [Val.substFrom] using LWSV.vcap_dormant
  | vthunk h => exact .vthunk (lwsc_subst_dormant hwd hcl k h)
  | inl h => exact .inl (lwsv_subst_dormant hwd hcl k h)
  | inr h => exact .inr (lwsv_subst_dormant hwd hcl k h)
  | pair h1 h2 => exact .pair (lwsv_subst_dormant hwd hcl k h1) (lwsv_subst_dormant hwd hcl k h2)
  | fold h => exact .fold (lwsv_subst_dormant hwd hcl k h)
theorem lwsc_subst_dormant {K : EvalCtx} {w : Val} (hwd : LWSV K false w)
    (hcl : ∀ j, Val.shiftFrom j w = w) {M : Comp} (k : Nat) (hM : LWSC K false M) :
    LWSC K false (Comp.substFrom k w M) := by
  have hsh : Val.shift w = w := hcl 0
  cases hM with
  | @ret b v q h => exact .ret (q := q) (lwsv_subst_dormant hwd hcl k (by simpa using h))
  | letC h1 h2 =>
    refine .letC (lwsc_subst_dormant hwd hcl k h1) ?_
    simp only [hsh]; exact lwsc_subst_dormant hwd hcl (k + 1) h2
  | force h => exact .force (lwsv_subst_dormant hwd hcl k h)
  | lam h => simp only [Comp.substFrom, hsh]; exact .lam (lwsc_subst_dormant hwd hcl (k + 1) h)
  | @app b M' v q h1 h2 =>
    exact .app (q := q) (lwsc_subst_dormant hwd hcl k h1) (lwsv_subst_dormant hwd hcl k (by simpa using h2))
  | case h1 h2 h3 =>
    simp only [Comp.substFrom, hsh]
    exact .case (q := 0) (lwsv_subst_dormant hwd hcl k (by simpa using h1))
      (lwsc_subst_dormant hwd hcl (k + 1) h2) (lwsc_subst_dormant hwd hcl (k + 1) h3)
  | split h1 h2 =>
    simp only [Comp.substFrom, hsh]
    exact .split (q := 0) (lwsv_subst_dormant hwd hcl k (by simpa using h1))
      (lwsc_subst_dormant hwd hcl (k + 2) h2)
  | unfold h => exact .unfold (lwsv_subst_dormant hwd hcl k h)
  | perform h1 h2 => exact .perform (lwsv_subst_dormant hwd hcl k h1) (lwsv_subst_dormant hwd hcl k h2)
  | handleThrows h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleThrows (lwsc_subst_dormant hwd hcl (k + 1) h)
  | handleState h1 h2 =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleState (lwsv_subst_dormant hwd hcl k h1) (lwsc_subst_dormant hwd hcl (k + 1) h2)
  | handleTransaction h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleTransaction (lwsc_subst_dormant hwd hcl (k + 1) h)
end

/-! ### §2′.4 — POP dead-cap: a dormant value is STACK-INDEPENDENT (re-homes to ANY stack). -/
mutual
theorem lwsv_dormant_stack_indep {K K' : EvalCtx} {u : Val} (h : LWSV K false u) : LWSV K' false u := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap_dormant => exact .vcap_dormant
  | vthunk h => exact .vthunk (lwsc_dormant_stack_indep h)
  | inl h => exact .inl (lwsv_dormant_stack_indep h)
  | inr h => exact .inr (lwsv_dormant_stack_indep h)
  | pair h1 h2 => exact .pair (lwsv_dormant_stack_indep h1) (lwsv_dormant_stack_indep h2)
  | fold h => exact .fold (lwsv_dormant_stack_indep h)
theorem lwsc_dormant_stack_indep {K K' : EvalCtx} {M : Comp} (h : LWSC K false M) : LWSC K' false M := by
  cases h with
  | @ret b v q h => exact .ret (q := q) (by simpa using lwsv_dormant_stack_indep (by simpa using h))
  | letC h1 h2 => exact .letC (lwsc_dormant_stack_indep h1) (lwsc_dormant_stack_indep h2)
  | force h => exact .force (lwsv_dormant_stack_indep h)
  | lam h => exact .lam (lwsc_dormant_stack_indep h)
  | @app b M' v q h1 h2 =>
    exact .app (q := q) (lwsc_dormant_stack_indep h1) (by simpa using lwsv_dormant_stack_indep (by simpa using h2))
  | case h1 h2 h3 =>
    exact .case (q := 0) (lwsv_dormant_stack_indep (by simpa using h1))
      (lwsc_dormant_stack_indep h2) (lwsc_dormant_stack_indep h3)
  | split h1 h2 =>
    exact .split (q := 0) (lwsv_dormant_stack_indep (by simpa using h1)) (lwsc_dormant_stack_indep h2)
  | unfold h => exact .unfold (lwsv_dormant_stack_indep h)
  | perform h1 h2 => exact .perform (lwsv_dormant_stack_indep h1) (lwsv_dormant_stack_indep h2)
  | handleThrows h => exact .handleThrows (lwsc_dormant_stack_indep h)
  | handleState h1 h2 => exact .handleState (lwsv_dormant_stack_indep h1) (lwsc_dormant_stack_indep h2)
  | handleTransaction h => exact .handleTransaction (lwsc_dormant_stack_indep h)
end

/-! ### §2′.5 — the SEED: a cap-free program is `LWSV`/`LWSC` at any flag (no `vcap_live` obligation).
Mirrors `wsv_capFree`; storage formers use `q := 0` so the sub-gate collapses to dormant. -/
mutual
theorem lwsv_capFree {γ Γ v A} (K : EvalCtx) (b : Bool)
    (d : HasVTy (Eff := Eff) (Mult := Mult) γ Γ v A) (h : capsV v = []) : LWSV K b v := by
  cases d with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar _ => exact .vvar
  | vcap => simp only [capsV] at h; exact absurd h (List.cons_ne_nil _ _)
  | vthunk hM => exact .vthunk (lwsc_capFree K b hM (by simpa only [capsV] using h))
  | inl hv => exact .inl (lwsv_capFree K b hv (by simpa only [capsV] using h))
  | inr hv => exact .inr (lwsv_capFree K b hv (by simpa only [capsV] using h))
  | pair hv hw _ =>
      simp only [capsV, List.append_eq_nil_iff] at h
      exact .pair (lwsv_capFree K b hv h.1) (lwsv_capFree K b hw h.2)
  | fold hv => exact .fold (lwsv_capFree K b hv (by simpa only [capsV] using h))
theorem lwsc_capFree {γ Γ c φ C} (K : EvalCtx) (b : Bool)
    (d : HasCTy (Eff := Eff) (Mult := Mult) γ Γ c φ C) (h : capsC c = []) : LWSC K b c := by
  cases d with
  | ret hv _ => exact .ret (q := 0) (lwsv_capFree K _ hv (by simpa only [capsC] using h))
  | letC hM hN _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .letC (lwsc_capFree K b hM h.1) (lwsc_capFree K b hN h.2)
  | force hv => exact .force (lwsv_capFree K b hv (by simpa only [capsC] using h))
  | lam hM => exact .lam (lwsc_capFree K b hM (by simpa only [capsC] using h))
  | app hM hv _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .app (q := 0) (lwsc_capFree K b hM h.1) (lwsv_capFree K _ hv h.2)
  | case hv hN₁ hN₂ _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .case (q := 0) (lwsv_capFree K _ hv h.1.1) (lwsc_capFree K b hN₁ h.1.2) (lwsc_capFree K b hN₂ h.2)
  | split hv hN _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .split (q := 0) (lwsv_capFree K _ hv h.1) (lwsc_capFree K b hN h.2)
  | unfold hv => exact .unfold (lwsv_capFree K b hv (by simpa only [capsC] using h))
  | perform hc _ _ _ hv =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .perform (lwsv_capFree K b hc h.1) (lwsv_capFree K _ hv h.2)
  | handleThrows _ _ hM _ _ =>
      simp only [capsC, capsH, List.nil_append] at h
      exact .handleThrows (lwsc_capFree K b hM h)
  | handleState _ _ _ _ _ hs hM _ _ =>
      simp only [capsC, capsH, List.append_eq_nil_iff] at h
      exact .handleState (lwsv_capFree K b hs h.1) (lwsc_capFree K b hM h.2)
  | handleTransaction _ _ _ _ _ _ _ _ hM _ _ =>
      simp only [capsC, capsH, List.append_eq_nil_iff] at h
      exact .handleTransaction (lwsc_capFree K b hM h.2)
end

/-- **FOCUSRESOLVES (typeless).** A LIVE `perform (vcap n ℓ)` focus's cap RESOLVES — from the term's
`ℓ` via `LWSV.vcap_live`, no type index. (Op-in-interface stays in the threaded typing.) -/
theorem lwsc_focus_resolves {K : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId} {v : Val}
    (h : LWSC K true (Comp.perform (Val.vcap n ℓ) op v)) : ResolvesLabel K n ℓ := by
  cases h with
  | perform h1 _ => cases h1 with | vcap_live hr => exact hr

/-- The ratified zero-sum-free property (ADR-0060): a sum is zero only if both summands are (`ℕ`,
`QTT` hold it; rings fail). The grade-rig commitment — discharges the dormant-arm grade-0 routing. -/
def ZeroSumFree (Mult : Type) [Add Mult] [Zero Mult] : Prop := ∀ a b : Mult, a + b = 0 → a = 0 ∧ b = 0

/-! ### §2′.6 — the MIXED β arm (b=true∧q=0), GIVEN coherence. `LWSVk`/`LWSCk` = `LWSV`/`LWSC` + "the
substituted var `k` occurs only at DORMANT flags" (`vvar_k` forces false; `k` shifts under each binder
— case/handle `k+1`, split `k+2`). Port discharges `γ[k]=0 ⇒ LWSVk` via the rig. -/
mutual
inductive LWSVk (K : EvalCtx) : Nat → Bool → Val → Prop where
  | vunit {k b} : LWSVk K k b Val.vunit
  | vint {k b n} : LWSVk K k b (Val.vint n)
  | vvar_other {k b i} (h : i ≠ k) : LWSVk K k b (Val.vvar i)
  | vvar_k {k} : LWSVk K k false (Val.vvar k)
  | vcap_live {k b n ℓ} (h : ResolvesLabel K n ℓ) (hb : b = true) : LWSVk K k b (Val.vcap n ℓ)
  | vcap_dormant {k b n ℓ} (hb : b = false) : LWSVk K k b (Val.vcap n ℓ)
  | vthunk {k b c} (h : LWSCk K k b c) : LWSVk K k b (Val.vthunk c)
  | inl {k b v} (h : LWSVk K k b v) : LWSVk K k b (Val.inl v)
  | inr {k b v} (h : LWSVk K k b v) : LWSVk K k b (Val.inr v)
  | pair {k b a c} (h1 : LWSVk K k b a) (h2 : LWSVk K k b c) : LWSVk K k b (Val.pair a c)
  | fold {k b v} (h : LWSVk K k b v) : LWSVk K k b (Val.fold v)
inductive LWSCk (K : EvalCtx) : Nat → Bool → Comp → Prop where
  | ret {k b v q} (h : LWSVk K k (b && decide (q ≠ 0)) v) : LWSCk K k b (Comp.ret v)
  | letC {k b M N} (h1 : LWSCk K k b M) (h2 : LWSCk K (k + 1) b N) : LWSCk K k b (Comp.letC M N)
  | force {k b v} (h : LWSVk K k b v) : LWSCk K k b (Comp.force v)
  | lam {k b M} (h : LWSCk K (k + 1) b M) : LWSCk K k b (Comp.lam M)
  | app {k b M v q} (h1 : LWSCk K k b M) (h2 : LWSVk K k (b && decide (q ≠ 0)) v) :
      LWSCk K k b (Comp.app M v)
  | case {k b v N₁ N₂ q} (h1 : LWSVk K k (b && decide (q ≠ 0)) v) (h2 : LWSCk K (k + 1) b N₁)
      (h3 : LWSCk K (k + 1) b N₂) : LWSCk K k b (Comp.case v N₁ N₂)
  | split {k b v N q} (h1 : LWSVk K k (b && decide (q ≠ 0)) v) (h2 : LWSCk K (k + 2) b N) :
      LWSCk K k b (Comp.split v N)
  | unfold {k b v} (h : LWSVk K k b v) : LWSCk K k b (Comp.unfold v)
  | perform {k b cv op v} (h1 : LWSVk K k b cv) (h2 : LWSVk K k false v) :
      LWSCk K k b (Comp.perform cv op v)
  | handleThrows {k b ℓ M} (h : LWSCk K (k + 1) b M) : LWSCk K k b (Comp.handle (Handler.throws ℓ) M)
  | handleState {k b ℓ s M} (h1 : LWSVk K k b s) (h2 : LWSCk K (k + 1) b M) :
      LWSCk K k b (Comp.handle (Handler.state ℓ s) M)
  | handleTransaction {k b ℓ Θ M} (h : LWSCk K (k + 1) b M) :
      LWSCk K k b (Comp.handle (Handler.transaction ℓ Θ) M)
end

mutual
theorem lwsvk_subst {K : EvalCtx} {w : Val} (hwd : LWSV K false w)
    (hcl : ∀ j, Val.shiftFrom j w = w) {u : Val} {bu : Bool} (k : Nat)
    (hu : LWSVk K k bu u) : LWSV K bu (Val.substFrom k w u) := by
  cases hu with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar_other hik => simp only [Val.substFrom, if_neg hik]; split <;> exact .vvar
  | vvar_k => simpa only [Val.substFrom, if_pos rfl] using hwd
  | vcap_live h hb => subst hb; simpa only [Val.substFrom] using LWSV.vcap_live h
  | vcap_dormant hb => subst hb; simpa only [Val.substFrom] using LWSV.vcap_dormant
  | vthunk h => exact .vthunk (lwsck_subst hwd hcl k h)
  | inl h => exact .inl (lwsvk_subst hwd hcl k h)
  | inr h => exact .inr (lwsvk_subst hwd hcl k h)
  | pair h1 h2 => exact .pair (lwsvk_subst hwd hcl k h1) (lwsvk_subst hwd hcl k h2)
  | fold h => exact .fold (lwsvk_subst hwd hcl k h)
theorem lwsck_subst {K : EvalCtx} {w : Val} (hwd : LWSV K false w)
    (hcl : ∀ j, Val.shiftFrom j w = w) {M : Comp} {bM : Bool} (k : Nat)
    (hM : LWSCk K k bM M) : LWSC K bM (Comp.substFrom k w M) := by
  have hsh : Val.shift w = w := hcl 0
  cases hM with
  | ret h => exact .ret (lwsvk_subst hwd hcl k h)
  | letC h1 h2 =>
    refine .letC (lwsck_subst hwd hcl k h1) ?_
    simp only [hsh]; exact lwsck_subst hwd hcl (k + 1) h2
  | force h => exact .force (lwsvk_subst hwd hcl k h)
  | lam h => simp only [Comp.substFrom, hsh]; exact .lam (lwsck_subst hwd hcl (k + 1) h)
  | app h1 h2 => exact .app (lwsck_subst hwd hcl k h1) (lwsvk_subst hwd hcl k h2)
  | @case _ _ _ _ _ q h1 h2 h3 =>
    simp only [Comp.substFrom, hsh]
    exact .case (q := q) (lwsvk_subst hwd hcl k h1) (lwsck_subst hwd hcl (k + 1) h2)
      (lwsck_subst hwd hcl (k + 1) h3)
  | @split _ _ _ _ q h1 h2 =>
    simp only [Comp.substFrom, hsh]
    exact .split (q := q) (lwsvk_subst hwd hcl k h1) (lwsck_subst hwd hcl (k + 2) h2)
  | unfold h => exact .unfold (lwsvk_subst hwd hcl k h)
  | perform h1 h2 => exact .perform (lwsvk_subst hwd hcl k h1) (lwsvk_subst hwd hcl k h2)
  | handleThrows h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]; exact .handleThrows (lwsck_subst hwd hcl (k + 1) h)
  | handleState h1 h2 =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleState (lwsvk_subst hwd hcl k h1) (lwsck_subst hwd hcl (k + 1) h2)
  | handleTransaction h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    exact .handleTransaction (lwsck_subst hwd hcl (k + 1) h)
end

/-! ### §2′.7 — LIVE-cap-across-POP, GIVEN B-occ freshness. `LWSVp`/`LWSCp` = `LWSV`/`LWSC` with
`vcap_live` carrying `n ≠ g` (resolution over the un-popped stack). `pop_restack` re-homes each live
cap below `g`. Port discharges `n ≠ g` from ADR-0057 B-occ. -/

/-- A cap with `n ≠ g` resolving over `handleF g hd :: K` resolves over the popped `K` (`splitAtId`
walks past the non-matching frame). Local copy of the later `resolvesLabel_uncons` (forward-ref). -/
theorem resolvesLabel_pop {g : Nat} {hd : Handler} {K : EvalCtx} {n : Nat} {ℓ : Label}
    (hng : n ≠ g) (hr : ResolvesLabel (Frame.handleF g hd :: K) n ℓ) : ResolvesLabel K n ℓ := by
  obtain ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩ := hr
  rw [splitAtId, if_neg (Ne.symm hng)] at hsplit
  obtain ⟨⟨Kᵢ', hh', Kₒ'⟩, hsK, heq⟩ := Option.map_eq_some_iff.mp hsplit
  simp only [Prod.mk.injEq] at heq
  exact ⟨Kᵢ', hh, Kₒ, by rw [hsK, heq.2.1, heq.2.2], hlbl⟩

mutual
inductive LWSVp (K : EvalCtx) (g : Nat) : Bool → Val → Prop where
  | vunit {b} : LWSVp K g b Val.vunit
  | vint {b n} : LWSVp K g b (Val.vint n)
  | vvar {b i} : LWSVp K g b (Val.vvar i)
  | vcap_live {n ℓ} (h : ResolvesLabel K n ℓ) (hng : n ≠ g) : LWSVp K g true (Val.vcap n ℓ)
  | vcap_dormant {n ℓ} : LWSVp K g false (Val.vcap n ℓ)
  | vthunk {b c} (h : LWSCp K g b c) : LWSVp K g b (Val.vthunk c)
  | inl {b v} (h : LWSVp K g b v) : LWSVp K g b (Val.inl v)
  | inr {b v} (h : LWSVp K g b v) : LWSVp K g b (Val.inr v)
  | pair {b a c} (h1 : LWSVp K g b a) (h2 : LWSVp K g b c) : LWSVp K g b (Val.pair a c)
  | fold {b v} (h : LWSVp K g b v) : LWSVp K g b (Val.fold v)
inductive LWSCp (K : EvalCtx) (g : Nat) : Bool → Comp → Prop where
  | ret {b v q} (h : LWSVp K g (b && decide (q ≠ 0)) v) : LWSCp K g b (Comp.ret v)
  | letC {b M N} (h1 : LWSCp K g b M) (h2 : LWSCp K g b N) : LWSCp K g b (Comp.letC M N)
  | force {b v} (h : LWSVp K g b v) : LWSCp K g b (Comp.force v)
  | lam {b M} (h : LWSCp K g b M) : LWSCp K g b (Comp.lam M)
  | app {b M v q} (h1 : LWSCp K g b M) (h2 : LWSVp K g (b && decide (q ≠ 0)) v) :
      LWSCp K g b (Comp.app M v)
  | case {b v N₁ N₂ q} (h1 : LWSVp K g (b && decide (q ≠ 0)) v) (h2 : LWSCp K g b N₁)
      (h3 : LWSCp K g b N₂) : LWSCp K g b (Comp.case v N₁ N₂)
  | split {b v N q} (h1 : LWSVp K g (b && decide (q ≠ 0)) v) (h2 : LWSCp K g b N) :
      LWSCp K g b (Comp.split v N)
  | unfold {b v} (h : LWSVp K g b v) : LWSCp K g b (Comp.unfold v)
  | perform {b cv op v} (h1 : LWSVp K g b cv) (h2 : LWSVp K g false v) :
      LWSCp K g b (Comp.perform cv op v)
  | handleThrows {b ℓ M} (h : LWSCp K g b M) : LWSCp K g b (Comp.handle (Handler.throws ℓ) M)
  | handleState {b ℓ s M} (h1 : LWSVp K g b s) (h2 : LWSCp K g b M) :
      LWSCp K g b (Comp.handle (Handler.state ℓ s) M)
  | handleTransaction {b ℓ Θ M} (h : LWSCp K g b M) :
      LWSCp K g b (Comp.handle (Handler.transaction ℓ Θ) M)
end

mutual
theorem lwsvp_pop_restack {g : Nat} {hd : Handler} {K : EvalCtx} {b : Bool} {v : Val}
    (hv : LWSVp (Frame.handleF g hd :: K) g b v) : LWSV K b v := by
  cases hv with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap_live hr hng => exact .vcap_live (resolvesLabel_pop hng hr)
  | vcap_dormant => exact .vcap_dormant
  | vthunk h => exact .vthunk (lwscp_pop_restack h)
  | inl h => exact .inl (lwsvp_pop_restack h)
  | inr h => exact .inr (lwsvp_pop_restack h)
  | pair h1 h2 => exact .pair (lwsvp_pop_restack h1) (lwsvp_pop_restack h2)
  | fold h => exact .fold (lwsvp_pop_restack h)
theorem lwscp_pop_restack {g : Nat} {hd : Handler} {K : EvalCtx} {b : Bool} {M : Comp}
    (hM : LWSCp (Frame.handleF g hd :: K) g b M) : LWSC K b M := by
  cases hM with
  | ret h => exact .ret (lwsvp_pop_restack h)
  | letC h1 h2 => exact .letC (lwscp_pop_restack h1) (lwscp_pop_restack h2)
  | force h => exact .force (lwsvp_pop_restack h)
  | lam h => exact .lam (lwscp_pop_restack h)
  | app h1 h2 => exact .app (lwscp_pop_restack h1) (lwsvp_pop_restack h2)
  | @case _ _ _ _ q h1 h2 h3 =>
      exact .case (q := q) (lwsvp_pop_restack h1) (lwscp_pop_restack h2) (lwscp_pop_restack h3)
  | @split _ _ _ q h1 h2 => exact .split (q := q) (lwsvp_pop_restack h1) (lwscp_pop_restack h2)
  | unfold h => exact .unfold (lwsvp_pop_restack h)
  | perform h1 h2 => exact .perform (lwsvp_pop_restack h1) (lwsvp_pop_restack h2)
  | handleThrows h => exact .handleThrows (lwscp_pop_restack h)
  | handleState h1 h2 => exact .handleState (lwsvp_pop_restack h1) (lwscp_pop_restack h2)
  | handleTransaction h => exact .handleTransaction (lwscp_pop_restack h)
end

/-! ### §2′.8 — the COHERENT graded liveness `LWSVg`/`LWSCg`/`LWSKg` (ADR-0060 / Task B, the Coh layer).

The typeless `LWSV`/`LWSC` leave the storage `q`'s (the `ret`/`app`/`appF` budget/mult) EXISTENTIAL, so a
`γ[k]=0` typing fact can't reach the liveness flags. `LWSVg`/`LWSCg` add a GRADE-CONTEXT index `γ` and
mirror `HasCTy`'s grade structure EXACTLY (the equation hypotheses `γ = q • γ'` at `ret`, `γ = γ₁ + q•γ₂`
at `app`, the binder extensions), pinning each storage `q` to the typing's scalar. The only NEW content
over `HasCTy` is the liveness gates (`b && decide (q ≠ 0)` on storage positions; `vvar`'s grade-liveness
link). Projects to `LWSV`/`LWSC` by FORGETTING `γ` (`lwsvg_to_lwsv`), so the green cap-bridge + positive
direction are reused UNCHANGED. The discharge `lwscg_to_lwsvk` reads `γ` to route `γ[k]=0 ⇒ dormant`. -/
mutual
inductive LWSVg (K : EvalCtx) : GradeVec Mult → Bool → Val → Prop where
  | vunit {γ : GradeVec Mult} {b} : LWSVg K γ b Val.vunit
  | vint {γ : GradeVec Mult} {b n} : LWSVg K γ b (Val.vint n)
  -- THE grade-liveness LINK: `vvar i` may be LIVE (`b = true`) only where its grade is non-zero.
  | vvar {γ : GradeVec Mult} {b i} (h : b = true → (γ[i]?.getD 0) ≠ 0) : LWSVg K γ b (Val.vvar i)
  | vcap_live {γ : GradeVec Mult} {n ℓ} (h : ResolvesLabel K n ℓ) : LWSVg K γ true (Val.vcap n ℓ)
  | vcap_dormant {γ : GradeVec Mult} {n ℓ} : LWSVg K γ false (Val.vcap n ℓ)
  | vthunk {γ : GradeVec Mult} {b c} (h : LWSCg K γ b c) : LWSVg K γ b (Val.vthunk c)
  | inl {γ : GradeVec Mult} {b v} (h : LWSVg K γ b v) : LWSVg K γ b (Val.inl v)
  | inr {γ : GradeVec Mult} {b v} (h : LWSVg K γ b v) : LWSVg K γ b (Val.inr v)
  | pair {γ γ_v γ_w : GradeVec Mult} {b a c} (hγ : γ = γ_v + γ_w) (hlen : γ_v.length = γ_w.length)
      (h1 : LWSVg K γ_v b a) (h2 : LWSVg K γ_w b c) : LWSVg K γ b (Val.pair a c)
  | fold {γ : GradeVec Mult} {b v} (h : LWSVg K γ b v) : LWSVg K γ b (Val.fold v)
inductive LWSCg (K : EvalCtx) : GradeVec Mult → Bool → Comp → Prop where
  | ret {γ γ' : GradeVec Mult} {b v} {q : Mult} (hγ : γ = q • γ')
      (h : LWSVg K γ' (b && decide (q ≠ 0)) v) : LWSCg K γ b (Comp.ret v)
  | letC {γ γ₁ γ₂ : GradeVec Mult} {b M N} {q1 q2 : Mult}
      (hγ : γ = (q_or_1 q2) • γ₁ + γ₂) (hlen : γ₁.length = γ₂.length)
      (h1 : LWSCg K γ₁ b M) (h2 : LWSCg K ((q1 * q_or_1 q2) :: γ₂) b N) : LWSCg K γ b (Comp.letC M N)
  | force {γ : GradeVec Mult} {b v} (h : LWSVg K γ b v) : LWSCg K γ b (Comp.force v)
  | lam {γ : GradeVec Mult} {b M} {q : Mult} (h : LWSCg K (q :: γ) b M) : LWSCg K γ b (Comp.lam M)
  | app {γ γ₁ γ₂ : GradeVec Mult} {b M v} {q : Mult} (hγ : γ = γ₁ + q • γ₂)
      (hlen : γ₁.length = γ₂.length)
      (h1 : LWSCg K γ₁ b M) (h2 : LWSVg K γ₂ (b && decide (q ≠ 0)) v) : LWSCg K γ b (Comp.app M v)
  | case {γ γ_v γ_N : GradeVec Mult} {b v N₁ N₂} {q : Mult} (hγ : γ = q • γ_v + γ_N)
      (hlen : γ_v.length = γ_N.length)
      (h1 : LWSVg K γ_v (b && decide (q ≠ 0)) v) (h2 : LWSCg K (q :: γ_N) b N₁)
      (h3 : LWSCg K (q :: γ_N) b N₂) : LWSCg K γ b (Comp.case v N₁ N₂)
  | split {γ γ_v γ_N : GradeVec Mult} {b v N} {q : Mult} (hγ : γ = q • γ_v + γ_N)
      (hlen : γ_v.length = γ_N.length)
      (h1 : LWSVg K γ_v (b && decide (q ≠ 0)) v) (h2 : LWSCg K (q :: q :: γ_N) b N) :
      LWSCg K γ b (Comp.split v N)
  | unfold {γ : GradeVec Mult} {b v} (h : LWSVg K γ b v) : LWSCg K γ b (Comp.unfold v)
  | perform {γ γ_v γ_c : GradeVec Mult} {b cv op v} {q : Mult} (hγ : γ = q • γ_v + γ_c)
      (hlen : γ_v.length = γ_c.length)
      (h1 : LWSVg K γ_c b cv) (h2 : LWSVg K γ_v false v) : LWSCg K γ b (Comp.perform cv op v)
  | handleThrows {γ : GradeVec Mult} {b ℓ M} {qc : Mult} (h : LWSCg K (qc :: γ) b M) :
      LWSCg K γ b (Comp.handle (Handler.throws ℓ) M)
  | handleState {γ : GradeVec Mult} {b ℓ s M} {qc : Mult} (hs : LWSVg K [] b s)
      (h : LWSCg K (qc :: γ) b M) : LWSCg K γ b (Comp.handle (Handler.state ℓ s) M)
  | handleTransaction {γ : GradeVec Mult} {b ℓ Θ M} {qc : Mult} (h : LWSCg K (qc :: γ) b M) :
      LWSCg K γ b (Comp.handle (Handler.transaction ℓ Θ) M)
end

/-- The COHERENT stack: each frame stores its continuation's `LWSCg`/`LWSVg` at the frame's FIXED grade
(`letF`'s `N` at `qk :: []`, `appF`'s closed `v` at `[]`). The ambient `γ : GradeVec Mult` index is
threaded unchanged (the frames carry their own internal grades) — it binds the `Mult` instances for the
constructor gates and matches the `WScfg` threading `LWSKg cfg.2.1 cfg.2.1 [] true`. -/
inductive LWSKg (K : EvalCtx) : EvalCtx → GradeVec Mult → Bool → Prop where
  | nil {γ b} : LWSKg K [] γ b
  | letF {Sg N γ b} {qk : Mult} (hN : LWSCg K (qk :: []) b N) (hK : LWSKg K Sg γ b) :
      LWSKg K (Frame.letF N :: Sg) γ b
  -- `q : ℕ` (like the typeless `LWSK.appF`): the stored `v` is CLOSED (cap-free ⇒ gate-vacuous), so the
  -- budget carries no grade meaning here; `ℕ` keeps `DecidableEq` global (`Mult`'s isn't auto-bound).
  | appF {Sg v γ b} {q : ℕ} (hv : LWSVg K ([] : GradeVec Mult) (b && decide (q ≠ 0)) v)
      (hK : LWSKg K Sg γ b) : LWSKg K (Frame.appF v :: Sg) γ b
  | handleF {Sg n ℓ γ b} (hK : LWSKg K Sg γ b) :
      LWSKg K (Frame.handleF n (Handler.throws ℓ) :: Sg) γ b
  | stateF {Sg n ℓ s γ b} (hs : LWSVg K ([] : GradeVec Mult) b s) (hK : LWSKg K Sg γ b) :
      LWSKg K (Frame.handleF n (Handler.state ℓ s) :: Sg) γ b
  | transactionF {Sg n ℓ Θ γ b} (hK : LWSKg K Sg γ b) :
      LWSKg K (Frame.handleF n (Handler.transaction ℓ Θ) :: Sg) γ b

/-! ### §2′.8a — the PROJECTION `LWSVg`/`LWSCg`/`LWSKg → LWSV`/`LWSC`/`LWSK` (forget `γ`).

Drops the grade index; the liveness gates carry over via `gnat` (the typeless `LWSV`/`LWSK` gates carry
a `ℕ`-typed budget `q` — only `decide (q ≠ 0)` matters — while `LWSCg`'s `q` is the `Mult` grade; `gnat`
realizes the `Mult`-non-zeroness as the `ℕ` witness). This is how the GREEN typeless cap-bridge +
positive direction are reused UNCHANGED. -/

/-- The `ℕ` budget realizing a `Mult`-grade's non-zeroness (the typeless gates' `q` is `ℕ`). -/
private def gnat (q : Mult) : Nat := if q = 0 then 0 else 1
private theorem decide_gnat (q : Mult) : decide (gnat q ≠ 0) = decide (q ≠ 0) := by
  unfold gnat; by_cases hq : q = 0 <;> simp [hq]

mutual
theorem lwsvg_to_lwsv {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} {v : Val}
    (h : LWSVg K γ b v) : LWSV K b v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar _ => exact .vvar
  | vcap_live hr => exact .vcap_live hr
  | vcap_dormant => exact .vcap_dormant
  | vthunk h => exact .vthunk (lwscg_to_lwsc h)
  | inl h => exact .inl (lwsvg_to_lwsv h)
  | inr h => exact .inr (lwsvg_to_lwsv h)
  | pair _ _ h1 h2 => exact .pair (lwsvg_to_lwsv h1) (lwsvg_to_lwsv h2)
  | fold h => exact .fold (lwsvg_to_lwsv h)
theorem lwscg_to_lwsc {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} {c : Comp}
    (h : LWSCg K γ b c) : LWSC K b c := by
  cases h with
  | @ret _ _ _ _ q _ h => exact .ret (q := gnat q) (by simpa only [decide_gnat] using lwsvg_to_lwsv h)
  | letC _ _ h1 h2 => exact .letC (lwscg_to_lwsc h1) (lwscg_to_lwsc h2)
  | force h => exact .force (lwsvg_to_lwsv h)
  | lam h => exact .lam (lwscg_to_lwsc h)
  | @app _ _ _ _ _ _ q _ _ h1 h2 =>
      exact .app (q := gnat q) (lwscg_to_lwsc h1) (by simpa only [decide_gnat] using lwsvg_to_lwsv h2)
  | @case _ _ _ _ _ _ _ q _ _ h1 h2 h3 =>
      exact .case (q := gnat q) (by simpa only [decide_gnat] using lwsvg_to_lwsv h1)
        (lwscg_to_lwsc h2) (lwscg_to_lwsc h3)
  | @split _ _ _ _ _ _ q _ _ h1 h2 =>
      exact .split (q := gnat q) (by simpa only [decide_gnat] using lwsvg_to_lwsv h1) (lwscg_to_lwsc h2)
  | unfold h => exact .unfold (lwsvg_to_lwsv h)
  | perform _ _ h1 h2 => exact .perform (lwsvg_to_lwsv h1) (lwsvg_to_lwsv h2)
  | handleThrows h => exact .handleThrows (lwscg_to_lwsc h)
  | handleState hs h => exact .handleState (lwsvg_to_lwsv hs) (lwscg_to_lwsc h)
  | handleTransaction h => exact .handleTransaction (lwscg_to_lwsc h)
end

theorem lwskg_to_lwsk {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} :
    ∀ {Sg : EvalCtx}, LWSKg K Sg γ b → LWSK K Sg b
  | [], h => by cases h; exact .nil
  | (Frame.letF _ :: _), h => by
      cases h with | letF hN hK => exact .letF (lwscg_to_lwsc hN) (lwskg_to_lwsk hK)
  | (Frame.appF _ :: _), h => by
      cases h with
      | @appF _ _ _ _ q hv hK => exact .appF (q := q) (lwsvg_to_lwsv hv) (lwskg_to_lwsk hK)
  | (Frame.handleF _ _ :: _), h => by
      cases h with
      | handleF hK => exact .handleF (lwskg_to_lwsk hK)
      | stateF hs hK => exact .stateF (lwsvg_to_lwsv hs) (lwskg_to_lwsk hK)
      | transactionF hK => exact .transactionF (lwskg_to_lwsk hK)

/-! ### §2′.8b — the q=0 β DISCHARGE `LWSCg → γ[k]=0 → LWSCk` (the rig + false-base + induction).

`lwscg_to_lwsck` upgrades a coherent `LWSCg` to the substituted-var-`k`-dormant `LWSCk` (which feeds the
green `lwsck_subst` at the dead-arg β step). Uses the `γ[k]?.getD 0 = 0` form — `some 0` OR out-of-range
`none` (so the closed grade-`[]` handler-state value is covered with no special case). The `+`-split is
length-pinned (`hlen` on every binary former, including `letC`'s, so `k` is in-range on both summands or
neither). The rig routes `γ[k]=0` through scale-`0` nodes: `q • γ' = 0` at `k` ⟹ `q = 0` (gate ⟹ false ⟹
`lwsvg_false_lwsvk`) OR `γ'[k] = 0` (recurse); `γ_a + γ_b = 0` at `k` ⟹ both `0` (`ZeroSumFree`). -/

/-- `•`-scale preserves length (`GradeVec.smul = map`). -/
private theorem smul_length {q : Mult} {γ : GradeVec Mult} : (q • γ).length = γ.length := by
  rw [show (q • γ) = GradeVec.smul q γ from rfl, GradeVec.smul, List.length_map]

/-- `q_or_1` is never `0`: the coeffect floor (`if q = 0 then 1 else q`); `1 ≠ 0` by `Nontrivial`. -/
private theorem q_or_1_ne_zero (q : Mult) : q_or_1 q ≠ 0 := by
  unfold q_or_1; split
  · exact one_ne_zero
  · assumption

/-- `•`-scale split (`NoZeroDivisors`): a scaled grade is `0` at `k` ⟹ the scalar is `0` or the grade is.
`getD 0` form: out-of-range (`none`) reads as `0`, so the `q = 0` disjunct or the recursive one always
holds. -/
private theorem smul_getD_zero {q : Mult} {γ : GradeVec Mult} {k : Nat}
    (h : (q • γ)[k]?.getD 0 = 0) : q = 0 ∨ γ[k]?.getD 0 = 0 := by
  rw [show (q • γ) = GradeVec.smul q γ from rfl, GradeVec.smul, List.getElem?_map] at h
  cases hk : γ[k]? with
  | none => exact Or.inr (by simp)
  | some x =>
    rw [hk] at h; simp only [Option.map_some, Option.getD_some] at h
    rcases mul_eq_zero.mp h with hq | hx
    · exact Or.inl hq
    · exact Or.inr (by simpa using hx)

/-- `+`-split (`ZeroSumFree`): a sum-grade is `0` at `k` ⟹ BOTH summands are. `getD 0` form needs the
length hypothesis (`hlen`): equal lengths ⟹ `k` in range for both or neither (`none.getD 0 = 0`). -/
private theorem add_getD_zero (hzsf : ZeroSumFree Mult) {γ_a γ_b : GradeVec Mult} {k : Nat}
    (hlen : γ_a.length = γ_b.length) (h : (γ_a + γ_b)[k]?.getD 0 = 0) :
    γ_a[k]?.getD 0 = 0 ∧ γ_b[k]?.getD 0 = 0 := by
  rw [show (γ_a + γ_b) = GradeVec.add γ_a γ_b from rfl, GradeVec.add, List.getElem?_zipWith] at h
  cases ha : γ_a[k]? with
  | none =>
    have hb : γ_b[k]? = none := by rw [List.getElem?_eq_none_iff] at ha ⊢; omega
    exact ⟨by simp, by simp [hb]⟩
  | some x =>
    cases hb : γ_b[k]? with
    | none =>
      obtain ⟨hka, _⟩ := List.getElem?_eq_some_iff.mp ha
      rw [List.getElem?_eq_none_iff] at hb; omega
    | some y =>
      rw [ha, hb] at h; simp only [Option.map₂_some_some, Option.getD_some] at h
      obtain ⟨hx, hy⟩ := hzsf x y h
      exact ⟨by simpa using hx, by simpa using hy⟩

/-! THE FALSE-BASE: a dormant (`flag = false`) `LWSVg`/`LWSCg` is var-`k`-dormant (`LWSVk`/`LWSCk`) at flag
`false`, for ANY grade and `k`. This is the q=0 gate-collapse base (and `perform`'s always-dormant payload):
a dormant value carries no liveness obligation, so the grade index is irrelevant — pure structural descent. -/
mutual
theorem lwsvg_false_lwsvk {K : EvalCtx} {γ : GradeVec Mult} {v : Val} (k : Nat)
    (h : LWSVg K γ false v) : LWSVk K k false v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar _ _ i _ =>
    by_cases hik : i = k
    · subst hik; exact .vvar_k
    · exact .vvar_other hik
  | vcap_dormant => exact .vcap_dormant rfl
  | vthunk h => exact .vthunk (lwscg_false_lwsck k h)
  | inl h => exact .inl (lwsvg_false_lwsvk k h)
  | inr h => exact .inr (lwsvg_false_lwsvk k h)
  | pair _ _ h1 h2 => exact .pair (lwsvg_false_lwsvk k h1) (lwsvg_false_lwsvk k h2)
  | fold h => exact .fold (lwsvg_false_lwsvk k h)
theorem lwscg_false_lwsck {K : EvalCtx} {γ : GradeVec Mult} {c : Comp} (k : Nat)
    (h : LWSCg K γ false c) : LWSCk K k false c := by
  cases h with
  | ret _ h => exact .ret (q := 0) (lwsvg_false_lwsvk k (by simpa using h))
  | letC _ _ h1 h2 => exact .letC (lwscg_false_lwsck k h1) (lwscg_false_lwsck (k + 1) h2)
  | force h => exact .force (lwsvg_false_lwsvk k h)
  | lam h => exact .lam (lwscg_false_lwsck (k + 1) h)
  | app _ _ h1 h2 =>
      exact .app (q := 0) (lwscg_false_lwsck k h1) (lwsvg_false_lwsvk k (by simpa using h2))
  | case _ _ h1 h2 h3 =>
      exact .case (q := 0) (lwsvg_false_lwsvk k (by simpa using h1))
        (lwscg_false_lwsck (k + 1) h2) (lwscg_false_lwsck (k + 1) h3)
  | split _ _ h1 h2 =>
      exact .split (q := 0) (lwsvg_false_lwsvk k (by simpa using h1)) (lwscg_false_lwsck (k + 2) h2)
  | unfold h => exact .unfold (lwsvg_false_lwsvk k h)
  | perform _ _ h1 h2 => exact .perform (lwsvg_false_lwsvk k h1) (lwsvg_false_lwsvk k h2)
  | handleThrows h => exact .handleThrows (lwscg_false_lwsck (k + 1) h)
  | handleState hs h => exact .handleState (lwsvg_false_lwsvk k hs) (lwscg_false_lwsck (k + 1) h)
  | handleTransaction h => exact .handleTransaction (lwscg_false_lwsck (k + 1) h)
end

/-! **THE DISCHARGE.** A coherent `LWSVg`/`LWSCg` whose grade reads `0` at the substituted var `k`
(`γ[k]?.getD 0 = 0` — `some 0` or out-of-range `none`) is var-`k`-dormant (`LWSVk`/`LWSCk`). The live
`vvar k` clause is the crux: `LWSVg.vvar` demands `b = true → γ[k] ≠ 0`, which `hk` refutes, forcing
`b = false` ⟹ `vvar_k`. The `+`/`•` grade structure routes via the rig; q=0 gates drop to the false-base. -/
mutual
theorem lwsvg_to_lwsvk {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} {v : Val} (hzsf : ZeroSumFree Mult)
    (k : Nat) (hk : γ[k]?.getD 0 = 0) (h : LWSVg K γ b v) : LWSVk K k b v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar γ b i hlive =>
    by_cases hik : i = k
    · subst hik
      cases b with
      | false => exact .vvar_k
      | true => exact absurd hk (hlive rfl)
    · exact .vvar_other hik
  | vcap_live hr => exact .vcap_live hr rfl
  | vcap_dormant => exact .vcap_dormant rfl
  | vthunk h => exact .vthunk (lwscg_to_lwsck hzsf k hk h)
  | inl h => exact .inl (lwsvg_to_lwsvk hzsf k hk h)
  | inr h => exact .inr (lwsvg_to_lwsvk hzsf k hk h)
  | @pair γ γ_v γ_w b a c hγ hlen h1 h2 =>
    subst hγ
    obtain ⟨hkv, hkw⟩ := add_getD_zero hzsf hlen hk
    exact .pair (lwsvg_to_lwsvk hzsf k hkv h1) (lwsvg_to_lwsvk hzsf k hkw h2)
  | fold h => exact .fold (lwsvg_to_lwsvk hzsf k hk h)
/-- **THE DISCHARGE** (computation level). The `+`/`•` grade structure is routed by the rig: every binary
former's `hlen` feeds `add_getD_zero`; every storage `q` feeds `smul_getD_zero` (`q = 0` ⟹ the gate is
`false` ⟹ `lwsvg_false_lwsvk`; else the sub-grade is `0` ⟹ recurse). Binders shift `k`/cons the grade,
so `(x :: γ)[k+1]? = γ[k]?` re-establishes `hk`. -/
theorem lwscg_to_lwsck {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} {c : Comp} (hzsf : ZeroSumFree Mult)
    (k : Nat) (hk : γ[k]?.getD 0 = 0) (h : LWSCg K γ b c) : LWSCk K k b c := by
  cases h with
  | @ret γ γ' b v q hγ h =>
    subst hγ
    refine .ret (q := gnat q) ?_
    simp only [decide_gnat]
    rcases smul_getD_zero hk with hq | hk'
    · subst hq
      have hf : (b && decide ((0 : Mult) ≠ 0)) = false := by simp
      rw [hf]; rw [hf] at h; exact lwsvg_false_lwsvk k h
    · exact lwsvg_to_lwsvk hzsf k hk' h
  | @letC γ γ₁ γ₂ b M N q1 q2 hγ hlen h1 h2 =>
    subst hγ
    obtain ⟨hk1, hk2⟩ := add_getD_zero hzsf (by rw [smul_length]; exact hlen) hk
    rcases smul_getD_zero hk1 with hq | hk1'
    · exact absurd hq (q_or_1_ne_zero q2)
    · exact .letC (lwscg_to_lwsck hzsf k hk1' h1) (lwscg_to_lwsck hzsf (k + 1) (by simpa using hk2) h2)
  | force h => exact .force (lwsvg_to_lwsvk hzsf k hk h)
  | lam h => exact .lam (lwscg_to_lwsck hzsf (k + 1) (by simpa using hk) h)
  | @app γ γ₁ γ₂ b M v q hγ hlen h1 h2 =>
    subst hγ
    obtain ⟨hk1, hk2⟩ := add_getD_zero hzsf (by rw [smul_length]; exact hlen) hk
    refine .app (q := gnat q) (lwscg_to_lwsck hzsf k hk1 h1) ?_
    simp only [decide_gnat]
    rcases smul_getD_zero hk2 with hq | hk2'
    · subst hq
      have hf : (b && decide ((0 : Mult) ≠ 0)) = false := by simp
      rw [hf]; rw [hf] at h2; exact lwsvg_false_lwsvk k h2
    · exact lwsvg_to_lwsvk hzsf k hk2' h2
  | @case γ γ_v γ_N b v N₁ N₂ q hγ hlen h1 h2 h3 =>
    subst hγ
    obtain ⟨hkv, hkN⟩ := add_getD_zero hzsf (by rw [smul_length]; exact hlen) hk
    refine .case (q := gnat q) ?_ (lwscg_to_lwsck hzsf (k + 1) (by simpa using hkN) h2)
      (lwscg_to_lwsck hzsf (k + 1) (by simpa using hkN) h3)
    simp only [decide_gnat]
    rcases smul_getD_zero hkv with hq | hkv'
    · subst hq
      have hf : (b && decide ((0 : Mult) ≠ 0)) = false := by simp
      rw [hf]; rw [hf] at h1; exact lwsvg_false_lwsvk k h1
    · exact lwsvg_to_lwsvk hzsf k hkv' h1
  | @split γ γ_v γ_N b v N q hγ hlen h1 h2 =>
    subst hγ
    obtain ⟨hkv, hkN⟩ := add_getD_zero hzsf (by rw [smul_length]; exact hlen) hk
    refine .split (q := gnat q) ?_ (lwscg_to_lwsck hzsf (k + 2) (by simpa using hkN) h2)
    simp only [decide_gnat]
    rcases smul_getD_zero hkv with hq | hkv'
    · subst hq
      have hf : (b && decide ((0 : Mult) ≠ 0)) = false := by simp
      rw [hf]; rw [hf] at h1; exact lwsvg_false_lwsvk k h1
    · exact lwsvg_to_lwsvk hzsf k hkv' h1
  | unfold h => exact .unfold (lwsvg_to_lwsvk hzsf k hk h)
  | @perform γ γ_v γ_c b cv op v q hγ hlen h1 h2 =>
    subst hγ
    obtain ⟨_, hkc⟩ := add_getD_zero hzsf (by rw [smul_length]; exact hlen) hk
    exact .perform (lwsvg_to_lwsvk hzsf k hkc h1) (lwsvg_false_lwsvk k h2)
  | handleThrows h => exact .handleThrows (lwscg_to_lwsck hzsf (k + 1) (by simpa using hk) h)
  | handleState hs h =>
      exact .handleState (lwsvg_to_lwsvk hzsf k (by simp) hs)
        (lwscg_to_lwsck hzsf (k + 1) (by simpa using hk) h)
  | handleTransaction h => exact .handleTransaction (lwscg_to_lwsck hzsf (k + 1) (by simpa using hk) h)
end

/-! ### §2′.8c — graded FLAG-MONOTONICITY (`true` is strongest; weakens to any flag). Mirrors the typeless
`lwsv_to_dormant`/`lwsv_of_live`, grade index threaded unchanged (the gate `b && decide (q ≠ 0)` collapses
under `b := false`). Foundation for the `lwscg_subst` leaf (a live arg plugs into any occurrence flag). -/
mutual
theorem lwsvg_to_dormant {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} {v : Val}
    (h : LWSVg K γ b v) : LWSVg K γ false v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar _ => exact .vvar (by simp)
  | vcap_live _ => exact .vcap_dormant
  | vcap_dormant => exact .vcap_dormant
  | vthunk h => exact .vthunk (lwscg_to_dormant h)
  | inl h => exact .inl (lwsvg_to_dormant h)
  | inr h => exact .inr (lwsvg_to_dormant h)
  | pair hγ hlen h1 h2 => exact .pair hγ hlen (lwsvg_to_dormant h1) (lwsvg_to_dormant h2)
  | fold h => exact .fold (lwsvg_to_dormant h)
theorem lwscg_to_dormant {K : EvalCtx} {γ : GradeVec Mult} {b : Bool} {c : Comp}
    (h : LWSCg K γ b c) : LWSCg K γ false c := by
  cases h with
  | ret hγ h => exact .ret hγ (by simpa using lwsvg_to_dormant h)
  | letC hγ hlen h1 h2 => exact .letC hγ hlen (lwscg_to_dormant h1) (lwscg_to_dormant h2)
  | force h => exact .force (lwsvg_to_dormant h)
  | lam h => exact .lam (lwscg_to_dormant h)
  | app hγ hlen h1 h2 => exact .app hγ hlen (lwscg_to_dormant h1) (by simpa using lwsvg_to_dormant h2)
  | case hγ hlen h1 h2 h3 =>
      exact .case hγ hlen (by simpa using lwsvg_to_dormant h1) (lwscg_to_dormant h2) (lwscg_to_dormant h3)
  | split hγ hlen h1 h2 => exact .split hγ hlen (by simpa using lwsvg_to_dormant h1) (lwscg_to_dormant h2)
  | unfold h => exact .unfold (lwsvg_to_dormant h)
  | perform hγ hlen h1 h2 =>
      exact .perform hγ hlen (lwsvg_to_dormant h1) (lwsvg_to_dormant h2)
  | handleThrows h => exact .handleThrows (lwscg_to_dormant h)
  | handleState hs h => exact .handleState (lwsvg_to_dormant hs) (lwscg_to_dormant h)
  | handleTransaction h => exact .handleTransaction (lwscg_to_dormant h)
end

/-- A live value plugs into ANY occurrence flag (graded; `true` identity, `false` = `lwsvg_to_dormant`). -/
theorem lwsvg_of_live {K : EvalCtx} {γ : GradeVec Mult} (b : Bool) {v : Val}
    (h : LWSVg K γ true v) : LWSVg K γ b v := by
  cases b
  · exact lwsvg_to_dormant h
  · exact h


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
-- `WellCounted cfg` (= `StackBelow cfg.1 cfg.2.1`) is conjoined for MINT id-FRESHNESS (ADR-0055):
-- the carried counter dominates every live handler id, so a minted `g` can't collide. It is the
-- well-scoping of IDENTITIES — parallel to `LWSC`/`LWSK` for caps — not derivable from the
-- typing/`LWSK` (which track cap-resolution, not id-counting), so the invariant must carry it.
def WScfg (Co : CTy Eff Mult) (cfg : Config) : Prop :=
  ∃ (e : Eff) (C : CTy Eff Mult), HasCTy [] [] cfg.2.2 e C ∧ HasStack cfg.2.1 e C ⊥ Co
    ∧ LWSC cfg.2.1 true cfg.2.2 ∧ LWSK cfg.2.1 cfg.2.1 true ∧ WellCounted cfg

/-- **SEED (GREEN).** A `VcapFree` closed program satisfies the typed-relative invariant at the initial
config — no caps to resolve, the stack is empty. The typing derivations come from `hty`. -/
theorem wellScoped_initial (c : Comp) (hvf : VcapFree c) {Co : CTy Eff Mult}
    (hty : HasConfigTy (0, [], c) ⊥ Co) : WScfg Co (0, [], c) := by
  obtain ⟨e, C, hfocus, hstack⟩ := hty
  -- the stack is `[]`, so `hstack : HasStack [] e C ⊥ Co` must be `nil` (`e = ⊥`, `C = Co`).
  cases hstack
  exact ⟨⊥, Co, hfocus, .nil, lwsc_capFree [] true hfocus hvf, .nil, trivial⟩

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
  obtain ⟨e, C, dc, dk, _, _, _⟩ := h; exact ⟨e, C, dc, dk⟩

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
  obtain ⟨e, C, dc, dk, hWSC, _, _⟩ := hWS
  obtain ⟨g, K, c⟩ := cfg
  -- now `dc : HasCTy [] [] c e C`, `hWSC : LWSC K true c`; split STRUCTURALLY on the focus `c`. The
  -- cap-resolution comes from `LWSC`'s `vcap_live` gate (the focus is LIVE, `b = true`).
  cases c with
  | perform cv op v =>
      cases cv with
      | vcap n ℓ =>
          obtain ⟨Kᵢ, h, Kₒ, hsplit, hlbl⟩ := lwsc_focus_resolves hWSC
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

/-- The REMOVAL direction (reverse of `resolvesLabel_cons`, the POP arm's mechanic): a cap that resolves
in `fr :: K` resolves in `K` when `fr` is not the `handleF` for that identity. `splitAtId` walks PAST a
non-matching head, so popping it leaves resolution of every OTHER id untouched. (The popped id itself is
ruled out separately — at POP via the B-occ lever / freshness, not by this lemma.) Invariant-shape
independent: purely a `splitAtId` fact, reused by any `wsCfg_step` redesign. -/
theorem resolvesLabel_uncons (fr : Frame) {K : EvalCtx} {n : Nat} {ℓ : Label}
    (hfr : ∀ m h, fr = Frame.handleF m h → m ≠ n) (h : ResolvesLabel (fr :: K) n ℓ) :
    ResolvesLabel K n ℓ := by
  obtain ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩ := h
  cases fr with
  | letF N =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsplit
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsplit', heq⟩ := hsplit
      simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
      exact ⟨Kᵢ', h', Kₒ', hsplit', hlbl⟩
  | appF w =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsplit
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsplit', heq⟩ := hsplit
      simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
      exact ⟨Kᵢ', h', Kₒ', hsplit', hlbl⟩
  | handleF m hd =>
      have hmn : ¬ (m = n) := hfr m hd rfl
      rw [splitAtId, if_neg hmn, Option.map_eq_some_iff] at hsplit
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsplit', heq⟩ := hsplit
      simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl, rfl⟩ := heq
      exact ⟨Kᵢ', h', Kₒ', hsplit', hlbl⟩

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

/-! ### §3′.5 — TYPELESS restack (the PUSH/MINT stack mechanics; mirrors `wsv_restack` onto `LWSV`).

`LWSV`/`LWSC`/`LWSK` re-home under a pushed frame. A restack changes only the resolution context `K`,
never the flag `b` nor the per-position gate `b && decide (q ≠ 0)`, so each `vcap_live` gate's
`ResolvesLabel` survives (`resolvesLabel_cons`) and every `vcap_dormant` is inert. Two variants:
  · NON-`handleF` push (PUSH/REDUCE `letF`/`appF`): the side-condition is the blanket `fr ≠ handleF`.
  · `handleF g` push (MINT): the side-condition `g ≠ n` rides FRESHNESS — a LIVE cap resolves in `K`,
    so its id `n < g` (`stackBelow_splitAtId`), given `StackBelow g K` (the `WellCounted` witness). -/
mutual
/-- `LWSV` re-homes under a pushed non-`handleF` frame. -/
theorem lwsv_restack {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h)
    {b : Bool} {v : Val} (h : LWSV K b v) : LWSV (fr :: K) b v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap_live hg =>
      exact .vcap_live (resolvesLabel_cons fr (fun m hd he => absurd he (hfr m hd)) hg)
  | vcap_dormant => exact .vcap_dormant
  | vthunk hM => exact .vthunk (lwsc_restack fr hfr hM)
  | inl hv => exact .inl (lwsv_restack fr hfr hv)
  | inr hv => exact .inr (lwsv_restack fr hfr hv)
  | pair h1 h2 => exact .pair (lwsv_restack fr hfr h1) (lwsv_restack fr hfr h2)
  | fold hv => exact .fold (lwsv_restack fr hfr hv)
/-- `LWSC` re-homes under a pushed non-`handleF` frame. -/
theorem lwsc_restack {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h)
    {b : Bool} {c : Comp} (h : LWSC K b c) : LWSC (fr :: K) b c := by
  cases h with
  | @ret b' v' q hv => exact .ret (q := q) (lwsv_restack fr hfr hv)
  | letC h1 h2 => exact .letC (lwsc_restack fr hfr h1) (lwsc_restack fr hfr h2)
  | force hv => exact .force (lwsv_restack fr hfr hv)
  | lam hM => exact .lam (lwsc_restack fr hfr hM)
  | @app b' M' v' q h1 h2 => exact .app (q := q) (lwsc_restack fr hfr h1) (lwsv_restack fr hfr h2)
  | @case b' v' N₁' N₂' q h1 h2 h3 =>
      exact .case (q := q) (lwsv_restack fr hfr h1) (lwsc_restack fr hfr h2) (lwsc_restack fr hfr h3)
  | @split b' v' N' q h1 h2 => exact .split (q := q) (lwsv_restack fr hfr h1) (lwsc_restack fr hfr h2)
  | unfold hv => exact .unfold (lwsv_restack fr hfr hv)
  | perform h1 h2 => exact .perform (lwsv_restack fr hfr h1) (lwsv_restack fr hfr h2)
  | handleThrows hM => exact .handleThrows (lwsc_restack fr hfr hM)
  | handleState h1 h2 => exact .handleState (lwsv_restack fr hfr h1) (lwsc_restack fr hfr h2)
  | handleTransaction hM => exact .handleTransaction (lwsc_restack fr hfr hM)
end

/-- `LWSK` re-homes under a pushed non-`handleF` frame (the PUSH/REDUCE stack-extension mechanic).
Recurses on `Sg`; each frame's stored cap re-homes via `lwsv_restack`/`lwsc_restack`. -/
theorem lwsk_restack {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h) :
    ∀ {Sg : EvalCtx} {b : Bool}, LWSK K Sg b → LWSK (fr :: K) Sg b
  | [], _, h => by cases h; exact .nil
  | (Frame.letF _ :: _), _, h => by
      cases h with | letF hN hK => exact .letF (lwsc_restack fr hfr hN) (lwsk_restack fr hfr hK)
  | (Frame.appF _ :: _), _, h => by
      cases h with
      | @appF _ _ _ q hv hK => exact .appF (q := q) (lwsv_restack fr hfr hv) (lwsk_restack fr hfr hK)
  | (Frame.handleF _ _ :: _), _, h => by
      cases h with
      | handleF hK => exact .handleF (lwsk_restack fr hfr hK)
      | stateF hs hK => exact .stateF (lwsv_restack fr hfr hs) (lwsk_restack fr hfr hK)
      | transactionF hK => exact .transactionF (lwsk_restack fr hfr hK)

mutual
/-- `LWSV` re-homes under a pushed `handleF g` (the MINT mechanic). Every LIVE cap resolves in `K`, so
its id `n < g` (`stackBelow_splitAtId hsb`) ⇒ `g ≠ n` ⇒ `resolvesLabel_cons` fires. `StackBelow g K`
is the freshness side-condition (supplied by `WellCounted` at the MINT step). -/
theorem lwsv_restack_handleF (g : Nat) (hd : Handler) {K : EvalCtx} (hsb : StackBelow g K)
    {b : Bool} {v : Val} (h : LWSV K b v) : LWSV (Frame.handleF g hd :: K) b v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap_live hg =>
      obtain ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩ := hg
      have hn := (stackBelow_splitAtId hsb hsplit).2.1
      exact .vcap_live (resolvesLabel_cons (Frame.handleF g hd)
        (fun m hd' he => by injection he with hmg _; omega) ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩)
  | vcap_dormant => exact .vcap_dormant
  | vthunk hM => exact .vthunk (lwsc_restack_handleF g hd hsb hM)
  | inl hv => exact .inl (lwsv_restack_handleF g hd hsb hv)
  | inr hv => exact .inr (lwsv_restack_handleF g hd hsb hv)
  | pair h1 h2 => exact .pair (lwsv_restack_handleF g hd hsb h1) (lwsv_restack_handleF g hd hsb h2)
  | fold hv => exact .fold (lwsv_restack_handleF g hd hsb hv)
/-- `LWSC` re-homes under a pushed `handleF g` (the MINT mechanic; freshness companion to `lwsc_restack`). -/
theorem lwsc_restack_handleF (g : Nat) (hd : Handler) {K : EvalCtx} (hsb : StackBelow g K)
    {b : Bool} {c : Comp} (h : LWSC K b c) : LWSC (Frame.handleF g hd :: K) b c := by
  cases h with
  | @ret b' v' q hv => exact .ret (q := q) (lwsv_restack_handleF g hd hsb hv)
  | letC h1 h2 => exact .letC (lwsc_restack_handleF g hd hsb h1) (lwsc_restack_handleF g hd hsb h2)
  | force hv => exact .force (lwsv_restack_handleF g hd hsb hv)
  | lam hM => exact .lam (lwsc_restack_handleF g hd hsb hM)
  | @app b' M' v' q h1 h2 =>
      exact .app (q := q) (lwsc_restack_handleF g hd hsb h1) (lwsv_restack_handleF g hd hsb h2)
  | @case b' v' N₁' N₂' q h1 h2 h3 =>
      exact .case (q := q) (lwsv_restack_handleF g hd hsb h1) (lwsc_restack_handleF g hd hsb h2)
        (lwsc_restack_handleF g hd hsb h3)
  | @split b' v' N' q h1 h2 =>
      exact .split (q := q) (lwsv_restack_handleF g hd hsb h1) (lwsc_restack_handleF g hd hsb h2)
  | unfold hv => exact .unfold (lwsv_restack_handleF g hd hsb hv)
  | perform h1 h2 => exact .perform (lwsv_restack_handleF g hd hsb h1) (lwsv_restack_handleF g hd hsb h2)
  | handleThrows hM => exact .handleThrows (lwsc_restack_handleF g hd hsb hM)
  | handleState h1 h2 => exact .handleState (lwsv_restack_handleF g hd hsb h1) (lwsc_restack_handleF g hd hsb h2)
  | handleTransaction hM => exact .handleTransaction (lwsc_restack_handleF g hd hsb hM)
end

/-- `LWSK` re-homes under a pushed `handleF g` (the MINT stack-extension mechanic). The new `handleF g`
frame is added by `LWSK.handleF`/`.stateF`/`.transactionF` at the assembly; this re-homes the OLD tail. -/
theorem lwsk_restack_handleF (g : Nat) (hd : Handler) {K : EvalCtx} (hsb : StackBelow g K) :
    ∀ {Sg : EvalCtx} {b : Bool}, LWSK K Sg b → LWSK (Frame.handleF g hd :: K) Sg b
  | [], _, h => by cases h; exact .nil
  | (Frame.letF _ :: _), _, h => by
      cases h with
      | letF hN hK => exact .letF (lwsc_restack_handleF g hd hsb hN) (lwsk_restack_handleF g hd hsb hK)
  | (Frame.appF _ :: _), _, h => by
      cases h with
      | @appF _ _ _ q hv hK =>
          exact .appF (q := q) (lwsv_restack_handleF g hd hsb hv) (lwsk_restack_handleF g hd hsb hK)
  | (Frame.handleF _ _ :: _), _, h => by
      cases h with
      | handleF hK => exact .handleF (lwsk_restack_handleF g hd hsb hK)
      | stateF hs hK =>
          exact .stateF (lwsv_restack_handleF g hd hsb hs) (lwsk_restack_handleF g hd hsb hK)
      | transactionF hK => exact .transactionF (lwsk_restack_handleF g hd hsb hK)

/-! ### §3′.5b — TYPELESS UNCONS (the REDUCE pop mechanic; the MIRROR of `lwsv_restack`).

A cap resolving under a pushed NON-`handleF` frame still resolves once that frame is popped
(`resolvesLabel_uncons` — `splitAtId` walks PAST a transparent head), so `LWSV`/`LWSC`/`LWSK` re-home
DOWN past a `letF`/`appF` frame. This is the REDUCE direction (the continuation/stack drops back to the
popped stack after a `ret`/`lam` β). `handleF` is EXCLUDED — popping a real handler can break a cap that
resolved to it (the POP-escape arm, handled separately). The exact reverse of the restack family. -/
mutual
/-- `LWSV` re-homes DOWN past a popped non-`handleF` frame. -/
theorem lwsv_uncons {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h)
    {b : Bool} {v : Val} (h : LWSV (fr :: K) b v) : LWSV K b v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar => exact .vvar
  | vcap_live hg => exact .vcap_live (resolvesLabel_uncons fr (fun m hd he => absurd he (hfr m hd)) hg)
  | vcap_dormant => exact .vcap_dormant
  | vthunk hM => exact .vthunk (lwsc_uncons fr hfr hM)
  | inl hv => exact .inl (lwsv_uncons fr hfr hv)
  | inr hv => exact .inr (lwsv_uncons fr hfr hv)
  | pair h1 h2 => exact .pair (lwsv_uncons fr hfr h1) (lwsv_uncons fr hfr h2)
  | fold hv => exact .fold (lwsv_uncons fr hfr hv)
/-- `LWSC` re-homes DOWN past a popped non-`handleF` frame. -/
theorem lwsc_uncons {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h)
    {b : Bool} {c : Comp} (h : LWSC (fr :: K) b c) : LWSC K b c := by
  cases h with
  | @ret b' v' q hv => exact .ret (q := q) (lwsv_uncons fr hfr hv)
  | letC h1 h2 => exact .letC (lwsc_uncons fr hfr h1) (lwsc_uncons fr hfr h2)
  | force hv => exact .force (lwsv_uncons fr hfr hv)
  | lam hM => exact .lam (lwsc_uncons fr hfr hM)
  | @app b' M' v' q h1 h2 => exact .app (q := q) (lwsc_uncons fr hfr h1) (lwsv_uncons fr hfr h2)
  | @case b' v' N₁' N₂' q h1 h2 h3 =>
      exact .case (q := q) (lwsv_uncons fr hfr h1) (lwsc_uncons fr hfr h2) (lwsc_uncons fr hfr h3)
  | @split b' v' N' q h1 h2 => exact .split (q := q) (lwsv_uncons fr hfr h1) (lwsc_uncons fr hfr h2)
  | unfold hv => exact .unfold (lwsv_uncons fr hfr hv)
  | perform h1 h2 => exact .perform (lwsv_uncons fr hfr h1) (lwsv_uncons fr hfr h2)
  | handleThrows hM => exact .handleThrows (lwsc_uncons fr hfr hM)
  | handleState h1 h2 => exact .handleState (lwsv_uncons fr hfr h1) (lwsc_uncons fr hfr h2)
  | handleTransaction hM => exact .handleTransaction (lwsc_uncons fr hfr hM)
end

/-- `LWSK` re-homes DOWN past a popped non-`handleF` frame (the REDUCE tail-uncons mechanic). -/
theorem lwsk_uncons {K : EvalCtx} (fr : Frame) (hfr : ∀ m h, fr ≠ Frame.handleF m h) :
    ∀ {Sg : EvalCtx} {b : Bool}, LWSK (fr :: K) Sg b → LWSK K Sg b
  | [], _, h => by cases h; exact .nil
  | (Frame.letF _ :: _), _, h => by
      cases h with | letF hN hK => exact .letF (lwsc_uncons fr hfr hN) (lwsk_uncons fr hfr hK)
  | (Frame.appF _ :: _), _, h => by
      cases h with
      | @appF _ _ _ q hv hK => exact .appF (q := q) (lwsv_uncons fr hfr hv) (lwsk_uncons fr hfr hK)
  | (Frame.handleF _ _ :: _), _, h => by
      cases h with
      | handleF hK => exact .handleF (lwsk_uncons fr hfr hK)
      | stateF hs hK => exact .stateF (lwsv_uncons fr hfr hs) (lwsk_uncons fr hfr hK)
      | transactionF hK => exact .transactionF (lwsk_uncons fr hfr hK)

/-- The `Sgrade` BINDER law: descending under a binder shifts the cutoff `k → k+1`, conses the body grade
(`q :: γ`), and shifts the substituted value's grade (`γ_v → 0 :: γ_v`, the `shift v` slot it doesn't use).
`Sgrade` commutes with that cons — the spine of every binder arm of `lwscg_subst`. -/
theorem Sgrade_cons (γ_v : GradeVec Mult) (k : Nat) (q : Mult) (γ : GradeVec Mult) :
    Sgrade (0 :: γ_v) (k + 1) (q :: γ) = q :: Sgrade γ_v k γ := by
  unfold Sgrade slotGrade
  rw [List.eraseIdx_cons_succ, List.getElem?_cons_succ]
  show GradeVec.add (q :: γ.eraseIdx k) (GradeVec.smul _ (0 :: γ_v))
    = q :: GradeVec.add (γ.eraseIdx k) (GradeVec.smul _ γ_v)
  rw [GradeVec.smul, List.map_cons, mul_zero]
  rw [GradeVec.add, List.zipWith_cons_cons, add_zero]
  rfl

/-! ### §2′.8c — the LENGTH-FREE `Sgrade` rig for `lwscg_subst`.

The typeless `LWSCg` carries no `k < γ.length` pin (the `[]`-graded handler-state value forces
`k` out of range under that sub-tree), so the length-BEARING Metatheory `Sgrade_add`/`slotGrade_add`
(which demand `k < γ.length`) cannot be used directly. These length-free analogues need only the
constructor's own `hlen` (the binary formers carry `γ₁.length = γ₂.length`). The substitution
induction threads a COVERAGE invariant `(γ.eraseIdx k).length ≤ γ_v.length` (the value's grade
covers the post-erase context) — which threads through every binder/binary node and is `0 ≤ _`
free at the `[]`-graded handler-state leaf. `Sgrade_smul` is already length-free (Metatheory).

NON-CANCELLATIVITY NOTE (constrains any future grade-REINDEX): `Mult` is `[CommSemiring]
[NoZeroDivisors] [Nontrivial]` — NOT cancellative (concrete QTT: `ω·1 = ω = ω·ω`, `1 ≠ ω`; no
`CancelCommMonoidWithZero`). So a closed value's `LWSVg` is NOT freely transportable across grades
by un-scaling a `ret`/`app` budget (`q•x = q•y ⇏ x = y`); and over this rig `1` is not a sum of two
non-zeros, so a shared bound var (`pair (vvar 0)(vvar 0)`) needs its binder slot graded the literal
occurrence sum, not a reused unit. This is why the `∀γ'b'` closed-arg builder (`lwscg_subst`'s `hvl`,
the consumer's job) is a genuine occurrence-count construction, not a grade-irrelevance one-liner. -/

/-- Length-free `slotGrade`/`+` split: equal lengths ⇒ `k` in range for both summands or neither. -/
theorem slotGrade_add_free {γ₁ γ₂ : GradeVec Mult} {k : Nat} (hlen : γ₁.length = γ₂.length) :
    slotGrade (GradeVec.add γ₁ γ₂) k = slotGrade γ₁ k + slotGrade γ₂ k := by
  unfold slotGrade
  rw [GradeVec.add, List.getElem?_zipWith]
  cases ha : γ₁[k]? with
  | none =>
    have hb : γ₂[k]? = none := by rw [List.getElem?_eq_none_iff] at ha ⊢; omega
    rw [hb]; simp
  | some a =>
    cases hb : γ₂[k]? with
    | none =>
      obtain ⟨hka, _⟩ := List.getElem?_eq_some_iff.mp ha
      rw [List.getElem?_eq_none_iff] at hb; omega
    | some b => simp

/-- Length-free `Sgrade`/`+` distribution (needs only `γ₁.length = γ₂.length`). -/
theorem Sgrade_add_free (γ_v : GradeVec Mult) (k : Nat) {γ₁ γ₂ : GradeVec Mult}
    (hlen : γ₁.length = γ₂.length) :
    Sgrade γ_v k (GradeVec.add γ₁ γ₂)
      = GradeVec.add (Sgrade γ_v k γ₁) (Sgrade γ_v k γ₂) := by
  unfold Sgrade
  apply List.ext_getElem?
  intro j
  rw [GradeVec.eraseIdx_add _ _ _ hlen, slotGrade_add_free hlen]
  simp only [GradeVec.add, GradeVec.smul, List.getElem?_zipWith, List.getElem?_map]
  rcases (γ₁.eraseIdx k)[j]? with _ | x <;> rcases (γ₂.eraseIdx k)[j]? with _ | y <;>
    rcases γ_v[j]? with _ | z <;>
    simp [add_comm, add_left_comm, add_assoc, add_mul]

/-- `Sgrade`/`•` in the `HSMul` notation the `LWSCg` constructors use (so `rw` matches `q • γ`). -/
theorem Sgrade_hsmul (γ_v : GradeVec Mult) (k : Nat) (q : Mult) (γ : GradeVec Mult) :
    Sgrade γ_v k (q • γ) = q • Sgrade γ_v k γ := Sgrade_smul γ_v k q γ

/-- `Sgrade`/`+` in the `HAdd` notation the `LWSCg` constructors use (so `rw` matches `γ₁ + γ₂`). -/
theorem Sgrade_hadd (γ_v : GradeVec Mult) (k : Nat) {γ₁ γ₂ : GradeVec Mult}
    (hlen : γ₁.length = γ₂.length) :
    Sgrade γ_v k (γ₁ + γ₂) = Sgrade γ_v k γ₁ + Sgrade γ_v k γ₂ := Sgrade_add_free γ_v k hlen

/-- `•` length in `HSMul` notation (so the `hlen_s` side-conditions match the constructors' `q • γ`). -/
theorem smul_hlength (q : Mult) (γ : GradeVec Mult) : (q • γ).length = γ.length :=
  GradeVec.smul_length q γ

/-- `Sgrade` of the empty grade is empty (the closed handler-state leaf). -/
theorem Sgrade_nil (γ_v : GradeVec Mult) (k : Nat) :
    Sgrade γ_v k ([] : GradeVec Mult) = [] := by
  unfold Sgrade; rw [GradeVec.add]; simp

/-- `Sgrade` length depends on `γ` only through its length, so equal-length grades give equal
`Sgrade` lengths — the `hlen` reconstructed at each binary former. -/
theorem Sgrade_length_eq (γ_v : GradeVec Mult) (k : Nat) {γ₁ γ₂ : GradeVec Mult}
    (hlen : γ₁.length = γ₂.length) :
    (Sgrade γ_v k γ₁).length = (Sgrade γ_v k γ₂).length := by
  unfold Sgrade
  simp only [GradeVec.add_length, GradeVec.smul_length, List.length_eraseIdx, hlen]

/-- THE `vvar` LEAF (`ZeroSumFree`): a body variable that SURVIVES the erase (its grade slot is
non-zero in `γ.eraseIdx k`) stays non-zero in `Sgrade γ_v k γ`. The added `slotGrade • γ_v` slot is
in range (coverage `hcov`), so `a + β` with `a ≠ 0` is non-zero by `ZeroSumFree`. -/
theorem Sgrade_vvar_ne (hzsf : ZeroSumFree Mult) {γ γ_v : GradeVec Mult} {k i' : Nat}
    (hcov : (γ.eraseIdx k).length ≤ γ_v.length)
    (hsurv : ((γ.eraseIdx k)[i']?).getD 0 ≠ 0) :
    ((Sgrade γ_v k γ)[i']?).getD 0 ≠ 0 := by
  unfold Sgrade
  rw [GradeVec.add, List.getElem?_zipWith]
  cases hA : (γ.eraseIdx k)[i']? with
  | none => rw [hA] at hsurv; simp at hsurv
  | some a =>
    have ha : a ≠ 0 := by rw [hA] at hsurv; simpa using hsurv
    have hi'A : i' < (γ.eraseIdx k).length := (List.getElem?_eq_some_iff.mp hA).1
    have hi'v : i' < γ_v.length := lt_of_lt_of_le hi'A hcov
    have hB : (GradeVec.smul (slotGrade γ k) γ_v)[i']?
        = some (slotGrade γ k * γ_v[i']) := by
      rw [GradeVec.smul, List.getElem?_map, List.getElem?_eq_getElem hi'v]; rfl
    rw [hB]
    simp only [Option.map₂_some_some, Option.getD_some]
    intro hsum
    exact ha (hzsf a (slotGrade γ k * γ_v[i']) hsum).1

/-! ### §2′.8d — COVERAGE threading helpers. The substitution induction maintains
`(γ.eraseIdx k).length ≤ γ_v.length` (the value's grade covers the post-erase context). Each
former transfers it to its sub-derivations: `+`-left/right (equal-length summands ⇒ same erase
length), `•` (length-preserving), and `::` (descend a binder: both sides grow by one). -/

/-- Transfer coverage to the left summand of a `+`. -/
theorem cov_add_left {γ_a γ_b γ_v : GradeVec Mult} {k : Nat} (hlen : γ_a.length = γ_b.length)
    (hcov : ((GradeVec.add γ_a γ_b).eraseIdx k).length ≤ γ_v.length) :
    (γ_a.eraseIdx k).length ≤ γ_v.length := by
  rw [List.length_eraseIdx]
  rwa [List.length_eraseIdx, GradeVec.add_length, ← hlen, Nat.min_self] at hcov

/-- Transfer coverage to the right summand of a `+`. -/
theorem cov_add_right {γ_a γ_b γ_v : GradeVec Mult} {k : Nat} (hlen : γ_a.length = γ_b.length)
    (hcov : ((GradeVec.add γ_a γ_b).eraseIdx k).length ≤ γ_v.length) :
    (γ_b.eraseIdx k).length ≤ γ_v.length := by
  rw [List.length_eraseIdx]
  rwa [List.length_eraseIdx, GradeVec.add_length, hlen, Nat.min_self] at hcov

/-- Transfer coverage through a `•` (length-preserving). -/
theorem cov_smul {q : Mult} {γ' γ_v : GradeVec Mult} {k : Nat}
    (hcov : ((GradeVec.smul q γ').eraseIdx k).length ≤ γ_v.length) :
    (γ'.eraseIdx k).length ≤ γ_v.length := by
  rw [List.length_eraseIdx]
  rwa [List.length_eraseIdx, GradeVec.smul_length] at hcov

omit [DecidableEq Mult] [NoZeroDivisors Mult] [Nontrivial Mult] in
/-- Descend a binder: coverage at `γ` ⇒ coverage at `q :: γ`, cutoff `k+1`, value grade `0 :: γ_v`. -/
theorem cov_cons {q : Mult} {γ_par γ_v : GradeVec Mult} {k : Nat}
    (hcov : (γ_par.eraseIdx k).length ≤ γ_v.length) :
    ((q :: γ_par).eraseIdx (k + 1)).length ≤ (0 :: γ_v).length := by
  rw [List.eraseIdx_cons_succ, List.length_cons, List.length_cons]; omega

/-! ### §2′.8e — THE MUTUAL substitution induction (general cutoff `k`, value grade `γ_v`).

Mirrors the typeless `lwsv_subst`/`lwsc_subst` (≈12 + ≈12 arms) but tracks the grade transform
`Sgrade γ_v k γ`. The `vvar k` (substituted) leaf is the DIRECT `hvl (Sgrade …) bu`; a surviving
body var stays live by `Sgrade_vvar_ne` (ZeroSumFree); binders cons the grade via `Sgrade_cons`
and the value's shift collapses via `hcl`. The `k = 0` corollary `lwscg_subst` follows. -/
mutual
theorem lwsvg_subst_gen {K : EvalCtx} {v : Val}
    (hvl : ∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg K γ' b' v)
    (hcl : ∀ j, Val.shiftFrom j v = v) (hzsf : ZeroSumFree Mult)
    (γ_v : GradeVec Mult) (k : Nat) {γ : GradeVec Mult} {bu : Bool} {u : Val}
    (hcov : (γ.eraseIdx k).length ≤ γ_v.length)
    (hu : LWSVg K γ bu u) :
    LWSVg K (Sgrade γ_v k γ) bu (Val.substFrom k v u) := by
  cases hu with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar _ _ i hgate =>
    simp only [Val.substFrom]
    by_cases hik : i = k
    · rw [if_pos hik]; exact hvl (Sgrade γ_v k γ) bu
    · rw [if_neg hik]
      by_cases hgt : i > k
      · rw [if_pos hgt]
        refine .vvar (fun hb => Sgrade_vvar_ne hzsf hcov ?_)
        rw [List.getElem?_eraseIdx, if_neg (by omega : ¬ (i - 1 < k)), show i - 1 + 1 = i from by omega]
        exact hgate hb
      · rw [if_neg hgt]
        refine .vvar (fun hb => Sgrade_vvar_ne hzsf hcov ?_)
        rw [List.getElem?_eraseIdx, if_pos (by omega : i < k)]
        exact hgate hb
  | vcap_live h => simp only [Val.substFrom]; exact .vcap_live h
  | vcap_dormant => simp only [Val.substFrom]; exact .vcap_dormant
  | vthunk h => exact .vthunk (lwscg_subst_gen hvl hcl hzsf γ_v k hcov h)
  | inl h => exact .inl (lwsvg_subst_gen hvl hcl hzsf γ_v k hcov h)
  | inr h => exact .inr (lwsvg_subst_gen hvl hcl hzsf γ_v k hcov h)
  | @pair γ γ_a γ_b b a w hγ hlen h1 h2 =>
    simp only [Val.substFrom]
    subst hγ
    exact .pair (Sgrade_add_free γ_v k hlen) (Sgrade_length_eq γ_v k hlen)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_add_left hlen hcov) h1)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_add_right hlen hcov) h2)
  | fold h => exact .fold (lwsvg_subst_gen hvl hcl hzsf γ_v k hcov h)
theorem lwscg_subst_gen {K : EvalCtx} {v : Val}
    (hvl : ∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg K γ' b' v)
    (hcl : ∀ j, Val.shiftFrom j v = v) (hzsf : ZeroSumFree Mult)
    (γ_v : GradeVec Mult) (k : Nat) {γ : GradeVec Mult} {bc : Bool} {c : Comp}
    (hcov : (γ.eraseIdx k).length ≤ γ_v.length)
    (hc : LWSCg K γ bc c) :
    LWSCg K (Sgrade γ_v k γ) bc (Comp.substFrom k v c) := by
  have hsh : Val.shift v = v := hcl 0
  cases hc with
  | @ret γ γ' b w q hγ h =>
    simp only [Comp.substFrom]
    subst hγ
    rw [Sgrade_hsmul]
    exact .ret (q := q) rfl (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_smul hcov) h)
  | @letC γ γ₁ γ₂ b M N q1 q2 hγ hlen h1 h2 =>
    simp only [Comp.substFrom, hsh]
    subst hγ
    have hlen_s : ((q_or_1 q2) • γ₁).length = γ₂.length := by
      rw [smul_hlength]; exact hlen
    rw [Sgrade_hadd γ_v k hlen_s, Sgrade_hsmul]
    have ih2 := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1)
      (cov_cons (cov_add_right hlen_s hcov)) h2
    rw [Sgrade_cons] at ih2
    exact .letC (q1 := q1) (q2 := q2) rfl (Sgrade_length_eq γ_v k hlen)
      (lwscg_subst_gen hvl hcl hzsf γ_v k (cov_smul (cov_add_left hlen_s hcov)) h1) ih2
  | force h => exact .force (lwsvg_subst_gen hvl hcl hzsf γ_v k hcov h)
  | @lam γ b M q h =>
    simp only [Comp.substFrom, hsh]
    have ih := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1) (cov_cons hcov) h
    rw [Sgrade_cons] at ih
    exact .lam (q := q) ih
  | @app γ γ₁ γ₂ b M w q hγ hlen h1 h2 =>
    simp only [Comp.substFrom]
    subst hγ
    have hlen_s : γ₁.length = (q • γ₂).length := by
      rw [smul_hlength]; exact hlen
    rw [Sgrade_hadd γ_v k hlen_s, Sgrade_hsmul]
    exact .app (q := q) rfl (Sgrade_length_eq γ_v k hlen)
      (lwscg_subst_gen hvl hcl hzsf γ_v k (cov_add_left hlen_s hcov) h1)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_smul (cov_add_right hlen_s hcov)) h2)
  | @case γ γ_s γ_N b w N₁ N₂ q hγ hlen h1 h2 h3 =>
    simp only [Comp.substFrom, hsh]
    subst hγ
    have hlen_s : (q • γ_s).length = γ_N.length := by
      rw [smul_hlength]; exact hlen
    rw [Sgrade_hadd γ_v k hlen_s, Sgrade_hsmul]
    have ih2 := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1)
      (cov_cons (cov_add_right hlen_s hcov)) h2
    have ih3 := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1)
      (cov_cons (cov_add_right hlen_s hcov)) h3
    rw [Sgrade_cons] at ih2 ih3
    exact .case (q := q) rfl (Sgrade_length_eq γ_v k hlen)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_smul (cov_add_left hlen_s hcov)) h1) ih2 ih3
  | @split γ γ_s γ_N b w N q hγ hlen h1 h2 =>
    simp only [Comp.substFrom, hsh]
    subst hγ
    have hlen_s : (q • γ_s).length = γ_N.length := by
      rw [smul_hlength]; exact hlen
    rw [Sgrade_hadd γ_v k hlen_s, Sgrade_hsmul]
    have ih2 := lwscg_subst_gen hvl hcl hzsf (0 :: 0 :: γ_v) (k + 2)
      (cov_cons (cov_cons (cov_add_right hlen_s hcov))) h2
    rw [Sgrade_cons, Sgrade_cons] at ih2
    exact .split (q := q) rfl (Sgrade_length_eq γ_v k hlen)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_smul (cov_add_left hlen_s hcov)) h1) ih2
  | unfold h => exact .unfold (lwsvg_subst_gen hvl hcl hzsf γ_v k hcov h)
  | @perform γ γ_s γ_c b cv op w q hγ hlen h1 h2 =>
    simp only [Comp.substFrom]
    subst hγ
    have hlen_s : (q • γ_s).length = γ_c.length := by
      rw [smul_hlength]; exact hlen
    rw [Sgrade_hadd γ_v k hlen_s, Sgrade_hsmul]
    exact .perform (q := q) rfl (Sgrade_length_eq γ_v k hlen)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_add_right hlen_s hcov) h1)
      (lwsvg_subst_gen hvl hcl hzsf γ_v k (cov_smul (cov_add_left hlen_s hcov)) h2)
  | @handleThrows γ b ℓ M qc h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    have ih := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1) (cov_cons hcov) h
    rw [Sgrade_cons] at ih
    exact .handleThrows (qc := qc) ih
  | @handleState γ b ℓ s M qc hs h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    have ihs := lwsvg_subst_gen hvl hcl hzsf γ_v k (by simp) hs
    rw [Sgrade_nil] at ihs
    have ih := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1) (cov_cons hcov) h
    rw [Sgrade_cons] at ih
    exact .handleState (qc := qc) ihs ih
  | @handleTransaction γ b ℓ Θ M qc h =>
    simp only [Comp.substFrom, Handler.substFrom, hsh]
    have ih := lwscg_subst_gen hvl hcl hzsf (0 :: γ_v) (k + 1) (cov_cons hcov) h
    rw [Sgrade_cons] at ih
    exact .handleTransaction (qc := qc) ih
end

/-- **coh_step / `lwscg_subst`** — the graded (Coh-layer) substitution-preservation consumed by the
REDUCE/MINT/DISPATCH arms of `wsCfg_step`. The graded mirror of `subst_value_proof` (Metatheory): a closed
value `v` substituted for var `0` of a body `c` graded `ρ :: γ` yields `Comp.subst v c` graded
`γ + ρ • γ_v`, preserving the reachability flag `b`. The `ρ = 0` (dead-arg) case is handled SEPARATELY by
the discharge `lwscg_to_lwsck` + the typeless `lwsck_subst`; this is the live companion (`ρ ≠ 0`).

WELL-SCOPING HYPOTHESIS (the reshape): `v` is well-scoped at ANY grade/flag (`∀ γ' b', LWSVg K γ' b' v`).
The substituted `v` occurs ONLY at the `vvar k` leaves, so quantifying its scoping over the grade index
DISSOLVES the closed-value REGRADE that the fixed-grade form (`LWSVg K γ_v true v`) forced at the leaf —
the leaf becomes a direct application of `hvl`. The obligation that a CLOSED value satisfies this `∀`-form
is RELOCATED to the consumer: a forward-build-from-typing (`HasCTy → LWSVg`), the natural content of the
deferred lift (#46), NOT a regrade transform here.

TWO MATHEMATICALLY-FORCED HYPOTHESES (both ambient in the consumer via the typing's `length_eq`):
  • `hzsf : ZeroSumFree Mult` — a SURVIVING body var (`γ[i] ≠ 0`) stays live after the subst-add
    (`a + b ≠ 0` from `a ≠ 0`), the contrapositive of `ZeroSumFree`.
  • `hlen_v : γ_v.length = γ.length` — WITHOUT it the statement is FALSE (`Bang/LwscgLengthRefute`,
    machine-checked): the truncating `GradeVec.add` (`zipWith`) drops a live body var's grade slot when
    `γ_v` is shorter, and `force` has no `q`-gate to absorb it. The typed template carries this pin
    for free (`HasVTy γ_v Γ` + `HasCTy (ρ::γ) (A::Γ)`); the typeless port restores it explicitly.

PROOF: the `k = 0` corollary of the mutual `lwsvg_subst_gen`/`lwscg_subst_gen` above, at
`Sgrade γ_v 0 (ρ :: γ) = γ + ρ • γ_v`. -/
theorem lwscg_subst (hzsf : ZeroSumFree Mult)
    {K : EvalCtx} {ρ : Mult} {γ γ_v : GradeVec Mult} {b : Bool} {v : Val} {c : Comp}
    (hvl : ∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg K γ' b' v) (hcl : ∀ j, Val.shiftFrom j v = v)
    (hlen_v : γ_v.length = γ.length)
    (hc : LWSCg K (ρ :: γ) b c) :
    LWSCg K (γ + ρ • γ_v) b (Comp.subst v c) := by
  have hcov : (((ρ :: γ).eraseIdx 0).length) ≤ γ_v.length := by
    show (γ.length) ≤ γ_v.length
    exact le_of_eq hlen_v.symm
  have ih := lwscg_subst_gen hvl hcl hzsf γ_v 0 hcov hc
  have hSg : Sgrade γ_v 0 (ρ :: γ) = γ + ρ • γ_v := by
    show GradeVec.add ((ρ :: γ).eraseIdx 0) (GradeVec.smul (slotGrade (ρ :: γ) 0) γ_v) = γ + ρ • γ_v
    rfl
  rw [hSg] at ih
  exact ih

/-! ### §2′.8f — THE CONSUMER BRIDGE: the EXISTENCE-lift `HasVTy`/`HasCTy` ∧ caps-resolve → `LWSVg`/`LWSCg`.

McDermott "Grading CBPV" §6 (FSCD'25): the lift is the EXISTENCE direction — produce ONE graded
witness at `HasCTy`'s canonical grade — NOT the coherence ⊤⊤-LR. Cap-resolution is supplied as a
SEPARATE side-condition (`∀ cap ∈ caps, ResolvesLabel K`), NOT recovered from the forgetful `LWSC`
(whose existential `q'=0` storage gates lose it — machine-refuted, `scratch/LwscgOfTypedRefute`).
Each arm reads the grade decomposition from the typing rule + supplies `LWSCg`'s (looser) constructor;
the `vcap` leaf discharges `vcap_live` from caps-resolve; per-node `hlen`s come from `length_eq`. -/

/-- caps-resolve transfers to the left of an append. -/
theorem capsR_left {K : EvalCtx} {a b : List (Nat × Label)}
    (h : ∀ p ∈ a ++ b, ResolvesLabel K p.1 p.2) : ∀ p ∈ a, ResolvesLabel K p.1 p.2 :=
  fun p hp => h p (List.mem_append_left b hp)

/-- caps-resolve transfers to the right of an append. -/
theorem capsR_right {K : EvalCtx} {a b : List (Nat × Label)}
    (h : ∀ p ∈ a ++ b, ResolvesLabel K p.1 p.2) : ∀ p ∈ b, ResolvesLabel K p.1 p.2 :=
  fun p hp => h p (List.mem_append_right a hp)

mutual
/-- value lift: a well-typed value whose caps resolve in `K` is `LWSVg` at its typed grade, any flag. -/
theorem lwsvg_of_typed {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val}
    {A : VTy Eff Mult} (b : Bool) (d : HasVTy γ Γ v A)
    (hcaps : ∀ p ∈ capsV v, ResolvesLabel K p.1 p.2) : LWSVg K γ b v := by
  cases d with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar Γ i A hget =>
    refine .vvar (fun _ => ?_)
    have hi : i < Γ.length := by rw [List.getElem?_eq_some_iff] at hget; exact hget.1
    rw [GradeVec.basis_getElem _ _ _ hi, if_pos rfl]
    exact one_ne_zero
  | @vcap Γ n ℓ =>
    cases b with
    | true => exact .vcap_live (hcaps (n, ℓ) (by simp [capsV]))
    | false => exact .vcap_dormant
  | vthunk hM => exact .vthunk (lwscg_of_typed b hM (by simpa only [capsV] using hcaps))
  | inl hv => exact .inl (lwsvg_of_typed b hv (by simpa only [capsV] using hcaps))
  | inr hv => exact .inr (lwsvg_of_typed b hv (by simpa only [capsV] using hcaps))
  | @pair γ γ_v γ_w Γ a w A B hv hw hγ =>
    subst hγ
    simp only [capsV] at hcaps
    exact .pair rfl (by rw [hv.length_eq, hw.length_eq])
      (lwsvg_of_typed b hv (capsR_left hcaps)) (lwsvg_of_typed b hw (capsR_right hcaps))
  | fold hv => exact .fold (lwsvg_of_typed b hv (by simpa only [capsV] using hcaps))
/-- comp lift: a well-typed comp whose caps resolve in `K` is `LWSCg` at its typed grade, any flag. -/
theorem lwscg_of_typed {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp}
    {φ : Eff} {C : CTy Eff Mult} (b : Bool) (d : HasCTy γ Γ c φ C)
    (hcaps : ∀ p ∈ capsC c, ResolvesLabel K p.1 p.2) : LWSCg K γ b c := by
  cases d with
  | @ret γ γ' Γ v A q hv hγ =>
    subst hγ
    exact .ret (q := q) rfl (lwsvg_of_typed _ hv (by simpa only [capsC] using hcaps))
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B hM hN hγ =>
    subst hγ
    simp only [capsC] at hcaps
    exact .letC (q1 := q1) (q2 := q2) rfl
      (by have h1 := hM.length_eq; have h2 := hN.length_eq;
          simp only [List.length_cons] at h2; omega)
      (lwscg_of_typed b hM (capsR_left hcaps)) (lwscg_of_typed b hN (capsR_right hcaps))
  | force hv => exact .force (lwsvg_of_typed b hv (by simpa only [capsC] using hcaps))
  | lam hM => exact .lam (lwscg_of_typed b hM (by simpa only [capsC] using hcaps))
  | @app γ γ₁ γ₂ Γ M v φ q A B hM hv hγ =>
    subst hγ
    simp only [capsC] at hcaps
    exact .app (q := q) rfl (by rw [hM.length_eq, hv.length_eq])
      (lwscg_of_typed b hM (capsR_left hcaps)) (lwsvg_of_typed _ hv (capsR_right hcaps))
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C hv hN₁ hN₂ hγ =>
    subst hγ
    simp only [capsC] at hcaps
    refine .case (q := q) rfl
      (by have h1 := hv.length_eq; have h2 := hN₁.length_eq;
          simp only [List.length_cons] at h2; omega) ?_ ?_ ?_
    · exact lwsvg_of_typed _ hv (capsR_left (capsR_left hcaps))
    · exact lwscg_of_typed b hN₁ (capsR_right (capsR_left hcaps))
    · exact lwscg_of_typed b hN₂ (capsR_right hcaps)
  | @split γ γ_v γ_N Γ v N φ q A B C hv hN hγ =>
    subst hγ
    simp only [capsC] at hcaps
    refine .split (q := q) rfl
      (by have h1 := hv.length_eq; have h2 := hN.length_eq;
          simp only [List.length_cons] at h2; omega) ?_ ?_
    · exact lwsvg_of_typed _ hv (capsR_left hcaps)
    · exact lwscg_of_typed b hN (capsR_right hcaps)
  | unfold hv => exact .unfold (lwsvg_of_typed b hv (by simpa only [capsC] using hcaps))
  | @perform γ_c γ_v Γ cv ℓ op v φ q A B hc hle hopA hopR hv =>
    simp only [capsC] at hcaps
    exact .perform (q := q) rfl (by rw [hv.length_eq, hc.length_eq])
      (lwsvg_of_typed b hc (capsR_left hcaps)) (lwsvg_of_typed false hv (capsR_right hcaps))
  | handleThrows _ _ hM _ _ =>
    exact .handleThrows (lwscg_of_typed b hM (by simpa only [capsC, capsH, List.nil_append] using hcaps))
  | handleState _ _ _ _ _ hs hM _ _ =>
    simp only [capsC, capsH] at hcaps
    exact .handleState (lwsvg_of_typed b hs (capsR_left hcaps))
      (lwscg_of_typed b hM (capsR_right hcaps))
  | handleTransaction _ _ _ _ _ _ _ _ hM _ _ =>
    simp only [capsC, capsH] at hcaps
    exact .handleTransaction (lwscg_of_typed b hM (capsR_right hcaps))
end

/-! ### §2′.8g — SPIKE (task #48): the ⊥-row return-escape coherence (POP-focus-live slice).

**Standalone** (NOT wired into `wsCfg_step` — that needs the strengthened graded invariant). Tests
whether the B-occ technique closes the POP focus: a value typed at the popped handler's answer type `A`
with `¬LabelOccurs ℓ A` re-homes its scoping past the popped frame `handleF g' hd` (`hd : ℓ`). The HEART
is the `vcap` leaf — a LIVE `vcap n ℓ'` has type `cap ℓ'`; `¬LabelOccurs ℓ A ⇒ ℓ ≠ ℓ'`; `n = g'` would
force it to resolve to the head `hd : ℓ` (so `ℓ' = ℓ`), contradiction ⇒ `n ≠ g'` ⇒ `resolvesLabel_pop`.
Dormant leaves are `lwsv_dormant_stack_indep`. The comp companion threads the ROW (`¬(ℓ ≤ φ)` + a
perform's `ℓ' ≤ φ` ⇒ `ℓ' ≠ ℓ`) and the result type (`¬CTy.labelOccurs ℓ C`).

SPIKE VERDICT (build-grounded): the technique CLOSES every value former + `ret`/`force`/`lam`/`perform`,
but WALLS at the ELIMINATION formers `letC`/`app`/`case`/`split`: B-occ constrains only the comp's
RESULT type `C`, never the CONSUMED intermediate (`letC`'s `M : F q1 A`, `app`'s arg `v : A`, the
scrutinee `: sum/prod A B`), where a flag-`true` cap labeled `ℓ` can hide with NO `¬LabelOccurs` premise
(exactly the `escapeB_app` arrow-blindness, at the lemma level). Those caps are the typed-DEAD ones the
GRADE gates dormant — so the standalone TYPELESS lemma is insufficient; it needs the typed grade
(`LWSVg`). `unfold`/`handle*` wall on orthogonal sublemmas (occ-monotonicity / local-handle threading),
NOT the B-occ blindness. -/
mutual
theorem lwsv_returnEscape {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ : Label}
    (hℓ : Handler.label hd = ℓ) {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val}
    {A : VTy Eff Mult} {b : Bool} (d : HasVTy γ Γ v A) (hbo : ¬ VTy.labelOccurs ℓ A)
    (h : LWSV (Frame.handleF g' hd :: K') b v) : LWSV K' b v := by
  cases d with
  | vunit => cases h with | vunit => exact .vunit
  | vint => cases h with | vint => exact .vint
  | vvar _ => cases h with | vvar => exact .vvar
  | @vcap Γ n ℓ' =>
    cases h with
    | vcap_live hr =>
      refine .vcap_live (resolvesLabel_pop ?_ hr)
      intro hng; subst hng
      obtain ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩ := hr
      rw [splitAtId, if_pos rfl] at hsplit
      simp only [Option.some.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨_, rfl, _⟩ := hsplit
      exact hbo (hℓ.symm.trans hlbl)
    | vcap_dormant => exact .vcap_dormant
  | @vthunk γ Γ M φ B hM =>
    cases h with
    | vthunk hc =>
      exact .vthunk (lwsc_returnEscape hℓ hM (fun hx => hbo (Or.inl hx)) (fun hx => hbo (Or.inr hx)) hc)
  | inl ha =>
    cases h with | inl hsc => exact .inl (lwsv_returnEscape hℓ ha (fun hx => hbo (Or.inl hx)) hsc)
  | inr ha =>
    cases h with | inr hsc => exact .inr (lwsv_returnEscape hℓ ha (fun hx => hbo (Or.inr hx)) hsc)
  | pair ha hc hγ =>
    cases h with
    | pair h1 h2 =>
      exact .pair (lwsv_returnEscape hℓ ha (fun hx => hbo (Or.inl hx)) h1)
        (lwsv_returnEscape hℓ hc (fun hx => hbo (Or.inr hx)) h2)
  | @fold _ _ _ Ai ha =>
    cases h with
    | fold hsc => exact .fold (lwsv_returnEscape hℓ ha (fun hx => hbo (labelOccurs_unrollMu ℓ Ai hx)) hsc)
theorem lwsc_returnEscape {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ : Label}
    (hℓ : Handler.label hd = ℓ) {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp}
    {φ : Eff} {C : CTy Eff Mult} {b : Bool} (d : HasCTy γ Γ c φ C)
    (hrow : ¬ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ) (hres : ¬ CTy.labelOccurs ℓ C)
    (h : LWSC (Frame.handleF g' hd :: K') b c) : LWSC K' b c := by
  cases d with
  | @ret γ γ' Γ v A q hv hγ =>
    cases h with
    | @ret _ _ q_tl hvsc => exact .ret (q := q_tl) (lwsv_returnEscape hℓ hv hres hvsc)
  | force hv =>
    cases h with
    | force hvsc => exact .force (lwsv_returnEscape hℓ hv (fun hx => hx.elim hrow hres) hvsc)
  | lam hM =>
    cases h with
    | lam hMsc => exact .lam (lwsc_returnEscape hℓ hM hrow (fun hx => hres (Or.inr hx)) hMsc)
  | @perform γ_c γ_v Γ cv ℓ2 op v φ q A B hc hle hopA hopR hv =>
    cases h with
    | perform h1 h2 =>
      refine .perform ?_ (lwsv_dormant_stack_indep h2)
      exact lwsv_returnEscape hℓ hc (by intro hx; simp only [VTy.labelOccurs] at hx; subst hx; exact hrow hle) h1
  | unfold hv =>
    -- WALL (orthogonal): needs `labelOccurs ℓ A → labelOccurs ℓ (unrollMu A)` (the REVERSE of
    -- `labelOccurs_unrollMu`); an occ-monotonicity sublemma, not the B-occ blindness.
    sorry
  | letC hM hN hγ =>
    -- ★ THE WALL (B-occ blindness). `M : F q1 A`; the let-INTERMEDIATE `A` can mention `ℓ`, but B-occ
    -- only gives `¬CTy.labelOccurs ℓ B` for the RESULT `B`. A flag-`true` cap labeled `ℓ` in `M`
    -- (typeless-live; the typed grade `q1 * q_or_1 q2` may be 0) has NO `¬LabelOccurs` premise and
    -- resolves to the popped head ⇒ non-poppable. Needs the typed grade (`LWSVg`). See escapeB_app.
    sorry
  | app hM hv hγ =>
    -- ★ THE WALL: `app`'s argument `v : A` (and `M : arr q A B`'s domain `A`) is uncovered by the
    -- result-type B-occ — the EXACT escapeB_app pattern (cap behind the arrow `app` eliminates).
    sorry
  | case hv hN₁ hN₂ hγ =>
    -- ★ THE WALL: the scrutinee `v : sum A B` is uncovered by `¬CTy.labelOccurs ℓ C`.
    sorry
  | split hv hN hγ =>
    -- ★ THE WALL: the scrutinee `v : prod A B` is uncovered by the result-type B-occ.
    sorry
  | handleThrows _ _ hM _ _ =>
    -- WALL (orthogonal): a term-level `handle` discharges its OWN label; threading the local
    -- discharge (`e ≤ ℓ_h ⊔ φ`) is separate machinery, not the B-occ blindness.
    sorry
  | handleState _ _ _ _ _ hs hM _ _ => sorry
  | handleTransaction _ _ _ _ _ _ _ _ hM _ _ => sorry
end

/- **OBLIGATION 2 — `WScfg` preservation by `Source.step` (the inc-5 crux).** `WScfg` =
`HasCTy ∧ HasStack ∧ LWSC ∧ LWSK ∧ WellCounted`. The TYPING half (`HasCTy`/`HasStack`) rides
`hasConfigTy_step`; `WellCounted` rides `wellCounted_step`; the WELL-SCOPED half (`LWSC`/`LWSK`) is
rebuilt per arm:
  • PUSH (letC/app)  — caps re-home under the pushed transparent frame via `lwsc_restack`/`lwsk_restack`.
  • MINT (handle)    — the minted cap resolves under its OWN freshly-pushed `handleF g` frame; the OLD
    tail re-homes via `lwsc_restack_handleF`/`lwsk_restack_handleF` (freshness from `StackBelow`).
  • REDUCE (letF/appF β, case/split) — the live arg is rebuilt at flag `true` from typing (PIECE 1,
    `lwsvg_of_typed`/`lwsvg_to_lwsv`) then the typeless `lwsc_subst` plugs it into the continuation
    (`lwsc_uncons`-ed past the popped transparent frame). The ONE focus sorry sits HERE
    (`capsResolve_reduce_TODO`, the substituted value's caps).
  • force/unfold     — the body/payload is directly `LWSC`-true; no subst.
  • POP (handleF-ret) — FLAGGED (`lws_pop_TODO`): popping a real handler needs the n≠g' freshness the
    typeless invariant discarded (the ⊥-row return-escape arm). See the report.
  • DISPATCH (perform) — `lws_dispatch_TODO` (#35). -/

/-- **NAMED SORRY (1 of the focus arms) — caps-resolve at REDUCE-subst.** Every cap in the substituted
value `v` resolves on the (popped) stack `K`. Discharge from typing-performability + `LWSK` (the stack's
installed handlers), NOT off `LWSV`-true (a thunk-buried cap is `LWSV`-true-dormant yet non-resolving —
`Bang/CohSubstRefute.lean::wbad_not_reshaped`). Precedent: `handlesOp_of_hasConfigTy` (~Model:1177).
Stated at any grade (`capsV` ignores the grade) so the closed-value `HasVTy` flows directly into PIECE 1. -/
theorem capsResolve_reduce_TODO {K : EvalCtx} {γ : GradeVec Mult} {v : Val} {A : VTy Eff Mult}
    (hv : HasVTy (Eff := Eff) (Mult := Mult) γ [] v A) (hWSK : LWSK K K true) :
    ∀ p ∈ capsV v, ResolvesLabel K p.1 p.2 := by
  sorry

/-- **NAMED SORRY (the DISPATCH arm, #35).** `idDispatch` reinstalls/pops a handler on a resume; the
resumed focus + reassembled stack stay well-scoped. DISPATCH resumption-grade arm, deferred to #35
(the abort/tail/general multiplicity grading). -/
theorem lws_dispatch_TODO {g : Nat} {K K' : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId}
    {v : Val} {c' : Comp}
    (hWSC : LWSC K true (Comp.perform (Val.vcap n ℓ) op v)) (hWSK : LWSK K K true)
    (hWC : StackBelow g K) (hd : idDispatch K n ℓ op v = some (K', c')) :
    LWSC K' true c' ∧ LWSK K' K' true := by
  sorry

/-- **FLAGGED (the POP-escape arm).** Pop a real `handleF g' hd` frame off the focus's `ret v` and the
tail stack `K'`. UNLIKE the transparent `letF`/`appF` pop (`lwsc_uncons`/`lwsk_uncons`), removing a
HANDLER can break a cap that resolved TO it. Closing this sorry-free needs the n≠g' freshness that the
typeless `LWSC`/`LWSK` have DISCARDED (it lives in `LWSCp`/`LWSVp`, but there is no `LWSC → LWSCp` lift
nor an `LWSK` pop in tree); per `scratch/DiagonalProbe.lean §POP-ESCAPE` this is the ⊥-row return-escape
discipline — a typing co-invariant, NOT a typeless restack. See the handoff report. -/
theorem lws_pop_TODO {g' : Nat} {hd : Handler} {K' : EvalCtx} {v : Val}
    (hWSC : LWSC (Frame.handleF g' hd :: K') true (Comp.ret v))
    (hWSK : LWSK (Frame.handleF g' hd :: K') (Frame.handleF g' hd :: K') true) :
    LWSC K' true (Comp.ret v) ∧ LWSK K' K' true := by
  sorry

theorem wsCfg_step {Co : CTy Eff Mult} (cfg cfg' : Config)
    (hP : WScfg Co cfg) (hstep : Source.step cfg = some cfg') : WScfg Co cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  obtain ⟨e, C, hfocus, hstack, hWSC, hWSK, hWC⟩ := hP
  -- TYPING half (uniform via `hasConfigTy_step`); `eo' ≤ ⊥` pins `eo' = ⊥`.
  obtain ⟨eo', hle, e', C', hf', hs'⟩ := hasConfigTy_step ⟨e, C, hfocus, hstack⟩ hstep
  obtain rfl : eo' = ⊥ := le_bot_iff.mp hle
  -- WellCounted half (uniform).
  have hWCr : WellCounted cfg' := wellCounted_step hWC hstep
  cases c with
  | ret v =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        have hfr : ∀ m h, Frame.letF N ≠ Frame.handleF m h := by intro m h; simp
        cases hWSK with
        | letF hN hKtail =>
          obtain ⟨γ', A, q0, he0, hC0, hγ0, hwv⟩ := hfocus.ret_inv
          have hKt : LWSK K' K' true := lwsk_uncons (Frame.letF N) hfr hKtail
          exact ⟨e', C', hf', hs',
            lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true hwv (capsResolve_reduce_TODO hwv hKt)))
              (fun j => hwv.shift_closed j (by simp)) 0 (lwsc_uncons (Frame.letF N) hfr hN),
            hKt, hWCr⟩
      | appF w => simp [Source.step] at hstep
      | handleF g' hd =>
        -- POP-escape arm — flagged: see `lws_pop_TODO` / the report.
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        obtain ⟨hlwsc, hlwsk⟩ := lws_pop_TODO hWSC hWSK
        exact ⟨e', C', hf', hs', hlwsc, hlwsk, hWCr⟩
  | letC M N =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    have hfr : ∀ m h, Frame.letF N ≠ Frame.handleF m h := by intro m h; simp
    cases hWSC with
    | letC hM hN =>
      exact ⟨e', C', hf', hs', lwsc_restack (Frame.letF N) hfr hM,
        .letF (lwsc_restack (Frame.letF N) hfr hN) (lwsk_restack (Frame.letF N) hfr hWSK), hWCr⟩
  | app M w =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    have hfr : ∀ m h, Frame.appF w ≠ Frame.handleF m h := by intro m h; simp
    cases hWSC with
    | @app _ _ _ q hM hw =>
      exact ⟨e', C', hf', hs', lwsc_restack (Frame.appF w) hfr hM,
        .appF (q := q) (lwsv_restack (Frame.appF w) hfr hw) (lwsk_restack (Frame.appF w) hfr hWSK), hWCr⟩
  | handle hh M =>
    cases hh with
    | throws ℓ =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | handleThrows hM =>
        exact ⟨e', C', hf', hs',
          lwsc_subst (.vcap_live ⟨[], Handler.throws ℓ, K, by simp [splitAtId], rfl⟩) (fun _ => rfl) 0
            (lwsc_restack_handleF g (Handler.throws ℓ) hWC hM),
          .handleF (lwsk_restack_handleF g (Handler.throws ℓ) hWC hWSK), hWCr⟩
    | state ℓ s =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | handleState hs0 hM =>
        exact ⟨e', C', hf', hs',
          lwsc_subst (.vcap_live ⟨[], Handler.state ℓ s, K, by simp [splitAtId], rfl⟩) (fun _ => rfl) 0
            (lwsc_restack_handleF g (Handler.state ℓ s) hWC hM),
          .stateF (lwsv_restack_handleF g (Handler.state ℓ s) hWC hs0)
            (lwsk_restack_handleF g (Handler.state ℓ s) hWC hWSK), hWCr⟩
    | transaction ℓ Θ =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | handleTransaction hM =>
        exact ⟨e', C', hf', hs',
          lwsc_subst (.vcap_live ⟨[], Handler.transaction ℓ Θ, K, by simp [splitAtId], rfl⟩)
            (fun _ => rfl) 0 (lwsc_restack_handleF g (Handler.transaction ℓ Θ) hWC hM),
          .transactionF (lwsk_restack_handleF g (Handler.transaction ℓ Θ) hWC hWSK), hWCr⟩
  | force w =>
    cases w with
    | vthunk M =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | force hv => cases hv with
        | vthunk hM => exact ⟨e', C', hf', hs', hM, hWSK, hWCr⟩
    | vunit | vint | vvar _ | vcap _ _ | inl _ | inr _ | pair _ _ | fold _ =>
      simp [Source.step] at hstep
  | lam M =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N => simp [Source.step] at hstep
      | handleF g' hd => simp [Source.step] at hstep
      | appF w =>
        simp only [Source.step, Option.some.injEq] at hstep; subst hstep
        have hfr : ∀ m h, Frame.appF w ≠ Frame.handleF m h := by intro m h; simp
        cases hWSC with
        | lam hM =>
          cases hWSK with
          | @appF _ _ _ q hw hKtail =>
            obtain ⟨qa, A, B, hCeq, hwty, hsub⟩ := hstack.appF_inv
            have hKt : LWSK K' K' true := lwsk_uncons (Frame.appF w) hfr hKtail
            exact ⟨e', C', hf', hs',
              lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true hwty (capsResolve_reduce_TODO hwty hKt)))
                (fun j => hwty.shift_closed j (by simp)) 0 (lwsc_uncons (Frame.appF w) hfr hM),
              hKt, hWCr⟩
  | case v N₁ N₂ =>
    cases v with
    | inl a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | @case _ _ _ _ q h1 h2 h3 =>
        obtain ⟨γ_v, γ_N, q0, A, B, hγ0, hv, hN1, hN2⟩ := hfocus.case_inv
        cases hv with
        | inl ha =>
          exact ⟨e', C', hf', hs',
            lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true ha (capsResolve_reduce_TODO ha hWSK)))
              (fun j => ha.shift_closed j (by simp)) 0 h2, hWSK, hWCr⟩
    | inr a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | @case _ _ _ _ q h1 h2 h3 =>
        obtain ⟨γ_v, γ_N, q0, A, B, hγ0, hv, hN1, hN2⟩ := hfocus.case_inv
        cases hv with
        | inr ha =>
          exact ⟨e', C', hf', hs',
            lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true ha (capsResolve_reduce_TODO ha hWSK)))
              (fun j => ha.shift_closed j (by simp)) 0 h3, hWSK, hWCr⟩
    | vunit | vint | vvar _ | vcap _ _ | vthunk _ | pair _ _ | fold _ =>
      simp [Source.step] at hstep
  | split v N =>
    cases v with
    | pair a b =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | @split _ _ _ q h1 h2 =>
        obtain ⟨γ_v, γ_N, q0, A, B, hγ0, hv, hN⟩ := hfocus.split_inv
        cases hv with
        | pair ha hb hγab =>
          have hbc : Val.shift b = b := hb.shift_closed 0 (by simp)
          have hbshift := hbc.symm ▸ hb
          have hinner : LWSC K true (Comp.subst (Val.shift b) N) :=
            lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true hbshift (capsResolve_reduce_TODO hbshift hWSK)))
              (fun j => by rw [hbc]; exact hb.shift_closed j (by simp)) 0 h2
          exact ⟨e', C', hf', hs',
            lwsc_subst (lwsvg_to_lwsv (lwsvg_of_typed true ha (capsResolve_reduce_TODO ha hWSK)))
              (fun j => ha.shift_closed j (by simp)) 0 hinner, hWSK, hWCr⟩
    | vunit | vint | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | fold _ =>
      simp [Source.step] at hstep
  | unfold v =>
    cases v with
    | fold a =>
      simp only [Source.step, Option.some.injEq] at hstep; subst hstep
      cases hWSC with
      | unfold hv => cases hv with
        | fold ha => exact ⟨e', C', hf', hs', .ret (q := (0 : ℕ)) (lwsv_of_live _ ha), hWSK, hWCr⟩
    | vunit | vint | vvar _ | vcap _ _ | vthunk _ | inl _ | inr _ | pair _ _ =>
      simp [Source.step] at hstep
  | perform cv op v =>
    cases cv with
    | vcap n ℓ =>
      simp only [Source.step, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨K', c'⟩, hd, hcfg⟩ := hstep
      subst hcfg
      obtain ⟨hlwsc, hlwsk⟩ := lws_dispatch_TODO hWSC hWSK hWC hd
      exact ⟨e', C', hf', hs', hlwsc, hlwsk, hWCr⟩
    | vunit | vint | vvar _ | vthunk _ | inl _ | inr _ | pair _ _ | fold _ =>
      simp [Source.step] at hstep
  | oom => simp [Source.step] at hstep
  | wrong s => simp [Source.step] at hstep

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
