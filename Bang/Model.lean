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
  | case {b v N₁ N₂} (h1 : LWSV K b v) (h2 : LWSC K b N₁) (h3 : LWSC K b N₂) :
      LWSC K b (Comp.case v N₁ N₂)
  | split {b v N} (h1 : LWSV K b v) (h2 : LWSC K b N) : LWSC K b (Comp.split v N)
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
  | case h1 h2 h3 => exact .case (lwsv_to_dormant h1) (lwsc_to_dormant h2) (lwsc_to_dormant h3)
  | split h1 h2 => exact .split (lwsv_to_dormant h1) (lwsc_to_dormant h2)
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
  | case h1 h2 h3 =>
    simp only [Comp.substFrom, hsh]
    exact .case (lwsv_subst hwl hcl k h1) (lwsc_subst hwl hcl (k + 1) h2) (lwsc_subst hwl hcl (k + 1) h3)
  | split h1 h2 =>
    simp only [Comp.substFrom, hsh]
    exact .split (lwsv_subst hwl hcl k h1) (lwsc_subst hwl hcl (k + 2) h2)
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
    exact .case (lwsv_subst_dormant hwd hcl k h1) (lwsc_subst_dormant hwd hcl (k + 1) h2)
      (lwsc_subst_dormant hwd hcl (k + 1) h3)
  | split h1 h2 =>
    simp only [Comp.substFrom, hsh]
    exact .split (lwsv_subst_dormant hwd hcl k h1) (lwsc_subst_dormant hwd hcl (k + 2) h2)
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
    exact .case (lwsv_dormant_stack_indep h1) (lwsc_dormant_stack_indep h2) (lwsc_dormant_stack_indep h3)
  | split h1 h2 => exact .split (lwsv_dormant_stack_indep h1) (lwsc_dormant_stack_indep h2)
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
      exact .case (lwsv_capFree K b hv h.1.1) (lwsc_capFree K b hN₁ h.1.2) (lwsc_capFree K b hN₂ h.2)
  | split hv hN _ =>
      simp only [capsC, List.append_eq_nil_iff] at h
      exact .split (lwsv_capFree K b hv h.1) (lwsc_capFree K b hN h.2)
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
  | case {k b v N₁ N₂} (h1 : LWSVk K k b v) (h2 : LWSCk K (k + 1) b N₁) (h3 : LWSCk K (k + 1) b N₂) :
      LWSCk K k b (Comp.case v N₁ N₂)
  | split {k b v N} (h1 : LWSVk K k b v) (h2 : LWSCk K (k + 2) b N) : LWSCk K k b (Comp.split v N)
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
  | case h1 h2 h3 =>
    simp only [Comp.substFrom, hsh]
    exact .case (lwsvk_subst hwd hcl k h1) (lwsck_subst hwd hcl (k + 1) h2) (lwsck_subst hwd hcl (k + 1) h3)
  | split h1 h2 =>
    simp only [Comp.substFrom, hsh]
    exact .split (lwsvk_subst hwd hcl k h1) (lwsck_subst hwd hcl (k + 2) h2)
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
  | case {b v N₁ N₂} (h1 : LWSVp K g b v) (h2 : LWSCp K g b N₁) (h3 : LWSCp K g b N₂) :
      LWSCp K g b (Comp.case v N₁ N₂)
  | split {b v N} (h1 : LWSVp K g b v) (h2 : LWSCp K g b N) : LWSCp K g b (Comp.split v N)
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
  | case h1 h2 h3 => exact .case (lwsvp_pop_restack h1) (lwscp_pop_restack h2) (lwscp_pop_restack h3)
  | split h1 h2 => exact .split (lwsvp_pop_restack h1) (lwscp_pop_restack h2)
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
      (hγ : γ = (q_or_1 q2) • γ₁ + γ₂)
      (h1 : LWSCg K γ₁ b M) (h2 : LWSCg K ((q1 * q_or_1 q2) :: γ₂) b N) : LWSCg K γ b (Comp.letC M N)
  | force {γ : GradeVec Mult} {b v} (h : LWSVg K γ b v) : LWSCg K γ b (Comp.force v)
  | lam {γ : GradeVec Mult} {b M} {q : Mult} (h : LWSCg K (q :: γ) b M) : LWSCg K γ b (Comp.lam M)
  | app {γ γ₁ γ₂ : GradeVec Mult} {b M v} {q : Mult} (hγ : γ = γ₁ + q • γ₂)
      (hlen : γ₁.length = γ₂.length)
      (h1 : LWSCg K γ₁ b M) (h2 : LWSVg K γ₂ (b && decide (q ≠ 0)) v) : LWSCg K γ b (Comp.app M v)
  | case {γ γ_v γ_N : GradeVec Mult} {b v N₁ N₂} {q : Mult} (hγ : γ = q • γ_v + γ_N)
      (hlen : γ_v.length = γ_N.length)
      (h1 : LWSVg K γ_v b v) (h2 : LWSCg K (q :: γ_N) b N₁) (h3 : LWSCg K (q :: γ_N) b N₂) :
      LWSCg K γ b (Comp.case v N₁ N₂)
  | split {γ γ_v γ_N : GradeVec Mult} {b v N} {q : Mult} (hγ : γ = q • γ_v + γ_N)
      (hlen : γ_v.length = γ_N.length)
      (h1 : LWSVg K γ_v b v) (h2 : LWSCg K (q :: q :: γ_N) b N) : LWSCg K γ b (Comp.split v N)
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
  | letC _ h1 h2 => exact .letC (lwscg_to_lwsc h1) (lwscg_to_lwsc h2)
  | force h => exact .force (lwsvg_to_lwsv h)
  | lam h => exact .lam (lwscg_to_lwsc h)
  | @app _ _ _ _ _ _ q _ _ h1 h2 =>
      exact .app (q := gnat q) (lwscg_to_lwsc h1) (by simpa only [decide_gnat] using lwsvg_to_lwsv h2)
  | case _ _ h1 h2 h3 => exact .case (lwsvg_to_lwsv h1) (lwscg_to_lwsc h2) (lwscg_to_lwsc h3)
  | split _ _ h1 h2 => exact .split (lwsvg_to_lwsv h1) (lwscg_to_lwsc h2)
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
    ∧ LWSC cfg.2.1 true cfg.2.2 ∧ LWSK cfg.2.1 cfg.2.1 true

/-- **SEED (GREEN).** A `VcapFree` closed program satisfies the typed-relative invariant at the initial
config — no caps to resolve, the stack is empty. The typing derivations come from `hty`. -/
theorem wellScoped_initial (c : Comp) (hvf : VcapFree c) {Co : CTy Eff Mult}
    (hty : HasConfigTy (0, [], c) ⊥ Co) : WScfg Co (0, [], c) := by
  obtain ⟨e, C, hfocus, hstack⟩ := hty
  -- the stack is `[]`, so `hstack : HasStack [] e C ⊥ Co` must be `nil` (`e = ⊥`, `C = Co`).
  cases hstack
  exact ⟨⊥, Co, hfocus, .nil, lwsc_capFree [] true hfocus hvf, .nil⟩

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
  | case h1 h2 h3 => exact .case (lwsv_restack fr hfr h1) (lwsc_restack fr hfr h2) (lwsc_restack fr hfr h3)
  | split h1 h2 => exact .split (lwsv_restack fr hfr h1) (lwsc_restack fr hfr h2)
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
  | case h1 h2 h3 =>
      exact .case (lwsv_restack_handleF g hd hsb h1) (lwsc_restack_handleF g hd hsb h2)
        (lwsc_restack_handleF g hd hsb h3)
  | split h1 h2 => exact .split (lwsv_restack_handleF g hd hsb h1) (lwsc_restack_handleF g hd hsb h2)
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

/-- **OBLIGATION 2 — the MUTUAL preservation (the research crux, multi-session).** `WScfg` is preserved
by every `Source.step`. `WScfg` = `HasCTy ∧ HasStack ∧ WSC ∧ WSK`: the TYPING half (`HasCTy`/`HasStack`)
rides EXISTING preservation (`preservation_proof`, Metatheory — NonEscape-free); the NEW content is the
`WSC`/`WSK` cap-resolution half, now invertible/buildable since they are TERM+TYPE indexed.

SUPPORTING LEMMAS:
  · ✓ DONE `resolvesLabel_cons` + `wsv_restack`/`wsc_restack` (§3.5) — `ResolvesLabel`/`WSV`/`WSC` re-home
    under a pushed non-`handleF` frame (the PUSH/REDUCE mechanics). The MINT `handleF g` push needs the
    freshness-keyed variant (`g` global-fresh ⇒ id ≠ any live cap, so `resolvesLabel_cons`'s side-condition
    discharges via `WellCounted`/`splitAtId_fresh`).
  · TODO `hasConfigTy_step` — factor the NonEscape-free TYPING preservation out of `preservation_proof`
    (Metatheory:2038). Every leaf there is `⟨eo',hle,⟨HasConfigTy⟩,hnecfg'⟩`; `hnecfg'` is the ONLY
    NonEscape use ⇒ drop the last tuple slot + the `hne`/`hnecfg'` lines ⇒ `HasConfigTy cfg eo Co → step →
    ∃ eo' ≤ eo, HasConfigTy cfg' eo' Co`. ~300 lines, mechanical. THE gate for every arm's typing half.
  · TODO `wsc_subst` — the cap-substitution lemma `WSV K ρ v A → WSC K ρ N … → WSC K ρ (subst v N) …`
    (the `subst_value` analogue for caps; REDUCE/MINT/DISPATCH need it).
  · TODO the B-occ lever (PROBE `scratch/WellScopedReshapeProbe.lean::surfaceCaps_labelOccurs`, promote it):
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
  • POP (`handleF g::K, ret v ↦ K, ret v`): THE crux — and the OPEN sub-case (the whole `sorry`).
    ⚠ The sketched closure ("`¬LabelOccurs ℓ_f A` ⇒ every `ℓ_f`-cap in `v` is under a thunk whose row
    excludes `ℓ_f`") is FALSE. The "deep B-occ lever" it relied on (`a performable cap at a thunk-row-φ
    position in v:A ⟹ LabelOccurs ℓ A`) is REFUTED by `Bang.BoccRegress.escapeB_app`: wrap the escaping
    `ℓ_f`-performing thunk `w : U {ℓ_f} (F 1 unit)` as the DISCARDED argument of `app (lam (ret vunit)) w`;
    `app` ELIMINATES the arrow, so `A = U ⊥ (F 1 unit)` with `¬LabelOccurs ℓ_f A` — B-occ ADMITS it
    (`escapeB_app_typeable`, qc = 0) — yet `w`'s thunk row `{ℓ_f}` makes the buried cap PERFORMABLE per
    `WSV`. So `WScfg` is NOT POP-preserved with the current `WSV` gate. The program is SAFE (the `lam`
    discards `w`, cap dead, never forced) — invariant-too-strong, NOT a soundness bug, NOT a Spec.lean
    issue. A type-level B-occ premise on the answer type cannot see arrow-guarded latent caps (the info
    is in the TERM, not `A`): the ADR-0041 later-modality territory. The fix is a WSV REDESIGN, decided
    by the opt-1/2/3 spikes: (1) later/Kripke LR (caps behind → resolve "later"); (2) focus-reachability-
    refined gate (require resolution only for caps that can reach a focus-perform); (3) grade-directed
    gate (the discarding `lam` binds at `q = 0` ⇒ `qc = 0` ⇒ the cap is statically dead; gate on grade).
NAMED SORRY: the mutual `WSC`/`WSK` preservation. The TYPING half rides `hasConfigTy_step` (DONE); the
PUSH/REDUCE/MINT/DISPATCH cap-halves are mechanical given `wsc_subst` + the restack/`resolvesLabel_uncons`
mechanics (`resolvesLabel_uncons` = the removal direction, DONE). The OPEN content is the POP arm above,
blocked on the WSV redesign (the arrow-guarded-cap wall, build-pinned by `escapeB_app`). -/
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
