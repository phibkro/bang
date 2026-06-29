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
module

public import Bang.Metatheory
-- Phase-1a finding: module boundaries surface implicit transitive Mathlib deps. This
-- lemma (`Option.map₂_some_some`) was visible transitively pre-module; now it must be an
-- explicit import to cross the public boundary.
public import Mathlib.Data.Option.NAry

namespace Bang.Model
open Bang
open Bang.EffectRow (Label)

-- Module reveal (Phase 1a). `@[expose] public section`: Model's caps/freshness layer
-- (FreshCfg/CapsBelow/splitAtId-adjacent, capsC/capsK) is unfolded by downstream CapCoh,
-- so bodies cross the boundary (Phase-1a finding). NOTE the dead-verdict: the gated
-- headlines reach Model only via Audit→CalcVM→CapCoh, and CapCoh consumes the freshness
-- layer — NOT the sorry-carrying NonEscape diagonal (which stays internal to Model).
@[expose] public section

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

/-! ### §2′.8a′ — GRADED dormant-stack-independence (the `false`-flag value/comp re-homes to ANY stack).

At flag `false` every storage gate `false && decide(q≠0)` collapses to `false`, so the whole sub-tree is
dormant: no `vcap_live` (hence no `ResolvesLabel` reading the stack `K`), so it re-homes to any `K'`. The
graded mirror of `lwsv_dormant_stack_indep` — consumed by `lwscg_returnEscape`'s `perform` arg + every
elimination's typed-DEAD (gate-`false`) sub-case. -/
mutual
theorem lwsvg_dormant_stack_indep {K K' : EvalCtx} {γ : GradeVec Mult} {v : Val}
    (h : LWSVg K γ false v) : LWSVg K' γ false v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar hh => exact .vvar hh
  | vcap_dormant => exact .vcap_dormant
  | vthunk hc => exact .vthunk (lwscg_dormant_stack_indep hc)
  | inl ha => exact .inl (lwsvg_dormant_stack_indep ha)
  | inr ha => exact .inr (lwsvg_dormant_stack_indep ha)
  | pair hγ hlen h1 h2 =>
      exact .pair hγ hlen (lwsvg_dormant_stack_indep h1) (lwsvg_dormant_stack_indep h2)
  | fold ha => exact .fold (lwsvg_dormant_stack_indep ha)
theorem lwscg_dormant_stack_indep {K K' : EvalCtx} {γ : GradeVec Mult} {c : Comp}
    (h : LWSCg K γ false c) : LWSCg K' γ false c := by
  cases h with
  | @ret _ _ _ _ q hγ hv =>
      exact .ret (q := q) hγ (lwsvg_dormant_stack_indep (by simpa using hv))
  | letC hγ hlen h1 h2 =>
      exact .letC hγ hlen (lwscg_dormant_stack_indep h1) (lwscg_dormant_stack_indep h2)
  | force hv => exact .force (lwsvg_dormant_stack_indep hv)
  | lam hM => exact .lam (lwscg_dormant_stack_indep hM)
  | @app _ _ _ _ _ _ q hγ hlen h1 h2 =>
      exact .app (q := q) hγ hlen (lwscg_dormant_stack_indep h1) (lwsvg_dormant_stack_indep (by simpa using h2))
  | @case _ _ _ _ _ _ _ q hγ hlen h1 h2 h3 =>
      exact .case (q := q) hγ hlen (lwsvg_dormant_stack_indep (by simpa using h1))
        (lwscg_dormant_stack_indep h2) (lwscg_dormant_stack_indep h3)
  | @split _ _ _ _ _ _ q hγ hlen h1 h2 =>
      exact .split (q := q) hγ hlen (lwsvg_dormant_stack_indep (by simpa using h1))
        (lwscg_dormant_stack_indep h2)
  | unfold hv => exact .unfold (lwsvg_dormant_stack_indep hv)
  | perform hγ hlen h1 h2 =>
      exact .perform hγ hlen (lwsvg_dormant_stack_indep h1) (lwsvg_dormant_stack_indep h2)
  | handleThrows hM => exact .handleThrows (lwscg_dormant_stack_indep hM)
  | handleState hs hM => exact .handleState (lwsvg_dormant_stack_indep hs) (lwscg_dormant_stack_indep hM)
  | handleTransaction hM => exact .handleTransaction (lwscg_dormant_stack_indep hM)
end

/-! ### §2′.8a″ — ANY-γ DORMANT regrade (the `b' = false` half of `lwsvg_closed_regrade`).

At flag `false` every gate `false && decide(q≠0)` collapses, every `vvar` gate is vacuous (`false → …`),
and every `vcap` is dormant — so NOTHING reads the grade for liveness. Hence the value/comp is `LWSVg`/
`LWSCg` at flag `false` for ANY target grade `γ'`: rebuild the grade equations freely (scaled positions
via `1 • γ' = γ'`, additive via `γ' + zeros`). Feeds the `b'=false` branch + the gated-DEAD sub-positions
of the `b'=true` branch. -/
private theorem gv_one_smul (γ : GradeVec Mult) : (1 : Mult) • γ = γ := by
  show GradeVec.smul 1 γ = γ
  rw [GradeVec.smul]; simp [one_mul]
mutual
theorem lwsvg_to_anyγ_false {K : EvalCtx} {γ0 : GradeVec Mult} {b0 : Bool} {v : Val}
    (h : LWSVg K γ0 b0 v) (γ' : GradeVec Mult) : LWSVg K γ' false v := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar _ => exact .vvar (by simp [GradeVec.zeros])
  | vcap_live _ => exact .vcap_dormant
  | vcap_dormant => exact .vcap_dormant
  | vthunk hc => exact .vthunk (lwscg_to_anyγ_false hc γ')
  | inl ha => exact .inl (lwsvg_to_anyγ_false ha γ')
  | inr ha => exact .inr (lwsvg_to_anyγ_false ha γ')
  | pair _ _ h1 h2 =>
      exact .pair (GradeVec.add_zeros γ').symm (by simp [GradeVec.zeros]) (lwsvg_to_anyγ_false h1 γ')
        (lwsvg_to_anyγ_false h2 (GradeVec.zeros γ'.length))
  | fold ha => exact .fold (lwsvg_to_anyγ_false ha γ')
theorem lwscg_to_anyγ_false {K : EvalCtx} {γ0 : GradeVec Mult} {b0 : Bool} {c : Comp}
    (h : LWSCg K γ0 b0 c) (γ' : GradeVec Mult) : LWSCg K γ' false c := by
  cases h with
  | ret _ hv =>
      exact .ret (q := 1) (gv_one_smul γ').symm (by simpa using lwsvg_to_anyγ_false hv γ')
  | letC _ _ h1 h2 =>
      have r1 := lwscg_to_anyγ_false h1 γ'
      have r2 := lwscg_to_anyγ_false h2 ((0 : Mult) :: GradeVec.zeros γ'.length)
      refine .letC (q1 := 0) (q2 := 1) (γ₁ := γ') (γ₂ := GradeVec.zeros γ'.length) ?_
        (by simp [GradeVec.zeros]) r1 (by simpa using r2)
      rw [show q_or_1 (1 : Mult) = 1 by simp [q_or_1], gv_one_smul]; exact (GradeVec.add_zeros γ').symm
  | force hv => exact .force (lwsvg_to_anyγ_false hv γ')
  | lam hM => exact .lam (q := 0) (lwscg_to_anyγ_false hM ((0 : Mult) :: γ'))
  | app _ _ h1 h2 =>
      have r1 := lwscg_to_anyγ_false h1 γ'
      have r2 := lwsvg_to_anyγ_false h2 (GradeVec.zeros γ'.length)
      refine .app (q := 1) (γ₁ := γ') (γ₂ := GradeVec.zeros γ'.length) ?_
        (by simp [GradeVec.zeros]) r1 (by simpa using r2)
      rw [gv_one_smul]; exact (GradeVec.add_zeros γ').symm
  | case _ _ h1 h2 h3 =>
      have r1 := lwsvg_to_anyγ_false h1 (GradeVec.zeros γ'.length)
      have r2 := lwscg_to_anyγ_false h2 ((1 : Mult) :: γ')
      have r3 := lwscg_to_anyγ_false h3 ((1 : Mult) :: γ')
      refine .case (q := 1) (γ_v := GradeVec.zeros γ'.length) (γ_N := γ') ?_
        (by simp [GradeVec.zeros]) (by simpa using r1) r2 r3
      rw [gv_one_smul]; exact (GradeVec.zeros_add γ').symm
  | split _ _ h1 h2 =>
      have r1 := lwsvg_to_anyγ_false h1 (GradeVec.zeros γ'.length)
      have r2 := lwscg_to_anyγ_false h2 ((1 : Mult) :: (1 : Mult) :: γ')
      refine .split (q := 1) (γ_v := GradeVec.zeros γ'.length) (γ_N := γ') ?_
        (by simp [GradeVec.zeros]) (by simpa using r1) r2
      rw [gv_one_smul]; exact (GradeVec.zeros_add γ').symm
  | unfold hv => exact .unfold (lwsvg_to_anyγ_false hv γ')
  | perform _ _ h1 h2 =>
      have r1 := lwsvg_to_anyγ_false h1 γ'
      have r2 := lwsvg_to_anyγ_false h2 (GradeVec.zeros γ'.length)
      refine .perform (q := 1) (γ_v := GradeVec.zeros γ'.length) (γ_c := γ') ?_
        (by simp [GradeVec.zeros]) r1 (by simpa using r2)
      rw [gv_one_smul]; exact (GradeVec.zeros_add γ').symm
  | handleThrows hM => exact .handleThrows (qc := 0) (lwscg_to_anyγ_false hM ((0 : Mult) :: γ'))
  | handleState hs hM =>
      exact .handleState (qc := 0) (lwsvg_to_anyγ_false hs []) (lwscg_to_anyγ_false hM ((0 : Mult) :: γ'))
  | handleTransaction hM => exact .handleTransaction (qc := 0) (lwscg_to_anyγ_false hM ((0 : Mult) :: γ'))
end

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
  | none => exact Or.inr (by simp [GradeVec.zeros])
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
      exact .handleState (lwsvg_to_lwsvk hzsf k (by simp [GradeVec.zeros]) hs)
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
  | vvar _ => exact .vvar (by simp [GradeVec.zeros])
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

/-! ## §3 — the combined invariant + the named obligations. -/

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
  | .oom | .wrong _ => rfl
theorem capsH_shiftFrom (j : Nat) (h : Handler) : capsH (Handler.shiftFrom j h) = capsH h := by
  match h with
  | .state _ s => simp only [Handler.shiftFrom, capsH]; exact capsV_shiftFrom j s
  | .throws _ => rfl
  | .transaction _ _ => rfl
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
  · rw [if_neg hk] at hd2; exact absurd hd2 (by simp)

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

/-! ### §2′.8f′ — GRADE-SENSITIVE caps-resolution (the coherence carrier, ADR-0061 / #51 keystone).

`LiveCapsResolveV`/`LiveCapsResolveC` recurse on the TYPING derivation and demand `ResolvesLabel` ONLY
at cap leaves reachable through gate-LIVE storage positions (`q ≠ 0`). The dormant-gated leaves (a
`ret`/`app`/`case`/`split` value at `q = 0`; a `perform` argument — always dormant) SKIP the
obligation, mirroring the `LWSCg` storage gates `b && decide (q ≠ 0)` EXACTLY. Two facts make this the
right carrier:
  • `HasVTy`/`HasCTy` are `Prop`, so a `List`-valued `liveCaps` over the derivation would need large
    elimination (illegal); a `Prop`-valued predicate is small elimination (legal). Hence a PREDICATE,
    not a list.
  • The grade-sensitivity is exactly what the all-caps `lwscg_of_typed` (§2′.8f) LACKS: it demands ALL
    of `capsC c` resolve, FALSE post-pop for a typed-DEAD ℓ-cap (the ADR-0061 root). Here the dead cap
    sits behind a `q = 0` gate ⇒ vacuous obligation.
WScfg carries this + the typing, and DERIVES the coherent `LWSCg` via `lwscg_of_typed_live` (grades =
typing grades by construction). #4 (returnEscape) + #5 (subst) UNIFY as "this predicate is preserved." -/
-- An INDUCTIVE PREDICATE indexed by the typing derivation (not a recursive def): `HasVTy`/`HasCTy`
-- are `Prop`, so a recursive def matching the derivation would need `brecOn` (Type elimination of a
-- `Prop` ⇒ illegal). An inductive `Prop` indexed by a `Prop` has no such restriction. Each storage
-- gate (`q ≠ 0 →`) mirrors `LWSCg`'s `b && decide (q ≠ 0)`: a typed-DEAD (`q = 0`) cap leaf SKIPS the
-- `ResolvesLabel` obligation — exactly what the all-caps `lwscg_of_typed` lacks (the ADR-0061 root).
mutual
inductive LiveCapsResolveV (K : EvalCtx) :
    ∀ {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}, HasVTy γ Γ v A → Prop
  | vunit {Γ} : LiveCapsResolveV K (Γ := Γ) HasVTy.vunit
  | vint {Γ n} : LiveCapsResolveV K (Γ := Γ) (HasVTy.vint (n := n))
  | vvar {Γ i A} {h : Γ[i]? = some A} : LiveCapsResolveV K (HasVTy.vvar h)
  | vcap {Γ n ℓ} (hr : ResolvesLabel K n ℓ) : LiveCapsResolveV K (HasVTy.vcap (Γ := Γ) (n := n) (ℓ := ℓ))
  | vthunk {γ Γ M φ B} {dM : HasCTy γ Γ M φ B} (h : LiveCapsResolveC K dM) :
      LiveCapsResolveV K (HasVTy.vthunk dM)
  | inl {γ Γ v A B} {dv : HasVTy γ Γ v A} (h : LiveCapsResolveV K dv) :
      LiveCapsResolveV K (HasVTy.inl (B := B) dv)
  | inr {γ Γ v A B} {dv : HasVTy γ Γ v B} (h : LiveCapsResolveV K dv) :
      LiveCapsResolveV K (HasVTy.inr (A := A) dv)
  | pair {γ γv γw Γ v w A B} {dv : HasVTy γv Γ v A} {dw : HasVTy γw Γ w B} {hγ : γ = γv + γw}
      (h1 : LiveCapsResolveV K dv) (h2 : LiveCapsResolveV K dw) :
      LiveCapsResolveV K (HasVTy.pair dv dw hγ)
  | fold {γ Γ v A} {dv : HasVTy γ Γ v (VTy.unrollMu A)} (h : LiveCapsResolveV K dv) :
      LiveCapsResolveV K (HasVTy.fold dv)
inductive LiveCapsResolveC (K : EvalCtx) :
    ∀ {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {φ : Eff} {C : CTy Eff Mult},
      HasCTy γ Γ c φ C → Prop
  | ret {γ γ' Γ v A} {q : Mult} {dv : HasVTy γ' Γ v A} {hγ : γ = q • γ'}
      (h : q ≠ 0 → LiveCapsResolveV K dv) : LiveCapsResolveC K (HasCTy.ret dv hγ)
  | letC {γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B} {dM : HasCTy γ₁ Γ M φ₁ (CTy.F q1 A)}
      {dN : HasCTy ((q1 * q_or_1 q2) :: γ₂) (A :: Γ) N φ₂ B} {hγ : γ = (q_or_1 q2) • γ₁ + γ₂}
      (h1 : LiveCapsResolveC K dM) (h2 : LiveCapsResolveC K dN) :
      LiveCapsResolveC K (HasCTy.letC dM dN hγ)
  | force {γ Γ v φ B} {dv : HasVTy γ Γ v (VTy.U φ B)} (h : LiveCapsResolveV K dv) :
      LiveCapsResolveC K (HasCTy.force dv)
  | lam {γ Γ M φ q A B} {dM : HasCTy (q :: γ) (A :: Γ) M φ B} (h : LiveCapsResolveC K dM) :
      LiveCapsResolveC K (HasCTy.lam dM)
  | app {γ γ₁ γ₂ Γ M v φ q A B} {dM : HasCTy γ₁ Γ M φ (CTy.arr q A B)} {dv : HasVTy γ₂ Γ v A}
      {hγ : γ = γ₁ + q • γ₂}
      (h1 : LiveCapsResolveC K dM) (h2 : q ≠ 0 → LiveCapsResolveV K dv) :
      LiveCapsResolveC K (HasCTy.app dM dv hγ)
  | case {γ γ_v γ_N Γ v N₁ N₂ φ q A B C} {dv : HasVTy γ_v Γ v (VTy.sum A B)}
      {dN1 : HasCTy (q :: γ_N) (A :: Γ) N₁ φ C} {dN2 : HasCTy (q :: γ_N) (B :: Γ) N₂ φ C}
      {hγ : γ = q • γ_v + γ_N}
      (h1 : q ≠ 0 → LiveCapsResolveV K dv) (h2 : LiveCapsResolveC K dN1) (h3 : LiveCapsResolveC K dN2) :
      LiveCapsResolveC K (HasCTy.case dv dN1 dN2 hγ)
  | split {γ γ_v γ_N Γ v N φ q A B C} {dv : HasVTy γ_v Γ v (VTy.prod A B)}
      {dN : HasCTy (q :: q :: γ_N) (B :: A :: Γ) N φ C} {hγ : γ = q • γ_v + γ_N}
      (h1 : q ≠ 0 → LiveCapsResolveV K dv) (h2 : LiveCapsResolveC K dN) :
      LiveCapsResolveC K (HasCTy.split dv dN hγ)
  | unfold {γ Γ v A} {dv : HasVTy γ Γ v (VTy.mu A)} (h : LiveCapsResolveV K dv) :
      LiveCapsResolveC K (HasCTy.unfold dv)
  | perform {γ_c γ_v Γ cv ℓ op v φ A B} {q : Mult} (dc : HasVTy γ_c Γ cv (VTy.cap ℓ))
      {hle : EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ}
      {hopA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A}
      {hopR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B} (dv : HasVTy γ_v Γ v A)
      (h : LiveCapsResolveV K dc) :
      LiveCapsResolveC K (HasCTy.perform dc hle hopA hopR dv)
  | handleThrows {γ Γ ℓ M e φ q qc A} {hopA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A}
      {hint : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise"}
      {dM : HasCTy (qc :: γ) (VTy.cap ℓ :: Γ) M e (CTy.F q A)}
      {hle : e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ}
      {hbo : ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A} (h : LiveCapsResolveC K dM) :
      LiveCapsResolveC K (HasCTy.handleThrows hopA hint dM hle hbo)
  | handleState {γ Γ ℓ s₀ M e φ q qc S A} {hga : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit}
      {hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S}
      {hpa : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S}
      {hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit}
      {hint : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put"}
      {dsv : HasVTy [] [] s₀ S} {dM : HasCTy (qc :: γ) (VTy.cap ℓ :: Γ) M e (CTy.F q A)}
      {hle : e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ}
      {hbo : ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A}
      (hs : LiveCapsResolveV K dsv) (h : LiveCapsResolveC K dM) :
      LiveCapsResolveC K (HasCTy.handleState hga hgr hpa hpr hint dsv dM hle hbo)
  | handleTransaction {γ Γ ℓ Θ₀ M e φ q qc A}
      {hna : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int}
      {hnr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int}
      {hra : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int}
      {hrr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int}
      {hwa : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some (VTy.prod VTy.int VTy.int)}
      {hwr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit}
      {hint : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
        op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar"}
      {hcells : ∀ cell ∈ Θ₀, HasVTy [] [] cell VTy.int}
      {dM : HasCTy (qc :: γ) (VTy.cap ℓ :: Γ) M e (CTy.F q A)}
      {hle : e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ}
      {hbo : ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A} (h : LiveCapsResolveC K dM) :
      LiveCapsResolveC K (HasCTy.handleTransaction hna hnr hra hrr hwa hwr hint hcells dM hle hbo)
end

/-- ADR-0061 (#51, the SYMMETRIC stack half): grade-sensitive caps-resolution over the STACK frames'
stored terms (`letF`'s continuation, `appF`'s arg, `stateF`'s state). The coherence the decoupled
`LWSKg` lacks — needed because REDUCE pulls a stack continuation `N` into the post-subst focus, so `N`'s
TYPED-live caps must resolve. `appF`'s arg is gated by the arrow `q` (dead arg ⇒ dormant, mirroring
`LWSKg.appF`); `letF`'s `N` is NOT gated (the continuation RUNS); `transactionF`'s `int` cells are
cap-free (omitted). Resolution is in the FULL stack `K` (a superset context; frames above don't capture). -/
inductive LiveCapsResolveK (K : EvalCtx) :
    ∀ {Kfr : EvalCtx} {ein : Eff} {Cin : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult},
      HasStack Kfr ein Cin eo Co → Prop
  | nil {e C} : LiveCapsResolveK K (HasStack.nil (e := e) (C := C))
  | letF {Kfr N e₁ e₂ eo q qk A B Co} {dN : HasCTy (qk :: []) [A] N e₂ B}
      {dK : HasStack Kfr (e₁ ⊔ e₂) B eo Co}
      (hN : LiveCapsResolveC K dN) (hK : LiveCapsResolveK K dK) :
      LiveCapsResolveK K (HasStack.letF (q := q) dN dK)
  | appF {Kfr v e eo A B Co} {q : Mult} {dv : HasVTy [] [] v A} {dK : HasStack Kfr e B eo Co}
      (hv : q ≠ 0 → LiveCapsResolveV K dv) (hK : LiveCapsResolveK K dK) :
      LiveCapsResolveK K (HasStack.appF (q := q) dv dK)
  | handleF {Kfr n ℓ e φ eo q A Co}
      {hr : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A}
      {hint : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise"}
      {hle : e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ}
      {hbo : ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A}
      {dK : HasStack Kfr φ (CTy.F q A) eo Co} (hK : LiveCapsResolveK K dK) :
      LiveCapsResolveK K (HasStack.handleF (n := n) hr hint hle hbo dK)
  | stateF {Kfr n ℓ s e φ eo q A S Co}
      {hga : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit}
      {hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S}
      {hpa : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S}
      {hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit}
      {hint : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put"}
      {ds : HasVTy [] [] s S} {hle : e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ}
      {hbo : ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A}
      {dK : HasStack Kfr φ (CTy.F q A) eo Co}
      (hs : LiveCapsResolveV K ds) (hK : LiveCapsResolveK K dK) :
      LiveCapsResolveK K (HasStack.stateF (n := n) hga hgr hpa hpr hint ds hle hbo dK)
  | transactionF {Kfr n ℓ Θ e φ eo q A Co}
      {hna : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some (VTy.int : VTy Eff Mult)}
      {hnr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some (VTy.int : VTy Eff Mult)}
      {hra : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some (VTy.int : VTy Eff Mult)}
      {hrr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some (VTy.int : VTy Eff Mult)}
      {hwa : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
        = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int)}
      {hwr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit}
      {hint : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
        op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar"}
      {hcells : ∀ cell ∈ Θ, HasVTy [] [] cell (VTy.int : VTy Eff Mult)}
      {hle : e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ}
      {hbo : ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A}
      {dK : HasStack Kfr φ (CTy.F q A) eo Co} (hK : LiveCapsResolveK K dK) :
      LiveCapsResolveK K (HasStack.transactionF (n := n) hna hnr hra hrr hwa hwr hint hcells hle hbo dK)

/-! ### §2′.8f″ — the GRADE-SENSITIVE lift `lwscg_of_typed_live` (the engine).

`lwsvg_of_typed_dormant`/`lwscg_of_typed_dormant`: at flag `false` EVERY gate collapses and EVERY cap
is dormant, so a typed term is `LWSVg`/`LWSCg` at flag `false` with NO caps premise (the from-typing
mirror of `lwsvg_to_anyγ_false`, but built straight from the typing for the `q = 0` dead branches).

`lwsvg_of_typed_live`/`lwscg_of_typed_live`: at flag `true`, consume `LiveCapsResolve` to discharge the
LIVE cap leaves, and route the dead-gated (`q = 0`) value positions through the dormant builder. The
grade-sensitive replacement for the all-caps `lwscg_of_typed` (§2′.8f) — grades = typing grades by
construction (coherence), live caps resolve, dead caps skipped. -/
mutual
theorem lwsvg_of_typed_dormant {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} (d : HasVTy γ Γ v A) : LWSVg K γ false v := by
  cases d with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar _ => exact .vvar (by simp)
  | vcap => exact .vcap_dormant
  | vthunk hM => exact .vthunk (lwscg_of_typed_dormant hM)
  | inl hv => exact .inl (lwsvg_of_typed_dormant hv)
  | inr hv => exact .inr (lwsvg_of_typed_dormant hv)
  | @pair γ γv γw Γ v w A B hv hw hγ =>
    subst hγ
    exact .pair rfl (by rw [hv.length_eq, hw.length_eq]) (lwsvg_of_typed_dormant hv)
      (lwsvg_of_typed_dormant hw)
  | fold hv => exact .fold (lwsvg_of_typed_dormant hv)
theorem lwscg_of_typed_dormant {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {φ : Eff} {C : CTy Eff Mult} (d : HasCTy γ Γ c φ C) : LWSCg K γ false c := by
  cases d with
  | @ret γ γ' Γ v A q hv hγ =>
    subst hγ; exact .ret (q := q) rfl (lwsvg_of_typed_dormant hv)
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B hM hN hγ =>
    subst hγ
    exact .letC (q1 := q1) (q2 := q2) rfl
      (by have h1 := hM.length_eq; have h2 := hN.length_eq; simp only [List.length_cons] at h2; omega)
      (lwscg_of_typed_dormant hM) (lwscg_of_typed_dormant hN)
  | force hv => exact .force (lwsvg_of_typed_dormant hv)
  | lam hM => exact .lam (lwscg_of_typed_dormant hM)
  | @app γ γ₁ γ₂ Γ M v φ q A B hM hv hγ =>
    subst hγ
    exact .app (q := q) rfl (by rw [hM.length_eq, hv.length_eq]) (lwscg_of_typed_dormant hM)
      (lwsvg_of_typed_dormant hv)
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C hv hN₁ hN₂ hγ =>
    subst hγ
    exact .case (q := q) rfl
      (by have h1 := hv.length_eq; have h2 := hN₁.length_eq; simp only [List.length_cons] at h2; omega)
      (lwsvg_of_typed_dormant hv) (lwscg_of_typed_dormant hN₁) (lwscg_of_typed_dormant hN₂)
  | @split γ γ_v γ_N Γ v N φ q A B C hv hN hγ =>
    subst hγ
    exact .split (q := q) rfl
      (by have h1 := hv.length_eq; have h2 := hN.length_eq; simp only [List.length_cons] at h2; omega)
      (lwsvg_of_typed_dormant hv) (lwscg_of_typed_dormant hN)
  | unfold hv => exact .unfold (lwsvg_of_typed_dormant hv)
  | @perform γ_c γ_v Γ cv ℓ op v φ q A B hc hle hopA hopR hv =>
    exact .perform (q := q) rfl (by rw [hv.length_eq, hc.length_eq]) (lwsvg_of_typed_dormant hc)
      (lwsvg_of_typed_dormant hv)
  | handleThrows _ _ hM _ _ => exact .handleThrows (lwscg_of_typed_dormant hM)
  | handleState _ _ _ _ _ hs hM _ _ =>
    exact .handleState (lwsvg_of_typed_dormant hs) (lwscg_of_typed_dormant hM)
  | handleTransaction _ _ _ _ _ _ _ _ hM _ _ => exact .handleTransaction (lwscg_of_typed_dormant hM)
end

mutual
theorem lwsvg_of_typed_live {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} (d : HasVTy γ Γ v A) (hres : LiveCapsResolveV K d) :
    LWSVg K γ true v := by
  -- invert `hres` (it is indexed by `d`, so its constructor pins `d`'s shape AND names the typing
  -- sub-derivations via the `@`-pattern) — `cases d` would fail dependent elimination on the grade index.
  cases hres with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar Γ i A hget =>
    refine .vvar (fun _ => ?_)
    have hi : i < Γ.length := by rw [List.getElem?_eq_some_iff] at hget; exact hget.1
    rw [GradeVec.basis_getElem _ _ _ hi, if_pos rfl]; exact one_ne_zero
  | vcap hr => exact .vcap_live hr
  | @vthunk γ Γ M φ B dM h => exact .vthunk (lwscg_of_typed_live dM h)
  | @inl γ Γ v A B dv h => exact .inl (lwsvg_of_typed_live dv h)
  | @inr γ Γ v A B dv h => exact .inr (lwsvg_of_typed_live dv h)
  | @pair γ γv γw Γ v w A B dv dw hγ h1 h2 =>
    subst hγ
    exact .pair rfl (by rw [dv.length_eq, dw.length_eq]) (lwsvg_of_typed_live dv h1)
      (lwsvg_of_typed_live dw h2)
  | @fold γ Γ v A dv h => exact .fold (lwsvg_of_typed_live dv h)
theorem lwscg_of_typed_live {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {φ : Eff} {C : CTy Eff Mult} (d : HasCTy γ Γ c φ C) (hres : LiveCapsResolveC K d) :
    LWSCg K γ true c := by
  cases hres with
  | @ret γ γ' Γ v A q dv hγ hgate =>
    subst hγ
    refine .ret (q := q) rfl ?_
    by_cases hq : q = 0
    · rw [show (true && decide (q ≠ 0)) = false by simp [hq]]; exact lwsvg_of_typed_dormant dv
    · rw [show (true && decide (q ≠ 0)) = true by simp [hq]]; exact lwsvg_of_typed_live dv (hgate hq)
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B dM dN hγ h1 h2 =>
    subst hγ
    exact .letC (q1 := q1) (q2 := q2) rfl
      (by have l1 := dM.length_eq; have l2 := dN.length_eq; simp only [List.length_cons] at l2; omega)
      (lwscg_of_typed_live dM h1) (lwscg_of_typed_live dN h2)
  | @force γ Γ v φ B dv h => exact .force (lwsvg_of_typed_live dv h)
  | @lam γ Γ M φ q A B dM h => exact .lam (lwscg_of_typed_live dM h)
  | @app γ γ₁ γ₂ Γ M v φ q A B dM dv hγ h1 hgate =>
    subst hγ
    refine .app (q := q) rfl (by rw [dM.length_eq, dv.length_eq]) (lwscg_of_typed_live dM h1) ?_
    by_cases hq : q = 0
    · rw [show (true && decide (q ≠ 0)) = false by simp [hq]]; exact lwsvg_of_typed_dormant dv
    · rw [show (true && decide (q ≠ 0)) = true by simp [hq]]; exact lwsvg_of_typed_live dv (hgate hq)
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C dv dN1 dN2 hγ hgate h2 h3 =>
    subst hγ
    refine .case (q := q) rfl
      (by have l1 := dv.length_eq; have l2 := dN1.length_eq; simp only [List.length_cons] at l2; omega)
      ?_ (lwscg_of_typed_live dN1 h2) (lwscg_of_typed_live dN2 h3)
    by_cases hq : q = 0
    · rw [show (true && decide (q ≠ 0)) = false by simp [hq]]; exact lwsvg_of_typed_dormant dv
    · rw [show (true && decide (q ≠ 0)) = true by simp [hq]]; exact lwsvg_of_typed_live dv (hgate hq)
  | @split γ γ_v γ_N Γ v N φ q A B C dv dN hγ hgate h2 =>
    subst hγ
    refine .split (q := q) rfl
      (by have l1 := dv.length_eq; have l2 := dN.length_eq; simp only [List.length_cons] at l2; omega)
      ?_ (lwscg_of_typed_live dN h2)
    by_cases hq : q = 0
    · rw [show (true && decide (q ≠ 0)) = false by simp [hq]]; exact lwsvg_of_typed_dormant dv
    · rw [show (true && decide (q ≠ 0)) = true by simp [hq]]; exact lwsvg_of_typed_live dv (hgate hq)
  | @unfold γ Γ v A dv h => exact .unfold (lwsvg_of_typed_live dv h)
  | perform dc dv h =>
    -- non-`@` pattern: names only the EXPLICIT fields `dc dv h`; `q` infers from the grade `rfl`.
    exact .perform rfl (by rw [dv.length_eq, dc.length_eq]) (lwsvg_of_typed_live dc h)
      (lwsvg_of_typed_dormant dv)
  | @handleThrows γ Γ ℓ M e φ q qc A hopA hint dM hle hbo h =>
    exact .handleThrows (lwscg_of_typed_live dM h)
  | @handleState γ Γ ℓ s₀ M e φ q qc S A hga hgr hpa hpr hint dsv dM hle hbo hsr h =>
    exact .handleState (lwsvg_of_typed_live dsv hsr) (lwscg_of_typed_live dM h)
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q qc A hna hnr hra hrr hwa hwr hint hcells dM hle hbo h =>
    exact .handleTransaction (lwscg_of_typed_live dM h)
end

-- (engine moved above `WScfg` so the def can reference `LiveCapsResolveC` / `lwscg_of_typed_live`)
/-- The COMBINED route-β invariant (ADR-0061 GRADED regrade of ADR-0057's typed-relative reshape): there
EXIST typing derivations for the focus + stack such that the GRADED liveness holds — `LWSCg` for the
focus (γ = `[]`, closed), `LWSKg` for the stack — PLUS the config freshness `FreshCfg`. The grade ties
each storage-`q` gate to the typed binder grade (vs. `LWSC`'s free `∃ q`), so a typed-DEAD cap is gated
dormant (closing the 4 elimination walls + the REDUCE dead-arg); `FreshCfg` supplies the cap-id freshness
the POP-tail needs. The output effect is `⊥` (the diagonal's target). -/
def WScfg (Co : CTy Eff Mult) (cfg : Config) : Prop :=
  ∃ (e : Eff) (C : CTy Eff Mult) (d : HasCTy [] [] cfg.2.2 e C) (dk : HasStack cfg.2.1 e C ⊥ Co),
    LiveCapsResolveC cfg.2.1 d
    ∧ LiveCapsResolveK cfg.2.1 dk ∧ FreshCfg cfg
-- ADR-0061 (#51 keystone): BOTH carried scoping witnesses are GRADE-SENSITIVE coherence carriers over
-- the bundled typings `d`/`dk` (replacing the DECOUPLED `LWSCg`/`LWSKg true` existentials): the focus
-- `LiveCapsResolveC` over `d` and the SYMMETRIC stack `LiveCapsResolveK` over `dk`. The coherent
-- `LWSCg`/`LWSKg` are DERIVED on demand (grades = typing grades by construction), closing the
-- spurious-live-cap hole on BOTH halves: a typed-DEAD cap is dormant in the derived view, never demanded
-- to resolve. REDUCE pulls a stack continuation into the focus, so the stack carrier must be coherent too.

-- **SEED (GREEN)** `wellScoped_initial` is defined just AFTER the graded lift `lwscg_of_typed` (§2′.8f)
-- which it consumes — see below §2′.8f. (The lift sits after §3 in the file's dependency order.)

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
  obtain ⟨e, C, dc, dk, hres, _, _⟩ := hWS
  obtain ⟨g, K, c⟩ := cfg
  -- DERIVE the coherent `LWSC` (grades = typing grades) from `dc` + `hres` via `lwscg_of_typed_live`,
  -- then project. Split STRUCTURALLY on the focus; cap-resolution comes from `vcap_live`.
  have hWSC : LWSC K true c := lwscg_to_lwsc (lwscg_of_typed_live dc hres)
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

/-- `Sgrade` of an all-`0` grade is all-`0` (the inert-LEAF case — `vunit`/`vint`/`vcap` type at
`zeros Γ.length`, ADR-0061 #51 PHASE A). The erased slot drops one `0`; the added `slotGrade • γ_v`
vanishes (`slotGrade (zeros n) k = 0`), leaving `zeros (n-1)` (lengths align via `hlen`). -/
theorem Sgrade_zeros (γ_v : GradeVec Mult) (k n : Nat) (hk : k < n) (hlen : γ_v.length = n - 1) :
    Sgrade γ_v k (GradeVec.zeros n) = GradeVec.zeros (n - 1) := by
  have hslot : slotGrade (GradeVec.zeros n) k = (0 : Mult) := by
    unfold slotGrade GradeVec.zeros
    rw [List.getElem?_replicate, if_pos hk, Option.getD_some]
  have herase : (GradeVec.zeros n).eraseIdx k = (GradeVec.zeros (n - 1) : GradeVec Mult) := by
    unfold GradeVec.zeros
    rw [List.eraseIdx_eq_take_drop_succ, List.take_replicate, List.drop_replicate,
      List.replicate_append_replicate]
    congr 1
    omega
  have hsmul : GradeVec.smul (0 : Mult) γ_v = GradeVec.zeros (n - 1) := by
    unfold GradeVec.smul GradeVec.zeros
    rw [← hlen]
    simp only [zero_mul, List.map_const']
  simp only [Sgrade, hslot, herase, hsmul]
  simp [GradeVec.add, GradeVec.zeros]

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
    have ihs := lwsvg_subst_gen hvl hcl hzsf γ_v k (by simp [GradeVec.zeros]) hs
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


/-! A cap-free (`capsV v = []`) typed value vacuously satisfies `LiveCapsResolveV` — no `vcap` leaf to
discharge. The seed's `LiveCapsResolve` (the new coherence carrier) at a `VcapFree` initial config. -/
mutual
theorem liveCapsResolveV_of_noCaps {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} (d : HasVTy γ Γ v A) (h : capsV v = []) : LiveCapsResolveV K d := by
  cases d with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar hget => exact .vvar (h := hget)
  | vcap => simp [capsV] at h
  | vthunk hM => exact .vthunk (liveCapsResolveC_of_noCaps hM (by simpa [capsV] using h))
  | inl hv => exact .inl (liveCapsResolveV_of_noCaps hv (by simpa [capsV] using h))
  | inr hv => exact .inr (liveCapsResolveV_of_noCaps hv (by simpa [capsV] using h))
  | pair hv hw hγ =>
    simp only [capsV, List.append_eq_nil_iff] at h
    exact .pair (hγ := hγ) (liveCapsResolveV_of_noCaps hv h.1) (liveCapsResolveV_of_noCaps hw h.2)
  | fold hv => exact .fold (liveCapsResolveV_of_noCaps hv (by simpa [capsV] using h))
theorem liveCapsResolveC_of_noCaps {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {φ : Eff} {C : CTy Eff Mult} (d : HasCTy γ Γ c φ C) (h : capsC c = []) :
    LiveCapsResolveC K d := by
  cases d with
  | ret hv hγ => exact .ret (hγ := hγ) (fun _ => liveCapsResolveV_of_noCaps hv (by simpa [capsC] using h))
  | letC hM hN hγ =>
    simp only [capsC, List.append_eq_nil_iff] at h
    exact .letC (hγ := hγ) (liveCapsResolveC_of_noCaps hM h.1) (liveCapsResolveC_of_noCaps hN h.2)
  | force hv => exact .force (liveCapsResolveV_of_noCaps hv (by simpa [capsC] using h))
  | lam hM => exact .lam (liveCapsResolveC_of_noCaps hM (by simpa [capsC] using h))
  | app hM hv hγ =>
    simp only [capsC, List.append_eq_nil_iff] at h
    exact .app (hγ := hγ) (liveCapsResolveC_of_noCaps hM h.1) (fun _ => liveCapsResolveV_of_noCaps hv h.2)
  | case hv hN₁ hN₂ hγ =>
    simp only [capsC, List.append_eq_nil_iff] at h
    exact .case (hγ := hγ) (fun _ => liveCapsResolveV_of_noCaps hv h.1.1)
      (liveCapsResolveC_of_noCaps hN₁ h.1.2) (liveCapsResolveC_of_noCaps hN₂ h.2)
  | split hv hN hγ =>
    simp only [capsC, List.append_eq_nil_iff] at h
    exact .split (hγ := hγ) (fun _ => liveCapsResolveV_of_noCaps hv h.1) (liveCapsResolveC_of_noCaps hN h.2)
  | unfold hv => exact .unfold (liveCapsResolveV_of_noCaps hv (by simpa [capsC] using h))
  | @perform γ_c γ_v Γ cv ℓ op v φ q A B hc hle hopA hopR hv =>
    simp only [capsC, List.append_eq_nil_iff] at h
    exact .perform (q := q) (hle := hle) (hopA := hopA) (hopR := hopR) hc hv
      (liveCapsResolveV_of_noCaps hc h.1)
  | handleThrows hopA hint hM hle hbo =>
    exact .handleThrows (hopA := hopA) (hint := hint) (hle := hle) (hbo := hbo)
      (liveCapsResolveC_of_noCaps hM (by simpa [capsC, capsH] using h))
  | handleState hga hgr hpa hpr hint hs hM hle hbo =>
    simp only [capsC, capsH, List.append_eq_nil_iff] at h
    exact .handleState (hga := hga) (hgr := hgr) (hpa := hpa) (hpr := hpr) (hint := hint)
      (hle := hle) (hbo := hbo) (liveCapsResolveV_of_noCaps hs h.1) (liveCapsResolveC_of_noCaps hM h.2)
  | handleTransaction hna hnr hra hrr hwa hwr hint hcells hM hle hbo =>
    exact .handleTransaction (hna := hna) (hnr := hnr) (hra := hra) (hrr := hrr) (hwa := hwa)
      (hwr := hwr) (hint := hint) (hcells := hcells) (hle := hle) (hbo := hbo)
      (liveCapsResolveC_of_noCaps hM (by
        simp only [capsC, capsH, List.append_eq_nil_iff] at h; exact h.2))
end

/-! **DE-RISK (#51 — the held-thunk-cap residual): CLOSED BY CONSTRUCTION in `lwscg_of_typed_live`.**
The team-lead flagged "a live cap buried in a held unperformed thunk inside `M`" as the spot the design
hand-waved. The mechanism is now machine-checked: `lwscg_of_typed_live`'s `ret`/`app`/`case`/`split`
branches `by_cases hq : q = 0`, and at `q = 0` route the value (incl. a held `vcap n ℓ`) through
`lwsvg_of_typed_dormant` — which builds `vcap_dormant` with NO `ResolvesLabel` obligation. Correspondingly
`LiveCapsResolveC`'s storage gates are `q ≠ 0 → …`, so a typed-DEAD cap is NEVER required to resolve.
The GRADE catches the held cap where B-occ does not: for `letC M N` with `M : F q1 A`, a cap of type
`cap ℓ` in `M`'s returned value sits in the dead INTERMEDIATE `A` (∉ the popped result type `C`, so
`¬labelOccurs ℓ C` is satisfied yet says nothing) — but if `q1 = 0` the `ret`-gate makes it dormant, and
if `q1 ≠ 0` the cap propagates into `N` where B-occ/row apply. No standalone witness theorem (the
indexed-predicate constructor elaboration is finicky for a single `q = 0` literal); the guarantee lives
in the engine itself. -/

/-- **SEED (GREEN).** A `VcapFree` closed program satisfies the GRADED invariant `WScfg` at the initial
config — no caps to resolve (the graded lift's side-condition + the `FreshCfg` focus-cap bound are
vacuous), the stack is empty (`LWSKg.nil`), the counter is `0` (`CapsBelow`/`StratFresh` trivial). The
typing derivations come from `hty`. (Placed here, after the §2′.8f lift it consumes.) -/
theorem wellScoped_initial (c : Comp) (hvf : VcapFree c) {Co : CTy Eff Mult}
    (hty : HasConfigTy (0, [], c) ⊥ Co) : WScfg Co (0, [], c) := by
  obtain ⟨e, C, hfocus, hstack⟩ := hty
  -- the stack is `[]`, so `hstack : HasStack [] e C ⊥ Co` must be `nil` (`e = ⊥`, `C = Co`).
  cases hstack
  -- the carried scoping witness is now `LiveCapsResolveC` — VACUOUS at a `VcapFree` config.
  refine ⟨⊥, Co, hfocus, .nil, liveCapsResolveC_of_noCaps hfocus hvf, .nil, ?_⟩
  exact ⟨trivial, fun p hp => absurd (hvf ▸ hp) (by simp [GradeVec.zeros]), trivial,
      by intro p hp; simp [capsK] at hp⟩

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
`HasCTy ∧ HasStack ∧ LWSCg ∧ LWSKg ∧ FreshCfg` (ADR-0061 GRADED regrade). The TYPING half
(`HasCTy`/`HasStack`) rides `hasConfigTy_step`; `FreshCfg` rides `freshCfg_step` (§3.0); the GRADED
WELL-SCOPED half (`LWSCg`/`LWSKg`) is rebuilt per arm via two coarse obligations
(`lwsg_step_nonperform` / `lwsg_step_dispatch`), each discharged in Phase 2 from the named building blocks
below. PHASE-1b SKELETON: the obligations + building blocks are SORRIED with their plan; `wsCfg_step`
re-stated over the new invariant + builds. The sorry map:
  • `lwsg_step_nonperform`   — PUSH (graded restack) · REDUCE (the eliminations: `lwsvg_closed_regrade` +
                               `lwscg_subst`) · MINT (graded restack_handleF) · POP (`lwscg_returnEscape`
                               focus + `lwskg_pop_fresh` tail) · force/unfold (direct).  [Phase 2]
  • `lwsg_step_dispatch`     — DISPATCH resume (#35).
  • `freshCfg_step`          — the freshness arm (§3.0).  [Phase 2]
  • `lwsvg_closed_regrade`   — REDUCE workhorse generaliser.  [Phase 2, HARD-not-FALSE]
  • `lwscg_returnEscape`     — POP focus, the spike ported over the GRADE.  [Phase 2]
  • `lwskg_pop_fresh`        — POP tail, via stratified freshness.  [Phase 2]
  • `handleF_bocc_inv`       — re-exposes the discarded answer-type B-occ for the POP arm.  [Phase 2] -/

/-- ⚠ **REFUTATION (REFUTE-FIRST, kept regression).** `lwsvg_closed_regrade` AS STATED (`∀ γ' b'`) is
FALSE. The doc's "no `vvar` leaves ⇒ γ-irrelevant" misses the SCALE gates: `ret`/`app`/`case`/`split`'s
`decide(q≠0)` couples the AMBIENT grade to cap liveness even for a CLOSED value. Witness (`K = []`, a
closed thunk holding a NON-resolving cap): `LWSVg [] [] true (vthunk (ret (vcap 0 0)))` holds via `ret`'s
`q = 0` DORMANT gate, but `LWSVg [] [1] true …` does NOT — the nonzero target forces `q ≠ 0` ⇒ the cap
must be `vcap_live` ⇒ `ResolvesLabel [] 0 0` = `splitAtId [] 0 = none`. So a closed-but-inner-dormant cap
can't be re-graded live; the statement needs restatement (hereditary liveness, or the consumer's actual
narrower need — `kernel`/lead call). Independent of the in-file `sorry` (the over-general claim is the
hypothesis `H`). -/
theorem lwsvg_closed_regrade_refute
    (H : ∀ {K : EvalCtx} {γ0 : GradeVec Mult} {v : Val},
         (∀ j, Val.shiftFrom j v = v) → LWSVg K γ0 true v →
         ∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg K γ' b' v) : False := by
  have hcl : ∀ j, Val.shiftFrom j (Val.vthunk (Comp.ret (Val.vcap 0 0)))
      = Val.vthunk (Comp.ret (Val.vcap 0 0)) := fun _ => rfl
  have h0 : LWSVg ([] : EvalCtx) ([] : GradeVec Mult) true
      (Val.vthunk (Comp.ret (Val.vcap 0 0))) := by
    refine .vthunk (.ret (q := 0) (γ' := []) ?_ ?_)
    · simp [GradeVec.smul, GradeVec.zeros]
    · rw [show (true && decide ((0 : Mult) ≠ 0)) = false from by simp]; exact .vcap_dormant
  have hbad := H hcl h0 [(1 : Mult)] true
  cases hbad with
  | vthunk hc =>
    cases hc with
    | @ret _ γ' _ _ q hγ hvc =>
      have hlen : γ'.length = 1 := by
        have h := congrArg List.length hγ
        simp only [smul_length, List.length_cons, List.length_nil] at h; omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
      rw [show (q • [a] : GradeVec Mult) = [q * a] from by simp [GradeVec.smul]] at hγ
      have h1 : (1 : Mult) = q * a := by simpa using hγ
      have hq : q ≠ 0 := by rintro rfl; rw [zero_mul] at h1; exact one_ne_zero h1
      rw [show (true && decide (q ≠ 0)) = true from by simp [hq]] at hvc
      cases hvc with
      | vcap_live hr =>
        obtain ⟨Kᵢ, hh, Kₒ, hsp, _⟩ := hr
        simp [splitAtId] at hsp

-- (PRUNED #51) `lwsvg_closed_regrade` (the `∀γ'b'` REDUCE generaliser, sorry) is DEAD: the
-- `of_typed_live` coherence path supersedes the `lwscg_subst` `∀γ'b'` hypothesis it fed (the subst arm
-- preserves `LiveCapsResolveC` directly, no closed-value regrade). The refuted form stays as the kept
-- witness `lwsvg_closed_regrade_refute`.

/-- **handleF_bocc_inv (Phase 2 — re-expose the discarded B-occ for the POP arm).** The frozen `handleF`/
`handleAny` typing inversions DISCARD the `¬labelOccurs` (B-occ) premise (ADR-0057); this inversion
RE-EXPOSES it. From a typed handle-frame atop the stack + the focus typed at `e`/`C`, expose the focus
answer-type B-occ (`¬labelOccurs (label hd) C`) + the row separation (`¬ label hd ≤ e`) that
`lwscg_returnEscape` consumes. -/
theorem handleF_bocc_inv {g' : Nat} {hd : Handler} {K' : EvalCtx} {e : Eff} {C Co : CTy Eff Mult}
    (hs : HasStack (Frame.handleF g' hd :: K') e C ⊥ Co) :
    ¬ CTy.labelOccurs (Handler.label hd) C := by
  -- (②, lead-approved) The row conjunct `¬(labelEff ℓ ≤ e)` was DROPPED: refutable for general `e`
  -- (`e = labelEff ℓ`, `φ = ⊥` satisfies the frame premise yet makes it false — the handle body MAY
  -- perform `ℓ`). The POP caller supplies `hrow` itself from `labelEff_ne_bot` at its `ret`-focus `e = ⊥`.
  -- Expose the answer-type B-occ the frozen `handleF`/`handleAny_inv` discard: `C = F q A`,
  -- `CTy.labelOccurs ℓ (F q A) = VTy.labelOccurs ℓ A = LabelOccurs ℓ A`, which the frame premise negates.
  cases hs with
  | handleF _ _ _ hbocc _ => exact hbocc
  | stateF _ _ _ _ _ _ _ hbocc _ => exact hbocc
  | transactionF _ _ _ _ _ _ _ _ _ hbocc _ => exact hbocc

/- **lwscg_returnEscape (Phase 2 — the POP focus arm, ⊥-row return-escape over the GRADE).** The graded
restatement of the spike `lwsc_returnEscape` (above): a focus typed at the popped handler's answer type
`C` with `¬labelOccurs ℓ C` re-homes its scoping past `handleF g' hd`. The spike's value-layer cases
(`lwsv_returnEscape`) port directly; the gated DEAD elimination sub-cases close via
`lwsvg_dormant_stack_indep`; the LIVE/`letC` sub-cases need the grade-type-occurrence coherence. -/
-- (①, lead-approved) the type-side grade `γ_ty` is DECOUPLED from the `LWSCg` grade `γ` (independent
-- inductives; their grades diverge under binders/splits). `d` is used for TYPE STRUCTURE only.
mutual
theorem lwsvg_returnEscape {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ : Label}
    (hℓ : Handler.label hd = ℓ) {γ_ty : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val}
    {A : VTy Eff Mult} {γ : GradeVec Mult} {b : Bool} (d : HasVTy γ_ty Γ v A)
    (hbo : ¬ VTy.labelOccurs ℓ A) (h : LWSVg (Frame.handleF g' hd :: K') γ b v) : LWSVg K' γ b v := by
  cases d with
  | vunit => cases h with | vunit => exact .vunit
  | vint => cases h with | vint => exact .vint
  | vvar _ => cases h with | vvar hh => exact .vvar hh
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
  | @vthunk γt Γ M φ B hM =>
    cases h with
    | vthunk hc =>
      exact .vthunk (lwscg_returnEscape hℓ hM (fun hx => hbo (Or.inl hx)) (fun hx => hbo (Or.inr hx)) hc)
  | inl ha =>
    cases h with | inl hsc => exact .inl (lwsvg_returnEscape hℓ ha (fun hx => hbo (Or.inl hx)) hsc)
  | inr ha =>
    cases h with | inr hsc => exact .inr (lwsvg_returnEscape hℓ ha (fun hx => hbo (Or.inr hx)) hsc)
  | pair ha hcv hγt =>
    cases h with
    | pair hγg hleng h1 h2 =>
      exact .pair hγg hleng (lwsvg_returnEscape hℓ ha (fun hx => hbo (Or.inl hx)) h1)
        (lwsvg_returnEscape hℓ hcv (fun hx => hbo (Or.inr hx)) h2)
  | @fold _ _ _ Ai ha =>
    cases h with
    | fold hsc => exact .fold (lwsvg_returnEscape hℓ ha (fun hx => hbo (labelOccurs_unrollMu ℓ Ai hx)) hsc)
theorem lwscg_returnEscape {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ : Label}
    (hℓ : Handler.label hd = ℓ) {γ_ty : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp}
    {φ : Eff} {C : CTy Eff Mult} {γ : GradeVec Mult} {b : Bool} (d : HasCTy γ_ty Γ c φ C)
    (hrow : ¬ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ) (hres : ¬ CTy.labelOccurs ℓ C)
    (h : LWSCg (Frame.handleF g' hd :: K') γ b c) : LWSCg K' γ b c := by
  cases d with
  | @ret γt γt' Γ v A q hv hγt =>
    cases h with
    | ret hγg hvsc => exact .ret hγg (lwsvg_returnEscape hℓ hv hres hvsc)
  | force hv =>
    cases h with
    | force hvsc => exact .force (lwsvg_returnEscape hℓ hv (fun hx => hx.elim hrow hres) hvsc)
  | lam hM =>
    cases h with
    | lam hMsc => exact .lam (lwscg_returnEscape hℓ hM hrow (fun hx => hres (Or.inr hx)) hMsc)
  | @perform γtc γtv Γ cv ℓ2 op v φ q A B hc hle hopA hopR hv =>
    cases h with
    | perform hγg hleng h1 h2 =>
      refine .perform hγg hleng ?_ (lwsvg_dormant_stack_indep h2)
      exact lwsvg_returnEscape hℓ hc
        (by intro hx; simp only [VTy.labelOccurs] at hx; subst hx; exact hrow hle) h1
  | unfold hv => sorry
  | letC hM hN hγt => sorry
  | app hM hv hγt => sorry
  | case hv hN₁ hN₂ hγt => sorry
  | split hv hN hγt => sorry
  | handleThrows _ _ hM _ _ => sorry
  | handleState _ _ _ _ _ hs hM _ _ => sorry
  | handleTransaction _ _ _ _ _ _ _ _ hM _ _ => sorry
end

/-! ### §3.6 — GRADED pop re-homing (the POP tail arm). The graded mirror of `lwsvp_pop_restack`: a
value/comp whose caps are all `≠ g'` re-homes its resolution context past the popped `handleF g'` frame
(`resolvesLabel_pop` at the `vcap_live` leaf; dormant + non-`vcap` leaves are structural). The `≠ g'`
condition is supplied per-frame by `capsK K' < g'` — the FLAT stored-cap bound (`CapsBelow` omits the
`stateF`-stored value's caps, so `capsK` is the right hypothesis, mirroring the `freshCfg_step` fix). -/
mutual
theorem lwsvg_pop_fresh {g' : Nat} {hd : Handler} {K' : EvalCtx} {γ : GradeVec Mult} {b : Bool}
    {v : Val} (hv : LWSVg (Frame.handleF g' hd :: K') γ b v)
    (hng : ∀ p ∈ capsV v, p.1 ≠ g') : LWSVg K' γ b v := by
  cases hv with
  | vunit => exact .vunit
  | vint => exact .vint
  | vvar h => exact .vvar h
  | @vcap_live _ n ℓ hr => exact .vcap_live (resolvesLabel_pop (hng (n, ℓ) (by simp [capsV])) hr)
  | vcap_dormant => exact .vcap_dormant
  | vthunk h => exact .vthunk (lwscg_pop_fresh h (fun p hp => hng p (by simpa only [capsV] using hp)))
  | inl h => exact .inl (lwsvg_pop_fresh h (fun p hp => hng p (by simpa only [capsV] using hp)))
  | inr h => exact .inr (lwsvg_pop_fresh h (fun p hp => hng p (by simpa only [capsV] using hp)))
  | pair hγ hlen h1 h2 =>
      exact .pair hγ hlen
        (lwsvg_pop_fresh h1 (fun p hp => hng p (by simp only [capsV]; exact List.mem_append_left _ hp)))
        (lwsvg_pop_fresh h2 (fun p hp => hng p (by simp only [capsV]; exact List.mem_append_right _ hp)))
  | fold h => exact .fold (lwsvg_pop_fresh h (fun p hp => hng p (by simpa only [capsV] using hp)))
theorem lwscg_pop_fresh {g' : Nat} {hd : Handler} {K' : EvalCtx} {γ : GradeVec Mult} {b : Bool}
    {c : Comp} (hc : LWSCg (Frame.handleF g' hd :: K') γ b c)
    (hng : ∀ p ∈ capsC c, p.1 ≠ g') : LWSCg K' γ b c := by
  cases hc with
  | ret hγ h => exact .ret hγ (lwsvg_pop_fresh h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | letC hγ hlen h1 h2 =>
      exact .letC hγ hlen
        (lwscg_pop_fresh h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (lwscg_pop_fresh h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | force h => exact .force (lwsvg_pop_fresh h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | lam h => exact .lam (lwscg_pop_fresh h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | app hγ hlen h1 h2 =>
      exact .app hγ hlen
        (lwscg_pop_fresh h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (lwsvg_pop_fresh h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | case hγ hlen h1 h2 h3 =>
      exact .case hγ hlen
        (lwsvg_pop_fresh h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ (List.mem_append_left _ hp))))
        (lwscg_pop_fresh h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ (List.mem_append_right _ hp))))
        (lwscg_pop_fresh h3 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | split hγ hlen h1 h2 =>
      exact .split hγ hlen
        (lwsvg_pop_fresh h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (lwscg_pop_fresh h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | unfold h => exact .unfold (lwsvg_pop_fresh h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | perform hγ hlen h1 h2 =>
      exact .perform hγ hlen
        (lwsvg_pop_fresh h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (lwsvg_pop_fresh h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | handleThrows h =>
      exact .handleThrows (lwscg_pop_fresh h (fun p hp => hng p (by simpa only [capsC, capsH, List.nil_append] using hp)))
  | handleState hs h =>
      exact .handleState
        (lwsvg_pop_fresh hs (fun p hp => hng p (by simp only [capsC, capsH]; exact List.mem_append_left _ hp)))
        (lwscg_pop_fresh h (fun p hp => hng p (by simp only [capsC, capsH]; exact List.mem_append_right _ hp)))
  | handleTransaction h =>
      exact .handleTransaction (lwscg_pop_fresh h (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
end

/-- Re-home an `LWSKg`'s resolution context past a popped `handleF g'` frame: every stored cap on the
tail `Sg` is `< g'` (`capsK Sg`), so `≠ g'`, so each frame's stored value re-homes (`lws*g_pop_fresh`). -/
theorem lwskg_rehome {g' : Nat} {hd : Handler} {K' : EvalCtx} {γ : GradeVec Mult} {b : Bool} :
    ∀ {Sg : EvalCtx}, LWSKg (Frame.handleF g' hd :: K') Sg γ b →
    (∀ p ∈ capsK Sg, p.1 < g') → LWSKg K' Sg γ b
  | [], h, _ => by cases h; exact .nil
  | (Frame.letF N :: Sg), h, hck => by
      cases h with
      | letF hN hK =>
        exact .letF (lwscg_pop_fresh hN (fun p hp => by
            have := hck p (by simp only [capsK]; exact List.mem_append_left _ hp); omega))
          (lwskg_rehome hK (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))
  | (Frame.appF w :: Sg), h, hck => by
      cases h with
      | appF hv hK =>
        exact .appF (lwsvg_pop_fresh hv (fun p hp => by
            have := hck p (by simp only [capsK]; exact List.mem_append_left _ hp); omega))
          (lwskg_rehome hK (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))
  | (Frame.handleF n hh :: Sg), h, hck => by
      cases h with
      | handleF hK =>
        exact .handleF (lwskg_rehome hK (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))
      | stateF hs hK =>
        exact .stateF (lwsvg_pop_fresh hs (fun p hp => by
            have := hck p (by simp only [capsK, capsH]; exact List.mem_append_left _ hp); omega))
          (lwskg_rehome hK (fun p hp => hck p (by simp only [capsK, capsH]; exact List.mem_append_right _ hp)))
      | transactionF hK =>
        exact .transactionF (lwskg_rehome hK (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))

/-- **lwskg_pop_fresh (Phase 2 — the POP tail arm, via FLAT stored-cap freshness).** Popping `handleF g'`:
every STORED cap on the tail `K'` has id `< g'` (`capsK K' < g'`, the `FreshCfg` conjunct), hence `≠ g'`,
so each re-homes past the popped frame (`resolvesLabel_pop`, via `lwskg_rehome`). The `LWSKg` analogue of
`lwsvp_pop_restack` — the `n ≠ g'` comes from FRESHNESS (the tail predates `g'`), not B-occ. -/
theorem lwskg_pop_fresh {g' : Nat} {hd : Handler} {K' : EvalCtx} {γ : GradeVec Mult} {b : Bool}
    (hck : ∀ p ∈ capsK K', p.1 < g')
    (h : LWSKg (Frame.handleF g' hd :: K') (Frame.handleF g' hd :: K') γ b) :
    LWSKg K' K' γ b := by
  have hK : LWSKg (Frame.handleF g' hd :: K') K' γ b := by
    cases h with
    | handleF hK => exact hK
    | stateF _ hK => exact hK
    | transactionF hK => exact hK
  exact lwskg_rehome hK hck

/-! ### §3.6′ — CARRIER pop re-homing (ADR-0061, the #51 PIECE-1 ripple). The `LiveCapsResolveC/V/K`
mirror of `lws*g_pop_fresh`: re-home the carrier's RESOLUTION CONTEXT past a popped `handleF g'` frame,
given every stored cap is `< g'` (so `≠ g'`). At a `vcap` leaf the freshness supplies `n ≠ g'` ⇒
`resolvesLabel_pop`; the gated (`q = 0`) value positions carry a VACUOUS obligation, so they re-home for
free; non-cap leaves are structural. This replaces `lwskg_pop_fresh` as the POP-tail building block now
that `WScfg` carries `LiveCapsResolveK` (the decoupled `LWSKg` retired). -/
mutual
/-- `LiveCapsResolveV` re-homes its resolution context past a popped `handleF g'` frame (caps `≠ g'`). -/
theorem liveCapsResolveV_pop {g' : Nat} {hd : Handler} {K' : EvalCtx}
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    {dv : HasVTy γ Γ v A} (h : LiveCapsResolveV (Frame.handleF g' hd :: K') dv)
    (hng : ∀ p ∈ capsV v, p.1 ≠ g') : LiveCapsResolveV K' dv := by
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar Γ i A hmem => exact .vvar (h := hmem)
  | @vcap Γ n ℓ hr => exact .vcap (resolvesLabel_pop (hng (n, ℓ) (by simp [capsV])) hr)
  | @vthunk γ Γ M φ B dM h =>
      exact .vthunk (liveCapsResolveC_pop h (fun p hp => hng p (by simpa only [capsV] using hp)))
  | @inl γ Γ v A B dv h =>
      exact .inl (liveCapsResolveV_pop h (fun p hp => hng p (by simpa only [capsV] using hp)))
  | @inr γ Γ v A B dv h =>
      exact .inr (liveCapsResolveV_pop h (fun p hp => hng p (by simpa only [capsV] using hp)))
  | @pair γ γv γw Γ v w A B dv dw hγ h1 h2 =>
      exact .pair (hγ := hγ)
        (liveCapsResolveV_pop h1 (fun p hp => hng p (by simp only [capsV]; exact List.mem_append_left _ hp)))
        (liveCapsResolveV_pop h2 (fun p hp => hng p (by simp only [capsV]; exact List.mem_append_right _ hp)))
  | @fold γ Γ v A dv h =>
      exact .fold (liveCapsResolveV_pop h (fun p hp => hng p (by simpa only [capsV] using hp)))
/-- `LiveCapsResolveC` re-homes its resolution context past a popped `handleF g'` frame (caps `≠ g'`).
The `q = 0` gated value positions (`ret`/`app`/`case`/`split`) re-home under the vacuous gate. -/
theorem liveCapsResolveC_pop {g' : Nat} {hd : Handler} {K' : EvalCtx}
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {φ : Eff} {C : CTy Eff Mult}
    {dc : HasCTy γ Γ c φ C} (h : LiveCapsResolveC (Frame.handleF g' hd :: K') dc)
    (hng : ∀ p ∈ capsC c, p.1 ≠ g') : LiveCapsResolveC K' dc := by
  cases h with
  | @ret γ γ' Γ v A q dv hγ hgate =>
      exact .ret (hγ := hγ) (fun hq => liveCapsResolveV_pop (hgate hq)
        (fun p hp => hng p (by simpa only [capsC] using hp)))
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B dM dN hγ h1 h2 =>
      exact .letC (hγ := hγ)
        (liveCapsResolveC_pop h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (liveCapsResolveC_pop h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | @force γ Γ v φ B dv h =>
      exact .force (liveCapsResolveV_pop h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | @lam γ Γ M φ q A B dM h =>
      exact .lam (liveCapsResolveC_pop h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | @app γ γ₁ γ₂ Γ M v φ q A B dM dv hγ h1 hgate =>
      exact .app (hγ := hγ)
        (liveCapsResolveC_pop h1 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (fun hq => liveCapsResolveV_pop (hgate hq)
          (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C dv dN1 dN2 hγ hgate h2 h3 =>
      exact .case (hγ := hγ)
        (fun hq => liveCapsResolveV_pop (hgate hq)
          (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ (List.mem_append_left _ hp))))
        (liveCapsResolveC_pop h2
          (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ (List.mem_append_right _ hp))))
        (liveCapsResolveC_pop h3
          (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | @split γ γ_v γ_N Γ v N φ q A B C dv dN hγ hgate h2 =>
      exact .split (hγ := hγ)
        (fun hq => liveCapsResolveV_pop (hgate hq)
          (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
        (liveCapsResolveC_pop h2 (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
  | @unfold γ Γ v A dv h =>
      exact .unfold (liveCapsResolveV_pop h (fun p hp => hng p (by simpa only [capsC] using hp)))
  | @perform _ γ_c γ_v Γ cv ℓ op v φ A B q dc hle hopA hopR dv h =>
      exact .perform (q := q) (hle := hle) (hopA := hopA) (hopR := hopR) dc dv
        (liveCapsResolveV_pop h (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_left _ hp)))
  | @handleThrows γ Γ ℓ M e φ q qc A hopA hint dM hle hbo h =>
      exact .handleThrows (hopA := hopA) (hint := hint) (hle := hle) (hbo := hbo)
        (liveCapsResolveC_pop h (fun p hp => hng p (by simpa only [capsC, capsH, List.nil_append] using hp)))
  | @handleState γ Γ ℓ s₀ M e φ q qc S A hga hgr hpa hpr hint dsv dM hle hbo hsr h =>
      exact .handleState (hga := hga) (hgr := hgr) (hpa := hpa) (hpr := hpr) (hint := hint) (hle := hle) (hbo := hbo)
        (liveCapsResolveV_pop hsr (fun p hp => hng p (by simp only [capsC, capsH]; exact List.mem_append_left _ hp)))
        (liveCapsResolveC_pop h (fun p hp => hng p (by simp only [capsC, capsH]; exact List.mem_append_right _ hp)))
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q qc A hna hnr hra hrr hwa hwr hint hcells dM hle hbo h =>
      exact .handleTransaction (hna := hna) (hnr := hnr) (hra := hra) (hrr := hrr) (hwa := hwa) (hwr := hwr)
        (hint := hint) (hcells := hcells) (hle := hle) (hbo := hbo)
        (liveCapsResolveC_pop h (fun p hp => hng p (by simp only [capsC]; exact List.mem_append_right _ hp)))
end

/-- Re-home a `LiveCapsResolveK`'s resolution context past a popped `handleF g'` frame: every stored cap
on the scoped stack `Kfr` is `< g'` (`capsK Kfr`), so each frame's stored term re-homes
(`liveCapsResolve*_pop`). The carrier mirror of `lwskg_rehome`; the scoped stack `dk` is unchanged. -/
theorem liveCapsResolveK_rehome {g' : Nat} {hd : Handler} {K' : EvalCtx} :
    ∀ {Kfr : EvalCtx} {ein : Eff} {Cin : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult}
      {dk : HasStack Kfr ein Cin eo Co},
      LiveCapsResolveK (Frame.handleF g' hd :: K') dk → (∀ p ∈ capsK Kfr, p.1 < g') →
      LiveCapsResolveK K' dk := by
  intro Kfr ein Cin eo Co dk h hck
  induction h with
  | nil => exact .nil
  | @letF Kfr N e₁ e₂ eo q qk A B Co dN dK hN hK ih =>
      exact .letF
        (liveCapsResolveC_pop hN (fun p hp => by
          have := hck p (by simp only [capsK]; exact List.mem_append_left _ hp); omega))
        (ih (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))
  | @appF Kfr v e eo A B Co q dv dK hv hK ih =>
      exact .appF
        (fun hq => liveCapsResolveV_pop (hv hq) (fun p hp => by
          have := hck p (by simp only [capsK]; exact List.mem_append_left _ hp); omega))
        (ih (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))
  | @handleF Kfr n ℓ e φ eo q A Co hr hint hle hbo dK hK ih =>
      exact .handleF (hr := hr) (hint := hint) (hle := hle) (hbo := hbo)
        (ih (fun p hp => hck p (by simpa only [capsK, capsH, List.nil_append] using hp)))
  | @stateF Kfr n ℓ s e φ eo q A S Co hga hgr hpa hpr hint ds hle hbo dK hsr hK ih =>
      exact .stateF (hga := hga) (hgr := hgr) (hpa := hpa) (hpr := hpr) (hint := hint) (hle := hle) (hbo := hbo)
        (liveCapsResolveV_pop hsr (fun p hp => by
          have := hck p (by simp only [capsK, capsH]; exact List.mem_append_left _ hp); omega))
        (ih (fun p hp => hck p (by simp only [capsK, capsH]; exact List.mem_append_right _ hp)))
  | @transactionF Kfr n ℓ Θ e φ eo q A Co hna hnr hra hrr hwa hwr hint hcells hle hbo dK hK ih =>
      exact .transactionF (hna := hna) (hnr := hnr) (hra := hra) (hrr := hrr) (hwa := hwa) (hwr := hwr)
        (hint := hint) (hcells := hcells) (hle := hle) (hbo := hbo)
        (ih (fun p hp => hck p (by simp only [capsK]; exact List.mem_append_right _ hp)))

/-- **VALUE substitution** (ADR-0061, #51 PHASE A — the dormant-value-position prerequisite). The value
mirror of `HasCTy.subst_gen`, derived as a sound COROLLARY of it (single-source: no second proof of the
subst logic) — substitute into `ret w` as a COMPUTATION, then invert the `ret` to extract the value
typing. Used by the gated comp-subst arms (ret/app/case/split q=0 branch, perform's arg) where the
substituted value's TYPING is needed without a carrier. -/
theorem HasVTy.subst_gen (Δ : TyCtx Eff Mult) {Γ : TyCtx Eff Mult} {γ_v : GradeVec Mult} {v : Val}
    {A : VTy Eff Mult} (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ_w : GradeVec Mult} {w : Val} {A_w : VTy Eff Mult} (hw : HasVTy γ_w (Δ ++ A :: Γ) w A_w) :
    HasVTy (Sgrade γ_v Δ.length γ_w) (Δ ++ Γ) (Val.substFrom Δ.length v w) A_w := by
  have hc : HasCTy γ_w (Δ ++ A :: Γ) (Comp.ret w) ⊥ (CTy.F 1 A_w) := HasCTy.ret hw (gv_one_smul γ_w).symm
  have hsub : HasCTy (Sgrade γ_v Δ.length γ_w) (Δ ++ Γ)
      (Comp.substFrom Δ.length v (Comp.ret w)) ⊥ (CTy.F 1 A_w) := HasCTy.subst_gen Δ hv hc
  rw [Comp.substFrom] at hsub
  generalize hg : Sgrade γ_v Δ.length γ_w = G at hsub ⊢
  cases hsub with
  | ret hw' hγ' => rw [gv_one_smul] at hγ'; rw [hγ']; exact hw'

/-! ### §3.6b — CARRIER WEAKENING (ADR-0061, #51 PIECE 2 PHASE A — the BINDER prerequisite).

The carrier mirror of `HasVTy.weaken`/`HasCTy.weaken` (Metatheory:530/644): inserting a fresh binder `A'`
at level `k` (shifting the term) PRESERVES the carrier. Needed by the comp-subst BINDER arms
(letC/lam/case/split/handle): the recursor hands the comp IH at the SHIFTED context `A₀::Δ++Γ`, so the
substituted value `v` must be re-typed there (`hv.weaken 0 …`) WITH its carrier — that's
`liveCapsResolveV_weaken hvres`. REFUTE-TESTED sound (closedness-INDEPENDENT): `weaken` only shifts vvar
INDICES (the `vvar` carrier leaf is obligation-free) and leaves vcaps UNTOUCHED (caps closed ⟹ shift = id),
so every `ResolvesLabel K n ℓ` is identical. The INDEXED form (over `hv.weaken …`) is what the binder IH
consumes (it wants the carrier over the SPECIFIC weakened typing, not an existential).
PROOF (PENDING): the index changes (`hv → hv.weaken`), and `hv.weaken` is an opaque theorem-output, so the
proof needs the `LiveCapsResolveV.rec` harness + per-arm transport via `HasVTy.weaken`'s constructor
behaviour (the same recursor pattern as the carrier-subst, simpler — no grade-gate threading). -/
/-- Motive for the VALUE carrier-weaken recursor: the carrier is preserved under `HasVTy.weaken` at any
cutoff `k`. Indexed (not existential): the consumer (subst binder arms) wants the carrier over the SPECIFIC
weakened typing `hv.weaken k hk A'`. Closed via definitional proof-irrelevance (`HasVTy : Prop`) — each arm
rebuilds the matching constructor; the opaque `hv.weaken` output is defeq (or grade-eq-cast) to it. -/
def VweakenMotive (K : EvalCtx) {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (hv : HasVTy γ Γ v A) (_ : LiveCapsResolveV K hv) : Prop :=
  ∀ (k : Nat) (hk : k ≤ Γ.length) (A' : VTy Eff Mult), LiveCapsResolveV K (hv.weaken k hk A')

def CweakenMotive (K : EvalCtx) {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {e : Eff}
    {B : CTy Eff Mult} (hc : HasCTy γ Γ c e B) (_ : LiveCapsResolveC K hc) : Prop :=
  ∀ (k : Nat) (hk : k ≤ Γ.length) (A' : VTy Eff Mult), LiveCapsResolveC K (hc.weaken k hk A')

/-- Transport a value carrier along a grade equality (the leaf-arm cast: a `zeros`/`basis` grade weakened
to `insG …` is provably-but-not-defeq equal, so the constructor carrier must be re-graded). -/
theorem liveCapsResolveV_cast {K : EvalCtx} {γ γ' : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val}
    {A : VTy Eff Mult} (hg : γ = γ') {hv : HasVTy γ Γ v A} (h : LiveCapsResolveV K hv) :
    LiveCapsResolveV K (hg ▸ hv) := by subst hg; exact h

theorem liveCapsResolveC_cast {K : EvalCtx} {γ γ' : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp}
    {e : Eff} {B : CTy Eff Mult} (hg : γ = γ') {hc : HasCTy γ Γ c e B} (h : LiveCapsResolveC K hc) :
    LiveCapsResolveC K (hg ▸ hc) := by subst hg; exact h

/-- Transport a value carrier along a TERM equality (for the `handleState` closed-state re-typing:
`shiftFrom k s₀ = s₀`). -/
theorem liveCapsResolveV_termCast {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v v' : Val}
    {A : VTy Eff Mult} (hv : v = v') {hw : HasVTy γ Γ v A} (h : LiveCapsResolveV K hw) :
    LiveCapsResolveV K (hv ▸ hw) := by subst hv; exact h

/-! Leaf inversions for the WEAKEN-OUTPUT term `Val.shiftFrom k (inert value)`: ANY typing of an inert
value carries (the carrier follows the term, not the grade — so `γ` is FREE and `cases` assigns the stuck
`insG`-grade). `revert hw; simp` dodges the dependent-motive trap (`hw` is a goal index); for `vvar` the
shifted term is a stuck `if`, so `split` first. The `vcap` resolution is supplied by the source carrier
(caps are closed: weaken leaves `n`/`ℓ` untouched). -/
theorem liveCapsResolveV_weaken_vunit {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {A : VTy Eff Mult} (k : Nat) (hw : HasVTy γ Γ (Val.shiftFrom k Val.vunit) A) :
    LiveCapsResolveV K hw := by
  revert hw; simp only [Val.shiftFrom]; intro hw; cases hw; exact .vunit
theorem liveCapsResolveV_weaken_vint {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {n : Int}
    {A : VTy Eff Mult} (k : Nat) (hw : HasVTy γ Γ (Val.shiftFrom k (Val.vint n)) A) :
    LiveCapsResolveV K hw := by
  revert hw; simp only [Val.shiftFrom]; intro hw; cases hw; exact .vint
theorem liveCapsResolveV_weaken_vcap {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {n : Nat}
    {ℓ : Label} {A : VTy Eff Mult} (k : Nat) (hr : ResolvesLabel K n ℓ)
    (hw : HasVTy γ Γ (Val.shiftFrom k (Val.vcap n ℓ)) A) : LiveCapsResolveV K hw := by
  revert hw; simp only [Val.shiftFrom]; intro hw; cases hw; exact .vcap hr
theorem liveCapsResolveV_weaken_vvar {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {i : Nat}
    {A : VTy Eff Mult} (k : Nat) (hw : HasVTy γ Γ (Val.shiftFrom k (Val.vvar i)) A) :
    LiveCapsResolveV K hw := by
  revert hw; simp only [Val.shiftFrom]; split <;>
    (intro hw; cases hw with | vvar hmem => exact LiveCapsResolveV.vvar (h := hmem))

/-- `insG (zeros |Γ|) k = zeros |insT Γ k A'|` — inserting a 0 keeps an all-zeros grade all-zeros at the
longer length (mirrors `HasVTy.weaken`'s `vunit`/`vcap` arithmetic). -/
theorem insG_zeros_eq (Γ : TyCtx Eff Mult) (k : Nat) (A' : VTy Eff Mult) (hk : k ≤ Γ.length) :
    insG (GradeVec.zeros Γ.length : GradeVec Mult) k
      = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult) := by
  apply List.ext_getElem?
  intro j
  show ((GradeVec.zeros Γ.length).take k ++ (0:Mult) :: (GradeVec.zeros Γ.length).drop k)[j]?
    = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult)[j]?
  rw [GradeVec.insert_get _ _ _ _ (by rw [GradeVec.zeros_length]; omega), GradeVec.zeros_get]
  simp only [GradeVec.zeros_get]
  have hl : (insT Γ k A').length = Γ.length + 1 := by
    simp only [insT, List.length_append, List.length_cons, List.length_take, List.length_drop]; omega
  rw [hl]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem liveCapsResolveV_weaken {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} {hv : HasVTy γ Γ v A} (hvres : LiveCapsResolveV K hv)
    (k : Nat) (hk : k ≤ Γ.length) (A' : VTy Eff Mult) :
    LiveCapsResolveV K (hv.weaken k hk A') := by
  refine LiveCapsResolveV.rec (motive_1 := VweakenMotive K) (motive_2 := CweakenMotive K)
    ?vunit ?vint ?vvar ?vcap ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState
    ?handleTransaction hvres k hk A'
  -- ── VALUE arms ──
  case vunit =>
    intro Γ k hk A'
    exact liveCapsResolveV_weaken_vunit k ((HasVTy.vunit (Γ := Γ)).weaken k hk A')
  case vint =>
    intro Γ n k hk A'
    exact liveCapsResolveV_weaken_vint k ((HasVTy.vint (Γ := Γ) (n := n)).weaken k hk A')
  case vvar =>
    intro Γ i A hget k hk A'
    exact liveCapsResolveV_weaken_vvar k ((HasVTy.vvar hget).weaken k hk A')
  case vcap =>
    intro Γ n ℓ hr k hk A'
    exact liveCapsResolveV_weaken_vcap k hr ((HasVTy.vcap (Γ := Γ) (n := n) (ℓ := ℓ)).weaken k hk A')
  case vthunk => intro γ Γ M φ B dM h ih k hk A'; exact .vthunk (ih k hk A')
  case inl => intro γ Γ w A B dw h ih k hk A'; exact .inl (ih k hk A')
  case inr => intro γ Γ w A B dw h ih k hk A'; exact .inr (ih k hk A')
  case pair =>
    intro γ γv γw Γ w₁ w₂ A B dw₁ dw₂ hγ h1 h2 ih1 ih2 k hk A'
    subst hγ
    exact .pair (hγ := insG_add γv γw k (by rw [dw₁.length_eq, dw₂.length_eq])) (ih1 k hk A') (ih2 k hk A')
  case fold => intro γ Γ w A dw h ih k hk A'; exact .fold (ih k hk A')
  -- ── COMP arms ──
  case ret =>
    intro γ γ' Γ w A q dw hγ h ih k hk A'
    subst hγ
    exact .ret (hγ := insG_smul q γ' k) (fun hq => ih hq k hk A')
  case letC =>
    intro γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B dM dN hγ h1 h2 ih1 ih2 k hk A'
    subst hγ
    exact .letC (hγ := insG_add_smul_aux (q_or_1 q2) γ₁ γ₂ k
        (by have h1 := dM.length_eq; have h2 := dN.length_eq; simp at h2; omega))
      (ih1 k hk A') (ih2 (k + 1) (Nat.succ_le_succ hk) A')
  case force => intro γ Γ w φ B dw h ih k hk A'; exact .force (ih k hk A')
  case lam => intro γ Γ M φ q A B dM h ih k hk A'; exact .lam (ih (k + 1) (Nat.succ_le_succ hk) A')
  case app =>
    intro γ γ₁ γ₂ Γ M w φ q A B dM dw hγ h1 h2 ih1 ih2 k hk A'
    subst hγ
    exact .app (hγ := insG_add_smul_aux' q γ₁ γ₂ k (by rw [dM.length_eq, dw.length_eq]))
      (ih1 k hk A') (fun hq => ih2 hq k hk A')
  case case =>
    intro γ γv γN Γ w N₁ N₂ φ q A B C dw dN₁ dN₂ hγ h1 h2 h3 ih1 ih2 ih3 k hk A'
    subst hγ
    exact .case (hγ := insG_add_smul_aux q γv γN k (by rw [dw.length_eq]; have := dN₁.length_eq; simp at this ⊢; omega))
      (fun hq => ih1 hq k hk A') (ih2 (k + 1) (Nat.succ_le_succ hk) A') (ih3 (k + 1) (Nat.succ_le_succ hk) A')
  case split =>
    intro γ γv γN Γ w N φ q A B C dw dN hγ h1 h2 ih1 ih2 k hk A'
    subst hγ
    exact .split (hγ := insG_add_smul_aux q γv γN k (by rw [dw.length_eq]; have := dN.length_eq; simp at this ⊢; omega))
      (fun hq => ih1 hq k hk A') (ih2 (k + 2) (Nat.succ_le_succ (Nat.succ_le_succ hk)) A')
  case unfold => intro γ Γ w A dw h ih k hk A'; exact .unfold (ih k hk A')
  case perform =>
    intro q γc γv Γ cv ℓ op w φ A B _q2 dc hle hopA hopR dw h ih k hk A'
    convert LiveCapsResolveC.perform (q := q) (dc.weaken k hk A') (hle := hle) (hopA := hopA)
      (hopR := hopR) (dw.weaken k hk A') (ih k hk A') using 2
    exact insG_add_smul_aux q γv γc k (by rw [dw.length_eq, dc.length_eq])
  case handleThrows =>
    intro γ Γ ℓ M e φ q qc A hopA hint dM hle hbo h ih k hk A'
    exact .handleThrows (hopA := hopA) (hint := hint) (hle := hle) (hbo := hbo)
      (ih (k + 1) (Nat.succ_le_succ hk) A')
  case handleState =>
    intro γ Γ ℓ s₀ M e φ q qc S A hga hgr hpa hpr hint dsv dM hle hbo hs h ihs ih k hk A'
    -- the weaken output stores `shiftFrom k s₀` (= s₀ by closedness, ADR-0025); retype the closed state
    -- there so the constructed carrier's term matches the goal's `Comp.shiftFrom k (handle …)` defeq.
    have hsc : Val.shiftFrom k s₀ = s₀ := dsv.shift_closed k (Nat.zero_le k)
    exact LiveCapsResolveC.handleState (dsv := hsc.symm ▸ dsv) (hga := hga) (hgr := hgr) (hpa := hpa)
      (hpr := hpr) (hint := hint) (hle := hle) (hbo := hbo) (liveCapsResolveV_termCast hsc.symm hs)
      (ih (k + 1) (Nat.succ_le_succ hk) A')
  case handleTransaction =>
    intro γ Γ ℓ Θ₀ M e φ q qc A hna hnr hra hrr hwa hwr hint hcells dM hle hbo h ih k hk A'
    exact .handleTransaction (hna := hna) (hnr := hnr) (hra := hra) (hrr := hrr) (hwa := hwa)
      (hwr := hwr) (hint := hint) (hcells := hcells) (hle := hle) (hbo := hbo)
      (ih (k + 1) (Nat.succ_le_succ hk) A')

/-- Inversion: the only carrier over a `vthunk`-typing is `.vthunk`. Stated with `γ` FREE so dependent
elimination can refute the other constructors (a stuck `insG`-grade index blocks `cases` otherwise). -/
theorem liveCapsResolveV_vthunk_inv {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {M : Comp} {φ : Eff} {B : CTy Eff Mult} {dM : HasCTy γ Γ M φ B}
    (h : LiveCapsResolveV K (HasVTy.vthunk dM)) : LiveCapsResolveC K dM := by
  cases h with
  | vthunk hc => exact hc

/-- Term-level vthunk inversion (`γ` free, so `cases` assigns the grade): any value carrier over a
`vthunk c` typing yields a comp carrier over the body. Lets the comp-subst twin ride the value twin. -/
theorem liveCapsResolveV_vthunk_termInv {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {φ : Eff} {B : CTy Eff Mult} (hw : HasVTy γ Γ (Val.vthunk c) (VTy.U φ B))
    (h : LiveCapsResolveV K hw) : ∃ dc : HasCTy γ Γ c φ B, LiveCapsResolveC K dc := by
  cases hw with
  | vthunk dc => exact ⟨dc, liveCapsResolveV_vthunk_inv h⟩

theorem liveCapsResolveC_weaken {K : EvalCtx} {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} {hc : HasCTy γ Γ c e B} (hcres : LiveCapsResolveC K hc)
    (k : Nat) (hk : k ≤ Γ.length) (A' : VTy Eff Mult) :
    LiveCapsResolveC K (hc.weaken k hk A') := by
  -- Derive from the value lemma via a thunk-wrap: `vthunk c` is grade-transparent, so
  -- `(HasVTy.vthunk hc).weaken = HasVTy.vthunk (hc.weaken)` (proof-irrelevant), then invert `.vthunk`.
  have h := liveCapsResolveV_weaken (LiveCapsResolveV.vthunk hcres) k hk A'
  have heq : (HasVTy.vthunk hc).weaken k hk A' = HasVTy.vthunk (hc.weaken k hk A') :=
    Subsingleton.elim _ _
  exact liveCapsResolveV_vthunk_inv (heq ▸ h)

/-! ### §3.7 — CARRIER SUBSTITUTION (ADR-0061, #51 PIECE 2 PHASE A — the SHARED #4+#5 core).

The carrier mirror of `HasCTy.subst_gen` (`Bang/Metatheory.lean`): substituting a value `v` (carrier-clean
in `K`) at de Bruijn level `|Δ|` into a carrier-clean term re-produces a carrier over the substituted
typing. This is the term-liveness object the lead's steer fixes the proof axis to — it NEVER touches
`labelOccurs` of any intermediate type; the dormant-thunk-cap case (`U {ℓ} Int`) is handled FOR FREE
because the substituted var is a `vvar` (no carrier obligation) until it materializes.

THE GRADE GATE (the #5 "dead positions discard `v`"): `v`'s carrier is required ONLY when the substituted
slot is grade-LIVE (`slotGrade γ_full |Δ| ≠ 0`). At a DEAD slot the var occurs only behind dormant gates
(`ret`/`app`/`case`/`split` at `q = 0`), so `v`'s caps are never demanded — the dormant builder discharges
them with NO `v`-clean hypothesis. The VALUE layer takes `v`-clean unconditionally (its caller, the comp
layer, only descends into a value position when that position is gate-LIVE).

CONSUMER (PHASE B, NOT here): REDUCE arm of `lwsg_step_nonperform` (β/let-reduction substitutes the redex
value at the top binder — `Δ = []`, `slotGrade = ρ`, the binder grade); and the `letC`/`app`/`case`/`split`
walls of `lwscg_returnEscape` (the closed let-head `M`'s value flows to `N`'s var-0 — same subst).

Existential output: the post-step focus typing in `lwsg_step_nonperform` is itself `∃ d'`, so producing a
FRESH derivation `d'` of the substituted term (grade = `Sgrade`, matching `subst_value_proof`) + its carrier
is exactly the consumer-facing shape; it avoids indexing the carrier over `subst_gen`'s opaque output. -/
-- The shared `v`-side hypotheses for the mutual carrier-subst (mirrors `lwsvg_subst_gen`'s `v`-bundle):
-- `v` typed `γ_v` over the post-erase context, CLOSED (`hcl`, for the shift-collapse under binders),
-- and carrier-CLEAN in `K`. The clean witness is the TYPING-INDEXED `LiveCapsResolveV K hv` (single,
-- coherent) — NOT the `∀ γ' b'` LWSVg regrade (`lwsvg_closed_regrade_refute`-flavoured, FALSE). That is
-- the payoff of the carrier switch: at the VALUE layer the carrier is grade-independent, so `v`'s caps
-- resolving in `K` transfers to every Sgrade-position without re-grading.

/-! ### §3.7a — the RECURSOR motives for the carrier-subst (ADR-0061, #51 PHASE A).

The carrier `LiveCapsResolveV K hw` is indexed by a PROOF (the typing `hw`), so a `cases hwres` + manual
recursive call cannot compile (the structural-recursion compiler can't extract the sub-derivation as the
recursive index — build-confirmed). The fix mirrors `HasCTy.subst_gen`: recurse via the explicit mutual
recursor with these motives carrying the `v`-bundle + `hcov`/gate + the ∃-output (the carrier analogue of
`VsubstMotive`/`CsubstMotive`). The context `Γ'` is split as `Δ ++ A :: Γ` by the threaded hypothesis. -/
def VcarrierSubstMotive (K : EvalCtx) {γ₀ : GradeVec Mult} {Γ' : TyCtx Eff Mult} {w : Val}
    {A₀ : VTy Eff Mult} (hw : HasVTy γ₀ Γ' w A₀) (_ : LiveCapsResolveV K hw) : Prop :=
  ∀ (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A), ZeroSumFree Mult → (∀ j, Val.shiftFrom j v = v) →
    Γ' = Δ ++ A :: Γ → (γ₀.eraseIdx Δ.length).length ≤ γ_v.length →
    (slotGrade γ₀ Δ.length ≠ 0 → LiveCapsResolveV K hv) →
    ∃ d' : HasVTy (Sgrade γ_v Δ.length γ₀) (Δ ++ Γ) (Val.substFrom Δ.length v w) A₀,
      LiveCapsResolveV K d'

def CcarrierSubstMotive (K : EvalCtx) {γ₀ : GradeVec Mult} {Γ' : TyCtx Eff Mult} {c : Comp}
    {e : Eff} {B : CTy Eff Mult} (hc : HasCTy γ₀ Γ' c e B) (_ : LiveCapsResolveC K hc) : Prop :=
  ∀ (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A), ZeroSumFree Mult → (∀ j, Val.shiftFrom j v = v) →
    Γ' = Δ ++ A :: Γ → (γ₀.eraseIdx Δ.length).length ≤ γ_v.length →
    (slotGrade γ₀ Δ.length ≠ 0 → LiveCapsResolveV K hv) →
    ∃ d' : HasCTy (Sgrade γ_v Δ.length γ₀) (Δ ++ Γ) (Comp.substFrom Δ.length v c) e B,
      LiveCapsResolveC K d'

/-- `slotGrade (q :: γ) (k+1) = slotGrade γ k` — the binder shifts the read index past the consed slot. -/
theorem slotGrade_cons (q : Mult) (γ : GradeVec Mult) (k : Nat) :
    slotGrade (q :: γ) (k + 1) = slotGrade γ k := by
  unfold slotGrade; rw [List.getElem?_cons_succ]

mutual
/-- VALUE carrier-subst (the `v`-clean witness is consumed unconditionally — the comp layer descends here
only at grade-LIVE value positions, supplying it from its own gate). -/
theorem liveCapsResolveV_subst_gen (hzsf : ZeroSumFree Mult) {Γ : TyCtx Eff Mult}
    (Δ : TyCtx Eff Mult) {γ_v : GradeVec Mult} {v : Val} {A : VTy Eff Mult} {K : EvalCtx}
    {hv : HasVTy γ_v (Δ ++ Γ) v A}
    (hcl : ∀ j, Val.shiftFrom j v = v)
    {γ_w : GradeVec Mult} {w : Val} {A_w : VTy Eff Mult}
    {hw : HasVTy γ_w (Δ ++ A :: Γ) w A_w}
    (hcov : (γ_w.eraseIdx Δ.length).length ≤ γ_v.length)
    (hvgate : slotGrade γ_w Δ.length ≠ 0 → LiveCapsResolveV K hv) (hwres : LiveCapsResolveV K hw) :
    ∃ d' : HasVTy (Sgrade γ_v Δ.length γ_w) (Δ ++ Γ) (Val.substFrom Δ.length v w) A_w,
      LiveCapsResolveV K d' := by
  -- Recurse via the explicit mutual carrier recursor with the §3.7a motives (the `subst_gen` shape;
  -- `cases hwres`+manual recursion is build-confirmed impossible for the Prop-indexed carrier).
  refine LiveCapsResolveV.rec (motive_1 := VcarrierSubstMotive K) (motive_2 := CcarrierSubstMotive K)
    ?vunit ?vint ?vvar ?vcap ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState ?handleTransaction
    hwres Δ Γ A γ_v v hv hzsf hcl rfl hcov hvgate
  case vunit =>
    intro Γ_w Δ' Γ' A' γ_v' v' hv' _ _ heq hcov' _
    subst heq
    have hk : Δ'.length < (Δ' ++ A' :: Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    have hlen : γ_v'.length = (Δ' ++ A' :: Γ').length - 1 := by
      rw [hv'.length_eq]; simp only [List.length_append, List.length_cons]; omega
    have hcnt : (Δ' ++ A' :: Γ').length - 1 = (Δ' ++ Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    rw [Val.substFrom, Sgrade_zeros γ_v' Δ'.length _ hk hlen, hcnt]
    exact ⟨HasVTy.vunit, .vunit⟩
  case vint =>
    intro Γ_w n Δ' Γ' A' γ_v' v' hv' _ _ heq hcov' _
    subst heq
    have hk : Δ'.length < (Δ' ++ A' :: Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    have hlen : γ_v'.length = (Δ' ++ A' :: Γ').length - 1 := by
      rw [hv'.length_eq]; simp only [List.length_append, List.length_cons]; omega
    have hcnt : (Δ' ++ A' :: Γ').length - 1 = (Δ' ++ Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    rw [Val.substFrom, Sgrade_zeros γ_v' Δ'.length _ hk hlen, hcnt]
    exact ⟨HasVTy.vint, .vint⟩
  case vcap =>
    intro Γ_w n ℓ hr Δ' Γ' A' γ_v' v' hv' _ _ heq hcov' _
    subst heq
    have hk : Δ'.length < (Δ' ++ A' :: Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    have hlen : γ_v'.length = (Δ' ++ A' :: Γ').length - 1 := by
      rw [hv'.length_eq]; simp only [List.length_append, List.length_cons]; omega
    have hcnt : (Δ' ++ A' :: Γ').length - 1 = (Δ' ++ Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    rw [Val.substFrom, Sgrade_zeros γ_v' Δ'.length _ hk hlen, hcnt]
    exact ⟨HasVTy.vcap, .vcap hr⟩
  case inl =>
    intro γ Γ_i v_i A_i B_i dv h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    obtain ⟨dv', hdv'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    rw [Val.substFrom]
    exact ⟨HasVTy.inl dv', .inl hdv'⟩
  case inr =>
    intro γ Γ_i v_i A_i B_i dv h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    obtain ⟨dv', hdv'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    rw [Val.substFrom]
    exact ⟨HasVTy.inr dv', .inr hdv'⟩
  case fold =>
    intro γ Γ_i v_i A_i dv h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    obtain ⟨dv', hdv'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    rw [Val.substFrom]
    exact ⟨HasVTy.fold dv', .fold hdv'⟩
  case vthunk =>
    -- V→C crossing: the IH is the COMP motive (same grade γ₀), pass the gate straight through.
    intro γ Γ_i M φ B dM h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    obtain ⟨dM', hdM'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    rw [Val.substFrom]
    exact ⟨HasVTy.vthunk dM', .vthunk hdM'⟩
  case pair =>
    intro γ γv γw Γ_i v_i w_i A_i B_i dv dw hγ h1 h2 ih1 ih2
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst hγ
    have hlen : γv.length = γw.length := by rw [dv.length_eq, dw.length_eq]
    -- build each sub-gate from the parent: slotGrade γv ≠ 0 ⟹ slotGrade (γv+γw) ≠ 0 (slotGrade_add + hzsf).
    have hlcov_v : Δ'.length < γv.length := by
      rw [dv.length_eq, heq, List.length_append, List.length_cons]; omega
    have hlcov_w : Δ'.length < γw.length := by
      rw [dw.length_eq, heq, List.length_append, List.length_cons]; omega
    obtain ⟨dv', hdv'⟩ := ih1 Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq (cov_add_left hlen hcov')
      (fun hsv => hgate' (show slotGrade (GradeVec.add γv γw) Δ'.length ≠ 0 by
        rw [slotGrade_add _ _ _ hlcov_v hlcov_w]; intro hsum; exact hsv (hzsf' _ _ hsum).1))
    obtain ⟨dw', hdw'⟩ := ih2 Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq (cov_add_right hlen hcov')
      (fun hsw => hgate' (show slotGrade (GradeVec.add γv γw) Δ'.length ≠ 0 by
        rw [slotGrade_add _ _ _ hlcov_v hlcov_w]; intro hsum; exact hsw (hzsf' _ _ hsum).2))
    rw [Val.substFrom]
    exact ⟨HasVTy.pair dv' dw' (Sgrade_add_free γ_v' Δ'.length hlen),
      .pair (hγ := Sgrade_add_free γ_v' Δ'.length hlen) hdv' hdw'⟩
  case vvar =>
    -- the substituted-slot split (mirrors `subst_vvar_case`): i<k survives (vvar i, `.vvar`),
    -- i=k is the slot (term = v, grade γ_v, carrier = hvres'), i>k renumbers down (vvar (i-1), `.vvar`).
    intro Γ_w i A₀ hmem Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst heq
    have hkn : Δ'.length < (Δ' ++ A' :: Γ').length := by
      simp only [List.length_append, List.length_cons]; omega
    have hn : (Δ' ++ A' :: Γ').length = (Δ' ++ Γ').length + 1 := by
      simp only [List.length_append, List.length_cons]; omega
    have hlen_v : γ_v'.length = (Δ' ++ Γ').length := hv'.length_eq
    have h0smul : GradeVec.smul (0 : Mult) γ_v' = GradeVec.zeros (Δ' ++ Γ').length := by
      apply List.ext_getElem?; intro j
      rw [GradeVec.smul, List.getElem?_map, GradeVec.zeros_get]
      rcases hj : γ_v'[j]? with _ | a
      · simp only [Option.map_none]; rw [List.getElem?_eq_none_iff] at hj
        rw [if_neg (by rw [hv'.length_eq] at hj; omega)]
      · simp only [Option.map_some]
        have : j < γ_v'.length := by rw [List.getElem?_eq_some_iff] at hj; exact hj.1
        rw [if_pos (by rw [hv'.length_eq] at this; omega), zero_mul]
    rw [Val.substFrom]
    rcases Nat.lt_trichotomy i Δ'.length with hlt | heq2 | hgt
    · rw [if_neg (by omega), if_neg (by omega)]
      have hslot : slotGrade (GradeVec.basis (Δ' ++ A' :: Γ').length i : GradeVec Mult) Δ'.length = 0 := by
        unfold slotGrade; rw [GradeVec.basis_get, if_pos hkn, if_neg (by omega : Δ'.length ≠ i)]; rfl
      have hSg : Sgrade γ_v' Δ'.length (GradeVec.basis (Δ' ++ A' :: Γ').length i)
          = GradeVec.basis (Δ' ++ Γ').length i := by
        unfold Sgrade
        rw [hslot, h0smul, GradeVec.basis_eraseIdx _ _ _ hkn (by omega), hn, if_pos hlt]
        simp only [Nat.add_sub_cancel]
        apply List.ext_getElem?; intro j
        simp only [GradeVec.add, List.getElem?_zipWith, GradeVec.basis_get, GradeVec.zeros_get]
        split_ifs <;> simp [add_zero]
      rw [hSg]
      have hmem' : (Δ' ++ Γ')[i]? = some A₀ := by
        rw [List.getElem?_append_left (by omega)] at hmem ⊢; exact hmem
      exact ⟨HasVTy.vvar hmem', .vvar (h := hmem')⟩
    · subst heq2; rw [if_pos rfl]
      have hAA : A₀ = A' := by
        rw [List.getElem?_append_right (by omega), Nat.sub_self] at hmem; simpa using hmem.symm
      subst hAA
      have hslot : slotGrade (GradeVec.basis (Δ' ++ A₀ :: Γ').length Δ'.length : GradeVec Mult) Δ'.length = 1 := by
        unfold slotGrade; rw [GradeVec.basis_get, if_pos hkn]; simp
      have herase : (GradeVec.basis (Δ' ++ A₀ :: Γ').length Δ'.length : GradeVec Mult).eraseIdx Δ'.length
          = GradeVec.zeros (Δ' ++ Γ').length := by
        apply List.ext_getElem?; intro j
        rw [List.getElem?_eraseIdx, GradeVec.zeros_get]
        by_cases hji : j < Δ'.length <;>
          simp only [hji, if_true, if_false, GradeVec.basis_get]
        · split_ifs <;> first | rfl | (exfalso; omega)
        · split_ifs <;> first | rfl | (exfalso; omega)
      have h1smul : GradeVec.smul (1 : Mult) γ_v' = γ_v' := by rw [GradeVec.smul]; simp
      have hSg : Sgrade γ_v' Δ'.length (GradeVec.basis (Δ' ++ A₀ :: Γ').length Δ'.length) = γ_v' := by
        unfold Sgrade
        rw [hslot, herase, h1smul, show (Δ' ++ Γ').length = γ_v'.length from hlen_v.symm]
        exact GradeVec.zeros_add γ_v'
      rw [hSg]
      -- the slot's grade is `basis k`, slotGrade = 1 ≠ 0, so the gate fires and hands back v's carrier.
      exact ⟨hv', hgate' (by rw [hslot]; exact one_ne_zero)⟩
    · rw [if_neg (by omega), if_pos hgt]
      have hslot : slotGrade (GradeVec.basis (Δ' ++ A' :: Γ').length i : GradeVec Mult) Δ'.length = 0 := by
        unfold slotGrade; rw [GradeVec.basis_get, if_pos hkn, if_neg (by omega : Δ'.length ≠ i)]; rfl
      have hSg : Sgrade γ_v' Δ'.length (GradeVec.basis (Δ' ++ A' :: Γ').length i)
          = GradeVec.basis (Δ' ++ Γ').length (i - 1) := by
        unfold Sgrade
        rw [hslot, h0smul, GradeVec.basis_eraseIdx _ _ _ hkn (by omega), hn, if_neg (by omega)]
        simp only [Nat.add_sub_cancel]
        apply List.ext_getElem?; intro j
        simp only [GradeVec.add, List.getElem?_zipWith, GradeVec.basis_get, GradeVec.zeros_get]
        split_ifs <;> simp [add_zero]
      rw [hSg]
      have hmem' : (Δ' ++ Γ')[i - 1]? = some A₀ := by
        rw [List.getElem?_append_right (by omega)] at hmem
        rw [List.getElem?_append_right (by omega)]
        rwa [show i - Δ'.length = (i - 1 - Δ'.length) + 1 by omega, List.getElem?_cons_succ] at hmem
      exact ⟨HasVTy.vvar hmem', .vvar (h := hmem')⟩
  -- ── COMP arms ──
  case force =>
    -- ungated value, grade passes through (force's γ₀ = the value's grade), so the comp gate is the
    -- value-IH gate verbatim. (The gated value motive makes this compose — the fix that unblocked comp.)
    intro γ Γ_i v_i φ B dv h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    obtain ⟨dv', hdv'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    rw [Comp.substFrom]
    exact ⟨HasCTy.force dv', .force hdv'⟩
  case unfold =>
    intro γ Γ_i v_i A_i dv h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    obtain ⟨dv', hdv'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    rw [Comp.substFrom]
    exact ⟨HasCTy.unfold dv', .unfold hdv'⟩
  case ret =>
    intro γ γ' Γ_i v_i A_i q dw hγ h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst hγ; subst heq
    rw [Comp.substFrom]
    refine ⟨HasCTy.ret (HasVTy.subst_gen Δ' hv' dw) (Sgrade_hsmul γ_v' Δ'.length q γ'),
      .ret (dv := HasVTy.subst_gen Δ' hv' dw) (hγ := Sgrade_hsmul γ_v' Δ'.length q γ') (fun hq => ?_)⟩
    obtain ⟨dw', hdw'⟩ := ih hq Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl (cov_smul hcov')
      (fun hs => hgate' (by
        rw [show (q • γ' : GradeVec Mult) = GradeVec.smul q γ' from rfl, slotGrade_smul]
        exact mul_ne_zero hq hs))
    exact hdw'
  case lam =>
    intro γ Γ_i M φ q A_lam B dM h ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst heq
    rw [Comp.substFrom]
    obtain ⟨dM', hdM'⟩ := ih (A_lam :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) A_lam) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons hcov')
      (fun hs => liveCapsResolveV_weaken
        (hgate' (by rw [List.length_cons, slotGrade_cons] at hs; exact hs)) 0 (Nat.zero_le _) A_lam)
    have hcons : Sgrade (0 :: γ_v') (A_lam :: Δ').length (q :: γ) = q :: Sgrade γ_v' Δ'.length γ := by
      simp only [List.length_cons]; exact Sgrade_cons γ_v' Δ'.length q γ
    exact ⟨HasCTy.lam (hcons ▸ dM'), .lam (liveCapsResolveC_cast hcons hdM')⟩
  case app =>
    intro γ γ₁ γ₂ Γ_i M w_i φ q A_i B_i dM dv hγ h1 h2 ih1 ih2
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst hγ; subst heq
    rw [Comp.substFrom]
    have hlen : γ₁.length = γ₂.length := by rw [dM.length_eq, dv.length_eq]
    have hlens : γ₁.length = (q • γ₂).length := by rw [smul_hlength]; exact hlen
    have hl1 : Δ'.length < γ₁.length := by
      rw [dM.length_eq, List.length_append, List.length_cons]; omega
    have hl2 : Δ'.length < (q • γ₂).length := by
      rw [smul_hlength, dv.length_eq, List.length_append, List.length_cons]; omega
    have hγ' : Sgrade γ_v' Δ'.length (γ₁ + q • γ₂)
        = Sgrade γ_v' Δ'.length γ₁ + q • Sgrade γ_v' Δ'.length γ₂ := by
      rw [Sgrade_hadd γ_v' Δ'.length hlens, Sgrade_hsmul]
    obtain ⟨dM', hdM'⟩ := ih1 Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl (cov_add_left hlens hcov')
      (fun hsg => hgate' (show slotGrade (GradeVec.add γ₁ (GradeVec.smul q γ₂)) Δ'.length ≠ 0 by
        rw [slotGrade_add γ₁ (GradeVec.smul q γ₂) Δ'.length hl1 hl2]; intro hsum; exact hsg (hzsf' _ _ hsum).1))
    refine ⟨HasCTy.app dM' (HasVTy.subst_gen Δ' hv' dv) hγ',
      .app (dv := HasVTy.subst_gen Δ' hv' dv) (hγ := hγ') hdM' (fun hq => ?_)⟩
    obtain ⟨dv', hdv'⟩ := ih2 hq Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl
      (cov_smul (cov_add_right hlens hcov'))
      (fun hsg => hgate' (show slotGrade (GradeVec.add γ₁ (GradeVec.smul q γ₂)) Δ'.length ≠ 0 by
        rw [slotGrade_add γ₁ (GradeVec.smul q γ₂) Δ'.length hl1 hl2, slotGrade_smul]
        intro hsum; exact hsg ((mul_eq_zero.mp (hzsf' _ _ hsum).2).resolve_left hq)))
    exact hdv'
  case letC =>
    intro γ γ₁ γ₂ Γ_i M N φ₁ φ₂ q1 q2 A_i B_i dM dN hγ h1 h2 ih1 ih2
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst hγ; subst heq
    rw [Comp.substFrom]
    have hlen : γ₁.length = γ₂.length := by
      have := dN.length_eq; simp only [List.length_cons] at this; rw [dM.length_eq]; omega
    have hlens : (q_or_1 q2 • γ₁).length = γ₂.length := by rw [smul_hlength]; exact hlen
    have hl1 : Δ'.length < (q_or_1 q2 • γ₁).length := by
      rw [smul_hlength, dM.length_eq, List.length_append, List.length_cons]; omega
    have hl2 : Δ'.length < γ₂.length := by
      rw [← hlen, dM.length_eq, List.length_append, List.length_cons]; omega
    have hγ' : Sgrade γ_v' Δ'.length (q_or_1 q2 • γ₁ + γ₂)
        = q_or_1 q2 • Sgrade γ_v' Δ'.length γ₁ + Sgrade γ_v' Δ'.length γ₂ := by
      rw [Sgrade_hadd γ_v' Δ'.length hlens, Sgrade_hsmul]
    obtain ⟨dM', hdM'⟩ := ih1 Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl
      (cov_smul (cov_add_left hlens hcov'))
      (fun hsg => hgate' (show slotGrade (GradeVec.add (GradeVec.smul (q_or_1 q2) γ₁) γ₂) Δ'.length ≠ 0 by
        rw [slotGrade_add (GradeVec.smul (q_or_1 q2) γ₁) γ₂ Δ'.length hl1 hl2, slotGrade_smul]
        intro hsum
        exact hsg ((mul_eq_zero.mp (hzsf' _ _ hsum).1).resolve_left (q_or_1_ne_zero q2))))
    obtain ⟨dN', hdN'⟩ := ih2 (A_i :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) A_i) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons (cov_add_right hlens hcov'))
      (fun hs => liveCapsResolveV_weaken (hgate' (show slotGrade (GradeVec.add (GradeVec.smul (q_or_1 q2) γ₁) γ₂) Δ'.length ≠ 0 by
        rw [List.length_cons, slotGrade_cons] at hs
        rw [slotGrade_add (GradeVec.smul (q_or_1 q2) γ₁) γ₂ Δ'.length hl1 hl2]; intro hsum; exact hs (hzsf' _ _ hsum).2))
        0 (Nat.zero_le _) A_i)
    have hcons : Sgrade (0 :: γ_v') (A_i :: Δ').length (q1 * q_or_1 q2 :: γ₂)
        = (q1 * q_or_1 q2) :: Sgrade γ_v' Δ'.length γ₂ := by
      simp only [List.length_cons]; exact Sgrade_cons γ_v' Δ'.length (q1 * q_or_1 q2) γ₂
    exact ⟨HasCTy.letC dM' (hcons ▸ dN') hγ',
      .letC (hγ := hγ') hdM' (liveCapsResolveC_cast hcons hdN')⟩
  case case =>
    intro γ γ_s γ_N Γ_i sc N₁ N₂ φ q A_i B_i C_i ds dN₁ dN₂ hγ h1 h2 h3 ihs ih1 ih2
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst hγ; subst heq
    rw [Comp.substFrom]
    have hlen : γ_s.length = γ_N.length := by
      have := dN₁.length_eq; simp only [List.length_cons] at this; rw [ds.length_eq]; omega
    have hlens : (q • γ_s).length = γ_N.length := by rw [smul_hlength]; exact hlen
    have hl1 : Δ'.length < (q • γ_s).length := by
      rw [smul_hlength, ds.length_eq, List.length_append, List.length_cons]; omega
    have hl2 : Δ'.length < γ_N.length := by
      rw [← hlen, ds.length_eq, List.length_append, List.length_cons]; omega
    have hγ' : Sgrade γ_v' Δ'.length (q • γ_s + γ_N)
        = q • Sgrade γ_v' Δ'.length γ_s + Sgrade γ_v' Δ'.length γ_N := by
      rw [Sgrade_hadd γ_v' Δ'.length hlens, Sgrade_hsmul]
    have hcons : ∀ (X : VTy Eff Mult),
        Sgrade (0 :: γ_v') (X :: Δ').length (q :: γ_N) = q :: Sgrade γ_v' Δ'.length γ_N := fun X => by
      simp only [List.length_cons]; exact Sgrade_cons γ_v' Δ'.length q γ_N
    have gate_N : ∀ {X : VTy Eff Mult},
        slotGrade (q :: γ_N) (X :: Δ').length ≠ 0 → LiveCapsResolveV K (hv'.weaken 0 (Nat.zero_le _) X) :=
      fun {X} hs => liveCapsResolveV_weaken (hgate' (show slotGrade (GradeVec.add (GradeVec.smul q γ_s) γ_N) Δ'.length ≠ 0 by
        rw [List.length_cons, slotGrade_cons] at hs
        rw [slotGrade_add (GradeVec.smul q γ_s) γ_N Δ'.length hl1 hl2]; intro hsum; exact hs (hzsf' _ _ hsum).2))
        0 (Nat.zero_le _) X
    obtain ⟨dN₁', hdN₁'⟩ := ih1 (A_i :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) A_i) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons (cov_add_right hlens hcov')) gate_N
    obtain ⟨dN₂', hdN₂'⟩ := ih2 (B_i :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) B_i) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons (cov_add_right hlens hcov')) gate_N
    refine ⟨HasCTy.case (HasVTy.subst_gen Δ' hv' ds) (hcons A_i ▸ dN₁') (hcons B_i ▸ dN₂') hγ',
      .case (dv := HasVTy.subst_gen Δ' hv' ds) (dN1 := hcons A_i ▸ dN₁') (dN2 := hcons B_i ▸ dN₂')
        (hγ := hγ') (fun hq => ?_) (liveCapsResolveC_cast (hcons A_i) hdN₁')
        (liveCapsResolveC_cast (hcons B_i) hdN₂')⟩
    obtain ⟨ds', hds'⟩ := ihs hq Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl
      (cov_smul (cov_add_left hlens hcov'))
      (fun hsg => hgate' (show slotGrade (GradeVec.add (GradeVec.smul q γ_s) γ_N) Δ'.length ≠ 0 by
        rw [slotGrade_add (GradeVec.smul q γ_s) γ_N Δ'.length hl1 hl2, slotGrade_smul]
        intro hsum; exact hsg ((mul_eq_zero.mp (hzsf' _ _ hsum).1).resolve_left hq)))
    exact hds'
  case split =>
    intro γ γ_s γ_N Γ_i sc N φ q A_i B_i C_i ds dN hγ h1 h2 ihs ihN
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst hγ; subst heq
    rw [Comp.substFrom]
    have hlen : γ_s.length = γ_N.length := by
      have := dN.length_eq; simp only [List.length_cons] at this; rw [ds.length_eq]; omega
    have hlens : (q • γ_s).length = γ_N.length := by rw [smul_hlength]; exact hlen
    have hl1 : Δ'.length < (q • γ_s).length := by
      rw [smul_hlength, ds.length_eq, List.length_append, List.length_cons]; omega
    have hl2 : Δ'.length < γ_N.length := by
      rw [← hlen, ds.length_eq, List.length_append, List.length_cons]; omega
    have hγ' : Sgrade γ_v' Δ'.length (q • γ_s + γ_N)
        = q • Sgrade γ_v' Δ'.length γ_s + Sgrade γ_v' Δ'.length γ_N := by
      rw [Sgrade_hadd γ_v' Δ'.length hlens, Sgrade_hsmul]
    have hsh2 : Val.shift (Val.shift v') = v' := by
      simp only [Val.shift]; rw [hcl' 0]; exact hcl' 0
    obtain ⟨dN', hdN'⟩ := ihN (B_i :: A_i :: Δ') Γ' A' (0 :: 0 :: γ_v') (Val.shift (Val.shift v'))
      ((hv'.weaken 0 (Nat.zero_le _) A_i).weaken 0 (Nat.zero_le _) B_i) hzsf'
      (fun j => by rw [hsh2]; exact hcl' j) rfl
      (cov_cons (cov_cons (cov_add_right hlens hcov')))
      (fun hs => by
        rw [List.length_cons, List.length_cons, slotGrade_cons, slotGrade_cons] at hs
        exact liveCapsResolveV_weaken (liveCapsResolveV_weaken
          (hgate' (show slotGrade (GradeVec.add (GradeVec.smul q γ_s) γ_N) Δ'.length ≠ 0 by
            rw [slotGrade_add (GradeVec.smul q γ_s) γ_N Δ'.length hl1 hl2]; intro hsum; exact hs (hzsf' _ _ hsum).2))
          0 (Nat.zero_le _) A_i) 0 (Nat.zero_le _) B_i)
    have hcons : Sgrade (0 :: 0 :: γ_v') (B_i :: A_i :: Δ').length (q :: q :: γ_N)
        = q :: q :: Sgrade γ_v' Δ'.length γ_N := by
      simp only [List.length_cons]
      rw [show Δ'.length + 1 + 1 = (Δ'.length + 1) + 1 from rfl, Sgrade_cons, Sgrade_cons]
    refine ⟨HasCTy.split (HasVTy.subst_gen Δ' hv' ds) (hcons ▸ dN') hγ',
      .split (dv := HasVTy.subst_gen Δ' hv' ds) (dN := hcons ▸ dN') (hγ := hγ') (fun hq => ?_)
        (liveCapsResolveC_cast hcons hdN')⟩
    obtain ⟨ds', hds'⟩ := ihs hq Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl
      (cov_smul (cov_add_left hlens hcov'))
      (fun hsg => hgate' (show slotGrade (GradeVec.add (GradeVec.smul q γ_s) γ_N) Δ'.length ≠ 0 by
        rw [slotGrade_add (GradeVec.smul q γ_s) γ_N Δ'.length hl1 hl2, slotGrade_smul]
        intro hsum; exact hsg ((mul_eq_zero.mp (hzsf' _ _ hsum).1).resolve_left hq)))
    exact hds'
  case perform =>
    intro q γ_c γ_v Γ_i cp ℓ op w_i φ A_i B_i _q2 dc hle hopA hopR dvw h ih
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst heq
    rw [Comp.substFrom]
    have hlen : γ_v.length = γ_c.length := by rw [dvw.length_eq, dc.length_eq]
    have hlens : (q • γ_v).length = γ_c.length := by rw [smul_hlength]; exact hlen
    have hl1 : Δ'.length < (q • γ_v).length := by
      rw [smul_hlength, dvw.length_eq, List.length_append, List.length_cons]; omega
    have hl2 : Δ'.length < γ_c.length := by
      rw [dc.length_eq, List.length_append, List.length_cons]; omega
    obtain ⟨dc', hdc'⟩ := ih Δ' Γ' A' γ_v' v' hv' hzsf' hcl' rfl (cov_add_right hlens hcov')
      (fun hsg => hgate' (show slotGrade (GradeVec.add (GradeVec.smul q γ_v) γ_c) Δ'.length ≠ 0 by
        rw [slotGrade_add (GradeVec.smul q γ_v) γ_c Δ'.length hl1 hl2]; intro hsum; exact hsg (hzsf' _ _ hsum).2))
    have hγ' : Sgrade γ_v' Δ'.length (q • γ_v + γ_c)
        = q • Sgrade γ_v' Δ'.length γ_v + Sgrade γ_v' Δ'.length γ_c := by
      rw [Sgrade_hadd γ_v' Δ'.length hlens, Sgrade_hsmul]
    have key : LiveCapsResolveC K
        (HasCTy.perform (q := q) dc' hle hopA hopR (HasVTy.subst_gen Δ' hv' dvw)) :=
      .perform (q := q) dc' (hle := hle) (hopA := hopA) (hopR := hopR)
        (HasVTy.subst_gen Δ' hv' dvw) hdc'
    exact ⟨_, liveCapsResolveC_cast (K := K) hγ'.symm key⟩
  case handleThrows =>
    intro γ Γ_i ℓ M e φ q qc A_i hopA hint dM hle hbo h ih
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst heq
    rw [Comp.substFrom, Handler.substFrom]
    obtain ⟨dM', hdM'⟩ := ih (VTy.cap ℓ :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) (VTy.cap ℓ)) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons hcov')
      (fun hs => liveCapsResolveV_weaken
        (hgate' (by rw [List.length_cons, slotGrade_cons] at hs; exact hs)) 0 (Nat.zero_le _) (VTy.cap ℓ))
    have hcons : Sgrade (0 :: γ_v') (VTy.cap ℓ :: Δ').length (qc :: γ) = qc :: Sgrade γ_v' Δ'.length γ := by
      simp only [List.length_cons]; exact Sgrade_cons γ_v' Δ'.length qc γ
    exact ⟨HasCTy.handleThrows hopA hint (hcons ▸ dM') hle hbo,
      .handleThrows (hopA := hopA) (hint := hint) (hle := hle) (hbo := hbo)
        (liveCapsResolveC_cast hcons hdM')⟩
  case handleState =>
    intro γ Γ_i ℓ s₀ M e φ q qc S A_i hga hgr hpa hpr hint dsv dM hle hbo hs h ihs ih
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst heq
    rw [Comp.substFrom, Handler.substFrom]
    have hsc : Val.substFrom Δ'.length v' s₀ = s₀ := dsv.subst_closed Δ'.length (Nat.zero_le _) v'
    obtain ⟨dM', hdM'⟩ := ih (VTy.cap ℓ :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) (VTy.cap ℓ)) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons hcov')
      (fun hsl => liveCapsResolveV_weaken
        (hgate' (by rw [List.length_cons, slotGrade_cons] at hsl; exact hsl)) 0 (Nat.zero_le _) (VTy.cap ℓ))
    have hcons : Sgrade (0 :: γ_v') (VTy.cap ℓ :: Δ').length (qc :: γ) = qc :: Sgrade γ_v' Δ'.length γ := by
      simp only [List.length_cons]; exact Sgrade_cons γ_v' Δ'.length qc γ
    exact ⟨HasCTy.handleState hga hgr hpa hpr hint (hsc.symm ▸ dsv) (hcons ▸ dM') hle hbo,
      .handleState (dsv := hsc.symm ▸ dsv) (hga := hga) (hgr := hgr) (hpa := hpa) (hpr := hpr)
        (hint := hint) (hle := hle) (hbo := hbo) (liveCapsResolveV_termCast hsc.symm hs)
        (liveCapsResolveC_cast hcons hdM')⟩
  case handleTransaction =>
    intro γ Γ_i ℓ Θ₀ M e φ q qc A_i hna hnr hra hrr hwa hwr hint hcells dM hle hbo h ih
      Δ' Γ' A' γ_v' v' hv' hzsf' hcl' heq hcov' hgate'
    subst heq
    rw [Comp.substFrom, Handler.substFrom]
    obtain ⟨dM', hdM'⟩ := ih (VTy.cap ℓ :: Δ') Γ' A' (0 :: γ_v') (Val.shift v')
      (hv'.weaken 0 (Nat.zero_le _) (VTy.cap ℓ)) hzsf'
      (fun j => by rw [show Val.shift v' = v' from hcl' 0]; exact hcl' j) rfl (cov_cons hcov')
      (fun hsl => liveCapsResolveV_weaken
        (hgate' (by rw [List.length_cons, slotGrade_cons] at hsl; exact hsl)) 0 (Nat.zero_le _) (VTy.cap ℓ))
    have hcons : Sgrade (0 :: γ_v') (VTy.cap ℓ :: Δ').length (qc :: γ) = qc :: Sgrade γ_v' Δ'.length γ := by
      simp only [List.length_cons]; exact Sgrade_cons γ_v' Δ'.length qc γ
    exact ⟨HasCTy.handleTransaction hna hnr hra hrr hwa hwr hint hcells (hcons ▸ dM') hle hbo,
      .handleTransaction (hna := hna) (hnr := hnr) (hra := hra) (hrr := hrr) (hwa := hwa) (hwr := hwr)
        (hint := hint) (hcells := hcells) (hle := hle) (hbo := hbo) (liveCapsResolveC_cast hcons hdM')⟩
/-- COMP carrier-subst — the grade GATE: `v`-clean is demanded only when the substituted slot is
grade-LIVE (`slotGrade γ_full |Δ| ≠ 0`). `hzsf` makes `slotGrade = 0 ⟹ all occurrences dormant`, so a
DEAD slot discharges via the dormant builder with NO `v`-clean. -/
theorem liveCapsResolveC_subst_gen (hzsf : ZeroSumFree Mult) {Γ : TyCtx Eff Mult}
    (Δ : TyCtx Eff Mult) {γ_v : GradeVec Mult} {v : Val} {A : VTy Eff Mult} {K : EvalCtx}
    {hv : HasVTy γ_v (Δ ++ Γ) v A}
    (hcl : ∀ j, Val.shiftFrom j v = v)
    {γ_full : GradeVec Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    {hc : HasCTy γ_full (Δ ++ A :: Γ) c e B}
    (hcov : (γ_full.eraseIdx Δ.length).length ≤ γ_v.length)
    (hgate : slotGrade γ_full Δ.length ≠ 0 → LiveCapsResolveV K hv)
    (hcres : LiveCapsResolveC K hc) :
    ∃ d' : HasCTy (Sgrade γ_v Δ.length γ_full) (Δ ++ Γ) (Comp.substFrom Δ.length v c) e B,
      LiveCapsResolveC K d' := by
  -- WRITE-ONCE: the comp twin rides the value twin via a thunk-wrap. `vthunk c` is grade-transparent, so
  -- `Sgrade Δ γ_full` and the gate transfer verbatim; `substFrom (vthunk c) = vthunk (substFrom c)`; the
  -- resulting value carrier inverts (`vthunk_termInv`) to the comp carrier. The 21 recursor arms live
  -- ONCE, in `liveCapsResolveV_subst_gen`.
  obtain ⟨dth, hdth⟩ :=
    liveCapsResolveV_subst_gen hzsf Δ hcl hcov hgate (LiveCapsResolveV.vthunk hcres)
  exact liveCapsResolveV_vthunk_termInv dth hdth
end

/-! ### §3.7c — CARRIER RETURN-ESCAPE (ADR-0061, #51 PIECE 3 — the POP-focus block for `lwsg_step_nonperform`).

The ADR-0061 carrier analogue of `lwsvg_returnEscape`/`lwscg_returnEscape`: a focus carrier resolving in
`Frame.handleF g' hd :: K'` re-homes to `K'` (the popped stack) when no CARRIER-live cap references the
just-popped handler. At the value layer the B-occ `¬ labelOccurs ℓ A` precludes a label-`ℓ` cap in `v`
(the only caps that resolve to `g'`, since resolution is by identity and the typed cap's label must match
the frame's `ℓ`). At the comp layer the ROW `¬(ℓ ≤ φ)` (covers caps that are PERFORMED) + B-occ
`¬ labelOccurs ℓ C` (covers caps that ESCAPE in the result) jointly cover every carrier-live cap.

REFUTE-FIRST (SOUND — survived the discarded-cap refutation; the prior refutes in this area, e.g.
`lwsvg_closed_regrade_refute`, made caution mandatory). Naive worry: a held-but-discarded live
`vcap g' ℓ` (`letC (ret (vcap g' ℓ)) N`, `N` discards var 0) would be carrier-live yet not survive the
pop, and NEITHER `hrow` (the cap isn't performed) NOR `hres` (it's intermediate, not in the result)
precludes it — that would make this statement FALSE, exactly the wall `lwscg_returnEscape`'s comp binder
arms sorried on. RESOLVED by the GRADE-COUPLING: `N` discarding var 0 forces the binding grade
`q1 * q_or_1 q2 = 0`; with `q_or_1 q2 ≠ 0` (`q_or_1_ne_zero`) + `[NoZeroDivisors Mult]` this gives `q1 = 0`,
so the head `ret`'s carrier gate `q1 ≠ 0` is OFF — the cap is DORMANT, no carrier obligation (the same
coupling forces a discarding callee's arrow grade `q = 0` in `app`/`lam`). So every CARRIER-live cap is
genuinely used downstream ⟹ performed (`hrow`) or escaped (`hres`). This typed-liveness + grade-coupling
is exactly why the carrier closes the binder arms the typeless `LWSCg` flag-liveness could not.

PROOF (PENDING — the next bounded grind): recurse via `LiveCapsResolveV.rec` over the carrier (`K` is a
PARAMETER, not an index, so the pop is a clean structural recursion — unlike the subst). Value arms mirror
`lwsvg_returnEscape` (`vcap` via `resolvesLabel_pop`); comp non-binder arms (`ret`/`force`/`lam`/`perform`/
`unfold`) mirror `lwscg_returnEscape`'s proven arms; comp BINDER arms (`letC`/`app`/`case`/`split`/`handle`)
thread `hrow`/`hres` to the sub-terms, discharging dead positions via the grade-coupling above. -/
mutual
theorem liveCapsResolveV_returnEscape {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ : Label}
    (hℓ : Handler.label hd = ℓ) {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    {dv : HasVTy γ Γ v A} (hbo : ¬ VTy.labelOccurs ℓ A)
    (h : LiveCapsResolveV (Frame.handleF g' hd :: K') dv) : LiveCapsResolveV K' dv := by
  -- shape: mirror the proven typeless `lwsvg_returnEscape` (§2′.8g) over the CARRIER. `cases h`
  -- (the carrier is indexed by `dv`, so the value-typing structure is refined per arm). The `vcap`
  -- crux re-homes via `resolvesLabel_pop`, killing `n = g'` with `hbo` exactly as the template does.
  cases h with
  | vunit => exact .vunit
  | vint => exact .vint
  | @vvar Γ i A hmem => exact .vvar (h := hmem)
  | @vcap Γ n ℓ' hr =>
      refine .vcap (resolvesLabel_pop ?_ hr)
      intro hng; subst hng
      obtain ⟨Kᵢ, hh, Kₒ, hsplit, hlbl⟩ := hr
      rw [splitAtId, if_pos rfl] at hsplit
      simp only [Option.some.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨_, rfl, _⟩ := hsplit
      exact hbo (hℓ.symm.trans hlbl)
  | @vthunk γ Γ M φ B dM h =>
      exact .vthunk (liveCapsResolveC_returnEscape hℓ
        (fun hx => hbo (Or.inl hx)) (fun hx => hbo (Or.inr hx)) h)
  | @inl γ Γ v A B dv h =>
      exact .inl (liveCapsResolveV_returnEscape hℓ (fun hx => hbo (Or.inl hx)) h)
  | @inr γ Γ v A B dv h =>
      exact .inr (liveCapsResolveV_returnEscape hℓ (fun hx => hbo (Or.inr hx)) h)
  | @pair γ γv γw Γ v w A B dv dw hγ h1 h2 =>
      exact .pair (hγ := hγ)
        (liveCapsResolveV_returnEscape hℓ (fun hx => hbo (Or.inl hx)) h1)
        (liveCapsResolveV_returnEscape hℓ (fun hx => hbo (Or.inr hx)) h2)
  | @fold γ Γ v A dv h =>
      exact .fold (liveCapsResolveV_returnEscape hℓ (fun hx => hbo (labelOccurs_unrollMu ℓ A hx)) h)
theorem liveCapsResolveC_returnEscape {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ : Label}
    (hℓ : Handler.label hd = ℓ) {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {φ : Eff}
    {C : CTy Eff Mult} {dc : HasCTy γ Γ c φ C}
    (hrow : ¬ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ) (hres : ¬ CTy.labelOccurs ℓ C)
    (h : LiveCapsResolveC (Frame.handleF g' hd :: K') dc) : LiveCapsResolveC K' dc := by
  -- shape: mirror `lwscg_returnEscape`'s PROVEN arms over the carrier. Non-binder arms
  -- (ret/force/lam/perform/unfold) thread `hrow`/`hres` to the (gated) value sub-carrier exactly as
  -- the typeless template; binder arms (letC/app/case/split/handle*) are the grade-coupling grind.
  cases h with
  | @ret γ γ' Γ v A q dv hγ hgate =>
      exact .ret (hγ := hγ) (fun hq => liveCapsResolveV_returnEscape hℓ hres (hgate hq))
  | @force γ Γ v φ B dv h =>
      exact .force (liveCapsResolveV_returnEscape hℓ (fun hx => hx.elim hrow hres) h)
  | @lam γ Γ M φ q A B dM h =>
      exact .lam (liveCapsResolveC_returnEscape hℓ hrow (fun hx => hres (Or.inr hx)) h)
  | @perform _ γ_c γ_v Γ cv ℓ2 op v φ A B q dc hle hopA hopR dv h =>
      exact .perform (q := q) (hle := hle) (hopA := hopA) (hopR := hopR) dc dv
        (liveCapsResolveV_returnEscape hℓ
          (by intro hx; simp only [VTy.labelOccurs] at hx; subst hx; exact hrow hle) h)
  | @unfold γ Γ v A dv h =>
      -- ORTHOGONAL gap (NOT the containment wall): value v : mu A, result F 1 (unrollMu A). `hres`
      -- gives ¬labelOccurs ℓ (unrollMu A); the value escape needs ¬labelOccurs ℓ (mu A) = ¬labelOccurs
      -- ℓ A. Needs the REVERSE-μ monotonicity `labelOccurs ℓ A → labelOccurs ℓ (unrollMu A)` (the
      -- converse of `vty_labelOccurs_tySubstFrom`; TRUE — subst touches only tvars, leaves cap-labels).
      sorry
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B dM dN hγ h1 h2 =>
      -- N : φ₂, B — result B covered by `hres`; row φ₂ ≤ φ₁⊔φ₂ covered by `hrow` (CLEAN).
      -- M : φ₁, F q1 A — row φ₁ covered; but the let-INTERMEDIATE `A` is NOT covered by `hres`
      -- (which is over the result `B`). THE WALL: a carrier-LIVE cap (q1 ≠ 0) of label ℓ in M's
      -- return value sits in `A`, resolving to the popped `g'`. SOUND (it must propagate into N and
      -- be performed ⇒ ℓ≤φ₂ ⊆ ℓ≤φ₁⊔φ₂ ✗hrow, or escape ⇒ labelOccurs ℓ B ✗hres), but the proof
      -- needs the CAPABILITY-CONTAINMENT lemma: "var 0 : A graded-live in N : φ₂,B ⇒ ℓ≤φ₂ ∨
      -- labelOccurs ℓ B" — a new induction over `dN`, NOT supplied by the carrier. q1 = 0 ⇒ gate off
      -- (vacuous, this `hresM` unused); the live (q1≠0) case is the irreducible gap.
      exact .letC (hγ := hγ)
        (liveCapsResolveC_returnEscape hℓ (fun hx => hrow (le_trans hx le_sup_left))
          (by sorry /- hresM : ¬ VTy.labelOccurs ℓ A — capability containment over `dN` -/) h1)
        (liveCapsResolveC_returnEscape hℓ (fun hx => hrow (le_trans hx le_sup_right)) hres h2)
  -- CONTAINMENT WALL (same as `letC` above — see that arm's comment). The eliminators consume an
  -- INPUT type uncovered by the result-type `hres`: `app`'s domain `A` (gated by the arrow `q`),
  -- `case`/`split`'s scrutinee `sum/prod A B` (gated by `q`). A graded-live (q≠0) cap of label ℓ
  -- there resolves to the popped `g'`; SOUND only because an honest arrow/eliminator surfaces it in
  -- the row (✗hrow) or result (✗hres) — the CAPABILITY-CONTAINMENT lemma the carrier does not supply.
  -- (The branch/body sub-carriers — `app`/`case`/`split`'s comp positions — are CLEAN: same row+result.)
  | @app γ γ₁ γ₂ Γ M v φ q A B dM dv hγ h1 hgate => sorry
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C dv dN1 dN2 hγ hgate h2 h3 => sorry
  | @split γ γ_v γ_N Γ v N φ q A B C dv dN hγ hgate h2 => sorry
  -- ORTHOGONAL gap (NOT containment): a term-level `handle` discharges its OWN label ℓ_h; the body
  -- runs at row `e ≤ ℓ_h ⊔ φ`. Threading the local discharge (re-exposing the carried answer-type
  -- B-occ `hbo` + the row separation) is separate machinery — the typeless `lwscg_returnEscape`
  -- walled here too (3197-3199). The carried `hbo : ¬LabelOccurs ℓ_h A` gives the body's result B-occ.
  | @handleThrows γ Γ ℓ M e φ q qc A hopA hint dM hle hbo h => sorry
  | @handleState γ Γ ℓ s₀ M e φ q qc S A hga hgr hpa hpr hint dsv dM hle hbo hsr h => sorry
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q qc A hna hnr hra hrr hwa hwr hint hcells dM hle hbo h => sorry
end

/-- **GRADED liveness preservation — the NON-perform arms (Phase 2).** Given the pre-step graded invariant
+ typing + freshness, the post-step focus/stack stay graded-well-scoped. Discharged in Phase 2 by:
PUSH/MINT graded restack (mechanical mirror of the §3.5 typeless `lwsc_restack` family); REDUCE via
`lwsvg_closed_regrade` + `lwscg_subst` (live) / `lwscg_to_lwsck` + `lwsck_subst` (dead); POP via
`lwscg_returnEscape` (focus) + `lwskg_pop_fresh` (tail) + `handleF_bocc_inv`; force/unfold direct. -/
-- ADR-0061 (#51): the WELL-SCOPED preservation now produces the post-step `WScfg`-TAIL — a coherent
-- typing `d'` + `LiveCapsResolveC` over it + the stack typing + `LWSKg`. (The bundled typing replaces
-- the separate `hasConfigTy_step` call; the obligation's proof will route through it.) The keystone
-- (`LiveCapsResolveC` preserved by subst/pop) lives HERE.
theorem lwsg_step_nonperform {g : Nat} {K : EvalCtx} {c : Comp} {e : Eff} {C Co : CTy Eff Mult}
    {cfg' : Config}
    (hfocus : HasCTy (Eff := Eff) (Mult := Mult) [] [] c e C) (hstack : HasStack K e C ⊥ Co)
    (hres : LiveCapsResolveC K hfocus) (hresK : LiveCapsResolveK K hstack)
    (hfresh : FreshCfg (g, K, c))
    (hnp : ∀ n ℓ op v, c ≠ Comp.perform (Val.vcap n ℓ) op v)
    (hstep : Source.step (g, K, c) = some cfg') :
    ∃ (e' : Eff) (C' : CTy Eff Mult) (d' : HasCTy [] [] cfg'.2.2 e' C')
      (dk' : HasStack cfg'.2.1 e' C' ⊥ Co),
      LiveCapsResolveC cfg'.2.1 d' ∧ LiveCapsResolveK cfg'.2.1 dk' := by
  sorry

/-- **GRADED liveness preservation — the DISPATCH arm (#35).** `idDispatch` reinstalls/pops a handler on a
resume; the resumed focus + reassembled stack stay graded-well-scoped. Deferred to #35 (the abort/tail/
general resumption-multiplicity grading — the "sorryAx-on-DISPATCH-only" endpoint of `type_safety`). -/
theorem lwsg_step_dispatch {g : Nat} {K : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId} {v : Val}
    {e : Eff} {C Co : CTy Eff Mult} {cfg' : Config}
    (hfocus : HasCTy (Eff := Eff) (Mult := Mult) [] [] (Comp.perform (Val.vcap n ℓ) op v) e C)
    (hstack : HasStack K e C ⊥ Co)
    (hres : LiveCapsResolveC K hfocus)
    (hresK : LiveCapsResolveK K hstack)
    (hfresh : FreshCfg (g, K, Comp.perform (Val.vcap n ℓ) op v))
    (hstep : Source.step (g, K, Comp.perform (Val.vcap n ℓ) op v) = some cfg') :
    ∃ (e' : Eff) (C' : CTy Eff Mult) (d' : HasCTy [] [] cfg'.2.2 e' C')
      (dk' : HasStack cfg'.2.1 e' C' ⊥ Co),
      LiveCapsResolveC cfg'.2.1 d' ∧ LiveCapsResolveK cfg'.2.1 dk' := by
  sorry

theorem wsCfg_step {Co : CTy Eff Mult} (cfg cfg' : Config)
    (hP : WScfg Co cfg) (hstep : Source.step cfg = some cfg') : WScfg Co cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  obtain ⟨e, C, hfocus, hstack, hres, hresK, hfresh⟩ := hP
  -- FRESHNESS half (uniform, §3.0).
  have hFreshr : FreshCfg cfg' := freshCfg_step (g, K, c) cfg' hfresh hstep
  -- WELL-SCOPED + TYPING half: route DISPATCH (perform-vcap, #35) vs every other arm. Each obligation
  -- returns the post-step `WScfg`-tail (typing `d'` + `LiveCapsResolveC` over it + stack `dk'` +
  -- `LiveCapsResolveK` over it).
  by_cases hperf : ∃ n ℓ op v, c = Comp.perform (Val.vcap n ℓ) op v
  · obtain ⟨n, ℓ, op, v, rfl⟩ := hperf
    obtain ⟨e', C', d', dk', hres', hkg⟩ := lwsg_step_dispatch hfocus hstack hres hresK hfresh hstep
    exact ⟨e', C', d', dk', hres', hkg, hFreshr⟩
  · obtain ⟨e', C', d', dk', hres', hkg⟩ := lwsg_step_nonperform hfocus hstack hres hresK hfresh
      (fun n ℓ op v hc => hperf ⟨n, ℓ, op, v, hc⟩) hstep
    exact ⟨e', C', d', dk', hres', hkg, hFreshr⟩

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

/-- ★ **THE NON-ESCAPE DIAGONAL, ADR-0063** (inc-5 Phase 3 — the defined-escape reshape; SUPERSEDES the
`WScfg`-carrier `diagonal` above). Once the capability-escape is a DEFINED terminal (`.escapedCap`),
the focus obligation `FocusResolves'` (resolve OR defined-escape) is a TAUTOLOGY (`idDispatch = some ⟹
CapResolves`), so `NonEscape'` holds unconditionally. The diagonal `HasConfigTy ⟹ NonEscape'` is thus
DISCHARGED with NO `WScfg` carrier, NO `liveCapsResolveC_returnEscape` (build-REFUTED, `ReturnEscapeRefute`),
and NO `lwsg_step_dispatch` (#35) dependency — the whole POP-preservation machinery the build-refuted
returnEscape needed DISSOLVES. The safety content moves entirely to PROGRESS (typing: a well-typed `⊥`
program steps, terminates, or hits a defined capability-escape — never genuine `.stuck`); the Spec-level
`type_safety` re-proof over the new `Result.escapedCap` routing is the inc-6 task (`Spec → Compile →
CalcVM`, currently pre-red). The sealed witness (`ReturnEscapeReach.progComp`) is the DEFINED branch of
`FocusResolves'`, not a counterexample. -/
theorem diagonal' {c : Comp} {q : Mult} {A : VTy Eff Mult}
    (_hty : HasConfigTy (0, [], c) ⊥ (CTy.F q A)) (_hvf : VcapFree c) :
    NonEscape' (0, [], c) :=
  nonEscape'_all _

end -- public section
end Bang.Model
