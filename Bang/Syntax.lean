/-
  Bang/Syntax.lean — typing judgments + grade discipline + row well-formedness.
  ─────────────────────────────────────────────────────────────────────────────
  Sits between Bang.Core (raw types) and Bang.Operational (executes terms).

    §1.5 q_or_1 (the let-rule's `q || 1` coeffect floor)
    §1.6 HasVTy, HasCTy (mutual inductive Props — resource-enforcing, Q10/ADR-0019)
    §0.5 Effect-row well-formedness: Disjoint, RowAll, WfInst, HandlesIntended

  Theorem STATEMENTS live in Bang/Spec.lean.
-/

import Bang.Core

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]


/-! ### 1.5 The `q || 1` coeffect floor (`q_or_1`)

Torczon's `T_Let` types its continuation under the bound-var multiplicity
`q1 * q'` where `q' = q_or_1 q2` and `q_or_1 q := if q = 0 then 1 else q`
(`common/coeffects.v`). The floor keeps a `let`-bound name from being graded
`0` purely because the *outer* usage `q2` is `0`; sequencing still forces the
bound computation once. We define it directly via `DecidableEq Mult`. -/

def q_or_1 {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] (q : Mult) : Mult :=
  if q = 0 then 1 else q


/-! ### 1.6 Typing judgments — resource-enforcing, de Bruijn (ADR-0020, Q10)

Two-component **positional** context (ADR-0019's split, ADR-0020's carrier):
a grade-vector `γ : List Mult` (the resources, which split/scale/add) and an
ambient `Γ : List VTy` (the types, shared), SAME length by construction. Ports
Torczon's `VWt`/`CWt` (`resource/CBPV/typing.v`) directly:
  - `gradeVec`/`context` ↦ `γ`/`Γ` (lists indexed by de Bruijn position);
  - `Q+`/`Q*` ↦ `GradeVec.add` (`+`) / `GradeVec.smul` (`•`);
  - the de-Bruijn cons `q .: γ` ↦ `q :: γ` (and `A .: Γ` ↦ `A :: Γ`).

HasVTy : values are inert (no effect grade); judged at VTy.
HasCTy : computations carry an explicit running effect grade `e`; inhabit CTy
         (whose `F q A` annotation is consumer-side coeffect).

ADR-0020: the five named side-conditions are GONE. `vvar`'s grade is the
positional basis vector (`1` at the index, `0` elsewhere) — no `γ y = 0`
freshness, no `(x,C) ∉ Γ` no-dup, no closedness; the cons `q :: γ` *structurally*
pins the bound var's grade and shadows positionally. `q_or_1` (the let coeffect
floor) survives — it is grade arithmetic, not a binder side-condition.

Refinements still open: Q4 (handle — keeps the same-φ shape below; the
label-removing rule is deferred), Q5 (up — omitted pending opArgTy/opResTy). -/

mutual
inductive HasVTy : GradeVec Mult → TyCtx Eff Mult → Val → VTy Eff Mult → Prop where
  -- T_Unit: `γ = 0s` (length matches Γ).
  | vunit  : ∀ {Γ}, HasVTy (GradeVec.zeros Γ.length) Γ Val.vunit VTy.unit
  | vint   : ∀ {Γ n}, HasVTy (GradeVec.zeros Γ.length) Γ (Val.vint n) VTy.int
  -- T_Var: the i-th basis vector (1 at index i, 0 elsewhere); `Γ.get? i` supplies
  -- the type. Position is unique by construction — no no-dup-keys side-condition.
  | vvar   : ∀ {Γ i A},
      Γ[i]? = some A →
      HasVTy (GradeVec.basis Γ.length i) Γ (Val.vvar i) A
  -- T_Thunk: γ passes through unchanged.
  | vthunk : ∀ {γ Γ M φ B},
      HasCTy γ Γ M φ B →
      HasVTy γ Γ (Val.vthunk M) (VTy.U φ B)
inductive HasCTy : GradeVec Mult → TyCtx Eff Mult → Comp → Eff → CTy Eff Mult → Prop where
  -- T_Ret: `γ = q Q* γ'`; the produced value's budget `q` is recorded in `F q A`.
  | ret    : ∀ {γ γ' Γ v A q},
      HasVTy γ' Γ v A →
      γ = q • γ' →
      HasCTy γ Γ (Comp.ret v) ⊥ (CTy.F q A)
  -- T_Let: `q' = q_or_1 q2`; continuation `N` typed under the cons `(q1*q') :: γ₂`
  -- at the bound position 0; `γ = (q' Q* γ₁) Q+ γ₂`. `q1` is M's returner grade,
  -- `q2` the outer usage budget (existentially quantified — not in bare syntax).
  | letC   : ∀ {γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B},
      HasCTy γ₁ Γ M φ₁ (CTy.F q1 A) →
      HasCTy ((q1 * q_or_1 q2) :: γ₂) (A :: Γ) N φ₂ B →
      γ = (q_or_1 q2) • γ₁ + γ₂ →
      HasCTy γ Γ (Comp.letC M N) (φ₁ ⊔ φ₂) B
  -- T_Force: γ passes through.
  | force  : ∀ {γ Γ v φ B},
      HasVTy γ Γ v (VTy.U φ B) →
      HasCTy γ Γ (Comp.force v) φ B
  -- T_Abs: body typed with grade `q` consed at position 0; the arrow records that
  -- same `q` (`A →^q B`). The lam CARRIES its body's latent effect `φ` (ADR-0021,
  -- C1; Torczon `effects/CBPV/typing.v` T_Abs: `CWt Γ (cAbs M) (CAbs A B) ϕ`).
  -- Effects ride the judgment / `U`, not `arr` (ADR-0019/0020), so `lam` threads
  -- `φ` like `force`/`vthunk` do — constructing a closure is operationally pure,
  -- but its type-level effect is the latent body effect (surfaced on application).
  -- An earlier first cut emitted `⊥` here and made `preservation` false on the
  -- `app (lam M) v ↦ M[v]` β-redex (reduct has effect φ, redex was typed ⊥).
  -- Torczon's `Qle q' q` subsumption is DROPPED: it needs an ordered `Mult`
  -- (POSR `le`), but our bound is `[CommSemiring Mult]` with no order (QTT defines
  -- none). Recording `q` directly is the resource-threading core; the subsumption
  -- is an orthogonal feature gated on an ordered semiring.
  | lam    : ∀ {γ Γ M φ q A B},
      HasCTy (q :: γ) (A :: Γ) M φ B →
      HasCTy γ Γ (Comp.lam M) φ (CTy.arr q A B)
  -- T_App: `γ = γ₁ Q+ (q Q* γ₂)`, scaling the argument's grades by the arrow's `q`.
  | app    : ∀ {γ γ₁ γ₂ Γ M v φ q A B},
      HasCTy γ₁ Γ M φ (CTy.arr q A B) →
      HasVTy γ₂ Γ v A →
      γ = γ₁ + q • γ₂ →
      HasCTy γ Γ (Comp.app M v) φ B
  -- up (ADR-0022 D2): perform operation `op` of effect `ℓ`. `labelEff ℓ ≤ φ` is the
  -- lacks-discipline membership "`ℓ ∈ φ`" (ADR-0018) in the abstract lattice. The
  -- grade `q • γ` mirrors `ret`: the produced value's budget `q` scales the
  -- argument's grade — this is what makes the `throws` β-grade match in preservation.
  | up : ∀ {γ Γ} {ℓ : Label} {op : OpId} {v : Val} {φ : Eff} {q : Mult} {A B : VTy Eff Mult},
      EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ →
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A →      -- op IS in ℓ's interface (D6)
      EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B →
      HasVTy γ Γ v A →
      HasCTy (q • γ) Γ (Comp.up ℓ op v) φ (CTy.F q B)
  -- handleThrows (ADR-0022 D4/D5, throws-only — `state` deferred per Q12): the
  -- `throws ℓ` handler DISCHARGES label `ℓ` from the row. Body uses effect `e`
  -- within `ℓ ⊔ φ` (SUBSUMPTION — a `ret v` body has effect `⊥ ≤ ℓ ⊔ φ`); the
  -- derivation picks the residual `φ`, choosing `φ` without `ℓ` discharges `ℓ`.
  -- `opArg ℓ "raise" = opRes ℓ "raise"` (D5 throws clause inlined): raise returns
  -- its payload as the block result, so arg type = result type. Handlers still
  -- handle RETURNERS (`F`-typed, ADR-0021 C2). `handle (state …) M` is now UNtypable
  -- (Q12 deferred); its `Source.step` reductions stay vacuous under typing.
  | handleThrows : ∀ {γ Γ} {ℓ : Label} {M : Comp} {e φ : Eff} {q : Mult} {A : VTy Eff Mult},
      -- ANSWER-TYPE (ADR-0023): the raise payload type = the handle block's result type `A`. A
      -- zero-shot abort yields `ret payload : F q A`, so the payload must inhabit `A`. (The old
      -- `opArg = opRes` premise was masked by the shallow step; the deep handler exposes it.)
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A →
      -- INTERFACE (ADR-0023 D6): label `ℓ`'s only operation is `raise`, so `up ℓ "get"`-style
      -- bodies are untypable — they would be stuck under a `throws ℓ` handler.
      (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise") →
      HasCTy γ Γ M e (CTy.F q A) →
      e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ →
      HasCTy γ Γ (Comp.handle (Handler.throws ℓ) M) φ (CTy.F q A)
  -- handleState (ADR-0025): a RESUMPTIVE state handler. Discharges label `ℓ` like `throws`; its
  -- interface is exactly `{get, put}` with `get : unit → S`, `put : S → unit` (the op-partial
  -- `EffSig`, ADR-0023 D6). The return clause is the identity (ADR-0023 Q6 simpl.), so the handle
  -- block has the body's result type `F q A`. THE GRADE DISCIPLINE (ADR-0025 D2, the Q12 crux): the
  -- initial state `s₀` is required CLOSED (`HasVTy [] [] s₀ S`), grade vector `[]`. The CK machine's
  -- closed focus makes the stored/threaded state grade-`[]`, so resumption copies it at zero variable
  -- budget for ANY `S` — no `ω`-restriction needed (Q12 option 1 is subsumed, not chosen).
  | handleState : ∀ {γ Γ} {ℓ : Label} {s₀ : Val} {M : Comp} {e φ : Eff} {q : Mult}
        {S A : VTy Eff Mult},
      -- INTERFACE: ℓ's ops are exactly get/put with the state signature.
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit →
      EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S →
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S →
      EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit →
      (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put") →
      -- THE GRADE DISCIPLINE: the stored state is a CLOSED value of type `S` (ADR-0025 D2).
      HasVTy [] [] s₀ S →
      HasCTy γ Γ M e (CTy.F q A) →
      e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ →
      HasCTy γ Γ (Comp.handle (Handler.state ℓ s₀) M) φ (CTy.F q A)
end


/-! ### 1.7 Configuration typing (ADR-0023) — the CK machine's stack + state.

`HasStack K e_in C_in e_out C_out`: plugging a focus of type `(e_in, C_in)` into frame stack `K`
yields a whole program of type `(e_out, C_out)`. Binding stays substitution-based, so the focus is
always CLOSED — the stack threads only effects + computation types; grades live inside each `letF`'s
stored continuation (one binder), discharged by the closed-`v` `subst_value`. The frame rules mirror
the corresponding `HasCTy` premises:
  - `letF N` : the `letC` continuation (`N` typed under one binder; total effect `e₁ ⊔ e₂`);
  - `appF v` : the `app` argument (effect unchanged: the function's effect IS the app's);
  - `handleF (throws ℓ)` : discharges `ℓ` (label-removing, ADR-0022 D4) with the answer-type +
    interface premises of `handleThrows` (ADR-0023). A `handleF (state …)` frame is UNtypable (Q12). -/

inductive HasStack : EvalCtx → Eff → CTy Eff Mult → Eff → CTy Eff Mult → Prop where
  | nil : ∀ {e C}, HasStack [] e C e C
  | letF : ∀ {K N e₁ e₂ eo q qk A B Co},
      HasCTy (qk :: []) [A] N e₂ B →
      HasStack K (e₁ ⊔ e₂) B eo Co →
      HasStack (Frame.letF N :: K) e₁ (CTy.F q A) eo Co
  | appF : ∀ {K v e eo q A B Co},
      HasVTy [] [] v A →
      HasStack K e B eo Co →
      HasStack (Frame.appF v :: K) e (CTy.arr q A B) eo Co
  | handleF : ∀ {K ℓ e φ eo q A Co},
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A →
      (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise") →
      e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ →
      HasStack K φ (CTy.F q A) eo Co →
      HasStack (Frame.handleF (Handler.throws ℓ) :: K) e (CTy.F q A) eo Co
  -- stateF (ADR-0025): a reinstalled resumptive `state ℓ s` frame on the stack. Mirrors
  -- `HasCTy.handleState`: discharges `ℓ`, interface `{get,put}` with `get : unit → S`,
  -- `put : S → unit`, the stored state `s` CLOSED of type `S` (the grade discipline, D2).
  | stateF : ∀ {K ℓ s e φ eo q A S Co},
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit →
      EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S →
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S →
      EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit →
      (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put") →
      HasVTy [] [] s S →
      e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ →
      HasStack K φ (CTy.F q A) eo Co →
      HasStack (Frame.handleF (Handler.state ℓ s) :: K) e (CTy.F q A) eo Co

/-- A config is *returned* iff it is `⟨[], ret v⟩` — a value with no work left on the stack. -/
def isReturnConfig : Config → Prop
  | ([], .ret _) => True
  | _            => False

/-- Configuration typing: the focus is closed and well-typed, and the stack carries it to the
whole-program type `(eo, Co)`. -/
def HasConfig (cfg : Config) (eo : Eff) (Co : CTy Eff Mult) : Prop :=
  ∃ e C, HasCTy [] [] cfg.2 e C ∧ HasStack cfg.1 e C eo Co


/-! ### 0.5 Effect-row well-formedness — keeps rows SET-shaped (ADR-0018)

The lacks-constraint discipline that licenses dropping Biernacki's ρ-maps.
With `[Lattice Eff] [OrderBot Eff]` (Q1 resolved), `Disjoint` is concrete
(Mathlib's `_root_.Disjoint`: `a ⊓ b ≤ ⊥`). `WfInst` is concretized below
(ADR-0024 D3); the operational abstraction-safety side (`HandlesWithin`,
`no_accidental_handling`) lives in `Bang/Metatheory.lean §F` (it needs the CK
machine's `handlesOp`). `RowAll`/`HandlesIntended` (the old axioms) are retired:
the monomorphic kernel has no `∀`-row `CTy` former to reify, and the
operational property replaces the abstract `HandlesIntended` placeholder. -/

/-- Two effect rows are disjoint iff their meet is bottom (no shared labels). -/
def Disjoint {Eff : Type} [Lattice Eff] [OrderBot Eff] (e₁ e₂ : Eff) : Prop :=
  _root_.Disjoint e₁ e₂

/-- Well-formedness of instantiating a lacks-constrained row quantifier `∀(α # L). q α` at
row `ε` (ADR-0018 rule 2, ADR-0024 D3): the instantiating row must avoid the forbidden labels
`L`. `WfInst` *is* that disjointness side-condition; the family `q` names the quantifier. The
monomorphic kernel has no `∀`-row binder, so the quantifier lives only as this `(q, L)` pair. -/
def WfInst {Eff Mult : Type} [Lattice Eff] [OrderBot Eff]
    (_q : Eff → CTy Eff Mult) (L ε : Eff) : Prop := Disjoint ε L

end Bang
