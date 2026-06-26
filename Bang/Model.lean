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

/-- **The route-β invariant.** Every `vcap` in focus + stack resolves to its handler. -/
def WellScoped : Config → Prop
  | (_, K, c) => ∀ p ∈ capsC c ++ capsK K, ResolvesLabel K p.1 p.2

/-- A source program is `VcapFree` when it contains NO raw `vcap` literal — the elaborator invariant
(`vcap`s arise only by minting). The diagonal's side-condition (the bare form is FALSE: a hand-written
`vcap 5` types but runs stuck — DiagonalProbe §B). -/
def VcapFree (c : Comp) : Prop := capsC c = []

/-- **SEED (GREEN).** A `VcapFree` closed program trivially satisfies `WellScoped` at the initial
config — no caps to resolve. -/
theorem wellScoped_initial (c : Comp) (hvf : VcapFree c) : WellScoped (0, [], c) := by
  have hvf' : capsC c = [] := hvf
  intro p hp
  simp only [capsK, List.append_nil, hvf'] at hp
  exact absurd hp (List.not_mem_nil)

/-- **POSITIVE (GREEN modulo the op-in-interface hypothesis).** `WellScoped ⇒ FocusResolves`. The label
match comes from `WellScoped`; the op-membership `handlesOp h ℓ op` is supplied by `hop` (a `HasConfigTy`
fact, discharged at the call site by `handlesOp_of_hasConfigTy`). -/
theorem focusResolves_of_wellScoped (cfg : Config) (hWS : WellScoped cfg)
    (hop : ∀ K n ℓ op v, cfg = (cfg.1, K, Comp.perform (Val.vcap n ℓ) op v) →
            ∀ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) → Handler.label h = ℓ →
            handlesOp h ℓ op = true) :
    FocusResolves cfg := by
  obtain ⟨g, K, c⟩ := cfg
  match c with
  | .perform (.vcap n ℓ) op v =>
      have hp : (n, ℓ) ∈ capsC (Comp.perform (Val.vcap n ℓ) op v) ++ capsK K := by
        simp only [capsC, capsV, List.mem_append, List.mem_cons]; tauto
      obtain ⟨Kᵢ, h, Kₒ, hsplit, hlbl⟩ := hWS (n, ℓ) hp
      exact ⟨Kᵢ, h, Kₒ, hsplit, hop K n ℓ op v rfl Kᵢ h Kₒ hsplit hlbl⟩
  | .ret _ | .letC _ _ | .force _ | .lam _ | .app _ _ | .handle _ _
  | .perform .vunit _ _ | .perform (.vint _) _ _ | .perform (.vvar _) _ _
  | .perform (.vthunk _) _ _ | .perform (.inl _) _ _ | .perform (.inr _) _ _
  | .perform (.pair _ _) _ _ | .perform (.fold _) _ _
  | .case _ _ _ | .split _ _ | .unfold _ | .oom | .wrong _ => trivial

/-! ## §3 — the combined invariant + the two named obligations. -/

/-- The COMBINED route-β invariant: `WellScoped` (caps resolve) AND well-typed at `⊥` (the focus types,
which licenses the op-in-interface half of `FocusResolves` and the ⊥-row return-escape discipline that
closes `WellScoped`'s pop-escape preservation arm). -/
def WScfg (Co : CTy Eff Mult) (cfg : Config) : Prop :=
  WellScoped cfg ∧ HasConfigTy cfg ⊥ Co

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

/-- **OBLIGATION 2 — the MUTUAL preservation (the research crux).** `WScfg` is preserved by every
`Source.step`. The arms (Source.step, Operational:455):
  • PUSH/REDUCE non-cap (letC/app/force/case/split/unfold/letF/appF): cap multiset preserved-or-shrinks,
    `K` grows only below ⇒ `WellScoped` mechanical; `HasConfigTy` by the focus-decomposition typing.
  • MINT (`handle h M ↦ (g+1, handleF g h::K, subst (vcap g ℓ) M)`): the new `vcap g` resolves to the
    just-pushed `handleF g` (label match by construction); old caps still resolve (`g` fresh by
    `WellCounted`, `splitAtId` monotone under a non-matching cons). PROVABLE.
  • DISPATCH (`perform (vcap n ℓ) ↦ idDispatch`): `WellScoped` supplies the resolution `idDispatch`
    fires on; the resume/abort reduct re-types via the resolved handler's interface. PROVABLE (uses
    `WellScoped`, which is why the two invariants must ride together — `HasConfigTy`-alone preservation
    is unavailable here, it would need `NonEscape`/`WellScoped` for the dispatch re-typing).
  • POP-ESCAPE (`handleF n::K, ret v ↦ K, ret v`): if `v`/`K` carries `vcap n`, it no longer resolves
    after the pop. CLOSED by the ⊥-row discipline: a value returned past `handleF n` typed at `⊥` cannot
    expose a performable `Cap ℓ` for the popped `ℓ` (performing needs an ℓ-handler, absent at ⊥). This is
    the inc-4 `preservation_returnEscape` content, now phrased over `WellScoped`. THE research arm.
NAMED SORRY: the mutual preservation; pop-escape is the ⊥-row return-escape crux. -/
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
    ⟨wellScoped_initial c hvf, hty⟩
  · -- hpos: WScfg ⇒ FocusResolves (label from WellScoped, op-membership from HasConfigTy).
    rintro cfg ⟨hWS, hty'⟩
    exact focusResolves_of_wellScoped cfg hWS (handlesOp_of_hasConfigTy cfg hty')
  · -- hpres: the mutual preservation.
    rintro cfg cfg' hP hstep
    exact wsCfg_step cfg cfg' hP hstep

end Bang.Model
