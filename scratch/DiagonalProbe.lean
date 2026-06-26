/-
  scratch/DiagonalProbe.lean — inc-5 PHASE 0 de-risk (LR re-index).
  ────────────────────────────────────────────────────────────────────────────
  Two arbitrations, BUILD-checked over the live kernel (Bang.Operational/Syntax),
  NO frozen-def edits. Run: `lake env lean scratch/DiagonalProbe.lean`.

  AXIS 1 (§A) — the `closeC_handle` shape under ADR-0054 identity caps.
    The committed `closeC_handleThrows/State/Transaction` (Compat:218/230/244) are
    PASS-THROUGH (handle non-binding, ADR-0053 era). Under the current kernel
    `handle` BINDS the cap (Comp.substFrom descends at k+1, Operational:111), so the
    correct shape is a BINDER-DESCENT, mirroring `closeC_lam` (Compat:684). Proven
    here + a concrete witness that the pass-through value is WRONG.

  AXIS 2 (§B) — route α (binary LR) vs β (unary reachability) for the diagonal
    `HasConfigTy (0,[],c) ⊥ (F q A) → NonEscape (0,[],c)`. Claim: β is the right
    tool — NonEscape is a pure REACHABILITY consequence of a forward-closed focus
    invariant, needing NO relation. The assembly is proven GREEN; the concrete
    invariant is seeded + its walls named. Plus the VcapFree-necessity finding.
-/
import Bang.Operational
import Bang.Syntax

namespace Bang.DiagonalProbe
open Bang
open Bang.EffectRow (Label)

/-! ## §A — `closeC_handle` is a BINDER-DESCENT (lam-shape), not pass-through.

`closeC`/`closeV`/`closeCUnderBinders`/`shiftN` replicated from LR.lean §5.2b / Compat
§B.1 (those modules are red; this is scratch). -/

def shiftN : Nat → Val → Val
  | 0,     v => v
  | d + 1, v => Val.shift (shiftN d v)

def closeC : List Val → Comp → Comp
  | [],     c => c
  | v :: δ, c => closeC δ (Comp.subst v c)

def closeV : List Val → Val → Val
  | [],     v => v
  | u :: δ, v => closeV δ (Val.subst u v)

def closeH : List Val → Handler → Handler
  | [],     h => h
  | v :: δ, h => closeH δ (Handler.substFrom 0 v h)

def closeCUnderBinders (d : Nat) : List Val → Comp → Comp
  | [],     c => c
  | v :: δ, c => closeCUnderBinders d δ (Comp.substFrom d (shiftN d v) c)

/-- The lam-shape `closeC_lam` (Compat:684), reproduced as the template. -/
theorem closeC_lam (δ : List Val) (M : Comp) :
    closeC δ (Comp.lam M) = Comp.lam (closeCUnderBinders 1 δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeCUnderBinders, Comp.subst, Comp.substFrom, shiftN]; exact ih _

/-- ★ THE AXIS-1 RESULT: `handle` closes like `lam` — the body descends under the
cap binder (`closeCUnderBinders 1`), the handler's stored value closes at level 0
(`closeH`). NO cap-shift (the ADR-0050 wall is gone). The committed pass-through
`= handle h (closeC δ M)` is REFUTED by the witness below. -/
theorem closeC_handle (δ : List Val) (h : Handler) (M : Comp) :
    closeC δ (Comp.handle h M) = Comp.handle (closeH δ h) (closeCUnderBinders 1 δ M) := by
  induction δ generalizing h M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeH, closeCUnderBinders, Comp.subst, Comp.substFrom, shiftN]
    exact ih _ _

/-- WITNESS: closing `handle (throws 2) (ret (vvar 0))` with `δ=[vint 7]` must LEAVE
the cap var (index 0) UNTOUCHED — it's the handle-bound capability, shielded by the
binder descent. The pass-through lemma would (wrongly) substitute it to `vint 7`. -/
example :
    closeC [Val.vint 7] (Comp.handle (Handler.throws 2) (Comp.ret (Val.vvar 0)))
      = Comp.handle (Handler.throws 2) (Comp.ret (Val.vvar 0)) := by
  rfl

/-- …and the pass-through value is genuinely DIFFERENT (the committed lemma is wrong-shaped). -/
example :
    closeC [Val.vint 7] (Comp.handle (Handler.throws 2) (Comp.ret (Val.vvar 0)))
      ≠ Comp.handle (Handler.throws 2) (Comp.ret (Val.vint 7)) := by
  intro h
  -- LHS reduces (rfl) to `handle (throws 2) (ret (vvar 0))`; peel to `vvar 0 = vint 7`.
  injection h with _ hbody; injection hbody with hval; exact Val.noConfusion hval

/-! ## §B — the diagonal is a UNARY REACHABILITY property (route β), not a relation.

`NonEscape cfg := ∀ cfg', StepStar cfg cfg' → FocusResolves cfg'` (Operational:507).
Route β: find a forward-closed invariant `P` with `P ⇒ FocusResolves` at the focus.
NonEscape is then its reachability closure — NO binary LR, NO `crelK_fund` re-key. -/

/-- ★ THE AXIS-2 ARCHITECTURE RESULT (GREEN, no sorry): ANY step-preserved invariant
that implies `FocusResolves` at every config gives `NonEscape` by reachability
induction. This is `wellCounted_reachable`'s shape (Operational:766) — confirming the
diagonal lives in the UNARY reachability world, where route β operates, not in the
relational LR (route α). α would route a unary fact through `crelK_fund` — wrong tool. -/
theorem nonEscape_of_fwd_invariant (P : Config → Prop)
    (hpos  : ∀ cfg, P cfg → FocusResolves cfg)
    (hpres : ∀ cfg cfg', P cfg → Source.step cfg = some cfg' → P cfg')
    (cfg : Config) (hP : P cfg) : NonEscape cfg := by
  -- P holds along every reachable path (induction on StepStar), then read off FocusResolves.
  have hreach : ∀ cfg', StepStar cfg cfg' → P cfg' := by
    intro cfg' h
    induction h with
    | refl => exact hP
    | tail _ hstep ih => exact hpres _ _ ih hstep
  exact fun cfg' hr => hpos _ (hreach cfg' hr)

/-! ### The concrete β invariant — `WellScoped`: every `vcap` in the config resolves.

`capsC`/`capsV`/`capsH` collect the (identity, label) of every `vcap` node; `ResolvesLabel`
says the id lands on a same-label handler frame. -/

mutual
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

/-- the cap `(n,ℓ)` lands on a same-LABEL handler frame on `K`. (Label-match; the op-in-
interface check is the secondary typing dependency, see `hpos` below.) -/
def ResolvesLabel (K : EvalCtx) (n : Nat) (ℓ : Label) : Prop :=
  ∃ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) ∧ Handler.label h = ℓ

/-- **The route-β invariant.** Every `vcap` in focus + stack resolves to its handler. -/
def WellScoped : Config → Prop
  | (_, K, c) => ∀ p ∈ capsC c ++ capsK K, ResolvesLabel K p.1 p.2

/-- **SEED (GREEN).** A `vcap`-free closed source program trivially satisfies `WellScoped`
at the initial config — there are no caps to resolve. (`VcapFree` = `capsC c = []`.) -/
theorem wellScoped_initial (c : Comp) (hvf : capsC c = []) : WellScoped (0, [], c) := by
  intro p hp
  simp only [capsK, List.append_nil, hvf] at hp
  exact absurd hp (List.not_mem_nil)

/-- **POSITIVE (the secondary wall).** `WellScoped ⇒ FocusResolves`. Closes EXCEPT the
op-in-interface gap: `FocusResolves` needs `handlesOp h ℓ op` (label==ℓ AND op∈h's ops);
`WellScoped` gives the label match, the op-membership is a HasConfigTy fact (the focus
`perform`'s `op` is in `ℓ`'s interface, Syntax `HasCTy.perform` opArg/opRes premises, and
the resolved frame is the ℓ-handler whose interface = ℓ's ops). Stated with that as the
labelled hypothesis `hop`; the rest is by construction. -/
theorem focusResolves_of_wellScoped (cfg : Config) (hWS : WellScoped cfg)
    (hop : ∀ K n ℓ op v, cfg = (cfg.1, K, Comp.perform (Val.vcap n ℓ) op v) →
            ∀ Kᵢ h Kₒ, splitAtId K n = some (Kᵢ, h, Kₒ) → Handler.label h = ℓ →
            handlesOp h ℓ op = true) :
    FocusResolves cfg := by
  obtain ⟨g, K, c⟩ := cfg
  -- FocusResolves is `True` except on a `perform (vcap …)` focus.
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

/-! ### PRESERVATION — the PRIMARY wall (named, not closed this pass).

`WellScoped` preservation has exactly these arms (Source.step, Operational:455):
  • PUSH/REDUCE non-cap arms (letC/app/force/case/split/unfold/letF/appF-reduce): the
    cap multiset is preserved or shrinks and `K` only grows below → MECHANICAL.
  • MINT (`handle h M ↦ (g+1, handleF g h :: K, subst (vcap g ℓ) M)`): introduces `vcap g`
    AND pushes `handleF g` simultaneously → the new cap resolves to the just-pushed frame
    (label match by construction); old caps still resolve (frame only added below, splitAtId
    monotone under a non-matching cons — `g` is fresh by `WellCounted`, ADR-0055). PROVABLE.
  • DISPATCH (`perform (vcap n ℓ) ↦ idDispatch`): reinstalls `handleF n` on resume / pops to
    `Kₒ` on abort; `stackBelow_idDispatch` (Operational:671) is the WellCounted analogue.
    PROVABLE (same shape as the merged inc-4 lemma).
  • POP-ESCAPE (`handleF n :: K, ret v ↦ K, ret v`): if `v` (or `K`) carries `vcap n`, it no
    longer resolves after the pop ⇒ `WellScoped` BREAKS. This is the ONE research arm — it is
    discharged by the ⊥-row / return-escape discipline: a well-typed-at-⊥ value returned past
    `handleF n` cannot expose a performable `Cap ℓ` for the popped `ℓ` (performing it needs an
    ℓ-handler, absent at ⊥). = `preservation_returnEscape` (ADR-0054 LWT gate). NEEDS the focus
    TYPING, so the real invariant is `WellScoped ∧ HasConfigTy` (typing rides along). -/
theorem wellScoped_step (cfg cfg' : Config)
    (hWS : WellScoped cfg) (hstep : Source.step cfg = some cfg') : WellScoped cfg' := by
  -- The non-escape arms are mechanical; the pop-escape arm needs the typing co-invariant
  -- (returnEscape). Banked as the labelled PRIMARY WALL for inc-5 Phase 3.
  sorry

/-! ### NON-VACUITY + the VcapFree-necessity FINDING (decidable, build-checked). -/

/-- run to the first cap-dispatch focus; report `capResolvesB` there (reuses the
NonEscapeProbe decidable reflection inline). -/
def capResolvesB (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) : Bool :=
  match splitAtId K n with
  | some (_, h, _) => handlesOp h ℓ op
  | none           => false

def firstPerformResolves : Nat → Config → Option Bool
  | 0, _ => none
  | _+1, (_, K, .perform (.vcap n ℓ) op _) => some (capResolvesB K n ℓ op)
  | f+1, cfg => match Source.step cfg with
                | some cfg' => firstPerformResolves f cfg'
                | none      => none

/-- SAFE — the insert-below-target migration (= `capMigrateInternal`): resolves + yields 7. -/
def migrateWitness : Comp :=
  .app (.lam (.handle (.throws 2) (.force (.vvar 1))))
    (.vthunk (.handle (.state 1 (.vint 7)) (.perform (.vvar 0) "get" .vunit)))
#guard firstPerformResolves 200 (0, [], migrateWitness) == some true
#guard (match Source.eval 200 migrateWitness with | .done (.vint 7) => true | _ => false)

/-- ESCAPE — the `state` handle wraps the `ret` (cap escapes its handler): does NOT
resolve, runs STUCK. `WellScoped` correctly REJECTS it (its escaped `vcap` fails to resolve). -/
def escapeWitness : Comp :=
  .letC (.handle (.state 1 (.vint 7)) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))
#guard firstPerformResolves 200 (0, [], escapeWitness) == some false
#guard (match Source.eval 200 escapeWitness with | .stuck => true | _ => false)

/-- ★ THE VcapFree-NECESSITY FINDING: a HAND-WRITTEN `vcap 5` literal (no `handle` mints
id 5) is structurally typeable (`HasVTy.vcap` types any `vcap n ℓ`, Syntax:71; the `state`
handle discharges `ℓ` so the whole program is at ⊥) — yet it runs STUCK (`splitAtId
[handleF 0] 5 = none`). So the bare diagonal `HasConfigTy → NonEscape` is FALSE; it needs a
`VcapFree` (capsC c = []) side-condition on the SOURCE (the elaborator invariant, Core:86).
A definitional finding to surface: `type_safety`/the diagonal carry `VcapFree c`. -/
def handwrittenVcap : Comp :=
  .handle (.state 1 (.vint 9)) (.perform (.vcap 5 1) "get" .vunit)
#guard (match Source.eval 200 handwrittenVcap with | .stuck => true | _ => false)
#guard capsC handwrittenVcap ≠ []   -- NOT VcapFree → excluded by the side-condition

end Bang.DiagonalProbe
