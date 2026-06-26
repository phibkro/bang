/-
  scratch/RenameInvarianceProbe.lean — inc-5 Phase-1 WALL de-risk.
  ─────────────────────────────────────────────────────────────────────────────
  The `plug`/`run_plug` adequacy bridge broke under ADR-0055 minting (plug erases
  handle FRAME ids; re-running re-mints). De-risk the principled fix.

  Two tractability questions for the team lead:
    Q1. Does `plug` ignore handler FRAME ids? (→ the bridge can canonicalize the
        observation stack — cheaper than a full bisimulation.)
    Q2. Does dispatch (`splitAtId`) commute with an injective id-renaming, and does
        the MINT arm thread the counter cleanly? (→ renaming-invariance is provable.)
  NO frozen-def edits. Run: `lake env lean scratch/RenameInvarianceProbe.lean`.
-/
import Bang.Operational
namespace Bang.RenameProbe
open Bang
open Bang.EffectRow (Label)

/-! ## 1. Renaming `σ : Nat → Nat` over values / comps / handlers / frames / stacks. -/

mutual
def renameV (σ : Nat → Nat) : Val → Val
  | .vcap n ℓ   => .vcap (σ n) ℓ
  | .vthunk c   => .vthunk (renameC σ c)
  | .inl v      => .inl (renameV σ v)
  | .inr v      => .inr (renameV σ v)
  | .pair a b   => .pair (renameV σ a) (renameV σ b)
  | .fold v     => .fold (renameV σ v)
  | v           => v
def renameC (σ : Nat → Nat) : Comp → Comp
  | .ret v        => .ret (renameV σ v)
  | .letC M N     => .letC (renameC σ M) (renameC σ N)
  | .force v      => .force (renameV σ v)
  | .lam M        => .lam (renameC σ M)
  | .app M v      => .app (renameC σ M) (renameV σ v)
  | .perform c op v => .perform (renameV σ c) op (renameV σ v)
  | .handle h M   => .handle (renameH σ h) (renameC σ M)
  | .case v N₁ N₂ => .case (renameV σ v) (renameC σ N₁) (renameC σ N₂)
  | .split v N    => .split (renameV σ v) (renameC σ N)
  | .unfold v     => .unfold (renameV σ v)
  | c             => c
def renameH (σ : Nat → Nat) : Handler → Handler
  | .state ℓ s  => .state ℓ (renameV σ s)
  | .throws ℓ   => .throws ℓ
  | .transaction ℓ Θ => .transaction ℓ (Θ.map (renameV σ))
end

/-- rename a frame: handleF carries the id; letF/appF only carry sub-terms. -/
def renameF (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF (renameC σ N)
  | .appF v      => .appF (renameV σ v)
  | .handleF n h => .handleF (σ n) (renameH σ h)

def renameK (σ : Nat → Nat) : EvalCtx → EvalCtx := List.map (renameF σ)

@[simp] theorem renameK_nil (σ : Nat → Nat) : renameK σ [] = [] := rfl
@[simp] theorem renameK_cons (σ : Nat → Nat) (fr : Frame) (K : EvalCtx) :
    renameK σ (fr :: K) = renameF σ fr :: renameK σ K := rfl

/-- renaming preserves a handler's label (touches only stored values + ids). -/
@[simp] theorem renameH_label (σ : Nat → Nat) (h : Handler) : (renameH σ h).label = h.label := by
  cases h <;> simp only [renameH, Handler.label]

/-! ## 2. Q1 — `plug` IGNORES handler FRAME ids: renaming the IDS of a stack (with the handler
VALUES held fixed, `σ' = id` on stored caps) leaves `plug` unchanged. This is the id-independence
that lets the bridge CANONICALIZE the observation stack: `Converges (plug C c)` does not see C's ids,
so WLOG C is canonical-id'd. Here, the pure FRAME-id renaming (handlers untouched). -/

def reId (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF N
  | .appF v      => .appF v
  | .handleF n h => .handleF (σ n) h         -- ONLY the frame id changes

theorem plug_reId (σ : Nat → Nat) (c : Comp) :
    ∀ K : EvalCtx, plug (K.map (reId σ)) c = plug K c := by
  intro K
  induction K generalizing c with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp only [List.map_cons, reId, plug, ih]

/-! ## 3. Q2 — `splitAtId` commutes with an INJECTIVE renaming (dispatch is renaming-stable). -/

theorem splitAtId_rename (σ : Nat → Nat) (hσ : Function.Injective σ) (n : Nat) :
    ∀ K : EvalCtx,
      splitAtId (renameK σ K) (σ n)
        = (splitAtId K n).map (fun x => (renameK σ x.1, renameH σ x.2.1, renameK σ x.2.2)) := by
  intro K
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF m h =>
      simp only [renameK_cons, renameF, splitAtId]
      by_cases hmn : m = n
      · subst hmn; rw [if_pos rfl, if_pos rfl]; rfl
      · rw [if_neg hmn, if_neg (fun h => hmn (hσ h)), ih]
        cases splitAtId K n <;> rfl
    | letF N =>
      simp only [renameK_cons, renameF, splitAtId, ih]
      cases splitAtId K n <;> rfl
    | appF v =>
      simp only [renameK_cons, renameF, splitAtId, ih]
      cases splitAtId K n <;> rfl



/-! ## 4. THE FINDING — the bridge is BIGGER than a renaming lemma.

Working the de-risk through reveals: under minting, running `plug C c` does NOT reach `(C, c)`. The
machine, stepping the `handle` nodes `plug` rebuilt, (a) advances the COUNTER, (b) assigns C's handler
frames CANONICAL ids (depth order, NOT C's original ids), and (c) SUBSTITUTES C's capabilities into the
focus (the handle binder). So `run_plug`'s RHS becomes `(handlerCount C, canonStack C, capSubst C c)`,
not `(C, c)`. Demonstrated on ONE handle frame below (rfl): plugging `[handleF 4 (state 1 _)]` and
stepping mints the COUNTER's id (7) — not 4 — and substitutes `vcap 7` into the body. -/

example (s : Val) (M : Comp) :
    Source.step (7, [], plug [Frame.handleF 4 (Handler.state 1 s)] M)
      = some (8, [Frame.handleF 7 (Handler.state 1 s)], Comp.subst (Val.vcap 7 1) M) := rfl

/-! So the renaming primitives above (§2 plug-id-independence, §3 splitAtId-commutation) are NECESSARY
INPUTS but not SUFFICIENT: closing `run_plug` needs it re-proven to the canonical-reached-config form
(counter + canonical ids + cap-substitution), whose exact shape couples to whether `KrelS` observes
SOURCE-shaped configs `(K, c)` (caps as `vvar`s under handles) or MACHINE-shaped ones (caps already
`vcap`-substituted). That is the design decision to make before the metering-spine re-key. -/
end Bang.RenameProbe
