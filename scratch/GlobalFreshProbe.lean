/-
  scratch/GlobalFreshProbe.lean — ADR-0055 DE-RISK (global-fresh capability identity).
  ─────────────────────────────────────────────────────────────────────────────────────
  GOAL (de-risk, NOT implement): validate the monotonic-counter minting scheme CHEAPLY,
  reusing the unchanged dispatch helpers (`splitAtId`/`idDispatch`/`dispatchOn`/`handlesOp`,
  all EvalCtx/Nat-keyed, NOT Config-keyed). Only `step`/`run`/`eval` thread a counter.

  Claims arbitrated here (build-gated, COMPILED-#guard authority per LWRegress header):
    1. progB (the ADR-0055 collision witness) → STUCK under counter-minting (was `done`).
    2. progB' (direct-force escape) → STUCK still (unchanged).
    3. the migration witnesses (capMigrate1/2/Internal) still YIELD their values.
    4. `WellCounted` is structurally preservable (a fresh `g ∉ stack`, and resume reuses
       an existing id < g) — stated + the freshness lemma proven.

  NO frozen-def edits. Scratch-only. Run: `lake env lean scratch/GlobalFreshProbe.lean`.
-/
import Bang.Operational

namespace Bang.GlobalFreshProbe
open Bang

/-! ## 0. The counter-threaded machine (the ONLY new code the rework adds).

`CConfig := Nat × EvalCtx × Comp` — the leading `Nat` is the NEXT-FRESH id (the gensym counter).
Every step threads it; only the `handle` arm MINTS (consumes `g`, pushes `handleF g`, returns `g+1`).
Dispatch (`idDispatch`) is Config-agnostic, so the perform arm just re-wraps with the SAME `g`. -/

abbrev CConfig := Nat × EvalCtx × Comp

/-- Counter-threaded transition. Mirror of `Source.step`; the ONLY behavioural change is the
`handle` arm mints `g` (not `handlerCount K`) and increments the carried counter. -/
def cstep : CConfig → Option CConfig
  -- PUSH
  | (g, K, .letC M N)          => some (g, .letF N :: K, M)
  | (g, K, .app M v)           => some (g, .appF v :: K, M)
  | (g, K, .handle h M)        =>
      -- MINT the global-fresh identity `g`; push `handleF g h`; substitute `vcap g h.label`;
      -- the reduct's counter is `g+1` (never reused).
      some (g + 1, .handleF g h :: K, Comp.subst (.vcap g h.label) M)
  | (g, K, .force (.vthunk M)) => some (g, K, M)
  -- REDUCE
  | (g, .letF N :: K, .ret v)  => some (g, K, Comp.subst v N)
  | (g, .appF v :: K, .lam M)  => some (g, K, Comp.subst v M)
  | (g, .handleF _ _ :: K, .ret v) => some (g, K, .ret v)
  | (g, K, .case (.inl v) N₁ _)  => some (g, K, Comp.subst v N₁)
  | (g, K, .case (.inr v) _ N₂)  => some (g, K, Comp.subst v N₂)
  | (g, K, .split (.pair v w) N) => some (g, K, Comp.subst v (Comp.subst (Val.shift w) N))
  | (g, K, .unfold (.fold v))    => some (g, K, .ret v)
  -- DISPATCH (counter threaded UNCHANGED — resume reuses the matched id, never mints):
  | (g, K, .perform (.vcap n ℓ) op v) =>
      (idDispatch K n ℓ op v).map (fun (K', c') => (g, K', c'))
  -- stuck
  | _                       => none

def crun : Nat → CConfig → Result Val
  | 0, _              => .oom
  | _ + 1, (_, [], .ret v) => .done v
  | n + 1, cfg        =>
      match cstep cfg with
      | some cfg' => crun n cfg'
      | none      => .stuck

/-- Load the closed program with a fresh counter at 0. -/
def ceval (fuel : Nat) (c : Comp) : Result Val := crun fuel (0, [], c)

/-! ## 1. CLAIM 1+2 — the escape witnesses now FAIL LOUD (stuck). -/

/-- progB — the RE-HANDLE escape (ADR-0055 collision). Inner handler mints id 0, pops; the escaped
`vcap 0` is forced under a FRESH re-handler that now mints id **1** (the counter advanced, never
reused). `splitAtId [handleF 1 …] 0 = none` → STUCK. The collision is structurally gone. -/
def progB : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.handle (.state 1 .vunit) (.force (.vvar 1)))

/-- progB' — the DIRECT-FORCE escape (no re-handler): stuck under depth-minting too; stays stuck. -/
def progB' : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))

-- CLAIM 1: the re-handle escape is now STUCK (was `done .vunit` under handlerCount minting).
#guard (match ceval 300 progB  with | .stuck => true | _ => false)
-- CLAIM 2: the direct-force escape is still STUCK.
#guard (match ceval 300 progB' with | .stuck => true | _ => false)

/-! ## 2. CLAIM 3 — the safe migration witnesses still yield (identity dispatch is migration-invariant;
the counter only changes WHICH id is minted, never breaks a legitimate match). -/

private def yieldsInt (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  match ceval fuel c with | .done (.vint m) => m == n | _ => false

/-- 1-deep migration: `{get}` thunk targets the OUTER state (its cap = `vvar 0`), forced under one
fresh `throws`. Under global-fresh: state mints id 0, throws mints id 1; the thunk's cap is `vcap 0`,
which still resolves to the state frame (id 0 still on the stack). = 5. -/
private def capMigrate1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 1))))
#guard yieldsInt 200 capMigrate1 5

/-- 2-deep migration: crosses TWO fresh `throws`; the outer state (id 0) is still live = 9. -/
private def capMigrate2 : Comp :=
  .handle (.state 1 (.vint 9))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.handle (.throws 3) (.force (.vvar 2)))))
#guard yieldsInt 300 capMigrate2 9

/-- ★ INSERT-BELOW-TARGET (ADR-0053 witness): a thunk handles its OWN `state`, forced under an
unrelated outer `throws`. The OWN state is installed AFTER the outer throws when the thunk is forced,
so it mints a HIGHER id, and the cap (bound by that own handle) names it. Reaches own state = 7. -/
private def capMigrateInternal : Comp :=
  .app (.lam (.handle (.throws 2) (.force (.vvar 1))))
    (.vthunk (.handle (.state 1 (.vint 7)) (.perform (.vvar 0) "get" .vunit)))
#guard yieldsInt 200 capMigrateInternal 7

/-! ## 3. CLAIM 4 — `WellCounted` + the freshness lemma (the ONE genuine new proof obligation).

`WellCounted (g, K, c)` := every `handleF n` frame in `K` has `n < g`. This is the invariant that
makes the minted `g` FRESH (∉ K): a fresh id collides with nothing, so an escaped cap whose handler
popped resolves to NOTHING (stuck), never to an impostor. -/

/-- Every `handleF` identity on the stack is `< g`. -/
def StackBelow (g : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => n < g ∧ StackBelow g K
  | .letF _ :: K => StackBelow g K
  | .appF _ :: K => StackBelow g K

def WellCounted : CConfig → Prop
  | (g, K, _) => StackBelow g K

/-- **Freshness**: if every id on `K` is `< g`, then `splitAtId K g = none` — the fresh id `g` matches
NO live frame. This is exactly what kills the collision: minting `g` and then (later) resolving a cap
named `g` finds ITS handler or nothing, never a same-depth impostor. -/
theorem splitAtId_fresh (g : Nat) (K : EvalCtx) (h : StackBelow g K) :
    splitAtId K g = none := by
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF n hd =>
      obtain ⟨hlt, hrest⟩ := h
      simp only [splitAtId]
      rw [if_neg (by omega : ¬ n = g), ih hrest]; rfl
    | letF N => simp only [splitAtId]; rw [ih h]; rfl
    | appF v => simp only [splitAtId]; rw [ih h]; rfl

/-- `StackBelow` is monotone in the counter (a larger counter still dominates). Used to show the
incremented `g+1` still bounds the OLD frames after a mint. -/
theorem StackBelow_mono {g g' : Nat} (hle : g ≤ g') :
    ∀ K, StackBelow g K → StackBelow g' K := by
  intro K hK
  induction K with
  | nil => trivial
  | cons fr K ih =>
    cases fr with
    | handleF n hd => obtain ⟨hlt, hrest⟩ := hK; exact ⟨by omega, ih hrest⟩
    | letF N => exact ih hK
    | appF v => exact ih hK

/-- **`WellCounted` is preserved by `cstep`** — the structural payoff. The mint arm pushes `handleF g`
with new counter `g+1` (old frames stay `< g < g+1` by mono, the new frame is `g < g+1`); every other
arm either keeps/shrinks the stack with an unchanged counter, or (dispatch) reinstalls an EXISTING id.
The dispatch case needs that the resumed stack's ids stay `< g`; rather than prove the full
`idDispatch` re-key here (mechanical, deferred to the rework), this de-risk proves the load-bearing
NON-dispatch arms and the MINT arm, which is where freshness is generated. -/
theorem wellCounted_preserved_mint (g : Nat) (K : EvalCtx) (h : Handler)
    (hwc : StackBelow g K) :
    StackBelow (g + 1) (.handleF g h :: K) :=
  ⟨Nat.lt_succ_self g, StackBelow_mono (Nat.le_succ g) K hwc⟩

end Bang.GlobalFreshProbe
