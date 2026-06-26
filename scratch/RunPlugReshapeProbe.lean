/-
  scratch/RunPlugReshapeProbe.lean — inc-5 Phase-1, the `run_plug` reshape lemma.
  ─────────────────────────────────────────────────────────────────────────────
  Under ADR-0055 global-fresh minting, `plug` ERASES handler-frame ids and re-running
  a plugged context RE-MINTS canonical ids (counter 0,1,2,… in outermost-push order)
  and SUBSTITUTES each minted capability into everything it encloses. So running
  `plug C c` does NOT reach `(C, c)`; it reaches the CANONICAL-reached config.

  This probe DEFINES that reached config (`reshape`, with `canonStack`/`capSubstInto`
  the stack/focus projections) and PROVES:

    run_plug_reshape : Config.run (n + C.length) (0, [], plug C c)
                     = Config.run n (handlerCount C, canonStack C c, capSubstInto C c)

  plus the renaming-invariance BRIDGE the inc-5 LR consumes (Source.step / Config.run
  commute with an injective id-renaming → the canonical-id config and the original-id
  config run to renamed-equal results).

  HARD boundary: writes ONLY this scratch file. READS Bang.Operational + the §2/§3
  renaming primitives of scratch/RenameInvarianceProbe (re-derived here, since a scratch
  file cannot import another scratch file across the build graph — flagged for the IC).

  Run: `nix develop -c lake env lean scratch/RunPlugReshapeProbe.lean`.
-/
import Bang.Operational
namespace Bang.RunPlugReshape
open Bang
open Bang.EffectRow (Label)

/-! ## 0. The machine's PUSH/handle sub-step — `stepReshape`.

`stepReshape` is the restriction of `Source.step` to the three "descend into the focus"
arms (PUSH `letC`/`app`, and the `handle` MINT). On those foci it agrees with `Source.step`
DEFINITIONALLY (`step_eq_stepReshape`); on any other focus it is the identity (those foci
never arise as the head of a `reshape` recursion). -/
def stepReshape : Config → Config
  | (g, K, .letC M N)   => (g, .letF N :: K, M)
  | (g, K, .app M v)    => (g, .appF v :: K, M)
  | (g, K, .handle h M) => (g + 1, .handleF g h :: K, Comp.subst (.vcap g h.label) M)
  | cfg                 => cfg

/-- On a `letC`/`app`/`handle` focus, `Source.step` fires and equals `stepReshape`. -/
theorem step_eq_stepReshape_letC (g : Nat) (K : EvalCtx) (M N : Comp) :
    Source.step (g, K, .letC M N) = some (stepReshape (g, K, .letC M N)) := rfl
theorem step_eq_stepReshape_app (g : Nat) (K : EvalCtx) (M : Comp) (v : Val) :
    Source.step (g, K, .app M v) = some (stepReshape (g, K, .app M v)) := rfl
theorem step_eq_stepReshape_handle (g : Nat) (K : EvalCtx) (h : Handler) (M : Comp) :
    Source.step (g, K, .handle h M) = some (stepReshape (g, K, .handle h M)) := rfl

/-! ## 1. The reached config — `reshape`.

`reshape g K C c` is the config that `(g, K, plug C c)` runs to after exactly `C.length`
steps (the machine descends every frame of `plug C c`). Recursion is on `C` (innermost-first):
`plug (fr :: C') c = plug C' (fr.wrapStep c)` (the outer frames `C'` wrap `fr.wrapStep c`),
so the machine processes `C'` first (reaching `reshape g K C' (fr.wrapStep c)`) and then takes
ONE more `stepReshape` to peel the now-innermost frame `fr`. -/
def reshape (g : Nat) (K : EvalCtx) : EvalCtx → Comp → Config
  | [], c      => (g, K, c)
  | fr :: C', c => stepReshape (reshape g K C' (fr.wrapStep c))

@[simp] theorem reshape_nil (g : Nat) (K : EvalCtx) (c : Comp) :
    reshape g K [] c = (g, K, c) := rfl
@[simp] theorem reshape_cons (g : Nat) (K : EvalCtx) (fr : Frame) (C' : EvalCtx) (c : Comp) :
    reshape g K (fr :: C') c = stepReshape (reshape g K C' (fr.wrapStep c)) := rfl

/-- SANITY (rfl): `reshape` matches the machine — one `state` handle frame, counter `7`, mints id `7`
(not the erased `4`) and substitutes `vcap 7 1`. (Mirror of RenameInvarianceProbe §4's `rfl` witness.) -/
example (s : Val) (M : Comp) :
    reshape 7 [] [Frame.handleF 4 (Handler.state 1 s)] M
      = (8, [Frame.handleF 7 (Handler.state 1 s)], Comp.subst (Val.vcap 7 1) M) := rfl

/-! ## 2. `stepReshape` on a known focus head, and `Source.step` agreement.

When the focus head is `letC`/`app`/`handle`, `stepReshape` and `Source.step` both fire to the same
config. These project-out lemmas let the inductions below peel a frame knowing only the focus head. -/
theorem stepReshape_letC (cfg : Config) (a b : Comp) (h : cfg.2.2 = .letC a b) :
    stepReshape cfg = (cfg.1, .letF b :: cfg.2.1, a) := by
  obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem stepReshape_app (cfg : Config) (a : Comp) (v : Val) (h : cfg.2.2 = .app a v) :
    stepReshape cfg = (cfg.1, .appF v :: cfg.2.1, a) := by
  obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem stepReshape_handle (cfg : Config) (hd : Handler) (a : Comp) (h : cfg.2.2 = .handle hd a) :
    stepReshape cfg = (cfg.1 + 1, .handleF cfg.1 hd :: cfg.2.1, Comp.subst (.vcap cfg.1 hd.label) a) := by
  obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl

theorem step_fires_letC (cfg : Config) (a b : Comp) (h : cfg.2.2 = .letC a b) :
    Source.step cfg = some (stepReshape cfg) := by obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem step_fires_app (cfg : Config) (a : Comp) (v : Val) (h : cfg.2.2 = .app a v) :
    Source.step cfg = some (stepReshape cfg) := by obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem step_fires_handle (cfg : Config) (hd : Handler) (a : Comp) (h : cfg.2.2 = .handle hd a) :
    Source.step cfg = some (stepReshape cfg) := by obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl

/-! ## 3. `applyCaps` — the cumulative cap-substitution `reshape` applies to its focus.

`reshape`'s focus is the innermost `c` with each enclosing handle's minted capability substituted in (at
the right de Bruijn level). We do NOT need its closed form — only that the focus is `applyCaps L c` for
SOME list `L` of `(level, filler)` substitutions, which preserves `c`'s head constructor. `bumpL` lifts
every level by one (and shifts the fillers) as substitution crosses a binder. -/
def applyCaps : List (Nat × Val) → Comp → Comp
  | [], c        => c
  | (k, v) :: L, c => applyCaps L (Comp.substFrom k v c)
def applyCapsV : List (Nat × Val) → Val → Val
  | [], v        => v
  | (k, u) :: L, v => applyCapsV L (Val.substFrom k u v)
def applyCapsH : List (Nat × Val) → Handler → Handler
  | [], h        => h
  | (k, u) :: L, h => applyCapsH L (Handler.substFrom k u h)
def bumpL (L : List (Nat × Val)) : List (Nat × Val) := L.map (fun p => (p.1 + 1, Val.shift p.2))

/-- `applyCaps` of a snoc = one outer `substFrom` over `applyCaps` of the prefix (last element applied
LAST / outermost). The handle arm of `reshape_focus` produces exactly this snoc. -/
theorem applyCaps_snoc (L : List (Nat × Val)) (k : Nat) (v : Val) (c : Comp) :
    applyCaps (L ++ [(k, v)]) c = Comp.substFrom k v (applyCaps L c) := by
  induction L generalizing c with
  | nil => rfl
  | cons p L ih => obtain ⟨k', v'⟩ := p; simp only [applyCaps, List.cons_append, ih]

/-- `applyCaps` distributes through `letC` — into the first hole (level unchanged) and the binder
(level bumped). -/
theorem applyCaps_letC (L : List (Nat × Val)) (a b : Comp) :
    applyCaps L (.letC a b) = .letC (applyCaps L a) (applyCaps (bumpL L) b) := by
  induction L generalizing a b with
  | nil => rfl
  | cons p L ih => obtain ⟨k, v⟩ := p; simp only [applyCaps, Comp.substFrom, bumpL, List.map_cons, ih]
/-- `applyCaps` distributes through `app` — into the function hole (Comp) and the argument (Val). -/
theorem applyCaps_app (L : List (Nat × Val)) (a : Comp) (v : Val) :
    applyCaps L (.app a v) = .app (applyCaps L a) (applyCapsV L v) := by
  induction L generalizing a v with
  | nil => rfl
  | cons p L ih => obtain ⟨k, u⟩ := p; simp only [applyCaps, applyCapsV, Comp.substFrom, ih]
/-- `applyCaps` distributes through `handle` — into the handler (no binder) and the body (binder bumped). -/
theorem applyCaps_handle (L : List (Nat × Val)) (hd : Handler) (a : Comp) :
    applyCaps L (.handle hd a) = .handle (applyCapsH L hd) (applyCaps (bumpL L) a) := by
  induction L generalizing hd a with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨k, u⟩ := p; simp only [applyCaps, applyCapsH, Comp.substFrom, bumpL, List.map_cons, ih]

/-- **Focus characterization**: `reshape`'s focus is `applyCaps L c` for some `L`. This is the ONLY fact
the run-equation needs about the focus — it pins the head constructor (each `substFrom` preserves it), so
the next frame's `Source.step` fires. -/
theorem reshape_focus (C : EvalCtx) : ∀ (g : Nat) (K : EvalCtx) (c : Comp),
    ∃ L, (reshape g K C c).2.2 = applyCaps L c := by
  induction C with
  | nil => intro g K c; exact ⟨[], rfl⟩
  | cons fr C' ih =>
    intro g K c
    rw [reshape_cons]
    obtain ⟨L, hL⟩ := ih g K (fr.wrapStep c)
    cases fr with
    | letF N =>
      -- focus = applyCaps L (letC c N) = letC (applyCaps L c) _ ; stepReshape peels to applyCaps L c.
      refine ⟨L, ?_⟩
      rw [stepReshape_letC _ (applyCaps L c) (applyCaps (bumpL L) N) (by rw [hL]; exact applyCaps_letC L c N)]
    | appF v =>
      refine ⟨L, ?_⟩
      rw [stepReshape_app _ (applyCaps L c) (applyCapsV L v) (by rw [hL]; exact applyCaps_app L c v)]
    | handleF m h =>
      -- focus = applyCaps L (handle h c) = handle _ (applyCaps (bumpL L) c); stepReshape substitutes the
      -- minted cap, giving applyCaps (bumpL L ++ [(0, vcap g'' label)]) c.
      refine ⟨bumpL L ++ [(0, .vcap (reshape g K C' (Comp.handle h c)).1 (applyCapsH L h).label)], ?_⟩
      rw [stepReshape_handle _ (applyCapsH L h) (applyCaps (bumpL L) c)
            (by rw [hL]; exact applyCaps_handle L h c)]
      simp only [Frame.wrapStep] at hL ⊢
      rw [applyCaps_snoc]

/-- A `reshape … (fr.wrapStep c)` config's focus head is `fr`'s constructor (`letC`/`app`/`handle`), so
`Source.step` fires and equals `stepReshape`. This is the single transition the run-equation consumes. -/
theorem reshape_step_fires (g : Nat) (K : EvalCtx) (C : EvalCtx) (fr : Frame) (c : Comp) :
    Source.step (reshape g K C (fr.wrapStep c))
      = some (stepReshape (reshape g K C (fr.wrapStep c))) := by
  obtain ⟨L, hL⟩ := reshape_focus C g K (fr.wrapStep c)
  cases fr with
  | letF N =>
      refine step_fires_letC _ (applyCaps L c) (applyCaps (bumpL L) N) ?_
      rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_letC L c N
  | appF v =>
      refine step_fires_app _ (applyCaps L c) (applyCapsV L v) ?_
      rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_app L c v
  | handleF m h =>
      refine step_fires_handle _ (applyCapsH L h) (applyCaps (bumpL L) c) ?_
      rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_handle L h c

/-- The focus is never a `ret` (it is `fr`'s constructor), so a `reshape … (fr.wrapStep c)` config is
never the terminal returning config — the side condition `Config.run_step` needs. -/
theorem reshape_wrapStep_ne_ret (g : Nat) (K : EvalCtx) (C : EvalCtx) (fr : Frame) (c : Comp) :
    ∀ (g' : Nat) (v : Val), reshape g K C (fr.wrapStep c) ≠ (g', [], .ret v) := by
  intro g' v h
  obtain ⟨L, hL⟩ := reshape_focus C g K (fr.wrapStep c)
  have h2 : (reshape g K C (fr.wrapStep c)).2.2 = Comp.ret v := by rw [h]
  rw [hL] at h2
  cases fr with
  | letF N => rw [show Frame.wrapStep (Frame.letF N) c = Comp.letC c N from rfl, applyCaps_letC] at h2;
              exact absurd h2 (by simp)
  | appF w => rw [show Frame.wrapStep (Frame.appF w) c = Comp.app c w from rfl, applyCaps_app] at h2;
              exact absurd h2 (by simp)
  | handleF m hd => rw [show Frame.wrapStep (Frame.handleF m hd) c = Comp.handle hd c from rfl,
                      applyCaps_handle] at h2; exact absurd h2 (by simp)

/-! ## 4. The counter projection — `reshape` advances the counter by `handlerCount C`.

Each handle frame mints one fresh id (counter `+1`); `letF`/`appF` leave it. So the reached counter is
`g + handlerCount C`, hence at the fresh start `g = 0` it is exactly `handlerCount C`. -/
theorem reshape_counter (C : EvalCtx) : ∀ (g : Nat) (K : EvalCtx) (c : Comp),
    (reshape g K C c).1 = g + handlerCount C := by
  induction C with
  | nil => intro g K c; simp [handlerCount]
  | cons fr C' ih =>
    intro g K c
    rw [reshape_cons]
    obtain ⟨L, hL⟩ := reshape_focus C' g K (fr.wrapStep c)
    have hcnt : (reshape g K C' (fr.wrapStep c)).1 = g + handlerCount C' := ih g K (fr.wrapStep c)
    cases fr with
    | letF N =>
      rw [stepReshape_letC _ (applyCaps L c) (applyCaps (bumpL L) N)
            (by rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_letC L c N)]
      simpa only [handlerCount] using hcnt
    | appF v =>
      rw [stepReshape_app _ (applyCaps L c) (applyCapsV L v)
            (by rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_app L c v)]
      simpa only [handlerCount] using hcnt
    | handleF m h =>
      rw [stepReshape_handle _ (applyCapsH L h) (applyCaps (bumpL L) c)
            (by rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_handle L h c)]
      simp only [handlerCount]; omega

/-! ## 5. THE MAIN LEMMA — `run_plug_reshape`.

Running `plug C c` from the fresh machine `(0, [], ·)` reaches the canonical-relabeled, cap-substituted
config `reshape 0 [] C c`. Proved by induction on `C` (innermost-first), generalized over the starting
counter `g`, stack `K`, and fuel `n`: each frame of `C` is one machine step (`reshape_step_fires`), and
the outer frames `C'` of `plug (fr :: C') c = plug C' (fr.wrapStep c)` are consumed first by the IH. -/
theorem run_reshape_gen : ∀ (C : EvalCtx) (n g : Nat) (K : EvalCtx) (c : Comp),
    Config.run (n + C.length) (g, K, plug C c) = Config.run n (reshape g K C c) := by
  intro C
  induction C with
  | nil => intro n g K c; simp [plug]
  | cons fr C' ih =>
    intro n g K c
    rw [plug_cons, show (fr :: C').length = C'.length + 1 from rfl,
        show n + (C'.length + 1) = (n + 1) + C'.length by omega,
        ih (n + 1) g K (fr.wrapStep c), reshape_cons,
        Config.run_step n _ (reshape_wrapStep_ne_ret g K C' fr c),
        reshape_step_fires g K C' fr c]

/-- `canonStack`/`capSubstInto` — the stack and focus of the canonical reached config. `c` is threaded
through both; the STACK is in fact `c`-independent (the focus is a sibling of every handler stored on the
stack), so the inc-5 LR may read `canonStack C := canonStack C anyDummy`. -/
def canonStack (C : EvalCtx) (c : Comp) : EvalCtx := (reshape 0 [] C c).2.1
def capSubstInto (C : EvalCtx) (c : Comp) : Comp := (reshape 0 [] C c).2.2

/-- **`run_plug_reshape`** (the contract). Running `plug C c` for `C.length + n` steps from the fresh
machine equals running the canonical reached config for `n` steps. -/
theorem run_plug_reshape (n : Nat) (C : EvalCtx) (c : Comp) :
    Config.run (n + C.length) (0, [], plug C c)
      = Config.run n (handlerCount C, canonStack C c, capSubstInto C c) := by
  rw [run_reshape_gen C n 0 [] c]
  have hc : (reshape 0 [] C c).1 = handlerCount C := by
    have := reshape_counter C 0 [] c; simpa using this
  show Config.run n (reshape 0 [] C c)
      = Config.run n (handlerCount C, canonStack C c, capSubstInto C c)
  unfold canonStack capSubstInto
  rw [← hc]

/-! ## 6. THE BRIDGE — id-agnosticism, for the inc-5 LR's `KrelS`.

`run_plug_reshape` reaches the CANONICAL-id config. The LR must connect this to `C`'s ORIGINAL ids. The
resolution (from `RenameInvarianceProbe §2/§4`): **`plug`/`reshape` ERASE handler-frame ids** — `wrapStep
(handleF _ h) = handle h ·` drops the id, and the machine re-mints canonical ids. So the canonical config
is the ONLY id-meaningful config the machine produces; `C`'s original ids never reach `plug C c`. Two
green primitives package this for `KrelS`:

  · `reshape_reId` / `plug_reId` — the reached config (and `plug C c` itself) is INVARIANT under any
    relabeling of `C`'s frame ids. So `KrelS` may take `C`'s ids to be canonical WLOG; there is no
    distinct "original-id config" to run — only a choice of representative.
  · `splitAtId_rename` — DISPATCH commutes with an injective id-renaming, so `KrelS`'s step-matching
    survives the canonical↔original relabeling at every later `perform`.

The remaining wiring (that `KrelS` itself is id-agnostic on the stack — `HasStack`-id-irrelevance) is a
property of the LR relation, which lives in `Bang/LR.lean`. This file supplies the operational inputs;
the IC closes the relational step. -/

/-- Relabel ONLY a handler frame's id (handlers/sub-terms fixed). `RenameInvarianceProbe §2`. -/
def reId (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF N
  | .appF v      => .appF v
  | .handleF n h => .handleF (σ n) h

/-- **`plug` ignores handler-frame ids** (`RenameInvarianceProbe §2`, re-derived on this base): the
reconstructed term `plug C c` does not depend on `C`'s ids — `wrapStep` discards them. -/
theorem plug_reId (σ : Nat → Nat) (c : Comp) :
    ∀ K : EvalCtx, plug (K.map (reId σ)) c = plug K c := by
  intro K
  induction K generalizing c with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp only [List.map_cons, reId, plug, ih]

/-- **`reshape` ignores handler-frame ids** (the bridge keystone): the canonical reached config — hence
`canonStack`/`capSubstInto` — is INVARIANT under any relabeling `reId σ` of `C`'s frames. `reshape`
re-mints from the counter and discards `C`'s ids exactly as `plug` does. So `KrelS` may canonicalize `C`'s
ids for free. -/
theorem reshape_reId (σ : Nat → Nat) (C : EvalCtx) : ∀ (g : Nat) (K : EvalCtx) (c : Comp),
    reshape g K (C.map (reId σ)) c = reshape g K C c := by
  induction C with
  | nil => intro g K c; rfl
  | cons fr C' ih =>
    intro g K c
    simp only [List.map_cons, reshape_cons]
    rw [show (reId σ fr).wrapStep c = fr.wrapStep c from by cases fr <;> rfl, ih]

/-! ### Renaming over the term language (`RenameInvarianceProbe §1/§3`, re-derived) — for `splitAtId_rename`. -/

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

def renameF (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF (renameC σ N)
  | .appF v      => .appF (renameV σ v)
  | .handleF n h => .handleF (σ n) (renameH σ h)

def renameK (σ : Nat → Nat) : EvalCtx → EvalCtx := List.map (renameF σ)

@[simp] theorem renameK_cons (σ : Nat → Nat) (fr : Frame) (K : EvalCtx) :
    renameK σ (fr :: K) = renameF σ fr :: renameK σ K := rfl

/-- **DISPATCH commutes with an injective id-renaming** (`RenameInvarianceProbe §3`, re-derived): the
identity search `splitAtId` is stable under `renameK σ` for injective `σ`. The inc-5 LR uses this to keep
`KrelS`'s step-matching across the canonical↔original relabeling. -/
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

/-- **The bridge corollary the IC consumes.** Running `plug C c` (for ANY id-relabeling of `C`) reaches
the SAME canonical config. Combined with `KrelS`'s `HasStack`-id-agnosticism (LR-side), this is the
`run_plug` adequacy step: the LR may read off `(handlerCount C, canonStack C c, capSubstInto C c)` as the
machine image of `plug C c`, with `C`'s original ids irrelevant. -/
theorem run_plug_reId (n : Nat) (σ : Nat → Nat) (C : EvalCtx) (c : Comp) :
    Config.run (n + C.length) (0, [], plug (C.map (reId σ)) c)
      = Config.run n (handlerCount C, canonStack C c, capSubstInto C c) := by
  rw [plug_reId σ c C, run_plug_reshape n C c]

end Bang.RunPlugReshape
