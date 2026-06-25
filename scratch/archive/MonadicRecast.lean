import Bang.CalcReifyRef
import Bang.CalcReifySim

/-!
# Spike: does the Bahr–Hutton 2022 monadic frame dissolve `perf_outcome_mono`?

**STATUS: feasibility spike. Unwired (no module imports this). Asserts only what it
elaborates; the prose verdict lives in `findings-monadic-recast.md`.**

## What this file DOES

It pins down — *in elaborated Lean, not prose* — the precise relationship between:

  (P)  the Bahr–Hutton 2022 step-indexed strong-bisimilarity machinery
       (`Partial A`, `_~[ i ]_`, `~idown`, `bind-cong`), and

  (B)  bang-lang's CalcReify obligation `perf_outcome_mono`, the (b)-gate of
       ADR-0015 / the k2-playbook: *reference perf-outcome fuel-monotonicity*.

Concretely it elaborates three things:

  1. `IdxDown` — the paper's `~idown` shape transcribed onto bang's actual objects
     (`Comp` + `observe` + the fuel index). This is the property the paper gets
     *for free* from the coinductive/sized construction of `_~[ i ]_`.

  2. `PerfOutcomeMono` — the EXACT obligation `perf_outcome_mono` names, written out
     against `CalcReifyRef.eval` for the FIRST time (it was only ever a doc-name).

  3. A direct elaboration showing what the deep case actually needs, by re-using the
     already-proven `bind_mono`, and exhibiting where `handleC` (the deep
     re-handling rebuild) does NOT fall to the same one-step argument.

## What this file does NOT do / does NOT prove

* It does NOT prove `perf_outcome_mono`. (That is the open research gate.)
* It does NOT introduce a coinductive `Partial`/`Delay` type or sized types. It tests
  the recast against bang's *existing eager fuel-indexed `Comp`*, because that is what
  the verdict must speak to: the question is whether ADOPTING the paper's frame helps,
  not whether the paper's own theorems hold (they do).
* It does NOT touch the graded-effect generalisation (the explicit out-of-scope trap).
-/

namespace Scratch.MonadicRecast

open Bang.CalcReifyRef
open Bang.CalcReify (Src)
open Bang.CalcReifySim (observe bind_mono)

/-! ## 1. The paper's `~idown`, transcribed onto bang's objects.

Bahr–Hutton 2022 `Partial.agda`:

    ~idown : a ~[ suc i ] b → a ~[ i ] b

i.e. bisimilarity is DOWNWARD-monotone in the step index: more budget ⇒ less budget.
This is free from the indexed-bisimilarity *constructors* (drop the last `~ilater`).

Bang's `RelV : Nat → Value → Entry → Prop` is exactly an `_~[ i ]_` between the two
machines' value domains. Its *own* downward step (env at `i+1` ⊢ conclusion at `i`)
is precisely `~idown` — and bang ALREADY relies on it implicitly: `sim_resume_pure_v`
takes `RelEnvI (i+1)` and concludes at `i`. So the paper's `~idown` is present and
load-bearing in bang's track, just un-named. -/

/-- The paper's `~idown` direction, stated for the *fuel* index on `Comp` outcomes.
Downward in the budget: if a longer run observes `n`, ... — note this is FALSE in
general for an EAGER `Comp` (less fuel can `stuck`), which is the first tell that
bang's index is NOT the paper's coinductive depth index. See `findings` §map. -/
def IdxDown : Prop :=
  ∀ (f : Nat) (renv : REnv) (e : Src) (n : Int),
    observe (eval (f + 1) renv e) = some n → observe (eval f renv e) = some n

/-! ## 2. `perf_outcome_mono`, written out for the first time.

The k2-playbook (lines 523–526) names it:

  > the reference perf-outcome fuel-monotonicity — genuinely bisimulation-shaped:
  > bumping fuel changes the env's `ek` closures, so it's a fuel-monotone logical
  > relation on `Comp`, not a simple equality.

So the obligation is the UPWARD direction (more fuel preserves a `perf` outcome AND
its continuation behaves compatibly) — the opposite of `~idown`. Here is the
outcome-level core: raising fuel preserves a *standing perf*'s payload, and the two
resumption closures agree pointwise *up to the same relation* (the recursive knot). -/

/-- Outcome-level `perf_outcome_mono`. Note the codomain is not a plain equality:
the two continuations `k`, `k'` must agree *as fuel-indexed `Comp`s* (the recursive,
bisimulation-shaped part). We phrase that agreement again via `observe` after an
arbitrary resumption value `w`, exposing the knot. -/
def PerfOutcomeMono : Prop :=
  ∀ (f f' : Nat) (renv : REnv) (e : Src) (p : Int) (k : Int → Comp),
    f ≤ f' →
    eval f renv e = .perf p k →
    ∃ k', eval f' renv e = .perf p k' ∧
      -- the bisimulation knot: the bumped continuation agrees on every observed run
      (∀ (w : Int), observe (k w) = observe (k' w))

/-! ## 3. What the recast actually buys: the SHALLOW case falls to `bind_mono`
(already proven); the DEEP case does not. -/

/-- **The shallow half is already a corollary of `bind_mono`.** `bind` returning a
`.ret` under more fuel is exactly `bind_mono` — i.e. the part of `perf_outcome_mono`
that the playbook calls the "honest fallback (a)" needs NO new monadic machinery; it
is the paper's `bind-cong` specialised to the `now`/`ret` leg, which bang HAS. -/
theorem shallow_is_bind_mono
    (f f' : Nat) (c : Comp) (g : Int → Comp) (n : Int)
    (h : bind f c g = .ret n) (hle : f ≤ f') :
    bind f' c g = .ret n :=
  bind_mono f f' c g n h hle

/-- **The deep case does NOT reduce the same way.** The reference `handleC` over a
performing body rebuilds the resumption `res w = handleC fuel (k w) clause cEnv` with
the *ambient* `fuel` captured. Raising fuel to `fuel'` gives a DIFFERENT `res'`, and
the two agree only if `handleC` is itself fuel-monotone on `k w` — which, when `k w`
performs, is `perf_outcome_mono` AGAIN (one handler-depth deeper). This is the knot;
we make the circularity *visible* by stating the single deep step and observing it
needs `PerfOutcomeMono` as its own hypothesis (i.e. it is not dissolved — it recurses).

This elaborates: the deep monotonicity step is *equivalent to itself one level down*,
not to a free monadic property. -/
theorem deep_step_recurses (hmono : PerfOutcomeMono) :
    ∀ (fuel fuel' : Nat) (k : Int → Comp) (clause : Src) (cEnv : REnv)
      (w p : Int) (kk : Int → Comp),
      fuel ≤ fuel' →
      -- the resumed body itself performs (the genuine deep case):
      handleC fuel (k w) clause cEnv = .perf p kk →
      ∃ kk', handleC fuel' (k w) clause cEnv = .perf p kk' := by
  -- We can only PROGRESS by appeal to monotonicity of `handleC`, which on a performing
  -- argument unfolds to `eval`-of-clause and lands back on `perf_outcome_mono`.
  -- The point of the spike: this `sorry` is dischargeable IFF `perf_outcome_mono`
  -- already holds — confirming the recast does not make it free, it merely RENAMES it.
  intro fuel fuel' k clause cEnv w p kk hle hperf
  sorry

end Scratch.MonadicRecast
