# Feasibility spike: recasting CalcReify's bisimulation into the Bahr–Hutton 2022 monadic frame

**VERDICT: NO-GO** (against bang's *eager fuel* index — the cheap hypothesis).
The recast **renames, it does not dissolve**. `perf_outcome_mono` survives essentially
unchanged. A coinductive-substrate version is a *separate, larger* question (§5), parked.

Time-boxed spike. Two new untracked files only: this doc + `scratch/archive/MonadicRecast.lean`
(unwired → inert to `lake build`/`just check`; elaborates green modulo ONE deliberate `sorry`).
Nothing of teammate lrA's touched (Operational/LR/Compat/Spec untouched; `git status` = `?? scratch/` + this doc).

---

## 0. Build state (which the verdict rests on)

- The tree is RED **downstream** (CalcVM/Surface, pending the LR re-key) — but the
  **CalcReify track builds**: `CalcReifyRef.lean` + `CalcReifySim.lean` elaborate green
  and `sorry`-free (`just check Bang/CalcReifySim.lean` → only unused-simp warnings).
- `scratch/archive/MonadicRecast.lean` elaborates **against the real built dependencies** (not
  stubs). Only diagnostic: the single `sorry` at `deep_step_recurses` (line 132).
  `shallow_is_bind_mono` typechecks against the real `Bang.CalcReifySim.bind_mono` and is
  **axiom-clean** (`propext, Classical.choice, Quot.sound` — no `sorryAx`).
- So the verdict did NOT need the red downstream; it rests on green, elaborated evidence.

---

## 1. Corrected current state (Task 1 — checked against the repo, not the brief)

**`perf_outcome_mono` was NEVER a Lean statement.** It existed only as a *doc-name* in
three places: `docs/decisions/0015-…md:191`, `docs/notes/k2-calculation-playbook.md:523`,
and a comment at `Bang/CalcReifySim.lean:1358`. No `theorem`/`sorry`/`admit` carried that
name. It is a *named-but-unformalized future obligation* (the (b) research gate of
ADR-0015). This spike writes it out in Lean for the first time (`PerfOutcomeMono`,
`scratch/archive/MonadicRecast.lean`). **This corrects the brief's premise** ("find its EXACT
statement / open goal / admitted").

Two more brief corrections:
- It's the **CalcReify track (ADR-0015)**, not "K2/K3" (those are legacy pre-pivot
  machines). Live files: `Bang/CalcReify.lean` (machine `exec`), `Bang/CalcReifyRef.lean`
  (reference `eval`, a CBPV+free-monad interpreter), `Bang/CalcReifySim.lean` (`RelV`).
- The obligation **is** a monotonicity-in-index property — but in the **fuel** index,
  **UPWARD** (`f ≤ f' ⇒ outcome preserved`), the *opposite* of the paper's free `~idown`
  (downward), and with a **non-equality** codomain (a recursive bisimulation knot).

**The open gate (`perf_outcome_mono`), per playbook 523–526:** reference perf-outcome
fuel-monotonicity — "bumping fuel changes the env's `ek` closures, so it's a fuel-monotone
logical relation on `Comp`, not a simple equality." It bites only on a *performing resumed
continuation* (deep re-handling): `handleC fuel (k w) clause cEnv` captures the ambient
`fuel`; when `k w` itself performs, raising fuel changes that closure.

---

## 2. The CalcReify → BH-2022 mapping

From the 2022 Agda artifact (`pa-ba/monadic-compiler-calculation`, `Partial.agda`):
`Partial A i` is **coinductive/sized**; `_~[ i ]_` is step-indexed strong bisim; the free
lemmas are `~idown : a ~[ suc i ] b → a ~[ i ] b` (DOWNWARD, free from constructors) and
`bind-cong`. The correctness theorem (`LambdaException.agda`) is an indexed strong bisim
`eval x e >>= … ~[ i ] exec (comp x c) …`. **THE TRAP confirmed:** the paper uses a
**single monad**; effects are inline (exceptions = `Maybe Value` in return position,
handlers = stack markers), **no lattice/grading**. The graded generalization is genuinely
unbounded research — out of scope, not pursued.

| 2022 object | bang CalcReify object | fit |
|---|---|---|
| `Partial A` (free/partiality monad) | `Comp = ret \| perf Int (Int→Comp) \| stuck` | **clean** — same construction, arrived at independently |
| `>>=` | `CalcReifyRef.bind` | clean |
| `_~[ i ]_` (step-indexed strong bisim) | `RelV : Nat → Value → Entry → Prop` | **clean in shape** — both step-indexed value relations |
| coinductive/sized `later` depth | **fuel** (`Nat`, EAGER) | **LOSSY — the decisive seam** |
| `~idown` (downward-mono, **FREE**) | `RelV`'s `i+1 ⊢ i` index drop | present + load-bearing (`sim_resume_pure_v`), already used |
| `bind-cong` | `bind_mono` + `relKont_push*` | **clean** — bang HAS this; `shallow_is_bind_mono` proves the leg from `bind_mono` |
| (no analog) | **`perf_outcome_mono` / `PerfOutcomeMono`** | **BREAKS** |

**The key lossiness — eager fuel ≠ coinductive depth.** `IdxDown` (the paper's `~idown`
transcribed onto bang's `observe ∘ eval`) is *FALSE* for bang's eager `Comp`: less fuel can
`stuck` where more fuel returns. The paper never needs upward monotonicity because `Partial`
is coinductive — `later` is productive, fuel is not a resource you exhaust, there is no
"ran out ⇒ stuck" mode to monotone over. Bang's `Comp` is eager + fuel-exhausting
(`eval 0 _ _ = .stuck`), so raising fuel genuinely changes outcomes and you must *prove* it
doesn't change a real one. That proof IS `perf_outcome_mono`, and the coinductive frame
**defines it away rather than proves it.**

---

## 3. Verdict — dissolved / reduced / UNCHANGED → **NO-GO**

`perf_outcome_mono` is **unchanged** under the recast. Evidence, all *elaborated* in
`scratch/archive/MonadicRecast.lean` (not asserted):

- **Shallow half = already done.** `shallow_is_bind_mono` proves the `now`/`ret` leg of
  upward monotonicity is *literally* `bind_mono` (the paper's `bind-cong` specialised to
  the `ret` leg). Axiom-clean. So the (a) "honest-fallback" deliverable already has its
  monadic core and needs **no recast**.
- **Deep half = recursive knot, not a `bind-cong` instance.** `deep_step_recurses` takes
  `PerfOutcomeMono` as a *hypothesis* and the deep single step (a performing resumed body
  under `handleC`) lands back on it one handler-depth down — the circularity is made to
  elaborate. `bind-cong` congruences over a *given* bisimilarity; here the bisimilarity at
  depth `n` is exactly what you're trying to establish, so `bind-cong` cannot discharge it.

Root cause in one line: **the 2022 frame gets its key monotonicity (`~idown`) FREE from
coinduction; bang's fuel index is eager, so the corresponding obligation is the *opposite
direction*, must be EARNED, and the deep case is a genuine bisimulation knot the
single-monad paper never confronts.** Net buy on the one open gate: **zero**.

---

## 4. The Lean partiality-monad situation (requested)

- **No usable coinductive `Delay`/`Partial` in Mathlib.** Mathlib has `Part`/`PFun` —
  *propositional* partiality (`Part A ≅ Σ p, p → A`): no step index, no strong bisimilarity.
  It would NOT reproduce `_~[ i ]_`.
- A faithful port would mean **BUILDING**: a coinductive `Partial`/`Delay` (Lean 4
  coinduction via QPF/Codata or hand-rolled) + its sized/step-indexed strong bisimilarity
  + the `~idown`/`bind-cong` lemmas — substantial infra, none in-repo. **Prohibitive for the
  payoff** (which is zero on the gate). Independently meets the NO-GO criterion.
- bang's eager `Comp` + `Nat` fuel + `RelV` is the pragmatic realization of the same idea,
  `sorry`-free where proven. **Keep it.**

---

## 5. One-line rec on the 2021 typed style (Pickard & Hutton)

**Mild yes, ORTHOGONAL to the gate.** Intrinsically-typed/scoped style tidies the
*compiler-correctness statement* and fits bang's NamedCore typed surface — but does **not**
touch `perf_outcome_mono` (a *semantic* fuel-monotonicity, not a typing invariant). Adopt
later as ergonomics if the typed-LR re-key stabilizes; **not** as a route to the gate.

---

## 6. What would flip it to GO (parked, larger question)

Only if the source language gained **genuine divergence** (recursion/loops). Then the
coinductive `Partial` earns its keep: fuel exhaustion stops being a bookkeeping artifact and
becomes real non-termination the frame models natively; `~idown` + productivity replace the
fuel-monotonicity bookkeeping wholesale. bang's v1 fragment is **total** (skeleton-bounded
firing), so this does not apply now. If a future checkpoint pushes the Div fragment into
CalcReify, **re-open this spike** — the calculus changes and the monadic frame may then
dissolve the bookkeeping it currently can't.

---

## Files (both untracked, for manager review)
- `findings-monadic-recast.md` — this doc.
- `scratch/archive/MonadicRecast.lean` — the spike. Elaborates green except ONE deliberate `sorry`
  (`deep_step_recurses`, the visible circularity). `shallow_is_bind_mono` axiom-clean.
  Unwired (no module imports it).
