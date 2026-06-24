# 0041 — ◊4.5: the LR's recursive fragment requires a `▷` (later) modality

- **Status:** Accepted (build-proven + literature-confirmed, 2026-06-24)
- **Layer:** C+ (LR metatheory / proof architecture)
- **Depends on / amends:** [0039](0039-cap4-non-triangleright-split.md) (the ◊4/◊4.5 split), [0035](0035-lr-for-equivalence-simulation-for-compilation.md) (LR vs compiler), [0033/0034/0036/0038] (the LR formulation)
- **Amended (2026-06-24, `560ba82`):** the chosen path below names "the `▷`-modality" and rejects alt-1 "step-bounded observation" as build-exploded. **Both are now refined by the build.** ◊4.5b's design pass found that for our *biorthogonal* LR the `▷` **must live in the observation** — so the "▷-modality" and "step-bounded observation" are the **same mechanism**, not alternatives. And alt-1's *explosion was a factoring artifact*, not fundamental: `lr45` metered **eval-fuel**, so the plug-refocus `+K.length` offset fought the bound at every site; metering at the **CONFIG level** (the relations observe the *focused* `(K,c)`, never `plug K c`) makes a head-step a clean `±1` via one `convergesC_le_step` lemma, confining the offset to the single adequacy bridge. The central `▷`-guarded head-expansion lemma **CLOSES** (`560ba82`). So the **CHOSEN mechanism is the config-level metered-observation `▷`** (`ConvergesC_le n cfg := ∃ v, Config.run n cfg = done v`; `Crel 0` vacuated via the observation premise `run 0 = oom`, leaving `Krel_mono` intact). Full rewire of the real `Crel`/`Krel`/`Srel` in progress.

- **Amended (2026-06-24, design pass — handled-`up`, ◊4.5b's last open case):** the ▷-rework closed μ + handler-CONSUMER cases + `krel_refl` (`6cf75fb`, banked); the one remaining sorry is the handled-op-PRODUCER (`up` observed by a stack that HANDLES it). Build-grounded findings: (1) the earlier "row-discipline as an added invariant" is FALSE — `krel_handleF` (Compat:1088) outputs `Krel` at the BODY effect `e ∋ ℓ` with a handler installed, so `splitAt = some` (the body-vantage row INCLUDES ℓ; "handler discharges ℓ" is the tunnel-OUT vantage). (2) The Biernacki-exact fix (POPL'18 §3.3, Lemmas 4/5/7) is **row-discipline as a DERIVED property**: DROP the baked `splitAt=none` from the `Srel` clause so the `Krel` stuck-half EXCLUDES handling stacks (a handling stack can't relate ℓ-raising terms as stuck) ⇒ `Krel n C ε K → ρ-free(K) for ℓ ≤ ε` is derivable ⇒ handled-`up`'s some-half is vacuous ⇒ `up` closes via the none-half (= Biernacki's `ρ-free`-only compat-op). The handled-dispatch work MOVES into re-proving the 3 handler CONSUMER cases at the DISCHARGED row (Lemma-4 cond-4) — re-opening them is expected and CORRECT (the handled-dispatch belongs in the handler, not the producer). **NO frozen-statement change** (the `Crel ∀K` restriction was assessed and ruled UNNECESSARY + dominated — the handling stacks stay quantified but vacuous since they're not in `Krel` at that row). WF via the same ▷-drop as the metered `Crel_head_step`. The build is a bounded structural `Srel`/`Krel`-stuck reshape + 3-handler re-proof — queued as a fresh focused effort.

- **Amended (2026-06-24, ◊4.5b handled-`up` RESOLVED to a core re-architecture — operator chose REBUILD over seam):** the design-pass plan above (DROP baked `splitAt=none`, row-discipline-as-derived) was **build-REFUTED** (polarity-inverted: dropping the conjunct *enlarges* `Srel`, which sits in `Krel`'s stuck-half as a premise — negative position — so it makes `Krel` HARDER, re-creating the resume obligation inside `krel_handleF`, not vacating it). ~25 build-arbitrated probes mapped the full solution space; every cheap save is build-dead (route-1 induction-on-K₁ walls because `Krel` doesn't decompose; `Krel→CrelCtx` equivalence walls on the same append; strengthened-IH-alone leaves the bare-`up` open core). **ROOT CAUSE (the real find):** our `Krel`'s flat-`CoApprox` observation was a **non-standard choice that ERASED Biernacki's answer type**. Biernacki's continuation relation is `K⟦τ/ε⟧` / the partial-context `C⟦τ₁/ε₁{τ₂/ε₂⟧` — **answer-typed**; the producer-`up` resume is exactly where the erasure bites (it needs `Krel→Crel(plug-ret)` = biorthogonal *composition*, which a focus-typed relation can't do). **THE FIX (build-verified feasible):** re-architect the core LR to the standard biorthogonal form — `Crel` observes via an **answer-typed `KrelS`/`CrelCtx`** stack relation (`CrelCtx n C D ε K₁ K₂ := ∀ c₁ c₂, Crel n C ε c₁ c₂ → Crel n D ε (plug K₁ c₁) (plug K₂ c₂)`, the `Crel⊸Crel` arrow). Composition (Biernacki **Lemma 2**) is then FREE (function composition + `plug_append`), the producer-resume closes in one line, and adequacy holds (identity stack → whole-program observation). **TERMINATION (the feasibility gate — CLOSES, build-confirmed):** the naive *type-driven* mutual def fails Lean termination (type grows under `plug`), but the **stack-structural** form — `KrelS` recurses on the EVAL-CONTEXT structure (frames peel, Biernacki induction-on-context), the answer-type threaded as an INERT parameter — is **well-founded by the STACK decrease ALONE** (measure role + stackLen; the index is NOT in the WF measure), Lean-accepted across `letF`/`appF`/the resumptive `handleF`. The frame-body `Crel` index (`n` vs `m<n`/`▷`) is a **SEPARABLE SEMANTIC choice** driven by proof-need (`Crel_head_step`/`krel_refl`/Kripke IHs), NOT a WF necessity — Lean accepts same-index too; the `▷` if used is the EXISTING metered-`▷`, not a new modality. **NO Iris-`▷`** (build ∥ literature agree: Biernacki §3.2 l.711-714 index-guarding; the Iris-forcing line is higher-order store + concurrency per blaze POPL'26, axes v1 is clear of — ADR-0030 single-threaded, STM-as-handler, one-shot resume). **SOUNDNESS TRAP:** `crelctx_compose` must carry the blaze §2.3 anti-handler side-condition (`0-free`/`n-free` / traversable) where composition crosses a handler for a threaded effect — baked into the lemma hypothesis, not bolted on. **FROZEN SURFACE: 2a SAFE** — `Crel`'s signature is byte-identical (answer-type `D` is internal to `KrelS`); `lr_sound`/`lr_fundamental` (Spec:174/192) reference only `Crel`/`Vrel`/`EnvRel` → **NO frozen-statement change.** Banked scratch infra (CrelCtx, `crelctx_compose`/Lemma-2, `plug_append`, `crel_fund_ctx` grounding, producer-resume one-liner) is the rebuild's starting point. **Scope:** STEP 2 is the multi-day, multi-SESSION re-prove of ALL of `Compat.lean` at the new mutual relation — laborious, no remaining conceptual unknown. The executable plan (sub-blocks a–g, def shape, gate) is in **`paths/PATH-cap45-rebuild.md`**. **Rejected alternative: ADR-0026 SEAM** (keep the single `up` sorry as the explicit verified/tested boundary, resumptive-handler equivalence tested-not-proven for v1) — viable + honest, but the operator chose the full verification (the moat: contextual equivalence for the full language incl. resumptive handlers; STM is one of the five kernel primitives).

## Context

◊4.5 closes the deferred `▷`-subsystem of the step-indexed biorthogonal logical relation
(μ recursion · `up` · resumptive state/transaction handlers). The non-▷ spine re-green
(`4b2f973`), the `Crel_mono` ▷-anti-reduction primitive + μ intro/elim (`b5cfc88`), the
resume infra (`421edc0`), and the corrected `▷`-guarded `Vrel` μ-clause (`33f50ea`) are all
banked and verified. The remaining μ-elim case at **index 0** (`unfold` of a `vvar`-bound μ
value) hit an **irreducible** wall.

## Decision

**The recursive fragment of the LR cannot be closed under plain-Nat `(n, sizeOf)` step-indexing.
It requires a genuine `▷` (later / guarded-recursion) modality.** This is build-PROVEN and
literature-CONFIRMED — two independent witnesses.

### The build proof (this session)
For `Crel 0 (F (unrollMu A))` to be dischargeable at the μ-floor it must be **vacuous**, i.e.
`Krel 0 (F (unrollMu A))` must be **uninhabited**. But the μ-anti-reduction (`crel_unfold` +
`Crel_mono`) that closes the n≥1 cases is built on **`Krel_mono : m ≤ n → Krel n → Krel m`**.
At `m=0, n=1`: `Krel 1 (F ..)` IS inhabited (`[]`, via `krel_nil_succ`), so monotonicity
FORCES `Krel 0 (F ..)` inhabited. **Uninhabited ∧ monotone-image-of-inhabited = contradiction.**
No scoping escapes it; degenerating any one index merely **relocates** the wall (n=0 → n=1 → …).
`Srel 0 := False` worked only because `Srel` is pure-premise; `Krel_mono` is load-bearing, so
`Krel` cannot be both downward-monotone (needed for μ) and floor-vacuous (needed for the
observation). That gap is exactly what a guarded `▷` expresses and plain `(n, sizeOf)` cannot.

### The literature (on-disk survey, 6 papers)
The root cause: **our observation `CoApprox = ∃ fuel, Converges` is fuel-UNBOUNDED**; the index
guards the value-relation recursion but does not meter the observation, so `Crel 0` carries the
full obligation. The survey is uniform:
- **Every** LR that handles iso-recursive types uses **step-bounded observation** (Ahmed ESOP'06;
  Pitts, *Step-Indexed Biorthogonality*, Remark 4.4 "the step-bound is syntactically essential")
  **or an explicit `▷`-modality** (Biernacki POPL'18; van Rooij–Krebbers POPL'25 *Affect*, via Iris).
- The **only** fully-biorthogonal *unbounded*-observation LR (Benton–Hur ICFP'09) has **no
  recursion**. Unbounded biorthogonal observation + μ is a vicious cycle — **there is no third way.**
- **We deviated from our own template.** Biernacki POPL'18 — the paper our LR is built on —
  guards recursion with the `▷` modality (`▷A` valid-at-0 ⇒ floor safe). We adopted Biernacki's
  biorthogonal structure but swapped in an unbounded `CoApprox` and *dropped the `▷`*. The μ wall
  is precisely the wall that `▷` exists to prevent. **Re-adding it is realigning with Biernacki**,
  not inventing something new.

## Chosen path: `▷`-realignment, in parallel with ◊5

Re-derive `Crel`/`Krel`/`Srel` over a guarded-recursion `▷` modality (LSLR / IxFree / Iris-style,
Löb induction). The `▷` is **internal to the proof**, so the frozen `lr_sound`/`lr_fundamental`
statements are **preserved**. Pursued **in parallel with ◊5** (the WasmFX compiler): ◊5's backend
target (`iris-wasmfx`) lives in the Iris `▷` world, so the modality is shared infrastructure and
the two efforts co-design.

Meanwhile the banked result is **honest**: `33f50ea`'s μ-clause fix makes `lr_fundamental`
**true-but-incomplete** (no longer false-as-stated for open μ-terms), with the n=0/μ-floor as a
documented open that **soundness never reaches** (`lr_sound_closed` consumes only index 1 — GREEN).

## Rejected alternatives (all build-arbitrated this session)

1. **Step-bounded observation** (`CoApprox_j` / "Route 2", the Ahmed move) — sound but **build-EXPLODED**: pervasive per-lemma fuel bookkeeping at the anti-reduction layer (`Crel_head_step` + 6 frame bridges, 16 sites). The literature itself calls this "tedious, error-prone" (LSLR's motivation).
2. **Typed `EnvRel`** (Ahmed's `RG⟦Γ⟧`) — gives each payload's *type* (canonical forms) but **not the cross-payload relation** the floor needs; ke traced it to the bottom. Also forces a frozen-statement change for no power at the wall.
3. **`Vrel` μ-floor down-closure + `Krel 0` degeneracy** ("Route 1 step ii") — **provably** destroys `Krel_mono` (see the build proof). Step (i) — the `▷`-guarded strict-`<` μ-clause — was kept (it's correct and banked); only step (ii) is impossible.
4. **Defer entirely per ADR-0039** — viable, but the `▷`-realignment is the *principled* fix and co-designs with ◊5, so the operator chose to pursue it rather than only defer.

## Consequences

- The LR gains a `▷` modality; this closes μ and (per the same `▷`-anti-reduction) likely the
  `up`/resumptive-handler cases. The resume **infra** (`krel_handleF*`, `421edc0`) is already
  built and `EnvRel`-independent, so the handler *cases* should be light once the `▷` lands.
- Frozen `Spec.lean` statements unchanged.
- Until the `▷`-rework lands, ◊4.5 carries 5 documented `▷`-fragment sorrys (μ-floor, `up`,
  handleState, handleTransaction, `krel_refl`); `lr_sound`/`lr_fundamental` carry `sorryAx` from
  exactly these; ◊2 (`no_accidental_handling`) 0-axiom and ◊3 (`compile_correct`) trusted-three intact.

## Revisit if

- The `▷`-rework reveals the resume cases need more than the `▷`-anti-reduction (then a localized
  refinement, not a statement change).
- A future formulation finds a sound *bounded-observation* form that doesn't explode (would
  reopen alternative 1) — unlikely given the literature.
