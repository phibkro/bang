# PATH — ◊4.5b LR core re-architecture (KrelS rebuild)

**Status:** STEP 1 (termination feasibility) GREEN, build-confirmed. STEP 2 (the rebuild)
queued for a fresh proof-engineer IC. Base: `cap45-modality` @ `c363304` (pristine, green,
1 sorry = handled-`up`). Decision + rationale: **ADR-0041** (last amendment). This doc is
the *executable* plan; the ADR is the *why*.

> Discovery is DONE (~25 build-arbitrated probes). STEP 2 is laborious re-proof, no remaining
> conceptual unknown. The feasibility-gating question (does a WF metric exist) is RESOLVED YES.

## The move (one sentence)

Replace the LR's non-standard flat-`CoApprox` `Krel` (which erased the answer type) with the
**standard biorthogonal answer-typed stack relation** `KrelS`, so the producer-`up` resume
closes by composition (Biernacki Lemma 2). `Crel`/`KrelS` become mutually defined.

## The definitions (build-verified shapes)

```
CrelCtx n C D ε K₁ K₂  :=  ∀ c₁ c₂, Crel n C ε c₁ c₂ → Crel n D ε (plug K₁ c₁) (plug K₂ c₂)
       -- the Crel⊸Crel arrow; answer type D internal; this is what COMPOSES (Lemma 2)
Crel  n C ε c₁ c₂      :=  ∀ D K₁ K₂, KrelS n C D ε K₁ K₂ → CoApproxC_le n (K₁,c₁) (K₂,c₂)
KrelS n C D ε K₁ K₂    :=  the answer-typed stack relation, defined STACK-STRUCTURALLY
                           (recurses on eval-context structure, frame-body Crel calls ▷-guarded m<n)
```

- **Frozen surface (2a, HOLD):** `Crel`'s signature stays byte-identical — `D` is internal to
  `KrelS`. `lr_sound`/`lr_fundamental` (Spec:174/192) are over `Crel`/`Vrel`/`EnvRel` → untouched.
  **If anything forces `D` into `Crel`'s signature, STOP and escalate** (that would be a
  frozen-statement change).

## Termination metric (the feasibility gate — GREEN, full 3-way block)

The REAL block is **3-way**: `Vrel`/`Crel`/`KrelS` are mutually recursive (`Vrel`'s U-clause
references `Crel`; `KrelS`'s nil/appF caps reference `Vrel`). Build-verified WF metric (Lean
accepts the full block):

**Lex `(n, role, stackLen, sizeOf)`**, roles `Vrel=0 < KrelS=1 < Crel=2`:
- `Vrel n` (U-clause) → `Crel j` at **strict `j < n`** (the ▷-guarded thunk): `n` drops. **The
  thunk guard MUST be `∀ j<n`, not `∀ j≤n`** — `≤` FAILS termination at this edge (build-confirmed
  both ways); `<` is Biernacki's standard guarded-thunk and is exactly what the sole consumer
  `crel_force` needs (`m<n`). This is the `STATEMENT_CHANGE_OK="◊4.5 Vrel U-clause ∀j≤n"` (LR:439)
  refinement — in-envelope, NO frozen-statement change (`Spec.lean` never references the U-clause body).
- `Crel n` (role 2) → `KrelS n` (role 1) → `Vrel n` (cap, role 0): role drops at same `n`.
- `KrelS n (fr::K)` → `KrelS n K`: `stackLen` drops (frames peel — Biernacki induction-on-context).
- `Vrel`-internal sum/prod edges: `sizeOf` (the 4th tiebreaker).
- answer-type `D` is INERT (threaded parameter, NOT a recursion driver). **DEAD-END (Lean-rejects):**
  recursing through `plug` (`CrelCtx n C D → Crel n D (plug K c)` wraps `c` into a LARGER term at
  the same index) — do NOT use the type-driven form.
- Verified across `letF`/`appF`/the resumptive `handleF`.

**TWO DISTINCT EDGES — do not conflate** (both build-confirmed):
- the **Vrel-U-clause → Crel thunk guard** is `∀ j<n` — **REQUIRED**, strict (this is the `n`-drop).
- the **letF frame-body `Crel` index** (`n` vs `m<n`) is a **SEPARATE FREE choice** — carried by
  `stackLen`, not `n`; pick per proof-need (likely `m<n` at the Kripke μ/resume seams to match the
  existing `Crel_head_step` ▷-anti-reduction). The `▷` here is the EXISTING metered-`▷`, no new
  modality, no Iris.

## Banked infra (scratch-proven; re-establish in the real LR)

- `CrelCtx` abbreviation + `crelctx_compose` (Biernacki **Lemma 2**): closes via function
  composition + `plug_append` (3 lines). **Bake the anti-handler side-condition** (blaze §2.3
  `0-free`/`n-free`/traversable) into its hypothesis at the handler-crossing seam — composition
  crossing a handler for a threaded effect is UNSOUND without it.
- `crel_fund_ctx → crel_fund` grounding at `D=C, K=[]` (identity stack): closes.
- producer-resume given `CrelCtx`: one line (`hctx _ _ (crel_ret …)`).

## STEP 2 sub-blocks (dependency order — commit + gate each on `cap45-modality`)

**SEQUENCING: ADDITIVE-THEN-MIGRATE (required — the gate cannot pass mid-migration).** Removing
the old `Krel`/`Srel` reds **183 references** (LR:86, Compat:97, Spec:7) until ALL of Compat is
re-proven. So land the new `KrelS` + biorthogonal `Crel`-core + 4 eq lemmas + adequacy + 5 gates
**ALONGSIDE** the existing `Vrel`/`Crel`/`Krel`/`Srel`, under a **TEMP name** (e.g. `CrelK`/`KrelS`);
the frozen `Crel` stays wired to the OLD def until (g). Build stays GREEN at every sub-block.
(b)–(f) incrementally migrate Compat's lemmas onto `KrelS`; **(g) re-points the frozen `Crel`
(body swap, signature byte-identical) + deletes the old `Krel`/`Srel`.** Each sub-block commits green.

| | sub-block | risk |
|---|---|---|
| a | `Crel`/`KrelS` def sink (additive, temp name) + adequacy + 5 gates | the foundation; gate first |
| b | `Krel_mono` / `Krel_eff_anti` at `KrelS` | structural |
| c | `Vrel` U-clause + frame lemmas (`letF`/`appF`/`handleF`) at `KrelS` | the bulk |
| d | `krel_refl` | uses the stuck-half |
| e | `compat_*` (the congruence lemmas) | re-thread through `CrelCtx` |
| f | producer (`up`) + the 3 handler cases | the payoff — composition closes them |
| g | final audit: `lr_sound`/`lr_fundamental` → trusted-three | the gate |

**Gate each sub-block:** `nix develop --command lake build` + `lake env lean Bang/Audit.lean`.
Target at (g): `lr_sound`/`lr_fundamental` drop `sorryAx` → trusted-three {propext,
Classical.choice, Quot.sound}; `no_accidental_handling` stays 0-axiom; `compile_correct` stays
trusted-three. `c363304` is the labelled fallback throughout. Commit frequently — multi-session.

## STEP-2(a) build notes (from the discovery IC — port these, don't rediscover)

- **`KrelS` def shape: SINGLE-BODY with an internal `match K₁, K₂ with`**, NOT a multi-clause
  def. The multi-clause form (`[]`/`letF::`/catch-all as separate clauses) type-checks and
  terminates but FIGHTS the unfolder — `rw [KrelF]` / `simp only [KrelF]` make "no progress".
  The single-body + internal-match form unfolds cleanly. Generate `@[simp]` per-case equation
  lemmas explicitly (`krelF_nil`, `krelF_letF`, `krelF_appF`, `krelF_handleF`) so the downstream
  proofs (`KrelF_mono`, the frame lemmas) rewrite through them. This is a known Lean-4
  mutual-def mechanic, not a soundness issue.
- **WF decreases on STACK SYNTAX, answer-type INERT.** `KrelF n (fr::K) → KrelF n K` (frames
  peel) is the structural decrease; the answer-type `D` is threaded as a parameter, NOT in the
  measure. The DEAD-END (Lean-rejected): recursing "through `plug`" (`CrelCtx n C D → Crel n D
  (plug K c)`) — `plug` wraps `c` into a LARGER term at the same index, no syntactic decrease.
  Use the stack-structural (induction-on-context) form; it sidesteps plug-at-same-index.
- **The frame-body `Crel` index (`n` vs `m<n`) is a FREE SEMANTIC choice** — termination forces
  NEITHER (the stack peeling carries WF either way; Lean accepts both). Pick per PROOF-need:
  likely `m<n` (the `▷`) at the Kripke μ/resume seams to match the existing ◊4.5 ▷-anti-reduction
  (`Crel_head_step`), `n` elsewhere. This is cleaner than "▷ forced for WF" — it's not.
- **letF clause: the continuation row `φ` MUST be existentially bound, INDEPENDENT of the stack's
  ambient `ε`** (build-caught in sub-block b). Threading the stack's `ε` into the continuation body
  (`CrelK m B ε`) breaks ε-antitonicity — the body is ε-covariant but `CrelK` is ε-MONOTONE, a
  polarity clash. With `φ` independent, `ε` appears in NO `KrelS` clause body, so `KrelS_eff_anti`
  is a clean structural pass-through. This matches the OLD `krel_letF` separation (stack at `φ₁`,
  continuation at `φ₂`). Landed in `615dd2a`/`2ef83af`.
- **(ii) cascade is structurally sound (NOT research-grade):** `crelF_zero` (μ-floor) closes
  trivially (vacuous metered obs at 0); `crelF_head_step` reduces to `KrelF_mono`; `KrelF_mono`'s
  argument is valid (frame-body `∀m<n` restricts to `∀m<k`, k≤n subset, + recurse on the smaller
  stack). The "does the `▷`-insert break adequacy" fear is NOT realized — μ-floor + head_step
  survive structurally. The only STEP-2(a) work is the def-shape-for-unfolding above.

## Discipline (carried from the discovery phase)

- The build/source arbitrates every fork. Pin sub-claims as falsifiable; revise on the build.
- flag-before-build: check a prescribed lemma against the source BEFORE sinking effort.
- Self-report saturation at a clean checkpoint → hand off to a fresh IC via the committed branch.
- Frozen `Spec.lean` change → STOP + escalate to the orchestrator.
