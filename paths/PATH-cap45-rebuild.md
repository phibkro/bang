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

## Termination metric (the feasibility gate — already GREEN)

Lex **`(n, role, stackLen)`** — build-verified Lean-accepts the mutual block:
- `Crel n C` (role 1) → `KrelS n C` (role 0): same `n`, role drops.
- `KrelS n (fr::K)` → `KrelS n K`: same `n`, same role, `stackLen` drops.
- `KrelS n` → `Crel m` (frame body, `m<n`, the `▷`): `n` drops — breaks the `Crel↔KrelS` 2-cycle.
- Verified for `letF`, `appF`, AND the resumptive `handleF`.
- **The recursion decreases on STACK SYNTAX, NOT the answer type** (type is inert). The
  type-driven form FAILS termination — do not use it. The `▷` is the EXISTING metered-`▷`
  (`Crel_head_step`), not a new modality. No Iris.

## Banked infra (scratch-proven; re-establish in the real LR)

- `CrelCtx` abbreviation + `crelctx_compose` (Biernacki **Lemma 2**): closes via function
  composition + `plug_append` (3 lines). **Bake the anti-handler side-condition** (blaze §2.3
  `0-free`/`n-free`/traversable) into its hypothesis at the handler-crossing seam — composition
  crossing a handler for a threaded effect is UNSOUND without it.
- `crel_fund_ctx → crel_fund` grounding at `D=C, K=[]` (identity stack): closes.
- producer-resume given `CrelCtx`: one line (`hctx _ _ (crel_ret …)`).

## STEP 2 sub-blocks (dependency order — commit + gate each on `cap45-modality`)

| | sub-block | risk |
|---|---|---|
| a | `Crel`/`KrelS` def sink + adequacy | the foundation; gate first |
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

## Discipline (carried from the discovery phase)

- The build/source arbitrates every fork. Pin sub-claims as falsifiable; revise on the build.
- flag-before-build: check a prescribed lemma against the source BEFORE sinking effort.
- Self-report saturation at a clean checkpoint → hand off to a fresh IC via the committed branch.
- Frozen `Spec.lean` change → STOP + escalate to the orchestrator.
