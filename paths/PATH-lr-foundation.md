# PATH · LR foundation (◊3 → ◊4)

> Build the step-indexed logical relation and prove the LR spine, so the calculated
> kernel inherits adequacy. Status: **IN PROGRESS** — the FOUNDATION (definitions + corrected
> spec) is landed axiom-clean; the PROOFS (U4/U5/U6) remain. Owner: kernel/proof-engineer.

## The ◊4 gate (ROADMAP)

`lr_sound`, `lr_fundamental`, `zero_usage_erasable` proven; `Audit.lean` axioms ⊆ {propext,
Classical.choice, Quot.sound} for these. `group_recovers` RETIRED (ADR-0032). `effect_sound`
(Q14 trace semantics) deferred → ◊5.

## Reframe (scope-d4-lr recon, 2026-06-23)

◊4 was **Phase-A-incomplete**: the whole LR was *axioms*, not stubbed defs — so the gate needs
the ~14 placeholder axioms turned into defs AND the theorems proven (an axiom-backed proof is a
fiction). The foundation work (U1–U3) discharged the axioms + corrected the spec; U4–U6 are the proofs.

## Staged units

| Unit | scope | status |
|---|---|---|
| **U1** | concretize §5.1/§6 helper axioms → defs (Cxt/Stack=EvalCtx, BaseRel, seqComp, raise…) | ✓ **DONE** `a58a396` (caught `raise` sig flaw: `Eff→` → `Label→`) |
| **U2** | define `Vrel`/`Srel`/`Krel`/`Crel` (step-indexed mutual WF) — **THE CRUX** | ✓ **DONE** `eadec83`. WF goes through on plain lex `(n, sizeOf type, role)` — no iris ▷. Caught the τ/ε under-spec → row-indexed (ADR-0033) |
| **U3** | `group_recovers` research spike (PROOF_ORDER #2, early) | ✓ **DONE** → RETIRED (`fcb2f51`, ADR-0032). `≈` cleared — no side-condition |
| **U4** | `seq_unit` + `NotEvaluated` def | ✓ **DONE (partial)** `53d2e1f`. `seq_unit` PROVEN axiom-clean (pure operational: autosubst β-identity `(shift c)[v]=c` + the `run_plug`/`converges_plug_iff` plug-run bridge — committed in LR.lean, reusable). `NotEvaluated` axiom→def (`∀ v₁ v₂, substFrom i v₁ c ≈ substFrom i v₂ c`). **`zero_usage` RE-SEQUENCED out** ↓ |
| **U5** | `lr_sound` — closed-fragment adequacy | ✓ **DONE (partial)** `f548999`. `lr_sound_closed` (Crel ⇒ Converges-preservation at the EMPTY context) + `krel_nil_succ`/`converges_ret`/`not_converges_up_nil` PROVEN axiom-clean (§5.3). **FINDING:** full `lr_sound` (⊑ over arbitrary `C`) is COUPLED to `lr_fundamental` — it needs `Krel`-reflexivity `Krel n B e C C` (context-congruence), which IS the compatibility direction (verified: the `letF`/`handleF` frame cases block on `N[v₁]~N[v₂]` from `Vrel v₁ v₂`). So PROOF_ORDER #1 groups them for real. `lr_sound` body stays `sorry` (dependency note in Spec.lean). Becomes a short capstone ↓ |
| **U6** | repopulate `Bang/Meta/BinaryLR.lean` (16 lemmas) → `lr_fundamental` by induction over `HasCTy` | ▶ **NEXT** — the real PROOF_ORDER #1 risk + unblocks lr_sound. Fresh proof-engineer (LR thread near budget; relations externalized in committed LR.lean). `compat_handle` LAST (consumes `Srel`) — the `[KEY]` one; SEQUENTIAL handoff to kernel-engineer if it needs depth, NOT concurrent pairing (one writer per file) |
| **U5′** | `lr_sound` capstone | pending U6. `lr_sound = lr_sound_closed ∘ (Krel-reflexivity, the identity instance of lr_fundamental)`. Short — → **LR thread** (owns §5.3 + the adequacy end) |
| **U4′** | `zero_usage_erasable` (RE-SEQUENCED here, U4's finding) | pending U5/U6. **NOT a cheap close** — verified: the 0-graded var still occurs syntactically + type-checks (`ret (vvar 0)` at `q=0`), so both syntactic readings of `NotEvaluated` are FALSE; the faithful notion is irreducibly SEMANTIC (Torczon `semtyping.v`), a **corollary of the LR**. The `sorry` body documents the closing argument: instantiate `Crel`/`Vrel` at the 0-graded slot via `lr_fundamental`, then `lr_sound` for `⊑` both ways |
| U7 | `effect_sound` | **DEFERRED → ◊5** (Q14 trace-semantics *design* decision, not a proof gap) |

## What's landed (the foundation)

- **LR machinery DEFINED, axiom-clean.** `Bang/Meta/LR.lean`: helpers (U1) + the 4 relations (U2) are real
  defs; `lr_sound`/`lr_fundamental` now `[propext, sorryAx, Quot.sound]` (only the proof bodies remain).
- **Spec corrected + cleaned.** `Crel`/`Krel`/`Srel` row-indexed (faithful Biernacki τ/ε, ADR-0033);
  `group_recovers` deleted (ADR-0032). `≈`/`⊑` UNCHANGED — so U5/U6 target a stable equivalence.
- ◊2/◊3 gates held 0-axiom / trusted-three throughout.

## Risks / open

- **U5 biorthogonality** is the remaining proof risk (adequacy of the LR wrt the observation `Converges`).
- **U6 `compat_handle`** consumes `Srel` (the control-stuck clause) — the `[KEY]` compat lemma, proven last.
- `zero_usage_erasable` (now **U4′**, post-LR): the cheap operational path is REFUTED (U4 verified — the
  0-graded var still occurs syntactically + type-checks, so non-occurrence/subst-independence are both false).
  It is an LR corollary (Torczon `semtyping.v`): closes once `lr_fundamental`/`lr_sound` land.

## ◀ RESUME POINT (2026-06-23 session end — HEAD `9e2a73d`, clean, green 723 jobs)

**Statements + infrastructure are landed; the proof BODIES of `lr_fundamental`/`lr_sound`/`zero_usage` are
the remaining work.** Two ◊4 frozen-statement corrections landed this session (ADR-0033 τ/ε row, ADR-0034
env-closed fundamental theorem) — **the "frozen" LR statements were Phase-A stubs being finalised through the
proofs; don't treat them as immutable** (the genuinely-frozen ones are the proven ◊2/STD block). Committed
green: `cab4dfd`→`a477554` (U6: anti-reduction infra, `crel_ret`/`crel_force`, `krel_refl` named contract,
ADR-0034 amendment, `closeC`/`closeV` commutation for non-binding formers).

**Remaining map (U6's, dependency order — resume here):**
1. **Binding-former `closeC` commutation** (letC/lam/case/split) — THE CRUX. **The ONE unblocking lemma
   (U6's precise next step):** `closeC_subst_comm : closed δ → (closeCUnderBinder δ N).subst w = closeC δ
   (Comp.subst w N)` (close-under-binder then substitute the filler = substitute then close). Holds because
   `EnvRel` fillers are CLOSED, so `Comp.substFrom 1 (Val.shift v) N = Comp.substFrom 1 v N` (the shift
   vanishes on closed `v`). **CONCRETE FIRST MOVE:** add a closedness carrier to `EnvRel` (or a parallel
   `EnvRelClosed`) — `Vrel`-values-closed is FALSE in general (a `vthunk` of an open comp can be
   `Vrel`-related), so thread it EXPLICITLY — then prove `closeC_letC`/`_lam`/`_case`/`_split` under it,
   **reusing `Bang/Core/Soundness.lean`'s `HasVTy.shift_closed`/`subst_closed`** (closed-typed values are
   shift/subst-invariant — exactly the vanishing-shift fact). [task #33]
2. **Mutual value+comp fundamental induction** (`vrel_refl` + `crel_fund`, mutual via `vthunk`), each case
   → its compat core. Leaf cases (ret/force/up) ready; binder cases gated on (1). [task #31]
3. `compat_up` (consumes `Srel`) then **`compat_handle` [KEY]** (`Srel` across resumption) — LAST. [task #30]
4. **`crel_unfold` μ/▷ off-by-one = BLOCKER 2, OPEN → route to the LR-relations thread** (it owns the
   relation defs). Root cause (verified vs biernacki-popl18 §4 Fig 7): `CoApprox` is deliberately index-free
   (`LR.lean:254`), which correctly absorbs the ▷ for the EFFECT fragment but silently drops the ▷ that
   `Krel`'s RETURN-half needs at recursive μ types — so `unfold (fold u)` at μ has no ▷ to spend. Decide:
   global `Krel`-return-half index-step vs a μ-localized Löb step (prefer the most-localized faithful fix —
   minimize blast radius on the compat lemmas). **Only bites the iso-recursive ADT fragment; everything else
   proceeds without it.**
5. Then the **`lr_sound` capstone** → the LR thread (`lr_sound = lr_sound_closed ∘ krel_refl`, short) + the
   **`zero_usage_erasable` corollary** (U4′, via the now-available `Vrel`/`lr_fundamental`).

**Orchestration note for the resume:** the proof spine is single-writer-serial (Compat/LR/Spec). Route the
LR-relation work (Blocker 2 + the `lr_sound` capstone) to ONE LR-relations thread (owns the relation silo);
the compat/substitution-descent to one proof-engineer; serialise their `LR.lean` access or worktree-isolate
(the `isolation` flag has been unreliable — verify `git worktree list`). See `[[subagent-procedure-vs-thread]]`.

## References

- `references/papers/3-lr/`: biernacki-popl18 (Figs 6–9, §5.4 set-row; **§4 Fig 7 = the ▷/Obs Blocker-2
  reference**), benton-hur-icfp09 (biorthogonality), ahmed-esop06 + pitts (step-indexing),
  proving-correctness-step-indexed.
- `docs/notes/spec-proof-discipline.md` (PROOF_ORDER), `docs/decisions/{0032,0033,0034}-*.md`, ADR-0015 (the
  reification frontier the LR subsumes), ADR-0016 (two-hop; LR = WasmFX-side correctness).
