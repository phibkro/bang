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
| **U4** | `seq_unit` + `zero_usage_erasable` — the two cheap closes | ▶ **NEXT**. seq_unit = left-unit monad law (seqComp def); zero_usage = `NotEvaluated` def + 0-graded reasoning (verify it closes operationally, not via full Vrel) |
| **U5** | `lr_sound` — biorthogonality adequacy (Crel ⇒ ⊑) | pending U4. benton-hur ICFP09 / pitts. The harder proof |
| **U6** | repopulate `Bang/Compat.lean` (16 lemmas) → `lr_fundamental` by induction over `HasCTy` | pending U5. `compat_handle` LAST (consumes `Srel`) — kernel-engineer pairing there |
| U7 | `effect_sound` | **DEFERRED → ◊5** (Q14 trace-semantics *design* decision, not a proof gap) |

## What's landed (the foundation)

- **LR machinery DEFINED, axiom-clean.** `Bang/LR.lean`: helpers (U1) + the 4 relations (U2) are real
  defs; `lr_sound`/`lr_fundamental` now `[propext, sorryAx, Quot.sound]` (only the proof bodies remain).
- **Spec corrected + cleaned.** `Crel`/`Krel`/`Srel` row-indexed (faithful Biernacki τ/ε, ADR-0033);
  `group_recovers` deleted (ADR-0032). `≈`/`⊑` UNCHANGED — so U5/U6 target a stable equivalence.
- ◊2/◊3 gates held 0-axiom / trusted-three throughout.

## Risks / open

- **U5 biorthogonality** is the remaining proof risk (adequacy of the LR wrt the observation `Converges`).
- **U6 `compat_handle`** consumes `Srel` (the control-stuck clause) — the `[KEY]` compat lemma, proven last.
- `zero_usage_erasable` (U4): Torczon proves it *semantically* via an LR; check whether our statement closes
  cheaper via an operational non-occurrence argument over `NotEvaluated` before reaching for the full Vrel.

## References

- `references/papers/3-lr/`: biernacki-popl18 (Figs 6–9, §5.4 set-row), benton-hur-icfp09 (biorthogonality),
  ahmed-esop06 + pitts (step-indexing), proving-correctness-step-indexed.
- `docs/notes/spec-proof-discipline.md` (PROOF_ORDER), `docs/decisions/{0032,0033}-*.md`, ADR-0015 (the
  reification frontier the LR subsumes), ADR-0016 (two-hop; LR = WasmFX-side correctness).
