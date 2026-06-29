# 0035 — Biorthogonal LR for equivalence (◊4); annotated simulation for compilation (◊5)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Biorthogonal LR proves ◊4's contextual-equivalence theorems; AsmFX-style annotated simulation is the method for ◊5's `compile_forward_sim`.
- **Depends-on**: 0016, 0033, 0034

- **Layer:** C (compiler / methodology)
- **Status:** Accepted
- **Depends on:** 0016 (two-hop architecture), 0033 (LR relations row-indexed), 0034 (lr_fundamental env-closed)

## Context

◊4 proves the source-level equational theorems with a **biorthogonal step-indexed
logical relation** (Biernacki POPL'18 + Benton–Hur ICFP'09): `Vrel`/`Crel`/`Krel`/`Srel`
in `Bang/Meta/LR.lean`, where `Crel` is co-behaviour against *every* `Krel`-related stack
and `Krel` closes back over `Crel`/`Srel` (the ⊤⊤-closure).

Lindley et al.'s **AsmFX — "Effect Handlers All the Way Down"** (Oct'25 draft,
`references/papers/4-wasmfx/lindley-draft25-...pdf`) is the **nearest published twin of
CalcVM→WasmFX**: it proves a handler-compiler correct via a *plain annotated simulation
relation* (no Iris, no biorthogonality). `references/README.md` flagged it as "the concrete
alternative to compare biorthogonality against **before committing the ◊4 proof
architecture**." This ADR records that comparison (run 2026-06-23, mid-◊4).

The question: should AsmFX's simpler simulation method **replace or reshape** our
biorthogonal LR for ◊4 and/or ◊5?

## Decision

**The two methods are complementary, not substitutes.**

- **◊4 (source equational theory) — keep biorthogonal LR.** `lr_sound`,
  `lr_fundamental`, `zero_usage_erasable` are two-sided contextual-equivalence claims;
  AsmFX's one-directional simulation cannot discharge them. ◊4 proceeds unchanged.
- **◊5 (`compile_forward_sim`) — adopt AsmFX-style forward simulation.** State it as
  `Source.step ⇒ Wasmfx.run(≥1)` preserving a modelling relation `⊨` (AsmFX Thm 7.2 /
  Benton–Hur shape). It needs only one-directional preservation; ⊤⊤-closure is not required.

## Why this model

1. **The first three theorems are two-sided contextual equivalence** (`⊑`/`≈` over
   *arbitrary* contexts `C`). Compositionality under arbitrary contexts is exactly what
   ⊤⊤-closure buys (`Crel` co-behaves vs every `Krel`-related stack; `Krel` closes back
   over `Crel`/`Srel`). `lr_fundamental`'s under-binder induction blocks on
   `N[v₁] ~ N[v₂]` from `Vrel v₁ v₂` (the congruence / identity-extension direction —
   `Spec.lean:153-165`), and `zero_usage_erasable` is irreducibly two-sided (two distinct
   fillers ⇒ `≈`-equal computations, `LR.lean:82-83`). A forward simulation never relates
   two *source* programs, so it cannot reach any of these.
2. **`compile_forward_sim` is one-source / one-target / one-direction** — no context
   quantification, no two-sidedness. A state simulation suffices. That is AsmFX's shape
   and the Benton–Hur ICFP'09 template the references already pin, applied to *handler*
   compilation.
3. **AsmFX does not secretly prove equivalence.** Its theorems (Thm 7.1 scope-preserving
   sim p.19; Thm 7.2 control-flow sim p.22; Cor 7.6 end-to-end) and observation (Thm 7.3,
   p.18: termination + value-preservation + lock-step partial-exec) are one-directional.
   `sim ∘ adequacy` yields "source converges ⇒ target converges with the right value," NOT
   "two source terms observationally equal." So ◊4 is **not over-built**.

## What it commits to

- **◊4 unchanged.** `closeC_subst_comm` + biorthogonal `lr_fundamental` + `krel_refl`
  (the `letF N::C'` congruence) are load-bearing for `lr_sound`/`zero_usage_erasable`;
  no AsmFX shortcut exists for the source equational obligations.
- **◊5 method = forward simulation** preserving a modelling relation. Budget a **two-step
  sim** (source → annotated intermediate → machine) and reuse AsmFX's **epilogue/annotation
  technique** (§7, p.18) for compiled-only fragments (suspend/resume scaffold, leave records)
  that have no source counterpart — AsmFX's exact difficulty and fix.
- **No one-shot precondition.** AsmFX handles multi-shot resumption (§2.4, pp.6–7) and does
  not distinguish deep/shallow (§4); its method is strictly more general than v1's one-shot
  handlers — a safety margin, not a blocker.

## Consequences for other ADRs

- **Confirms ADR-0016** (two-hop; WasmFX target; LR as the correctness notion) — unchanged;
  this only refines the ◊5 sub-method.
- **Confirms ADR-0033 / ADR-0034** — the LR relation + env-closed fundamental statements are
  the right tool for the equational theorems, not over-engineering.
- **Bears on Q9 (WasmFX target drift).** AsmFX is its *own* abstract register ISA, agnostic
  to the engine (§8, p.24) — it is **not** WasmFX. We adopt its proof **method**, not its
  machine. Q9's recommendation stands: pin the **target semantics** to a live engine oracle
  (Iris-WasmFX / WasmFXCert, `legoupil-pldi26`), not either paper's frozen syntax.

## Rejected alternatives

1. **Replace biorthogonal LR with AsmFX simulation for ◊4 too.** Why not: forward
   simulation is one-directional and never proves two-sided `≈`; `zero_usage_erasable` and
   `lr_sound` are irreducibly two-sided contextual equivalence. This would leave the source
   equational theory unprovable.
2. **Use biorthogonal LR for ◊5 compile-correctness too (one method everywhere).** Why not:
   over-engineered — `compile_forward_sim` needs only one-directional preservation; ⊤⊤-closure
   adds compositionality machinery the single-source/single-target statement does not require.
   AsmFX demonstrates the simpler simulation suffices for handler compilation.
3. **Adopt AsmFX as the backend target.** Why not: AsmFX is its own abstract ISA (§8), not
   WasmFX. We take its proof method, not its machine (see Q9).

## Revisit if

- ◊5 begins and the forward simulation cannot carry handler suspend/resume cleanly — escalate
  to a relational/Iris approach (the "multi-shot continuations cross mutable TVars" trigger,
  post-v1; `references/README.md`).
- A published result unifies compile-correctness and contextual equivalence for handlers in a
  single relation.
- AsmFX's **appendix** (deferred from the read 24-page draft; full ASFX machine + detailed
  Thm 7.1/7.2 case analyses) reveals a two-sided lemma — *unverified* here; the verdict rests
  on the main-body theorem **statements**, which are direction-unambiguous. (A one-sided
  theorem cannot discharge a two-sided `≈` regardless of proof internals.)
