# 0058 — The CrelK Canonical wall is a frozen-signature artifact; route 1 (carry the real counter) deletes it

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The binary-LR **Canonical wall** (task #33) — closing `crelK_fund`'s ret case, hence
  `lr_fundamental`/`lr_sound`, needs `Canonical` (dense ids) for arbitrary `KrelS`-related observation
  stacks — is a **frozen-signature ARTIFACT**, not a fundamental difficulty. `CrelK` observes configs at
  the DERIVED counter `handlerCount K` *because* the frozen `CrelK`/`KrelS` signatures cannot carry the
  real gensym counter `g` (the code says so verbatim: *"CrelK/KrelS signatures are frozen, so the counter
  is DERIVED, not a param"*, LR ~:1445-1447, inc5-lr-reindex). `Canonical`, `Val.CapsBelow`, and
  `run_bump_converges` exist **solely** to validate that the faked counter matches the real ids (density)
  and to bridge the `+1` shift when a pop makes them disagree. A **machine-checked GC-simulation relation**
  (`CtxRel`/`SegRel`, Lean 4.31, axiom-clean — keys handler identity by a **bare reference** with **no
  counter**) proves the identity-keyed target closes axiom-free for both HANDLE (append-only `Ξ`,
  `ctxRel_mono` axiom-free) and RESUME (**read-disjointness** `h ∉ rs`, not arithmetic; `resume_preserves`
  `propext`-only). **DECISION: route 1** — un-freeze `CrelK`/`KrelS` to carry the real counter `g` (or the
  read-set), which makes the observed config the *actual* config, the pop shift the *actual* `g → g+1`, and
  deletes `Canonical`/`CapsBelow`/`run_bump` entirely (no faked counter to reconcile). A frozen `Crel`/
  `Spec.lean` signature change, scheduled for **inc-6** (the binary LR is the contextual-equivalence /
  compiler-correctness path; `type_safety` goes through the diagonal and is unaffected). Route 2 (prove the
  stacks Canonical) *fights* the artifact; route 1 *deletes* it.
- **Refines**: 0055, 0054
- **Depends-on**: 0016, 0050, 0052, 0055
- **See-also**: 0044, 0057

## Status

Accepted (2026-06-26). Operator-ratified during the Lexa / Wasm-3.0-backend design session, on the strength
of a machine-checked reference relation (below). Implementation scheduled for **inc-6** (the binary LR is
the compiler-correctness deliverable, not the soundness one — `type_safety`/`NonEscape` close via the
diagonal, ADR-0056/0057, independently of this).

## Context

### The wall (task #33)

Closing `crelK_fund`'s ret case — and therefore the frozen `lr_fundamental`/`lr_sound` (contextual
equivalence) — requires `Canonical K₁ K₂` (each `handleF`'s id is dense, `< handlerCount`) for **arbitrary**
`KrelS`-related observation stacks. Build-confirmed (`e909e73`, `CanonicalWallProbe`): the obligation is
neither **derivable** (route 3 — `krelS_handleF` carries no `n < handlerCount` bound; B-occ is orthogonal to
id-density) nor **removable** (route 4 — the guarded `crelK_ret`'s `Canonical` is load-bearing at the
handleF-pop `+1` bridge via `run_bump_converges`). So it appeared to need a frozen-`Crel` change (route 1)
or a hard reachability lemma (route 2), and was deferred.

### The root cause, read from the code (the artifact)

`CrelK` (LR ~:1442) observes the config at a **derived** counter:

```lean
CrelK n C ε c₁ c₂ = ∀ D K₁ K₂, KrelS n C D ε K₁ K₂ →
    CoApproxC_le n (handlerCount K₁, K₁, c₁) (handlerCount K₂, K₂, c₂)
```

and the comment is explicit: *"the canonical fresh counter for a stack K is `handlerCount K` … **CrelK/KrelS
signatures are frozen, so the counter is DERIVED, not a param.**"* The config's *real* counter is the
gensym `g` (ADR-0055); the LR cannot carry it (frozen signature), so it fakes one from the stack structure
(`handlerCount K`). Consequently:

- **`Canonical`** (LR ~:1164, `Frame.CapsBelow (handlerCount …)`) is the obligation that the *faked* counter
  equals the *real* ids — i.e. the stack is dense.
- **`run_bump_converges`** (LR ~:963) bridges the `+1` shift when a `handleF` pop makes the faked counter
  (`handlerCount K' + 1`) and the recursion's observation (`handlerCount K'`) disagree.
- **`Val.CapsBelow 0`** is the value-side half of the same density bookkeeping.

All three exist **only** to reconcile a counter the frozen signature forced the LR to fabricate. The count
is otherwise never external — it is always written `handlerCount K₁` *adjacent to* `K₁`, so it is always
reconstructible from the structure; `handlerCount` is NOT load-bearing for the step index (`n`, separate) or
the `crelK_ret` induction (on `K₁`'s structure).

### The reference: a machine-checked identity-keyed relation

The Lexa-comparison / Wasm-3.0-backend design (2026-06-26) produced a **machine-checked** simulation
relation for a GC-frame abstract machine (Lean 4.31, standalone, axiom-clean — grep-confirmed zero `sorry`,
no `sorryAx`). It keys a handler instance by a **bare GC reference**, not a counter:

```lean
| hdl : H r = some (Node.handler parent op henv) → Ξ L = some r → … → CtxRel … (some r)
```

and proves the structural lemmas that are the *exact* analogues of our obligations:

| GC-machine lemma | axioms | our artifact it dissolves |
|---|---|---|
| `ctxRel_mono` (relation survives `Ξ` extension) | **none** | the append-only property (no offset reinterpretation) |
| `handle_preserves` (HANDLE = append `Ξ[L↦h]`) | `propext` | the "did the handler land where the counter says" step |
| `resume_preserves` (the `delim.parent := cur` splice) | `propext` | the pop/resume bridge — **via read-disjointness `h ∉ rs`, no arithmetic** |

The decisive refinement (build-corrected, not guessed): the splice's side-condition is **read-disjointness**
(`h ∉ rs`, the refs the relation dereferences as nodes), **not** reachability (`h` *is* reachable — it is the
segment's bottom target). There is no `next^m`, no segment-length counting anywhere. The identity-keyed
relation is fully in the easy, append-only, arithmetic-free regime.

## Decision

**Route 1: un-freeze `CrelK`/`KrelS` to carry the real gensym counter `g`** (minimal encoding) **or the
read-set** (structural encoding, matching the GC-machine reference). The observed config becomes the
*actual* config (`(g, K, c)`, not `(handlerCount K, K, c)`); the pop shift becomes the *actual* `g → g+1`;
and **`Canonical`, `Val.CapsBelow`, and `run_bump_converges` all delete** — there is no faked counter to
reconcile, so there is nothing for them to validate. The guarded `crelK_ret`'s `hcan`/`hvcf` premises
vanish and its ret case closes.

The route-1 re-key needs one invariant — *the freshly-minted id is disjoint from the live stack* (the real-
`g` analogue of the GC-machine's `h ∉ rs`). **We already have it**: `WellCounted` / `splitAtId_fresh`
(ADR-0055). So the read-disjointness the GC-machine assumes and our freshness lemma are the same fact in two
encodings. NOTE: the sharper re-keying criterion (from the machine-checked invariant lemma) is **carry the
read-set as a `NoDup` list** — the density obligations become `nodup_split`-shaped membership facts
(`h ∉ prefix`), not counts; so route 1 is mechanical iff `handlerCount` is reconstructible as the length of a
`NoDup` read-set the relation already carries (it is — `handlerCount K` is written adjacent to `K`).

**EPISTEMIC STATUS (build-confirmable, NOT yet proven).** The `CtxRel`/`SegRel` reference relation is
machine-checked axiom-clean for a *clean-slate* machine; that *our* `crelK_ret` re-keys onto it — that
`handlerCount` is load-bearing for nothing the read-set can't reconstruct (in particular not the step index
or the `crelK_ret` induction) — is a **code-read conclusion**, not a `#print axioms` result. The code
documents the artifact (the "DERIVED, not a param" comment is dispositive about *why* the counter is faked),
and that is the right basis for the decision — but it is a different epistemic status than the
machine-checked target. **The deletion COMPILING is the proof.** So: *here is the artifact we believe
deletes, pending the re-key actually compiling* (inc-6). The decision is sound; the verification is the
implementation.

## Consequences

- **Frozen-statement change.** `CrelK`/`KrelS` (the `Crel` target `lr_sound`/`lr_fundamental` consume, in
  `Spec.lean`) gain the real counter / read-set. This is a frozen acceptance-criterion change → this ADR +
  `STATEMENT_CHANGE_OK` at implementation.
- **Deletes:** `Canonical` + `Canonical.capsBelow` (LR), the `CapsBelow` density premises on
  `crelK_ret`/`crelK_fund`, `run_bump_converges` and its `run_rename` plumbing where it served only the fake
  counter, and the `hcan`/`hvcf` arguments threaded through the Compat consumers. Net LR/Compat LOC is
  expected **negative**.
- **Banked work carries over.** inc-5 Units 1+2 (the `splitAtId` decomp + the KrelS layer, `285338a`) are
  stack-structural and identity-keyed already; verify they survive the counter re-key (expected: yes — they
  never consumed `handlerCount` except as the adjacent observation slot).
- **Decided on the merits, not deferred.** Route 2 (prove `lr_sound`'s instantiation stacks Canonical —
  hard, `krelS_refl` needs its own density story) *establishes* density for the fake counter; route 1
  *removes* the fake counter. The machine-checked relation is the argument that route 1's target is clean.
- **Scope boundary.** This is the **binary LR** (contextual equivalence, the inc-6 compiler-correctness
  path). `type_safety`/soundness goes through the **diagonal** (`NonEscape`, ADR-0056/0057) and is
  unaffected — this ADR does not touch it.
- **Forward link.** The same GC-machine reference is the codegen design for inc-6's CalcVM→target lowering
  (handler = stable reference, raise/resume = one swap). A separate ADR will revise ADR-0016's target
  (Wasm 3.0 + grade-directed pluggable backend) — this ADR is only the *relation* decision. That revision is
  **conditional on** a check that the grades track *resumption* multiplicity (0×/1×-tail/1×-arbitrary), not
  just value/computation multiplicity (ADR-0025); if they do not, the abort/tail/general routing is a goal,
  not a result.

## Alternatives considered (rejected)

- **Route 2 — a Canonical-reachability lemma.** Prove the stacks `lr_sound` actually instantiates `CrelK` at
  are always Canonical. Fights the artifact (validates the fake counter); hard, since `krelS_refl`
  (Spec ~:192) instantiates at the observation context via its own density-free path. Strictly harder than
  route 1 for no benefit.
- **Routes 3 + 4 — derive `Canonical` from `KrelS`, or drop the guard as over-strong.** Both build-refuted
  (`e909e73`): `KrelS` carries no density bound, and the guard is load-bearing at the pop bridge.
- **Keep `handlerCount` (status quo).** The wall stands; `lr_sound` cannot close. Rejected.
