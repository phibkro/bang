# PATH — the typed + static-dispatch pivot (ADR-0045)

> The build sequence for ADR-0045 (pivot to typed LR + static/capability dispatch). Each step is
> build-gated (whole-tree `lake build` + `#print axioms`). The DECISION is made + de-risked by three
> gated spikes; this PATH lands it. Multi-session, fresh-context — the LR re-index (step 2) is the bulk.

## Start from the gated spikes (the models to lift)

- `static-dispatch-spike @ b1330db` — `Bang/StaticSpike.lean`: `staticSplit` (cap-counting dispatch),
  `staticSplit_zero_inner_noHandleF` (cap=0 dissolves), `staticSplit_succ_inner` (cap>0 cap-indexed).
- `setrow-tension-spike @ f92a504` — `Bang/SetRowSpike.lean`: the typed `perform cap` rule keeping `Finset`
  rows, `CapResolves`/`CapResolvesKind` (decidable positional well-scopedness, no polymorphism).

Both are pushed branches; lift their definitions into the kernel proper.

## Build sequence (each step a build-gated commit)

1. **Kernel dispatch swap.** `Comp.up ℓ op v` → `Comp.perform cap op v` (cap : Nat); `splitAt` → `staticSplit`
   in the operational step; `dispatchOn` (throws/state/txn arms) UNCHANGED (they consume `(Kᵢ, h, Kₒ)`).
   Add the typing rule `HasCTy.perform` (row premise `labelEff ℓ ≤ φ` — set-rows, from SetRowSpike) + the
   `CapResolves` well-scopedness side-condition. Re-green the operational metatheory (preservation/progress
   over `staticSplit` — a *simpler* obligation than the search). **Gate:** whole-tree build + the STD block
   axiom-clean.

2. **LR re-index (the bulk).** Re-index the biorthogonal relation from raw stacks to the type structure
   (`Vτ`/`Cτ`/`Tτ`), reusing the EXISTING Nat-step + `▷` substrate (`ConvergesC_le n`, the metered-`▷`) — only
   the index set changes. Re-prove `lr_fundamental` / `lr_sound` over the typed relation. The resume-edge now
   discharges: cap=0 via `staticSplit_zero` (handler-free captured continuation, structural); cap>0 via the
   cap-indexed answer-type witness. **Gate:** `#print axioms lr_sound` / `lr_fundamental` — `sorryAx` GONE
   (the ADR-0043 edge dissolved), trusted-three only.

3. **`no_accidental_handling` → structural.** At cap=0 it holds by construction (a perform reaches only its
   cap-named handler). Decide: retire the lacks-constraint proof, or relocate it to the shell's dynamic macro.
   **Gate:** the 0-axiom property restated structurally, audit green.

4. **Dynamic-dispatch-as-shell-macro.** Surface elaboration: a `with h` block binds a capability; `perform name`
   elaborates to a reader-effect lookup resolving `name` → cap by lexical scope, emitting `perform cap op v`.
   This is shell (TESTED vs the kernel oracle — differential, not proven). **Gate:** the differential battery
   (dynamic-surface program ≡ its static-elaborated kernel form on observable values).

5. **Calculated-VM re-run.** Re-run the Bahr–Hutton derivation over the simpler static dispatch (a strictly
   smaller obligation). **Gate:** `compile_correct` / `exec ∘ compile ≡ eval` re-green, trusted-three.

## The one open design choice (decide in step 1)

**cap>0 (resume-into-an-outer handler):** KEEP it (ride the typed cap-witness — full expressivity, the pivot's
intent) **or** FORBID it (nearest-only caps — the dissolve becomes TOTAL + untyped, but no resume-into-outer).
Recommendation: keep it (the typed witness is cheap given the typed LR; expressivity matters), but the
nearest-only fallback is a clean de-risk if step 2's cap>0 arm proves hard.

## Risks / watch

- **Step 2 is the multi-session bulk** — re-indexing the mutual LR block by typing. It is IN-FAMILY (the
  substrate is unchanged; only the index moves) and the typed form is the *standard* biorthogonal shape, so it
  is a deepening not a rewrite — but it touches the whole relation. Fresh-context; flag-before-build at any WF
  wobble in the mutual block.
- **Frozen statements** (`lr_sound`/`lr_fundamental`) gain a typed index — a STATEMENT_CHANGE_OK amendment,
  recorded against ADR-0045 (and they get STRONGER: the edge sorry vanishes).
- **CalcVM** (step 5) is low-risk but must re-green; do it last so the dispatch + LR are settled first.

## Discipline (carried)

Build is the only arbiter; gate the AXIOM SET each commit + whole-tree `lake build` (never per-module).
Commit-first per clean step. flag-before-build at the first wall. The three gated spikes are the proof the
direction is sound; this PATH is mechanical-but-large, not research — the research risk was retired by ADR-0043
(the edge is real under dynamic) + the spikes (static dissolves it, set-rows hold).
