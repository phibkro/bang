# PATH — ◊4.5b finish: the append crux + the (g) re-point

**Status:** THROWS CLOSED end-to-end in the new arch (cap45-modality @ 3eca3ce, build GREEN,
axiom set clean: no_accidental 0-axiom, compile_correct trusted-three). The whole ◊4.5b moat is
reduced to ONE research crux + the (g) mechanical migration. Two INDEPENDENT remaining pieces.

## What is DONE (committed 86a906f → 3eca3ce, all green + axiom-gated)

- **`h₁=h₂` handleF clause** (`LR.lean` KrelS) — equal handlers ⇒ `splitAt` fires identically.
- **RESUME CONJUNCT** in KrelS's handleF clause — op-arg-keyed (`opArg h.label op`) under a
  `handlesOp h h.label op` guard, so suppliers pin the resume value's type from the handler
  interface. (The producer lacks `HasStack`; the conjunct CARRIES the typed resume.)
- **`krelS_splitAt_decomp`** (Compat) — extracts same-handler split + related outer tails +
  the resume conjunct at the catching frame.
- **`Handler.label`, `handlesOp_label`, `splitAt_some_handlesOp`** (helpers).
- **THROWS supplies SORRY-FREE**: `compatK_handleThrows` + `krelS_refl` handleF arm (via `crelK_ret`).
- **Producer `up` THROWS sub-case CLOSED** in `crelK_fund` (decompose → []-prefix dispatch agrees
  for throws → `coApproxC_le_anti_step` + extracted `hres`; type alignment from `hArg`+`handlesOp_label`).
- mono/eff lemmas thread the conjunct; WF intact.

## REMAINING PIECE 1 — the `krelS_append` crux (RESEARCH or SEAM; operator decision)

The ONE research question, in 6 new-arch spots that are all THE SAME: `compatK_handleState`,
`compatK_handleTransaction`, `krelS_refl` state/txn arms, `crelK_fund` producer state/txn arms.
- **The crux:** state/txn dispatch KEEPS `Kᵢ` and reinstalls the handler:
  `dispatchOn op v (Kᵢ, state ℓ s, Kₒ) = (Kᵢ ++ handleF (state ℓ s')::Kₒ, ret r)`. The `[]`-prefix
  resume conjunct must bridge to the producer's `Kᵢ`-prefix via **`krelS_append`** (compose the
  kept `Kᵢ` + reinstalled handler + `Kₒ`), AND the **▷-metering** must compose so the 1 dispatch
  step stays payable (likely the resume conjunct at `m<n` per `coApproxC_le_anti_step`, LR:140).
- **Throws needs NONE of this** (`Kᵢ` discarded regardless of length) — hence throws closed cleanly.
- **SEAM fallback (ADR-0026):** if the metering walls after a real attempt, the state/txn-resume
  producer is the tested-superset descent (throws-handlers verified, state/txn-resume diff-tested).

## REMAINING PIECE 2 — sub-block (g), the re-point (MECHANICAL, ~147 old-arch lemmas)

`lr_fundamental` is still wired to the OLD `crel_fund` (over `Crel`/`Krel`/`Srel`); `lr_sound`
(Spec:174) is still `sorry`. (g) wires the headline theorems onto the new arch:
- Redefine frozen `Crel := CrelK`, `Vrel := VrelK`, `EnvRel := EnvRelK` (body swap, **signature
  byte-identical** — the frozen statements don't change).
- Delete old `Krel`/`Srel` + their lemma blocks + old `vrel_fund`/`crel_fund`/`krel_refl`
  (~147 lemmas reference the old bodies; ~218 mentions in Compat). This is the bulk.
- Rewire `lr_fundamental := crelK_fund`; prove `lr_sound` via `lr_sound_closed ∘ krelS_refl`.
- **This is careful REFACTORING, not research.** Best done in a FRESH context (Context-Rot risk on
  a 147-lemma body-swap in a long session). Build-gate incrementally; the gate cannot pass
  mid-migration (the additive-then-migrate sequencing note in PATH-cap45-rebuild applies).

When (g) lands AND the append crux resolves (research or seam): `lr_sound`/`lr_fundamental` →
trusted-three = the full contextual-equivalence moat.

## (g) STATUS — LANDED (cap45-finish: `812e9da` LR, `6764d22` Compat, `89e98e0` Spec)

The body-swap is DONE and build-green. Old flat `Vrel`/`Crel`/`Krel`/`Srel` + `crel_fund`/`vrel_fund`/
`krel_refl` + old compat cores DELETED (grep gate clean). Frozen `Vrel`/`Crel`/`EnvRel` re-pointed to the
answer-typed `VrelK`/`CrelK`/`EnvRelK` via `abbrev` (signature byte-identical). `lr_fundamental :=
crelK_fund` — axioms `[propext, sorryAx, Classical.choice, Quot.sound]`, `sorryAx` traces SOLELY to the
append crux. `no_accidental_handling` 0-axiom + `compile_correct`/`compile_forward_sim` trusted-three
PRESERVED. The 6 append-crux sorrys (`compatK_handleState`/`Transaction`, `crelK_fund` + `krelS_refl`
state/txn arms) are the ONLY research sorrys `lr_fundamental` depends on.

### BLOCKER on `lr_sound` (ESCALATION — NOT the append crux)

`lr_sound` could NOT be closed by `lr_sound_closed ∘ krelS_refl`. The migration plumbing composes (refocus
`⊑` to config level + `CrelK` unfold + instantiate at observation context `(C,C)`), but the sole remaining
obligation `KrelS fuel B C e C C = krelS_refl` REQUIRES `C` WELL-TYPED at the hole type `B`
(`HasStack C e B eo (F qo Ao)`). The FROZEN `⊑`/`ctxApprox` (LR.lean:64) quantifies over ARBITRARY UNTYPED
`Cxt` — and `KrelS`-reflexivity genuinely FAILS for a context ill-typed at the hole (`letF N :: K'` with
`B ≠ F q A` makes the `KrelS` letF clause FALSE, not vacuous; `lr_sound` is likely even FALSE over untyped
contexts). RESOLUTION (orchestrator decision): (a) restrict `ctxApprox`/`⊑` to well-typed contexts (the
standard contextual-equivalence quantifier — a `ctxApprox` def change), then `lr_sound = lr_sound_closed ∘
krelS_refl` traces to the append crux; or (b) add a `HasStack` hypothesis to `lr_sound` (frozen-statement
change). `lr_sound` left as honest `sorry` with the precise blocker comment at `Spec.lean:188`.

## ◊4.5b-answertrack — the scoped-seam (ADR-0043, branch `cap45-answertrack` off `eb599b6`)

The append crux + (g) + the `lr_sound` `HasStack`-typing escalation are ALL CLOSED (in `eb599b6`):
`lr_sound`/`lr_fundamental` build green, `sorryAx` traces to EXACTLY ONE spot — `krelS_splitAt_decomp`'s
handleF-MISS (the nested-wrapping-handler edge, `Compat.lean:1474`). This branch scoped that last edge.

### LANDED (`1d715cb`, whole-tree green)
- **`NoWrapMiss : EvalCtx → Label → OpId → Prop`** (`Operational.lean`, after `splitAt`): the dispatch
  reaches its catcher with a handler-free captured continuation. Standalone; kernel/`KrelS` PRISTINE.
- **ADR-0043**: the moat scope. COVERED = all contexts incl. legitimate handler stacking (each op at its
  nearest handler); EXCLUDED narrow = pass-through resumption (op caught by a non-nearest handler).

### WHY sorryAx-ZERO IS DEFERRED (build-pinned, this session) — the EXACT next-session plan

**typed-CrelK necessity — BUILD-PINNED (2026-06-24).** Row-indexed (ii-b) `NoWrapMissRow` on `CrelK`'s
tail threads `crelK_zero`/`adequacy_nil`/`eff_mono` (antitone OK) but WALLS at `crelK_ret`'s two
frame-strips: (1) **letF** (LR.lean ~879) — the continuation runs at row `φ` over `K₁'`, needs `φ ≤ e`
which a RAW `KrelS` lemma lacks → typing required; (2) **handleF** (LR.lean:887) — passing a `ret` through
`handleF h₁` masks `h₁`'s caught ops, so `NoWrapMiss (handleF h₁::K₁') ⊬ NoWrapMiss K₁'` → handler-
interface knowledge required. The row-discharge discriminator is right for the handle-ARM but the scope
dies UPSTREAM in `crelK_ret` first. ⇒ **typed-`CrelK`** (`CrelK` re-indexed by `HasCTy`/`HasStack`) is the
necessary mechanism, threaded through the whole mutual block. Probe (i) corroborates: threads
`krelS_splitAt_decomp` + `crelK_fund_up`, walls at `crelK_fund:1957` (unscoped `CrelK` can't supply the
up-arm premise). (The green partials re-derive cheaply; a fresh (ii) session wants them fresh — no
Context-Rot from a stale mutual-block reshape.)

The MISS-vacuity needs `CrelK` to range only over stacks handling the focus's ops at the nearest handler.
ALL simple stack-scope predicates WALL at one root cause: `crelK_fund`'s handle-arm pushes the focus's OWN
handler (`handle h M` → `M` over `handleF h :: K₁`), violating any runtime-stack scope `P K₁` (need
`P (handleF h :: K₁)`). Build-and-reasoning-confirmed dead: row-indexed `NoWrapMissRow K ε` (walls at
`crelK_ret` letF row-change, no `φ ≤ e` untyped), row-agnostic ∀-ops (walls at `crelK_ret` handleF
handler-masking), fully-`HandlerFree` (walls at the handle-arm push). The `HandlerFree`-ON-the-`KrelS`-clause
variant OVER-FORBIDS (bans legit stacking, breaks `krelS_refl`) — DO NOT re-try it.

**THE CLOSE = a TYPED `CrelK`** (the deferred kernel project, ~pinned-index order of magnitude):
- Re-index `CrelK`'s scope by typing (`HasCTy`/`HasStack`) so it distinguishes the focus's
  legitimately-installed handlers from a pre-existing context wrap — that distinction is what no raw
  stack predicate can make.
- `CrelK`'s body gains the scope premise ⇒ ripples to **every `rw [CrelK]` site** (`LR.lean`:
  `crelK_zero`, `crelK_adequacy_nil`, `CrelK_eff_mono`, `crelK_ret`, `crel_force`, `lr_sound_closed`,
  ~10 sites — each `intro` gains the scope hyp; each APPLICATION supplies it) **+ all Compat compat
  lemmas** (the `hM D (handleF h :: K₁)` applications) **+ the `crelK_fund` mutual block** (WF watch:
  the scope is a non-recursive `Prop` premise, so the `(n,role,stackLen,sizeOf)` metric is unaffected —
  but verify it stays inferring).
- `krelS_splitAt_decomp` takes the typed-scope hyp ⇒ MISS vacuous (via `NoWrapMiss` + the handler-free
  captured continuation it now certifies); `crelK_fund_up` supplies it; `lr_sound`'s `ctxApprox` carries
  the matching premise on the observation context `C` (mirror the #11 `HasStack` premise).
- Frozen-stmt: `lr_sound` + `lr_fundamental` gain the scope premise (STATEMENT_CHANGE_OK, per ADR-0043).
- Do it in a FRESH context (Context-Rot on the ~10-site + Compat reshape). Commit-first per clean lemma;
  flag-before-build at the first `crelK_fund` WF wobble.

## Discipline (carried)
Build is the only arbiter; gate the AXIOM SET each commit (`lake env lean Bang/Audit.lean`) AND on a
WHOLE-TREE `lake build` (never a per-module build — that gives false-green). flag-before-build the
scope-thread WF. Shared git store had a broken cache-tree — recover per-worktree via `git read-tree HEAD`
(do NOT gc/prune the shared store; other writers active). The pre-commit `just verify` reclones loogle
(network-flaky); `--no-verify` with `BANGLANG_SKIP_VERIFY_REASON` is OK for that, but run the whole-tree
build manually before declaring green.
