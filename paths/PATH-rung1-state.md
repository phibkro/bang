# PATH · Rung 1 — State (the first resumptive paradigm)

> The first paradigm-as-library on the verified kernel: **mutable State as a handler.** Ladder rung 1
> (PRD §3.1). Status: **READY** (scoped 2026-06-22, not started).

## ⚠ The finding that reshapes this issue

Rung 1 is **NOT a surface-only issue.** The kernel deferred resumptive state (`dispatch` returns
`none` for `.state` — Q12, which was blocked on Q6/the CK machine). Rung 0's `throws` was *zero-shot*:
it DISCARDS the captured continuation. State must KEEP and RESUME it (return the stored value, thread
the new state, continue). That is a **kernel + proof** change, not a parser change. The surface piece
(`get`/`put`/`handle`-state syntax) is thin and trivial *once the kernel resumes*.

So rung 1 is the first place the **product spine pulls the verification spine**: surface needs a
kernel capability → kernel adds it with proof → surface lowers to it. The roadmap's "product spine
runs in parallel freely" holds only for rung 0; rung 1+ each demand a kernel feature (state → Q12; a
real *counter* → arithmetic; rung 2 → products/sums). Coupled through one-kernel-feature-per-rung.

**Q12 is now unblocked**: it was blocked on Q6 (continuation reified, not substituted); Q6 landed as
ADR-0023. Rung 1 IS Q12's resolution.

## GOAL (verifiable)

A State program runs end-to-end: `handle (state ℓ s₀) { … put v … get … }` → `Source.eval` → the
final value, as a green Lean check. **Minimal demo = a state CELL** (`put 7; get` ⟶ `7`) — needs
ONLY resumptive state. A **counter** (`get; put (get+1)`) additionally needs arithmetic (`+`), a
separate K-ADR (tracer finding #1) — out of scope here. Land the cell first.

## SCOPE — kernel-first, three layers

**K — kernel (the real work): resolve Q12.** Make `dispatch` resume for `state`:
- `get`: return the stored state `s` to the captured continuation Kᵢ, reinstall the (deep) handler,
  continue — `handle (state ℓ s) (Kᵢ[up ℓ "get" unit]) ↦ handle (state ℓ s) (Kᵢ[ret s])`.
- `put v`: update the handler's stored state to `v`, return unit to Kᵢ, continue.
Unlike throws, the captured continuation Kᵢ (the `letF`/`appF` frames between the `up` and the
`handleF`) is **kept, not discarded** — one-shot resume (no multi-shot reification; that stays the
ADR-0015 frontier). Q12's grade-threading tension (get's reduct grade vs redex grade; put storing an
open value) is the proof obligation — the CK machine (continuation in the frame, not substituted) is
the intended fix Q12 names.

**P — proof: extend preservation/progress** to the state-resume transition. Likely an ADR
(resumptive-handler semantics is a genuine semantic addition; copy ADR-0023's format). Keep the axiom
set ⊆ {propext, Classical.choice, Quot.sound}; do **not** regress `no_accidental_handling` (must stay
0-axiom — the ◊2 gate).

**S — surface (thin): extend `Bang/Surface.lean`.** Parse/lower `get`, `put e`, and a state-handler
form. Lower to `up ℓ "get"/"put"` + `Handler.state ℓ s₀`. Add a green state-cell demo from source
text, à la rung 0.

## DELIVERABLE

- Kernel: `dispatch` resumes for state; metatheory extended; ADR written; `just verify` green,
  axiom-clean, `no_accidental_handling` still 0-axiom.
- Surface: state-cell demo runs from source text (green `#guard`/`rfl`).
- Finding appended here: what resumptive state actually cost (grade threading, continuation handling).
- **Confirm/refute the event-store framing** (PRD §6 / Framing A): both the event-store (verifiable,
  default) and in-place (fast, opt-in) handlers should be expressible as `state` handlers over THIS
  one mechanism — the event-store handler is plausibly `state ℓ (event-log)` whose `get` folds the
  log. If so, the event-store/in-place split is a *library* choice, NOT extra kernel work. Verify.

## OUT OF SCOPE

Arithmetic / `+` (separate K-ADR; blocks a "counter" but not a "cell") · STM (rung 3) · reactivity
(rung 4) · multi-shot / actors (ADR-0015) · the full event-store handler library · effect-row
checking of the surface · in-place handler optimization (invariant #7 — later).

## OWNER

**kernel-engineer + proof-engineer** (the K + P layers are the work). The S layer is a thin
follow-on, foldable into the same PATH or handed to a surface IC after. NOT a surface-only issue.

## POINTERS

- Q12 (graded state handlers) + Q6 (resolved — CK machine) in `docs/notes/OPEN_QUESTIONS.md`.
- Kernel: `Bang/Operational.lean` `dispatch` (the `.state _ _ => none` line is the gap) + `handlesOp`
  (already recognizes `get`/`put`). `Bang/Core.lean` `Handler.state ℓ s`.
- Typing: `Bang/Syntax.lean` handler typing; `Bang/Metatheory.lean` §E (config preservation/progress).
- Pattern: **ADR-0023** (the throws CK machine) is the template — state is the SAME stack scan,
  KEEPING Kᵢ instead of discarding it.
- Surface: `Bang/Surface.lean` (rung 0) — extend the parser + lowering.
