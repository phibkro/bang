# The cap-assignment elaborator (the shell side of `LWT`)

> ADR-0045 PATH step 4 — the surface elaborator that assigns lexical capabilities. Spiked +
> implemented + build-gated 2026-06-25 (`Bang/Surface.lean`, branch `shell-elaborator-spike @ ac7df60`).
> The kernel side is `LWT` (paths/PATH-cap-assignment-spike.md); this is its surface realization.

## What it does

Under static (capability) dispatch, an effect op `perform cap ℓ op v` carries a `cap` = the number of
handler frames the kernel's `staticSplit` skips to reach its handler. The elaborator computes that cap
by **lexical scope** at the op's author site.

```
lowerC/lowerV thread  hs : List Label   -- enclosing handler labels, INNERMOST first
  handle / state…in / atomically  →  PUSH the handler's label onto hs for the body
  effect op at label ℓ             →  cap = capFor hs ℓ = hs.idxOf? ℓ
                                        (the nearest enclosing handler for ℓ; frames before it are skipped)
  {thunk}                          →  body lowered under the CURRENT hs  (caps fixed at AUTHOR site)
  no handler for ℓ in hs           →  LOWERING ERROR = capability escape (case B)
```

## Why `cap = idxOf? ℓ` is right

`staticSplit` counts only `handleF` frames (non-handler frames are transparent). `hs` lists exactly the
enclosing handlers, innermost first. So the index of `ℓ` in `hs` is the number of intervening handlers =
the cap. Examples (all build-gated `#guard`s):
- `state 0 in (put 7; get)` — get under its state, `hs=[state]`, cap **0**.
- `handle (atomically (… raise 100))` — raise reaches PAST the transaction to throws: `hs=[stm, exn]`,
  `idxOf exn = ` **1**. (This demo was RED under the old `perform 0`-everywhere lowering; the elaborator
  fixes it — `staticSplit 0` would wrongly stop at the transaction.)
- reactive cell `state 0 in (let c = {get} in … $c)` — `{get}` authored under the state, cap **0**;
  re-forcing crosses only `letC` frames (not handlers), so no cap-shift — stays 0, resolves to state.

## Elaborator + kernel = `LWT`, by construction

The elaborator fixes caps at the **author** site (against `hs`); the kernel's `shiftCapFrom`/`substFrom`
**shift** them under `handle` binders as a thunk migrates. Together they realize the two-context `LWT`
discipline: caps always target the lexically-correct handler. **Case B** (a thunk authored with no
enclosing handler, forced under a later one) is a lowering error here — exactly what `LWT` rejects in the
kernel. No v1 rung needs case B (all rungs are case A — audited 2026-06-25).

## Status / integration

Implemented + compiled-green (`lake build Bang.Surface`, 709 jobs). Sits on `Bang/Surface.lean`, which is
INDEPENDENT of the R1 kernel re-index (Operational/Metatheory/Syntax) — merges alongside the pivot. It
also re-greens `Surface.lean`, which was red on `typed-static-b3a` (the old `perform 0` reach-past bug).
Remaining: fold into the full pivot merge; the lowering-error message is minimal (a richer "effect E
escapes its handler" diagnostic is a polish item).
