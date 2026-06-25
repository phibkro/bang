# 0053 — Absolute (root-level) caps dissolve the shift wall; LR seam 5→2

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: GO on **absolute/level caps** — the `perform` cap is a ROOT-LEVEL (from the program root / stack bottom; `lvl=0` = outermost handler), NOT a de-Bruijn outward index. Crossing a `handle` does NOT shift the cap (`Comp.subst` leaves it unchanged), which **dissolves the de-Bruijn shift wall (ADR-0050) BY CONSTRUCTION**: `closeC_handle*` rewrite to the UNSHIFTED `closeC δ M`, so the 3 `crelK_fund` handler arms close on their LANDED `compatK_handle*` cores — **LR seam 5→2** (only `hcatch` + `:1801` remain as ADR-0043 descents). Runtime dispatch resolves the level via `absSplit K cap = staticSplit K (handlerCount K - 1 - cap)` (the conversion modulus self-adjusts under stack mutation — the `+1` the shift threaded is absorbed). The WC/`LWT`/`progress` cap-resolution re-keys to `absResolvesKind`; the **WC keystone** (`WCComp.shiftCap_insert` general-Δ insert) reformulation is the one **kernel-engineer-paired 2c** piece still seamed. Frozen-statement-free for the 5→2. Supersedes ADR-0050's "defer the representation fix."
- **Amends**: 0050
- **Depends-on**: 0045, 0046, 0050
- **See-also**: 0052

## Status
Accepted (2026-06-25, operator ratification of the cap-representation feasibility spike). The 5→2 is
**landed + axiom-gated** (below); the WC-keystone 2c is a separate, deliberate, kernel-engineer-paired
unit. CalcVM is the orthogonal deferred route-B (ADR-0052), unaffected by this decision.

## Context

ADR-0050 build-refuted the env cap-shift cancellation the 3 handler arms needed and shipped the LR at
**seam-5**, identifying the root cause as the **de-Bruijn cap SHIFT** (ADR-0046: crossing a `handle`
bumps caps via `Val.shiftCap`) — a bang-specific artifact with no Biernacki proof to inherit. It deferred
the real 5→2/full-close to a representation-change feasibility spike (absolute caps, or named handlers).

The spike (`findings-cap-representation` + the de-risk probes `scratch/AbsoluteCaps{,Step}Probe.lean`)
returned **GO on absolute caps**, build-grounded:
- The shift dissolves by construction (`abs_handle_no_shift`: `subst`'s handle arm fills the body with
  the filler UNCHANGED). The config-simulation `(handleF h :: K, shiftCap c) ≈ (K, c)` that walled
  routes A/B becomes `(handleF h :: K, c) ≈ (K, c)` — `shiftCap = id`.
- The level↔index dispatch invariance is discharged sorry-free against the real kernel
  (`absSplit_stable_under_top_push` / `migration_no_shift_needed`): a root-level resolves to the SAME
  handler across a top-`handleF` PUSH (migration), because the conversion modulus `handlerCount - 1 - lvl`
  absorbs the `+1` the de-Bruijn shift threaded.
- Cost measured near-zero where feared: **CalcVM/Compile ignore the cap** (label-dispatched), so the
  representation change has ZERO blast radius there; the STD block is **net DELETION + SIMPLIFY** (the
  shift commutation theory and the `HasVTy/HasCTy.shiftCap` re-typing theorems are deleted; the 6 STD
  handle arms simplify to close like `letC`/`perform`).
- No 6th primitive; the cap stays a `Nat` (only its counting origin changes); set-rows untouched.

## Decision

**Caps are ABSOLUTE root-levels (Shape A: conversion-at-boundary).** `staticSplit`/`CapResolves`/
`CapResolvesKind` stay byte-identical (top-indexed internally); the cap field's *meaning* flips to a
root-level, `subst` stops shifting, and dispatch + the WC/`LWT` author-site discipline convert via the
modulus (`absSplit`, `absResolves`, `absResolvesKind`). This is the **smallest** change that dissolves
the wall — it spares the ~87 Metatheory / 72 Operational `CapResolves`/`staticSplit` internals that a
"re-key staticSplit to count from root" (Shape B) would touch.

### Why root-level is SOUND
A cap-carrying thunk **cannot escape its handler** (the `LWT` return-escape gate, ADR-0045 (D) /
`preservation_returnEscape_TODO`), so a pending `perform`'s target handler is always still on the stack
when it fires; migration only pushes handlers ABOVE the target, never pops below it. The kernel runs only
CLOSED configs (`Source.eval` loads `([], c)`), so stack-bottom = program root = a well-defined anchor.
Author-site assignment for OPEN terms is the shell elaborator's job (the downstream consistency
requirement: the elaborator must emit root-level caps to match).

## The double-duty consequence (a genuine semantic shift — pinned)

The de-Bruijn shift was doing **DOUBLE DUTY**:
1. **Correctness for well-typed migration** — KEPT under absolute caps (via the conversion modulus).
2. **An *incidental* runtime backstop** — it bumped an ill-typed capability-ESCAPE's cap out of range,
   so the escape ran STUCK. DROPPED under absolute caps (no shift → the escaped cap resolves silently;
   the program TERMINATES instead of getting stuck).

**Type safety is unaffected:** escape-safety always rode the **typing** non-escape property (`LWT` rejects
the escape — `escapeM_ill_typed`/`progB_ill_typed` STILL hold under absolute caps; the rejection is the
return-context discipline, dispatch-direction-independent). The runtime stuck→terminates shift is
**don't-care** for an ill-typed program. The `LWRegress` regression oracle moved accordingly: the old
`#guard progB_stuck` pinned a *representation artifact*, not a safety property; it is retired in favour of
`progB_ill_typed` (the surviving invariant). The well-typed `capMigrate` guards (→ 5/9) are preserved
verbatim.

**Consequence flagged:** `preservation_returnEscape_TODO`'s priority ROSE. Under de-Bruijn, a
typing-slipping escape would have STUCK (a runtime net); under absolute caps it resolves silently, so that
sorry is now the **sole** line for escape behaviour. Closing it is higher-priority than before.

## Consequences

- **LR seam 5→2 — LANDED + AXIOM-GATED.** The 3 `crelK_fund` handler arms (`compatK_handle{Throws,
  State,Transaction}`) close on their cores. `#print axioms`: the 3 cores are axiom-clean
  `[propext, Classical.choice, Quot.sound]`; `crelK_fund`/`lr_fundamental`/`lr_sound` trace `sorryAx`
  SOLELY to the 2 remaining ADR-0043 descents (`hcatch` + `:1801`) — verified no keystone/progress-seam
  leak (Compat has zero `WCComp` refs; the arm cores are clean).
- **Deleted (net-negative):** the `shiftCapFrom` commutation theory + `Val.CapClosed`/`CapScopedIn`
  (route-A, ADR-0050-dead) in Compat; `HasVTy/HasCTy.shiftCap` re-typing theorems in Metatheory.
- **Simplified:** the 6 STD handle arms (`subst_gen` + preservation) drop `shiftCap`; `closeC_handle*`
  rewrite unshifted.
- **Added:** `handlerCount`, `absSplit`, `absResolves`, `absResolvesKind` + the level↔index bricks
  (`staticSplit_isSome_iff_lt`, `absSplit_stable_under_top_push`, `krelS_handlerCount_eq`).
- **WC-keystone 2c — SEAMED; a genuine WC-invariant DESIGN problem (kernel-engineer-paired).**
  `WCComp.shiftCap_insert` (restated shift-free) carries a documented `sorry`. **Build-traced finding:**
  `absResolvesKind`-based well-cappedness is **NOT preserved under handler insertion BELOW the use-site**.
  Inserting `handleF h` below an existing `handleF h₀` shifts `h₀`'s absolute root-level, so a `perform`
  targeting `h₀` (e.g. inside a thunk's own `handle h₀ …`) mis-resolves to `h` after the insert
  (Lean-checked: level `handlerCount Sg` resolves to `h₀` in `handleF h₀ :: Sg` but to `h` in
  `handleF h₀ :: handleF h :: Sg`). `absSplit_stable_under_top_push` only covers caps targeting handlers
  BELOW the inserted frame; caps targeting ABOVE it break. The de-Bruijn `shiftCap` compensated exactly
  this (it re-based the internal caps); absolute caps remove the compensation. **This is NOT a mechanical
  re-proof** — it needs a different WC formulation (e.g. caps stored relative to the nearest enclosing
  handler; or WC stated so insertion only ever happens above all caps' targets; or stored-thunk
  cap-closedness revisited). The `WCComp.substFrom` consumer's specific need (the FILLER `v` at Δ=[], caps
  targeting `Sg`) is the SAFE case — but the keystone's general recursion into thunk-internal handles hits
  the unsafe case. The consumer seam (Stage-2a) is discharged; the keystone proof carries the 2c seam. It
  feeds only `WellCapped → LWConfig → preservation/progress`, behind `preservation_returnEscape_TODO`; the
  LR 5→2 is independent (Compat has zero `WCComp` refs).
- CalcVM stays RED (deferred route-B, ADR-0052) — orthogonal; the cap is label-dispatched there.

## Rejected alternatives

- **Named handlers (ADR-0044).** The representation where this is a non-problem (names don't shift) and
  the only candidate that closes 5→0 by construction — but a substrate change (Core/Syntax), a re-derived
  VM (HIGH cost, opposite of absolute caps' ZERO), and a **possible 6th primitive** (Option B direct
  dispatch, unresolved). Post-v1, the principled future direction. (Capability-as-value collapses into it.)
- **Shape B (re-key `staticSplit` to count from the root).** Touches all ~159 `CapResolves`/`staticSplit`
  internals; Shape A (convert-at-boundary) leaves them byte-identical. Rejected as larger for no gain.
- **Stay seam-5 (ADR-0050).** The do-nothing baseline; superseded — absolute caps dissolve the wall at a
  measured net-negative cost.

## See also
- `findings-cap-representation` (the spike — not committed; captured in the team report) + the de-risk
  probes `scratch/AbsoluteCapsProbe.lean`, `scratch/AbsoluteCapsStepProbe.lean` (committed `20fa7ab`).
- ADR-0052 (CalcVM route-B, orthogonal); ADR-0050 (the seam-5 this supersedes); ADR-0046 (de-Bruijn caps).
- `Bang/Compat.lean` `crelK_fund` (the closed handler arms + the 2 deferred descents);
  `Bang/Operational.lean` `absSplit`/`absResolvesKind` + the seamed `WCComp.shiftCap_insert` (2c).
