# 0050 — The LR handler-arm cancellation is build-refuted; v1 ships LR seam-5

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The env cap-shift cancellation that the 3 `crelK_fund` handler arms (`compatK_handle{Throws,State,Transaction}`) need is BUILD-REFUTED. Its U-clause reduces to a config-simulation `(handleF h :: K, shiftCap c) ≈ (K, c)` that walls at the state/txn resume. Root cause: this is a bang-SPECIFIC artifact of the de-Bruijn cap representation (ADR-0046) — crossing a `handle` SHIFTS caps (`Val.shiftCap`); Biernacki's named-handler `n-free` never has this obligation, so there is no proof to inherit. Both attempted carriers — A (LR `LWStack`-fold, the operator's committed route) and B (standalone config-simulation) — share this ONE wall. v1 ships the LR with the 3 arms as ADR-0043 seam descents (seam-5); the real 5→2/full close is a REPRESENTATION change (absolute/level caps, or named handlers ADR-0044) deferred to a feasibility spike.
- **Amends**: 0043, 0045
- **Depends-on**: 0043, 0044, 0045, 0046

## Status
Accepted (2026-06-25, operator ruling). The seam is a v1 SCOPE decision: the LR layer
(LR/Compat/Spec) is the verified core; the 3 handler arms are explicit, documented descents,
not silent gaps. The representation fix is a separate, deliberate effort.

## Context

ADR-0045 pivoted to a typed LR + static (capability) dispatch and committed to the Biernacki
route — putting back the `n-free` well-bracketing predicate (carried in `KrelS`) that the
PATH believed bang had "dropped when it swapped labels for de-Bruijn caps." The `crelK_fund`
proof leaves 3 handler arms RED (`Compat.lean` `compatK_handle{Throws,State,Transaction}`):
the IH gives `CrelK n (F q A) e (closeC δ M)`, but `closeC_handle*` rewrites the goal to demand
`closeC (δ.map Val.shiftCap) M` — the body closes over the CAP-SHIFTED fillers, because crossing
the `handle` cap-binder bumps every ambient cap (`Val.shiftCapFrom`, ADR-0046 representation).

The committed plan (PATH `typed-lr-reindex`, the "5→2 win"): carry `LWStack` in `KrelS` so the
env-shift cancellation discharges, closing the 3 arms LR-only.

## Decision

**The cancellation is build-refuted. v1 ships LR seam-5.** Established by a build-gated de-risk
(scratch, no frozen-def edits) BEFORE any 60-site spread:

1. **The cancellation building block LANDS** — `staticSplit_insert_ge` (`Metatheory.lean`, commit
   `7c781cf`, axiom-clean): inserting `handleF h` at handler-depth `|Δ|` and bumping an ambient cap
   resolves to the SAME handler — the dynamic sibling of `CapResolvesKind.insert`. Reusable for the
   representation spike.

2. **Stack-side `LWStack` is INSUFFICIENT.** The 3 arms' obligation reduces (U-clause of
   `VrelK`-shiftCap-stability) to `CrelK j B φ c c' → CrelK j B φ (shiftCap c) (shiftCap c')`, i.e.
   `∀ K₁ K₂, KrelS … → CoApproxC_le (K₁, shiftCap c) (K₂, shiftCap c')`. The cancellation needs the
   consumed stack `K₁` handleF-HEADED to absorb the `perform 0→1` bump — which `LWStack K₁` does NOT
   force (it is per-frame cap-discipline, not "head is a handler").

3. **A focus-side premise is a FALSE FLOOR.** Adding `WCComp (handlersOf K) c` gives the shifted
   focus's STATIC well-cappedness for free (keystone `WCComp.shiftCap_insert`) but leaves the DYNAMIC
   residual untouched: the config-simulation `(handleF h :: K, shiftCap c) ≈ (K, c)`. That has no
   lemma and **walls at the state/txn resume** — the resume reinstalls the handler and returns the
   UNSHIFTED stored `s`/cells, so re-syncing the simulation needs `shiftCapFrom |Kᵢ| s = s`
   (cap-closedness), which is FALSE for a general resumptive state (the stored value is only
   de-Bruijn-closed, `Val.Closed`, not `Val.CapClosed` — and route-A-CapClosed was itself
   build-refuted earlier this saga).

4. **A and B share ONE wall.** The env-shift carrier (A) merely relocates the obligation to
   `EnvRelK_shiftCap`, whose U-clause IS the same config-simulation that the standalone route (B)
   could not complete through state/txn. They are not independent.

**Root cause (corrects the PATH's central diagnosis):** the shiftCap obligation is a bang-SPECIFIC
artifact of the de-Bruijn cap representation (ADR-0046, `perform cap`; `handle` shifts caps).
Biernacki uses NAMED handlers, which do NOT shift on `handle`-crossing — so Biernacki's `n-free`
never carries a shiftCap obligation. `n-free` is well-bracketing for NAMES; bang's wall is the
de-Bruijn SHIFT. Putting `n-free` back does not help — **there was never a Biernacki proof to
inherit here.**

## Consequences

- v1's LR layer is **seam-5**: the 3 handler arms + the `hcatch` (ADR-0043) + `:1801` resume edges
  ride as documented descents. `#print axioms lr_sound`/`lr_fundamental` trace `sorryAx` only to
  that descent set (no NEW sorry; `crelK_fund` = `[propext, sorryAx, Classical.choice, Quot.sound]`).
- The `staticSplit_insert_ge` brick + the `compatK_handle*` cores + `closeC_handle*` are LANDED and
  load-bearing for whichever representation the spike picks.
- The frozen `lr_sound`/`lr_fundamental` STATEMENTS are UNCHANGED (the operator-approved `ctxApprox`
  `LWStack C` premise was REVERTED with the dead A attempt — it bought nothing once A was refuted).

## Rejected alternatives

- **A — LR `LWStack`-fold (the committed Biernacki route).** Build-refuted (this ADR). Stack-side
  insufficient; focus-side a false floor. NOT pursued to the 60-site spread — refuted at the crux.
- **B — standalone config-simulation `(handleF h :: K, shiftCap c) ≈ (K, c)`.** Same state/txn wall.
- **Absolute / level caps** (cap from root, not de-Bruijn from use-site): dissolves the shift (no
  cancellation obligation) but BALLOONS into the axiom-clean STD block (`Val.shiftCap` is woven
  through `preservation`'s handle arms + `staticSplit`/migration-soundness + CalcVM/Compile cascade).
  A KERNEL change — deferred to a feasibility spike.
- **Named handlers** (ADR-0044, Koka/Lexa/Effekt): the representation where this is a NON-problem
  (names don't shift). A different kernel + post-v1 (ADR-0044 records it as a future direction).
- **Cap-closed fillers** (`shiftCap v = v`, the `EnvRelK` comment's original intent): DEAD —
  route-A-CapClosed build-refuted (`EnvRelK` cannot carry it; the stored values are not cap-closed).

## See also
- `paths/archive/PATH-typed-lr-reindex.md` (the CROSSROADS + the de-risk audit trail)
- `Bang/Core/Soundness.lean` `staticSplit_insert_ge` (the landed brick)
- `Bang/Meta/BinaryLR.lean` `crelK_fund` handler arms (the seam descents) + `compatK_handle*` cores
