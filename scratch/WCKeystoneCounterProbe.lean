/-
WC-keystone 2c counterexample probe (ADR-0053, option (c) scoping).

BUILD-GATED CLAIM: under absolute caps, a `perform`'s cap mis-resolves when a handler is inserted
BELOW its target (the `shiftCap_insert`/migration property is FALSE). And this hits the dispatch
mechanism (`absSplit`) that BOTH the dead `WCComp` AND the live `LWT` resolve through identically —
so LWT's two-context (S,R) split does NOT already provide option (c)'s migration-stability (the
R-context governs RETURN-escape; `perform` resolves against S via the SAME `absSplit`). Hence:
  • option (c) needs a NEW migration-stability invariant on the LIVE LWConfig path, and
  • the `WCComp.shiftCap_insert` keystone is on the dead `WellCapped` path.

Witness: cap 0 (= outermost level) targeting an inner `state 1` handler. Insert `throws 2` BELOW it
(stack `[state1]` ↦ `[state1, throws2]`, i.e. throws becomes the new outermost). The state shifts to
level 1, but cap 0 stays 0 → now resolves to `throws 2`, which does NOT handle `(1,"get")`.
-/
import Bang.Operational

namespace Bang
open Frame

/- BEFORE insert: cap 0 over `[handleF (state 1 _)]` resolves to the state handler (label 1). -/
#guard ((absSplit [handleF (Handler.state 1 (.vint 0))] 0).map (fun x => x.2.1.label)) == some 1

/- AFTER inserting `throws 2` BELOW (new outermost): the SAME cap 0 now resolves to `throws 2`
(label 2) — the mis-resolution. `state` shifted to level 1; cap 0 did not follow it. -/
#guard ((absSplit [handleF (Handler.state 1 (.vint 0)), handleF (Handler.throws 2)] 0).map
          (fun x => x.2.1.label)) == some 2

/- The kind-match the invariants actually check: BEFORE insert, cap 0 resolves to a handler that
HANDLES `(1,"get")`; AFTER the below-insert it resolves to one that does NOT. This is the literal
`absResolvesKind` predicate `perform` is checked against in BOTH `WCComp` and `LWT`. -/
#guard ((absSplit [handleF (Handler.state 1 (.vint 0))] 0).map
          (fun x => handlesOp x.2.1 1 "get")) == some true
#guard ((absSplit [handleF (Handler.state 1 (.vint 0)), handleF (Handler.throws 2)] 0).map
          (fun x => handlesOp x.2.1 1 "get")) == some false

end Bang
