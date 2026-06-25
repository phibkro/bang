/-
Identity-representation de-risk (ADR-0054, the mechanism) — NO frozen-def edits.

CLAIM: the migration mis-dispatch is fixed by referencing the handler via a GENERATIVE (unique)
IDENTITY and dispatching by MATCH, not by re-counting position. The same `migrate vFragile` stack that
absolute caps mis-resolve (WCKeystoneCounterProbe) resolves CORRECTLY under label-MATCH when labels are
unique — because a match does not re-count under stack growth, so it cannot shift.

Witness stack at the firing `get` (migration: the thunk's OWN inner `state` is now BELOW an unrelated
outer `throws`):  [ handleF (state IN 7) , handleF (throws OUT) ]   (IN inner/innermost, OUT outer/below)
The thunk's `get` carries the capability that names ITS OWN handler = the generative identity `IN`.
-/
import Bang.Operational

namespace Bang
open Frame

/-- generative identities (unique per handle installation) -/
private def IN : Nat := 100   -- the thunk's own inner state handler
private def OUT : Nat := 101  -- the unrelated outer throws

private def stk : EvalCtx := [handleF (Handler.state IN (.vint 7)), handleF (Handler.throws OUT)]

/- ABSOLUTE CAP (the bug): cap 0 = outermost → resolves to the OUTER throws (mis-dispatch). -/
#guard ((absSplit stk 0).map (fun x => x.2.1.label)) == some OUT
#guard ((absSplit stk 0).map (fun x => handlesOp x.2.1 IN "get")) == some false   -- throws can't handle get

/- IDENTITY / label-MATCH dispatch: the capability names `IN` → splitAt MATCHES the inner state,
regardless of the outer throws sitting between the program root and it. NO re-count → NO shift. -/
#guard ((splitAt stk IN "get").map (fun x => x.2.1.label)) == some IN              -- reaches its OWN handler
#guard ((splitAt stk IN "get").map (fun x => handlesOp x.2.1 IN "get")) == some true  -- and it handles get

/- The fix is migration-INVARIANT by construction: insert ANY further handlers below (deeper migration);
the match still finds IN. (absolute caps would shift again each time.) -/
private def stk2 : EvalCtx :=
  [handleF (Handler.state IN (.vint 7)), handleF (Handler.throws OUT), handleF (Handler.throws 102)]
#guard ((splitAt stk2 IN "get").map (fun x => x.2.1.label)) == some IN
#guard ((absSplit stk2 0).map (fun x => x.2.1.label)) == some 102                  -- absolute cap shifts AGAIN

end Bang
