/- scratch/PlugMintWall.lean — inc-5 Phase-1 WALL confirmation (build-grounded).
   Under ADR-0055 minting, `run_plug`'s induction step is FALSE for handle frames:
   `wrapStep` drops the stored id, and re-stepping `handle h c` MINTS a fresh id +
   substitutes the new capability into the body. -/
import Bang.Operational
namespace Bang.PlugMintWall
open Bang

def c : Comp := Comp.ret Val.vunit

-- What `run_plug`'s `hwrap` (LR:212) NEEDS (reproduce the id-4 frame, counter unchanged):
--   Source.step (7, [], wrapStep (handleF 4 h) c) = some (7, [handleF 4 h], c)
-- What `Source.step` ACTUALLY produces — proven by `rfl`: id 7 minted (not 4), counter 8,
-- and `vcap 7` substituted into the body. The two are visibly different ⇒ `hwrap` is false.
example :
    Source.step (7, [], Frame.wrapStep (Frame.handleF 4 (Handler.throws 1)) c)
      = some (8, [Frame.handleF 7 (Handler.throws 1)], Comp.subst (Val.vcap 7 1) c) := rfl

end Bang.PlugMintWall
