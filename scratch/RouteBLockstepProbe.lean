/-
U3 LOCKSTEP DE-RISK (inc-6) — refute-first check of the CalcVM route-B BRIDGE invariant.

The §4 spike (RouteBShadowProbe) showed identity-keyed `evalD'` agrees with the kernel on the
OBSERVABLE VALUE. This probe checks the next, harder thing the bridge proof needs: the STEP-WISE
`Corr`-lockstep — the kernel's frame-projection equals the identity-keyed store at EVERY dispatch
point, not just at the end. If this holds on the §2b put-outer/get-inner witness, the
`CtxCorr`/`run_evalD` bridge is well-founded; if the projection ever diverges, that is a route-B
refutation (a finding), not a failure.

The invariant under test (the bridge's `Corr` analog):
  `frameProj (kernel EvalCtx at config c) = evalD-store when evaluating c.focus`
where `frameProj` reads the kernel's `handleF n (state ℓ v)` frames IDENTITY-keyed (n ↦ v) — exactly
how route-B's `evalD` keys its `SStore`. The kernel mutates state by REINSTALLing `handleF n (state ℓ v')`
(deep handler), so `frameProj` tracks the mutation in place.
-/
import Bang.Operational

namespace RouteBLockstepProbe
open Bang

/-- Identity-keyed projection of the kernel's `EvalCtx` state-frames — the `Corr`/`CtxCorr` analog the
bridge proof must maintain (`frameProj K = evalD σ`). Innermost first, mirroring `SStore`. Observed as
`(identity, Int)` so it prints / `#guard`s. -/
def frameProj : EvalCtx → List (Nat × Int)
  | []                                  => []
  | .handleF n (.state _ (.vint v)) :: K => (n, v) :: frameProj K
  | _ :: K                              => frameProj K

/-- Step the kernel until the focus is a `perform`, returning that config (or none). -/
def stepToPerform : Nat → Config → Option Config
  | 0,    _   => none
  | f+1,  cfg =>
      match cfg.2.2 with
      | .perform _ _ _ => some cfg
      | _              => match Source.step cfg with
                          | some cfg' => stepToPerform f cfg'
                          | none      => none

/-- One `Source.step` past the current perform, then on to the next perform. -/
def nextPerform (f : Nat) (cfg : Config) : Option Config :=
  match Source.step cfg with
  | some cfg' => stepToPerform f cfg'
  | none      => none

def projOf  (c : Option Config) : List (Nat × Int) := match c with | some cfg => frameProj cfg.2.1 | none => []
/-- The dispatched cap's IDENTITY and op at a perform config (the lexically-named handler). -/
def dispatchOf (c : Option Config) : Option (Nat × String) :=
  match c with | some (_, _, .perform (.vcap n _) op _) => some (n, op) | _ => none

/-! ## The §2b witness — PUT via outer cap, GET via inner cap. -/
def w2b : Comp :=
  .handle (.state 1 (.vint 10)) (.handle (.state 1 (.vint 20))
    (.letC (.perform (.vvar 1) "put" (.vint 99))
           (.perform (.vvar 1) "get" .vunit)))

def cPut : Option Config := stepToPerform 50 (0, [], w2b)
def cGet : Option Config := nextPerform 50 (cPut.getD (0, [], w2b))

def kInt (r : Bang.Result Val) : Option Int := match r with | .done (.vint n) => some n | _ => none

/-! ## The lockstep, build-gated. At EVERY dispatch point the kernel's identity-keyed frame-projection
equals the store route-B's `evalD` maintains — the `CtxCorr`/`Corr` invariant, exhibited concretely.

  PUT point: dispatched via the OUTER cap (identity 0); store = both cells at their seed values.
  GET point: dispatched via the INNER cap (identity 1); the outer put LANDED ON CELL 0 (→99), the
             INNER cell (1) is UNTOUCHED (still 20) — identity dispatch, NOT nearest-label. -/
#guard dispatchOf cPut == some (0, "put")        -- PUT resolves the OUTER handler's identity
#guard projOf     cPut == [(1, 20), (0, 10)]     -- frameProj = evalD σ (seed): inner 20, outer 10
#guard dispatchOf cGet == some (1, "get")        -- GET resolves the INNER handler's identity
#guard projOf     cGet == [(1, 20), (0, 99)]     -- frameProj = evalD σ: OUTER mutated to 99, INNER intact
#guard kInt (Source.eval 50 w2b) == some 20      -- ⇒ the GET reads the untouched inner cell: 20

end RouteBLockstepProbe
