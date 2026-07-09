import Bang.Core.Semantics.Eval
import Bang.Core.Semantics.Dispatch

/-! Probe: does the KERNEL service a "get" performed on a CUSTOM frame whose clause list keys "get"?
If yes, evalD (op-first, raises) and the kernel (identity-first, services) DIVERGE — confirming the
op-priority wall in run_evalD's RAISED part. -/

open Bang

-- a custom frame at identity 0, label 0, with a clause keyed "get" returning `ret (vint 99)`.
def K0 : EvalCtx := [Frame.handleF 0 (Handler.custom 0 Val.vunit [("get", Comp.ret (Val.vint 99))])]

-- perform (vcap 0 0) "get" unit  — the cap's label 0 matches the custom frame's label 0.
#eval (idDispatch K0 0 0 "get" Val.vunit).isSome
-- expect: true  ⇒ the kernel SERVICES it (does NOT return none/raise)

-- Confirm it resumes with the CLAUSE BODY (`ret (vint 99)`), not a raise:
#eval match idDispatch K0 0 0 "get" Val.vunit with
  | some (_, Comp.ret (Val.vint k)) => s!"SERVICED clause ⇒ ret (vint {k})"
  | some _ => "SERVICED (other focus)"
  | none => "NONE (raised)"
-- expect: "SERVICED clause ⇒ ret (vint 99)" ⇒ kernel resumes; evalD (op-first) would RAISE. DIVERGENCE.
