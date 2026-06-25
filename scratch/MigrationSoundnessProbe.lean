/-
Migration-soundness crux probe (ADR-0053 option (c), the deciding build-test).

QUESTION: does typing/LWConfig exclude the below-insert migration, or is there a real soundness gap?
FACT (Syntax.lean:163): `HasCTy.perform` leaves `cap` UNCONSTRAINED — plain typing accepts any cap.
So cap-correctness lives only in the structural `LWConfig`/`LWT` invariant. The crux is whether
`LWConfig` is PRESERVED across a β-step that migrates a "fragile" thunk under a fresh handler.

Witness `prog`: a CLOSED program that is LWConfig-valid at the start. Its argument `vFragile` is a
thunk that locally handles its OWN `state 1` and performs `get` on it with cap 0 (correct while the
ambient is empty). One β-step migrates it UNDER a `throws 2` handler (`force` it inside `handle throws`).
Intended result: `get` reads the thunk's own state → 7. Under absolute caps with cap 0, after migration
`get` resolves to the OUTERMOST handler (the throws), which does not handle `get`.

  prog ≡  (λx. handle (throws 2) (force x))  vFragile
  vFragile ≡  { handle (state 1 (vint 7)) (perform 0 1 "get" unit) }

If `Source.eval prog ≠ done 7`, absolute caps have a genuine LWConfig-preservation gap (the WORSE
case): option (c) cannot be just a typing premise. The `capCorrect` variant (cap 1, accounting for the
throws below) shows the SAME program is sound with the migration-aware cap — i.e. the issue is that a
single absolute cap cannot be portable across force sites.
-/
import Bang.Operational

namespace Bang
open Frame

private def vFragile : Val :=
  .vthunk (.handle (.state 1 (.vint 7)) (.perform 0 1 "get" .vunit))

private def vCapCorrect : Val :=
  .vthunk (.handle (.state 1 (.vint 7)) (.perform 1 1 "get" .vunit))  -- cap 1: skips the throws below

private def migrate (v : Val) : Comp :=
  .app (.lam (.handle (.throws 2) (.force (.vvar 0)))) v

/-- Classify the run result as an Int, or a tag for stuck/oom/non-int. -/
private def runTag (fuel : Nat) (c : Comp) : String :=
  match Source.eval fuel c with
  | .done (.vint n) => s!"done {n}"
  | .done _         => "done(non-int)"
  | .stuck          => "STUCK"
  | .oom            => "oom"

-- Intended answer for BOTH is 7 (get reads the thunk's own state). Watch which one mis-evaluates.
#eval runTag 200 (migrate vFragile)      -- cap 0: expected to MIS-evaluate under absolute caps
#eval runTag 200 (migrate vCapCorrect)   -- cap 1 (migration-aware): expected `done 7`

-- Control: the SAME fragile thunk forced with NO migration (ambient empty) — cap 0 is correct here.
#eval runTag 200 (.force vFragile)


/- DECISIVE: is the START config LWConfig-valid? If it proves, `migrate vFragile` is a well-typed
(HasCTy.perform cap-unconstrained) + LWConfig-valid program that mis-evaluates → a genuine
preservation gap (worse case). -/
example : LWConfig ([], migrate vFragile) := by
  simp only [migrate, vFragile, LWConfig, LWStack, handlersOf, retCtx, LWT, LWVal, LWHandler,
    absResolvesKind, CapResolvesKind, handlerCount, handlesOp]
  decide
end Bang
