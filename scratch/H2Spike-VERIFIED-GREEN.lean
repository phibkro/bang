/-! ### THROWAWAY DESIGN-PROBE (#97 item 2, mutual let rec) — NOT for commit, reverted after run.
Generalizes `buildLetRec` from a single self-knot `Rec = μX. Thunk(X → T)` to a PAIR self-knot
`Rec2 = μX. Thunk(X → T1 * T2)`, built by hand at the `Surf` level to test the encoding end-to-end
before any parser/elaborator change (this file's internal `synthSC`/`runInferC` are needed, hence
inline here rather than an external scratch module). -/
namespace H2MutRecSpike
def fnTy : Ty := .tArr .tInt .tInt
def pairTy2 : Ty := .tProd fnTy fnTy
def recTy2 : Ty := .tMu (.tThunk (.tArr (.tVar 0) pairTy2))
def knotBody2 (sv : String) : Surf :=
  .lett "#g" (.unfoldS (.var sv)) (.app (.force (.var "#g")) (.foldS (.var "#g")))
def evenBody : Surf :=
  .lam "n" (.lett "#c" (.binopS .eq (.var "n") (.lit 0))    -- A-normalize the if-condition (#41)
    (.ifS (.var "#c")
              (.lit 1)
              (.lett "#n1" (.binopS .sub (.var "n") (.lit 1))     -- A-normalize the app argument (#41)
                (.app (.force (.var "odd")) (.var "#n1")))))
def oddBody : Surf :=
  .lam "n" (.lett "#c" (.binopS .eq (.var "n") (.lit 0))
    (.ifS (.var "#c")
              (.lit 0)
              (.lett "#n1" (.binopS .sub (.var "n") (.lit 1))
                (.app (.force (.var "even")) (.var "#n1")))))
-- `evenThunk sv`/`oddThunk sv`: each is a THUNK that, when forced, re-derives the PAIR from the
-- self-knot `sv` and projects out its own half — this is `buildLetRec`'s "name bound to a re-
-- entrant thunk over #self" move, generalized to 2 names via one shared pair-producing knot.
def evenThunk (sv : String) : Surf :=
  .lett "#p" (.force (.thunk (knotBody2 sv)))
    (.splitS "#e" "#o" (.var "#p") (.force (.var "#e")))
def oddThunk (sv : String) : Surf :=
  .lett "#p" (.force (.thunk (knotBody2 sv)))
    (.splitS "#e" "#o" (.var "#p") (.force (.var "#o")))
-- ASCRIBE each self-referential thunk explicitly (`.annotS _ (.tThunk fnTy)`) — mirrors
-- `letRecS`'s mandatory `: T` annotation (ADR-0073): HM can't infer THROUGH a self-reference
-- without a known type breaking the circularity (`even`'s RHS mentions `odd`, `odd`'s mentions
-- `even`; unascribed, `.lett`'s HM generalize path has nothing to unify against until BOTH exist).
def inner2 : Surf :=
  .annotS
    (.lam "#self"
      (.lett "even" (.annotS (.thunk (evenThunk "#self")) (.tThunk fnTy))
        (.lett "odd" (.annotS (.thunk (oddThunk "#self")) (.tThunk fnTy))
          (.pairS (.thunk evenBody) (.thunk oddBody)))))
    (.tArr recTy2 pairTy2)
def recVal2 : Surf := .annotS (.foldS (.thunk inner2)) recTy2
def outerAndBody2 (tailUsing : Surf) : Surf :=
  .lett "#rec" recVal2
    (.lett "even" (.annotS (.thunk (evenThunk "#rec")) (.tThunk fnTy))
      (.lett "odd" (.annotS (.thunk (oddThunk "#rec")) (.tThunk fnTy))
        tailUsing))
def progEven10 : Surf := outerAndBody2 (.app (.force (.var "even")) (.lit 10))
def progOdd10 : Surf := outerAndBody2 (.app (.force (.var "odd")) (.lit 10))
def progEven7 : Surf := outerAndBody2 (.app (.force (.var "even")) (.lit 7))
def progEven0 : Surf := outerAndBody2 (.app (.force (.var "even")) (.lit 0))
def progEven1 : Surf := outerAndBody2 (.app (.force (.var "even")) (.lit 1))
def runFull2 (fuel : Nat) (p : Surf) : Option Int :=
  match (do
      let _ ← runInferC (synthSC [] p) []
      Bang.Surface.lower p) with
  | .ok c => (match Source.eval fuel c with | .done (.vint n) => some n | _ => none)
  | .error _ => none

-- H2 TYPES + RUNS end-to-end, on BOTH projections out of the SAME shared knot:
#guard runFull2 5000 progEven0  == some 1
#guard runFull2 5000 progEven1  == some 0
#guard runFull2 5000 progEven10 == some 1
#guard runFull2 5000 progOdd10  == some 0
#guard runFull2 5000 progEven7  == some 0

-- FALSIFIER: a NAIVE (non-fixpoint) mutual pair via splitS — even/odd bound directly as a pair
-- of closures, no self-knot — is REJECTED at LOWER time ("unbound variable: odd"), confirming
-- true mutual forward-reference genuinely needs the fixpoint (siblings aren't in scope of each
-- other's bodies without one; a plain pair-split can't back-reference its own binders).
def bareEvenBody : Surf :=
  .lam "n" (.lett "#c" (.binopS .eq (.var "n") (.lit 0))
    (.ifS (.var "#c") (.lit 1)
      (.lett "#n1" (.binopS .sub (.var "n") (.lit 1))
        (.app (.force (.var "odd")) (.var "#n1")))))
def bareOddBody : Surf :=
  .lam "n" (.lett "#c" (.binopS .eq (.var "n") (.lit 0))
    (.ifS (.var "#c") (.lit 0)
      (.lett "#n1" (.binopS .sub (.var "n") (.lit 1))
        (.app (.force (.var "even")) (.var "#n1")))))
def bareProg (n : Int) : Surf :=
  .splitS "even" "odd" (.pairS (.thunk bareEvenBody) (.thunk bareOddBody))
    (.app (.force (.var "even")) (.lit n))
#guard (match Bang.Surface.lower (bareProg 0) with
        | .error m => (m.splitOn "unbound variable").length > 1
        | .ok _    => false)
-- differential vs the hand-fused single-function equivalent (the status-quo workaround shape)
def fusedBody : Surf :=
  .lam "p" (.lam "n"
    (.lett "#c" (.binopS .eq (.var "n") (.lit 0))
    (.ifS (.var "#c")
      (.binopS .sub (.lit 1) (.var "p"))
      (.lett "#p1" (.binopS .sub (.lit 1) (.var "p"))
        (.lett "#n1" (.binopS .sub (.var "n") (.lit 1))
          (.app (.app (.force (.var "fused")) (.var "#p1")) (.var "#n1")))))))
def fusedRecTy : Ty := .tMu (.tThunk (.tArr (.tVar 0) (.tArr .tInt (.tArr .tInt .tInt))))
def fusedInner : Surf :=
  .annotS (.lam "#self" (.lett "fused" (.thunk (knotBody2 "#self")) fusedBody))
          (.tArr fusedRecTy (.tArr .tInt (.tArr .tInt .tInt)))
def fusedRecVal : Surf := .annotS (.foldS (.thunk fusedInner)) fusedRecTy
def fusedProg (p n : Int) : Surf :=
  .lett "#rec" fusedRecVal
    (.lett "fused" (.thunk (knotBody2 "#rec"))
      (.app (.app (.force (.var "fused")) (.lit p)) (.lit n)))
#guard runFull2 5000 (fusedProg 0 10) == runFull2 5000 progEven10
#guard runFull2 5000 (fusedProg 1 10) == runFull2 5000 progOdd10
#guard runFull2 5000 (fusedProg 0 7)  == runFull2 5000 progEven7
end H2MutRecSpike

end Bang.TypeCheck

