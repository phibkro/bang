module

-- The `#guard`s run COMPILED code (`Source.eval` / `runYieldsInt`) at the META
-- (elaboration) phase, so the modules providing it must be `meta import`ed in
-- addition to the runtime import — the cross-module `#guard` codegen wall
-- (Lean v4.30, Phase-1a finding). Mirrors `Bang/Frontend/NamedCore.lean`:41 and
-- `Bang/Witness/LWRegress.lean`:23.
meta import Bang.Frontend.Surface
public import Bang.Frontend.Surface
-- §C runs the CALCULATED machine `exec ∘ compile` (Bang.CalcVM) as the second
-- engine in the differential `#guard`s. Apex (this file) may import Backend.
meta import Bang.Backend.AbstractMachine
public import Bang.Backend.AbstractMachine
-- §D (issue #95 regression) needs the TYPED elaborator (`let rec`'s `letRecS` desugar
-- lives in `TypeCheck.elabS`/`buildLetRec` — the untyped `Surface.lower` §C already
-- imports cannot reach it, per `TypeCheck.lean`'s own `letRecS` arm: "reaching the
-- checker means elabProg didn't run"). Apex may import Frontend freely.
meta import Bang.Frontend.TypeCheck
public import Bang.Frontend.TypeCheck

/-!
  Bang/Examples.lean — the behavioral-conformance corpus (#80 layer A).
  ────────────────────────────────────────────────────────────────────
  A curated, READABLE set of Bang programs, each paired with a build-gated
  `#guard` that asserts its expected `Source.eval` result. Read top-to-bottom,
  this file IS the language's worked-examples documentation: one line of plain
  English per program, then the machine-checked outcome.

  Every `#guard` runs the COMPILED kernel (`Source.eval`); a false assertion
  FAILS `lake build` — that is the gate (the project oracle, NOT `lake env
  lean`, whose fuel-recursion #eval gives garbage; see
  `lean-eval-reliable-only-compiled`). This is a LEAF consumer: nothing imports
  it, so it is OUTSIDE the soundness/axiom closure (`Bang/Audit.lean` does not
  import it).

  Two assertion idioms, both reused verbatim from `Bang/Frontend/Surface.lean`
  (the single source of the run-pipeline — no new machinery here):

    1. `runYieldsInt fuel "source" n` — parse the surface string, run, check it
       returns `done (vint n)`. PREFERRED where the parser covers the construct.
    2. structural `match Source.eval fuel term with …` on the raw `Result` — for
       μ-stack / handler-escape / non-int outcomes the surface parser cannot build.

  Coverage (one behavior class per `§`): pure let · shadowing · thunk/force ·
  lambda β · exceptions · state (resumptive) · reactive cell · STM commit/abort ·
  sum/case · product/split · μ stack (LIFO) · capability escape (fail-loud).
-/

namespace Bang.Examples

open Bang
open Bang.EffectRow (Label)
-- Reuse the run-pipeline and the Stack/label vocabulary from the surface layer
-- (single source of truth — these are `@[expose] public` there).
open Bang.Surface (runYieldsInt exnLabel stateLabel stmLabel empty push pop)

/-! ## A. Surface-string programs (run via `runYieldsInt`)

Each parses the readable source, runs `Source.eval`, and checks `done (vint n)`. -/

-- A1. PURE LET: a binding sequences; the body reads it. `let x = 3 in x` ⟶ 3.
#guard runYieldsInt 20 "let x = 3 in x" 3

-- A2. LEXICAL SHADOWING: the inner binding of `x` wins; the outer `1` is hidden.
#guard runYieldsInt 20 "let x = 1 in (let x = 2 in x)" 2

-- A3. THUNK / FORCE: `{7}` is a DESCRIPTION (a thunk); `$c` FORCES it to its
-- value. Nothing runs until forced (ADR-0007). `let c = {7} in $c` ⟶ 7.
#guard runYieldsInt 20 "let c = {7} in $c" 7

-- A4. LAMBDA β: applying the identity function to `5` reduces to `5`.
#guard runYieldsInt 20 "(fun x => x) 5" 5

-- A5. EXCEPTION (zero-shot): `raise` aborts to the nearest `handle`, which
-- yields the payload. `handle (raise 7)` ⟶ 7.
#guard runYieldsInt 20 "handle (raise 7)" 7

-- A6. DEEP HANDLER DISCARDS THE CONTINUATION: the `raise` aborts PAST the
-- `let … in 99` frame; the `99` continuation is dropped (zero-shot). ⟶ 7.
#guard runYieldsInt 20 "handle (let z = raise 7 in 99)" 7

-- A7. STATE — GET DEFAULT: with no write, `get` reads the initial cell. ⟶ 5.
#guard runYieldsInt 50 "state 5 in get" 5

-- A8. STATE — RESUMPTIVE (resume-through): `put 7` RESUMES the continuation
-- (unlike `raise`), threading the new cell; the following `get` reads it. ⟶ 7.
#guard runYieldsInt 50 "state 0 in (let z = put 7 in get)" 7

-- A9. REACTIVE CELL (ADR-0005): `c = {get}` is an UNMEMOIZED thunk, so each `$c`
-- RE-SAMPLES the current state. After `put 5` then `put 9`, forcing reads the
-- LATEST write (9) — pull-based reactivity, no `sig`, no kernel change. ⟶ 9.
#guard runYieldsInt 80
  "state 0 in (let c = {get} in (let a = put 5 in (let b = put 9 in $c)))" 9

-- A9b. LEXICAL CAPTURE (ADR-0052): the capability a thunk closes over names its
-- LEXICALLY-enclosing handler, NOT the dynamically-nearest one. `{get}` is built
-- under the OUTER `state 1`; forcing it INSIDE `state 2` still reads the OUTER cell.
-- DYNAMIC (nearest-handler) dispatch would read 2 — it reads 1: dispatch-by-identity
-- realizing lexical scope, the heart of the inc-5/6 soundness story, made observable.
#guard runYieldsInt 80 "state 1 in (let c = {get} in (state 2 in $c))" 1

-- A10. STM COMMIT (ADR-0030): inside `atomically`, allocate a TVar = 100, write
-- 70, read it back — the heap is threaded, the write is visible. ⟶ 70.
#guard runYieldsInt 200
  "atomically (let r = new 100 in (let z = write r 70 in read r))" 70

-- A11. STM ABORT — ALL-OR-NOTHING: an outer `handle` wraps a transaction that
-- writes 70 then `raise`s. The `raise` is foreign to `transaction`, so it
-- ESCAPES the frame (ADR-0023 discards the captured continuation) — the write
-- never commits. The abort payload is the ORIGINAL 100: the rollback witness.
#guard runYieldsInt 200
  "handle (atomically (let r = new 100 in (let z = write r 70 in raise 100)))" 100

-- A12. SUM / CASE (issue #1): `match` discriminates a tagged sum and binds the payload.
-- `Right(7)` is the right injection; the `Right` arm fires, binding `x = 7`. ⟶ 7.
#guard runYieldsInt 20 "match Right(7) { Left(a) -> 0 , Right(x) -> x }" 7

-- A13. PRODUCT / SPLIT (issue #1): `let (a, b) = (3, 4)` destructures a pair, `a` = fst,
-- `b` = snd. Re-pairing swapped `(b, a)` and reading the first proves the binding order. ⟶ 4.
#guard runYieldsInt 20 "let (a, b) = (3, 4) in (let (c, d) = (b, a) in c)" 4

/-! ### A14–A16: ARITHMETIC COMPOSES with the other features (issue #4 × #1/#3/rung-4).

Found by running real programs through `bang` after #4 landed: integer arithmetic threads through
pure binding, the STM ledger, and reactive cells. (Arithmetic in an effect-op ARGUMENT must be
let-bound first — `put (get + 1)` is a value-position arg; see GitHub issue for that rough edge.) -/

-- A14. PURE arithmetic composition: `x² + y²` over two bindings. ⟶ 9 + 16 = 25.
#guard runYieldsInt 30 "let x = 3 in let y = 4 in x * x + y * y" 25

-- A15. STM × ARITHMETIC — the moat with REAL math (rung 3 × #4): a transactional bank transfer that
-- COMPUTES the new balance (`100 - 30`), not a literal post-balance. read → subtract → write → read. ⟶ 70.
#guard runYieldsInt 200
  "atomically (let a = new 100 in (let bal = read a in (let bal2 = bal - 30 in (let z = write a bal2 in read a))))" 70

-- A16. REACTIVE DERIVED CELL × ARITHMETIC (rung 4, ADR-0005 × #4): `c = {get * get}` is an unmemoized
-- thunk computing the SQUARE of the live state. Each `$c` re-samples + recomputes; after `put 9`, forcing
-- reads 9 and squares it. ⟶ 81. Derived reactivity falls straight out of thunks + the δ-rule.
#guard runYieldsInt 80 "state 4 in (let c = {get * get} in (let z = put 9 in $c))" 81

/-! ### A17–A19: arithmetic AS an effect-op argument (issue #26 part-1 — A-normalized lowering).

`put`/`raise`/`write` take value-position arguments, but the lowering now A-normalizes a *computation*
argument (let-bind it, perform on the bound value). So an effectful program reads naturally — no manual
`let`-pyramid to thread the arithmetic out. (Part-2, `read a + 1` directly, still needs the parser
precedence split — see the issue.) -/

-- A17. THE INCREMENTING COUNTER — `put (get + 1)` writes a COMPUTED value back into the cell. The
-- canonical mutable counter, finally one line: read, add one, store. `state N in (put (get+1); get)` ⟶ N+1.
#guard runYieldsInt 80 "state 0 in (let z = put (get + 1) in get)" 1
#guard runYieldsInt 80 "state 41 in (let z = put (get + 1) in get)" 42

-- A18. GUARDED TRANSFER — overdraft check + a computed withdrawal `put (bal - 30)` in the else-branch,
-- no let-binding needed for the arithmetic. balance 100 ≥ 30 ⟹ withdraw ⟹ 70.
#guard runYieldsInt 80
  "state 100 in (let bal = get in (if bal < 30 then bal else (let z = put (bal - 30) in get)))" 70

-- A19. COMPUTED EXCEPTION PAYLOAD — `raise (x * 6)` performs the throw with a *computed* error value;
-- the deep `handle` catches it. x = 7 < 10 ⟹ raise 42 ⟹ caught ⟹ 42.
#guard runYieldsInt 80 "handle (let x = 7 in (if x < 10 then raise (x * 6) else x))" 42

/-! ### A20–A21: an effect op FEEDS the operator chain (issue #26 part-2 — parser precedence).

`raise`/`put`/`new`/`read`/`write` now parse at application precedence (like the atom `get`), so their
result is an operand of `+ - * /` — `read a - 30` is `(read a) - 30`, not a parse error. Combined with
part-1's A-normalized op arguments, arithmetic and effects compose in BOTH directions: an op result INTO
an expression (A20), and a computation INTO an op argument (A21). -/

-- A20. OP RESULT IN AN OPERATOR CHAIN — `read a - 30` reads the TVar (100) and subtracts. Before the
-- precedence fix this was "expected ')', got '-'". atomically ⟹ 100 - 30 ⟹ 70.
#guard runYieldsInt 80 "atomically (let a = new 100 in read a - 30)" 70
#guard runYieldsInt 80 "atomically (let a = new 5 in read a + 1)" 6

-- A21. BOTH FIXES AT ONCE — `write a (read a - 30)`: the op result `read a` feeds `-` (part-2), and the
-- whole computation `read a - 30` is the value-position arg of `write` (part-1, A-normalized). Store the
-- computed balance, read it back: 100 - 30 ⟹ 70. (Also the effect-op-arith example project.)
#guard runYieldsInt 80 "atomically (let a = new 100 in (let z = write a (read a - 30) in read a))" 70

/-! ### A22–A25: `do`-notation (issue #27) — sequential effectful statements, desugaring to nested `letC`.

`x = e` binds (`=`, like `let` — CBPV has no monadic-vs-pure split, so no `<-`), a bare `e` sequences
(value discarded), the last statement is the result. Pure surface sugar; with #26 part-1 the canonical
effectful program reads like imperative code. -/

-- A22. PURE do: binds then a result expression. ⟶ 3 + 4 = 7.
#guard runYieldsInt 30 "do { x = 3; y = 4; x + y }" 7

-- A23. THE EFFECTFUL COUNTER, clean (do × state × #26): read into `x`, write `x + 1` (bare/sequenced),
-- return the cell. Reads like `x = get(); set(x+1); return get()`. ⟶ 6.
#guard runYieldsInt 80 "state 5 in (do { x = get; put (x + 1); get })" 6

-- A24. SEQUENCED bare statements: two `put`s in a row (values discarded), then `get`. ⟶ 9.
#guard runYieldsInt 80 "state 0 in (do { put 5; put 9; get })" 9

-- A25. THE WHOLE STACK in one program (do × STM × #4 arithmetic): a transactional bank transfer that
-- reads like imperative code — allocate, read the balance, write the COMPUTED new balance, read it back.
-- `atomically (do { a = new 100; bal = read a; write a (bal - 30); read a })` ⟶ 70. Still a verified
-- CBPV kernel underneath; this is what "surface the verified kernel" looks like end-to-end.
#guard runYieldsInt 200
  "atomically (do { a = new 100; bal = read a; z = write a (bal - 30); read a })" 70

/-! ### A24–A25: arithmetic/computations in ADT INTRO args & ELIMINATOR scrutinees (issue #29).

The value-restriction A-normalization, generalized past effect-op args (#26) to `Left`/`Right`/pair
intros and `match`/`split` scrutinees: a computed value can be injected or destructured directly. -/

-- A24. SAFE DIVIDE as a Result: `Right(x / y)` injects a COMPUTED quotient, then `match` on the (computed)
-- Result recovers it. y = 4 ≠ 0 ⟹ Right(20/4) ⟹ matched ⟹ 5. (The `if` scrutinee + `Right` arg both A-norm.)
#guard runYieldsInt 50
  "let x = 20 in (let y = 4 in (match (if y == 0 then Left(0) else Right(x / y)) { Left(e) -> 0 , Right(q) -> q }))" 5

-- A25. DESTRUCTURE A COMPUTED PAIR: `let (a, b) = (if … then (3,4) else (5,6))` splits a value produced by
-- a computation (the `split` scrutinee is A-normalized). 1 < 2 ⟹ (3,4) ⟹ a + b = 7.
#guard runYieldsInt 50 "let (a, b) = (if 1 < 2 then (3, 4) else (5, 6)) in a + b" 7

/-! ## B. Raw-`Comp` programs (structural `match` on `Result`)

Sum/product (§A12/A13, issue #1) and arithmetic (issue #4 — now infix from source, see
`Surface.lean` Stage 2e) are surfaceable; what remains hand-built is μ (`fold`/`unfold` —
recursive data, issue #2) and the capability escape. The arithmetic guards below stay as
hand-built `Comp` because they pin the *kernel δ-rule directly* (the reference, below the
surface). These are written as `Comp` terms with the de-Bruijn indices noted; the `#guard`
structurally matches the `Result Val` (no `BEq` on kernel types). -/

-- B0a. ARITHMETIC (issue #4, ADR-0065): the `binop` δ-rule reduces two `vint` operands in
-- place (no eval-context frame, like `case`/`split`). `3 + 4 ⟶ 7`, `6 × 7 ⟶ 42`, `10 − 3 ⟶ 7`.
#guard (match Source.eval 20 (.binop .add (.vint 3) (.vint 4)) with | .done (.vint n) => n == 7 | _ => false)
#guard (match Source.eval 20 (.binop .mul (.vint 6) (.vint 7)) with | .done (.vint n) => n == 42 | _ => false)
#guard (match Source.eval 20 (.binop .sub (.vint 10) (.vint 3)) with | .done (.vint n) => n == 7 | _ => false)
-- B0b. COMPARISON returns `Bool = 1 + 1` (ADR-0029/0065): `3 < 4 ⟶ true = inr unit`; `4 < 3 ⟶ false = inl unit`.
#guard (match Source.eval 20 (.binop .lt (.vint 3) (.vint 4)) with | .done (.inr .vunit) => true | _ => false)
#guard (match Source.eval 20 (.binop .lt (.vint 4) (.vint 3)) with | .done (.inl .vunit) => true | _ => false)
-- B0c. A counter step `get + 1` over a state cell — the canonical motivating program (rung 1 × arithmetic).
-- `state 5 in (binop add get 1)` ⟶ 6: `get` reads 5, the δ-rule adds 1. (Hand-built: `get` = perform.)
#guard (match Source.eval 50
    (.handle (.state stateLabel (.vint 5))
      (.letC (.perform (.vvar 0) "get" .vunit) (.binop .add (.vvar 0) (.vint 1)))) with
  | .done (.vint n) => n == 6 | _ => false)

-- B1. μ STACK — LIFO (rung 2, ADR-0029): `Stack = μX. 1 + (Int × X)`. `pop` is
-- `unfold`→`case`→`split` under the hood; the user sees only `empty`/`push`/`pop`
-- (reused from `Bang.Surface`). Popping `push 9 (push 7 empty)` returns the most
-- recent push on top: `some (9, …)` = `inr ⟨9, …⟩`. ⟶ done (inr (9, _)).
#guard (match Source.eval 50 (pop (push 9 (push 7 empty))) with
  | .done (.inr (.pair (.vint n) _)) => n == 9 | _ => false)

-- B2. μ STACK — EMPTY: `pop empty` is the "none" of `1 + (Int × Stack)`,
-- i.e. `inl unit`. The empty-stack branch fires. ⟶ done (inl unit).
#guard (match Source.eval 50 (pop empty) with
  | .done (.inl .vunit) => true | _ => false)

-- B3. CAPABILITY ESCAPE — FAIL-LOUD (ADR-0063): a `{get}` thunk captures its
-- state handler's capability, is RETURNED out of the handler, then forced at top
-- level where that handler has POPPED. The cap names a frame no longer on the
-- stack, so dispatch finds nothing → the DEFINED terminal `.escapedCap` (NOT a
-- silent `stuck`; the kernel documents its error outcome). de-Bruijn: the thunk
-- captures `vvar 0` (the handle binder); the outer `letC` binds it, `$` forces it.
def capEscape : Comp :=
  .letC
    (.handle (.state stateLabel .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
    (.force (.vvar 0))
#guard (match Source.eval 50 capEscape with | .escapedCap => true | _ => false)

/-! ## C. Compiled-path differential guards — `exec ∘ compile ≡ Source.eval` (issue #6)

The `bang run --compiled` engine runs the CALCULATED abstract machine (`Bang.CalcVM`,
the verified compiler output of the two-hop architecture, ADR-0016) instead of the
kernel oracle. `compile_correct` / `evalD_agrees_source` PROVE these engines agree in
general; the guards below are the concrete cross-check that catches definitional drift,
run on the SAME readable surface sources §A uses — so they exercise the full runner
pipeline `parse → lower → compile → exec` that the CLI flag drives.

`compiledAgreesInt` ties BOTH engines to one literal `n`: a false "they agree" is
structurally unrepresentable (you cannot satisfy it with the two engines returning
different values). A false guard FAILS `lake build` — the gate. Fuel is generous:
`exec` counts machine-instruction steps (finer than `Source.eval`'s recursion depth),
but both are monotone once terminated, so one over-supply serves both engines. -/

/-- Compiled-path differential check: the calculated machine `exec ∘ compile` AND the
kernel oracle `Source.eval` both yield exactly `vint n` for the lowered `src`. Mirrors
`runYieldsInt`'s structural style — no `BEq` on kernel types. -/
def compiledAgreesInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  match Bang.Surface.parse src with
  | .error _ => false
  | .ok surf =>
    match Bang.Surface.lower surf with
    | .error _ => false
    | .ok c =>
      (match Bang.CalcVM.exec fuel 0 (Bang.CalcVM.compile c []) [] [] with
       | some [.ret (.vint m)] => m == n
       | _                     => false)
      &&
      (match Source.eval fuel c with
       | .done (.vint m) => m == n
       | _               => false)

-- C-PURE. let-binding (A1) and lambda β (A4): the compiled machine reduces `SUBST`/`APP`
-- to the same value the oracle does.
#guard compiledAgreesInt 2000 "let x = 3 in x" 3
#guard compiledAgreesInt 2000 "(fun x => x) 5" 5

-- C-THROWS. zero-shot `raise` caught by `handle` (A5), and the DEEP handler that discards
-- the captured continuation (A6): the machine's `THROW`/`unwindFind` aborts to the same payload.
#guard compiledAgreesInt 2000 "handle (raise 7)" 7
#guard compiledAgreesInt 2000 "handle (let z = raise 7 in 99)" 7

-- C-STATE. read-default (A7) and RESUMPTIVE put-then-get (A8): the machine's `OP`/`stateUpdate`
-- resumes the continuation and threads the store exactly as the oracle's resumptive handler.
#guard compiledAgreesInt 2000 "state 5 in get" 5
#guard compiledAgreesInt 2000 "state 0 in (let z = put 7 in get)" 7

-- C-STM. transaction commit (A10) and abort-ROLLBACK on a foreign throw (A11): the machine's
-- `txnUpdate` threads the heap, and the zero-shot escape discards the uncommitted write — the
-- observable `100` (original balance) proves the rollback, agreeing with the oracle.
#guard compiledAgreesInt 2000 "atomically (let r = new 100 in (let z = write r 70 in read r))" 70
#guard compiledAgreesInt 2000 "handle (atomically (let r = new 100 in (let z = write r 70 in raise 100)))" 100

-- C-BINOP (build-enforced, issue #40 CLOSED): the ADR-0065 δ-rule now lives in the calculated
-- machine — `evalD` gained a `binop op (vint a) (vint b) ⇒ ret (op.eval a b)` arm that COLLAPSES
-- onto `RET` in `compile` (NO new instruction; invariant #4 — the machine is the calculation's
-- output). Arithmetic on `--compiled` now agrees with the oracle, so the old boundary guard flips
-- to POSITIVE differential checks: plain arithmetic (with precedence) AND binop composed with the
-- other effect channels (the composition `state 5 in (get + 1)` is exactly what exposed the gap).
#guard compiledAgreesInt 2000 "3 + 4" 7
#guard compiledAgreesInt 2000 "2 + 3 * 4" 14                        -- precedence: `*` binds tighter
#guard compiledAgreesInt 2000 "state 5 in (get + 1)" 6             -- binop over the STATE channel
#guard compiledAgreesInt 2000 "handle (7 + (raise 3))" 3          -- binop operand raises → caught

-- C-CUSTOM (ADR-0085 Stage 4 — user-defined effects through the COMPILED path). The custom
-- clause-service arm now closes `exec_wexec_sim_ok`'s custom-freedom seam; these two guards tie
-- `exec ∘ compile` back to `Source.eval` on the general `Handler.custom`. The surface has no custom
-- syntax yet (Stage 7), so the programs are hand-built at the `Comp` IR level (mirroring the kernel
-- `#guard`s in `Core/Semantics/Eval.lean`, now also driven through the calculated machine). The
-- `readerClauses` clause resumes with `arg@0 + param@1`; dispatch is first-match-wins.
private def customReaderClauses : List (Bang.ClauseKey × Comp) :=
  [(.plain "read", .binop .add (.vvar 0) (.vvar 1))]

/-- Custom DISPATCH + one-shot RESUME: `read 5` runs the clause `5 + 100 = 105`, resumes the `letC`
continuation `105 + 1 = 106`. The calculated machine's `customUpdate` clause-service agrees with the
kernel's resumptive dispatch. -/
private def customResume : Comp :=
  .handle (.custom 1 (.vint 100) customReaderClauses)
    (.letC (.perform (.vvar 0) "read" (.vint 5))
      (.binop .add (.vvar 0) (.vint 1)))

/-- Custom ABORT coexisting with `throws`: a custom frame (label 1) sits between `raise 42` and its
`throws` handler (label 2); the abort discards the custom frame and the read continuation, yielding
`42`. The machine's `unwindFind` skips the custom frame exactly as the kernel does. -/
private def customAbortCoexist : Comp :=
  .handle (.throws 2)
    (.handle (.custom 1 (.vint 100) customReaderClauses)
      (.letC (.perform (.vvar 1) "raise" (.vint 42))
        (.perform (.vvar 0) "read" (.vint 5))))

/-- Direct-`Comp` differential check (custom effects have no surface syntax): the calculated machine
`exec ∘ compile` AND the kernel oracle `Source.eval` both yield exactly `vint n`. Mirrors
`compiledAgreesInt`, bypassing the surface parse/lower. -/
private def compiledAgreesC (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  (match Bang.CalcVM.exec fuel 0 (Bang.CalcVM.compile c []) [] [] with
   | some [.ret (.vint m)] => m == n
   | _                     => false)
  &&
  (match Source.eval fuel c with
   | .done (.vint m) => m == n
   | _               => false)

#guard compiledAgreesC 2000 customResume 106
#guard compiledAgreesC 2000 customAbortCoexist 42

/-! ## D. Typed `let rec` on the COMPILED path (issue #95 regression)

`let rec` (ADR-0073) desugars via the TYPED elaborator (`TypeCheck.elabS`'s `letRecS` arm →
`buildLetRec`'s μ-knot, `Bang/Frontend/TypeCheck.lean`) — the untyped `Surface.lower` §C's guards
above never reach it (reaching `letRecS` on that path is itself a checker error: "let rec is
desugared away by the elaborator"). `compiledAgreesTyped` mirrors `compiledAgreesInt` but routes
through `TypeCheck.checkAndLower` (the production `bang run`/`bang check` pipeline) so recursion's
μ-knot IS exercised. This is the compiled-path companion to `runTypedYieldsInt`'s kernel-only
`let rec` guards (`Bang/Frontend/TypeCheck.lean`'s `recProg`/`assertTypedOutOfFuel` corpus, e.g. the
countdown-sum `#guard`s near `recProg`). -/

/-- Typed-pipeline compiled-path differential check: `checkAndLower src` then BOTH the calculated
machine `exec ∘ compile` and the kernel oracle `Source.eval` agree on `vint n`. -/
def compiledAgreesTyped (fuel : Nat) (src : String) (n : Int) : Bool :=
  match Bang.TypeCheck.checkAndLower src with
  | .error _ => false
  | .ok c =>
    (match Bang.CalcVM.exec fuel 0 (Bang.CalcVM.compile c []) [] [] with
     | some [.ret (.vint m)] => m == n
     | _                     => false)
    &&
    (match Source.eval fuel c with
     | .done (.vint m) => m == n
     | _               => false)

-- D-LETREC (issue #95 fix pin). A RE-ENTRANT nested-`let rec` knot — an outer `p` with sibling
-- `factor`/`term`, where `factor` calls BACK into the outer `p` (the exact shape
-- `scratch/calc95/repro-min.bang` isolated from `examples/calc`'s parser, whose FOUR large
-- sibling productions pushed `--compiled` to an 873s residual-recompile blowup before the
-- `buildLetRec` knot-sharing fix, `docs/notes/dogfood-calc-findings.md` wall 1). Both engines
-- agree at 12 — the SAME value `examples/calc`'s own re-entrant grammar agrees on across all
-- three engines (`env`/`ck`/`--compiled`), now cheap on the compiled path too.
#guard compiledAgreesTyped 4000
  ("let rec p : Int -> Option (Int * Int) ! {Div} = fun n => "
    ++ "let rec factor : Int -> Option (Int * Int) ! {Div} = fun ts => "
    ++ "if ts == 0 then Some(0, 0) "
    ++ "else match ($p (ts - 1) : Option (Int * Int)) { "
    ++ "None -> None, Some(q) -> let (a, b) = q in Some(a + 1, b + 1) } "
    ++ "in "
    ++ "let rec term : Int -> Option (Int * Int) ! {Div} = fun ts => "
    ++ "match ($factor ts : Option (Int * Int)) { "
    ++ "None -> None, Some(q) -> let (a, b) = q in Some(a, b) } "
    ++ "in "
    ++ "$term n "
    ++ "match ($p 6 : Option (Int * Int)) { None -> 0, Some(q) -> let (a, b) = q in a + b }")
  12

/-! ## E. MUTUAL `let rec … and …` on the COMPILED path (#97 item 2).

The H2 tuple-of-thunks μ-knot (`buildLetRecMulti`) reuses `buildLetRec`'s `knotBody` BYTE-FOR-BYTE
(the #95 knot-sharing fix — `fold #g`, never a second free `sv`) — so the per-level residual-cost
argument transfers unchanged: a mutual group should NOT reintroduce the pre-#95 `2^depth` blowup on
the compiled path. `compiledAgreesTyped` exercises `CalcVM.exec ∘ compile` (NOT just the kernel
oracle `Source.eval`), the same two-engine differential §D already runs for the single-function
knot. -/
-- even/odd at a moderately re-entrant depth (10 mutual unfolds) — both engines agree at `1`.
#guard compiledAgreesTyped 4000
  ("let rec even : Int -> Int ! {Div} = fun n => "
    ++ "let c = n == 0 in if c then 1 else let n1 = n - 1 in ($odd) n1 "
    ++ "and odd : Int -> Int ! {Div} = fun n => "
    ++ "let c = n == 0 in if c then 0 else let n1 = n - 1 in ($even) n1 "
    ++ "in ($even) 10")
  1

/-! ## F. Bound-free `let rec` monomorphization (ADR-0103, #120 List-family door)

`length : List a -> Int` — a SELF-RECURSIVE generic with NO trait bound — is realized by a
call-site-monomorphization pre-pass (`TypeCheck.monomorphizeLetRec`/`monomorphizeOne`) running
BEFORE `elabS`: it discovers the finite instantiation set from ANNOTATED call-site arguments and
emits one monomorphic `let rec` residue per element, exactly witness w3's by-hand shape
(`docs/decisions/witness-0103/w3-two-residues-one-program.bang`), auto-generated. -/

-- w3's TWO residues (`List Int` + `List (Unit+Unit)`), now written as ONE bound-free `let rec`
-- ascription instead of two hand-written monomorphic ones — the ADR-0103 payoff. Both call sites
-- carry an explicit argument annotation (the discovery anchor, decision item 3); the pre-pass
-- discovers `{Int, Unit+Unit}` and emits two residues, agreeing with w3's own hand-written result.
#guard compiledAgreesTyped 4000
  ("data List a = Nil | Cons(a, List a) "
    ++ "let rec length : List a -> Int = fun xs => "
    ++ "match (xs : List a) { Nil -> 0, Cons(h, t) -> 1 + (($length) t) } "
    ++ "let x = ($length) (Cons(1, Cons(2, Nil)) : List Int) in "
    ++ "let y = ($length) (Cons(Left(()), Nil) : List (Unit + Unit)) in "
    ++ "x + y")
  3

-- A user re-declaring `length` for a DIFFERENT (non-generic) type shadows the bound-free `let
-- rec` entirely (ordinary lexical shadowing, `TypeCheck.monomorphizeOne`'s `.letRecS`/shadow arm)
-- — the outer generic residue (called BEFORE the shadow) and the inner monomorphic `length : Int
-- -> Int` (called after) coexist without collision: `1 + 10 = 11`.
#guard compiledAgreesTyped 4000
  ("data List a = Nil | Cons(a, List a) "
    ++ "let rec length : List a -> Int = fun xs => "
    ++ "match (xs : List a) { Nil -> 0, Cons(h, t) -> 1 + (($length) t) } "
    ++ "let outer = ($length) (Cons(1, Nil) : List Int) in "
    ++ "let rec length : Int -> Int = fun n => n in "
    ++ "outer + (($length) 10)")
  11

-- An UNREFERENCED bound-free `let rec` costs NOTHING (the `expandBFns`/`env.bfns` precedent,
-- ADR-0098's mention-filter the same move one layer up): `monomorphizeOne` DROPS a zero-call-site
-- binding rather than emitting a residue, so the surviving program is just `42` — verified at a
-- FUEL BOUND (`50`, far below the `4000` the OTHER guards in this section need) that would starve
-- if the dropped `let rec`'s knot were ever built.
#guard compiledAgreesTyped 50
  ("data List a = Nil | Cons(a, List a) "
    ++ "let rec length : List a -> Int = fun xs => "
    ++ "match (xs : List a) { Nil -> 0, Cons(h, t) -> 1 + (($length) t) } "
    ++ "42")
  42

-- POLYMORPHIC recursion (a self-call at a DIFFERENT instantiation than the enclosing call, R6's
-- finiteness-gate wall — ADR-0103 decision item 3) is REJECTED, never silently monomorphized: the
-- residue built for the OUTER call's instantiation (`List (Unit+Unit)`) has its self-call forced
-- to the SAME residue (every self-reference inside ONE residue's body maps to that residue alone,
-- `w4`'s monomorphic-recursion invariant), so the INNER self-call's own `List Int` annotation is
-- discarded — producing an ill-typed residue the downstream type-checker rejects LOUD (never a
-- wrong-but-quiet result). `checkAndLower` errors ⟹ `compiledAgreesTyped` returns `false` for
-- EVERY `n` (the `.error _ => false` arm) — asserting rejection at `n := 0` (an arbitrary
-- sentinel) is equivalent to asserting "this program never type-checks", the negative-test idiom
-- this file's own `.error _ => false` arm already establishes.
#guard !(compiledAgreesTyped 4000
  ("data List a = Nil | Cons(a, List a) "
    ++ "let rec weird : List a -> Int = fun xs => "
    ++ "match (xs : List a) { Nil -> 0, "
    ++ "Cons(h, t) -> 1 + (($weird) (Cons(1, Nil) : List Int)) } "
    ++ "($weird) (Cons(Left(()), Nil) : List (Unit + Unit))")
  0)

-- `take`/`drop` (`Prelude.bang`, the ADR-0103 payoff) called through the AUTO-`use` alias
-- (ADR-0098) — `$take`/`$drop` here resolve `Prelude_take`/`Prelude_drop`'s bare `let take =
-- Prelude_take in …` alias, NOT the qualified name directly, so this pins the `inlineVarAliases`
-- fix (the module-alias-indirection gap discovery couldn't see through until fixed): `take 2` of
-- `[1,2,3]` then `drop 1` leaves `[2]`, head 2.
#guard compiledAgreesTyped 4000
  ("data List a = Nil | Cons(a, List a) "
    ++ "let taken = ($take 2) (Cons(1, Cons(2, Cons(3, Nil))) : List Int) in "
    ++ "match (($drop 1) (taken : List Int) : List Int) { Nil -> 0, Cons(h, t) -> h }")
  2

end Bang.Examples
