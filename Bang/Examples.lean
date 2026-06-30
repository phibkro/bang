/-
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

module

-- The `#guard`s run COMPILED code (`Source.eval` / `runYieldsInt`) at the META
-- (elaboration) phase, so the modules providing it must be `meta import`ed in
-- addition to the runtime import — the cross-module `#guard` codegen wall
-- (Lean v4.30, Phase-1a finding). Mirrors `Bang/Frontend/NamedCore.lean`:41 and
-- `Bang/Witness/LWRegress.lean`:23.
meta import Bang.Frontend.Surface
public import Bang.Frontend.Surface

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

end Bang.Examples
