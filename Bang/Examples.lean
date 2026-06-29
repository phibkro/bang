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
       ADTs / handler-escape / non-int outcomes the surface parser cannot build.

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

/-! ## B. Raw-`Comp` programs (structural `match` on `Result`)

The surface parser does not build ADTs (sum/product/μ) or a capability escape;
these are written as hand-built `Comp` terms with the de-Bruijn indices noted.
The `#guard` structurally matches the `Result Val` (no `BEq` on kernel types). -/

-- B1. SUM / CASE: `case (inr 7) { inl ⇒ 0 | inr x ⇒ x }` discriminates the tag
-- and runs the `inr` branch, binding the payload `7` at index 0. ⟶ done 7.
def sumCase : Comp :=
  .case (.inr (.vint 7)) (.ret (.vint 0)) (.ret (.vvar 0))
#guard (match Source.eval 20 sumCase with | .done (.vint n) => n == 7 | _ => false)

-- B2. PRODUCT / SPLIT: destructure `(3, 4)` then REBUILD it swapped. `split`
-- binds the first component at index 1 and the second at index 0. ⟶ done (4, 3).
def prodSwap : Comp :=
  .split (.pair (.vint 3) (.vint 4)) (.ret (.pair (.vvar 0) (.vvar 1)))
#guard (match Source.eval 20 prodSwap with
  | .done (.pair (.vint a) (.vint b)) => a == 4 && b == 3 | _ => false)

-- B3. μ STACK — LIFO (rung 2, ADR-0029): `Stack = μX. 1 + (Int × X)`. `pop` is
-- `unfold`→`case`→`split` under the hood; the user sees only `empty`/`push`/`pop`
-- (reused from `Bang.Surface`). Popping `push 9 (push 7 empty)` returns the most
-- recent push on top: `some (9, …)` = `inr ⟨9, …⟩`. ⟶ done (inr (9, _)).
#guard (match Source.eval 50 (pop (push 9 (push 7 empty))) with
  | .done (.inr (.pair (.vint n) _)) => n == 9 | _ => false)

-- B4. μ STACK — EMPTY: `pop empty` is the "none" of `1 + (Int × Stack)`,
-- i.e. `inl unit`. The empty-stack branch fires. ⟶ done (inl unit).
#guard (match Source.eval 50 (pop empty) with
  | .done (.inl .vunit) => true | _ => false)

-- B5. CAPABILITY ESCAPE — FAIL-LOUD (ADR-0063): a `{get}` thunk captures its
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
