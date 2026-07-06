/-
  Bang/Frontend/OutcomeSpike.lean — issue #54 SPIKE: a structured `Outcome`-ADT assertion layer.
  ────────────────────────────────────────────────────────────────────────────────────────────
  The bespoke test guards (`runYieldsInt`, `check == .error`, `parseLocated` span checks, …) are each
  a `Bool` predicate that PROJECTS the pipeline result onto ONE outcome and collapses everything else
  to `false`: `runYieldsInt` = `match … | .done (.vint m) => m==n | _ => false`. A failure shows
  "not 7", never WHICH outcome (a wrong value / `oom` / `stuck` / `escapedCap` are indistinguishable),
  and the RUNTIME exceptional terminals (`stuck`/`oom`/`escaped`) have no systematic assertion.

  This spike models the FULL pipeline result as ONE ADT (`Outcome`) with a `runOutcome` that produces
  it, and re-derives the bespoke helpers as thin projections. It applies bang's OWN principle — model
  the result space as a total sum, make the exceptional states first-class — to the harness.

  A LEAF (nothing in `Bang/` imports it; census/soundness closure untouched), like `HMSpike.lean`.
  It REUSES the production entry points (`checkAndLower`, `elaborateToComp`, `Source.eval`) as the
  single source of truth for "what a program does" — it does NOT reimplement the pipeline.

  FINDING at the bottom.
-/
module

-- #guards run the COMPILED pipeline (checkAndLower / elaborateToComp / Source.eval) at the META
-- phase → meta imports, mirroring TypeCheck.lean's cross-module #guard wall.
meta import Bang.Frontend.Surface
meta import Bang.Frontend.TypeCheck
meta import Bang.Core.Semantics
public import Bang.Frontend.Surface
public import Bang.Frontend.TypeCheck

namespace Bang.OutcomeSpike
open Bang
open Bang.Surface

/-! ## 1. The `Outcome` ADT — the FULL pipeline result space as one total sum.

The REAL terminals, grounded in the source (NOT invented):

  · `Source.eval : … → Result Val`  where  `Result = done Val | oom | escapedCap | stuck`
    (Eval.lean:38 — FOUR terminals; UB-set = ∅, every result DEFINED).
  · two PRE-eval stage failures the run never reaches: a located PARSE error (with a `Span`) and an
    elaboration/TYPE error (un-located in v1).

Note there is NO `wrong` variant: `Comp.wrong : String → Comp` is a TERM constructor (IR.lean:138,
produced ONLY by the `NamedCore` core-term parser, never by the surface `parse`/`lower` path), and
`Source.eval` has no `.wrong` RESULT — a `.wrong` term that reaches the machine focus classifies as
`.stuck` (Eval.lean:225). So the surface pipeline's result space is EXACTLY these six. -/
inductive Outcome where
  | parseErr : Option Span → String → Outcome   -- located parse error (span from `parseProgLocated`)
  | typeErr  : String → Outcome                 -- elaboration or type error (un-located in v1 ⇒ no span)
  | yields   : Val → Outcome                    -- `Result.done v`
  | oom      : Outcome                           -- `Result.oom`   (fuel exhausted / divergence)
  | escaped  : Outcome                           -- `Result.escapedCap` (ADR-0063 capability-escape)
  | stuck    : Outcome                           -- `Result.stuck` (genuine stuck)

/-- Structural equality. `Val` has a `BEq` (Surface.lean); `Span` derives `DecidableEq`. Hand-written
(not `deriving BEq`) because `Val` exposes only `BEq`, not `DecidableEq`, so `deriving` can't fire. -/
def Outcome.beq : Outcome → Outcome → Bool
  | .parseErr s1 m1, .parseErr s2 m2 =>
      (match s1, s2 with
       | some a, some b => a.line == b.line && a.col == b.col && a.endLine == b.endLine && a.endCol == b.endCol
       | none,   none   => true
       | _,      _      => false) && m1 == m2
  | .typeErr m1, .typeErr m2 => m1 == m2
  | .yields v1,  .yields v2  => v1 == v2
  | .oom,        .oom        => true
  | .escaped,    .escaped    => true
  | .stuck,      .stuck      => true
  | _,           _           => false

instance : BEq Outcome := ⟨Outcome.beq⟩

/-! ## 2. `runOutcome` — thread each stage's failure into the structured result.

Two entry points, mirroring the actual pipeline's own split (its SSoT):

  · `runOutcome`     = the TYPED default (`checkAndLower`: parse-located → elaborate → TYPE-CHECK →
                       lower → eval). Produces `parseErr | typeErr | yields | oom | escaped`.
  · `runOutcomeRaw`  = the `--no-typecheck` escape (`elaborateToComp`: parse → elaborate → lower →
                       eval). Produces `parseErr(no span) | yields | oom | escaped | stuck`.

The split is FORCED by type safety, not taste: a well-typed program NEVER goes `.stuck`
(`type_safety`: well-typed ⟹ progress). So `.stuck` is reachable ONLY through the raw path — the
`Outcome` layer makes the stratification seam (verified/total vs raw/stuck) directly assertable. -/

/-- The kernel `Result` → `Outcome` (the eval-terminal half; total over all four `Result` ctors). -/
def evalToOutcome : Result Val → Outcome
  | .done v     => .yields v
  | .oom        => .oom
  | .escapedCap => .escaped
  | .stuck      => .stuck

/-- TYPED pipeline (the production default). A parse error keeps its `Span` (`some`); an
elaboration/type error is un-located (`none`). Never returns `.stuck` (type safety). -/
def runOutcome (fuel : Nat) (src : String) : Outcome :=
  match Bang.TypeCheck.checkAndLower src with
  | .error (m, some sp) => .parseErr (some sp) m
  | .error (m, none)    => .typeErr m
  | .ok c               => evalToOutcome (Source.eval fuel c)

/-- UNTYPED escape (`--no-typecheck`): no type gate, so a `.stuck`/`.escaped` terminal is reachable.
`elaborateToComp` parses UN-located, so a parse error here carries no span. -/
def runOutcomeRaw (fuel : Nat) (src : String) : Outcome :=
  match Bang.TypeCheck.elaborateToComp src with
  | .error m => .parseErr none m
  | .ok c    => evalToOutcome (Source.eval fuel c)

/-! ## 3. Structured assertions — thin projections of `runOutcome` (Bool, for `#guard`).

`outcomeIs` is the total comparison; the named projections are its ergonomic faces. `stuck`/`escaped`
go through the RAW path (unreachable through the type gate); the rest through the typed path. -/

def outcomeIs (o expected : Outcome) : Bool := o == expected

def assertYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  match runOutcome fuel src with | .yields (.vint m) => m == n | _ => false

def assertTypeError (fuel : Nat) (src : String) : Bool :=
  match runOutcome fuel src with | .typeErr _ => true | _ => false

def assertParseErrorAt (fuel : Nat) (src : String) (line col : Nat) : Bool :=
  match runOutcome fuel src with | .parseErr (some sp) _ => sp.line == line && sp.col == col | _ => false

def assertOom (fuel : Nat) (src : String) : Bool :=
  match runOutcome fuel src with | .oom => true | _ => false

def assertStuck (fuel : Nat) (src : String) : Bool :=
  match runOutcomeRaw fuel src with | .stuck => true | _ => false

def assertEscaped (fuel : Nat) (src : String) : Bool :=
  match runOutcomeRaw fuel src with | .escaped => true | _ => false

/-! ## 4. Guards — one per terminal (a false `#guard` is a BUILD ERROR, so each is verified). -/

-- a VALUE: `3 + 4` → `.yields (vint 7)`.
#guard assertYieldsInt 20 "3 + 4" 7
#guard outcomeIs (runOutcome 20 "3 + 4") (.yields (.vint 7))

-- a TYPE error: `1 + Left(0)` — the sum injection can't be added to an Int (elaborator rejects).
#guard assertTypeError 20 "1 + Left(0)"

-- a located PARSE error: `let x 3 in x` — the missing `=` (the `3` sits where `=` was wanted) at 1:7.
#guard assertParseErrorAt 20 "let x 3 in x" 1 7

-- an OOM: an unbounded recursion (types fine ⇒ typed path reaches it) under bounded fuel.
#guard assertOom 60 "let rec loop : Int -> Int = fun n => ($loop)(n + 1) in ($loop) 0"

-- a STUCK: force a NON-thunk (`$3`) — ill-formed at runtime, rejected by the type gate, so run RAW.
#guard assertStuck 20 "$3"

-- an ESCAPED (ADR-0063): a capability captured in a thunk and forced PAST its handler.
-- `state 0 in {get}` returns the thunk `{get}`; binding it out and forcing (`$c`) dispatches `get`
-- after the `state` frame popped ⇒ the DEFINED `escapedCap` terminal. Constructible from surface.
#guard assertEscaped 80 "let c = (state 0 in {get}) in $c"

/-! ## 5. Unification demo — the bespoke helpers ARE projections of `runOutcome`.

`Surface.runYieldsInt` (the untyped, decl-free bespoke helper) agrees with the `Outcome` projection
on the well-typed corpus: for a well-typed value-yielding program the typed and untyped run paths
agree (type safety), so `runYieldsInt fuel src n` is EXACTLY `outcomeIs (runOutcome fuel src)
(.yields (vint n))`. Drift is caught at build. -/
#guard Surface.runYieldsInt 20 "3 + 4" 7 == outcomeIs (runOutcome 20 "3 + 4") (.yields (.vint 7))
#guard Surface.runYieldsInt 20 "let x = 3 in x" 3 == assertYieldsInt 20 "let x = 3 in x" 3
#guard Surface.runYieldsInt 30 "if 3 < 4 then 1 else 0" 1 == assertYieldsInt 30 "if 3 < 4 then 1 else 0" 1
-- the projection is STRICTLY MORE INFORMATIVE: where the bespoke helper says only `false`, the
-- Outcome names the actual terminal (here: a type error, invisible to `runYieldsInt`).
#guard (Surface.runYieldsInt 20 "1 + Left(0)" 0 == false) && assertTypeError 20 "1 + Left(0)"

end Bang.OutcomeSpike
