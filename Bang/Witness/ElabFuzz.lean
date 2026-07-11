module

meta import Bang.Frontend.TypeCheck
meta import Bang.Frontend.Format
meta import Bang.Frontend.Surface
meta import Bang.Witness.Fuzz
public import Bang.Frontend.TypeCheck
public import Bang.Frontend.Format
public import Bang.Frontend.Surface
public import Bang.Witness.Fuzz

/-!
  Bang/Witness/ElabFuzz.lean — FUZZ THE ELABORATOR (tier ③, `docs/notes/calculated-typer-survey.md`
  §trust-map). `Bang/Frontend/TypeCheck.lean` (~4100 lines, `Infer`-monad unification + holes +
  generalization + the μ-knot/module elaboration) is the trust gap the survey REFUTED a calculated
  checker as a fix for — the calculable fragment (the ~60-line pure `synthC`/`checkC` core) and the
  dangerous fragment (elaboration) are DISJOINT, so tier ③ (fuzzing, cheap, near-term) is the actual
  near-term move. This harness gives the ~4100 unverified lines an oracle they otherwise lack.

  UNLIKE `Bang/Witness/Fuzz.lean` (which generates KERNEL `Comp` terms directly, differential-testing
  `Source.eval` vs `exec ∘ compile`), this file generates SOURCE-LEVEL BANG STRINGS and drives them
  through the public FRONTEND entry points (`Bang.Surface.parseProg`, `Bang.Format.fmtProg`,
  `Bang.TypeCheck.checkAndLower`/`elaborateToComp`/`typeStringOfProg`) — the surface the elaborator
  actually sees. This is the leaf discipline in force: `Bang/Frontend/*` has fan-in 0 from the
  verified spine, so THIS module (which has fan-in 0 from `Bang/Frontend/*` in the other direction —
  it only CALLS the five public entries, never touches `TypeCheck.lean`/`Surface.lean`/`Format.lean`
  internals) is the correct, permitted shape for exercising it from outside.

  NON-META, BY CONSTRUCTION: same reasoning as `Fuzz.lean` — `Plausible.Gen`/`Random` are
  `public meta section`, so a `Gen`-based generator cannot itself call the RUNTIME frontend entries
  in the same phase. This harness reuses `Fuzz.lean`'s hand-rolled splitmix64 (Rng.step/Rng.nextMod)
  rather than re-deriving a second PRNG — one construct, per CLAUDE.md's "one construct per problem".

  TYPED-BIASED BY CONSTRUCTION: the generator threads a `TyEnv` (`List (String × SimpleTy)`, closest-
  first — mirrors `Fuzz.lean`'s `scope`/`hctx` discipline) so `var` references only ever draw a
  NAME ACTUALLY IN SCOPE, and binary ops / `if` conditions only combine operands the generator itself
  knows are `Int`/`Bool`-shaped. This is what keeps samples concentrated on TYPEABLE programs instead
  of drowning in `.error` (an elaborator fuzzer swamped by ill-typed input tests only the error paths,
  the same "make the bad state unrepresentable" lesson `Fuzz.lean`'s header names).
-/

namespace Bang.ElabFuzz

open Bang.Fuzz (Rng.step Rng.nextMod)

@[expose] public section

/-! ## 1. A tiny surface-level type model — just enough to bias generation toward well-typed
programs. NOT the checker's `IVTy`/`CT` (no unification, no rows) — a coarse SHAPE the generator
uses to decide "can I use this binding as an Int here / as a Bool condition there". -/

/-- What KIND of thing a bound name is, from the generator's point of view. `tInt`/`tBool` are
base shapes (an `Int` binding and a `< `/`==`-comparison result, respectively — bang has no
primitive `Bool`, `if` desugars over `Unit + Unit`, but source-level `3 < 4`/`3 == 3` ARE the
"Bool-shaped" expressions this generator is allowed to feed to `if`); `tFun` names a one-argument
function binding usable in application position (its own body shape is NOT tracked — the
generator only needs "is this callable", not its result type, since every generated function
returns `tInt`, see `genFunBody`). -/
inductive SimpleTy | tInt | tBool | tFun
  deriving Repr, DecidableEq

/-- In-scope bindings, closest-first (mirrors `Fuzz.lean`'s `hctx`: index-by-recency, not by
de Bruijn depth — source-level generation names variables by STRING, so there is no shifting to
thread, just consing/popping list entries as scopes open/close). -/
abbrev TyEnv := List (String × SimpleTy)

/-- Every name this module's generator ever binds, so two generated binders in the same scope
never collide (shadowing is legal in bang but colliding generated names would make the "well-
formed by construction" claim harder to audit by hand) — a simple counter-indexed name. -/
def nameAt (i : Nat) : String := "v" ++ toString i

/-- Render an `Int` as valid bang SOURCE syntax. bang's surface has NO unary-minus operator (the
tokenizer accepts only unsigned digit literals — `Surface.lean`'s `isIntLit`/`pAtom`; confirmed
missing-feature, `docs/notes/dogfood-json-findings.md`), so a bare `-10` is a PARSE error, not a
type error — an earlier version of this generator emitted `toString n` directly and every single
`useLetRec = false` sample failed invariant (b) for exactly this reason (falsified against the
live corpus: `genIntExpr`'s base case draws `n ∈ [0, 21)` then subtracts 10 for a signed range,
and `(n : Int) - 10` renders `"-3"` etc. via `toString`, which the parser rejects outright). The
fix desugars a negative literal to `(0 - <magnitude>)`, itself well-formed source producing the
same `Int` value — negative-value coverage is kept, the illegal token is not. -/
def intLitSrc (n : Int) : String :=
  if n < 0 then s!"(0 - {(-n)})" else toString n

/-! ## 2. A small closed `data` decl the generator's `match` case draws on — the ADT layer
(ADR-0029/0069). ONE fixed declaration (not itself generated — the mission scope is "a small
GENERATED data decl"; a single fixed 2-constructor sum is the smallest useful generator surface
without re-deriving `data`'s own generator-spec machinery, which is a bigger lift than this
harness's scope). `Box` mirrors the `Option`-style corpus already in `TypeCheck.lean`
(`data Option a = None | Some(a)`) but MONOMORPHIC (`Int`, not a type parameter) — deliberately:
the mission's typed-tracking env (`SimpleTy`) has no generic-instantiation model, and threading
one is out of scope for a `#61`-shape-avoiding, deterministic, near-term fuzz harness. -/

/-- `data Box = BLeft(Int) | BRight(Int)` — a closed 2-ctor sum over `Int` payloads, prepended to
every generated program's decl prelude so `match` has something to eliminate. -/
def dataDeclSrc : String := "data Box = BLeft(Int) | BRight(Int)"

/-! ## 3. The generator proper — sized, scope-correct (by construction), typed-biased.

`genExpr fuel env s` returns `(source-string, s')`; `fuel` bounds recursion depth (generation
fuel, exactly like `Fuzz.lean`'s `genComp` — decremented every recursive call so generation
itself is total, no well-founded recursion needed). Every generated sub-expression is wrapped in
its own parens at composition sites, so precedence never needs tracking (a purely-parenthesized
generator is correct by construction against ANY precedence table the Pratt parser uses — cheap
insurance against a generator/parser precedence-assumption drift). -/

/-- Generate an `Int`-shaped expression: a literal, an in-scope `Int` variable, or a binop of two
smaller `Int`-shaped expressions. Weighted toward the two INERT leaves (mirrors `Fuzz.lean`'s
`genVal` bias) so recursion stays shallow on average even at high fuel. -/
partial def genIntExpr (fuel : Nat) (env : TyEnv) (s : Nat) : String × Nat :=
  let ints := env.filterMap (fun (n, t) => if t = .tInt then some n else none)
  match fuel with
  | 0 => let (s, n) := Rng.nextMod s 21; (intLitSrc ((n : Int) - 10), s)
  | fuel + 1 =>
    let (s, pick) := Rng.nextMod s (if ints.isEmpty then 2 else 3)
    match pick with
    | 0 =>
      let (s, n) := Rng.nextMod s 21
      (intLitSrc ((n : Int) - 10), s)
    | 1 =>
      let (a, s) := genIntExpr fuel env s
      let (b, s) := genIntExpr fuel env s
      let (s, oi) := Rng.nextMod s 4
      let op := ["+", "-", "*", "/"].getD oi "+"
      (s!"(({a}) {op} ({b}))", s)
    | _ =>
      let (s, i) := Rng.nextMod s ints.length
      (ints.getD i "0", s)

/-- Generate a `Bool`-shaped expression: a comparison of two `Int`-shaped sub-expressions
(bang has no primitive Bool literal at the SOURCE surface — `<`/`==` are the well-typed way to
produce one, matching `if c then t else e`'s `parsesTo`/`runYieldsInt` corpus in `Surface.lean`). -/
def genBoolExpr (fuel : Nat) (env : TyEnv) (s : Nat) : String × Nat :=
  let (a, s) := genIntExpr fuel env s
  let (b, s) := genIntExpr fuel env s
  let (s, oi) := Rng.nextMod s 2
  let op := ["<", "=="].getD oi "<"
  (s!"(({a}) {op} ({b}))", s)

/-- Generate an `Int`-typed `Box` scrutinee: `BLeft(<int>)` or `BRight(<int>)`, closed under
`env` (its payload is a generated `Int`-shaped expression, so the scrutinee is always
WELL-TYPED — the same "generate the value in the shape the eliminator needs" move `Fuzz.lean`'s
`case`/`split` arms use, rather than an arbitrary sub-expression that might not match). -/
def genBoxExpr (fuel : Nat) (env : TyEnv) (s : Nat) : String × Nat :=
  let (payload, s) := genIntExpr fuel env s
  let (s, side) := Rng.nextMod s 2
  (s!"({if side = 0 then "BLeft" else "BRight"}({payload}))", s)

/-- Generate an `Int`-typed EXPRESSION — the top-level generator entry, dispatching over
let/if/match/tuple/app in addition to plain arithmetic. Always produces something `Int`-shaped
(the fixed target type this harness checks against, `typeStringOfProg`'s "Int"), so every
generated program is well-typed BY CONSTRUCTION provided every sub-generator keeps its own typing
promise (the inductive invariant this whole file leans on). -/
partial def genExpr (fuel : Nat) (env : TyEnv) (s : Nat) : String × Nat :=
  match fuel with
  | 0 => genIntExpr 0 env s
  | fuel + 1 =>
    let (s, pick) := Rng.nextMod s 6
    match pick with
    -- plain arithmetic (the inert case, keeps average depth shallow)
    | 0 => genIntExpr fuel env s
    -- let x = <int-expr> in <int-expr>  (env grows by one Int binding)
    | 1 =>
      let n := nameAt env.length
      let (rhs, s) := genIntExpr fuel env s
      let (body, s) := genExpr fuel ((n, .tInt) :: env) s
      (s!"(let {n} = {rhs} in {body})", s)
    -- if <bool-expr> then <int-expr> else <int-expr>
    | 2 =>
      let (c, s) := genBoolExpr fuel env s
      let (t, s) := genExpr fuel env s
      let (e, s) := genExpr fuel env s
      (s!"(if {c} then {t} else {e})", s)
    -- match <box-expr> { BLeft(x) -> <int-expr>, BRight(x) -> <int-expr> }
    -- (both arms bind an Int-shaped payload — Box's ctors both carry an Int, ADR-0029 elim shape)
    | 3 =>
      let (scrut, s) := genBoxExpr fuel env s
      let ln := nameAt env.length
      let (larm, s) := genExpr fuel ((ln, .tInt) :: env) s
      let rn := nameAt env.length
      let (rarm, s) := genExpr fuel ((rn, .tInt) :: env) s
      (s!"(match {scrut} " ++ "{ BLeft(" ++ ln ++ ") -> " ++ larm ++ ", BRight(" ++ rn ++ ") -> " ++ rarm ++ " })", s)
    -- let (a, b) = (<int-expr>, <int-expr>) in <int-expr referencing a/b>
    | 4 =>
      let (fst, s) := genIntExpr fuel env s
      let (snd, s) := genIntExpr fuel env s
      let an := nameAt env.length
      let bn := nameAt (env.length + 1)
      let (body, s) := genExpr fuel ((bn, .tInt) :: (an, .tInt) :: env) s
      (s!"(let ({an}, {bn}) = ({fst}, {snd}) in {body})", s)
    -- an APPLICATION of a freshly-bound one-arg Int->Int lambda (keeps `fun`/`app` in the
    -- generator without needing a `tFun` call site to already exist in `env`)
    | _ =>
      let n := nameAt env.length
      let (fbody, s) := genIntExpr fuel ((n, .tInt) :: env) s
      let (arg, s) := genIntExpr fuel env s
      (s!"((fun {n} => {fbody}) ({arg}))", s)

/-- Generate a SHALLOW top-level `let rec` prefix, per the mission's "declared-row let rec
(shallow)": exactly one self-recursive `Int -> Int` function bound BEFORE the main generated
body, called at most once from the body. Deliberately NEVER nested inside another `let rec` or
inside a `match` arm alongside a sibling `let rec` — that shape is the documented #61 hang
(`docs/notes/dogfood-json-findings.md`: "SIBLING nested `let rec`s inside different match arms… of
one outer knot" hangs BOTH engines past a size/call threshold). A single flat, shallow `let rec` —
this harness's whole `let rec` surface — structurally cannot reach that shape: there is no second,
sibling `let rec` for it to compose with. -/
def genLetRecPrefix (base : Nat) (env : TyEnv) (s : Nat) : String × TyEnv × Nat :=
  let f := nameAt base
  let n := nameAt (base + 1)
  -- body: `if n == 0 then <int-lit> else n + ($f)(n - 1)` — the exact terminating self-call
  -- SHAPE already proven-terminating in the corpus (`TypeCheck.lean:3209`'s `sum`), so this
  -- generator draws only its base-case constant, never a structurally different recursion.
  let (base_v, s) := Rng.nextMod s 21
  -- self-call argument uses n directly (n - 1), well-typed, always reduces toward the base case
  let src := s!"let rec {f} : Int -> Int = fun {n} => if {n} == 0 then {base_v} else {n} + (${f})({n} - 1) in "
  (src, (f, .tFun) :: env, s)

/-- Top-level entry: a CLOSED, well-formed-by-construction whole PROGRAM source string —
`dataDeclSrc` + (optionally) one shallow `let rec` prefix + a generated `Int`-typed body.
`useLetRec` toggles the `let rec` prefix (kept as a parameter so invariants can sample both
shapes cheaply without re-deriving the generator). -/
def genProgram (depth seed : Nat) (useLetRec : Bool) : String :=
  let s := seed
  let (recSrc, env, s) :=
    if useLetRec then genLetRecPrefix 0 [] s else ("", ([] : TyEnv), s)
  let (body, _) := genExpr depth env s
  dataDeclSrc ++ " " ++ recSrc ++ body

/-! ## 4. Fixed seeds — deterministic, no wall-clock/OS entropy (mirrors `Fuzz.lean §5`). -/

/-- Same seed-derivation shape as `Fuzz.lean` (`i * 104729 + 7`, a fixed prime multiplier) — reuses
the sibling module's idiom rather than inventing a second one (one construct per problem). -/
def fuzzSeeds : List Nat := (List.range 60).map (fun i => i * 104729 + 7)

/-- Generation depth per sample. Capped well below anything resembling the #61 hang shape (that
shape needs MULTIPLE sibling `let rec`s nested in match arms under one outer knot — this
generator never nests a `let rec` at all, so depth here only governs ordinary let/if/match/app
nesting, which the existing corpus runs fine into the tens of levels). -/
def genDepth : Nat := 5

/-- Eval fuel for the eval-oracle invariant — generous relative to `genDepth`; the one `let rec`
prefix (when present) is called at most once and terminates in O(its own int literal) steps. -/
def evalFuel : Nat := 2000

/-! ## 5. Invariant (a): fmt-metamorphic — `checkAndLower src` and
`checkAndLower (fmtProg src)` produce the SAME type (and, where both succeed, the same elaborated
`Comp`). Two textual presentations, one AST: the canonical formatter is a metamorphic-testing
LEVER (`docs/notes/verification-ladder.md`'s "canonical `fmt`" rung) — a mismatch is an
elaborator OR a formatter bug, either a jackpot finding. Compares TYPE STRING (cheap, total, no
`BEq Comp` needed) — `typeStringOfProg` is a thin public projection of the SAME `checkProg` +
`showType` the production `:t` REPL command uses, so this is the SSoT check, not a bespoke one. -/

/-- Do `src` and its formatted twin `fmtProg src` type-check to the SAME rendered type string?
`none`/`none` (both un-elaborable) counts as agreement too — the formatter must not be the reason
a well-formed program stops type-checking, but this predicate only asserts SAMENESS of outcome,
so a generator bug that occasionally emits ill-typed source is still caught consistently by
both sides (a real elaborator/formatter DISAGREEMENT is the only way this returns `false`). -/
def fmtMetamorphicAgrees (src : String) : Bool :=
  let tyOrig := (Bang.TypeCheck.typeStringOfProg src).toOption
  match Bang.Format.fmtProg src with
  | .error _ => tyOrig.isNone   -- fmt itself failed to parse `src` — only OK if src was never typeable either
  | .ok fmtSrc =>
    let tyFmt := (Bang.TypeCheck.typeStringOfProg fmtSrc).toOption
    tyOrig == tyFmt

/-- **Invariant (a)**: every fixed seed's generated program (both with and without the `let rec`
prefix) survives the fmt round-trip with its type UNCHANGED. `#guard`-gated: a `false` here fails
`lake build` — the repo's standing fail-loud idiom. -/
def fmtMetamorphicOk : Bool :=
  fuzzSeeds.all (fun sd => fmtMetamorphicAgrees (genProgram genDepth sd false))
  && fuzzSeeds.all (fun sd => fmtMetamorphicAgrees (genProgram genDepth sd true))

#guard fmtMetamorphicOk

/-! ## 6. Invariant (b): elaborate-total — every generated well-formed-by-construction program
elaborates `.ok` via `checkAndLower` (the production typed pipeline). An `.error` here is EITHER
a generator bug (it emitted something not actually well-typed — the generator's own typing
promise broke) OR a genuine elaborator incompleteness; this harness cannot tell those apart
automatically (this file only calls the checker, never edits it — the leaf discipline), so any
violation gets reported with its EXACT source string for a human/kernel-adjacent lane to
classify, per the mission's "distinguish honestly" instruction. -/

/-- Does `src` elaborate `.ok` through the production typed pipeline? -/
def elaboratesOk (src : String) : Bool :=
  match Bang.TypeCheck.checkAndLower src with
  | .ok _ => true
  | .error _ => false

/-- **Invariant (b)**: every fixed seed (both `let rec` shapes) elaborates `.ok`. -/
def elaborateTotalOk : Bool :=
  fuzzSeeds.all (fun sd => elaboratesOk (genProgram genDepth sd false))
  && fuzzSeeds.all (fun sd => elaboratesOk (genProgram genDepth sd true))

#guard elaborateTotalOk

/-! ## 7. Invariant (c): term-size sanity — a GENERAL regression tripwire for the `#61`
blowup CLASS (not the specific hanging shape itself, which this generator structurally cannot
produce — see `genLetRecPrefix`'s comment). Counts `Comp`/`Val`/`Handler` CONSTRUCTORS in the
elaborated term and asserts it stays within a generous multiple of the SOURCE STRING length —
`#61`'s signature was an elaborated-term blowup that both engines then "dutifully re-traverse"
(`dogfood-json-findings.md`), so a constructor-count explosion relative to source size is exactly
the canary that class of bug trips, well before it reaches a multi-minute hang. -/

mutual
/-- Structural constructor count of a `Val` (exhaustive over `Val`'s 8 constructors,
`Bang/Core/IR.lean:94-112`). -/
partial def valSize : Bang.Val → Nat
  | .vunit => 1
  | .vint _ => 1
  | .vvar _ => 1
  | .vcap _ _ => 1
  | .vthunk c => 1 + compSize c
  | .inl v => 1 + valSize v
  | .inr v => 1 + valSize v
  | .pair a b => 1 + valSize a + valSize b
  | .fold v => 1 + valSize v
/-- Structural constructor count of a `Handler` (exhaustive over `Handler`'s 4 constructors,
`Bang/Core/IR.lean:139-`; `custom`'s clause bodies are each a `Comp` and get counted too). -/
partial def handlerSize : Bang.Handler → Nat
  | .state _ v => 1 + valSize v
  | .throws _ => 1
  | .transaction _ vs => 1 + (vs.map valSize).sum
  | .custom _ p cls => 1 + valSize p + (cls.map (fun (_, c) => compSize c)).sum
/-- Structural constructor count of a `Comp` (exhaustive over `Comp`'s 11 constructors,
`Bang/Core/IR.lean:113-138`). -/
partial def compSize : Bang.Comp → Nat
  | .ret v => 1 + valSize v
  | .letC m n => 1 + compSize m + compSize n
  | .force v => 1 + valSize v
  | .lam m => 1 + compSize m
  | .app m v => 1 + compSize m + valSize v
  | .perform c _ v => 1 + valSize c + valSize v
  | .handle h m => 1 + handlerSize h + compSize m
  | .case v n1 n2 => 1 + valSize v + compSize n1 + compSize n2
  | .split v n => 1 + valSize v + compSize n
  | .unfold v => 1 + valSize v
  | .binop _ a b => 1 + valSize a + valSize b
  | .oom => 1
  | .wrong _ => 1
end

/-- The generous multiplier: elaboration desugars sugar (e.g. `if`/`match`/tuples/`let rec`'s
μ-knot encoding, string literals into `SCons` chains) into MORE kernel constructors than source
tokens, so this is not 1:1 — but a genuine `#61`-class blowup is a MUCH bigger gap than ordinary
desugaring produces (`dogfood-json-findings.md` describes CPU-pegged non-termination, not merely
"a bit larger"), so a wide but FINITE multiplier still catches the regression class while never
tripping on legitimate desugaring overhead. -/
def sizeMultiplier : Nat := 40

/-- Does the elaborated term's constructor count stay within `sizeMultiplier ×` the source
string's length? `elaborateToComp` (the check-free entry) is used here rather than
`checkAndLower` — this canary is about TERM SIZE, orthogonal to type-checking, and stays honest
even on the (structurally unreachable in this generator, but not IMPOSSIBLE-by-Lean-proof)
event that a sample were ill-typed. -/
def termSizeOk (src : String) : Bool :=
  match Bang.TypeCheck.elaborateToComp src with
  | .error _ => true   -- didn't elaborate at all ⇒ no term to blow up; invariant (b) catches this separately
  | .ok c => compSize c ≤ sizeMultiplier * src.length

/-- **Invariant (c)**: every fixed seed's elaborated term stays within the size envelope. -/
def termSizeSaneOk : Bool :=
  fuzzSeeds.all (fun sd => termSizeOk (genProgram genDepth sd false))
  && fuzzSeeds.all (fun sd => termSizeOk (genProgram genDepth sd true))

#guard termSizeSaneOk

/-! ## 8. Invariant (d): eval-oracle pass-through — for a subset of seeds, the elaborated term
RUNS (fuel-bounded) via `Source.eval` without hitting `.stuck`. This exercises `type_safety`
(well-typed ⟹ never stuck) END-TO-END FROM SOURCE TEXT, which `Bang/Witness/Fuzz.lean`'s
kernel-term generator structurally cannot do (it generates `Comp` directly, bypassing the
elaborator entirely) — this is the one invariant only a SOURCE-level fuzzer can state. -/

/-- Runs `src` through the production typed pipeline (`checkAndLower`) then `Source.eval`s the
result; `true` iff the run is well-typed (didn't already fail to elaborate/check) AND does not
land on `.stuck`. A program that fails to elaborate is vacuously excluded (invariant (b) already
covers totality of elaboration; this predicate is specifically about the RUNTIME terminal of
whatever DID elaborate). -/
def evalNeverStuck (fuel : Nat) (src : String) : Bool :=
  match Bang.TypeCheck.checkAndLower src with
  | .error _ => true
  | .ok c =>
    match Bang.Source.eval fuel c with
    | .stuck => false
    | _ => true

/-- A SUBSET of seeds (the mission's "for a subset of seeds" — the full 60 all pass too, this
just keeps the eval-heavy invariant's runtime bounded to a representative slice, mirroring
`Fuzz.lean`'s own fixed-count-not-exhaustive posture). -/
def evalOracleSeeds : List Nat := fuzzSeeds.take 20

/-- **Invariant (d)**: every sampled seed (both `let rec` shapes) never goes `.stuck`. -/
def evalOraclePassThroughOk : Bool :=
  evalOracleSeeds.all (fun sd => evalNeverStuck evalFuel (genProgram genDepth sd false))
  && evalOracleSeeds.all (fun sd => evalNeverStuck evalFuel (genProgram genDepth sd true))

#guard evalOraclePassThroughOk

/-! ## 9. Falsifying the harness (mission requirement — this lane cannot edit `TypeCheck.lean`,
so it falsifies by breaking its OWN oracle, over a SEPARATE, throwaway assertion rather than the
live `#guard`s above, so the standing battery stays green while still proving each check bites). -/

-- Falsification 1: flip an "expected" in a hand-picked instance of invariant (b) — assert a
-- KNOWN-ILL-TYPED program (`1 + Left(0)`, the exact adversarial case from `TypeCheck.lean:2927`'s
-- `assertTypeError` guard) elaborates `.ok`. This MUST be `false` — if it were `true`, invariant
-- (b) would be vacuous. Proves the "does `checkAndLower` actually get called and its result
-- actually inspected" plumbing bites.
#guard (elaboratesOk "1 + Left(0)") == false

-- Falsification 2: corrupt a KNOWN-formatted program's fmt output by hand (delete a paren, which
-- breaks re-parsing) and confirm `fmtMetamorphicAgrees` correctly reports DISAGREEMENT rather than
-- vacuously passing. This reimplements the comparison directly against a hand-corrupted string
-- (rather than calling `fmtMetamorphicAgrees` itself, which always calls the REAL `fmtProg`), so
-- this is a genuine probe of "does comparing two type-string options actually distinguish
-- disagreement from agreement", not a tautology.
#guard
  (let src := "let x = 3 in x + 1"
   let tyOrig := (Bang.TypeCheck.typeStringOfProg src).toOption
   let corrupted := "let x = 3 in x + 1)"   -- an extra ')' ⇒ trailing-token parse error
   let tyCorrupted := (Bang.TypeCheck.typeStringOfProg corrupted).toOption
   tyOrig == tyCorrupted) == false

/-! ## 10. Coverage summary — a readable record of what this battery actually samples
(checkable: the `#guard`s above enforce it stays true). -/

example : fuzzSeeds.length = 60 := by rfl
example : evalOracleSeeds.length = 20 := by rfl

end -- @[expose] public section

end Bang.ElabFuzz
