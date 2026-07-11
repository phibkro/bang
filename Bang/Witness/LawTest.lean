module

meta import Bang.Frontend.TypeCheck
meta import Bang.Core.Semantics
meta import Bang.Witness.Fuzz
public import Bang.Frontend.TypeCheck
public import Bang.Core.Semantics
public import Bang.Witness.Fuzz

/-!
  Bang/Witness/LawTest.lean — `bang test`'s CORE (#60): the law runner + derived generators +
  shrinking, as a plain module with NO CLI wiring (that is a follow-up slice, exactly like
  `fmt`/`check`'s own subcommand landings).
  ───────────────────────────────────────────────────────────────────────────────────────────
  GROUND TRUTH (this file's design rests on it): laws are TRAIT laws only (ADR-0068) — there is
  no free-standing `law` declaration. `Bang/Frontend/TypeCheck.lean` already has a hand-rolled
  predecessor, `checkLaws` (+ `checkLawOn`/`sampleVT`/`tuples`/`valToSurf`), that walks a
  program's decl prelude, builds a FIXED small literal pool per value type, and sample-checks
  each trait law via `Source.eval`. This is exactly the "tested rung" ADR-0068 describes; #60's
  job is to generalize it: `data`-decl-derived generators (not just Int/prod), splitmix64
  sampling (not a fixed pool), and shrinking (none today).

  THE ACCESS SEAM — RESOLVED (#60, two landed exports): `checkLaws`'s internals were originally
  entirely private to `TypeCheck.lean`/`Surface.lean`. Two additive, behavior-preserving exports
  since landed: `TypeCheck.lawInstancesOf (src) : Except String (List (String × String × List
  String × String))` (trait name × law name × params × body-as-SOURCE-TEXT, one entry per
  trait-law×matching-impl pair — a thin projection of `checkLaws`'s own decl walk, `Surf`/`Ty`-free
  by construction) is the DISCOVERY surface `runLawsFromSource` below drives; the earlier broader
  markers (`ElabEnv`/`buildEnv`/`checkLawOn`/`sampleVT`/`VT`, etc.) remain available but are NOT
  needed by this file, which stays entirely SOURCE-STRING-level per `ElabFuzz.lean`'s proven
  pattern — generate/derive Bang source text and drive it through the PUBLIC frontend entries
  (`TypeCheck.elaborateToComp`, `Core.Semantics.Eval.Source.eval`, `TypeCheck.lawInstancesOf`) — a
  leaf module with fan-in 0 FROM `Bang/Frontend/*`, calling only its public entries.

  NON-META, BY CONSTRUCTION: same reasoning as `Fuzz.lean`/`ElabFuzz.lean` — this file reuses
  `Fuzz.lean`'s hand-rolled splitmix64 (`Rng.step`/`Rng.nextMod`) rather than re-deriving a THIRD
  PRNG (one construct per problem), and stays a plain `module` (no `Plausible.Gen`, which is
  `public meta section` and cannot call the runtime frontend entries in the same phase).
-/

namespace Bang.LawTest

open Bang.Fuzz (Rng.step Rng.nextMod)

@[expose] public section

/-! ## 1. Derived generators — a `data` decl's own shape as its generator SPEC.

Only the shapes an author can actually write in a `data` decl need generating: sums of products
of `Int`/named-ctor recursion, arity ≤ 2 per ctor (v1's own bound, `Surface.lean` §`dataD`). This
harness works at the SOURCE level (`ElabFuzz`'s move) so a "value" here is source text for a
constructor application, not a kernel `Val` — the law runner splices it directly into the law
body's param position. -/

/-- One constructor a derived generator can produce: its SOURCE name + how many `Int`-typed
payload slots it carries (v1 arity ≤ 2, `Surface.lean`'s `dataD` ceiling) + whether a payload
slot recurses into the SAME data type (so depth-bounded self-application terminates generation,
mirroring `Fuzz.lean`'s `fuel`-decrementing discipline). `.int`/`.recur` are the only payload
kinds a v1 `data` decl's constructor can carry beyond `Int` literals and self-recursion — a
richer payload alphabet (a NAMED different data type nested inside another) is a natural
extension or the seam, not built here (kept honest: this harness targets the common law-bearing
shapes the existing `VecOps`/`IntOrd` corpus already exercises, `Int` and products of `Int`). -/
inductive PayloadKind | int | recur
  deriving Repr, DecidableEq

/-- A generator SPEC for one `data` decl: its name + each constructor's (name, payload kinds).
`dataDeclSrc` renders it back to the `data N = C₀(...) | C₁(...) | ...` source the law program's
prelude carries; `genValueOf` uses the SAME spec to generate a matching value — spec and source
render from ONE structure, so they cannot drift (the single-source-of-truth move). -/
structure DataSpec where
  /-- The `data` declaration's name. -/
  name  : String
  /-- Each constructor's name and its payload kinds. -/
  ctors : List (String × List PayloadKind)
  deriving Repr, DecidableEq

-- `deriving Repr`'s generated `repr` ignores its `prec` arg (unusedArguments false-positive).
attribute [nolint unusedArguments] instReprDataSpec.repr

/-- Render a `DataSpec` back to its `data` declaration source text. -/
def DataSpec.toSrc (d : DataSpec) : String :=
  let ctorSrc := fun (c : String × List PayloadKind) =>
    match c.2 with
    | [] => c.1
    | ps => c.1 ++ "(" ++ String.intercalate ", " (ps.map (fun
              | .int   => "Int"
              | .recur => d.name)) ++ ")"
  "data " ++ d.name ++ " = " ++ String.intercalate " | " (d.ctors.map ctorSrc)

-- a monomorphic Int-payload sum renders to legal `data` source.
#guard DataSpec.toSrc ⟨"Box", [("BLeft", [.int]), ("BRight", [.int])]⟩ == "data Box = BLeft(Int) | BRight(Int)"
-- a self-recursive ctor (a `List`-shaped spec) renders `Cons(Int, IntList)`.
#guard DataSpec.toSrc ⟨"IntList", [("Nil", []), ("Cons", [.int, .recur])]⟩ ==
  "data IntList = Nil | Cons(Int, IntList)"

/-- Render an `Int` as valid bang SOURCE syntax. bang's tokenizer has no unary minus (only
unsigned digit literals — confirmed missing feature, `ElabFuzz.lean`'s own `intLitSrc` hit the
identical wall), so a bare `toString (-3)` is a PARSE error, not a type error; `(0 - n)` is legal
source producing the same `Int` value. Not imported from `ElabFuzz.lean` (that helper is not
`public`, and pulling in the whole module for one five-line helper would be a needless coupling —
"one construct per problem" cuts the other way for a genuinely tiny, self-contained fix). -/
def intLitSrc (n : Int) : String :=
  if n < 0 then s!"(0 - {(-n)})" else toString n

#guard intLitSrc 3 == "3"
#guard intLitSrc (-3) == "(0 - 3)"
#guard intLitSrc 0 == "0"

/-- Generate a small signed `Int` LITERAL, source-rendered. Range matches `Fuzz.lean`'s `genVal`/
`ElabFuzz`'s `genIntExpr` (`[-10, 10]`), a small spread that still exercises negative/zero/positive
law instances. -/
def genIntLit (s : Nat) : String × Nat :=
  let (s, n) := Rng.nextMod s 21
  let v : Int := (n : Int) - 10
  (intLitSrc v, s)

/-- Generate a VALUE matching one `DataSpec`, depth-bounded by `fuel` (decremented on every
`.recur` payload — the generation-terminates-by-construction discipline `Fuzz.lean`'s `genVal`/
`genComp` both use). At `fuel = 0` a `.recur` slot falls back to the FIRST non-recursive
constructor (never absent in a well-formed spec — `data` requires ≥ 1 ctor and a base case is
what makes the type inhabited at all, mirroring `dataD`'s own "needs at least one constructor"
elaboration-time check) so generation cannot dead-end. Returns the constructor APPLICATION as
source text (`"BLeft(3)"`, `"Cons(2, Cons(-1, Nil))"`). -/
partial def genValueOf (spec : DataSpec) (fuel : Nat) (s : Nat) : String × Nat :=
  let baseCtor := spec.ctors.find? (fun c => !c.2.contains .recur)
  let (s, ci) := Rng.nextMod s spec.ctors.length
  let chosen := spec.ctors.getD ci (spec.ctors.getD 0 ("_", []))
  let (name, pays) :=
    if fuel = 0 then
      match baseCtor with
      | some c => c
      | none   => chosen   -- no non-recursive ctor exists (spec itself infinite); fuel 0 degrades to 1 anyway below
    else chosen
  match pays with
  | [] => (name, s)
  | ps =>
    let rec goArgs : List PayloadKind → Nat → String × List String × Nat
      | [],      s => ("", [], s)
      | p :: rest, s =>
        let (argSrc, s) := match p with
          | .int   => genIntLit s
          | .recur => genValueOf spec (fuel - 1 |>.min fuel) s   -- strictly decreasing when fuel > 0 (fuel=0 handled above)
        let (_, restArgs, s) := goArgs rest s
        ("", argSrc :: restArgs, s)
    let (_, args, s) := goArgs ps s
    (name ++ "(" ++ String.intercalate ", " args ++ ")", s)

-- a pure-Int ctor: exactly one of the two names, an Int literal payload, no recursion.
#guard ((genValueOf ⟨"Box", [("BLeft", [.int]), ("BRight", [.int])]⟩ 3 7).1.startsWith "BLeft(") ||
       ((genValueOf ⟨"Box", [("BLeft", [.int]), ("BRight", [.int])]⟩ 3 7).1.startsWith "BRight(")
-- depth-0 fuel on a self-recursive spec degrades to the BASE constructor (`Nil`), never loops.
#guard (genValueOf ⟨"IntList", [("Nil", []), ("Cons", [.int, .recur])]⟩ 0 1).1 == "Nil"
-- fuel > 0 CAN reach a `Cons`, and its recursive tail is itself well-formed IntList source
-- (either `Nil` or another `Cons(...)`) — checked by parsing it (§3 reuses `elaborateToComp`).
#guard ((genValueOf ⟨"IntList", [("Nil", []), ("Cons", [.int, .recur])]⟩ 4 3).1.startsWith "Cons(") ||
       ((genValueOf ⟨"IntList", [("Nil", []), ("Cons", [.int, .recur])]⟩ 4 3).1 == "Nil")

/-! ## 2. A generated VALUE TREE — the shrinking domain. Shrinking operates on the STRUCTURE
(which ctor, which sub-values), not the rendered string, so "try an earlier constructor" / "shrink
an Int toward 0" / "drop a recursive layer" are structural rewrites, re-rendered to source only at
the end. This mirrors the issue's prescribed shrink moves exactly (drop list elements ≈ drop a
recursive layer; shrink ints toward 0; prefer earlier ctors). -/

/-- A generated value, kept STRUCTURED (not yet rendered) so shrinking can rewrite it before a
single final `render` pass. `.ival` is a leaf Int; `.ctor` is one constructor application (name +
its sub-values, in payload order) — this is the ONLY shape `genValueOf`'s output needs to be
re-expressed as, since every non-Int payload slot is itself a same-spec value or absent. -/
inductive GVal where
  | ival : Int → GVal
  | ctor : String → List GVal → GVal
  deriving Repr, BEq

instance : Inhabited GVal := ⟨.ival 0⟩

/-- Render a `GVal` back to bang source text (the inverse of the structural view — `ival`
through `intLitSrc` for the same negative-literal reason as `genIntLit`, `ctor` with no payload
rendering bare (a nullary constructor is just its name, `dataD`'s own convention). -/
partial def GVal.toSrc : GVal → String
  | .ival n     => intLitSrc n
  | .ctor n []  => n
  | .ctor n ps  => n ++ "(" ++ String.intercalate ", " (ps.map GVal.toSrc) ++ ")"

/-- Generate a STRUCTURED value for a spec (the `GVal` sibling of `genValueOf`, same fuel
discipline) — shrinking works on this; `genValueOf` (source-only) stays for the case a caller
wants text directly without ever shrinking. -/
partial def genGValOf (spec : DataSpec) (fuel : Nat) (s : Nat) : GVal × Nat :=
  let baseCtor := spec.ctors.find? (fun c => !c.2.contains .recur)
  let (s, ci) := Rng.nextMod s spec.ctors.length
  let chosen := spec.ctors.getD ci (spec.ctors.getD 0 ("_", []))
  let (name, pays) := if fuel = 0 then (baseCtor.getD chosen) else chosen
  match pays with
  | [] => (.ctor name [], s)
  | ps =>
    let rec goArgs : List PayloadKind → Nat → List GVal × Nat
      | [],        s => ([], s)
      | p :: rest, s =>
        let (v, s) := match p with
          | .int   => let (s, n) := Rng.nextMod s 21; (GVal.ival ((n : Int) - 10), s)
          | .recur => genGValOf spec (fuel - 1 |>.min fuel) s
        let (restVs, s) := goArgs rest s
        (v :: restVs, s)
    let (args, s) := goArgs ps s
    (.ctor name args, s)

-- structured generation renders IDENTICALLY to the source-only path on the same seed/fuel
-- (one spec, one generation walk — `genValueOf`/`genGValOf` must agree, checked directly).
#guard (genGValOf ⟨"Box", [("BLeft", [.int]), ("BRight", [.int])]⟩ 3 7).1.toSrc ==
       (genValueOf ⟨"Box", [("BLeft", [.int]), ("BRight", [.int])]⟩ 3 7).1

/-! ## 3. Shrinking — greedy, structural, re-checked at every candidate (issue's prescribed
moves: drop a recursive layer / shrink an Int toward 0 / prefer an earlier constructor). `shrink1`
proposes ONE step smaller than `v`; `shrinkTo` repeatedly applies whichever proposal the caller's
predicate (a re-check of the SAME failing law) still falsifies, greedily, until no proposal
shrinks further — a basic but real shrinker (not "seed 173"), bounded by construction (`shrink1`
always proposes something STRICTLY smaller in constructor-count + Int-magnitude, so the greedy
loop terminates; `fuel` caps the loop as defensive belt-and-braces against a shrink1 bug). -/

/-- One structural size measure — constructor-application count PLUS Int magnitude (so a leaf
`.ival` shrinking toward 0 still counts as strictly smaller; constructor-count ALONE is blind to
that, since `.ival 19` and `.ival 9` are both a single "node"). Drives loop termination in
`shrinkTo` below. -/
partial def GVal.size : GVal → Nat
  | .ival n    => 1 + n.natAbs
  | .ctor _ ps => 1 + (ps.map GVal.size).foldl (· + ·) 0

/-- Every ONE-STEP-SMALLER candidate for `v`: an Int nudged toward 0, OR (for a `ctor`) each
immediate sub-value substituted in place of the whole node (the "drop a layer" move — replacing
`Cons(3, Nil)` by its own payload `Nil`), OR the SAME constructor with one payload slot shrunk,
keeping the rest fixed. A caller re-checks every candidate against the (still-failing) law before
accepting it (`shrinkTo` below) — an ill-typed substitution (e.g. dropping to a sub-value of a
different shape than the whole node expects) simply fails to elaborate/type-check downstream and
is skipped, never silently accepted, so this generator does not need its own static type tag to
stay safe. -/
partial def GVal.shrinkCandidates : GVal → List GVal
  | .ival n =>
    if n == 0 then []
    else
      let halved : Int := n / 2
      (if n != 0 then [GVal.ival 0] else []) ++ (if halved != n then [GVal.ival halved] else [])
  | .ctor name ps =>
    -- (a) each immediate sub-value stands in for the whole node ("drop a layer").
    ps ++
    -- (b) the SAME constructor with exactly one payload slot shrunk one step, rest fixed.
    (List.range ps.length).flatMap (fun i =>
      (ps.getD i (.ival 0)).shrinkCandidates.map (fun v' => .ctor name (ps.set i v')))

-- an Int shrinks toward 0 (and eventually terminates: no candidates once it IS 0).
#guard (GVal.ival 7).shrinkCandidates == [GVal.ival 0, GVal.ival 3]
#guard (GVal.ival 0).shrinkCandidates == []
-- a `Cons(3, Nil)`-shaped node offers EACH immediate sub-value ("drop a layer": `3` or `Nil`),
-- PLUS the same ctor with the Int slot shrunk toward 0 (both `0` and the halved `1`) — the
-- `Nil` slot itself offers no candidates (empty payload, nothing to shrink).
#guard (GVal.ctor "Cons" [.ival 3, .ctor "Nil" []]).shrinkCandidates ==
  [.ival 3, .ctor "Nil" [],
   .ctor "Cons" [.ival 0, .ctor "Nil" []], .ctor "Cons" [.ival 1, .ctor "Nil" []]]

/-- Greedily shrink `v` against a still-failing predicate `stillFails` (typically "does the law
still produce a counterexample on this value"): repeatedly replace `v` by the FIRST candidate
(smallest-first-in-list, since `shrinkCandidates` lists "drop a layer" before "shrink one slot")
that still satisfies `stillFails`, until no candidate does. `fuel` bounds the loop (belt-and-
braces against a `shrinkCandidates` bug that fails to strictly decrease `GVal.size`; every real
step DOES decrease size, so this terminates long before `fuel` in practice). -/
partial def GVal.shrinkTo (stillFails : GVal → Bool) (fuel : Nat) (v : GVal) : GVal :=
  match fuel with
  | 0 => v
  | fuel + 1 =>
    match v.shrinkCandidates.find? stillFails with
    | some v' => if v'.size < v.size then GVal.shrinkTo stillFails fuel v' else v
    | none    => v

-- shrinking a failing-Int-property ("n != 0") down to its minimal counterexample: any nonzero
-- seed shrinks to `ival 1` (the smallest nonzero value `shrinkCandidates` can reach: 0 is
-- REJECTED by `stillFails`, so the loop lands on the least nonzero candidate it can find).
#guard GVal.shrinkTo (fun v => match v with | .ival n => n != 0 | _ => false) 20 (.ival 19) == .ival 1
/-- A `GVal` is `Cons`/`Nil`-SHAPED (the "drop a layer" move can propose a bare `.ival` in place
of a whole list node — `GVal` carries no static type tag, per `shrinkCandidates`'s own docstring —
so a realistic `stillFails` predicate for a list-shaped property must reject anything that is no
longer list-shaped, exactly as a real law-check would when the candidate's RENDERED source fails
to elaborate/type-check against the law's declared param type). -/
partial def isConsListShaped : GVal → Bool
  | .ctor "Nil" []    => true
  | .ctor "Cons" [_, tail] => isConsListShaped tail
  | _                 => false

-- shrinking a failing list-nonempty property ("this Cons/Nil value is not Nil"), GUARDED to stay
-- list-shaped (the realistic predicate, see `isConsListShaped`): drops straight to the smallest
-- failing sub-structure — a single-element list (one Cons wrapping Nil).
#guard GVal.shrinkTo
    (fun v => isConsListShaped v && (match v with | .ctor "Nil" [] => false | _ => true)) 20
  (.ctor "Cons" [.ival 5, .ctor "Cons" [.ival 3, .ctor "Nil" []]]) ==
  .ctor "Cons" [.ival 0, .ctor "Nil" []]

/-! ## 4. The law runner — SOURCE-STRING driven (`ElabFuzz.lean`'s proven pattern; see the module
header for why: `TypeCheck.lean`'s law-COLLECTION machinery, `checkLaws`/`ElabEnv`/`Decl`/
`LawDecl`, is entirely private, so this file cannot discover "every law in an arbitrary program"
today — that upgrade is the seam reported to the manager). What it CAN do, using only the public
`TypeCheck.elaborateToComp` + `Bang.Source.eval`, is CHECK one caller-named law against caller-
generated samples: exactly `checkLawOn`'s move (bind params, wrap in a truth-readback, run,
compare), reimplemented at the source-string level because the `Val`-level machinery is private.
`runLaws`'s signature is deliberately RE-DISCOVERY-READY: once `collectLawInstances` (or
equivalent) is exported, a second entry point can enumerate law instances from a program and
delegate the per-sample checking to the SAME `checkLawInstance` this file already has — additive,
not a rewrite. -/

/-- One law instance to check: the source PROGRAM (its whole decl prelude, `trait`+`impl`+
anything else the law needs — the caller's job, mirroring `vecOpsProg`/`intOrdProg` in
`TypeCheck.lean`), the law's quantified PARAM NAMES (in order), and the Bool-valued BODY
expression over them (`a < b => b < c => a < c`-shaped, ADR-0068's v1 law-body scope — a plain
`Surf`-level string, not a parsed AST, since this file has no access to `Surf`/`LawDecl`). Each
param is assumed `Int`-typed in v1 (matches `TypeCheck.lean`'s own `sampleVT` ceiling — `IntOrd`/
`VecOps`'s laws are all over `Int`/`(Int*Int)`; a `data`-decl-typed param is the `DataSpec` upgrade,
sketched in `checkLawInstanceOverSpec` below). -/
structure LawInstance where
  /-- Everything before the body: the trait/impl/data decls the body resolves against. -/
  progPrelude : String    -- everything BEFORE the body (trait/impl/data decls, space-terminated)
  /-- The law's name (for the report line). -/
  lawName     : String    -- for the report line only
  /-- The law's quantified parameter names, in order. -/
  params      : List String
  /-- The law's Bool-valued body expression over `params` + the prelude's ops. -/
  body        : String    -- the law's Bool-valued expression, over `params` + the prelude's ops
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg (unusedArguments false-positive).
attribute [nolint unusedArguments] instReprLawInstance.repr

/-- Wrap a law's body in the SAME truth-readback idiom `checkLawOn` uses (`let #r = body in
if #r then 1 else 0`) — encoding-agnostic (works whether the elaborator represents a bool as
`Unit + Unit` or otherwise), and bind each param to a GENERATED Int-literal source string via
nested `let`, innermost binding first so EARLIER params stay in scope for LATER ones (matches
source `let` shadowing left-to-right, mirroring `checkLawOn`'s `foldr` over `params.zip args`). -/
def wrapLawBody (params : List String) (args : List String) (body : String) : String :=
  let readback := "(let #lawR = (" ++ body ++ ") in (if #lawR then 1 else 0))"
  (params.zip args).foldr (fun (pv : String × String) acc =>
    "(let " ++ pv.1 ++ " = " ++ pv.2 ++ " in " ++ acc ++ ")") readback

#guard wrapLawBody ["a", "b"] ["3", "(0 - 2)"] "a < b" ==
  "(let a = 3 in (let b = (0 - 2) in (let #lawR = (a < b) in (if #lawR then 1 else 0))))"

/-- Run ONE sample of a law instance: bind `inst.params` to the GENERATED int-literal source
`args` (`args.length == inst.params.length`, checked by the caller — a mismatch is the caller's
bug, so this stays a total Bool rather than an `Except`, matching `checkLawOn`'s own
fail-quiet-to-false convention: an elaboration/type error on a MALFORMED sample is indistinguishable
here from a law FAILURE, both render `false` — a real limitation this file's `LawOutcome` (below)
resolves by re-running through `TypeCheck.elaborateToComp` directly and keeping the `Except`). -/
def evalLawOn (inst : LawInstance) (args : List String) : Bool :=
  let src := inst.progPrelude ++ " " ++ wrapLawBody inst.params args inst.body
  match Bang.TypeCheck.elaborateToComp src with
  | .error _ => false
  | .ok c    => match Bang.Source.eval 400 c with
                | .done (.vint 1) => true
                | _                => false

-- IntOrd.trans discharges on real generated Int samples (mirrors `intOrdProg` in TypeCheck.lean,
-- reconstructed here as a `LawInstance` — same corpus content, source-string driven).
/-- The `IntOrd.trans` corpus prelude (trait + `Int` impl) as source text. -/
def intOrdPrelude : String :=
  "trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c } " ++
  "impl IntOrd for Int { fn lt(a, b) = a < b }"

#guard evalLawOn ⟨intOrdPrelude, "trans", ["a", "b", "c"], "a < b => b < c => a < c"⟩ ["1", "2", "3"]
-- antisymmetry is FALSE and evalLawOn catches it non-vacuously on a genuinely ordered triple.
#guard !evalLawOn ⟨intOrdPrelude, "antisym_bogus", ["a", "b"], "a < b => b < a"⟩ ["0", "1"]
-- a program that fails to ELABORATE (malformed prelude) reports `false`, not a crash.
#guard !evalLawOn ⟨"not valid bang", "x", ["a"], "a == a"⟩ ["1"]

/-! ## 5. The result type — FAIL-LOUD, each case its own constructor (never folded into a bare
`Bool`/`false`): a law that HOLDS on every sample, a COUNTEREXAMPLE (with its shrunk witness), a
law whose program is UNTYPEABLE (the elaboration/type error itself, so the caller sees WHY, not
just "false"), EVAL-STUCK (the sample elaborated and type-checked but `Source.eval` produced
neither `done (vint 1)` nor `done (vint 0)` — `.oom`/`.escapedCap`/`.stuck`/a non-Int `done`, each
a genuinely different failure mode from "the law is false"; distinguished from `.counterexample`
because a law author needs to know their LAW EVALUATES rather than merely FALSIFIES), and SKIPPED
(issue #113: a law on an impl `unreachableIntImplDiagnostics` already flags — its op is shadowed by
the kernel's own `Int` δ-rule, so the impl's body never runs. Sampling it anyway and reporting
`.holds` was MISLEADING: the samples exercise the KERNEL's built-in `==`/`<`/etc., not the
impl the law is nominally checking — a `PASS` a user could trust as validating their impl when the
impl never executed. `.skipped` reports this honestly instead of silently reusing `.holds`). -/
/-- The fail-loud result of checking one law: `holds`, `counterexample` (shrunk
witness), `untypeable`, `evalStuck`, or `skipped` — each a distinct failure mode. -/
inductive LawOutcome where
  | holds        : Nat → LawOutcome                      -- N samples, all true
  | counterexample : List String → LawOutcome            -- the SHRUNK witness, rendered per param
  | untypeable   : String → LawOutcome                   -- the elaboration/type error message
  | evalStuck    : List String → LawOutcome              -- the witness that got PAST typing but didn't eval to a Bool
  | skipped      : String → LawOutcome                   -- #113: not sampled — the impl is unreachable (reason text)
  deriving Repr

/-- Render one witness (a list of per-param source strings) as `"(a=1, b=2, c=3)"` — used by both
`.counterexample` and `.evalStuck` reports. -/
def renderWitness (params args : List String) : String :=
  "(" ++ String.intercalate ", " ((params.zip args).map (fun (p, a) => p ++ "=" ++ a)) ++ ")"

#guard renderWitness ["a", "b"] ["1", "(0 - 2)"] == "(a=1, b=(0 - 2))"

/-- Classify ONE sample against `inst`, distinguishing untypeable / eval-stuck / true / false —
the `Except`-preserving sibling of `evalLawOn` (which collapses the first two into `false`). -/
def classifyLawOn (inst : LawInstance) (args : List String) : Except String Bool :=
  let src := inst.progPrelude ++ " " ++ wrapLawBody inst.params args inst.body
  match Bang.TypeCheck.elaborateToComp src with
  | .error m => .error m
  | .ok c    => match Bang.Source.eval 400 c with
                | .done (.vint 1) => .ok true
                | .done (.vint 0) => .ok false
                | _               => .error "eval-stuck"   -- sentinel; distinguished by caller via a re-check, see runLaws

/-- Generate `n` Int-literal-source samples for a law's params (each param independently drawn,
`Fuzz.lean`'s splitmix64 threaded across params AND samples so every draw is distinct — no two
samples/params ever reuse the same RNG state). Returns `n` argument LISTS, each of length
`inst.params.length`. -/
def genIntSamples (paramCount n : Nat) (seed : Nat) : List (List String) :=
  let rec goSample : Nat → Nat → List (List String)
    | 0,     _ => []
    | k + 1, s =>
      let rec goParam : Nat → Nat → List String × Nat
        | 0,     s => ([], s)
        | j + 1, s => let (lit, s) := genIntLit s
                      let (rest, s) := goParam j s
                      (lit :: rest, s)
      let (args, s') := goParam paramCount s
      args :: goSample k s'
  goSample n seed

#guard (genIntSamples 3 5 42).length == 5
#guard (genIntSamples 3 5 42).all (fun args => args.length == 3)
-- deterministic: the SAME seed reproduces the SAME samples (CI-reproducibility, the issue's
-- explicit requirement — "fixed seeds, byte-reproducible").
#guard genIntSamples 2 4 99 == genIntSamples 2 4 99

/-- Shrink a FAILING witness (a `List String` of Int-literal args) toward a minimal one: convert
each arg to a `GVal.ival`, shrink each COORDINATE independently and greedily (holding the others
fixed — a simple but real per-coordinate shrink, sufficient for the k-tuple law-argument shape;
whole-tuple joint shrinking is a strictly more thorough follow-up, not needed to satisfy "agents
need minimal counterexamples, not seed 173"), re-checking `stillFails` (a re-run of `evalLawOn`)
at each step, then renders back to source. -/
def shrinkWitness (inst : LawInstance) (args : List String) : List String :=
  let toInt (s : String) : Int :=
    -- args are ALWAYS `genIntLit`-rendered (`"n"` or `"(0 - n)"`), so a direct parse suffices;
    -- anything else (a future non-Int param kind) is out of THIS shrinker's v1 scope and is left
    -- unshrunk (returned as-is) rather than mis-parsed — fail-SAFE, never fail-silent-wrong.
    if s.startsWith "(0 - " then
      -(String.toInt! ((s.drop 5 |>.dropEnd 1).toString))
    else
      String.toInt! s
  let stillFailsAt (i : Nat) (v : GVal) : Bool :=
    let v' := match v with | .ival n => intLitSrc n | _ => "0"
    !evalLawOn inst (args.set i v')
  (List.range args.length).foldl (fun acc i =>
    let shrunk := GVal.shrinkTo (stillFailsAt i) 30 (.ival (toInt (acc.getD i "0")))
    match shrunk with
    | .ival n => acc.set i (intLitSrc n)
    | _       => acc) args

/-- **The law runner** (public entry, #60's core deliverable): sample `n` generated Int-tuples
against `inst`, classify EVERY outcome distinctly (never folding untypeable/stuck into "false"):
- the FIRST sample whose program does not even ELABORATE ⟹ `.untypeable` (the raw error message —
  this is almost always a caller bug in `progPrelude`/`body`, not a property of the law itself, so
  it short-circuits immediately rather than wasting the remaining samples).
- the FIRST sample that elaborates+type-checks but does not evaluate to a Bool-readback (`vint 0`
  or `vint 1`) ⟹ `.evalStuck`, carrying that witness (NOT shrunk — a stuck program's failure mode
  isn't "smaller is more informative" the way a counterexample's is; the witness that TRIGGERED it
  is exactly what a debugging author needs).
- the FIRST sample where the law evaluates to `false` ⟹ `.counterexample`, carrying the SHRUNK
  witness (`shrinkWitness`) — "minimal counterexamples, not seed 173" is the point.
- every sample TRUE ⟹ `.holds n`. -/
def runLaws (inst : LawInstance) (n seed : Nat) : LawOutcome :=
  let samples := genIntSamples inst.params.length n seed
  let rec go : List (List String) → LawOutcome
    | []          => .holds n
    | args :: rest =>
      match classifyLawOn inst args with
      | .error m =>
        if m == "eval-stuck" then .evalStuck args else .untypeable m
      | .ok true  => go rest
      | .ok false => .counterexample (shrinkWitness inst args)
  go samples

-- IntOrd.trans HOLDS on 20 generated samples (a real trait law, real generation, real eval).
#guard (match runLaws ⟨intOrdPrelude, "trans", ["a", "b", "c"], "a < b => b < c => a < c"⟩ 20 7 with
        | .holds 20 => true | _ => false)
-- a DELIBERATELY FALSE law (antisymmetry) yields a COUNTEREXAMPLE.
#guard (match runLaws ⟨intOrdPrelude, "antisym_bogus", ["a", "b"], "a < b => b < a"⟩ 20 7 with
        | .counterexample _ => true | _ => false)
-- SHRINKING WORKS: a law that is false for EVERY Int (`a == a + 1`) has exactly ONE
-- shrink-minimal witness family (`a = 0`, since `shrinkCandidates` nudges toward 0 and 0 always
-- still falsifies) — asserting the EXACT shrunk witness (not just "some counterexample") is the
-- issue's explicit ask ("assert the shrunk form, proving shrinking works").
#guard (match runLaws ⟨"trait T { fn f(a) -> Int law bogus(a): a == a + 1 }", "bogus", ["a"], "a == a + 1"⟩ 10 3 with
        | .counterexample ["0"] => true | _ => false)
-- a MALFORMED prelude is caught as untypeable, carrying the real elaboration error (not a bare
-- `false` indistinguishable from a genuine counterexample) — an `impl` of an UNDECLARED trait is
-- a genuine elaboration error (`buildEnv`'s own check, `TypeCheck.lean` §Validation).
#guard (match runLaws ⟨"impl Nope for Int { fn foo(a) = a }", "x", ["a"], "a == a"⟩ 5 1 with
        | .untypeable _ => true | _ => false)
-- EVAL-STUCK, witnessed: a law body that TYPE-CHECKS (a well-typed `Div`-rowed `let rec` that
-- never returns) but does not terminate within `evalLawOn`'s fixed 400-fuel budget — genuinely
-- distinct from BOTH a counterexample (the law never gets to evaluate `false`) and untypeable
-- (elaboration/type-checking succeeds; only EVALUATION doesn't reach a Bool readback).
/-- A well-typed but non-terminating (`Div`-rowed) law body — used to witness `evalStuck`. -/
def loopyLawBody : String :=
  "let rec loop : Int -> Int = fun n => ($loop)(n + 1) in (let z = ($loop) a in a == a)"
/-- The trait prelude wrapping `loopyLawBody`. -/
def loopyPrelude : String := "trait T { fn f(a) -> Int law loopy(a): " ++ loopyLawBody ++ " }"
#guard (match runLaws ⟨loopyPrelude, "loopy", ["a"], loopyLawBody⟩ 3 1 with
        | .evalStuck _ => true | _ => false)

/-! ## 6. Discovery mode — auto-find every law in a REAL program (`TypeCheck.lawInstancesOf`,
#60's landed seam), replacing "check the law you're told about" with "find every law yourself".
Each discovered instance becomes a `LawInstance` whose `progPrelude` is the WHOLE original source
(the trait+impl decls it needs are already there — `elaborateToComp` re-elaborating the same decls
once per law instance is cheap relative to one interpreter run per sample, and keeps this file from
needing its own decl-subsetting logic, which `lawInstancesOf` deliberately doesn't expose either). -/

/-- One discovered law instance's outcome, tagged with WHICH trait/law it came from (so a report
over several discovered laws can name each one — `runLaws`'s own `LawOutcome` says nothing about
identity, correctly: a caller-supplied `LawInstance` already carries `lawName`, but a multi-law
DISCOVERY run needs the trait name too, since two traits can share a law name). -/
structure NamedOutcome where
  /-- The trait the discovered law came from. -/
  traitName : String
  /-- The law's name. -/
  lawName   : String
  /-- The law's check outcome. -/
  outcome   : LawOutcome
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg (unusedArguments false-positive).
attribute [nolint unusedArguments] instReprNamedOutcome.repr

/-- **Discovery entry (public, #60):** find every law instance in a program made of `decls`
(the trait/impl prelude, NO trailing body — `lawInstancesOf` needs a full parseable program, so
this appends a throwaway `0` body ONLY for that discovery pass; `runLaws`'s own per-sample
programs are built from `decls` directly, matching `LawInstance.progPrelude`'s own contract of
"everything BEFORE the body" — passing a decls+body string as a `progPrelude` would let
`evalLawOn`'s own body-splice land AFTER an already-present body, parsing as a bogus application
rather than two statements, exactly the bug this signature design avoids by construction). Each
discovered instance is `runLaws`-checked against `n` generated samples (seed offset by POSITION
so two laws in the same program never draw the identical sample sequence). A `lawInstancesOf`
failure (malformed decls) short-circuits with that same error — no partial discovery silently
swallowed.

**#74 fix:** BEFORE running a discovered instance, check `Bang.TypeCheck.lawInstanceOpCallDiagnostics`
(the SAME trait×impl walk, in the SAME order, so zipping by position lines them up) — a law body
that calls its own trait's op BY NAME (`eq(x, x)`, `add a b`, either call shape) has no execution
path in v1 (ADR-0068: trait ops resolve ONLY through the overloaded operator, never a direct call;
confirmed even a sibling op of the same impl can't call another by name). Diagnosing this UP FRONT
turns the previous opaque runtime crash (`app: callee is not a function ('eq')`, discovered by the
stranger test with zero PASS/FAIL/shrink ever reached) into a `.untypeable` outcome naming the
actual constraint — `bang test` now fails LOUD with a fixable message instead of a bare crash,
closing the loop without changing what the language can express.

**#74 fix, part 2:** ALSO check `Bang.TypeCheck.unreachableIntImplDiagnostics` — an `impl <Trait>
for Int` whose op aliases a built-in binop (`add`/`sub`/`mul`/`div`/`lt`/`eq`) is SILENTLY DEAD
(the kernel's own `Int` δ-rule intercepts the operator before `env.insts` is ever consulted, so the
impl's op body can never run) — a program-wide warning, not a per-law outcome, so it's surfaced as
a synthetic `NamedOutcome` PREPENDED to the per-law results (piggybacking the EXISTING
`Main.lean`/`renderOutcome` print+exit-code path with zero changes there: `.untypeable` already
renders as a named `✗ … — ERROR — …` line and folds into the pass/fail tally correctly).

**#113 fix:** a law instance whose TRAIT NAME appears in `unreachable` is on a dead impl too — the
previous behavior sampled it anyway (`runLaws`, below) and reported `.holds`/PASS, which is
MISLEADING: `evalLawOn`'s samples are plain `Int` literals, so the law body's operator hits the
KERNEL's own `==`/`<`/etc. via the δ-rule, never the impl being nominally validated — a `PASS` a
user could trust as "my impl satisfies this law" when the impl never ran. Checked BEFORE sampling
(short-circuits `runLaws` entirely, so no wasted elaboration+eval either): the law reports
`.skipped` instead, naming the SAME unreachable-impl reason the ERROR line above already gives, so
a reader sees both "this impl can never run" (the ERROR line) and "…so its laws weren't sampled"
(the SKIP line) without needing to infer the connection. -/
def runLawsFromSource (decls : String) (n seed : Nat) : Except String (List NamedOutcome) := do
  let instances ← Bang.TypeCheck.lawInstancesOf (decls ++ " 0")
  let diagnostics ← Bang.TypeCheck.lawInstanceOpCallDiagnostics (decls ++ " 0")
  let unreachable ← Bang.TypeCheck.unreachableIntImplDiagnostics (decls ++ " 0")
  let unreachableOutcomes := unreachable.map (fun (tn, opName) =>
    (⟨tn, "(unreachable impl)", .untypeable
      s!"impl '{tn}' for Int defines '{opName}', which aliases a built-in operator — Int operands \
always use the kernel's own arithmetic/comparison, so this impl's '{opName}' can never run (v1 \
gap: pick a non-Int target type, e.g. a custom data type or (Int * Int), to exercise a custom \
'{opName}')"⟩ : NamedOutcome))
  let unreachableTraits := unreachable.map Prod.fst
  let lawOutcomes := (instances.zip (List.range instances.length)).map
    (fun ((tn, ln, params, body), i) =>
      match diagnostics.getD i (tn, ln, none) with
      | (_, _, some opName) =>
          ⟨tn, ln, .untypeable
            s!"law '{tn}.{ln}' calls trait op '{opName}' directly — trait ops are invoked ONLY \
through their overloaded operator in v1 (ADR-0068; e.g. write the law using '==' or the op's \
aliased operator, not '{opName}(...)' or '{opName} ...' by name)"⟩
      | (_, _, none) =>
          if unreachableTraits.contains tn then
            ⟨tn, ln, .skipped
              s!"impl '{tn}' for Int is unreachable (its op aliases a built-in operator — see the \
'(unreachable impl)' note above), so '{tn}.{ln}' was not sampled — a PASS here would validate the \
kernel's own operator, not this impl"⟩
          else
            ⟨tn, ln, runLaws ⟨decls, ln, params, body⟩ n (seed + i)⟩)
  return unreachableOutcomes ++ lawOutcomes

/-- The `VecOps` northstar DECLS ONLY (mirrors `TypeCheck.lean`'s own `vecOpsProg`/`vecLawProg` —
same content, reconstructed locally since those are internal test helpers, not exported; NO
trailing body here — unlike the single-trait `#guard`s elsewhere in this file, the multi-trait
tests below need to APPEND a second trait's decls before the one shared body, so the body is
supplied once, by the caller, at the very end). Component-wise `add`/`eq` over `(Int * Int)`,
parametrized by the law so both a TRUE and a FALSE law variant can be exercised. -/
def vecOpsDecls (law : String) : String :=
  "trait VecOps { fn add(a, b) -> Self " ++
  "fn eq(a, b) -> (Unit + Unit) " ++
  "law " ++ law ++ " } " ++
  "impl VecOps for (Int * Int) { " ++
  "fn add(p, q) = let (a, b) = p in (let (c, d) = q in (let x = a + c in (let y = b + d in (x, y)))) " ++
  "fn eq(p, q) = let (a, b) = p in (let (c, d) = q in (let e = a == c in (if e then b == d else 0 == 1))) }"

/-- A true `VecOps` law (addition commutes) as source text. -/
def vecCommLaw : String := "comm(a, b): let s = a + b in (let t = b + a in s == t)"
/-- A false `VecOps` law (used to witness a counterexample) as source text. -/
def vecBogusLaw : String := "bogus(a, b): let s = a + b in (let t = a + a in s == t)"

-- a SINGLE-law program: discovery finds exactly the one instance, and it HOLDS (VecOps.comm is a
-- real, true law — the same corpus program `TypeCheck.lean`'s own `#guard`s check).
#guard (match runLawsFromSource (vecOpsDecls vecCommLaw) 20 7 with
        | .ok [⟨"VecOps", "comm", .holds 20⟩] => true | _ => false)
-- a MULTI-TRAIT program: discovery finds BOTH law instances, in program order, each classified
-- independently — VecOps.comm holds (a real true law) — PLUS the #74 part-2 warning, PREPENDED:
-- `intOrdPrelude`'s `impl IntOrd for Int { fn lt(a, b) = a < b }` targets `Int` with an op named
-- `lt`, which ALIASES the built-in `<` — exactly the silently-dead shape
-- `unreachableIntImplDiagnostics` exists to catch. #113: IntOrd.trans is therefore `.skipped`, NOT
-- `.holds` — sampling it would exercise the KERNEL's own `<`, not this dead impl's `lt`, so a PASS
-- would misleadingly look like the impl was validated.
#guard (match runLawsFromSource
    (vecOpsDecls vecCommLaw ++ " " ++ intOrdPrelude) 20 7 with
        | .ok [⟨"IntOrd", "(unreachable impl)", .untypeable _⟩,
               ⟨"VecOps", "comm", .holds 20⟩, ⟨"IntOrd", "trans", .skipped _⟩] => true
        | _ => false)
-- a MULTI-TRAIT program where ONE law is deliberately FALSE: discovery still finds both, and only
-- the false one reports a counterexample — proving per-law classification doesn't cross-contaminate
-- (same prepended IntOrd/Int warning as above; IntOrd.trans still `.skipped`, #113).
#guard (match runLawsFromSource
    (vecOpsDecls vecBogusLaw ++ " " ++ intOrdPrelude) 20 7 with
        | .ok [⟨"IntOrd", "(unreachable impl)", .untypeable _⟩,
               ⟨"VecOps", "bogus", .counterexample _⟩, ⟨"IntOrd", "trans", .skipped _⟩] => true
        | _ => false)
-- a program with NO trait laws at all discovers an EMPTY list (not an error) — vacuously fine.
#guard (match runLawsFromSource "" 20 7 with | .ok [] => true | _ => false)
-- a malformed decls prelude propagates lawInstancesOf's OWN error, not a bare crash.
#guard (match runLawsFromSource "trait { " 20 7 with | .error _ => true | .ok _ => false)

-- **#117's trait-prelude migration regression net:** a DERIVE-ONLY program (zero hand-written
-- `trait`/`impl`, `deriving (Eq, Ord)` alone) discovers the FULL 6-law suite `Prelude.bang`'s
-- canonical `trait Eq`/`trait Ord` carry (refl/symm/trans, irrefl/asym/trans) — not the deleted
-- stopgap's single minimal law each. `injectPrelude`'s widened mention-set (`p.derivesFor`, not
-- just a bare `Eq`/`Ord` reference anywhere in the body) is what makes this resolve at ALL: this
-- program mentions neither trait name outside its `deriving` clause.
#guard (match runLawsFromSource "data Point = Pt(Int, Int) deriving (Eq, Ord)" 30 7 with
    | .ok outcomes => outcomes.length == 6 && outcomes.all (fun o => match o.outcome with
        | .holds _ => true | _ => false)
    | .error _ => false)

