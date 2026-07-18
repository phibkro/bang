module

-- `meta import`s bring the COMPILED frontend/witness code into the elaboration phase so the `#guard`
-- gates below can NATIVELY evaluate `exportGoal` (which calls `elaborateToComp`/`typeStringOfProg`/
-- `wrapLawBody`); `public import`s re-export the same modules for this file's own public signatures.
-- Same two-phase pattern as `ElabFuzz.lean`/`LawTest.lean` (a leaf over the public frontend).
meta import Bang.Frontend.TypeCheck
meta import Bang.Core.Semantics
meta import Bang.Core.Fingerprint
meta import Bang.Witness.LawTest
public import Bang.Frontend.TypeCheck
public import Bang.Core.Semantics
public import Bang.Core.Fingerprint
public import Bang.Witness.LawTest

/-!
  Bang/Witness/ProofExport.lean — Q43 R1: a bang `law` becomes a Lean PROOF GOAL (arm B, with
  `sorry`). The GOAL EMITTER only — no proof discharge, no cache infra (those are R2/R3).
  ───────────────────────────────────────────────────────────────────────────────────────────
  RULED DESIGN (`docs/notes/proof-export-survey.md` §6 ADR-INPUTS, operator 2026-07-09):
    • GOAL SHAPE = arm B: `∀ args, Source.eval N₀ (bodyComp args) = .done (.vint 1)` — the
      universally-quantified form of the EXACT readback proposition `bang test` fuzzes
      (`LawTest.wrapLawBody`'s `let #r = body in if #r then 1 else 0` idiom). `bodyComp` is the law
      body LAMBDA-abstracted over its params, so it elaborates to a CLOSED `Comp` (a `lam`-nest) and
      `bodyComp args` is `.app (.app … arg₁) … argₖ`.
    • TOTAL-ONLY: `#prove` on a non-⊥-row law is a TYPED REJECTION, not a goal (a `Div`-rowed law
      stays on the fuzzed rung, visibly). Proof-eligibility is TYPED — read off the row.
    • CONTENT-ADDRESS INDEX = the shared `Bang.CoreFingerprint` fold of the ELABORATED `Comp`
      (de-Bruijn, so α/param-rename-invariant; post-parse+`fmt`, so formatting-invariant) — NOT
      source text (§3.1). It is UInt64/hex and non-cryptographic at R1; the proof artifact is always
      rechecked, while an unchecked R2/R3 cache must use a collision-safe, version-domain key.

  SCOPE / SEAM DISCIPLINE (this is a LEAF over the public frontend, exactly like `ElabFuzz.lean`/
  `LawTest.lean`): it CALLS only the public entries `TypeCheck.elaborateToComp`,
  `TypeCheck.typeStringOfProg`, and `TypeCheck.lawInstancesOf`, plus `LawTest.wrapLawBody` for the
  readback idiom (SSoT — the runner and the goal must phrase truth identically, else test≠proof). It
  touches NO `TypeCheck.lean`/`Surface.lean` internals and NO `Main.lean`/CLI surface (the `#prove`
  pragma + `proofs/` writer + report line are named FOLLOW-UP slices).

  TOTAL-ONLY, THE STRUCTURED CHECK: "the law body's row = ⊥" is read off the RAW `EffRow` via the
  public `TypeCheck.checkProgRow` (a minimal row projection of `checkProg`, landed for exactly this
  gate). The predicate is `decide (φ = ∅)`, immune to any pretty-printer formatting; a
  non-⊥ row is REJECTED with the row named from the public built-in label constants
  (`Bang.Surface.{exn,state,stm,div}Label`). (The earlier string-suffix reading of `typeStringOfProg`
  is retired — the structured `EffRow` decision replaces it.)
-/

namespace Bang.ProofExport

open Bang (Comp Val Handler BinOp)

@[expose] public section

/-! ## 1. Content-address compatibility wrapper

The structural fold is owned by `Bang.CoreFingerprint`, where compiler-query and proof-export
consumers share it. This wrapper preserves ProofExport's R1 API and artifact shape. It is still a
64-bit experimental index whose proof consumer rechecks the emitted goal; it is not safe as the key
of an unchecked persistent compiler cache. -/

/-- ProofExport's compatibility name for the shared elaborated-`Comp` fingerprint. -/
def contentAddress (c : Comp) : String := Bang.CoreFingerprint.fingerprint c

/-! ## 2. Render an elaborated `Comp`/`Val`/`Handler` to LEAN-TERM SOURCE.

The goal artifact must be a SELF-CONTAINED `.lean` file that COMPILES under `lake env lean`, so the
elaborated law `Comp` appears as literal Lean syntax (`Bang.Comp.letC (.ret (.vint 3)) …`). The
renderer is TOTAL (every constructor handled) though a TOTAL-fragment law never contains
`perform`/`handle`/`custom`/`oom`/`wrong` — handling them keeps the emitter robust and the seam
honest (a mis-classified non-total law would still render, then fail the total-only gate first). -/

/-- Render a `BinOp` as its Lean anonymous-constructor source (`.add`, …). -/
def showBinOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul"
  | .div => ".div" | .lt => ".lt" | .eq => ".eq"

/-- A source string escaped for the emitted Lean source (`wrong` payloads / op ids). -/
def strLit (s : String) : String :=
  "\"" ++ (s.foldl (fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | _    => String.singleton c)) "") ++ "\""

/-- `Int` literal as Lean source — parenthesize negatives so `.vint (-3)` parses. -/
def intLit (n : Int) : String := if n < 0 then s!"({n})" else toString n

/-- Render a custom clause key as literal Lean-term source. -/
def showClauseKey : ClauseKey → String
  | .plain op => s!"(Bang.ClauseKey.plain {strLit op})"
  | .updating op => s!"(Bang.ClauseKey.updating {strLit op})"

mutual
/-- Render a value as literal Lean-term source (`Bang.Val.…`). -/
partial def showVal : Val → String
  | .vunit      => "Bang.Val.vunit"
  | .vint n     => s!"(Bang.Val.vint {intLit n})"
  | .vvar i     => s!"(Bang.Val.vvar {i})"
  | .vcap n ℓ   => s!"(Bang.Val.vcap {n} {ℓ})"
  | .vthunk c   => s!"(Bang.Val.vthunk {showComp c})"
  | .inl v      => s!"(Bang.Val.inl {showVal v})"
  | .inr v      => s!"(Bang.Val.inr {showVal v})"
  | .pair a b   => s!"(Bang.Val.pair {showVal a} {showVal b})"
  | .fold v     => s!"(Bang.Val.fold {showVal v})"
/-- Render a computation as literal Lean-term source (`Bang.Comp.…`). -/
partial def showComp : Comp → String
  | .ret v         => s!"(Bang.Comp.ret {showVal v})"
  | .letC m n      => s!"(Bang.Comp.letC {showComp m} {showComp n})"
  | .force v       => s!"(Bang.Comp.force {showVal v})"
  | .lam m         => s!"(Bang.Comp.lam {showComp m})"
  | .app m v       => s!"(Bang.Comp.app {showComp m} {showVal v})"
  | .perform c op v => s!"(Bang.Comp.perform {showVal c} {strLit op} {showVal v})"
  | .handle h m    => s!"(Bang.Comp.handle {showHandler h} {showComp m})"
  | .case v n₁ n₂  => s!"(Bang.Comp.case {showVal v} {showComp n₁} {showComp n₂})"
  | .split v n     => s!"(Bang.Comp.split {showVal v} {showComp n})"
  | .unfold v      => s!"(Bang.Comp.unfold {showVal v})"
  | .binop op v w  => s!"(Bang.Comp.binop {showBinOp op} {showVal v} {showVal w})"
  | .oom           => "Bang.Comp.oom"
  | .wrong s       => s!"(Bang.Comp.wrong {strLit s})"
/-- Render a handler as literal Lean-term source (`Bang.Handler.…`). -/
partial def showHandler : Handler → String
  | .state ℓ v        => s!"(Bang.Handler.state {ℓ} {showVal v})"
  | .throws ℓ         => s!"(Bang.Handler.throws {ℓ})"
  | .transaction ℓ vs => s!"(Bang.Handler.transaction {ℓ} [{String.intercalate ", " (vs.map showVal)}])"
  | .custom ℓ p cls   =>
      let clsSrc := String.intercalate ", " (cls.map (fun (key, c) => s!"({showClauseKey key}, {showComp c})"))
      s!"(Bang.Handler.custom {ℓ} {showVal p} [{clsSrc}])"
end

/-! ## 3. The goal emitter. -/

/-- The total-fragment fuel bound baked into the arm-B goal (`N₀`). A ⊥-row law reaches `.done` in
steps bounded by its term size; `400` is `LawTest`/`checkLaws`'s own budget (SSoT with the fuzzer —
the proof is about the SAME fixed-fuel proposition `bang test` samples). -/
def N₀ : Nat := 400

/-- The self-contained Lean goal artifact for one law. `theorem` carries the WHOLE emitted `.lean`
source (imports + header comment + the arm-B `theorem … := by sorry`); `address` is the elaborated
`Comp`'s content-address. -/
structure LeanGoalArtifact where
  /-- The law's name. -/
  lawName : String
  /-- The elaborated `Comp`'s content-address. -/
  address : String
  /-- The whole emitted `.lean` source (imports, header, the arm-B theorem). -/
  «theorem» : String
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg (unusedArguments false-positive).
attribute [nolint unusedArguments] instReprLeanGoalArtifact.repr

/-- One law instance to export — the `lawInstancesOf` projection PLUS the source program the law
lives in. `params`/`body` are source text; `prelude` is the trait/impl/data decls the body's ops
resolve against (NO trailing body). -/
structure LawInput where
  /-- The trait the law belongs to. -/
  trait   : String
  /-- The implementation the law is checked against. -/
  impl    : String
  /-- The law's name. -/
  lawName : String
  /-- The law's parameter names (source text). -/
  params  : List String
  /-- The law body (source text). -/
  body    : String
  /-- The trait/impl/data decls the body's ops resolve against (no trailing body). -/
  prelude : String
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg (unusedArguments false-positive).
attribute [nolint unusedArguments] instReprLawInput.repr

/-- Lambda-wrap a law body over its params, ending in `LawTest.wrapLawBody`'s readback idiom — the
form that elaborates to a CLOSED `Comp` function. -/
def lamWrap (params : List String) (body : String) : String :=
  let readback := s!"(let #lawR = ({body}) in (if #lawR then 1 else 0))"
  params.foldr (fun p acc => s!"fun {p} => {acc}") readback

/-- Apply an elaborated law-function `Comp` (as Lean-term text) to `k` fresh `Int` args `a0 … a(k-1)`
— the `bodyComp args` of arm B (`.app (.app c (.vint a0)) (.vint a1) …`). -/
def applyArgs (compSrc : String) (k : Nat) : String :=
  (List.range k).foldl (fun acc i => s!"(Bang.Comp.app {acc} (Bang.Val.vint a{i}))") compSrc

/-- Name a non-⊥ effect row from the FOUR public built-in label constants (`Bang.Surface.*Label`,
in Surface's `@[expose] public section`). Uses ONLY decidable membership (`ℓ ∈ φ`) — the exact
computable idiom `showRow` uses (`Finset.toList`/`.card` are noncomputable, so unavailable in the
`#guard`-compiled path). `showRow`/`effName` themselves are not public; this is a local renderer over
the same known labels. A declared user-effect label (`≥ 4`) has no public name here, so a purely
user-effect row renders empty — harmless, since the row is rejected on `¬(φ = ∅)`, not on the name. -/
def namedRow (φ : Bang.EffectRow.EffRow) : String :=
  String.intercalate ", " (
    (if Bang.Surface.exnLabel ∈ φ then ["throws"] else []) ++
    (if Bang.Surface.stateLabel ∈ φ then ["state"] else []) ++
    (if Bang.Surface.stmLabel ∈ φ then ["stm"] else []) ++
    (if Bang.Surface.divLabel ∈ φ then ["Div"] else []))

/-- Read totality STRUCTURALLY off the CONCRETE-ARGS-wrapped body via the public `checkProgRow`
(landed for exactly this gate — `origin/main` `checkProgRow`). `.ok ()` iff the law body's row is ⊥
(`decide (φ = ∅)` — `Finset`'s computable `DecidableEq`, NOT the noncomputable `.card`), else
`.error <row named>`. This REPLACES the earlier string-suffix fallback: the decision is now on the
raw `EffRow`, immune to `showType`/pretty-printer formatting. Concrete args are `0`s (the row is
arg-independent for a well-typed body). -/
def totalityCheck (inp : LawInput) : Except String Unit :=
  let zeros := inp.params.map (fun _ => "0")
  let concreteProg := inp.prelude ++ " " ++ LawTest.wrapLawBody inp.params zeros inp.body
  match Bang.TypeCheck.checkProgRow concreteProg with
  | .error m => .error s!"law '{inp.lawName}' does not type-check: {m}"
  | .ok φ =>
    if decide (φ = ∅) then .ok ()
    else .error s!"law '{inp.lawName}' is NOT total (row = \{{namedRow φ}}): proof-eligibility is typed — a non-⊥-row law stays on the fuzzed rung (total-only ruling)"

/-- **The goal emitter (R1's deliverable).** Elaborate the lambda-wrapped law body to its closed
kernel `Comp`, REJECT it if non-total (typed rejection, row named), else emit the arm-B goal artifact
(content-addressed, header-commented, `sorry`-bodied). `srcHash` is the caller's hash of the source
program (opaque here — the caller owns source provenance). -/
def exportGoal (srcHash : String) (inp : LawInput) : Except String LeanGoalArtifact := do
  totalityCheck inp
  let prog := inp.prelude ++ " " ++ lamWrap inp.params inp.body
  let bodyComp ← Bang.TypeCheck.elaborateToComp prog
  let addr := contentAddress bodyComp
  let k := inp.params.length
  let compSrc := showComp bodyComp
  let binders := String.intercalate " " ((List.range k).map (fun i => s!"a{i}"))
  let forallHead := if k == 0 then "" else s!"∀ ({binders} : Int), "
  let applied := applyArgs compSrc k
  let thmName := s!"{inp.lawName}_holds"
  let header :=
    s!"-- Q43 R1 exported law goal (arm B, total-only). DO NOT EDIT the statement — regenerated.\n" ++
    s!"-- law:     {inp.trait}.{inp.lawName}  (impl {inp.impl})\n" ++
    s!"-- source-hash:      {srcHash}\n" ++
    s!"-- content-address:  {addr}\n"
  let artifact :=
    header ++
    "import Bang.Core.Semantics\n" ++
    "open Bang\n\n" ++
    s!"theorem {thmName} : {forallHead}Bang.Source.eval {N₀} {applied} = .done (.vint 1) := by\n" ++
    "  sorry\n"
  return ⟨inp.lawName, addr, artifact⟩

/-! ## 4. #guard gates — each FALSIFIED (see the commit message / the falsification log). -/

/-- The `IntOrd.trans` corpus law (a real, true, TOTAL law over `Int`) — mirrors `LawTest`'s own
`intOrdPrelude`, reconstructed locally (those helpers are test-internal, not exported). -/
def intOrdPrelude : String :=
  "trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c } " ++
  "impl IntOrd for Int { fn lt(a, b) = a < b }"

/-- The `IntOrd.trans` corpus law as a `LawInput` fixture. -/
def transInput : LawInput :=
  ⟨"IntOrd", "Int", "trans", ["a", "b", "c"], "a < b => b < c => a < c", intOrdPrelude⟩

-- (a) a known corpus law exports an artifact (the total-only gate PASSES, a goal is emitted).
#guard (match exportGoal "src0000" transInput with | .ok _ => true | .error _ => false)

-- the emitted artifact carries the arm-B skeleton — the theorem name, ∀-binder, eval-goal, and the
-- `sorry`, plus the import — the structural lines a standalone `lake env lean` compile depends on.
-- (A full compile-in-CI of the written file is the R3 `just prove` leg; here we assert the key
-- lines, and the falsification log records the OUT-OF-BAND standalone compile of one artifact.)
#guard (match exportGoal "src0000" transInput with
        | .ok a =>
            (a.«theorem».splitOn "theorem trans_holds : ∀ (a0 a1 a2 : Int), Bang.Source.eval 400 ").length == 2
            && (a.«theorem».splitOn "= .done (.vint 1) := by").length == 2
            && (a.«theorem».splitOn "\n  sorry\n").length == 2
            && (a.«theorem».splitOn "import Bang.Core.Semantics").length == 2
        | .error _ => false)

-- (b) a Div-rowed law is REJECTED, with the row NAMED (`Div`) — proof-eligibility is typed.
/-- A `Div`-rowed (non-total) law body: a recursive `loop` — used to test rejection. -/
def loopyBody : String :=
  "let rec loop : Int -> Int = fun n => ($loop)(n + 1) in (let z = ($loop) a in a == a)"
/-- The trait prelude wrapping `loopyBody`. -/
def loopyPrelude : String := "trait T { fn f(a) -> Int law loopy(a): " ++ loopyBody ++ " }"
/-- The non-total `loopy` law as a `LawInput` fixture. -/
def loopyInput : LawInput := ⟨"T", "Int", "loopy", ["a"], loopyBody, loopyPrelude⟩

#guard (match exportGoal "src0000" loopyInput with
        | .error m => (m.splitOn "NOT total").length == 2 && (m.splitOn "Div").length == 2
        | .ok _ => false)

-- (c) two α-renamed variants of the SAME law produce IDENTICAL content-addresses (de-Bruijn:
-- renaming params can't move the elaborated term, so the address is rename-invariant).
/-- An α-renamed variant of `transInput` — used to test content-address rename-invariance. -/
def transRenamed : LawInput :=
  ⟨"IntOrd", "Int", "trans", ["x", "y", "z"], "x < y => y < z => x < z", intOrdPrelude⟩

#guard (match exportGoal "src0000" transInput, exportGoal "src9999" transRenamed with
        | .ok a, .ok b => a.address == b.address
        | _, _ => false)

-- (d) two DIFFERENT laws produce DIFFERENT content-addresses (comm over Int ≠ trans).
/-- The `IntAdd.comm` corpus law as a `LawInput` fixture — a different law than `trans`. -/
def commInput : LawInput :=
  ⟨"IntAdd", "Int", "comm", ["a", "b"],
   "let s = a + b in (let t = b + a in s == t)",
   "trait IntAdd { fn add(a, b) -> Int law comm(a, b): let s = a + b in (let t = b + a in s == t) } impl IntAdd for Int { fn add(a, b) = a + b }"⟩

#guard (match exportGoal "src0000" transInput, exportGoal "src0000" commInput with
        | .ok a, .ok b => a.address != b.address
        | _, _ => false)

-- content-address is a fixed 16-hex-digit string (the stable cache-key shape).
#guard (match exportGoal "src0000" transInput with
        | .ok a => a.address.length == 16 && a.address.toList.all (fun c => "0123456789abcdef".toList.contains c)
        | .error _ => false)
