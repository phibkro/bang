/-
  Bang/Frontend/NamedCore.lean — the canonical core, made writable (ADR-0046 ①).
  ────────────────────────────────────────────────────────────────────────────
  ADR-0046 decided a THREE-seam pipeline:

      sugar surface  →  named-explicit core (S-expr)  →  de-Bruijn kernel term
        (concise)         THIS MODULE                      Bang/Core.lean

  Until now the code collapsed the last two seams into one fold (`Surface.lowerC`
  did desugaring AND name→de-Bruijn at once), and the middle layer — the canonical
  core the ADR calls "a first-class WRITABLE surface" — had no type and no printer,
  so the faithfulness gate it mandates (`read ∘ print = id`) could not exist.

  This module reifies that middle layer:

    §1  `NVal`/`NComp`/`NHandler` — 1:1 with `Bang/Core.lean`'s `Val`/`Comp`/`Handler`,
        but with NAMED binders + variables. Caps/labels/ops stay EXPLICIT (the "true
        shape"); only variables differ (named here, de-Bruijn in the kernel).
    §2  `elab` — the THIN seam: `name → de-Bruijn`. The only inference at this layer.
    §3  `print` — NamedCore → canonical S-expression text. The inspectability ADR-0046
        promises ("show me the elaboration").
    §4  `read`  — S-expression text → NamedCore. A small fuel-total recursive descent.
    §5  the FAITHFULNESS GATE — `read ∘ print = id` (#guard, structural) + end-to-end
        `elab`→`Source.eval` demos (by rfl, the ADR-0046 round-trip programs RUN).

  ARCHITECTURE (the V, not a line). This file lives in `Bang.Frontend` and imports
  `Bang.Operational` (Core). Frontend DEPENDS ON Core; Core depends on NOTHING outward.
  Data FLOWS Frontend → Core → Backend (text → IR → WASM); DEPENDENCIES point inward at
  Core. A linter/LSP/formatter consuming `NComp` therefore depends on Core alone — which
  is why this writable IR is the natural plugin surface (ADR-0047).

  Scope (v1): the term level (Val/Comp/Handler) in full. The TYPED precision form
  (`(let (x : A) C C)` + grade/row annotations, ADR-0046 grammar) is the next increment;
  the untyped run-form here is exactly what the kernel evaluates today. Op names and the
  `wrong` payload print as bare tokens (no embedded whitespace) — an identifier-like
  assumption the rung programs satisfy; the typed form will carry a quoted-string reader.
-/

module

-- `#guard roundtrips …` runs `Source.eval` (compiled Operational) at the META phase → meta import.
meta import Bang.Operational
public import Bang.Operational

namespace Bang.Frontend

open Bang
open Bang.EffectRow (Label)

/-! ## 1. The named-explicit core — 1:1 with `Bang/Core.lean`, named binders -/

mutual
/-- A value of the canonical core. Mirrors `Bang.Val`; `var` is a NAME, not a de-Bruijn
index — that is the single difference the `elab` seam (§2) erases. -/
inductive NVal where
  | unit  : NVal
  | int   : Int → NVal
  | var   : String → NVal                 -- NAMED variable (kernel: de-Bruijn `vvar`)
  | thunk : NComp → NVal
  | inl   : NVal → NVal
  | inr   : NVal → NVal
  | pair  : NVal → NVal → NVal
  | fold  : NVal → NVal
/-- A computation of the canonical core. Mirrors `Bang.Comp`. Binders carry NAMES
(`lett`/`lam`/`handle`/`case`-arms bind one; `split` binds two — fst then snd). The `perform`
capability is now a named VALUE (ADR-0054: `Comp.perform : Val → OpId → Val` — the cap is a value,
the label is recovered from its type, not stored in the term). `handle` BINDS a capability name (the
kernel's `handle h M` binds a cap at de-Bruijn 0; the named mirror binds `x`). -/
inductive NComp where
  | ret     : NVal → NComp
  | lett    : String → NComp → NComp → NComp       -- (let x  C C)  — name binds in the 2nd
  | force   : NVal → NComp
  | lam     : String → NComp → NComp               -- (lam x  C)
  | app     : NComp → NVal → NComp
  | perform : NVal → OpId → NVal → NComp            -- (perform cap op V) — cap is a named VALUE
  | handle  : String → NHandler → NComp → NComp     -- (handle x H C) — binds the capability name x in C
  | case    : NVal → String → NComp → String → NComp → NComp   -- (case V (x C) (y C))
  | split   : String → String → NVal → NComp → NComp           -- (split (xfst ysnd) V C)
  | unfold  : NVal → NComp
  | oom     : NComp
  | wrong   : String → NComp
/-- A handler of the canonical core. Mirrors `Bang.Handler`. Handlers do not bind. -/
inductive NHandler where
  | state       : Label → NVal → NHandler
  | throws      : Label → NHandler
  | transaction : Label → List NVal → NHandler
end

deriving instance Repr for NVal, NComp, NHandler


/-! ## 2. `elab` — the thin seam: name → de-Bruijn

The ONLY inference at this layer (ADR-0046: "the bottom inference is `name → de-Bruijn`").
`env` is the in-scope names innermost-first, so a name's index is its position
(`List.idxOf?`) — identical to `Surface.lowerC`'s resolution, now isolated as its own
seam. A free name is a loud error (`Except String`), not a silent default. -/

mutual
def NVal.elab (env : List String) : NVal → Except String Val
  | .unit     => .ok .vunit
  | .int n    => .ok (.vint n)
  | .var x    => match env.idxOf? x with
                 | some i => .ok (.vvar i)
                 | none   => .error s!"unbound variable: {x}"
  | .thunk c  => do return .vthunk (← NComp.elab env c)
  | .inl v    => do return .inl (← NVal.elab env v)
  | .inr v    => do return .inr (← NVal.elab env v)
  | .pair a b => do return .pair (← NVal.elab env a) (← NVal.elab env b)
  | .fold v   => do return .fold (← NVal.elab env v)
def NComp.elab (env : List String) : NComp → Except String Comp
  | .ret v          => do return .ret (← NVal.elab env v)
  | .lett x m n     => do return .letC (← NComp.elab env m) (← NComp.elab (x :: env) n)
  | .force v        => do return .force (← NVal.elab env v)
  | .lam x m        => do return .lam (← NComp.elab (x :: env) m)
  | .app m v        => do return .app (← NComp.elab env m) (← NVal.elab env v)
  | .perform cv op v => do return .perform (← NVal.elab env cv) op (← NVal.elab env v)
  -- `handle x H C` binds the capability name `x` at index 0 in `C` (mirrors the kernel's
  -- `handle h M` binding a cap at de-Bruijn 0): push `x` before elaborating the body.
  | .handle x h c   => do return .handle (← NHandler.elab env h) (← NComp.elab (x :: env) c)
  | .case v x m y n => do
      return .case (← NVal.elab env v) (← NComp.elab (x :: env) m) (← NComp.elab (y :: env) n)
  -- `split` binds fst at de-Bruijn index 1, snd at index 0 (Core.lean §1.2), so the env
  -- gains snd (innermost, idx 0) then fst (idx 1): `ysnd :: xfst :: env`.
  | .split xfst ysnd v n => do
      return .split (← NVal.elab env v) (← NComp.elab (ysnd :: xfst :: env) n)
  | .unfold v       => do return .unfold (← NVal.elab env v)
  | .oom            => .ok .oom
  | .wrong s        => .ok (.wrong s)
def NHandler.elab (env : List String) : NHandler → Except String Handler
  | .throws ℓ         => .ok (.throws ℓ)
  | .state ℓ v        => do return .state ℓ (← NVal.elab env v)
  | .transaction ℓ vs => do return .transaction ℓ (← NVal.elabList env vs)
/-- Elaborate a heap of TVar initial values (the `transaction` store). Spelled as explicit
recursion (not `List.mapM`) so the mutual block is structurally terminating. -/
def NVal.elabList (env : List String) : List NVal → Except String (List Val)
  | []      => .ok []
  | v :: vs => do return (← NVal.elab env v) :: (← NVal.elabList env vs)
end

/-- Elaborate a closed program (empty name environment). -/
def NComp.elabClosed (c : NComp) : Except String Comp := NComp.elab [] c


/-! ## 3. `print` — NamedCore → canonical S-expression text

One head form per constructor (ADR-0046 amendment grammar): unambiguous, no precedence.
The printer is total and trivial; it is the inspectability half of the faithfulness gate. -/

mutual
def NVal.print : NVal → String
  | .unit     => "unit"
  | .int n    => toString n
  | .var x    => x
  | .thunk c  => "(thunk " ++ NComp.print c ++ ")"
  | .inl v    => "(inl " ++ NVal.print v ++ ")"
  | .inr v    => "(inr " ++ NVal.print v ++ ")"
  | .pair a b => "(pair " ++ NVal.print a ++ " " ++ NVal.print b ++ ")"
  | .fold v   => "(fold " ++ NVal.print v ++ ")"
def NComp.print : NComp → String
  | .ret v          => "(ret " ++ NVal.print v ++ ")"
  | .lett x m n     => "(let " ++ x ++ " " ++ NComp.print m ++ " " ++ NComp.print n ++ ")"
  | .force v        => "(force " ++ NVal.print v ++ ")"
  | .lam x m        => "(lam " ++ x ++ " " ++ NComp.print m ++ ")"
  | .app m v        => "(app " ++ NComp.print m ++ " " ++ NVal.print v ++ ")"
  | .perform cv op v =>
      "(perform " ++ NVal.print cv ++ " " ++ op ++ " " ++ NVal.print v ++ ")"
  | .handle x h c   => "(handle " ++ x ++ " " ++ NHandler.print h ++ " " ++ NComp.print c ++ ")"
  | .case v x m y n =>
      "(case " ++ NVal.print v ++ " (" ++ x ++ " " ++ NComp.print m ++ ") ("
        ++ y ++ " " ++ NComp.print n ++ "))"
  | .split xfst ysnd v n =>
      "(split (" ++ xfst ++ " " ++ ysnd ++ ") " ++ NVal.print v ++ " " ++ NComp.print n ++ ")"
  | .unfold v       => "(unfold " ++ NVal.print v ++ ")"
  | .oom            => "oom"
  | .wrong s        => "(wrong " ++ s ++ ")"
def NHandler.print : NHandler → String
  | .state ℓ v        => "(state " ++ toString ℓ ++ " " ++ NVal.print v ++ ")"
  | .throws ℓ         => "(throws " ++ toString ℓ ++ ")"
  | .transaction ℓ vs => "(transaction " ++ toString ℓ ++ " [" ++ NVal.printList vs ++ "])"
def NVal.printList : List NVal → String
  | []      => ""
  | [v]     => NVal.print v
  | v :: vs => NVal.print v ++ " " ++ NVal.printList vs
end


/-! ## 4. `read` — S-expression text → NamedCore

Tokenize (parens/brackets are their own tokens), then a fuel-total recursive descent.
`parseV`/`parseC`/`parseH` each consume a balanced prefix and return the rest; a malformed
program is a loud `Except String` error, never a silent partial parse. -/

/-- Split into tokens: `(` `)` `[` `]` are self-delimiting; everything else is a maximal
run of non-whitespace. A char fold (the toolchain's `String.split` yields a slice iterator,
not a `List`), accumulating the current token and flushing on a punctuator or whitespace. -/
def tokenize (s : String) : List String :=
  let step : (String × List String) → Char → (String × List String) := fun (cur, acc) c =>
    let flushed := if cur.isEmpty then acc else cur :: acc
    if c == '(' || c == ')' || c == '[' || c == ']' then ("", c.toString :: flushed)
    else if c.isWhitespace then ("", flushed)
    else (cur.push c, acc)
  let (cur, acc) := s.foldl step ("", [])
  (if cur.isEmpty then acc else cur :: acc).reverse

/-- Consume an exact token or fail. -/
def expectTok (t : String) : List String → Except String (List String)
  | x :: rest => if x == t then .ok rest else .error s!"parse: expected '{t}', got '{x}'"
  | []        => .error s!"parse: expected '{t}', got end of input"

/-- Consume any one token (a name / number / op id) or fail. -/
def takeTok : List String → Except String (String × List String)
  | x :: rest => .ok (x, rest)
  | []        => .error "parse: expected a token, got end of input"

mutual
def parseV (fuel : Nat) (ts : List String) : Except String (NVal × List String) :=
  match fuel with
  | 0 => .error "parse: out of fuel"
  | fuel + 1 =>
    match ts with
    | "(" :: "thunk" :: r => do
        let (c, r) ← parseC fuel r; let r ← expectTok ")" r; return (.thunk c, r)
    | "(" :: "inl" :: r => do
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.inl v, r)
    | "(" :: "inr" :: r => do
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.inr v, r)
    | "(" :: "fold" :: r => do
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.fold v, r)
    | "(" :: "pair" :: r => do
        let (a, r) ← parseV fuel r; let (b, r) ← parseV fuel r
        let r ← expectTok ")" r; return (.pair a b, r)
    | "(" :: tok :: _ => .error s!"parse: '{tok}' is not a value head"
    | "(" :: [] => .error "parse: '(' then end of input"
    | tok :: rest =>
        if tok == "unit" then .ok (.unit, rest)
        else match tok.toInt? with
          | some n => .ok (.int n, rest)
          | none   => .ok (.var tok, rest)
    | [] => .error "parse: expected a value, got end of input"
termination_by fuel
def parseC (fuel : Nat) (ts : List String) : Except String (NComp × List String) :=
  match fuel with
  | 0 => .error "parse: out of fuel"
  | fuel + 1 =>
    match ts with
    | "oom" :: rest => .ok (.oom, rest)
    | "(" :: "ret" :: r => do
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.ret v, r)
    | "(" :: "force" :: r => do
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.force v, r)
    | "(" :: "unfold" :: r => do
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.unfold v, r)
    | "(" :: "let" :: r => do
        let (x, r) ← takeTok r; let (m, r) ← parseC fuel r; let (n, r) ← parseC fuel r
        let r ← expectTok ")" r; return (.lett x m n, r)
    | "(" :: "lam" :: r => do
        let (x, r) ← takeTok r; let (m, r) ← parseC fuel r
        let r ← expectTok ")" r; return (.lam x m, r)
    | "(" :: "app" :: r => do
        let (m, r) ← parseC fuel r; let (v, r) ← parseV fuel r
        let r ← expectTok ")" r; return (.app m v, r)
    | "(" :: "perform" :: r => do
        let (cv, r) ← parseV fuel r; let (op, r) ← takeTok r
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.perform cv op v, r)
    | "(" :: "handle" :: r => do
        let (x, r) ← takeTok r; let (h, r) ← parseH fuel r; let (c, r) ← parseC fuel r
        let r ← expectTok ")" r; return (.handle x h c, r)
    | "(" :: "wrong" :: r => do
        let (s, r) ← takeTok r; let r ← expectTok ")" r; return (.wrong s, r)
    | "(" :: "case" :: r => do
        let (v, r) ← parseV fuel r
        let r ← expectTok "(" r; let (x, r) ← takeTok r; let (m, r) ← parseC fuel r
        let r ← expectTok ")" r
        let r ← expectTok "(" r; let (y, r) ← takeTok r; let (n, r) ← parseC fuel r
        let r ← expectTok ")" r
        let r ← expectTok ")" r; return (.case v x m y n, r)
    | "(" :: "split" :: r => do
        let r ← expectTok "(" r; let (xf, r) ← takeTok r; let (ys, r) ← takeTok r
        let r ← expectTok ")" r
        let (v, r) ← parseV fuel r; let (n, r) ← parseC fuel r
        let r ← expectTok ")" r; return (.split xf ys v n, r)
    | "(" :: tok :: _ => .error s!"parse: '{tok}' is not a computation head"
    | tok :: _ => .error s!"parse: expected a computation, got '{tok}'"
    | [] => .error "parse: expected a computation, got end of input"
termination_by fuel
def parseH (fuel : Nat) (ts : List String) : Except String (NHandler × List String) :=
  match fuel with
  | 0 => .error "parse: out of fuel"
  | fuel + 1 =>
    match ts with
    | "(" :: "throws" :: r => do
        let (ls, r) ← takeTok r
        let some l := ls.toNat? | throw s!"parse: bad label '{ls}'"
        let r ← expectTok ")" r; return (.throws l, r)
    | "(" :: "state" :: r => do
        let (ls, r) ← takeTok r
        let some l := ls.toNat? | throw s!"parse: bad label '{ls}'"
        let (v, r) ← parseV fuel r; let r ← expectTok ")" r; return (.state l v, r)
    | "(" :: "transaction" :: r => do
        let (ls, r) ← takeTok r
        let some l := ls.toNat? | throw s!"parse: bad label '{ls}'"
        let r ← expectTok "[" r; let (vs, r) ← parseVList fuel r; let r ← expectTok "]" r
        let r ← expectTok ")" r; return (.transaction l vs, r)
    | tok :: _ => .error s!"parse: '{tok}' is not a handler"
    | [] => .error "parse: expected a handler, got end of input"
termination_by fuel
/-- Parse zero or more values up to (but not consuming) the closing `]`. -/
def parseVList (fuel : Nat) (ts : List String) : Except String (List NVal × List String) :=
  match fuel with
  | 0 => .error "parse: out of fuel"
  | fuel + 1 =>
    match ts with
    | "]" :: _ => .ok ([], ts)
    | [] => .error "parse: unterminated value list"
    | _ => do
        let (v, r) ← parseV fuel ts
        let (vs, r) ← parseVList fuel r
        return (v :: vs, r)
termination_by fuel
end

/-- Read a closed canonical-core program from S-expression text. Fails loud on a parse
error or trailing tokens. -/
def readC (s : String) : Except String NComp := do
  let ts := tokenize s
  let (c, rest) ← parseC (ts.length + 1) ts
  if rest.isEmpty then .ok c
  else .error s!"parse: trailing tokens {rest}"


/-! ## 5. The faithfulness gate — `read ∘ print = id` + end-to-end RUN

The structural gate: printing a NamedCore term then reading it back recovers it exactly
(names are preserved, so equality is on the nose — no α needed). Drift between the two
representations is now a build failure, not convention. -/

/-- `true` iff `c` survives the print→read round-trip unchanged. `print` has one head form
per constructor, so it is INJECTIVE; comparing re-printed text therefore certifies
`read (print c) = c` while needing only `BEq String` (mutual `DecidableEq` isn't derivable). -/
def roundtrips (c : NComp) : Bool :=
  let s := NComp.print c
  match readC s with
  | .ok c'    => NComp.print c' == s
  | .error _  => false

-- The ADR-0046 round-trip programs, as canonical-core terms (labels: exn=0, state=1, stm=2).
-- ADR-0054: each `handle` BINDS a capability NAME; the operations inside `perform` on that name.

/-- `state-get`: `(handle c (state 1 5) (perform c get unit))` ⟶ 5. -/
def stateGet : NComp :=
  .handle "c" (.state 1 (.int 5)) (.perform (.var "c") "get" .unit)

/-- `reactive cell`: an unmemoized thunk over a state cell; each force re-samples. ⟶ 5. -/
def reactiveCell : NComp :=
  .handle "k" (.state 1 (.int 0))
    (.lett "c" (.ret (.thunk (.perform (.var "k") "get" .unit)))
      (.lett "_" (.perform (.var "k") "put" (.int 5))
        (.force (.var "c"))))

/-- `STM abort`: the abort `raise` names the OUTER `throws` capability `exn` — it reaches PAST the
transaction (the inner `tx` cap), dropping the heap with it. ⟶ (100, 0). -/
def stmAbort : NComp :=
  .handle "exn" (.throws 0)
    (.handle "tx" (.transaction 2 [])
      (.lett "_" (.perform (.var "tx") "newTVar" (.int 100))
        (.lett "_" (.perform (.var "tx") "writeTVar" (.pair (.int 0) (.int 70)))
          (.perform (.var "exn") "raise" (.pair (.int 100) (.int 0))))))

-- (a) STRUCTURAL gate: read ∘ print = id on each program.
#guard roundtrips stateGet
#guard roundtrips reactiveCell
#guard roundtrips stmAbort

-- (b) END-TO-END: the writable core ELABORATES + RUNS to the ADR-0046 values.
-- `by rfl` forces `elab` (through `getD`) AND `Source.eval` by kernel reduction, so a wrong
-- elaboration OR a wrong value fails the build loudly (verify, don't claim).
private def run (c : NComp) : Result Val :=
  Source.eval 100 ((NComp.elabClosed c).toOption.getD (.wrong "elab-failed"))

example : run stateGet = .done (.vint 5) := by rfl
example : run reactiveCell = .done (.vint 5) := by rfl
example : run stmAbort = .done (.pair (.vint 100) (.vint 0)) := by rfl

end Bang.Frontend
