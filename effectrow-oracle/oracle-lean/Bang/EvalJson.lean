import Bang.Eval
import Bang.Calc
import Lean.Data.Json

/-!
# JSON codec for the `eval` oracle

Wire format for driving `Bang.Eval.eval` over the same newline-delimited JSON
protocol the unifier oracle uses. This is *harness glue*, not the reference: the
parsers are `partial def` (recursion is over JSON lookups, not a structural
subterm), whereas `eval` itself is total. A malformed program fails loudly with
an `Except String` error rather than producing a bogus value.

Expr  E := {"t":"lit","v":Int} | {"t":"unit"} | {"t":"var","x":Str}
         | {"t":"lam","x":Str,"body":E} | {"t":"app","f":E,"a":E}
         | {"t":"thunk","e":E} | {"t":"force","e":E}
         | {"t":"let","x":Str,"e1":E,"e2":E}
         | {"t":"con","c":Str,"args":[E..]}
         | {"t":"match","scrut":E,"arms":[{"pat":P,"rhs":E}..]}
         | {"t":"if","c":E,"then":E,"else":E}
         | {"t":"binop","op":Str,"a":E,"b":E}
         | {"t":"perform","label":Nat,"op":Str,"arg":E}
         | {"t":"handle","h":H,"body":E}
Pat   P := {"p":"wild"} | {"p":"var","x":Str} | {"p":"lit","v":Int}
         | {"p":"con","c":Str,"args":[P..]}
Hsp   H := {"h":"state","label":Nat,"init":E} | {"h":"throws","label":Nat}

Result := {"ok":true,"value":V}
        | {"ok":false,"reason":"outOfFuel"}
        | {"ok":false,"reason":"uncaught","label":Nat,"effOp":Str}
        | {"ok":false,"reason":"stuck","msg":Str}
Value V := {"v":"int","n":Int} | {"v":"unit"} | {"v":"con","c":Str,"args":[V..]}
         | {"v":"clos"} | {"v":"thunk"}
-/

open Lean (Json)
open Bang.Eval

namespace Bang.EvalJson

/-! ## Decoding -/

/-- Read a JSON number as an `Int` (the harness sends integer literals). -/
def jInt : Json → Except String Int
  | .num n => pure n.mantissa
  | _      => throw "expected an integer"

def jField (j : Json) (key : String) : Except String Json := j.getObjVal? key
def jStr (j : Json) (key : String) : Except String String := do (← j.getObjVal? key).getStr?
def jIntF (j : Json) (key : String) : Except String Int := do jInt (← j.getObjVal? key)
def jNat (j : Json) (key : String) : Except String Nat := do pure (← jIntF j key).toNat
def jArr (j : Json) (key : String) : Except String (Array Json) := do (← j.getObjVal? key).getArr?

mutual

partial def patFromJson (j : Json) : Except String Pat := do
  match ← jStr j "p" with
  | "wild" => pure .pwild
  | "var"  => pure (.pvar (← jStr j "x"))
  | "lit"  => pure (.plit (← jIntF j "v"))
  | "con"  => do
      let args ← (← jArr j "args").toList.mapM patFromJson
      pure (.pcon (← jStr j "c") args)
  | other  => throw s!"unknown pattern tag {other}"

partial def hspecFromJson (j : Json) : Except String HandlerSpec := do
  match ← jStr j "h" with
  | "state"  => pure (.stateH (← jNat j "label") (← exprFromJson (← jField j "init")))
  | "throws" => pure (.throwsH (← jNat j "label"))
  | other    => throw s!"unknown handler tag {other}"

partial def exprFromJson (j : Json) : Except String Expr := do
  match ← jStr j "t" with
  | "lit"   => pure (.lit (← jIntF j "v"))
  | "unit"  => pure .unit
  | "var"   => pure (.var (← jStr j "x"))
  | "lam"   => pure (.lam (← jStr j "x") (← exprFromJson (← jField j "body")))
  | "app"   => pure (.app (← exprFromJson (← jField j "f")) (← exprFromJson (← jField j "a")))
  | "thunk" => pure (.thnk (← exprFromJson (← jField j "e")))
  | "force" => pure (.force (← exprFromJson (← jField j "e")))
  | "let"   => pure (.letE (← jStr j "x")
                           (← exprFromJson (← jField j "e1"))
                           (← exprFromJson (← jField j "e2")))
  | "con"   => do
      let args ← (← jArr j "args").toList.mapM exprFromJson
      pure (.con (← jStr j "c") args)
  | "match" => do
      let arms ← (← jArr j "arms").toList.mapM fun a => do
        pure (← patFromJson (← jField a "pat"), ← exprFromJson (← jField a "rhs"))
      pure (.matchE (← exprFromJson (← jField j "scrut")) arms)
  | "if"    => pure (.ifE (← exprFromJson (← jField j "c"))
                          (← exprFromJson (← jField j "then"))
                          (← exprFromJson (← jField j "else")))
  | "binop" => pure (.binop (← jStr j "op")
                            (← exprFromJson (← jField j "a"))
                            (← exprFromJson (← jField j "b")))
  | "perform" => pure (.perform (← jNat j "label") (← jStr j "op")
                                (← exprFromJson (← jField j "arg")))
  | "handle" => pure (.handle (← hspecFromJson (← jField j "h"))
                              (← exprFromJson (← jField j "body")))
  | other   => throw s!"unknown expr tag {other}"

end

/-! ## Encoding -/

partial def valueToJson : Value → Json
  | .vunit       => Json.mkObj [("v", Json.str "unit")]
  | .vint n      => Json.mkObj [("v", Json.str "int"), ("n", Lean.toJson n)]
  | .vclos _ _ _ => Json.mkObj [("v", Json.str "clos")]
  | .vthunk _ _  => Json.mkObj [("v", Json.str "thunk")]
  | .vcon c args => Json.mkObj [("v", Json.str "con"), ("c", Json.str c),
                                ("args", Json.arr ((args.map valueToJson).toArray))]

def runResultToJson : RunResult → Json
  | .value v        => Json.mkObj [("ok", Json.bool true), ("value", valueToJson v)]
  | .outOfFuel      => Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")]
  | .stuck msg      => Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                                   ("msg", Json.str msg)]
  | .uncaught ℓ o   => Json.mkObj [("ok", Json.bool false), ("reason", Json.str "uncaught"),
                                   ("label", Lean.toJson ℓ), ("effOp", Json.str o)]

/-- Parse and run an `{"op":"eval","fuel":N,"expr":E}` request. -/
def evalRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let e    ← exprFromJson (← jField j "expr")
  pure (runResultToJson (run fuel e))

/-! ## The calculated machine (`exec`) over the arithmetic kernel (ADR-0009)

Translate the arithmetic subset of `Expr` into `Bang.Calc.Src`, run the
*calculated* stack machine, and return the result in the same value shape `eval`
uses — so the harness can diff-test the machine against the `eval` oracle. By
`Bang.Calc.compile_correct` the machine always halts on a singleton stack. -/

-- Translate the supported `Expr` subset into the de Bruijn `Calc.Src`. `ctx` is
-- the binding context (names, innermost first); a `var` resolves to its index, a
-- `let` extends the context. Unbound names / unsupported nodes fail loudly.
partial def srcFromExpr (ctx : List String) : Expr → Except String Bang.Calc.Src
  | .lit n          => pure (.val n)
  | .binop "+" a b  => do pure (.add (← srcFromExpr ctx a) (← srcFromExpr ctx b))
  | .binop "*" a b  => do pure (.mul (← srcFromExpr ctx a) (← srcFromExpr ctx b))
  | .var x          => match ctx.findIdx? (· = x) with
                       | some i => pure (.var i)
                       | none   => throw s!"exec: unbound variable {x}"
  | .letE x e1 e2   => do pure (.letE (← srcFromExpr ctx e1) (← srcFromExpr (x :: ctx) e2))
  | _               => throw "exec: only lit, +, *, var, let are compiled so far"

/-- Parse and run an `{"op":"exec","expr":E}` request on the calculated machine. -/
def execRequest (j : Json) : Except String Json := do
  let e   ← exprFromJson (← jField j "expr")
  let src ← srcFromExpr [] e
  match Bang.Calc.exec (Bang.Calc.compile src []) [] [] with
  | [n] => pure (Json.mkObj [("ok", Json.bool true),
                             ("value", Json.mkObj [("v", Json.str "int"), ("n", Lean.toJson n)])])
  | _   => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                             ("msg", Json.str "exec: machine halted on a non-singleton stack")])

end Bang.EvalJson
