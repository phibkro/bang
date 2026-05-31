import Bang.Eval
import Bang.Calc
import Bang.CalcHO
import Bang.CalcCBN
import Bang.CalcEff
import Bang.CalcSt
import Bang.CalcCBNEff
import Bang.CalcCBNSt
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

/-! ## The higher-order calculated machine (`execho`) — closures (ADR-0010)

Same idea as `exec`, but over `Bang.CalcHO` (arithmetic + let/var + λ/app, CBV,
fuel-bounded). Translates the `Expr` subset to the de Bruijn `CalcHO.Src` and runs
the calculated closure machine. Diff-tested vs the `eval` oracle on the pure total
fragment (CBV ≡ CBN there). -/

partial def srcHOFromExpr (ctx : List String) : Expr → Except String Bang.CalcHO.Src
  | .lit n          => pure (.val n)
  | .binop "+" a b  => do pure (.add (← srcHOFromExpr ctx a) (← srcHOFromExpr ctx b))
  | .binop "*" a b  => do pure (.mul (← srcHOFromExpr ctx a) (← srcHOFromExpr ctx b))
  | .var x          => match ctx.findIdx? (· = x) with
                       | some i => pure (.var i)
                       | none   => throw s!"execho: unbound variable {x}"
  | .letE x e1 e2   => do pure (.letE (← srcHOFromExpr ctx e1) (← srcHOFromExpr (x :: ctx) e2))
  | .lam x body     => do pure (.lam (← srcHOFromExpr (x :: ctx) body))
  | .app f a        => do pure (.app (← srcHOFromExpr ctx f) (← srcHOFromExpr ctx a))
  | _               => throw "execho: only lit, +, *, var, let, lam, app are compiled so far"

def valueHOToJson : Bang.CalcHO.Value → Json
  | .vint n   => Json.mkObj [("v", Json.str "int"), ("n", Lean.toJson n)]
  | .vclo _ _ => Json.mkObj [("v", Json.str "clos")]

/-- Parse and run an `{"op":"execho","fuel":N,"expr":E}` request on the HO machine. -/
def execHORequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let e    ← exprFromJson (← jField j "expr")
  let src  ← srcHOFromExpr [] e
  match Bang.CalcHO.exec fuel (Bang.CalcHO.compile src []) [] [] with
  | some (rv :: _) => pure (Json.mkObj [("ok", Json.bool true), ("value", valueHOToJson rv)])
  | some []        => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                                        ("msg", Json.str "execho: empty result stack")])
  | none           => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuckOrOom"),
                                        ("msg", Json.str "execho: none (out-of-fuel or stuck)")])

/-! ## The call-by-name calculated machine (`execcbn`) — thunk/force (ADR-0010+)

`Bang.CalcCBN` is the CBN machine; it should match the operational `Bang.Eval`
(also CBN) exactly. Adds `thnk`/`force` to the translation. The top result is
forced to WHNF (`forceV`) so it matches `Bang.Eval`'s forced output. -/

partial def srcCBNFromExpr (ctx : List String) : Expr → Except String Bang.CalcCBN.Src
  | .lit n          => pure (.val n)
  | .binop "+" a b  => do pure (.add (← srcCBNFromExpr ctx a) (← srcCBNFromExpr ctx b))
  | .binop "*" a b  => do pure (.mul (← srcCBNFromExpr ctx a) (← srcCBNFromExpr ctx b))
  | .var x          => match ctx.findIdx? (· = x) with
                       | some i => pure (.var i)
                       | none   => throw s!"execcbn: unbound variable {x}"
  | .lam x body     => do pure (.lam (← srcCBNFromExpr (x :: ctx) body))
  | .app f a        => do pure (.app (← srcCBNFromExpr ctx f) (← srcCBNFromExpr ctx a))
  | .letE x e1 e2   => do pure (.letE (← srcCBNFromExpr ctx e1) (← srcCBNFromExpr (x :: ctx) e2))
  | .thnk e         => do pure (.thnk (← srcCBNFromExpr ctx e))
  | .force e        => do pure (.force (← srcCBNFromExpr ctx e))
  | _               => throw "execcbn: only lit, +, *, var, lam, app, let, thunk, force are compiled so far"

def valueCBNToJson : Bang.CalcCBN.Value → Json
  | .vint n     => Json.mkObj [("v", Json.str "int"), ("n", Lean.toJson n)]
  | .vclo _ _   => Json.mkObj [("v", Json.str "clos")]
  | .vthunk _ _ => Json.mkObj [("v", Json.str "thunk")]

/-- Parse and run an `{"op":"execcbn","fuel":N,"expr":E}` request on the CBN machine. -/
def execCBNRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let e    ← exprFromJson (← jField j "expr")
  let src  ← srcCBNFromExpr [] e
  match Bang.CalcCBN.exec fuel (Bang.CalcCBN.compile src []) [] [] with
  | some (rv :: _) =>
      match Bang.CalcCBN.forceV fuel rv with     -- force the top result, like Bang.Eval's run
      | some w => pure (Json.mkObj [("ok", Json.bool true), ("value", valueCBNToJson w)])
      | none   => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuckOrOom"),
                                    ("msg", Json.str "execcbn: forcing the result returned none")])
  | _ => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuckOrOom"),
                           ("msg", Json.str "execcbn: none (out-of-fuel or stuck)")])

/-! ## The effect machine (`evaleff`/`execeff`) — general handlers, Throws (K3)

Its own de Bruijn wire format (`Bang.CalcEff.Src`). Both the reference `eval`
(`evaleff`) and the calculated handler machine (`execeff`) return an `Outcome` in
the same JSON shape, so the harness diff-tests them directly. -/

partial def srcEffFromJson (j : Json) : Except String Bang.CalcEff.Src := do
  match ← jStr j "t" with
  | "val"     => pure (.val (← jIntF j "n"))
  | "var"     => pure (.var (← jNat j "i"))
  | "add"     => pure (.add (← srcEffFromJson (← jField j "a")) (← srcEffFromJson (← jField j "b")))
  | "let"     => pure (.letE (← srcEffFromJson (← jField j "e1")) (← srcEffFromJson (← jField j "e2")))
  | "perform" => pure (.perform (← jNat j "l") (← srcEffFromJson (← jField j "arg")))
  | "handle"  => pure (.handle (← jNat j "l") (← srcEffFromJson (← jField j "onRaise"))
                               (← srcEffFromJson (← jField j "body")))
  | other     => throw s!"eff: unknown tag {other}"

def outcomeToJson : Bang.CalcEff.Outcome → Json
  | .ret n   => Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "ret"), ("n", Lean.toJson n)]
  | .exc l p => Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "exc"),
                            ("label", Lean.toJson l), ("payload", Lean.toJson p)]

def resultToJson : Bang.CalcEff.Result → Json
  | .halt (n :: _)  => Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "ret"), ("n", Lean.toJson n)]
  | .halt []        => Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                                   ("msg", Json.str "execeff: empty halt stack")]
  | .uncaught l p   => Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "exc"),
                                   ("label", Lean.toJson l), ("payload", Lean.toJson p)]

/-- `{"op":"evaleff","expr":E}` — the total reference semantics. -/
def evalEffRequest (j : Json) : Except String Json := do
  pure (outcomeToJson (Bang.CalcEff.eval [] (← srcEffFromJson (← jField j "expr"))))

/-- `{"op":"execeff","fuel":N,"expr":E}` — the calculated handler machine. -/
def execEffRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let src  ← srcEffFromJson (← jField j "expr")
  match Bang.CalcEff.run fuel src with
  | some res => pure (resultToJson res)
  | none     => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")])

/-! ## The State machine (`evalst`/`execst`) — threaded register (K3)

`Bang.CalcSt`: the total reference `eval` (`evalst`) and the calculated state-
register machine (`execst`) both return `(value, state)`. -/

partial def srcStFromJson (j : Json) : Except String Bang.CalcSt.Src := do
  match ← jStr j "t" with
  | "val"      => pure (.val (← jIntF j "n"))
  | "var"      => pure (.var (← jNat j "i"))
  | "add"      => pure (.add (← srcStFromJson (← jField j "a")) (← srcStFromJson (← jField j "b")))
  | "let"      => pure (.letE (← srcStFromJson (← jField j "e1")) (← srcStFromJson (← jField j "e2")))
  | "get"      => pure .get
  | "put"      => pure (.put (← srcStFromJson (← jField j "arg")))
  | "runState" => pure (.runState (← srcStFromJson (← jField j "init")) (← srcStFromJson (← jField j "body")))
  | other      => throw s!"st: unknown tag {other}"

def stOut (value state : Int) : Json :=
  Json.mkObj [("ok", Json.bool true), ("value", Lean.toJson value), ("state", Lean.toJson state)]

/-- `{"op":"evalst","expr":E}` — the total reference semantics. -/
def evalStRequest (j : Json) : Except String Json := do
  let (v, st) := Bang.CalcSt.eval 0 [] (← srcStFromJson (← jField j "expr"))
  pure (stOut v st)

/-- `{"op":"execst","expr":E}` — the calculated state-register machine. -/
def execStRequest (j : Json) : Except String Json := do
  match Bang.CalcSt.run (← srcStFromJson (← jField j "expr")) with
  | some (v :: _, st) => pure (stOut v st)
  | _ => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                           ("msg", Json.str "execst: empty/stuck")])

/-! ## Effects over the CBN closure core (`evalcbneff`/`execcbneff`) — Throws (K3)

The real K3 composition (`Bang.CalcCBNEff`, ADR-0012): zero-shot Throws fused into
the call-by-name closure/thunk core. Both the reference `eval` (fuel-bounded,
`Option Outcome`) and the calculated re-throw-at-boundary machine (`Option Result`)
report the same JSON shape — the top result forced to WHNF on both sides (so they
agree value-for-value), exceptions as `exc label payload`. -/

partial def srcCBNEffFromJson (j : Json) : Except String Bang.CalcCBNEff.Src := do
  match ← jStr j "t" with
  | "val"     => pure (.val (← jIntF j "n"))
  | "var"     => pure (.var (← jNat j "i"))
  | "add"     => pure (.add (← srcCBNEffFromJson (← jField j "a")) (← srcCBNEffFromJson (← jField j "b")))
  | "lam"     => pure (.lam (← srcCBNEffFromJson (← jField j "body")))
  | "app"     => pure (.app (← srcCBNEffFromJson (← jField j "f")) (← srcCBNEffFromJson (← jField j "a")))
  | "let"     => pure (.letE (← srcCBNEffFromJson (← jField j "e1")) (← srcCBNEffFromJson (← jField j "e2")))
  | "thunk"   => pure (.thnk (← srcCBNEffFromJson (← jField j "e")))
  | "force"   => pure (.force (← srcCBNEffFromJson (← jField j "e")))
  | "perform" => pure (.perform (← jNat j "l") (← srcCBNEffFromJson (← jField j "arg")))
  | "handle"  => pure (.handle (← jNat j "l") (← srcCBNEffFromJson (← jField j "onRaise"))
                               (← srcCBNEffFromJson (← jField j "body")))
  | other     => throw s!"cbneff: unknown tag {other}"

def valueCBNEffToJson : Bang.CalcCBNEff.Value → Json
  | .vint n     => Json.mkObj [("v", Json.str "int"), ("n", Lean.toJson n)]
  | .vclo _ _   => Json.mkObj [("v", Json.str "clos")]
  | .vthunk _ _ => Json.mkObj [("v", Json.str "thunk")]

/-- Force a result value to WHNF and report it — shared by `eval`/`exec` so they
agree value-for-value. Forcing can itself raise (`exc`) or run out of fuel. -/
def cbnEffReport (fuel : Nat) (v : Bang.CalcCBNEff.Value) : Json :=
  match Bang.CalcCBNEff.forceV fuel v with
  | some (.ret w)   => Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "ret"),
                                   ("value", valueCBNEffToJson w)]
  | some (.exc l p) => Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "exc"),
                                   ("label", Lean.toJson l), ("payload", valueCBNEffToJson p)]
  | none            => Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")]

/-- `{"op":"evalcbneff","fuel":N,"expr":E}` — the reference semantics. -/
def evalCBNEffRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let src  ← srcCBNEffFromJson (← jField j "expr")
  match Bang.CalcCBNEff.eval fuel [] src with
  | none            => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")])
  | some (.ret v)   => pure (cbnEffReport fuel v)
  | some (.exc l p) => pure (Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "exc"),
                                         ("label", Lean.toJson l), ("payload", valueCBNEffToJson p)])

/-- `{"op":"execcbneff","fuel":N,"expr":E}` — the calculated handler+closure machine. -/
def execCBNEffRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let src  ← srcCBNEffFromJson (← jField j "expr")
  match Bang.CalcCBNEff.run fuel src with
  | some (.halt (v :: _)) => pure (cbnEffReport fuel v)
  | some (.halt [])       => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                                               ("msg", Json.str "execcbneff: empty halt stack")])
  | some (.uncaught l p)  => pure (Json.mkObj [("ok", Json.bool true), ("outcome", Json.str "exc"),
                                               ("label", Lean.toJson l), ("payload", valueCBNEffToJson p)])
  | none                  => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")])

/-! ## State over the CBN closure core (`evalcbnst`/`execcbnst`) — K3 (ADR-0013)

State (`get`/`put`/`runState`) threaded through the call-by-name closure/thunk
core (`Bang.CalcCBNSt`). Both the reference `eval` and the calculated machine
return `(value, state)`; the value is reported as a WHNF tag (the machine's halt
value equals `eval`'s, so they agree directly). -/

partial def srcCBNStFromJson (j : Json) : Except String Bang.CalcCBNSt.Src := do
  match ← jStr j "t" with
  | "val"      => pure (.val (← jIntF j "n"))
  | "var"      => pure (.var (← jNat j "i"))
  | "add"      => pure (.add (← srcCBNStFromJson (← jField j "a")) (← srcCBNStFromJson (← jField j "b")))
  | "lam"      => pure (.lam (← srcCBNStFromJson (← jField j "body")))
  | "app"      => pure (.app (← srcCBNStFromJson (← jField j "f")) (← srcCBNStFromJson (← jField j "a")))
  | "let"      => pure (.letE (← srcCBNStFromJson (← jField j "e1")) (← srcCBNStFromJson (← jField j "e2")))
  | "thunk"    => pure (.thnk (← srcCBNStFromJson (← jField j "e")))
  | "force"    => pure (.force (← srcCBNStFromJson (← jField j "e")))
  | "get"      => pure .get
  | "put"      => pure (.put (← srcCBNStFromJson (← jField j "arg")))
  | "runState" => pure (.runState (← srcCBNStFromJson (← jField j "init")) (← srcCBNStFromJson (← jField j "body")))
  | other      => throw s!"cbnst: unknown tag {other}"

def valueCBNStToJson : Bang.CalcCBNSt.Value → Json
  | .vint n     => Json.mkObj [("v", Json.str "int"), ("n", Lean.toJson n)]
  | .vclo _ _   => Json.mkObj [("v", Json.str "clos")]
  | .vthunk _ _ => Json.mkObj [("v", Json.str "thunk")]

def cbnStOut (v : Bang.CalcCBNSt.Value) (st : Int) : Json :=
  Json.mkObj [("ok", Json.bool true), ("value", valueCBNStToJson v), ("state", Lean.toJson st)]

/-- `{"op":"evalcbnst","fuel":N,"expr":E}` — the reference semantics. -/
def evalCBNStRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let src  ← srcCBNStFromJson (← jField j "expr")
  match Bang.CalcCBNSt.eval fuel 0 [] src with
  | some (v, st) => pure (cbnStOut v st)
  | none         => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")])

/-- `{"op":"execcbnst","fuel":N,"expr":E}` — the calculated state+closure machine. -/
def execCBNStRequest (j : Json) : Except String Json := do
  let fuel ← jNat j "fuel"
  let src  ← srcCBNStFromJson (← jField j "expr")
  match Bang.CalcCBNSt.run fuel src with
  | some (v :: _, st) => pure (cbnStOut v st)
  | some ([], _)      => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "stuck"),
                                           ("msg", Json.str "execcbnst: empty halt stack")])
  | none              => pure (Json.mkObj [("ok", Json.bool false), ("reason", Json.str "outOfFuel")])

end Bang.EvalJson
