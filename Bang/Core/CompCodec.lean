module

meta import Lean.Data.Json
meta import Bang.Core.IR
public import Lean.Data.Json
public import Bang.Core.IR

/-!
  Bang/Core/CompCodec.lean — the versioned structural interchange codec for kernel `Comp` values.
  ───────────────────────────────────────────────────────────────────────────────────────────────
  The format is deliberately constructor-shaped rather than surface or Lean syntax. Every node is a
  JSON array whose first element is a constructor tag; the artifact envelope is exactly
  `["bang-core-comp-json-v1", COMP]`. Arrays avoid object-key ordering becoming part of canonical bytes.

  This is a STRUCTURAL codec, not a type checker or a cache-authority boundary. A decoded term may be
  ill-typed; a caller that did not receive it from the checked producer still needs validation. Input
  bytes and constructor depth are bounded before/while decoding so the first persistent-input seam does
  not accidentally promise unbounded work.
-/

namespace Bang.CompCodec

open Lean
open Bang (BinOp ClauseKey Comp Handler Val)

@[expose] public section

/-- Exact format/version tag in every encoded artifact envelope. -/
def format : String := "bang-core-comp-json-v1"

/-- Default maximum UTF-8 input size accepted by `decodeArtifact` (one MiB). -/
def defaultMaxBytes : Nat := 1024 * 1024

/-- Default maximum constructor nesting accepted by the structural decoder. -/
def defaultMaxDepth : Nat := 512

/-- A constructor-shaped JSON node. -/
def node (tag : String) (args : List Json := []) : Json :=
  .arr ((.str tag :: args).toArray)

/-- Decode a constructor-shaped JSON node into its tag and operands. -/
def nodeView (context : String) : Json → Except String (String × List Json)
  | .arr xs =>
      match xs.toList with
      | .str tag :: args => pure (tag, args)
      | _ => throw s!"{context}: expected a non-empty constructor array beginning with a string tag"
  | _ => throw s!"{context}: expected a constructor array"

/-- Consume one unit of the constructor-depth budget. -/
def descend (context : String) : Nat → Except String Nat
  | 0 => throw s!"{context}: constructor depth exceeds the configured limit"
  | fuel + 1 => pure fuel

def expectNat (context : String) (j : Json) : Except String Nat :=
  j.getNat?.mapError fun _ => s!"{context}: expected a natural number"

def expectInt (context : String) (j : Json) : Except String Int :=
  j.getInt?.mapError fun _ => s!"{context}: expected an integer"

def expectString (context : String) (j : Json) : Except String String :=
  j.getStr?.mapError fun _ => s!"{context}: expected a string"

def expectArray (context : String) : Json → Except String (List Json)
  | .arr xs => pure xs.toList
  | _ => throw s!"{context}: expected an array"

/-- Encode a primitive binary operator. -/
def encodeBinOp : BinOp → Json
  | .add => .str "add"
  | .sub => .str "sub"
  | .mul => .str "mul"
  | .div => .str "div"
  | .lt  => .str "lt"
  | .eq  => .str "eq"

/-- Strictly decode a primitive binary operator. -/
def decodeBinOp (j : Json) : Except String BinOp := do
  match ← expectString "binop" j with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | "div" => pure .div
  | "lt"  => pure .lt
  | "eq"  => pure .eq
  | other => throw s!"binop: unknown tag '{other}'"

/-- Encode a custom-handler clause key including its parameter-update mode. -/
def encodeClauseKey : ClauseKey → Json
  | .plain op => node "plain" [.str op]
  | .updating op => node "updating" [.str op]

/-- Strictly decode a custom-handler clause key. -/
def decodeClauseKey (j : Json) : Except String ClauseKey := do
  match ← nodeView "clause key" j with
  | ("plain", [op]) => .plain <$> expectString "plain operation" op
  | ("updating", [op]) => .updating <$> expectString "updating operation" op
  | (tag, args) => throw s!"clause key: unknown tag or arity '{tag}'/{args.length}"

mutual
/-- Exhaustively encode a kernel value. New constructors make this definition fail to compile. -/
partial def encodeVal : Val → Json
  | .vunit => node "vunit"
  | .vint n => node "vint" [n]
  | .vvar i => node "vvar" [i]
  | .vcap n l => node "vcap" [n, l]
  | .vthunk c => node "vthunk" [encodeComp c]
  | .inl v => node "inl" [encodeVal v]
  | .inr v => node "inr" [encodeVal v]
  | .pair a b => node "pair" [encodeVal a, encodeVal b]
  | .fold v => node "fold" [encodeVal v]

/-- Exhaustively encode a kernel computation. -/
partial def encodeComp : Comp → Json
  | .ret v => node "ret" [encodeVal v]
  | .letC m n => node "letC" [encodeComp m, encodeComp n]
  | .force v => node "force" [encodeVal v]
  | .lam m => node "lam" [encodeComp m]
  | .app m v => node "app" [encodeComp m, encodeVal v]
  | .perform c op v => node "perform" [encodeVal c, .str op, encodeVal v]
  | .handle h m => node "handle" [encodeHandler h, encodeComp m]
  | .case v n1 n2 => node "case" [encodeVal v, encodeComp n1, encodeComp n2]
  | .split v n => node "split" [encodeVal v, encodeComp n]
  | .unfold v => node "unfold" [encodeVal v]
  | .binop op v w => node "binop" [encodeBinOp op, encodeVal v, encodeVal w]
  | .oom => node "oom"
  | .wrong s => node "wrong" [.str s]

/-- Exhaustively encode a kernel handler. -/
partial def encodeHandler : Handler → Json
  | .state l v => node "state" [l, encodeVal v]
  | .throws l => node "throws" [l]
  | .transaction l vs => node "transaction" [l, .arr (vs.map encodeVal).toArray]
  | .custom l p cls =>
      let clauses := cls.map fun (key, c) => .arr #[encodeClauseKey key, encodeComp c]
      node "custom" [l, encodeVal p, .arr clauses.toArray]
end

mutual
/-- Decode a value with an explicit maximum constructor depth. -/
partial def decodeVal (fuel : Nat) (j : Json) : Except String Val := do
  let fuel ← descend "value" fuel
  match ← nodeView "value" j with
  | ("vunit", []) => pure .vunit
  | ("vint", [n]) => .vint <$> expectInt "vint" n
  | ("vvar", [i]) => .vvar <$> expectNat "vvar" i
  | ("vcap", [n, l]) => .vcap <$> expectNat "vcap identity" n <*> expectNat "vcap label" l
  | ("vthunk", [c]) => .vthunk <$> decodeComp fuel c
  | ("inl", [v]) => .inl <$> decodeVal fuel v
  | ("inr", [v]) => .inr <$> decodeVal fuel v
  | ("pair", [a, b]) => .pair <$> decodeVal fuel a <*> decodeVal fuel b
  | ("fold", [v]) => .fold <$> decodeVal fuel v
  | (tag, args) => throw s!"value: unknown tag or arity '{tag}'/{args.length}"

/-- Decode a computation with an explicit maximum constructor depth. -/
partial def decodeComp (fuel : Nat) (j : Json) : Except String Comp := do
  let fuel ← descend "computation" fuel
  match ← nodeView "computation" j with
  | ("ret", [v]) => .ret <$> decodeVal fuel v
  | ("letC", [m, n]) => .letC <$> decodeComp fuel m <*> decodeComp fuel n
  | ("force", [v]) => .force <$> decodeVal fuel v
  | ("lam", [m]) => .lam <$> decodeComp fuel m
  | ("app", [m, v]) => .app <$> decodeComp fuel m <*> decodeVal fuel v
  | ("perform", [c, op, v]) =>
      .perform <$> decodeVal fuel c <*> expectString "perform operation" op <*> decodeVal fuel v
  | ("handle", [h, m]) => .handle <$> decodeHandler fuel h <*> decodeComp fuel m
  | ("case", [v, n1, n2]) =>
      .case <$> decodeVal fuel v <*> decodeComp fuel n1 <*> decodeComp fuel n2
  | ("split", [v, n]) => .split <$> decodeVal fuel v <*> decodeComp fuel n
  | ("unfold", [v]) => .unfold <$> decodeVal fuel v
  | ("binop", [op, v, w]) =>
      .binop <$> decodeBinOp op <*> decodeVal fuel v <*> decodeVal fuel w
  | ("oom", []) => pure .oom
  | ("wrong", [s]) => .wrong <$> expectString "wrong payload" s
  | (tag, args) => throw s!"computation: unknown tag or arity '{tag}'/{args.length}"

/-- Decode a handler with an explicit maximum constructor depth. -/
partial def decodeHandler (fuel : Nat) (j : Json) : Except String Handler := do
  let fuel ← descend "handler" fuel
  match ← nodeView "handler" j with
  | ("state", [l, v]) => .state <$> expectNat "state label" l <*> decodeVal fuel v
  | ("throws", [l]) => .throws <$> expectNat "throws label" l
  | ("transaction", [l, vs]) => do
      let label ← expectNat "transaction label" l
      let values ← expectArray "transaction values" vs
      .transaction label <$> values.mapM (decodeVal fuel)
  | ("custom", [l, p, cls]) => do
      let label ← expectNat "custom label" l
      let param ← decodeVal fuel p
      let clauses ← expectArray "custom clauses" cls
      let clauses ← clauses.mapM fun clause => do
        match ← expectArray "custom clause" clause with
        | [key, body] => pure (← decodeClauseKey key, ← decodeComp fuel body)
        | args => throw s!"custom clause: expected pair, got {args.length} elements"
      pure (.custom label param clauses)
  | (tag, args) => throw s!"handler: unknown tag or arity '{tag}'/{args.length}"
end

/-- The canonical JSON value for one structural `Comp` artifact. -/
def encodeArtifactJson (c : Comp) : Json := .arr #[.str format, encodeComp c]

/-- The canonical compact JSON bytes for one structural `Comp` artifact. -/
def encodeArtifact (c : Comp) : String := (encodeArtifactJson c).compress

/-- Decode an already-parsed artifact JSON value, enforcing exact envelope version and shape. -/
def decodeArtifactJson (j : Json) (maxDepth : Nat := defaultMaxDepth) : Except String Comp := do
  match j with
  | .arr xs =>
      match xs.toList with
      | [.str version, body] =>
          if version = format then decodeComp maxDepth body
          else throw s!"comp artifact: unsupported format '{version}', expected '{format}'"
      | args => throw s!"comp artifact: expected a two-element versioned envelope, got {args.length} elements"
  | _ => throw "comp artifact: expected a versioned array envelope"

/-- Parse and decode a structural `Comp` artifact. This checks syntax and shape, not typing.
The byte bound is applied before JSON parsing; the depth bound is applied at every IR constructor. -/
def decodeArtifact (s : String) (maxBytes : Nat := defaultMaxBytes)
    (maxDepth : Nat := defaultMaxDepth) : Except String Comp := do
  if s.utf8ByteSize > maxBytes then
    throw s!"comp artifact: input is {s.utf8ByteSize} bytes; limit is {maxBytes}"
  let json ← Json.parse s |>.mapError fun e => s!"comp artifact: invalid JSON: {e}"
  decodeArtifactJson json maxDepth

private def fullShapeSample : Comp :=
  .letC (.ret (.pair (.vint (-3)) (.vvar 7)))
    (.handle (.custom 9 (.inl .vunit)
      [(.plain "ping", .ret (.vthunk (.lam (.ret (.fold (.vvar 0)))))),
       (.updating "step", .binop .add (.vint 1) (.vint 2))])
      (.case (.inr (.vcap 4 9))
        (.app (.force (.vthunk (.lam (.ret (.vvar 0))))) .vunit)
        (.split (.pair .vunit (.vint 4))
          (.letC (.unfold (.fold (.vvar 0)))
            (.perform (.vcap 4 9) "ping" (.vvar 0))))))

-- Round-trip the dense cross-constructor witness through bytes and back to identical canonical JSON.
#guard match decodeArtifact (encodeArtifact fullShapeSample) with
  | .ok decoded => encodeArtifact decoded == encodeArtifact fullShapeSample
  | .error _ => false

-- Adverse format poles: version, tag/arity, scalar kind, trailing input, depth, and bytes fail loud.
private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard rejected (decodeArtifact "[\"bang-core-comp-json-v0\",[\"oom\"]]")
#guard rejected (decodeArtifact "[\"bang-core-comp-json-v1\",[\"future\"]]")
#guard rejected (decodeArtifact "[\"bang-core-comp-json-v1\",[\"ret\"]]")
#guard rejected (decodeArtifact "[\"bang-core-comp-json-v1\",[\"ret\",[\"vvar\",-1]]]")
#guard rejected (decodeArtifact "[\"bang-core-comp-json-v1\",[\"oom\"]] trailing")
#guard rejected (decodeArtifact (encodeArtifact (.ret .vunit)) defaultMaxBytes 1)
#guard rejected (decodeArtifact (encodeArtifact (.ret .vunit)) 1 defaultMaxDepth)

end


end Bang.CompCodec
