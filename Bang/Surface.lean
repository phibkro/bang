/-
  Bang/Surface.lean — the tracer-bullet surface layer (PATH-tracer-bullet).
  ─────────────────────────────────────────────────────────────────────────
  The thinnest end-to-end slice that makes bang-lang RUN a program:

      surface String  →[parse]→  Surf  →[lower]→  Comp  →[Source.eval]→  Result Val

  This module is ADDITIVE and lives OUTSIDE the verification spine. It produces
  no typing derivations: `Comp` is grade-free, so to *run* a program we only need
  the AST, not a `HasCTy` proof (type-checking the surface is a later issue).

  Two stages, both exercised by the `example`s at the bottom (so `lake build`
  fails if either regresses):

    §1  Surface AST (`Surf`) — names, not de Bruijn indices.
    §2  Lowering `Surf → Comp` — the name→index resolution pass.
    §3  A minimal hand-rolled parser `String → Except String Surf`.
    §4  `run : String → Result Val` and the green demo checks (Stage 1 + Stage 2).

  The kernel has NO primitive arithmetic (five primitives; adding `+` needs a
  K-ADR), so the "pure" demo is `let`/binding-shaped, not `x + y`. See the
  FINDING in `paths/PATH-tracer-bullet.md`.
-/

import Bang.Operational

namespace Bang.Surface

open Bang
open Bang.EffectRow (Label)

/-- The single concrete label the tracer bullet uses for `raise`/`handle`.
`Label := Nat` (EffectRow.lean), so `0` is the simplest concrete value. The
surface exposes exactly one exception channel; richer effect declarations are a
later issue (out of scope per PATH-tracer-bullet). -/
def exnLabel : Label := 0

/-- The state channel (rung 1, ADR-0025) — a DISTINCT label from `exnLabel`, so a
state cell and an exception channel coexist without colliding. -/
def stateLabel : Label := 1


/-! ## 1. Surface AST (named binders)

A NAMED surface tree — the parser is far simpler with names than with de Bruijn
indices, and lowering does the single name→index pass (§2). The split mirrors
CBPV (`SVal` inert, `SExpr` effectful) but stays deliberately tiny: only the
constructs the subset grammar (§3) produces.

Grammar (the subset this tracer bullet covers):

    expr   ::= 'let' ident '=' expr 'in' expr      -- sequencing → letC
             | 'fun' ident '=>' expr               -- lambda → lam
             | 'handle' expr                       -- install the throws handler
             | 'raise' atom                        -- perform the exception op → up
             | 'state' atom 'in' expr              -- install a state handler (rung 1) → handle (Handler.state)
             | 'put' atom                          -- write the state cell → up stateLabel "put"
             | app
    app    ::= atom atom*                           -- juxtaposition → app (left assoc)
    atom   ::= int                                  -- literal → ret (vint n)
             | ident                                -- variable → ret (vvar i)
             | 'get'                                -- read the state cell → up stateLabel "get" unit
             | '$' atom | '!' atom                  -- force a thunk → force
             | '{' expr '}'                         -- thunk a computation → vthunk
             | '(' expr ')'                         -- grouping

State (rung 1, ADR-0025) is a RESUMPTIVE handler on its own label (`stateLabel`,
distinct from `exnLabel`). `state v in e` installs `Handler.state stateLabel v`
around `e`; inside, `put a` stores and `get` reads the cell. `get` is nullary
(atom-position, like a literal); `put`/`state` take an atom argument. The initial
state and `put`'s argument are VALUE-position (so `put { … }` thunks a comp).

`$`/`!` are BOTH force (the v0.1 `!`-force UX; ADR-0007 makes `$` the canonical
force, `!` is actor-send in full bang — here we accept both as force for the
subset, documented as a liquid surface choice). -/

inductive Surf where
  | lit    : Int → Surf                 -- 3
  | var    : String → Surf              -- x
  | thunk  : Surf → Surf                -- { e }    (suspend)
  | force  : Surf → Surf                -- $e / !e  (observe)
  | lett   : String → Surf → Surf → Surf -- let x = e1 in e2
  | lam    : String → Surf → Surf        -- fun x => e
  | app    : Surf → Surf → Surf          -- e1 e2
  | raise  : Surf → Surf                 -- raise e
  | handle : Surf → Surf                 -- handle e
  | getS   : Surf                        -- get      (read the state cell)
  | putS   : Surf → Surf                 -- put e    (write the state cell)
  | stateS : Surf → Surf → Surf          -- state e0 in e (install state handler)
  deriving Repr, Inhabited, DecidableEq


/-! ## 2. Lowering `Surf → Comp` (the name→de-Bruijn pass)

The de-Bruijn conversion is a single environment-threading pass: `env` is the
list of in-scope names, innermost binder first, so a name's index is its
position in `env` (`List.idxOf?`). Every binder (`lett`, `lam`) conses its name
onto `env` for the body. A free name is a lowering error (returned as
`Except String`).

The value/computation boundary: literals and variables are *values*, but `Comp`
sequences computations, so an atom in computation position lowers to `ret v`.
`force`/`raise`/`thunk` bridge the adjunction. -/

/-- Resolve a name to its de Bruijn index given the in-scope environment
(innermost binder at position 0). -/
def lookup (env : List String) (x : String) : Except String Nat :=
  match env.idxOf? x with
  | some i => .ok i
  | none   => .error s!"unbound variable: {x}"

mutual
/-- Lower a surface term that is in COMPUTATION position to a `Comp`. -/
def lowerC (env : List String) : Surf → Except String Comp
  | .lit n      => .ok (.ret (.vint n))
  | .var x      => do return .ret (.vvar (← lookup env x))
  | .thunk e    => do return .ret (.vthunk (← lowerC env e))   -- a thunk is a value
  | .force e    => do return .force (← lowerV env e)
  | .lett x e b => do return .letC (← lowerC env e) (← lowerC (x :: env) b)
  | .lam x b    => do return .lam (← lowerC (x :: env) b)
  | .app f a    => do return .app (← lowerC env f) (← lowerV env a)
  | .raise e    => do return .up exnLabel "raise" (← lowerV env e)
  | .handle e   => do return .handle (.throws exnLabel) (← lowerC env e)
  | .getS       => .ok (.up stateLabel "get" .vunit)
  | .putS e     => do return .up stateLabel "put" (← lowerV env e)
  | .stateS e0 e => do return .handle (.state stateLabel (← lowerV env e0)) (← lowerC env e)

/-- Lower a surface term that is in VALUE position to a `Val`. Only the
value-shaped constructors are legal here; a computation in value position must
be explicitly thunked (`{ … }`) at the surface. -/
def lowerV (env : List String) : Surf → Except String Val
  | .lit n      => .ok (.vint n)
  | .var x      => do return .vvar (← lookup env x)
  | .thunk e    => do return .vthunk (← lowerC env e)
  | _           => .error "expected a value (wrap a computation in braces)"
end

/-- Lower a closed surface program. -/
def lower (e : Surf) : Except String Comp := lowerC [] e


/-! ## 3. Minimal parser `String → Except String Surf`

Hand-rolled tokenizer + recursive descent. Deliberately small: no spans, no
error recovery — a parse error is a `String`. The grammar is §1's block comment.

Tokenizer: whitespace-separated, with the single-char punctuators
`( ) { } $ !` split off so they need not be space-delimited; `=` and `=>` and
keywords are ordinary tokens. -/

/-- Split a source string into tokens. Punctuators `()[]{}$!` are always their
own token; everything else is a maximal run of non-space, non-punctuator chars. -/
def tokenize (s : String) : List String :=
  let punct := "(){}$!".toList
  let rec go (cs : List Char) (cur : List Char) (acc : List String) : List String :=
    let flush (acc : List String) : List String :=
      if cur.isEmpty then acc else acc ++ [String.ofList cur.reverse]
    match cs with
    | [] => flush acc
    | c :: rest =>
      if c = ' ' || c = '\n' || c = '\t' || c = '\r' then
        go rest [] (flush acc)
      else if punct.contains c then
        go rest [] ((flush acc) ++ [String.ofList [c]])
      else
        go rest (c :: cur) acc
  go s.toList [] []

/-- Parser state = remaining token list. The parser is a function
`List String → Except String (α × List String)`. -/
abbrev P (α : Type) := List String → Except String (α × List String)

def expect (tok : String) : P Unit
  | t :: ts => if t = tok then .ok ((), ts) else .error s!"expected '{tok}', got '{t}'"
  | []      => .error s!"expected '{tok}', got end of input"

/-- Is `s` a non-negative integer literal? -/
def isIntLit (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit

/-- Parse an identifier token (not a keyword/punctuator). Non-recursive. -/
def pIdent : P String
  | t :: ts =>
      if t = "let" || t = "fun" || t = "handle" || t = "raise"
          || t = "state" || t = "get" || t = "put"
          || t = "in" || t = "=" || t = "=>" then
        .error s!"expected an identifier, got keyword '{t}'"
      else .ok (t, ts)
  | [] => .error "expected an identifier, got end of input"

/-! The recursive-descent core is **fuel-driven total** recursion (not `partial`)
so the demo `example`s reduce under `rfl` — a `partial def` is opaque to the
kernel's definitional unfolding, which would block the green checks. Fuel bounds
the descent depth; `tokenize`'s output length is a safe bound, and the demos
pass `(tokenize src).length + 1`. The inner application `loop` also consumes
fuel (one per consumed atom). -/

mutual
/-- Parse a full expression (lowest precedence: let / fun / handle / raise / app).
The `Nat` is structural fuel — every recursive call passes the decremented `f`,
which is what makes this total (and lets the demo `example`s reduce under `rfl`).
Fuel is set generously at the call site (token count), so it never bites a
well-formed program; it only bounds the descent. -/
def pExpr : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, "let" :: ts => do
      let (x, ts) ← pIdent ts
      let (_, ts) ← expect "=" ts
      let (e1, ts) ← pExpr f ts
      let (_, ts) ← expect "in" ts
      let (e2, ts) ← pExpr f ts
      .ok (.lett x e1 e2, ts)
  | f + 1, "fun" :: ts => do
      let (x, ts) ← pIdent ts
      let (_, ts) ← expect "=>" ts
      let (b, ts) ← pExpr f ts
      .ok (.lam x b, ts)
  | f + 1, "handle" :: ts => do
      let (e, ts) ← pExpr f ts
      .ok (.handle e, ts)
  | f + 1, "raise" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.raise a, ts)
  | f + 1, "state" :: ts => do
      let (e0, ts) ← pAtom f ts
      let (_, ts) ← expect "in" ts
      let (e, ts) ← pExpr f ts
      .ok (.stateS e0 e, ts)
  | f + 1, "put" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.putS a, ts)
  | f + 1, ts => pApp f ts

/-- Parse an application chain: one or more atoms, left-associated. -/
def pApp : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do
      let (head, ts) ← pAtom f ts
      pAppLoop f head ts

/-- The left-association loop of `pApp`: keep eating atoms while one can start. -/
def pAppLoop : Nat → Surf → P Surf
  | 0,      acc, ts => .ok (acc, ts)
  | f + 1, acc, ts =>
    match ts with
    | [] => .ok (acc, ts)
    | t :: _ =>
      if t = ")" || t = "}" || t = "in" || t = "=" || t = "=>" then
        .ok (acc, ts)
      else
        match pAtom f ts with
        | .ok (a, ts') => pAppLoop f (.app acc a) ts'
        | .error _     => .ok (acc, ts)

/-- Parse an atom (highest precedence). -/
def pAtom : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, "(" :: ts => do
      let (e, ts) ← pExpr f ts
      let (_, ts) ← expect ")" ts
      .ok (e, ts)
  | f + 1, "{" :: ts => do
      let (e, ts) ← pExpr f ts
      let (_, ts) ← expect "}" ts
      .ok (.thunk e, ts)
  | f + 1, "$" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.force a, ts)
  | f + 1, "!" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.force a, ts)
  | _ + 1, "get" :: ts => .ok (.getS, ts)
  | _ + 1, t :: ts =>
      if isIntLit t then .ok (.lit (Int.ofNat (t.toNat!)), ts)
      else if t = "let" || t = "fun" || t = "handle" || t = "raise"
              || t = "state" || t = "put"
              || t = "in" || t = "=" || t = "=>" || t = ")" || t = "}" then
        .error s!"unexpected '{t}' where an atom was expected"
      else .ok (.var t, ts)
  | _ + 1, [] => .error "unexpected end of input where an atom was expected"
end

/-- Parse a whole program: tokenize, parse one expression, require all tokens
consumed. Fuel = token count + 1 (an upper bound on descent depth). -/
def parse (src : String) : Except String Surf := do
  let toks := tokenize src
  let (e, rest) ← pExpr (toks.length + 1) toks
  if rest.isEmpty then .ok e
  else .error s!"trailing tokens after expression: {rest}"


/-! ## 4. The end-to-end pipeline + green demo checks

`runFrom` is the whole tracer bullet as one function. The `example`s below are
the GOAL of PATH-tracer-bullet: a value pops out of a source string. They sit in
the build, so `lake build` regresses if the pipeline breaks.

Discharge strategy (deliberate, two kinds of check):

  * **Kernel-eval and lowering checks** (Stage 1, 1b) are `example … := by rfl`:
    these reduce a concrete `Nat`-fuelled recursion over a *small* `Comp`, which
    the kernel handles in well under a second.

  * **String-parsing checks** (Stage 2, 2b) use `#guard` (compiled / interpreted
    evaluation), NOT `rfl`/`decide`. Reducing the parser over a `String` in the
    *kernel* (`rfl`/`decide`) is pathologically slow — `String` operations don't
    reduce cheaply by `whnf`. `#guard` runs the same check via the compiler in
    milliseconds and STILL fails the build if false, so it is a real green check.
    It is not a banned tactic: the audit forbids `sorry`/`admit`/`native_decide`
    on the spine; `#guard` is none of those and touches no spine theorem.

`runFrom` reports a parse/lower error as `stuck` (the demo programs never hit it).
`runResult` returns the raw `Bool` a `#guard` checks (avoids needing a `BEq`
instance on the kernel's `Result`/`Val`, which would mean editing `Core.lean`). -/

/-- The whole pipeline: source text → value (or a `String` error reported as `stuck`). -/
def runFrom (fuel : Nat) (src : String) : Result Val :=
  match parse src >>= lower with
  | .ok c    => Source.eval fuel c
  | .error _ => .stuck

/-- Does running `src` yield exactly `done (vint n)`? A `Bool` so `#guard` can
check string-driven runs without a `BEq` on kernel types. -/
def runYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  match runFrom fuel src with
  | .done (.vint m) => m == n
  | _               => false

/-! ### Stage 1 — hand-built `Comp` ASTs run to a value. -/

/-- pure: `let x = 3 in x` (let-shaped, NOT `x+y` — kernel has no `+`). -/
def pureComp : Comp := .letC (.ret (.vint 3)) (.ret (.vvar 0))
example : Source.eval 20 pureComp = .done (.vint 3) := by rfl

/-- throws: `handle (raise 7)` — the deep handler aborts with the payload. -/
def throwsComp : Comp := .handle (.throws exnLabel) (.up exnLabel "raise" (.vint 7))
example : Source.eval 20 throwsComp = .done (.vint 7) := by rfl

/-- deep-throws: `handle (let _ = raise 7 in 99)` — `99` is the discarded
continuation; proves the deep handler reaches PAST a `letC` frame. -/
def deepComp : Comp :=
  .handle (.throws exnLabel) (.letC (.up exnLabel "raise" (.vint 7)) (.ret (.vint 99)))
example : Source.eval 20 deepComp = .done (.vint 7) := by rfl

/-- state CELL (rung 1, ADR-0025): `handle (state ℓ 0) (let _ = put 7 in get ())` ⟶ `7`.
The RESUMPTIVE handler stores `7` on `put`, then `get` returns it — the deep handler KEEPS the
captured `letC` continuation and threads the state, unlike `throws` which discards it. (A *counter*
— `get; put (get+1)` — additionally needs arithmetic `+`, a separate K-ADR; out of scope.) -/
def stateCellComp : Comp :=
  .handle (.state stateLabel (.vint 0))
    (.letC (.up stateLabel "put" (.vint 7)) (.up stateLabel "get" .vunit))
example : Source.eval 50 stateCellComp = .done (.vint 7) := by rfl

/-- state GET-default: `handle (state ℓ 5) (get ())` ⟶ `5` (read the initial state). -/
def stateGetComp : Comp :=
  .handle (.state stateLabel (.vint 5)) (.up stateLabel "get" .vunit)
example : Source.eval 50 stateGetComp = .done (.vint 5) := by rfl

/-! ### Stage 1b — the lowering of the hand-written surface ASTs matches Stage 1.

This pins the §2 lowering (name→de-Bruijn pass) independently of the parser. -/

example : lower (.lett "x" (.lit 3) (.var "x")) = .ok pureComp := by rfl
example : lower (.handle (.raise (.lit 7))) = .ok throwsComp := by rfl
example :
    lower (.handle (.lett "_" (.raise (.lit 7)) (.lit 99))) = .ok deepComp := by rfl
-- state forms lower to the hand-built Stage-1 ASTs (pins get/put/state lowering).
example :
    lower (.stateS (.lit 0) (.lett "_" (.putS (.lit 7)) .getS)) = .ok stateCellComp := by rfl
example : lower (.stateS (.lit 5) .getS) = .ok stateGetComp := by rfl

/-! ### Stage 2 — the SAME programs, parsed from SOURCE TEXT, run to the SAME
values (compiled `#guard`; see the discharge note above). -/

-- pure, from source: `let x = 3 in x`  ⟶ done (vint 3)
#guard runYieldsInt 20 "let x = 3 in x" 3
-- throws, from source: `handle (raise 7)`  ⟶ done (vint 7)
#guard runYieldsInt 20 "handle (raise 7)" 7
-- deep-throws, from source: `handle (let z = raise 7 in 99)`  ⟶ done (vint 7)
#guard runYieldsInt 20 "handle (let z = raise 7 in 99)" 7
-- state cell, from source: `state 0 in (let z = put 7 in get)`  ⟶ done (vint 7)
#guard runYieldsInt 50 "state 0 in (let z = put 7 in get)" 7
-- state get-default, from source: `state 5 in get`  ⟶ done (vint 5)
#guard runYieldsInt 50 "state 5 in get" 5

/-! ### Stage 2b — parse alone resolves to the expected surface tree (pins the
parser independently of eval). `parsesTo` returns a `Bool` (via `DecidableEq
Surf`), so `#guard` needs no `BEq`/`Except` instance. -/

/-- Does `src` parse to exactly the surface tree `e`? -/
def parsesTo (src : String) (e : Surf) : Bool :=
  match parse src with
  | .ok e' => decide (e' = e)
  | .error _ => false

#guard parsesTo "let x = 3 in x" (.lett "x" (.lit 3) (.var "x"))
#guard parsesTo "handle (raise 7)" (.handle (.raise (.lit 7)))
#guard parsesTo "state 0 in (let z = put 7 in get)"
  (.stateS (.lit 0) (.lett "z" (.putS (.lit 7)) .getS))
#guard parsesTo "state 5 in get" (.stateS (.lit 5) .getS)
#guard parsesTo "fun x => x" (.lam "x" (.var "x"))

end Bang.Surface
