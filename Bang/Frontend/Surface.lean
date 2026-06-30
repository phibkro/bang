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

module

-- Surface's remaining #guards run `Source.eval` (compiled Operational) at the META phase
-- → meta import. (The Plausible `#test` STACK-LAWS block — meta generators that build
-- runtime values — could NOT live in a module; it was extracted to the non-module
-- `Bang/Surface/PropTest.lean`, the documented tested-superset seam. Phase-1a finding.)
meta import Bang.Core.Semantics
public import Bang.Core.Semantics

namespace Bang.Surface

open Bang
open Bang.EffectRow (Label)

-- Module reveal (Phase 1a). `@[expose] public section`: Audit gates cell_reflects_latest;
-- Surface.Trait + the extracted PropTest consume push/empty/pop and the reactive/trait defs.
@[expose] public section

/-- The single concrete label the tracer bullet uses for `raise`/`handle`.
`Label := Nat` (EffectRow.lean), so `0` is the simplest concrete value. The
surface exposes exactly one exception channel; richer effect declarations are a
later issue (out of scope per PATH-tracer-bullet). -/
def exnLabel : Label := 0

/-- The state channel (rung 1, ADR-0025) — a DISTINCT label from `exnLabel`, so a
state cell and an exception channel coexist without colliding. -/
def stateLabel : Label := 1

/-- The STM channel (rung 3, ADR-0030) — a DISTINCT label from `exnLabel`/`stateLabel`, so a
transactional heap, a state cell, and an exception channel coexist. The `transaction` handler on
this label catches `newTVar`/`readTVar`/`writeTVar`. -/
def stmLabel : Label := 2


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
             | 'atomically' expr                   -- install the STM transaction handler (rung 3) → handle (Handler.transaction)
             | 'new' atom                          -- allocate a TVar (rung 3) → up stmLabel "newTVar"
             | 'read' atom                         -- read a TVar → up stmLabel "readTVar"
             | 'write' atom atom                   -- write a TVar → up stmLabel "writeTVar" (pair ref val)
             | 'match' atom '{' arm arm '}'        -- sum elim → case (arms order-independent, opt commas)
             | 'let' '(' ident ',' ident ')' '=' expr 'in' expr  -- product elim → split
             | 'if' expr 'then' expr 'else' expr   -- conditional → case on Bool=1+1 (issue #4)
             | 'do' '{' stmt (';' stmt)* '}'       -- sequential block → nested letC (issue #27)
             | compare                             -- infix chain: compare → add/sub → mul/div → app (#4)
    compare::= addsub (('<'|'==') addsub)*          -- comparisons (loosest infix; return Bool)
    addsub ::= muldiv (('+'|'-') muldiv)*           -- additive
    muldiv ::= app    (('*'|'/') app)*              -- multiplicative (tightest infix)
    app    ::= atom atom*                           -- juxtaposition → app (left assoc)
    stmt   ::= ident '=' expr | expr                -- do-statement: bind (`=`, like let), or seq/result expr
    arm    ::= ('Left'|'Right') '(' ident ')' '->' expr  -- a match arm (binds the payload at idx 0)
    atom   ::= int                                  -- literal → ret (vint n)
             | ident                                -- variable → ret (vvar i)
             | 'get'                                -- read the state cell → up stateLabel "get" unit
             | '$' atom | '!' atom                  -- force a thunk → force
             | '{' expr '}'                         -- thunk a computation → vthunk
             | '(' expr ')'                         -- grouping
             | '(' expr ',' expr ')'                -- product intro → pair
             | 'Left' '(' expr ')'                  -- sum intro (left)  → inl
             | 'Right' '(' expr ')'                 -- sum intro (right) → inr

State (rung 1, ADR-0025) is a RESUMPTIVE handler on its own label (`stateLabel`,
distinct from `exnLabel`). `state v in e` installs `Handler.state stateLabel v`
around `e`; inside, `put a` stores and `get` reads the cell. `get` is nullary
(atom-position, like a literal); `put`/`state` take an atom argument. The initial
state and `put`'s argument are VALUE-position (so `put { … }` thunks a comp).

STM (rung 3, ADR-0030) reuses the same shape on `stmLabel`. `atomically e` installs
`Handler.transaction stmLabel []` (an empty heap) around `e` — keyword-prefixed like
`handle`, NOT a new punctuator. Inside, the three stm ops are computation-position
`up`-operations: `new a` allocates (returns the TVar index), `read a` reads the cell
at index `a`, and `write r w` packs `(r, w)` into a `pair` and writes. Each op's
arguments are VALUE-position atoms (so a TVar ref is just an `int`, ADR-0030's
`TVarRef = int`). Monomorphic int cells, single-threaded; no `orElse`/`retry`.

`$`/`!` are BOTH force (the v0.1 `!`-force UX; ADR-0007 makes `$` the canonical
force, `!` is actor-send in full bang — here we accept both as force for the
subset, documented as a liquid surface choice). -/

/-- Surface type expressions (ADR-0066 ②). A single grammar, NOT split into value/computation
types — the checker interprets it into the kernel's `VTy`/`CTy` (`tArr` ⇒ a `CTy.arr`, everything
else a `VTy`, with `F`/`U` wrapping inserted by the checker). Carried only by the ascription node
`annotS`; erased at lowering (types never reach the kernel term). -/
inductive Ty where
  | tInt   : Ty                  -- Int
  | tUnit  : Ty                  -- Unit
  | tArr   : Ty → Ty → Ty        -- A -> B   (function; right-assoc)
  | tSum   : Ty → Ty → Ty        -- A + B
  | tProd  : Ty → Ty → Ty        -- A * B
  | tThunk : Ty → Ty             -- Thunk T  (a suspended computation value, the `U` former)
  | tEff   : List String → Ty → Ty  -- T ! {throws, …}  effect-row annotation (names; checker maps to labels)
  deriving Repr, Inhabited, DecidableEq

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
  | stateS : Surf → Surf → Surf          -- state e0 in e   (install the state handler)
  | atomS  : Surf → Surf                 -- atomically e  (install the STM transaction handler)
  | newS   : Surf → Surf                 -- new e   (allocate a TVar)
  | readS  : Surf → Surf                 -- read e   (read a TVar)
  | writeS : Surf → Surf → Surf          -- write r w   (write a TVar)
  -- ADTs (issue #1): sum + product. Intros are values; eliminators carry NAMED binders
  -- that lowering (§2) resolves to the kernel's de-Bruijn `case`/`split`.
  | inlS   : Surf → Surf                 -- Left(e)   (sum intro, left)
  | inrS   : Surf → Surf                 -- Right(e)   (sum intro, right)
  | pairS  : Surf → Surf → Surf          -- (a, b)   (product intro)
  | matchS : Surf → String → Surf → String → Surf → Surf
    -- match s { Left(x) -> e₁ , Right(y) -> e₂ }  → case  (x, y each bind at idx 0)
  | splitS : String → String → Surf → Surf → Surf
    -- let (a, b) = p in body  → split  (a = fst at idx 1, b = snd at idx 0)
  -- arithmetic (issue #4, ADR-0065). Operands are ARBITRARY exprs (A-normalized at lowering, since
  -- the kernel `binop` takes VALUES); `if` is sugar over `case` on `Bool = 1+1`.
  | binopS : BinOp → Surf → Surf → Surf   -- a + b   (arithmetic + - * /, comparison < ==)
  | ifS    : Surf → Surf → Surf → Surf    -- if c then t else e   (sugar over case on Bool = 1+1)
  | annotS : Surf → Ty → Surf             -- (e : T)   type ascription (ADR-0066 ②); erased at lowering
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

/-! ### Capability binders (ADR-0054/0055)

The kernel's `handle h M` now BINDS a capability value at de Bruijn index 0 in `M` (like `lam`):
stepping a `handle` mints a fresh identity `g` and substitutes `vcap g h.label` for that var
(`Source.step`, Operational.lean). An operation no longer carries a positional cap-id or a label —
`perform : Val → OpId → Val` takes the CAPABILITY VALUE, and the label is recovered from the cap's
type (`handlesOp` gates on it). The elaborator emits a `vvar` referencing the enclosing handler's
binder (Core.lean: "the elaborator emits `vvar`, never `vcap`").

Lowering threads the cap binder by pushing a RESERVED sentinel name onto `env` when entering a
handler body, so intervening `lett`/`lam` binders shift it correctly and each operation resolves
its enclosing handler by `lookup`. The sentinels start with `#` (never produced by `pIdent`, which
rejects only keywords/punctuators — so in practice a source program cannot bind one; the tracer
bullet's grammar has no `#`-led idents). One sentinel per handler KIND, so a `raise`/`get`/`new`
each finds its own nearest handler even when kinds nest. -/
def capExn   : String := "#exn"     -- the throws-handler cap binder
def capState : String := "#state"   -- the state-handler cap binder
def capStm   : String := "#stm"     -- the transaction-handler cap binder

mutual
/-- Lower a surface term that is in COMPUTATION position to a `Comp`. -/
def lowerC (env : List String) : Surf → Except String Comp
  | .lit n      => .ok (.ret (.vint n))
  | .var x      => do return .ret (.vvar (← lookup env x))
  | .thunk e    => do return .ret (.vthunk (← lowerC env e))   -- a thunk is a value
  | .force e    => do return .force (← lowerV env e)
  | .lett x e b => do return .letC (← lowerC env e) (← lowerC (x :: env) b)
  | .lam x b    => do return .lam (← lowerC (x :: env) b)
  | .annotS e _ => lowerC env e          -- ascription erased: types never reach the kernel term
  | .app f a    => do return .app (← lowerC env f) (← lowerV env a)
  -- `raise`/`put`/stm ops resolve the enclosing handler's cap binder by sentinel `lookup`, then
  -- `perform` on that `vvar` (ADR-0054). The ARGUMENT is value-position, but issue #26 A-NORMALIZES it:
  -- an atom passes through directly (historical shape — Stage-1b `lower`-examples preserved); a
  -- COMPUTATION (e.g. `get + 1`) is `letC`-bound, performed on `vvar 0`, with the cap index shifted by
  -- the new binder. So `put (get + 1)`, `raise (x * 6)`, `write a (m - 30)` now work.
  | .raise e    => do
      let c ← lookup env capExn
      match lowerV env e with
      | .ok v    => return .perform (.vvar c) "raise" v
      | .error _ => return .letC (← lowerC env e) (.perform (.vvar (c+1)) "raise" (.vvar 0))
  -- handlers BIND the cap at index 0: push the sentinel before lowering the body.
  | .handle e   => do return .handle (.throws exnLabel) (← lowerC (capExn :: env) e)
  | .getS       => do return .perform (.vvar (← lookup env capState)) "get" .vunit
  | .putS e     => do
      let c ← lookup env capState
      match lowerV env e with
      | .ok v    => return .perform (.vvar c) "put" v
      | .error _ => return .letC (← lowerC env e) (.perform (.vvar (c+1)) "put" (.vvar 0))
  -- the initial state `e0` is evaluated OUTSIDE the handler scope (it is the handler's payload, not
  -- under the cap binder), so it lowers in `env`, not `capState :: env`. A-normalized (#29): a computed
  -- initial value (`state (3 + 4) in …`) is `letC`-bound first; the handler reads it at `vvar 0`, and the
  -- body lowers under both the e0 binder and the cap binder (`capState :: "#s0" :: env`).
  | .stateS e0 e => do
      match lowerV env e0 with
      | .ok v    => return .handle (.state stateLabel v) (← lowerC (capState :: env) e)
      | .error _ => do
          let c0 ← lowerC env e0
          let body ← lowerC (capState :: "#s0" :: env) e
          return .letC c0 (.handle (.state stateLabel (.vvar 0)) body)
  | .atomS e    => do return .handle (.transaction stmLabel []) (← lowerC (capStm :: env) e)
  | .newS e     => do
      let c ← lookup env capStm
      match lowerV env e with
      | .ok v    => return .perform (.vvar c) "newTVar" v
      | .error _ => return .letC (← lowerC env e) (.perform (.vvar (c+1)) "newTVar" (.vvar 0))
  | .readS e    => do
      let c ← lookup env capStm
      match lowerV env e with
      | .ok v    => return .perform (.vvar c) "readTVar" v
      | .error _ => return .letC (← lowerC env e) (.perform (.vvar (c+1)) "readTVar" (.vvar 0))
  -- write: the TVar REF stays value-position (refs are atoms); only the written VALUE is A-normalized,
  -- shifting the ref by the new binder when it is.
  | .writeS r w => do
      let c ← lookup env capStm
      let rv ← lowerV env r
      match lowerV env w with
      | .ok wv   => return .perform (.vvar c) "writeTVar" (.pair rv wv)
      | .error _ => return .letC (← lowerC env w) (.perform (.vvar (c+1)) "writeTVar" (.pair (Val.shift rv) (.vvar 0)))
  -- ADTs (issue #1). Intros lower to `ret <val>`; eliminators thread NAMED binders → de-Bruijn case/split.
  -- VALUE-position args are A-NORMALIZED (issue #29): an atom passes through unchanged (old shape, so the
  -- Stage-1b/2d lower-examples are preserved); a COMPUTATION (`Right(x / y)`, `match (if …){…}`) is
  -- `letC`-bound and used at `vvar 0`, with the rest shifted by the new binder (#26 part-1, generalized).
  | .inlS e     => do
      match lowerV env e with
      | .ok v    => return .ret (.inl v)
      | .error _ => return .letC (← lowerC env e) (.ret (.inl (.vvar 0)))
  | .inrS e     => do
      match lowerV env e with
      | .ok v    => return .ret (.inr v)
      | .error _ => return .letC (← lowerC env e) (.ret (.inr (.vvar 0)))
  | .pairS a b  => do
      match lowerV env a, lowerV env b with
      | .ok av, .ok bv => return .ret (.pair av bv)   -- both values: unchanged
      | _, _ => do                                    -- ≥1 computation: bind both, pair vvar1/vvar0
          let ca ← lowerC env a
          let cb ← lowerC ("#pa" :: env) b
          return .letC ca (.letC cb (.ret (.pair (.vvar 1) (.vvar 0))))
  -- `case v N₁ N₂`: each branch binds its payload at idx 0 → push the arm's binder. A-normalize the
  -- scrutinee: a computation `case`s on the bound `vvar 0`, branches lowered under the scrutinee binder.
  | .matchS s lx e1 ry e2 => do
      match lowerV env s with
      | .ok v    => return .case v (← lowerC (lx :: env) e1) (← lowerC (ry :: env) e2)
      | .error _ => do
          let cs ← lowerC env s
          let n1 ← lowerC (lx :: "#sc" :: env) e1
          let n2 ← lowerC (ry :: "#sc" :: env) e2
          return .letC cs (.case (.vvar 0) n1 n2)
  -- `split v N`: N binds idx 1 = fst, idx 0 = snd → cons snd LAST (`b :: a :: env`). Verified vs B2.
  | .splitS a b p body => do
      match lowerV env p with
      | .ok v    => return .split v (← lowerC (b :: a :: env) body)
      | .error _ => do
          let cp ← lowerC env p
          let n ← lowerC (b :: a :: "#sc" :: env) body
          return .letC cp (.split (.vvar 0) n)
  -- ARITHMETIC (issue #4). A-NORMALIZE: the kernel `binop` needs VALUE operands, but `a`/`b` may be
  -- computations (nested arithmetic, calls), so let-bind both — `a` at idx 1, `b` at idx 0 — then
  -- `binop op (vvar 1) (vvar 0)`. Uniform: a literal lowers to `ret`, which `letC` binds fine. The
  -- sentinel names (`#bl`) only shift de-Bruijn depth; the grammar can't bind a `#`-name.
  | .binopS op a b => do
      let ca ← lowerC env a
      let cb ← lowerC ("#bl" :: env) b
      return .letC ca (.letC cb (.binop op (.vvar 1) (.vvar 0)))
  -- `if c then t else e`: A-normalize `c` (a comparison is a comp), then `case` on it. `Bool = 1+1`
  -- (ADR-0065): `inl unit = false → e`, `inr unit = true → t`. Branches sit under 2 binders (the
  -- condition `letC` + the `case` payload), so they lower in `env` shifted by 2.
  | .ifS c t e => do
      let cc ← lowerC env c
      let ct ← lowerC ("#p" :: "#c" :: env) t
      let ce ← lowerC ("#p" :: "#c" :: env) e
      return .letC cc (.case (.vvar 0) ce ct)

/-- Lower a surface term that is in VALUE position to a `Val`. Only the
value-shaped constructors are legal here; a computation in value position must
be explicitly thunked (`{ … }`) at the surface. -/
def lowerV (env : List String) : Surf → Except String Val
  | .lit n      => .ok (.vint n)
  | .var x      => do return .vvar (← lookup env x)
  | .thunk e    => do return .vthunk (← lowerC env e)
  -- ADT intros are values (issue #1); the eliminators (match/split) are NOT — they hit the catch-all.
  | .inlS e     => do return .inl (← lowerV env e)
  | .inrS e     => do return .inr (← lowerV env e)
  | .pairS a b  => do return .pair (← lowerV env a) (← lowerV env b)
  | .annotS e _ => lowerV env e          -- ascription erased; lower the inner value
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

/-- Split a source string into tokens. Punctuators `(){}$!,;` are always their
own token; everything else is a maximal run of non-space, non-punctuator chars
(so `->` / `<-` / `=>` / `=` and keywords are ordinary space-delimited tokens). -/
def tokenize (s : String) : List String :=
  let punct := "(){}$!,;".toList
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
          || t = "atomically" || t = "new" || t = "read" || t = "write"
          || t = "match" || t = "Left" || t = "Right" || t = "if" || t = "then" || t = "else"
          || t = "do" || t = ";"
          || t = "in" || t = "=" || t = "=>" || t = "->" || t = ","
          || t = "+" || t = "-" || t = "*" || t = "/" || t = "<" || t = "==" || t = ":" then
        .error s!"expected an identifier, got keyword '{t}'"
      else .ok (t, ts)
  | [] => .error "expected an identifier, got end of input"

/-! ### Type-expression parser (ADR-0066 ②)

Own fuel-driven recursion (types contain no expressions). Precedence: `->` (right-assoc, lowest)
over `*` then `+` (left-assoc loops) over atoms (`Int`/`Unit`/`Thunk T`/`(T)`). Invoked only after
a `:` ascription, so its keywords (`Int`, `Unit`, `Thunk`) never collide with value parsing.
Effect annotation `T ! {throws, …}` is a postfix binding tighter than `->` (so `A -> B ! {ρ}` reads
as `A -> (B ! {ρ})` — the latent effect is the codomain's). -/

/-- After a `{`, parse `name (, name)* }` (or `}` for the empty row). Structural on the token list. -/
def pEffRow : P (List String)
  | "}" :: ts      => .ok ([], ts)
  | n :: "}" :: ts => .ok ([n], ts)
  | n :: "," :: ts => do let (rest, ts) ← pEffRow ts; .ok (n :: rest, ts)
  | ts             => .error s!"malformed effect row at {ts}"

/-- Optionally wrap an already-parsed type in `tEff` if a `! { … }` postfix follows. -/
def pTyPostEff (a : Ty) : P Ty
  | "!" :: "{" :: ts => do let (ns, ts) ← pEffRow ts; .ok (.tEff ns a, ts)
  | ts               => .ok (a, ts)

mutual
def pTy : Nat → P Ty
  | 0,     _  => .error "type parser out of fuel"
  | f + 1, ts => do
      let (a, ts) ← pTyAdd f ts
      let (a, ts) ← pTyPostEff a ts        -- optional `! {ρ}` (tighter than ->)
      match ts with
      | "->" :: ts => do let (b, ts) ← pTy f ts; .ok (.tArr a b, ts)   -- right-assoc
      | _          => .ok (a, ts)
def pTyAdd : Nat → P Ty                      -- A + B  (left-assoc, loosest after ->)
  | 0,     _  => .error "type parser out of fuel"
  | f + 1, ts => do let (a, ts) ← pTyMul f ts; pTyAddLoop f a ts
def pTyAddLoop : Nat → Ty → P Ty
  | 0,     a, ts          => .ok (a, ts)
  | f + 1, a, "+" :: ts   => do let (b, ts) ← pTyMul f ts; pTyAddLoop f (.tSum a b) ts
  | _ + 1, a, ts          => .ok (a, ts)
def pTyMul : Nat → P Ty                      -- A * B  (left-assoc, binds tighter than +)
  | 0,     _  => .error "type parser out of fuel"
  | f + 1, ts => do let (a, ts) ← pTyAtom f ts; pTyMulLoop f a ts
def pTyMulLoop : Nat → Ty → P Ty
  | 0,     a, ts          => .ok (a, ts)
  | f + 1, a, "*" :: ts   => do let (b, ts) ← pTyAtom f ts; pTyMulLoop f (.tProd a b) ts
  | _ + 1, a, ts          => .ok (a, ts)
def pTyAtom : Nat → P Ty
  | 0,     _            => .error "type parser out of fuel"
  | _ + 1, "Int" :: ts  => .ok (.tInt, ts)
  | _ + 1, "Unit" :: ts => .ok (.tUnit, ts)
  | f + 1, "Thunk" :: ts => do let (t, ts) ← pTyAtom f ts; .ok (.tThunk t, ts)
  | f + 1, "(" :: ts    => do
      let (t, ts) ← pTy f ts
      let (_, ts) ← expect ")" ts
      .ok (t, ts)
  | _ + 1, t :: _       => .error s!"expected a type, got '{t}'"
  | _ + 1, []           => .error "expected a type, got end of input"
end

/-! The recursive-descent core is **fuel-driven total** recursion (not `partial`)
so the demo `example`s reduce under `rfl` — a `partial def` is opaque to the
kernel's definitional unfolding, which would block the green checks. Fuel bounds
the descent depth; `4·(tokenize output length) + 1` is a safe bound (see `parse`
— each nesting level is a 3-call descent that may consume only one token). The
inner application `loop` also consumes fuel (one per consumed atom). -/

mutual
/-- Parse a full expression (lowest precedence: let / fun / handle / raise / app).
The `Nat` is structural fuel — every recursive call passes the decremented `f`,
which is what makes this total (and lets the demo `example`s reduce under `rfl`).
Fuel is set generously at the call site (token count), so it never bites a
well-formed program; it only bounds the descent. -/
def pExpr : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, "let" :: "(" :: ts => do      -- product elim: let (a, b) = p in body
      let (a, ts) ← pIdent ts
      let (_, ts) ← expect "," ts
      let (b, ts) ← pIdent ts
      let (_, ts) ← expect ")" ts
      let (_, ts) ← expect "=" ts
      let (p, ts) ← pExpr f ts
      let (_, ts) ← expect "in" ts
      let (body, ts) ← pExpr f ts
      .ok (.splitS a b p body, ts)
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
  | f + 1, "atomically" :: ts => do
      let (e, ts) ← pExpr f ts
      .ok (.atomS e, ts)
  | f + 1, "new" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.newS a, ts)
  | f + 1, "read" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.readS a, ts)
  | f + 1, "write" :: ts => do
      let (r, ts) ← pAtom f ts
      let (w, ts) ← pAtom f ts
      .ok (.writeS r w, ts)
  | f + 1, "match" :: ts => do           -- sum elim: match s { Left(x) -> e₁ , Right(y) -> e₂ }
      let (s, ts) ← pAtom f ts            -- scrutinee is an atom (value position); `let`-bind a comp
      let (_, ts) ← expect "{" ts
      let ((c1, x1, b1), ts) ← pArm f ts
      let ts := (match ts with | "," :: r => r | _ => ts)   -- optional separator comma
      let ((c2, x2, b2), ts) ← pArm f ts
      let ts := (match ts with | "," :: r => r | _ => ts)   -- optional trailing comma
      let (_, ts) ← expect "}" ts
      -- arms are order-independent: slot Left→branch₁, Right→branch₂ (kernel `case` order).
      match c1, c2 with
      | "Left", "Right" => .ok (.matchS s x1 b1 x2 b2, ts)
      | "Right", "Left" => .ok (.matchS s x2 b2 x1 b1, ts)
      | _, _ => .error s!"match needs exactly one Left and one Right arm (got {c1}, {c2})"
  | f + 1, "if" :: ts => do            -- conditional: if c then t else e  (sugar over `case` on Bool)
      let (cnd, ts) ← pExpr f ts
      let (_, ts) ← expect "then" ts
      let (thn, ts) ← pExpr f ts
      let (_, ts) ← expect "else" ts
      let (els, ts) ← pExpr f ts
      .ok (.ifS cnd thn els, ts)
  | f + 1, "do" :: ts => do             -- do { stmt ; … ; result } → nested letC (issue #27)
      let (_, ts) ← expect "{" ts
      pDo f ts
  | f + 1, ts => pCompare f ts          -- ▼ infix precedence chain (issue #4)

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
      if t = ")" || t = "}" || t = "in" || t = "=" || t = "=>" || t = "," || t = "->"
         || t = "+" || t = "-" || t = "*" || t = "/" || t = "<" || t = "=="
         || t = "then" || t = "else" || t = ";" then
        .ok (acc, ts)
      else
        match pAtom f ts with
        | .ok (a, ts') => pAppLoop f (.app acc a) ts'
        | .error _     => .ok (acc, ts)

/-- Infix arithmetic via precedence climbing (issue #4): `compare` (loosest) → `add/sub` →
`mul/div` → `app` (tightest). Each level parses a higher-precedence term then left-folds its own
operators. Operators are SPACE-DELIMITED ordinary tokens (`3 + 4`, `x < 3`), so `-` never clashes
with the `->` match-arrow and no tokenizer change is needed. -/
def pCompare : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do let (lhs, ts) ← pAddSub f ts; pCompareLoop f lhs ts
def pCompareLoop : Nat → Surf → P Surf
  | 0,      acc, ts => .ok (acc, ts)
  | f + 1, acc, ts =>
    match ts with
    | "<"  :: r => do let (rhs, ts) ← pAddSub f r; pCompareLoop f (.binopS .lt acc rhs) ts
    | "==" :: r => do let (rhs, ts) ← pAddSub f r; pCompareLoop f (.binopS .eq acc rhs) ts
    | _ => .ok (acc, ts)
def pAddSub : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do let (lhs, ts) ← pMulDiv f ts; pAddSubLoop f lhs ts
def pAddSubLoop : Nat → Surf → P Surf
  | 0,      acc, ts => .ok (acc, ts)
  | f + 1, acc, ts =>
    match ts with
    | "+" :: r => do let (rhs, ts) ← pMulDiv f r; pAddSubLoop f (.binopS .add acc rhs) ts
    | "-" :: r => do let (rhs, ts) ← pMulDiv f r; pAddSubLoop f (.binopS .sub acc rhs) ts
    | _ => .ok (acc, ts)
def pMulDiv : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do let (lhs, ts) ← pApp f ts; pMulDivLoop f lhs ts
def pMulDivLoop : Nat → Surf → P Surf
  | 0,      acc, ts => .ok (acc, ts)
  | f + 1, acc, ts =>
    match ts with
    | "*" :: r => do let (rhs, ts) ← pApp f r; pMulDivLoop f (.binopS .mul acc rhs) ts
    | "/" :: r => do let (rhs, ts) ← pApp f r; pMulDivLoop f (.binopS .div acc rhs) ts
    | _ => .ok (acc, ts)

/-- Parse a `do`-block body (after `do {`), up to and including `}`. Each statement is `x = e` (a
binding) or a bare `e` (sequenced, value discarded); the LAST statement is the block's result. Desugars
straight to nested `letC` — `x = e ; rest` ↦ `let x = e in rest`, `e ; rest` ↦ `let #do = e in rest`,
final `e` ↦ `e` (issue #27, surface sugar — no AST change). Binding uses `=` (NOT a monadic `<-`): in
CBPV `let`/`=` already IS the effectful sequencing bind, so a separate operator would be redundant. The
`#do` discard name is unbindable by the grammar (it starts with `#`), held-then-shifted, never read. -/
def pDo : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts =>
    match ts with
    | "}" :: _ => .error "empty do block"
    | x :: "=" :: rest => do             -- binding statement: x = e
        let (e, ts) ← pExpr f rest
        match ts with
        | ";" :: ts => do let (body, ts) ← pDo f ts; .ok (.lett x e body, ts)
        | "}" :: _  => .error "a do block must END in an expression, not a binding (x = e)"
        | _         => .error "expected ';' or '}' after a do-block statement"
    | _ => do                            -- bare statement, or the final result
        let (e, ts) ← pExpr f ts
        match ts with
        | ";" :: ts => do let (body, ts) ← pDo f ts; .ok (.lett "#do" e body, ts)
        | "}" :: ts => .ok (e, ts)       -- the final statement is the block's value
        | _         => .error "expected ';' or '}' after a do-block statement"

/-- Parse one match arm `('Left'|'Right') '(' ident ')' '->' expr`. Returns the
constructor name, the bound variable, and the arm body (used by `match` in `pExpr`). -/
def pArm : Nat → P (String × String × Surf)
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do
      let (ctor, ts) ← (match ts with
        | "Left"  :: r => (.ok ("Left", r) : Except String (String × List String))
        | "Right" :: r => .ok ("Right", r)
        | t :: _ => .error s!"expected 'Left' or 'Right' starting a match arm, got '{t}'"
        | []     => .error "expected a match arm, got end of input")
      let (_, ts) ← expect "(" ts
      let (x, ts) ← pIdent ts
      let (_, ts) ← expect ")" ts
      let (_, ts) ← expect "->" ts
      let (body, ts) ← pExpr f ts
      .ok ((ctor, x, body), ts)

/-- Parse an atom (highest precedence). -/
def pAtom : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, "(" :: ts => do               -- grouping `(e)` OR product intro `(a, b)`
      let (e, ts) ← pExpr f ts
      match ts with
      | "," :: ts =>
          let (e2, ts) ← pExpr f ts
          let (_, ts) ← expect ")" ts
          .ok (.pairS e e2, ts)
      | ":" :: ts =>                      -- type ascription `(e : T)` → annotS (ADR-0066 ②)
          let (t, ts) ← pTy f ts
          let (_, ts) ← expect ")" ts
          .ok (.annotS e t, ts)
      | _ =>
          let (_, ts) ← expect ")" ts
          .ok (e, ts)
  | f + 1, "Left" :: ts => do            -- sum intro (left) → inl
      let (_, ts) ← expect "(" ts
      let (e, ts) ← pExpr f ts
      let (_, ts) ← expect ")" ts
      .ok (.inlS e, ts)
  | f + 1, "Right" :: ts => do           -- sum intro (right) → inr
      let (_, ts) ← expect "(" ts
      let (e, ts) ← pExpr f ts
      let (_, ts) ← expect ")" ts
      .ok (.inrS e, ts)
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
              || t = "state" || t = "put" || t = "match" || t = "if" || t = "then" || t = "else"
              || t = "atomically" || t = "new" || t = "read" || t = "write" || t = "do"
              || t = "+" || t = "-" || t = "*" || t = "/" || t = "<" || t = "=="
              || t = "in" || t = "=" || t = "=>" || t = "->" || t = "," || t = ";" || t = ")" || t = "}" || t = ":" then
        .error s!"unexpected '{t}' where an atom was expected"
      else .ok (.var t, ts)
  | _ + 1, [] => .error "unexpected end of input where an atom was expected"
end

/-- Parse a whole program: tokenize, parse one expression, require all tokens
consumed. Fuel = 4·(token count) + 1: each NESTING level costs a full
`pExpr→pApp→pAtom` descent (≈3 fuel) yet may consume only one token (e.g.
`Left(7)`, `(a, b)`, deeply-nested parens), so the bound must be a multiple of
the token count, not `+1`. Generous by construction — it never bites a
well-formed program (it only caps runaway recursion for totality). -/
def parse (src : String) : Except String Surf := do
  let toks := tokenize src
  let (e, rest) ← pExpr (toks.length * 4 + 1) toks
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

/-- throws: `handle (raise 7)` — the deep handler aborts with the payload. The `handle` binds the
cap at index 0; the `raise` directly under it references `vvar 0` (ADR-0054). -/
def throwsComp : Comp := .handle (.throws exnLabel) (.perform (.vvar 0) "raise" (.vint 7))
example : Source.eval 20 throwsComp = .done (.vint 7) := by rfl

/-- deep-throws: `handle (let _ = raise 7 in 99)` — `99` is the discarded
continuation; proves the deep handler reaches PAST a `letC` frame. The `raise` is the `letC` HEAD
(not under the `letC` binder), so the cap is still `vvar 0` (the handle binder). -/
def deepComp : Comp :=
  .handle (.throws exnLabel) (.letC (.perform (.vvar 0) "raise" (.vint 7)) (.ret (.vint 99)))
example : Source.eval 20 deepComp = .done (.vint 7) := by rfl

/-- state CELL (rung 1, ADR-0025): `handle (state ℓ 0) (let _ = put 7 in get ())` ⟶ `7`.
The RESUMPTIVE handler stores `7` on `put`, then `get` returns it — the deep handler KEEPS the
captured `letC` continuation and threads the state, unlike `throws` which discards it. (A *counter*
— `get; put (get+1)` — additionally needs arithmetic `+`, a separate K-ADR; out of scope.) -/
def stateCellComp : Comp :=
  .handle (.state stateLabel (.vint 0))
    (.letC (.perform (.vvar 0) "put" (.vint 7)) (.perform (.vvar 1) "get" .vunit))
example : Source.eval 50 stateCellComp = .done (.vint 7) := by rfl

/-- state GET-default: `handle (state ℓ 5) (get ())` ⟶ `5` (read the initial state). -/
def stateGetComp : Comp :=
  .handle (.state stateLabel (.vint 5)) (.perform (.vvar 0) "get" .vunit)
example : Source.eval 50 stateGetComp = .done (.vint 5) := by rfl

/-! ### STM ledger (rung 3, ADR-0030): the transactional moat demo.

`atomically M = handle (transaction stmLabel []) M`. The stm ops are `up`-operations on `stmLabel`,
with the TVar index packed into the payload (Operational.lean §dispatchOn):
  · `newTVar v` = `up stmLabel "newTVar" v`             → returns `vint idx` (the new TVar)
  · `readTVar i` = `up stmLabel "readTVar" (vint i)`     → returns the cell
  · `writeTVar i w` = `up stmLabel "writeTVar" (pair (vint i) w)` → returns `unit`

The ledger has two accounts (TVar 0 = A, TVar 1 = B). The kernel has NO arithmetic (five primitives),
so a "transfer" writes LITERAL post-transfer balances — the demo exercises the heap THREADING +
all-or-nothing ROLLBACK, not arithmetic (a counter needs `+`, a separate K-ADR). `#guard` (compiled),
NOT `rfl`: kernel whnf over the machine is pathological under `rfl`. -/

/-- Helpers building the raw stm operations (the surface `newTVar`/`readTVar`/`writeTVar`
lowerings the L-phase IC will hide behind sugar). Each takes the CAPABILITY value `c` (ADR-0054):
a `vvar` referencing the enclosing `transaction` handler's binder. The de Bruijn index varies with
nesting depth, so the cap is a parameter, not baked in (`stmNew (.vvar 0)`, `stmRead (.vvar 4)`, …). -/
def stmNew (c : Val) (v : Val) : Comp := .perform c "newTVar" v
def stmRead (c : Val) (i : Int) : Comp := .perform c "readTVar" (.vint i)
def stmWrite (c : Val) (i : Int) (w : Val) : Comp := .perform c "writeTVar" (.pair (.vint i) w)

/-- COMMIT: `atomically (alloc A=100, B=0; A:=70; B:=30; read (A,B))` ⟶ `(70, 30)`.
The heap is threaded through every op; the final reads see the committed writes. -/
-- The `transaction` handle binds the stm cap at index 0; each nested `letC` HEAD sits one binder
-- deeper than the last, so the cap climbs `vvar 0 → 1 → … → 5`. (The TVar heap indices `0`/`1` and
-- the final result refs `vvar 1`/`vvar 0` are unaffected — the cap is the OUTERMOST binder.)
def ledgerCommit : Comp :=
  .handle (.transaction stmLabel [])
    (.letC (stmNew (.vvar 0) (.vint 100))        -- idx 0 = A (bind unused: A is statically TVar 0)
      (.letC (stmNew (.vvar 1) (.vint 0))        -- idx 1 = B
        (.letC (stmWrite (.vvar 2) 0 (.vint 70))     -- A := 70
          (.letC (stmWrite (.vvar 3) 1 (.vint 30))   -- B := 30
            (.letC (stmRead (.vvar 4) 0)         -- bind 0 ↦ A's balance
              (.letC (stmRead (.vvar 5) 1)       -- bind 0 ↦ B's balance, A's now at idx 1
                (.ret (.pair (.vvar 1) (.vvar 0)))))))))   -- (A, B) = (70, 30)

#guard (match Source.eval 200 ledgerCommit with
  | .done (.pair (.vint a) (.vint b)) => a == 70 && b == 30 | _ => false)

/-- ABORT: an outer `throws exnLabel` wraps `atomically (alloc; write; raise initial-balances)`.
The `raise` is a foreign op to the `transaction` frame, so it ESCAPES it (ADR-0023 discards the
captured continuation) — the write-delta `(70, 30)` never commits. The abort payload carries the
ORIGINAL balances `(100, 0)`, the observable proof that the transaction rolled back. -/
-- Outer `throws` binds the exn cap (idx 0 in its body); inner `transaction` binds the stm cap (idx 0
-- in the inner body, exn cap now at idx 1 there). The stm ops climb `vvar 0 → 3`; the `raise` is the
-- innermost `letC` continuation and reaches the OUTER exn cap past 4 `letC`s + the inner handle binder
-- ⇒ `vvar 5`.
def ledgerAbort : Comp :=
  .handle (.throws exnLabel)
    (.handle (.transaction stmLabel [])
      (.letC (stmNew (.vvar 0) (.vint 100))
        (.letC (stmNew (.vvar 1) (.vint 0))
          (.letC (stmWrite (.vvar 2) 0 (.vint 70))      -- attempted write (rolled back on abort)
            (.letC (stmWrite (.vvar 3) 1 (.vint 30))    -- attempted write (rolled back on abort)
              -- insufficient funds ⇒ abort with the ORIGINAL balances (100, 0).
              (.perform (.vvar 5) "raise" (.pair (.vint 100) (.vint 0))))))))

#guard (match Source.eval 200 ledgerAbort with
  | .done (.pair (.vint a) (.vint b)) => a == 100 && b == 0 | _ => false)

/-! ### Stage 1e — the REACTIVE CELL (rung 4, ADR-0005): reactivity falls out of thunks.

The LAST v1 MVP rung VALIDATES a thesis rather than adding a capability: reactivity is
EMERGENT, not a new kernel form. A **reactive cell is an unmemoized thunk over a State
cell** — `let c = {get}`. The kernel does NOT memoize a thunk, so every `$c` (force) RE-RUNS
the `get`, re-sampling the *current* threaded state. That re-sample-on-force IS pull-based
reactivity (ADR-0005: "sampling = forcing in equate position"); no `sig`, no subscription
machinery, no kernel change. Push-based / glitch-free propagation is the deferred dial
(PRD §6) and stays out.

These demos run the cell from SOURCE TEXT — a live `{get}` cell whose `$c` reflects each
`put` — then the liveness law proves it for arbitrary writes. -/

-- A reactive cell `c = {get}` re-samples on each force: after `put 5` then `put 9`,
-- `$c` reads the LATEST write (9), not 5 and not the initial 0. THE re-sampling demo.
#guard runYieldsInt 80
  "state 0 in (let c = {get} in (let a = put 5 in (let b = put 9 in $c)))" 9
-- One write: the cell reflects it (5), not the initial 0.
#guard runYieldsInt 80 "state 0 in (let c = {get} in (let z = put 5 in $c))" 5
-- No write: forcing the cell reads the INITIAL state (0) — a live read, not a stale snapshot.
#guard runYieldsInt 80 "state 0 in (let c = {get} in $c)" 0

/-- The reactive cell at the `Comp` level, parameterised by initial state `s0` and the
written value `v`: `state s0 in (let c = {get} in (let _ = put v in $c))`. de Bruijn: `c` is
idx 0 after its binder, idx 1 after the `put`'s `let`, so `$c` is `force (vvar 1)`. -/
def cellComp (s0 v : Int) : Comp :=
  .handle (.state stateLabel (.vint s0))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))         -- c = {get}   (idx 0); cap vvar 0
      (.letC (.perform (.vvar 1) "put" (.vint v))                     -- _ = put v; under 1 letC ⇒ cap vvar 1
        (.force (.vvar 1))))                                   -- $c

/-- **Liveness law (rung 4, ADR-0005):** a reactive cell always reflects the latest write.
For ARBITRARY initial state `s0` and ARBITRARY written `v`, forcing the cell after `put v`
yields exactly `v`. PROVEN by `rfl` (climbs the ADR-0026 ladder to the *verified* rung, not
the tested one): `v` only flows `vint v → stored in the cell → read back`, never inspected,
so the machine reduces symbolically over `s0` and `v`. The initial `s0` is shadowed by the
write — the cell is LIVE, not a snapshot of `s0`. axioms ⊆ {propext} (see `Bang/Audit.lean`). -/
theorem cell_reflects_latest (s0 v : Int) :
    Source.eval 80 (cellComp s0 v) = .done (.vint v) := by rfl

/-! ### Structural equality on kernel terms (additive — NOT a kernel change).

The laws (Stage 1d) compare an evaluated stack against an expected one, so we need to
decide equality of `Val`s. `Core.lean` (the kernel) deliberately derives only `Inhabited`;
adding `DecidableEq` there would be a kernel edit (forbidden at this layer). Instead we
define a structural `BEq` HERE, in the additive surface, mutually over `Val`/`Comp`/`Handler`
(the recursion crosses the CBPV adjunction at `vthunk`). It is total and structural — no
stack-shape assumption — so it is also safe under the `#guard`s above. -/

mutual
def beqVal : Val → Val → Bool
  | .vunit,      .vunit      => true
  | .vint a,     .vint b     => a == b
  | .vvar i,     .vvar j     => i == j
  | .vthunk c,   .vthunk d   => beqComp c d
  | .inl a,      .inl b      => beqVal a b
  | .inr a,      .inr b      => beqVal a b
  | .pair a b,   .pair c d   => beqVal a c && beqVal b d
  | .fold a,     .fold b     => beqVal a b
  | _,           _           => false
def beqComp : Comp → Comp → Bool
  | .ret a,        .ret b        => beqVal a b
  | .letC a b,     .letC c d     => beqComp a c && beqComp b d
  | .force a,      .force b      => beqVal a b
  | .lam a,        .lam b        => beqComp a b
  | .app a v,      .app b w      => beqComp a b && beqVal v w
  -- ADR-0054: `perform c op v` — `c` is the CAPABILITY value (compare structurally), no positional
  -- cap-id and no label (the label is recovered from `c`'s type, not stored in the term).
  | .perform c o v, .perform c' o' w => beqVal c c' && o == o' && beqVal v w
  | .handle h a,   .handle h' b  => beqHandler h h' && beqComp a b
  | .case v a b,   .case w c d   => beqVal v w && beqComp a c && beqComp b d
  | .split v a,    .split w b    => beqVal v w && beqComp a b
  | .unfold v,     .unfold w     => beqVal v w
  | .oom,          .oom          => true
  | .wrong s,      .wrong t      => s == t
  | _,             _             => false
def beqHandler : Handler → Handler → Bool
  | .state ℓ v,   .state ℓ' w   => ℓ == ℓ' && beqVal v w
  | .throws ℓ,    .throws ℓ'    => ℓ == ℓ'
  | .transaction ℓ Θ, .transaction ℓ' Θ' => ℓ == ℓ' && beqStore Θ Θ'
  | _,            _             => false
def beqStore : List Val → List Val → Bool
  | [],      []      => true
  | a :: as, b :: bs => beqVal a b && beqStore as bs
  | _,       _       => false
end

instance : BEq Val := ⟨beqVal⟩


/-! ### Stage 1c — the surface `Stack` (rung 2 L, ADR-0029): the first moat demo.

GOAL-1 (phase L): a friendly `Stack` surface that HIDES `fold`/`unfold` — the user
writes `empty`/`push`/`pop`, never the μ coercions or the sum/product formers. This
runs sum + product + μ end-to-end via `Source.eval`.

`Stack = μX. 1 + (Int × X)`:
  · `empty      = fold (inl unit)`
  · `push n s   = fold (inr (pair (vint n) s))`
  · `pop s`     ⟶ a STRUCTURED result, encoded in the object language as a sum value:
       - empty  ⟶ `inl unit`                    (the "none" of `1 + (Int × Stack)`)
       - cons   ⟶ `inr (pair (vint top) rest)`  (the "some (top, rest)")
    so the round-trip law `pop (push x s) = some (x, s)` can recover BOTH the popped
    element AND the remaining stack (K1's `stPop` returned only the top Int, which the
    round-trip law cannot witness). `pop` is `unfold` → `case` on the sum; the cons
    branch `split`s the pair and re-pairs `(top, rest)` under `inr`. `#guard` (compiled),
    NOT `rfl`: kernel whnf over the machine is pathological under `rfl`. -/

/-- `empty = fold (inl unit)` — the surface form; `fold`/`inl` stay hidden from the user. -/
def empty : Val := .fold (.inl .vunit)

/-- `push n s = fold (inr ⟨n, s⟩)` — cons a new top; the μ-`fold` is hidden. -/
def push (n : Int) (s : Val) : Val := .fold (.inr (.pair (.vint n) s))

/-- `pop s` as a computation returning the STRUCTURED result `1 + (Int × Stack)`:
`inl unit` on empty (none), `inr ⟨top, rest⟩` on a cons (some). `unfold s` exposes
the sum; `case` picks the branch; the cons branch `split`s the payload pair into
`top` (idx 1) and `rest` (idx 0) and re-pairs them under `inr`. The user never sees
`unfold`/`case`/`split` — only `pop`. -/
def pop (s : Val) : Comp :=
  -- letC (unfold s) binds the unfolded `1 + (Int×Stack)` value at index 0.
  .letC (.unfold s)
    (.case (.vvar 0)
      -- empty branch: vvar0 = unit → none = inl unit.
      (.ret (.inl .vunit))
      -- cons branch: payload pair at idx 0; split binds top (idx 1), rest (idx 0);
      -- re-pair as some (top, rest) = inr (pair top rest).
      (.split (.vvar 0) (.ret (.inr (.pair (.vvar 1) (.vvar 0))))))

/-- `pop (push 7 empty)` ⟶ `done (some (7, empty))` = `inr ⟨vint 7, empty⟩`. -/
def stackTopComp : Comp := pop (push 7 empty)
#guard (match Source.eval 50 stackTopComp with
  | .done (.inr (.pair (.vint n) _)) => n == 7 | _ => false)

/-- `pop (push 9 (push 7 empty))` ⟶ top is `9` (LIFO: the most recent push tops),
and the `rest` is `push 7 empty`. -/
def stackTop2Comp : Comp := pop (push 9 (push 7 empty))
#guard (match Source.eval 50 stackTop2Comp with
  | .done (.inr (.pair (.vint n) rest)) => n == 9 && (rest == push 7 empty) | _ => false)

-- `pop empty` ⟶ `done (inl unit)` = none — the empty-stack branch fires.
#guard (match Source.eval 50 (pop empty) with | .done (.inl .vunit) => true | _ => false)

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

/-! ### Stage 2c — the STM ledger, run FROM SOURCE TEXT (rung 3, ADR-0030).

The same transactional semantics as the hand-built `ledgerCommit`/`ledgerAbort` above,
now parsed: `atomically` installs `transaction stmLabel []`, `new`/`read`/`write` lower
to the `up stmLabel …` ops. `new` returns the fresh TVar index, so `let r = new v` binds
`r` to the heap index (the first alloc is `vint 0`). -/

-- COMMIT, from source: allocate r=100, write 70, read it back ⟶ done (vint 70).
-- The heap is threaded through the transaction; the read sees the committed write.
#guard runYieldsInt 200
  "atomically (let r = new 100 in (let z = write r 70 in read r))" 70

-- COMMIT, two TVars: r0=100, r1=0; write r1 := 55; read r1 ⟶ 55 (the second cell).
-- Pins that `new` allocates DISTINCT indices and writes hit the right cell.
#guard runYieldsInt 200
  "atomically (let r0 = new 100 in (let r1 = new 0 in (let z = write r1 55 in read r1)))" 55

-- ABORT rolls back, from source: an outer `handle` (throws) wraps a transaction that
-- allocates r=100, writes 70, then `raise`s the ORIGINAL balance `100`. The `raise` is
-- foreign to the `transaction` frame, so it ESCAPES it (ADR-0023 discards the captured
-- continuation) — the write-delta `70` never commits. The abort payload is the original
-- `100`, the observable witness that the transaction rolled back. ⟶ done (vint 100).
#guard runYieldsInt 200
  "handle (atomically (let r = new 100 in (let z = write r 70 in raise 100)))" 100

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
-- STM forms (rung 3): `atomically`/`new`/`read`/`write` parse to their `Surf` constructors.
#guard parsesTo "atomically (let r = new 100 in (let z = write r 70 in read r))"
  (.atomS (.lett "r" (.newS (.lit 100))
    (.lett "z" (.writeS (.var "r") (.lit 70)) (.readS (.var "r")))))

/-! ### Stage 2d — ADTs from source text (issue #1): sums + products, modern surface.

The kernel sum/product (`inl`/`inr`/`pair`/`case`/`split`) are now SURFACEABLE — no
hand-built `Comp`. Modern syntax: `Left`/`Right` build a sum, `(a, b)` a product,
`match s { Left(x) -> … , Right(y) -> … }` eliminates a sum (arms order-independent),
and `let (a, b) = p in …` destructures a product. `Left`/`Right` are the anonymous-sum
core; named user variants (`Some`/`Ok`) need the type-declaration layer (a later issue). -/

-- Lowering (Stage-1b style): the named surface tree lowers to the de-Bruijn `case`/`split`.
-- `match Right(7) { Left(a) -> 0 , Right(x) -> x }` ⟶ `case (inr 7) (ret 0) (ret vvar0)`.
example :
    lower (.matchS (.inrS (.lit 7)) "a" (.lit 0) "x" (.var "x"))
      = .ok (.case (.inr (.vint 7)) (.ret (.vint 0)) (.ret (.vvar 0))) := by rfl
-- `let (a, b) = (3, 4) in a` lowers `split` with fst at idx 1 (`vvar 1`) — the binding-order pin.
example :
    lower (.splitS "a" "b" (.pairS (.lit 3) (.lit 4)) (.var "a"))
      = .ok (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1))) := by rfl

-- SUM, from source: `match` discriminates the tag and binds the payload.
#guard runYieldsInt 20 "match Right(7) { Left(a) -> 0 , Right(x) -> x }" 7
#guard runYieldsInt 20 "match Left(7) { Left(a) -> a , Right(x) -> 0 }" 7
-- arms are order-independent: Right-first parses to the SAME `case`.
#guard runYieldsInt 20 "match Left(7) { Right(x) -> 0 , Left(a) -> a }" 7

-- PRODUCT, from source: destructure `(3, 4)`; `a` = fst = 3, `b` = snd = 4 (binding order).
#guard runYieldsInt 20 "let (a, b) = (3, 4) in a" 3
#guard runYieldsInt 20 "let (a, b) = (3, 4) in b" 4
-- nested destructure + re-pair proves the swap round-trips: (3,4) → (b,a) = (4,3) → fst = 4.
#guard runYieldsInt 20 "let (a, b) = (3, 4) in (let (c, d) = (b, a) in c)" 4

-- Parse checks (Stage-2b style): the surface trees parse exactly as expected.
#guard parsesTo "Left(7)" (.inlS (.lit 7))
#guard parsesTo "(3, 4)" (.pairS (.lit 3) (.lit 4))
#guard parsesTo "match s { Left(x) -> x , Right(y) -> y }"
  (.matchS (.var "s") "x" (.var "x") "y" (.var "y"))
#guard parsesTo "let (a, b) = p in a" (.splitS "a" "b" (.var "p") (.var "a"))

/-! ### Stage 2e — arithmetic & `if` from source text (issue #4, ADR-0065).

Infix `+ − × ÷` and `< ==` with C-style precedence (`*` tighter than `+`, both tighter than `<`),
plus `if c then t else e` as sugar over `case` on `Bool = 1+1`. Operators are space-delimited. -/

#guard runYieldsInt 20 "3 + 4" 7
#guard runYieldsInt 20 "2 + 3 * 4" 14            -- `*` binds tighter than `+`
#guard runYieldsInt 20 "10 - 3 - 2" 5            -- left-associative
#guard runYieldsInt 20 "(2 + 3) * 4" 20          -- parentheses override precedence
#guard runYieldsInt 30 "let x = 5 in x + 1" 6    -- the counter step, from source text
#guard runYieldsInt 30 "if 3 < 4 then 1 else 0" 1
#guard runYieldsInt 30 "if 4 < 3 then 1 else 0" 0
#guard runYieldsInt 30 "if 2 == 2 then 7 else 8" 7
-- the canonical COUNTER over a live state cell — blocked since rung-1, now written from source:
#guard runYieldsInt 50 "state 5 in (get + 1)" 6

-- parse-shape checks: precedence is structural, not eval-coincidence.
#guard parsesTo "a + b * c" (.binopS .add (.var "a") (.binopS .mul (.var "b") (.var "c")))
#guard parsesTo "if c then t else e" (.ifS (.var "c") (.var "t") (.var "e"))

-- do-notation (issue #27): `x = e` → `lett x`, bare `e` → `lett "#do"`, last stmt = result.
#guard runYieldsInt 30 "do { x = 3; y = 4; x + y }" 7
#guard parsesTo "do { x = a; b; c }" (.lett "x" (.var "a") (.lett "#do" (.var "b") (.var "c")))

end -- public section
end Bang.Surface
