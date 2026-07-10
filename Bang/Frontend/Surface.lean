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

/-- The divergence channel (ADR-0073 §2, #46) — a DISTINCT label marking may-not-terminate. UNLIKE
the other channels it is NEVER performed or handled: it has no operation and no handler (recursion's
partiality has no runtime semantics — `Source.eval` just ooms). It is a pure TYPING marker, added to
the row of a `let rec`'s CALL-SITES (the ADR-0028 total/`Div` stratification seam made type-visible),
stripped at lowering (the kernel term never carries it). -/
def divLabel : Label := 3


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

/-! Surface type expressions (ADR-0066 ②). A single grammar, NOT split into value/computation
types — the checker interprets it into the kernel's `VTy`/`CTy` (`tArr` ⇒ a `CTy.arr`, everything
else a `VTy`, with `F`/`U` wrapping inserted by the checker). Carried only by the ascription node
`annotS`; erased at lowering (types never reach the kernel term). -/
mutual
inductive Ty where
  | tInt   : Ty                  -- Int
  | tUnit  : Ty                  -- Unit
  | tArr   : Ty → Ty → Ty        -- A -> B   (function; right-assoc)
  | tSum   : Ty → Ty → Ty        -- A + B
  | tProd  : Ty → Ty → Ty        -- A * B
  | tThunk : Ty → Ty             -- Thunk T  (a suspended computation value, the `U` former)
  | tSelf  : Ty                  -- Self — the impl target, in trait op signatures (#24, ADR-0068)
  | tName  : String → Ty         -- a declared data name (resolved against the decl env at elaboration, ADR-0069)
  | tApp   : String → TyArgs → Ty  -- a generic data name applied to type args: `List Int` (ADR-0069 generic, bite-1; arity ≤ 2)
  | tMu    : Ty → Ty             -- μ former (INTERNAL — built by data-decl encoding, never parsed in v1)
  | tVar   : Nat → Ty            -- μ-bound de Bruijn type var (INTERNAL, ditto)
  | tEff   : List String → Ty → Ty  -- T ! {throws, …}  effect-row annotation (names; checker maps to labels)
  -- #84 gap 1 (caps-through-functions): `Cap Net` ascribes a function param to a named effect's
  -- capability type. SURFACE form parses as an ordinary `tApp "Cap" (.one (.tName effN))` (no new
  -- grammar — `Cap` rides the EXISTING generic-application parser, `pTyAtom`); `resolveTyG`
  -- special-cases the head name `"Cap"` and resolves `effN` against `env.effects` into THIS closed
  -- RESOLVED form (the `tName`/`tApp` "poison-until-resolveTy-runs" precedent, ADR-0069) — `tyBoth`
  -- reads a `tCap` verbatim (no further env needed) into the kernel's `VT.cap ℓ` (ADR-0054/0070's
  -- existing capability value type). A `tCap` reaching `tyBoth` UNRESOLVED cannot happen (the parser
  -- never emits one directly — only `resolveTyG` constructs it, always already-closed).
  | tCap   : Label → Ty
  -- #90 (row-annotation gap, the #84 gap-1 follow-up): `T ! {…}` could only name the four BUILT-IN
  -- effects (`throws`/`state`/`stm`/`Div`) — `effNames`/`effOf` matched a FIXED literal-string list,
  -- no `env.effects` access, so a USER effect name in a row annotation silently resolved to nothing.
  -- Exactly the `tCap` shape: `resolveTyG`'s `.tEff` arm now resolves EACH name (built-in OR user)
  -- against `effects` into THIS closed RESOLVED form (labels, not names) — `tyBoth`/`effOf` read a
  -- `tEffR` verbatim, no further env needed. A `tEffR` reaching `tyBoth` unresolved cannot happen
  -- (only `resolveTyG` constructs one, always already-closed — same invariant as `tCap`).
  | tEffR  : List Label → Ty → Ty
/-- Type-application arguments, capped at the v1 arity (≤ 2: `Pair a b`, `Either a b`). A mutual
inductive (not `List Ty`) so `Ty`'s `DecidableEq`/`Repr` derive — the `DArms`/`SurfArgs` precedent. -/
inductive TyArgs where
  | one  : Ty → TyArgs
  | two  : Ty → Ty → TyArgs
end
deriving instance Repr, DecidableEq for Ty, TyArgs
instance : Inhabited Ty := ⟨.tInt⟩
instance : Inhabited TyArgs := ⟨.one .tInt⟩

/-- Type-application args as a list (the resolver/monomorphizer consumes them positionally). -/
def TyArgs.toList : TyArgs → List Ty
  | .one a   => [a]
  | .two a b => [a, b]
/-- Map a pure type transform over the args (`substSelf`, structural rewrites). -/
def TyArgs.map (f : Ty → Ty) : TyArgs → TyArgs
  | .one a   => .one (f a)
  | .two a b => .two (f a) (f b)

mutual
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
  -- ── ADR-0069 (data declarations) ──
  | unitS  : Surf                         -- ()   the unit value literal
  | foldS  : Surf → Surf                  -- μ intro (INTERNAL: emitted by ctor elaboration; check-mode only)
  | unfoldS : Surf → Surf                 -- μ elim  (INTERNAL: emitted by named-match elaboration)
  | matchD : Surf → DArms → Surf          -- named-ctor match (parse-only; ELIMINATED by the elaborator —
                                          -- the untyped path fail-louds, data is a Prog-level feature)
  -- ── ADR-0070 (named capabilities) ──
  | withCapS : String → Surf → String → Surf → Surf  -- state <init> as <name> in <body>  (named cap; also `handle as h e` / `atomically as h e`, ADR-0072)
  | dotPerform : Surf → String → SurfArgs → Surf     -- h.op(args) — perform op on the named cap
  -- ── ADR-0073 (recursion) ──
  | letRecS : String → Ty → Surf → Surf → Surf       -- let rec f : T = <fun> in <body>  (μ-knot; DESUGARED in elabS, typed-path only)
  | divMark : Surf → Surf                             -- INTERNAL (#46): adds {divLabel} to the wrapped computation's row; RUNTIME no-op (lowers to its child)
  -- ── issue #68 (multi-binding let sugar) ──
  | lettMulti : LetBindings → Surf → Surf
    -- let x = e1; y = e2; … in body  — a SUGAR MARKER (like `divMark`): semantically transparent
    -- everywhere except the PRINTER, which uses it to distinguish "the author wrote `;`-sugar"
    -- from "the author wrote out a nested `let..in` chain by hand" (the operator's #68 ruling: fmt
    -- prints the sugar for sugar-parsed input, but does NOT auto-collapse a hand-written chain —
    -- and once desugared to plain nested `.lett`, that distinction has NO surviving signal, so the
    -- marker IS the signal). `desugarLettMulti` (below) turns it into the identical nested `.lett`
    -- chain a hand-written pyramid produces; every OTHER consumer (lowering, the typed elaborator,
    -- qualification/renaming passes) calls that FIRST and never pattern-matches `.lettMulti` itself
    -- — the parser produces it, the printer consumes it directly, everything in between erases it.
  -- ── ADR-0095 D1 (RULED, 2026-07-10 — s7probe strawman superseded by the operator-accepted
  -- surface; the D1-binding-gap ruling picked reading (b): `as h` is MANDATORY, no implicit
  -- lowercase-of-Name default — rejected on "silently-shadowing nested same-effect handlers") ──
  | handleCustomS : Option Label → Surf → SurfArgs → String → HClauses → Surf → Surf
    -- `handle e with Name as h { op1(x) => body1, op2(y) => body2, … }` (param-less), or
    -- `handle e with (Name init) as h { … }` (param-carrying, `param` names it in clause bodies).
    -- Field order (NOT the textual order — `e` prints FIRST in source, `label?`/`Name`/`init`/`h`/
    -- `cls` are the `with …` clause; `body` below IS `e`, kept last to match `withCapS`'s own field
    -- convention of "binder info, then the scope it binds"):
    --   `label?`  : the RESOLVED-LABEL slot (WALL 1 fix, manager-ruled Option A) — `none` at parse
    --               time (no `env.effects` in scope yet); `elabS`'s new arm REWRITES it to
    --               `some ℓ` once `Name` resolves against the program's declared effects. `lowerC`
    --               stays a PURE function of the tree (no `ElabEnv` threading) — it reads this slot
    --               directly and fails loud on `none` (unresolved ⟹ elaboration never ran, or the
    --               effect name never resolved — a genuine pipeline gap, never guessed through).
    --               PLAIN `Option Label` (not a mutual mirror of `SurfArgs`'s shape) is fine here —
    --               `Label := Nat` is NOT self-referential, so `deriving DecidableEq` sees through
    --               it without the `Option Surf` wall below.
    --   `effName` : a bare effect-name reference (`.var "Net"`), resolved against `env.effects` at
    --               elaboration (same D1/D2 lookup `.dotPerform`'s D2 arm already uses).
    --   `paramInit` : `SurfArgs.none` for the param-less bare-`Name` form, `.one e0` for the
    --               param-carrying `(Name init)` form — REUSES `SurfArgs` (rather than inventing a
    --               fresh `Option Surf`-shaped mutual type) precisely because `Option Surf` does
    --               NOT derive `DecidableEq` across this mutual group (confirmed: Lean's
    --               structural-deriving handler cannot see through `Option <mutual-self-type>`,
    --               the SAME reason `SurfArgs`/`DArms`/`LetBindings` are bespoke mutual types
    --               instead of `List`/`Option` of `Surf` in the first place — this is that
    --               precedent's rationale generalizing to a NEW field, not a new problem). `.two`
    --               is unused here (never constructed by the parser) but costs nothing structurally.
    --               `.none` desugars to the CLOSED unit value at elaboration (the kernel's
    --               `Handler.custom` always carries a `p : Val`, ADR-0092's premise; a param-less
    --               `effect` still needs SOME closed `p`, and `Unit` is the honest empty choice,
    --               mirroring `state`'s `s : S` — no such gap exists there since `state` ALWAYS has
    --               an explicit `init`).
    --   `h`       : the MANDATORY cap binder (ADR-0095 D1-binding-gap ruling, reading (b) — v1 has
    --               NO implicit/ambient binder; a future additive sugar MAY relax this, but the
    --               ruling is explicit-only for v1, precisely to avoid a same-effect nested `handle`
    --               silently shadowing an outer binding under an implicit lowercase-of-Name name).
    --   `cls`     : the clause list (curried per D3 — see `HClauses`'s own doc comment for the
    --               curry-desugar). Ret-shape UNCHECKED at parse (ADR-0092 D3's gate is
    --               elaboration-time, D4's teaching diagnostic fires there).
    --   `body`    : `e`, the handled expression — elaborated under `h`'s EXTENDED Γ (the D1-binding-
    --               gap ruling's reading (c) mechanics: install the clause-map/binder FIRST, then
    --               elaborate `e` under it — even though `e` prints textually BEFORE `with Name as h
    --               { … }` in source, per D1's own worked example).

/-- A cap-op argument list, capped at the v1 arity (≤ 2: `write` is the only binary op). A mutual
inductive (not `List Surf`) so `Surf`'s `DecidableEq`/`Repr` derive — the `DArms` precedent. -/
inductive SurfArgs where
  | none : SurfArgs
  | one  : Surf → SurfArgs
  | two  : Surf → Surf → SurfArgs

/-- Named-match arms `C(x, y) -> e` — a `Surf`-mutual list (not `List (… × Surf)`) so the
`DecidableEq`/`Repr` derivations stay straightforward (the `VTy`/`CTy` precedent). -/
inductive DArms where
  | nil  : DArms
  | cons : String → List String → Surf → DArms → DArms

/-- The `;`-separated binding list of issue #68's multi-binding `let` sugar — a `Surf`-mutual list
(the SAME reason `DArms` is one, not `List (String × Surf)`): keeps `Surf`'s `DecidableEq`/`Repr`
derivations straightforward. ORDER is binding order (`cons` prepends the FIRST-parsed binding at
the head — see `toLetBindings`), matching how `desugarLettMulti`'s `foldr`-equivalent nests them. -/
inductive LetBindings where
  | nil  : LetBindings
  | cons : String → Surf → LetBindings → LetBindings

/-- ADR-0095 D1/D3 (RULED): clause list `op(argName) => body` entries, a `Surf`-mutual list (the
`DArms` precedent — keeps `Surf`'s `DecidableEq`/`Repr` derivations straightforward). One binder
per clause (the ADR-0092 D3 `arg@0` slot) — the AMBIENT param binder (`P@1`, spelled `param` in
clause bodies per D1's worked example) is NOT here; it is bound once by `handleCustomS`'s own
elaboration (mirrors how `HasClauses.cons` types every clause body under the SAME fixed
`[opA, P]` context, not a per-clause one). D3 rules effect ops CURRIED — but v1's `EffectInfo`/
`HasClauses` (ADR-0092) support only SINGLE-ARG ops (a multi-arrow `effect` op sig is already a
v1 elaboration error, "op is multi-argument"), so a curried MULTI-arg clause has no v1 op to bind
to yet — this ONE-BINDER shape is the currently-reachable v1 fragment of D3's convention; a
curry-desugar for `op(a, b) => body` (→ nested single-binder clauses) is FUTURE work gated on the
`effect` decl surface itself growing multi-arg ops, not something this shape needs to anticipate. -/
inductive HClauses where
  | nil  : HClauses
  | cons : String → String → Surf → HClauses → HClauses
end

deriving instance Repr, Inhabited, DecidableEq for Surf, DArms, SurfArgs, LetBindings, HClauses

/-- Pack parsed match arms into `DArms` (the parser's list shape → the AST's mutual shape). -/
def toDArms : List (String × List String × Surf) → DArms
  | []                => .nil
  | (c, bs, b) :: r   => .cons c bs b (toDArms r)

/-- Pack the parser's `List (String × Surf)` binding list into the mutual-inductive `LetBindings`
shape (the `toDArms` precedent, same reason). -/
def toLetBindings : List (String × Surf) → LetBindings
  | []            => .nil
  | (n, e) :: r   => .cons n e (toLetBindings r)

/-- #21 s7probe: the INVERSE of the `toDArms`/`toLetBindings` packing — unpack `HClauses` to a plain
`List` for a CALLER that wants to `for`-loop over clauses (TypeCheck's `synthSC` arm does; a `for`
loop inside the `Infer` monad can't be a LOCAL `let rec` there without joining `synthSC`'s own
mutual-recursion group, which breaks termination — #21's own finding). Plain structural recursion
(NOT part of any mutual block), so no termination hazard here. -/
def hClausesToList : HClauses → List (String × String × Surf)
  | .nil              => []
  | .cons op x b rest => (op, x, b) :: hClausesToList rest

/-- Desugar `.lettMulti binds body` to the IDENTICAL nested `.lett` chain a hand-written
`let x = e1 in let y = e2 in … in body` already produces — a ONE-LEVEL unfold (does NOT itself
recurse into `binds`'s/`body`'s own sub-trees; `eraseLettMulti` below is the FULL tree-wide pass
that ALSO uses this at the leaf). -/
def desugarLettMulti : LetBindings → Surf → Surf
  | .nil,          body => body
  | .cons n e rest, body => .lett n e (desugarLettMulti rest body)

#guard desugarLettMulti .nil (.var "body") == .var "body"
#guard desugarLettMulti (.cons "x" (.lit 3) .nil) (.var "x") == .lett "x" (.lit 3) (.var "x")
#guard desugarLettMulti (.cons "x" (.lit 3) (.cons "y" (.lit 4) .nil)) (.var "x")
  == .lett "x" (.lit 3) (.lett "y" (.lit 4) (.var "x"))

-- The FULL tree-wide erasure of lettMulti (issue #68).
mutual
def eraseLettMulti : Surf → Surf
  | .lit n       => .lit n
  | .var x       => .var x
  | .thunk e     => .thunk (eraseLettMulti e)
  | .force e     => .force (eraseLettMulti e)
  | .lett n a b  => .lett n (eraseLettMulti a) (eraseLettMulti b)
  | .lam n e     => .lam n (eraseLettMulti e)
  | .app a b     => .app (eraseLettMulti a) (eraseLettMulti b)
  | .raise e     => .raise (eraseLettMulti e)
  | .handle e    => .handle (eraseLettMulti e)
  | .getS        => .getS
  | .putS e      => .putS (eraseLettMulti e)
  | .stateS a b  => .stateS (eraseLettMulti a) (eraseLettMulti b)
  | .atomS e     => .atomS (eraseLettMulti e)
  | .newS e      => .newS (eraseLettMulti e)
  | .readS e     => .readS (eraseLettMulti e)
  | .writeS a b  => .writeS (eraseLettMulti a) (eraseLettMulti b)
  | .inlS e      => .inlS (eraseLettMulti e)
  | .inrS e      => .inrS (eraseLettMulti e)
  | .pairS a b   => .pairS (eraseLettMulti a) (eraseLettMulti b)
  | .matchS s lx e1 ry e2 => .matchS (eraseLettMulti s) lx (eraseLettMulti e1) ry (eraseLettMulti e2)
  | .splitS a b p body    => .splitS a b (eraseLettMulti p) (eraseLettMulti body)
  | .binopS op a b => .binopS op (eraseLettMulti a) (eraseLettMulti b)
  | .ifS c t e     => .ifS (eraseLettMulti c) (eraseLettMulti t) (eraseLettMulti e)
  | .annotS e t    => .annotS (eraseLettMulti e) t
  | .unitS         => .unitS
  | .foldS e       => .foldS (eraseLettMulti e)
  | .unfoldS e     => .unfoldS (eraseLettMulti e)
  | .matchD s arms => .matchD (eraseLettMulti s) (eraseLettMultiDArms arms)
  | .withCapS k i n b => .withCapS k (eraseLettMulti i) n (eraseLettMulti b)
  | .dotPerform r op .none      => .dotPerform (eraseLettMulti r) op .none
  | .dotPerform r op (.one a)   => .dotPerform (eraseLettMulti r) op (.one (eraseLettMulti a))
  | .dotPerform r op (.two a b) => .dotPerform (eraseLettMulti r) op (.two (eraseLettMulti a) (eraseLettMulti b))
  | .letRecS n t f b => .letRecS n t (eraseLettMulti f) (eraseLettMulti b)
  | .divMark e     => .divMark (eraseLettMulti e)
  | .lettMulti binds body => desugarLettMulti (eraseLettMultiBindings binds) (eraseLettMulti body)
  | .handleCustomS lbl n p? h cls body =>
      .handleCustomS lbl (eraseLettMulti n)
        (match p? with | .none => .none | .one p => .one (eraseLettMulti p) | .two a b => .two (eraseLettMulti a) (eraseLettMulti b))
        h (eraseLettMultiHClauses cls) (eraseLettMulti body)
def eraseLettMultiDArms : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest  => .cons c ps (eraseLettMulti b) (eraseLettMultiDArms rest)
def eraseLettMultiBindings : LetBindings → LetBindings
  | .nil            => .nil
  | .cons n e rest  => .cons n (eraseLettMulti e) (eraseLettMultiBindings rest)
def eraseLettMultiHClauses : HClauses → HClauses
  | .nil              => .nil
  | .cons op x b rest => .cons op x (eraseLettMulti b) (eraseLettMultiHClauses rest)
end

#guard eraseLettMulti (.lit 3) == .lit 3
#guard eraseLettMulti (.lettMulti (.cons "x" (.lit 3) (.cons "y" (.lit 4) .nil)) (.var "x"))
  == .lett "x" (.lit 3) (.lett "y" (.lit 4) (.var "x"))
-- a NESTED occurrence (inside a `fun` body, not at the tree root) is ALSO erased.
#guard eraseLettMulti (.lam "z" (.lettMulti (.cons "x" (.lit 3) (.cons "y" (.lit 4) .nil)) (.var "x")))
  == .lam "z" (.lett "x" (.lit 3) (.lett "y" (.lit 4) (.var "x")))
-- a plain single-binding `.lett` (never sugar) passes through UNCHANGED.
#guard eraseLettMulti (.lett "x" (.lit 3) (.var "x")) == .lett "x" (.lit 3) (.var "x")


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

/-- Map a surface cap-op name (`h.new`) to the kernel `OpId` (`newTVar`) — ADR-0070. The
state/exn ops are already the kernel names; the stm ops abbreviate. Unknown names pass through
(the checker rejects a label mismatch). -/
def capOpKernel : String → String
  | "new"   => "newTVar"
  | "read"  => "readTVar"
  | "write" => "writeTVar"
  | op      => op

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
  -- ── ADR-0069 ──
  | .unitS => .ok (.ret .vunit)
  | .foldS e => do                       -- μ intro; A-normalize a computation payload (the inlS idiom)
      match lowerV env e with
      | .ok v    => return .ret (.fold v)
      | .error _ => return .letC (← lowerC env e) (.ret (.fold (.vvar 0)))
  | .unfoldS e => do                     -- μ elim; same scrutinee idiom as `case`
      match lowerV env e with
      | .ok v    => return .unfold v
      | .error _ => return .letC (← lowerC env e) (.unfold (.vvar 0))
  | .matchD .. => .error "named match needs the typed path (data declarations, ADR-0069) — run via checkProg/runTyped"
  | .letRecS .. => .error "let rec needs the typed path (μ-encoded recursion, ADR-0073) — run via checkProg/runTyped"
  | .divMark e => lowerC env e   -- #46: Div is a pure TYPING marker (no runtime semantics) — erase it
  -- `.lettMulti` (issue #68) should NEVER reach `lowerC`: every entry point (`lower` below,
  -- `elabProg`) calls `eraseLettMulti` FIRST, resolving every occurrence (root or nested) to plain
  -- `.lett` chains before lowering/elaboration ever runs — matching `letRecS`/`matchD`'s own
  -- "needs the typed/pre-pass path" fail-loud convention immediately above. Calling `lowerC`
  -- recursively on the desugared term from INSIDE `lowerC`'s own match was tried first and
  -- rejected: Lean's structural-recursion checker can't see the desugared output as a subterm of
  -- the `.lettMulti` input, which pushed the WHOLE mutual group to well-founded recursion — that
  -- broke the file's `rfl`-based Stage-1b pinning examples (well-founded output doesn't reduce
  -- definitionally the way structural-recursion output does). Pre-erasing at the entry point
  -- keeps `lowerC` itself simple structural recursion, untouched.
  | .lettMulti .. => .error "unreachable: .lettMulti must be pre-erased by eraseLettMulti before lowering (issue #68)"
  -- ADR-0095 D1 (RULED) + WALL-1 fix (manager-ruled Option A, #21 s7probe): `handleCustomS` now
  -- carries a RESOLVED-LABEL slot (`Option Label`), filled by `elabS` before `lower` ever runs —
  -- `lowerC` stays a PURE function of the tree (no `ElabEnv` threading, unlike the rejected
  -- alternative of polluting a structural pass with elaboration state; the untyped
  -- `elaborateToComp` path also lacks a full `ElabEnv`, so that alternative would have been a
  -- dead end there too). `none` here means elaboration never ran (or the effect name never
  -- resolved) — a genuine PIPELINE gap, not a user error to guess through, hence the loud
  -- `.error` rather than a silent default label.
  --
  -- Builds `Handler.custom ℓ p clauses` (ADR-0087 finite rep) + installs it via `Comp.handle`,
  -- mirroring `withCapS "state"`'s A-normalization shape: the param-init `p?` (`none` for a
  -- param-less `Name`, desugared to CLOSED `.vunit` — the kernel's `Handler.custom` always
  -- carries a `p : Val`, ADR-0092's premise) is evaluated OUTSIDE the handler scope (it is the
  -- handler's PAYLOAD, not under the cap binder) exactly like `state`'s `s : S`. `body` (= `e`)
  -- lowers under the cap binder `h :: env` (ADR-0095's binding-gap ruling, reading (c) mechanics
  -- — `h` is in scope for `e` regardless of `e`'s textual position before `with Name as h { … }`
  -- in source). Each clause body lowers under TWO fresh binders, `arg :: "#param" :: env`
  -- (`HasClauses.cons`'s premise order: `opArg` at idx 0, `P` at idx 1) — `param` is NOT a
  -- user-visible identifier in `env`'s namespace (a clause referencing the ADR's `param` name
  -- resolves via a DEDICATED lookup, not `env`'s ordinary `lookup`, since `#param` is a sentinel
  -- like `lowerC`'s other internal binder names — `#s0`, `#anf…` — that the grammar cannot spell,
  -- so `param` the SURFACE identifier and `#param` the internal sentinel never collide; the
  -- surface→sentinel bridge is `lowerHClauses`'s own small env-prepend below, not a generic rename).
  | .handleCustomS .none _ _ _ _ _ =>
      .error "handleCustomS: unresolved effect label reaching lowering — elaboration must run first (ADR-0095 WALL-1 fix, #21 s7probe finding)"
  | .handleCustomS (some ℓ) _ p? h cls body => do
      let clausesC ← lowerHClauses env cls
      match p? with
      | .none => return .handle (.custom ℓ .vunit clausesC) (← lowerC (h :: env) body)
      | .one p0 =>
          match lowerV env p0 with
          | .ok v    => return .handle (.custom ℓ v clausesC) (← lowerC (h :: env) body)
          | .error _ => do
              let cp ← lowerC env p0
              let b  ← lowerC (h :: "#p0" :: env) body
              return .letC cp (.handle (.custom ℓ (.vvar 0) clausesC) b)
      | .two _ _ => .error "handleCustomS: param-init takes at most 1 argument"
  -- ── ADR-0070 (named capabilities) — `with` reuses the handler lowering with a USER name where the
  -- sentinel went; `h.op` is `perform (vvar h) op arg` (args A-normalized like the ambient ops). ──
  | .withCapS "state" init name body => do
      match lowerV env init with
      | .ok v    => return .handle (.state stateLabel v) (← lowerC (name :: env) body)
      | .error _ => do
          let ci ← lowerC env init
          let b  ← lowerC (name :: "#s0" :: env) body
          return .letC ci (.handle (.state stateLabel (.vvar 0)) b)
  | .withCapS "throws" _ name body => do
      return .handle (.throws exnLabel) (← lowerC (name :: env) body)
  | .withCapS "atomically" _ name body => do
      return .handle (.transaction stmLabel []) (← lowerC (name :: env) body)
  | .withCapS k _ _ _ => .error s!"with: unknown handler kind '{k}'"
  | .dotPerform recv op .none      => do return .perform (← lowerV env recv) (capOpKernel op) .vunit
  | .dotPerform recv op (.one a)   =>
      match lowerV env a with
      | .ok av   => do return .perform (← lowerV env recv) (capOpKernel op) av
      | .error _ => do
          let ca ← lowerC env a
          let rv ← lowerV ("#arg" :: env) recv     -- cap shifted past the arg binder
          return .letC ca (.perform rv (capOpKernel op) (.vvar 0))
  | .dotPerform recv op (.two r w) => do
      let rref ← lowerV env r
      match lowerV env w with
      | .ok wv   => do return .perform (← lowerV env recv) (capOpKernel op) (.pair rref wv)
      | .error _ => do
          let cw ← lowerC env w
          let rv ← lowerV ("#w" :: env) recv
          return .letC cw (.perform rv (capOpKernel op) (.pair (Val.shift rref) (.vvar 0)))

/-- ADR-0095 D1/#21 s7probe: lower a `handleCustomS` clause list to the kernel's `List (OpId ×
Comp)` (ADR-0087 finite rep). Each clause body lowers under `arg :: "#param" :: env` — the
`HasClauses.cons` binder order (`opArg` at idx 0, `P` at idx 1) — regardless of ITS OWN op's arity
(v1 is single-arg only, so `arg` is always exactly one name). -/
def lowerHClauses (env : List String) : HClauses → Except String (List (OpId × Comp))
  | .nil              => .ok []
  | .cons op x b rest => do
      let bc ← lowerC (x :: "#param" :: env) b
      let restC ← lowerHClauses env rest
      return (op, bc) :: restC

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
  | .unitS      => .ok .vunit
  | .foldS e    => do return .fold (← lowerV env e)   -- μ intro is a value former (ADR-0069)
  | .annotS e _ => lowerV env e          -- ascription erased; lower the inner value
  | _           => .error "expected a value (wrap a computation in braces)"
end

/-- Lower a closed surface program. `eraseLettMulti` FIRST (issue #68): resolves every `.lettMulti`
sugar marker — root or nested — to plain `.lett` chains before `lowerC` ever runs (see its own
`.lettMulti` arm's doc comment for why lowering can't handle the marker directly). A no-op on any
tree with no sugar in it (the overwhelmingly common case), so this adds no observable cost there. -/
def lower (e : Surf) : Except String Comp := lowerC [] (eraseLettMulti e)


/-! ## 3. Minimal parser `String → Except String Surf`

Hand-rolled tokenizer + recursive descent. Deliberately small: no spans, no
error recovery — a parse error is a `String`. The grammar is §1's block comment.

Tokenizer: WHITESPACE-INSENSITIVE (ADR-0071 ④) — punctuators and operators (`+ - * / < = |`
and the maximal-munch `== => ->`) self-separate, so `a+b`/`x=1`/`->Self` need no spaces; a
spaced program tokenizes identically. Identifiers/numbers/keywords are the remaining maximal runs. -/

/-- Scan a quoted literal body up to (not including) the unescaped closing `delim`, KEEPING escape
sequences RAW (`\n` stays the two chars backslash-n) for the parser to decode. `none` = unterminated
(ran off the end without a closing delimiter). Total — structural on the char list. (ADR-0074, #49) -/
def scanQuoted (delim : Char) : List Char → List Char → Option (String × List Char)
  | '\\' :: c :: rest, acc => scanQuoted delim rest (c :: '\\' :: acc)   -- keep an escape pair raw
  | d :: rest,         acc => if d == delim then some (String.ofList acc.reverse, rest)
                              else scanQuoted delim rest (d :: acc)
  | [],                _   => none

/-- Split a source string into tokens — WHITESPACE-INSENSITIVE (ADR-0071 ④). Punctuators
`(){}$!,;.` and the single-char operators `+ - * / < = |` are always their own token (no
surrounding space needed); the multi-char operators `== => ->` are matched by MAXIMAL MUNCH,
BEFORE their single-char prefixes (`==`/`=>` before `=`, `->` before `-`). A `--` runs a LINE
COMMENT: everything up to (not including) the next `\n`, or end-of-input, is dropped — no token
is emitted (comments are lexer-stripped, not preserved into the token stream; issue #62,
ruling: all three independent stranger-test victims reached for `--` unprompted, so the syntax
rides that pattern-match rather than picking a novel marker). `--` is matched BEFORE the bare
`-`/`->` arms (maximal munch again: two dashes beat one). Everything else is a maximal run of the
remaining chars (identifiers, numbers, keywords). A spaced program tokenizes IDENTICALLY to its
unspaced form: whitespace only ever separated tokens, and operators now self-separate (so `a+b`,
`x=1`, `->Self`, `a==b` no longer glue). `<-` is not a token in this grammar (`do`-bind uses `=`),
so `<` stays single-char; `:` stays space-delimited (not an operator the parser splits on). -/
def tokenize (s : String) : List String :=
  let punct := "(){}$!,;.+*/<|".toList     -- punctuators (ADR-0070 `.`) + always-split single-char operators
  -- FUEL-driven (not structural): string/char literal scanning consumes a multi-char span via
  -- `scanQuoted`, so recursion is on a suffix `scanQuoted` returns, not a `cs` sub-pattern. Fuel =
  -- length+1 ≥ steps (each step drops ≥1 char, decrements fuel by 1), so it never bites. (#49)
  let rec go (fuel : Nat) (cs : List Char) (cur : List Char) (acc : List String) : List String :=
    let flush (acc : List String) : List String :=
      if cur.isEmpty then acc else acc ++ [String.ofList cur.reverse]
    let emit (acc : List String) (t : String) : List String := (flush acc) ++ [t]
    -- drop chars up to (not incl.) the next '\n', or end-of-input — the comment body itself.
    let rec dropLine (fuel2 : Nat) (cs2 : List Char) : List Char :=
      match fuel2, cs2 with
      | 0, _ => cs2
      | _, [] => []
      | _, '\n' :: _ => cs2
      | f2 + 1, _ :: rest => dropLine f2 rest
    match fuel, cs with
    | 0, _ => flush acc
    | _, [] => flush acc
    | f + 1, '-' :: '-' :: rest => go f (dropLine f rest) [] (flush acc)   -- `--` line comment: dropped, no token
    | f + 1, '=' :: '=' :: rest => go f rest [] (emit acc "==")     -- maximal munch: `==` before `=`
    | f + 1, '=' :: '>' :: rest => go f rest [] (emit acc "=>")     --               `=>` before `=`
    | f + 1, '-' :: '>' :: rest => go f rest [] (emit acc "->")     --               `->` before `-`
    -- STRING / CHAR literals (ADR-0074): scan the whole quoted span as ONE token (spaces inside are
    -- kept), delimiters preserved so `pAtom` can tell it apart; unterminated ⟹ a lone-delim token it rejects.
    | f + 1, '"' :: rest =>
        match scanQuoted '"' rest [] with
        | some (raw, rest') => go f rest' [] (emit acc ("\"" ++ raw ++ "\""))
        | none              => flush acc ++ ["\""]
    | f + 1, '\'' :: rest =>
        match scanQuoted '\'' rest [] with
        | some (raw, rest') => go f rest' [] (emit acc ("'" ++ raw ++ "'"))
        | none              => flush acc ++ ["'"]
    | f + 1, c :: rest =>
      if c = ' ' || c = '\n' || c = '\t' || c = '\r' then
        go f rest [] (flush acc)
      else if c = '=' || c = '-' || punct.contains c then  -- single `=`/`-` (munch forms handled above), or a punct/op
        go f rest [] (emit acc (String.ofList [c]))
      else
        go f rest (c :: cur) acc
  go (s.length + 1) s.toList [] []

/-- A LOCATED parse error (ADR-0076 #2 — errors are VIEWS over the spanned IR): a message plus the
token list AT THE POINT OF FAILURE (its head is the offending token; `[]` = at/after end of input).
`rest` is always a SUFFIX of `tokenize src` (the parser only ever drops tokens from the front), so
`parseLocated` recovers the offending token's `Span` by index (`length - rest.length`). `parse`
ERASES this to a bare `String` (behaviour-preserving); the internal combinators thread it. -/
structure PErr where
  msg  : String
  rest : List String
  deriving Repr

/-- A bare message locates at end-of-input (`rest = []`). Lets the UNREACHABLE error sites (fuel
exhaustion, rule-arity) stay `.error "…"` unchanged — only REACHABLE structural errors attach the
current token list for a precise `line:col`. -/
instance : Coe String PErr := ⟨fun m => ⟨m, []⟩⟩

/-- Parser state = remaining token list. The parser is a function
`List String → Except PErr (α × List String)` — the error carries the failure position. -/
abbrev P (α : Type) := List String → Except PErr (α × List String)

def expect (tok : String) : P Unit
  | t :: ts => if t = tok then .ok ((), ts) else .error ⟨s!"expected '{tok}', got '{t}'", t :: ts⟩
  | []      => .error s!"expected '{tok}', got end of input"

/-- Is `s` a non-negative integer literal? -/
def isIntLit (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit

/-- Decode the backslash escapes bang string/char literals support: `\n \t \" \' \\` (ADR-0074).
An unknown `\x` passes the `x` through (permissive; a spec Non-Feature is silent, not an error). -/
def decodeEsc : List Char → List Char
  | '\\' :: 'n'  :: rest => '\n' :: decodeEsc rest
  | '\\' :: 't'  :: rest => '\t' :: decodeEsc rest
  | '\\' :: '"'  :: rest => '"'  :: decodeEsc rest
  | '\\' :: '\'' :: rest => '\'' :: decodeEsc rest
  | '\\' :: '\\' :: rest => '\\' :: decodeEsc rest
  | c :: rest            => c :: decodeEsc rest
  | []                   => []

/-- Desugar a decoded char list to the `Str` ctor chain (ADR-0074): `"" ⟹ SNil`, `c :: cs ⟹
SCons(Char <codepoint>, …)`. The ctors resolve against the injected `Char`/`Str` prelude (elabProg). -/
def strToSurf : List Char → Surf
  | []      => .var "SNil"
  | c :: cs => .app (.var "SCons") (.pairS (.app (.var "Char") (.lit (Int.ofNat c.toNat))) (strToSurf cs))

/-- Parse an identifier token (not a keyword/punctuator). Non-recursive. -/
def pIdent : P String
  | t :: ts =>
      if t = "let" || t = "fun" || t = "handle" || t = "raise"
          || t = "state" || t = "get" || t = "put"
          || t = "atomically" || t = "new" || t = "read" || t = "write"
          || t = "match" || t = "Left" || t = "Right" || t = "if" || t = "then" || t = "else"
          || t = "do" || t = ";"
          || t = "trait" || t = "impl" || t = "for" || t = "fn" || t = "law" || t = "data" || t = "|"
          || t = "effect"
          || t = "import" || t = "use" || t = "pub"
          || t = "as" || t = "." || t = "where"
          || t = "in" || t = "=" || t = "=>" || t = "->" || t = ","
          || t = "+" || t = "-" || t = "*" || t = "/" || t = "<" || t = "==" || t = ":"
          -- ADR-0095 D1 (RULED): `with` is now RESERVED — the `handle e with Name as h { … }`
          -- construct needs it to STOP `pApp`'s application-fold / `pOp`'s Pratt loop deterministically
          -- (confirmed live: without reserving it, `e with Net { … }` parsed as one giant application
          -- chain `e with Net {thunk}`, since a bare `with` fell through to `pAtom`'s `.var` catch-all
          -- and nothing marked it as a non-atom boundary — the SAME class of bug #26 fixed for
          -- `read`/`write`/`get`, generalized to a new keyword).
          || t = "with"
          -- #93 (ADR-0095 D5, RULED but never implemented until now): `resume` is RESERVED as a
          -- BINDER name (a clause-arg name, a `let`/`fun` name, …) so the future explicit
          -- `resume(w)` form (and the eventual multi-shot first-class `k`, Q22/Q27) slots in
          -- without colliding with a program that already used `resume` as an ordinary identifier.
          -- This is the BINDER half of D5's reservation — `pIdent` is where every other binder-name
          -- reservation already lives (`with`, the built-in ambient-op names); the EFFECT-OP-NAME
          -- half is a SEPARATE check in `buildEnv`'s `.effectD` case, since `pEffectMembers` parses
          -- an op name directly off the token stream, never through `pIdent`.
          || t = "resume" then
        .error ⟨s!"expected an identifier, got keyword '{t}'", t :: ts⟩
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
  | ts             => .error ⟨s!"malformed effect row at {ts}", ts⟩

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
-- Can `t` START a type atom? (⟹ a candidate type-application ARGUMENT after a data name.) Every
-- separator/operator token is NOT an atom start, so application stops at `*`/`+`/`->`/`)`/… — exactly
-- the tokens that continue an enclosing type or end it. A bare identifier (`a`, `List`), `Int`/`Unit`/…,
-- and `(` (a parenthesized arg, `List (Int * Int)`) all START an atom.
def isTyAtomStart : String → Bool
  | ")" | "}" | "{" | "," | ";" | "|" | "->" | "+" | "*" | "!" | "=" | "in" | "=>" | "where" => false
  | _ => true
def pTyAtom1 : Nat → P Ty                     -- ONE atom, no trailing application (args of an application)
  | 0,     _            => .error "type parser out of fuel"
  | _ + 1, "Int" :: ts  => .ok (.tInt, ts)
  | _ + 1, "Unit" :: ts => .ok (.tUnit, ts)
  | _ + 1, "Self" :: ts => .ok (.tSelf, ts)
  | f + 1, "Thunk" :: ts => do let (t, ts) ← pTyAtom1 f ts; .ok (.tThunk t, ts)
  | f + 1, "(" :: ts    => do
      let (t, ts) ← pTy f ts
      let (_, ts) ← expect ")" ts
      .ok (t, ts)
  | _ + 1, t :: ts      =>
      -- a bare identifier in type position = a declared data name (ADR-0069); resolved (or
      -- fail-louded) against the decl env at elaboration, so a typo is still an error — later.
      if isTyAtomStart t then .ok (.tName t, ts)
      else .error ⟨s!"expected a type, got '{t}'", t :: ts⟩
  | _ + 1, []           => .error "expected a type, got end of input"
-- Greedy trailing type ARGUMENTS after a data name (`List Int a` ⇒ args `[Int, a]`); each is ONE atom
-- (`List (Map k v)` needs parens), application tightest, stops at the first non-atom token.
def pTyArgs : Nat → P (List Ty)
  | 0,     ts => .ok ([], ts)   -- fuel out ⟹ no more args (the head already parsed; safe)
  | f + 1, ts => match ts with
    | t :: _ => if isTyAtomStart t then
                  do let (a, ts) ← pTyAtom1 f ts; let (rest, ts) ← pTyArgs f ts; .ok (a :: rest, ts)
                else .ok ([], ts)
    | []     => .ok ([], ts)
-- A type atom = one atom, then (if it is a bare NAME) any trailing atom args ⇒ a type APPLICATION.
def pTyAtom : Nat → P Ty
  | 0,     _  => .error "type parser out of fuel"
  | f + 1, ts => do
      let (a, ts) ← pTyAtom1 f ts
      match a with
      | .tName n => do
          let (args, ts) ← pTyArgs f ts
          match args with
          | []     => .ok (.tName n, ts)
          | [a]    => .ok (.tApp n (.one a), ts)
          | [a, b] => .ok (.tApp n (.two a b), ts)
          | _      => .error ⟨s!"type application '{n} …' takes ≤ 2 arguments in v1", ts⟩
      | _        => .ok (a, ts)
end

/-! The recursive-descent core is **fuel-driven total** recursion (not `partial`)
so the demo `example`s reduce under `rfl` — a `partial def` is opaque to the
kernel's definitional unfolding, which would block the green checks. Fuel bounds
the descent depth; `4·(tokenize output length) + 1` is a safe bound (see `parse`
— each nesting level is a 3-call descent that may consume only one token). The
inner application `loop` also consumes fuel (one per consumed atom). -/

/-- The reified infix-operator table (ADR-0071 ①): each operator token maps to `(leftBP, rightBP,
build)` — its binding powers and the `Surf` builder. Paper convention (higher BP binds tighter;
left-assoc ⟹ `leftBP < rightBP`, right-assoc ⟹ `leftBP > rightBP`). Application (juxtaposition,
tightest) has no token, so it is NOT here — it is `pOp`'s operand (`pApp`); `.`-postfix (tighter
still) stays in `pDotted`. `=>` builds the `#p`/`ifS` implication desugar the old `pImp` did.
Pure data, so `docs/reference` + the tree-sitter grammar can generate from this ONE root. -/
def opInfo : String → Option (Nat × Nat × (Surf → Surf → Surf))
  | "=>" => some (2, 1, fun l r => .lett "#p" l (.ifS (.var "#p") r (.binopS .eq (.lit 0) (.lit 0))))
  | "<"  => some (3, 4, fun l r => .binopS .lt  l r)
  | "==" => some (3, 4, fun l r => .binopS .eq  l r)
  | "+"  => some (5, 6, fun l r => .binopS .add l r)
  | "-"  => some (5, 6, fun l r => .binopS .sub l r)
  | "*"  => some (7, 8, fun l r => .binopS .mul l r)
  | "/"  => some (7, 8, fun l r => .binopS .div l r)
  | _    => none

/-! ### Reified keyword-led rules (ADR-0071 ②)

Per §3 of the paper (Cheng-Parreaux, ECOOP'26): a keyword-led construct is a `Rule` — a linear
sequence of `Choice`s (a `kw` to match-and-consume · a `refE`/`refA`/`refI` to parse a sub-kind)
plus a `build` that assembles the collected fragments into a `Surf`. ONE driver (`pRuleDrive`)
interprets any rule, so `pExpr`'s single-keyword arms retire into a table (`keywordRule`) the
fallthrough consults. Multi-keyword / delegating constructs (`let (a,b)=`, `with … as`, `match`,
`do`) stay bespoke — they don't fit a single-leading-keyword linear rule (see the fork note above
each retained arm).

The paper threads the builder as a curried continuation (`Ref`'s `f : (Tree, B) → A`); Lean needs
STRUCTURAL recursion for totality (the demo `#guard`s must reduce), and a continuation `k e` is not
a structural sub-term, so the builder is a `List Frag → …` over the collected fragments instead —
the same rule DATA, but the driver recurses on the `Choice` list (fuel-decrementing) rather than on
a closure. -/

/-- A fragment collected while driving a rule: a parsed sub-expression, or a bound identifier. -/
inductive Frag
  | expr : Surf → Frag      -- an expr/atom sub-parse
  | name : String → Frag    -- an identifier (a binder)

/-- One step of a rule: match a keyword, or parse a sub-kind (a full expression / an atom / an
identifier), or the OPTIONAL `as <ident>` binder. The three `ref` kinds mirror the sub-parsers the
retired bespoke arms called. `optAs` is the one OPTIONAL segment in the grammar (ADR-0072): the
`as <ident>` capability binder on `state`/`handle`/`atomically` — present ⟹ pushes a `.name` frag,
absent ⟹ pushes nothing. It is "optional" (present/absent), NOT alternation, so the rule stays
grammar-regular (the reified/bespoke line, ADR-0071 ②b). -/
inductive Choice
  | kw    : String → Choice
  | refE  : Choice          -- parse a full expression (pExpr)
  | refA  : Choice          -- parse an atom (pAtom)
  | refI  : Choice          -- parse an identifier (pIdent)
  | optAs : Choice          -- optionally match `as <ident>` — the named-capability binder (ADR-0072)

/-- A keyword-led parsing rule: a linear choice sequence + a builder over the collected frags.
`build` is total (`Except`); the choice sequence GUARANTEES the frag shape, so each rule's mismatch
branch is unreachable — it exists only because `List Frag` cannot be statically arity-constrained. -/
structure Rule where
  choices : List Choice
  build   : List Frag → Except String Surf

/-- The reified keyword rules (ADR-0071 ②). Keyed on the leading keyword; `pExpr`'s fallthrough
consults this table. Each `build` produces the EXACT `Surf` the retired bespoke arm produced, so the
`parsesTo` corpus is preserved. `let` is NOT here (issue #68): the multi-binding sugar (`let x = e1;
y = e2 in body`) needs a repeated-group grammar the fixed linear `Choice` sequence can't express, so
`let` — like `let (a,b) = …`, `let rec`, `match`, `do` — is a bespoke `pExpr` arm instead (its `n=1`
case, no `;`, subsumes the old single-binding form this table used to carry). -/
def keywordRule : String → Option Rule
  | "if"         => some ⟨[.kw "if", .refE, .kw "then", .refE, .kw "else", .refE],
      fun | [.expr c, .expr t, .expr e] => .ok (.ifS c t e) | _ => .error "if: rule arity"⟩
  -- `handle`/`atomically`/`state` carry the OPTIONAL `as <ident>` binder (ADR-0072): absent ⟹ the
  -- ambient form, present ⟹ the named-capability form (the same `withCapS` the old `with … as` emitted).
  | "handle"     => some ⟨[.kw "handle", .optAs, .refE],
      fun | [.expr e]          => .ok (.handle e)
          | [.name h, .expr e] => .ok (.withCapS "throws" .unitS h e)
          | _ => .error "handle: rule arity"⟩
  | "atomically" => some ⟨[.kw "atomically", .optAs, .refE],
      fun | [.expr e]          => .ok (.atomS e)
          | [.name h, .expr e] => .ok (.withCapS "atomically" .unitS h e)
          | _ => .error "atomically: rule arity"⟩
  -- `raise`/`put`/`new`/`read`/`write` are NO LONGER keyword rules: they are prefix-application forms
  -- parsed in `pApp` at application precedence (like the atom `get`), so their result feeds the Pratt
  -- operator chain — `read a - 30` parses as `(read a) - 30` (#26 part-2). A keyword rule returns
  -- BEFORE the operator loop, which is exactly the bug.
  | "state"      => some ⟨[.kw "state", .refA, .optAs, .kw "in", .refE],
      fun | [.expr e0, .expr e]          => .ok (.stateS e0 e)
          | [.expr e0, .name h, .expr e] => .ok (.withCapS "state" e0 h e)
          | _ => .error "state: rule arity"⟩
  | "fun"        => some ⟨[.kw "fun", .refI, .kw "=>", .refE],
      fun | [.name x, .expr b] => .ok (.lam x b) | _ => .error "fun: rule arity"⟩
  | _            => none

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
  | f + 1, "let" :: "rec" :: ts => do    -- recursion: let rec f : T = <fun> in <body> (ADR-0073; annotation required)
      let (name, ts) ← pIdent ts
      let (_, ts) ← expect ":" ts
      let (t, ts) ← pTy f ts
      let (_, ts) ← expect "=" ts
      let (e, ts) ← pExpr f ts
      let (_, ts) ← expect "in" ts
      let (body, ts) ← pExpr f ts
      .ok (.letRecS name t e body, ts)
  -- MULTI-BINDING LET SUGAR (issue #68): `let x = e1; y = e2 in body` desugars to the IDENTICAL
  -- nested `.lett` chain a hand-written `let x = e1 in let y = e2 in body` already produces — NO
  -- new `Surf` constructor, elaborate-away, sequential scoping (each binding sees the earlier
  -- ones; this is NOT Haskell's mutually-recursive let-block — bang's plain `let` stays
  -- non-recursive by convention, `let rec` is the only recursion marker, so sequential is the
  -- consistent reading). A BESPOKE arm (not `keywordRule`, whose `Rule`/`Choice` grammar is a
  -- FIXED linear sequence — it cannot express "0-or-more repeated group"), matching how `let (a,b)`/
  -- `let rec`/`match`/`do` already sit outside that table for the same reason. `n=1` binding (no
  -- `;`) is the base case of the same loop, so this ALSO retires `keywordRule`'s old single-binding
  -- `"let"` entry (ADR-0071 ②) — one construct, not two mechanisms for the same shape.
  | f + 1, "let" :: ts => do
      let (name, ts) ← pIdent ts
      let (_, ts) ← expect "=" ts
      let (e, ts) ← pExpr f ts
      let (bindings, ts) ← pLetBindings f ts
      let (_, ts) ← expect "in" ts
      let (body, ts) ← pExpr f ts
      -- `bindings = []` (no `;`) is the PLAIN single-binding form — was never sugar, stays a bare
      -- `.lett` exactly as before #68 (zero behavior change for the overwhelmingly common case,
      -- and the printer never needs to special-case it). Only a NON-EMPTY tail is the sugar marker.
      match bindings with
      | [] => .ok (.lett name e body, ts)
      | _  => .ok (.lettMulti (toLetBindings ((name, e) :: bindings)) body, ts)
  -- ADR-0095 D1 (RULED): `handle e with Name as h { op(x) => body, … }` (param-less) or
  -- `handle e with (Name init) as h { … }` (param-carrying). A BESPOKE arm (not `keywordRule`):
  -- the clause list is a repeated group, the same "0-or-more" shape `let`-multi/`match` already
  -- sit outside the linear `Choice` grammar for (ADR-0071 ②'s own documented boundary) —
  -- CONFIRMS the boundary generalizes to this construct too (an #21 s7probe finding that
  -- survived the syntax ruling unchanged, since it is syntax-INDEPENDENT).
  -- DISAMBIGUATION from plain `handle e` / `handle as h e` (keywordRule's existing entry,
  -- `[.kw "handle", .optAs, .refE]` — the OPTIONAL `as h` binder comes BEFORE `e` there): the
  -- SECOND token after `handle` decides it deterministically — `"as"` immediately means the
  -- built-in named-throws form (re-drive `keywordRule`, never re-implemented here); anything
  -- else means "parse an ordinary `e`", after which `with` (custom form) vs anything else
  -- (bare `handle e`, the built-in AMBIENT throws form) splits again. On ANY mismatch past
  -- `with`, this arm's `.error`s propagate (never silently re-drive a different-shape parse,
  -- per ADR-0046).
  | f + 1, "handle" :: "as" :: ts =>
      match keywordRule "handle" with
      | some r => pRuleDrive f r.build r.choices [] ("handle" :: "as" :: ts)
      | none   => pOp 0 f ("handle" :: "as" :: ts)
  | f + 1, "handle" :: ts0 => do
      let (e, ts) ← pExpr f ts0
      match ts with
      | "with" :: ts => do
          -- `Name` (param-less) or `(Name init)` (param-carrying).
          let ((nm, p?), ts) ← pHandlerName f ts
          let (_, ts) ← expect "as" ts
          let (h, ts) ← pIdent ts
          let (_, ts) ← expect "{" ts
          let (cls, ts) ← pHClauses f ts
          -- constructed tuple order matches `handleCustomS`'s DECLARED field order (label?,
          -- effName, paramInit?, h, cls, body) — NOT the surface's textual order (`e` prints
          -- FIRST; the constructor's own doc comment explains why).
          .ok (.handleCustomS none (.var nm) p? h cls e, ts)
      -- no `with`: this is the plain AMBIENT `handle e` form (unnamed throws-handler install) —
      -- re-drive `keywordRule`'s `handle` entry over the FULL original token stream so its own
      -- `refE` re-parses `e` (never guess by reusing the `e`/`ts` already parsed here: the two
      -- arms' `Surf` OUTPUT shapes differ — `.handle e` vs `.handleCustomS …` — so there is no
      -- shortcut that skips a full re-parse without risking a stale/wrong tree).
      | _ => match keywordRule "handle" with
        | some r => pRuleDrive f r.build r.choices [] ("handle" :: ts0)
        | none   => pOp 0 f ("handle" :: ts0)
  | f + 1, "match" :: ts => do           -- match s { arms } — anonymous sums (Left/Right → matchS)
      let (s, ts) ← pAtom f ts            -- OR named data ctors (→ matchD, elaborated later; ADR-0069)
      let (_, ts) ← expect "{" ts
      let (arms, ts) ← pArms f ts
      -- exactly the Left/Right pair (order-independent, 1 binder each) is the anonymous-sum
      -- form — it stays `matchS` so the UNTYPED path keeps working. Anything else is a named
      -- match, a typed-path (`Prog`) feature.
      match arms with
      | [("Left", [x1], b1), ("Right", [x2], b2)] => .ok (.matchS s x1 b1 x2 b2, ts)
      | [("Right", [x2], b2), ("Left", [x1], b1)] => .ok (.matchS s x1 b1 x2 b2, ts)
      | _ => .ok (.matchD s (toDArms arms), ts)
  | f + 1, "do" :: ts => do             -- do { stmt ; … ; result } → nested letC (issue #27)
      let (_, ts) ← expect "{" ts
      pDo f ts
  -- Named capabilities (ADR-0072): the `with … as` construct is GONE. `as <h>` is now an optional
  -- binder folded into the reified `state`/`handle`/`atomically` rules (`keywordRule` + `optAs`), so
  -- the named forms flow through the table below with no bespoke arm.
  -- ▼ single-keyword constructs (if/handle/atomically/raise/put/new/read/write/state/fun/let) are
  -- reified as `Rule`s (ADR-0071 ②): consult the table, else fall to the Pratt op loop (#4, #39, ①).
  | f + 1, ts =>
      match ts with
      | tok :: _ =>
          match keywordRule tok with
          | some r => pRuleDrive f r.build r.choices [] ts
          | none   => pOp 0 f ts
      | []       => pOp 0 f ts

/-- The REPEATED tail of the multi-binding `let` sugar (issue #68): while the next token is `;`,
consume it and parse one more `<ident> = <expr>` binding, accumulating in ORDER (later `foldr` in
the caller nests them correctly — see `pExpr`'s `let` arm). Stops (returns `[]`, `ts` unchanged) at
anything else — the caller's own `expect "in"` reports the right error if that's not actually `in`. -/
def pLetBindings : Nat → P (List (String × Surf))
  | 0,     _ => .error "parser out of fuel"
  | f + 1, ";" :: ts => do
      let (name, ts) ← pIdent ts
      let (_, ts) ← expect "=" ts
      let (e, ts) ← pExpr f ts
      let (rest, ts) ← pLetBindings f ts
      .ok ((name, e) :: rest, ts)
  | _ + 1, ts => .ok ([], ts)

/-- ONE Pratt binding-power loop over the reified operator table `opInfo` (ADR-0071 ①), replacing
the fixed `=>`/`<`·`==`/`+`·`-`/`*`·`/` precedence chain. `minBP` is the incoming binding power: an
operand is `pApp` (application — the tightest operator, juxtaposition), then while the next token is
an operator whose `leftBP > minBP`, consume it and recurse at its `rightBP` for the right operand.
Left-assoc ops have `leftBP < rightBP` (so a same-precedence sibling STOPS the recursion and folds
left); right-assoc ops have `leftBP > rightBP` (so the sibling RE-ENTERS and nests right). The
build-fn (from `opInfo`) produces the exact `Surf` the old chain did — `=>` is still the `#p`/`ifS`
desugar. Fuel-driven total (no `partial`), so the demo `#guard`s reduce. -/
def pOp : Nat → Nat → P Surf
  | _,     0,     _  => .error "parser out of fuel"
  | minBP, f + 1, ts => do
      let (lhs, ts) ← pApp f ts
      pOpLoop minBP f lhs ts

/-- The Pratt loop's tail: fold operators tighter than `minBP` onto `lhs`, left-to-right. -/
def pOpLoop : Nat → Nat → Surf → P Surf
  | _,     0,     acc, ts => .ok (acc, ts)
  | minBP, f + 1, acc, ts =>
    match ts with
    | op :: rest =>
      match opInfo op with
      | some (lbp, rbp, build) =>
          if lbp > minBP then do
            let (rhs, ts) ← pOp rbp f rest
            pOpLoop minBP f (build acc rhs) ts
          else .ok (acc, ts)
      | none => .ok (acc, ts)
    | [] => .ok (acc, ts)

/-- Interpret a reified keyword rule (ADR-0071 ②): walk the `Choice`s left-to-right, matching
keywords and collecting sub-parse frags, then `build` the result from the frags (in source order).
Fuel decrements per step exactly like the rest of the descent, so the mutual's uniform
fuel-measure covers it (total, no `partial`); sub-parses use the current fuel, mirroring the fuel
the retired bespoke arms passed. -/
def pRuleDrive : Nat → (List Frag → Except String Surf) → List Choice → List Frag → P Surf
  | 0,     _,     _,            _,   _  => .error "parser out of fuel"
  | _ + 1, build, [],           acc, ts => do
      let s ← (build acc.reverse).mapError (fun m => (⟨m, ts⟩ : PErr))   -- Rule.build stays `Except String`
      .ok (s, ts)
  | f + 1, build, .kw k :: cs,  acc, ts => do let (_, ts) ← expect k ts; pRuleDrive f build cs acc ts
  | f + 1, build, .refE :: cs,  acc, ts => do let (e, ts) ← pExpr f ts;  pRuleDrive f build cs (.expr e :: acc) ts
  | f + 1, build, .refA :: cs,  acc, ts => do let (a, ts) ← pAtom f ts;  pRuleDrive f build cs (.expr a :: acc) ts
  | f + 1, build, .refI :: cs,  acc, ts => do let (x, ts) ← pIdent ts;   pRuleDrive f build cs (.name x :: acc) ts
  -- optional `as <ident>` (ADR-0072): consume it and push a `.name` frag ONLY when the next token is
  -- `as` (a reserved keyword, so never a variable); otherwise skip, leaving the ambient form. Regular.
  | f + 1, build, .optAs :: cs, acc, ts =>
      match ts with
      | "as" :: rest => do let (h, ts) ← pIdent rest; pRuleDrive f build cs (.name h :: acc) ts
      | _            => pRuleDrive f build cs acc ts

/-- Parse an application chain: one or more DOTTED atoms, left-associated. The EFFECT OPS
(`raise`/`put`/`new`/`read`/`write`) are prefix-application forms parsed HERE, at application
precedence — like the nullary atom `get` — so their result feeds the Pratt operator chain (`pOp`).
That is what makes `read a - 30` parse as `(read a) - 30` and `write a (read a - 30)` accept the
operator (#26 part-2). Each op takes atom argument(s) (`pAtom`), matching the retired `keywordRule`
`.refA` shape, so the `parsesTo` corpus is preserved; a parenthesized computation `(get + 1)` is an
atom, so `put (get + 1)` still works. -/
def pApp : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, "raise" :: ts => do let (a, ts) ← pAtom f ts; pAppLoop f (.raise a) ts
  | f + 1, "put"   :: ts => do let (a, ts) ← pAtom f ts; pAppLoop f (.putS a)  ts
  | f + 1, "new"   :: ts => do let (a, ts) ← pAtom f ts; pAppLoop f (.newS a)  ts
  | f + 1, "read"  :: ts => do let (a, ts) ← pAtom f ts; pAppLoop f (.readS a) ts
  | f + 1, "write" :: ts => do let (r, ts) ← pAtom f ts; let (w, ts) ← pAtom f ts; pAppLoop f (.writeS r w) ts
  | f + 1, ts => do
      let (head, ts) ← pDotted f ts
      pAppLoop f head ts

/-- The left-association loop of `pApp`: keep eating dotted atoms while one can start. -/
def pAppLoop : Nat → Surf → P Surf
  | 0,      acc, ts => .ok (acc, ts)
  | f + 1, acc, ts =>
    match ts with
    | [] => .ok (acc, ts)
    | t :: _ =>
      if t = ")" || t = "}" || t = "in" || t = "=" || t = "=>" || t = "," || t = "->"
         || t = "+" || t = "-" || t = "*" || t = "/" || t = "<" || t = "==" || t = "."
         || t = "then" || t = "else" || t = ";" || t = "as" then
        .ok (acc, ts)
      else
        match pDotted f ts with
        | .ok (a, ts') => pAppLoop f (.app acc a) ts'
        | .error _     => .ok (acc, ts)

/-- An atom followed by zero+ method-performs `.op` / `.op(args)` (ADR-0070). Binds tighter than
application, so `h.get + 1` = `(h.get) + 1` and `f h.get` = `f (h.get)`. -/
def pDotted : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do let (a, ts) ← pAtom f ts; pDotLoop f a ts
def pDotLoop : Nat → Surf → P Surf
  | 0,      a, ts => .ok (a, ts)
  | f + 1, a, ts =>
    match ts with
    | "." :: op :: "(" :: r => do
        let (args, ts) ← pArgList f r
        let sa ← (match args with
          | []     => (.ok .none : Except PErr SurfArgs)
          | [x]    => .ok (.one x)
          | [x, y] => .ok (.two x y)
          | _      => .error ⟨s!"cap op '{op}' takes at most 2 arguments (got {args.length})", ts⟩)
        pDotLoop f (.dotPerform a op sa) ts
    | "." :: op :: r        => pDotLoop f (.dotPerform a op .none) r   -- nullary (h.get)
    | _                     => .ok (a, ts)
/-- A parenthesized, comma-separated cap-op argument list (after the opening `(`). -/
def pArgList : Nat → P (List Surf)
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ")" :: r => .ok ([], r)
  | f + 1, ts => do
      let (e, ts) ← pExpr f ts
      match ts with
      | "," :: r => do let (rest, ts) ← pArgList f r; .ok (e :: rest, ts)
      | ")" :: r => .ok ([e], r)
      | t :: r   => .error ⟨s!"expected ',' or ')' in a cap-op argument list, got '{t}'", t :: r⟩
      | []       => .error "unterminated cap-op argument list"

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
    | "}" :: r => .error ⟨"empty do block", "}" :: r⟩
    | x :: "=" :: rest => do             -- binding statement: x = e
        let (e, ts) ← pExpr f rest
        match ts with
        | ";" :: ts => do let (body, ts) ← pDo f ts; .ok (.lett x e body, ts)
        | "}" :: r  => .error ⟨"a do block must END in an expression, not a binding (x = e)", "}" :: r⟩
        | ts        => .error ⟨"expected ';' or '}' after a do-block statement", ts⟩
    | _ => do                            -- bare statement, or the final result
        let (e, ts) ← pExpr f ts
        match ts with
        | ";" :: ts => do let (body, ts) ← pDo f ts; .ok (.lett "#do" e body, ts)
        | "}" :: ts => .ok (e, ts)       -- the final statement is the block's value
        | ts        => .error ⟨"expected ';' or '}' after a do-block statement", ts⟩

/-- Parse one match arm `C -> e` · `C(x) -> e` · `C(x, y) -> e` (ctor name is `Left`/`Right` or
any identifier — named data ctors, ADR-0069; payload arity ≤ 2 in v1, the tuple-grammar bound). -/
def pArm : Nat → P (String × List String × Surf)
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do
      let (ctor, ts) ← (match ts with
        | "Left"  :: r => (.ok ("Left", r) : Except PErr (String × List String))
        | "Right" :: r => .ok ("Right", r)
        | ts           => pIdent ts)
      let (bs, ts) ← (match ts with
        | "(" :: r => do
            let (b1, ts) ← pIdent r
            (match ts with
             | ")" :: r2 => (.ok ([b1], r2) : Except PErr (List String × List String))
             | "," :: r2 => do
                 let (b2, ts) ← pIdent r2
                 let (_, ts) ← expect ")" ts
                 .ok ([b1, b2], ts)
             | t :: r => .error ⟨s!"expected ',' or ')' in a match-arm payload, got '{t}'", t :: r⟩
             | []     => .error "unterminated match-arm payload")
        | ts => (.ok ([], ts) : Except PErr (List String × List String)))
      let (_, ts) ← expect "->" ts
      let (body, ts) ← pExpr f ts
      .ok ((ctor, bs, body), ts)

/-- Parse match arms up to and including `}` (≥ 1 arm; `,` separators optional). -/
def pArms : Nat → P (List (String × List String × Surf))
  | 0,      _ => .error "parser out of fuel"
  | f + 1, ts => do
      let ((c, bs, b), ts) ← pArm f ts
      let ts := (match ts with | "," :: r => r | _ => ts)   -- optional separator/trailing comma
      match ts with
      | "}" :: r => .ok ([(c, bs, b)], r)
      | _        => do let (rest, ts) ← pArms f ts; .ok ((c, bs, b) :: rest, ts)

/-- Parse an atom (highest precedence). -/
def pAtom : Nat → P Surf
  | 0,      _ => .error "parser out of fuel"
  | _ + 1, "(" :: ")" :: ts => .ok (.unitS, ts)   -- `()` — the unit value literal (ADR-0069)
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
  -- UNARY MINUS (issue #64): `-e` desugars to `0 - e` — the SAME `.binopS .sub` node binary `-`
  -- already produces (opInfo `"-"`), so no new AST shape / lowering / typing rule is needed. Binds
  -- to ONE atom, exactly like `$`/`!` immediately above (so `-f 5` is `(-f) 5`, matching how `$f 5`
  -- is already `($f) 5` — confirmed by that pair's own runtime behavior, not assumed): tighter than
  -- application is the WRONG frame here, since `pAtom` feeds `pApp`'s loop the same way `$`/`!` do.
  | f + 1, "-" :: ts => do
      let (a, ts) ← pAtom f ts
      .ok (.binopS .sub (.lit 0) a, ts)
  | _ + 1, "get" :: ts => .ok (.getS, ts)
  | _ + 1, t :: ts =>
      let tc := t.toList
      -- STRING literal `"…"` → the `Str` ctor chain; CHAR literal `'c'` → `Char <codepoint>` (ADR-0074).
      if tc.length ≥ 2 && tc.head? == some '"' && tc.getLast? == some '"' then
        .ok (strToSurf (decodeEsc (tc.drop 1).dropLast), ts)
      else if tc.length ≥ 2 && tc.head? == some '\'' && tc.getLast? == some '\'' then
        match decodeEsc (tc.drop 1).dropLast with
        | [c] => .ok (.app (.var "Char") (.lit (Int.ofNat c.toNat)), ts)
        | _   => .error ⟨"char literal must be exactly one character (e.g. 'a')", t :: ts⟩
      else if isIntLit t then .ok (.lit (Int.ofNat (t.toNat!)), ts)
      else if t = "let" || t = "fun" || t = "handle" || t = "raise"
              || t = "state" || t = "put" || t = "match" || t = "if" || t = "then" || t = "else"
              || t = "atomically" || t = "new" || t = "read" || t = "write" || t = "do"
              || t = "trait" || t = "impl" || t = "for" || t = "fn" || t = "law" || t = "data" || t = "|"
              || t = "effect"
              || t = "import" || t = "use" || t = "pub"
              || t = "as" || t = "."
              || t = "+" || t = "-" || t = "*" || t = "/" || t = "<" || t = "=="
              || t = "in" || t = "=" || t = "=>" || t = "->" || t = "," || t = ";" || t = ")" || t = "}" || t = ":"
              -- ADR-0095 D1 (RULED): `with` reserved — see `pIdent`'s own arm for why.
              || t = "with"
              -- #93 (ADR-0095 D5): `resume` reserved — see `pIdent`'s own arm for why.
              || t = "resume" then
        .error ⟨s!"unexpected '{t}' where an atom was expected", t :: ts⟩
      else .ok (.var t, ts)
  | _ + 1, [] => .error "unexpected end of input where an atom was expected"

/-- ADR-0095 D1: the `with` clause's handler-name position — a bare `Name` (param-less) or a
parenthesized `(Name init)` (param-carrying). A genuine top-level function (not an inline-ascribed
`match … : P (…)`, which Lean's `do`-notation elaborator cannot place a monad hint on correctly
across TWO branches with different internal `do` blocks — tried first, rejected: "invalid `do`
notation, expected type is not a monad application"). -/
def pHandlerName : Nat → P (String × SurfArgs)
  | 0,     _ => .error "parser out of fuel"
  | f + 1, "(" :: ts => do
      let (nm, ts) ← pIdent ts
      let (p, ts) ← pAtom f ts
      let (_, ts) ← expect ")" ts
      .ok ((nm, .one p), ts)
  | _ + 1, ts => do
      let (nm, ts) ← pIdent ts
      .ok ((nm, .none), ts)

/-- ADR-0095 D1/D3 (RULED): one custom-handle clause `op(x) => body` (1-ary only — v1's
`EffectInfo` op sigs are 0/1-ary, matching `pArm`'s ctor-payload shape but WITHOUT the 2-ary
case: no declared op takes 2 args currently, D3's curry-desugar is future work — see `HClauses`'s
own doc comment). `=>` (not `->`) per D1's exact grammar — no ambiguity with `opInfo`'s `"=>"`
implication operator: this arm `expect`s the token directly (never routes through `pExpr`'s
Pratt loop for the arrow itself), matching `fun x => body`'s own `keywordRule` entry. -/
def pHClause : Nat → P (String × String × Surf)
  | 0,     _ => .error "parser out of fuel"
  | f + 1, ts => do
      let (op, ts) ← pIdent ts
      let (_, ts) ← expect "(" ts
      let (x, ts) ← pIdent ts
      let (_, ts) ← expect ")" ts
      let (_, ts) ← expect "=>" ts
      let (body, ts) ← pExpr f ts
      .ok ((op, x, body), ts)

/-- #21 s7probe: clause list up to and including `}` (≥ 1 clause; `,` separators optional, the
`pArms` precedent). -/
def pHClauses : Nat → P HClauses
  | 0,     _ => .error "parser out of fuel"
  | f + 1, ts => do
      let ((op, x, b), ts) ← pHClause f ts
      let ts := (match ts with | "," :: r => r | _ => ts)
      match ts with
      | "}" :: r => .ok (.cons op x b .nil, r)
      | _        => do let (rest, ts) ← pHClauses f ts; .ok (.cons op x b rest, ts)
end

/-- Parse a whole program: tokenize, parse one expression, require all tokens
consumed. Fuel = 6·(token count) + 1: each NESTING level costs a
`pExpr→pOp→pApp→pDotted→pAtom` descent plus the Pratt loop's `pOp→pOpLoop→pOp`
step (2 fuel per operator), yet a level may consume only one token (e.g.
`Left(7)`, `(a, b)`, deeply-nested parens), so the bound must be a multiple of
the token count, not `+1`. ×6 is a generous over-approximation (the Pratt loop
is SHALLOWER than the old 7-deep `pImp→pMulDiv` chain it replaced, so the bound
that worked for that chain still holds) — it never bites a well-formed program
(it only caps runaway recursion for totality).

`parseE` is the LOCATED internal: errors carry a `PErr` (message + failure position). `parse` erases
it to a bare `String` (behaviour-preserving); `parseLocated` (spans section) resolves it to a `Span`. -/
def parseE (src : String) : Except PErr Surf := do
  let toks := tokenize src
  let (e, rest) ← pExpr (toks.length * 6 + 1) toks
  if rest.isEmpty then .ok e
  else .error ⟨s!"trailing tokens after expression: {rest}", rest⟩

def parse (src : String) : Except String Surf := (parseE src).mapError (·.msg)

/-! ### Source spans (ADR-0076 #2 — the IR carries source truth; errors/LSP are VIEWS)

The FOUNDATION step (deliberately minimal): positions ENTER at the tokenizer, so a downstream view
can locate a token by `line:col`. Spans are FRONTEND metadata — ERASED before the kernel (the lowered
`Comp` carries none), so kernel/`HasCTy`/`Source.eval` are UNTOUCHED. `tokenize` itself is UNCHANGED
(parsing behaviour preserved, corpus tokenizes identically); `tokenizeSpanned` is the additive
position-carrying sibling, pinned equal to `tokenize` by a `#guard` (the SSoT test rung — drift is
caught at build). FULLY located parse/type errors (each error at its exact AST node) need spans
threaded through the parser `P`-type + a `Spanned` Surf carrier — the LATER, bigger tier (see the
FINDING at the bottom of this section). -/

/-- A source location: a half-open `[start, end)` range in 1-based `line`/`col`. Frontend/IR metadata.
PUBLIC so the `bang` CLI can print a located parse error's `line:col` (ADR-0076 #51/#52). -/
public structure Span where
  line    : Nat        -- 1-based start line
  col     : Nat        -- 1-based start column
  endLine : Nat
  endCol  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The human-facing `line:col` (start) — what an error view prints. -/
public def Span.loc (s : Span) : String := s!"{s.line}:{s.col}"

/-- Tokenize WITH source spans: the same tokens as `tokenize` (pinned by `#guard` below), each paired
with its `[start, end)` span. Positions thread through the identical scan — a newline resets column and
bumps line; `advStr` advances over a multi-char token's (or a scanned string literal's) source chars,
so spans stay correct across multi-line string literals. This is where source truth ENTERS the IR. -/
def tokenizeSpanned (s : String) : List (String × Span) :=
  let punct := "(){}$!,;.+*/<|".toList
  let adv    : (Nat × Nat) → Char → (Nat × Nat) := fun p c => if c = '\n' then (p.1 + 1, 1) else (p.1, p.2 + 1)
  let advStr : (Nat × Nat) → String → (Nat × Nat) := fun p str => str.toList.foldl adv p
  let rec go (fuel : Nat) (cs : List Char) (pos : Nat × Nat)
             (cur : List Char) (curStart : Nat × Nat)
             (acc : List (String × Span)) : List (String × Span) :=
    let flush (acc : List (String × Span)) : List (String × Span) :=
      if cur.isEmpty then acc
      else acc ++ [(String.ofList cur.reverse, ⟨curStart.1, curStart.2, pos.1, pos.2⟩)]
    let emit (acc : List (String × Span)) (t : String) (p0 p1 : Nat × Nat) : List (String × Span) :=
      (flush acc) ++ [(t, ⟨p0.1, p0.2, p1.1, p1.2⟩)]
    -- drop chars (advancing pos) up to (not incl.) the next '\n', or end-of-input.
    let rec dropLine (fuel2 : Nat) (cs2 : List Char) (pos2 : Nat × Nat) : List Char × (Nat × Nat) :=
      match fuel2, cs2 with
      | 0, _ => (cs2, pos2)
      | _, [] => ([], pos2)
      | _, '\n' :: _ => (cs2, pos2)
      | f2 + 1, c :: rest => dropLine f2 rest (adv pos2 c)
    match fuel, cs with
    | 0, _ => flush acc
    | _, [] => flush acc
    | f + 1, '-' :: '-' :: rest =>
        let (rest', pos') := dropLine f rest (adv (adv pos '-') '-')
        go f rest' pos' [] pos (flush acc)          -- `--` line comment: dropped, no token
    | f + 1, '=' :: '=' :: rest => let p1 := advStr pos "=="; go f rest p1 [] pos (emit acc "==" pos p1)
    | f + 1, '=' :: '>' :: rest => let p1 := advStr pos "=>"; go f rest p1 [] pos (emit acc "=>" pos p1)
    | f + 1, '-' :: '>' :: rest => let p1 := advStr pos "->"; go f rest p1 [] pos (emit acc "->" pos p1)
    | f + 1, '"' :: rest =>
        match scanQuoted '"' rest [] with
        | some (raw, rest') => let tok := "\"" ++ raw ++ "\""; let p1 := advStr pos tok
                               go f rest' p1 [] pos (emit acc tok pos p1)
        | none              => flush acc ++ [("\"", ⟨pos.1, pos.2, pos.1, pos.2 + 1⟩)]
    | f + 1, '\'' :: rest =>
        match scanQuoted '\'' rest [] with
        | some (raw, rest') => let tok := "'" ++ raw ++ "'"; let p1 := advStr pos tok
                               go f rest' p1 [] pos (emit acc tok pos p1)
        | none              => flush acc ++ [("'", ⟨pos.1, pos.2, pos.1, pos.2 + 1⟩)]
    | f + 1, c :: rest =>
      let p1 := adv pos c
      if c = ' ' || c = '\n' || c = '\t' || c = '\r' then
        go f rest p1 [] pos (flush acc)
      else if c = '=' || c = '-' || punct.contains c then
        go f rest p1 [] pos (emit acc (String.ofList [c]) pos p1)
      else
        go f rest p1 (c :: cur) (if cur.isEmpty then pos else curStart) acc
  go (s.length + 1) s.toList (1, 1) [] (1, 1) []

/-- VIEW: locate the FIRST token equal to `name`, returning its span. -/
def locateToken (src name : String) : Option Span :=
  (tokenizeSpanned src).find? (fun p => p.1 == name) |>.map (·.2)

/-- VIEW (the first located error): run parse→lower; on an unbound-variable error, pair the message
with the variable's source span. Demonstrates errors-as-a-view over the spanned IR — the message is
DATA, the span LOCATES it. (Full located errors — every parse/type error at its node — are the parser-
threading tier; this shows the pattern on the one error that already names its identifier.) -/
def unboundLocated (src name : String) : Option (String × Span) :=
  match parse src >>= lower with
  | .error m => (locateToken src name).map (fun sp => (m, sp))
  | .ok _    => none

/-- VIEW (post-hoc located TYPE errors, issue #52 Stage B): the generalization of `unboundLocated` for
the `bang eval` type/elab error path. Many checker/elaborator messages NAME the offending construct —
a bare variable (`unbound variable x`) or a single-quoted name (`unknown type name 'Foo'`, `constructor
'Cons' expects …`, `no impl provides '+' for …`, `let-binding 'f': …`). This resolves that name to its
source `Span` AFTER the fact via `locateToken`, WITHOUT annotating `Surf` (the per-node span tier — every
mismatch at its exact node + LSP hover — stays deferred to the AST-annotation build). Extraction: the
first single-quoted token if present, else the identifier after `unbound variable `. It locates the FIRST
occurrence — exact for an unbound variable (never a binder site) and a good approximation elsewhere; a
nested `let-binding 'f': <inner>` points at the outer binding `f`. Returns `none` (→ a plain, un-located
message) when the message names no locatable token (e.g. `value type mismatch`) — those are the deferred
per-node tier. -/
public def locateInMsg (src msg : String) : Option Span :=
  let candidate : Option String :=
    match msg.splitOn "'" with
    | _ :: name :: _ :: _ => some name                       -- first single-quoted token
    | _ => if "unbound variable ".isPrefixOf msg
           then some (msg.drop "unbound variable ".length).toString   -- the bare unbound identifier
           else none
  candidate.bind (locateToken src)

-- POST-HOC located TYPE errors (issue #52 Stage B): the name a message carries resolves to its span.
#guard (locateInMsg "let x = 3 in bar" "unbound variable bar").map (·.loc) == some "1:14"
#guard (locateInMsg "match Nope(0) { Nope(a) -> a }" "unknown constructor 'Nope' in match").map (·.loc) == some "1:7"
#guard (locateInMsg "1 + Left(0)" "no impl provides '+' for Left").map (·.loc) == some "1:3"
-- a nested let-binding error points at the OUTER binding (the first quoted name).
#guard (locateInMsg "let f = g in f" "let-binding 'f': unbound variable g").map (·.loc) == some "1:5"
-- a message naming NO locatable token stays un-located (→ a plain message; the deferred per-node tier).
#guard (locateInMsg "let x = 3 in $x" "value type mismatch") == none

/-- Resolve a `PErr.rest` (the token list at failure) to a source `Span`. `rest` is a SUFFIX of
`tokenize src`, so its head sits at index `length - rest.length`; the same index into
`tokenizeSpanned` (same tokens, pinned by `#guard`) gives the offending token's span. `rest = []`
(at/after end of input) locates a zero-width span at the position just past the last token. -/
def spanOfRest (src : String) (rest : List String) : Option Span :=
  let toks := tokenizeSpanned src
  match rest with
  | []     => toks.getLast?.map (fun p => let e := p.2; ⟨e.endLine, e.endCol, e.endLine, e.endCol⟩)
  | _ :: _ => toks[toks.length - rest.length]?.map (·.2)

/-- VIEW: the FULLY-located parse (ADR-0076 #2). Runs the internal `parseE` (which threads `PErr`
through the ~30 combinators) and resolves each parse error to `(message, Span)` — every parse error at
its exact token. `parse`'s bare-`String` result is `parseLocated` with the span dropped; both share
one code path (SSoT). This is the substrate #51 (a stricter `bang eval` gate) needs to make a parse
error a helpful `line:col`, not a wall. -/
def parseLocated (src : String) : Except (String × Option Span) Surf :=
  (parseE src).mapError (fun e => (e.msg, spanOfRest src e.rest))

-- CONSISTENCY (the SSoT test rung): `tokenizeSpanned` emits exactly `tokenize`'s tokens.
#guard (tokenizeSpanned "let x = 3 in bar").map (·.1) == tokenize "let x = 3 in bar"
#guard (tokenizeSpanned "fun x => x+1").map (·.1) == tokenize "fun x => x+1"
#guard (tokenizeSpanned "match s { Left(x)->x, Right(y)->y }").map (·.1) == tokenize "match s { Left(x)->x, Right(y)->y }"
-- POSITIONS: a token's line:col is correct, including across a newline and past a multi-char operator.
#guard (locateToken "let x = 3 in bar" "bar").map (·.loc) == some "1:14"
#guard (locateToken "let x =\n  y in y" "y").map (·.loc) == some "2:3"
#guard (locateToken "a == b" "b").map (·.loc) == some "1:6"
-- LOCATED ERROR (the view): an unbound variable reports its position.
#guard (unboundLocated "let x = 3 in bar" "bar").map (fun p => p.2.loc) == some "1:14"
#guard (match unboundLocated "let x = 3 in bar" "bar" with | some (m, _) => (m.splitOn "bar").length > 1 | none => false)
-- LOCATED PARSE ERRORS (issue #52, Stage A): a parse error reports the offending token's `line:col`.
-- `expect` mismatch — the missing `=` in `let x <3> in x`: the `3` at col 7 is where a `=` was wanted.
#guard (match parseLocated "let x 3 in x" with | .error (_, some sp) => sp.loc == "1:7" | _ => false)
-- `pAtom` unexpected token — the stray `)` at col 5 in `1 + )` (an atom was expected there).
#guard (match parseLocated "1 + )" with | .error (_, some sp) => sp.loc == "1:5" | _ => false)
-- located across a NEWLINE: the reserved `in` used as an atom on line 2, col 3.
#guard (match parseLocated "3 +\n  in" with | .error (_, some sp) => sp.loc == "2:3" | _ => false)
-- a WELL-FORMED program is `.ok` through the located path too (parse behaviour preserved).
#guard (match parseLocated "let x = 3 in x" with | .ok _ => true | _ => false)
-- the message is preserved verbatim (the located view only ADDS a span; `parse` erases it).
#guard (match parseLocated "1 + )", parse "1 + )" with
        | .error (m, _), .error m' => m == m' | _, _ => false)

-- LINE COMMENTS (issue #62): `--` runs to end-of-line and is DROPPED — no token, no span.
#guard tokenize "let x = 3 -- the answer\nin x" == tokenize "let x = 3 \nin x"
#guard tokenize "-- a whole-line comment\nlet x = 3 in x" == tokenize "let x = 3 in x"
#guard tokenize "let x = 3 in x -- trailing, no newline after" == tokenize "let x = 3 in x "
-- a comment does not need a following newline to close (end-of-input closes it too).
#guard tokenize "let x = 3 in x --" == tokenize "let x = 3 in x "
-- `--` beats the single `-` / `->` munch forms (maximal munch: two dashes before one).
#guard tokenize "x -- >x" == tokenize "x "
#guard tokenize "1 -> -- not an arrow, a comment\n2" == tokenize "1 -> \n2"
-- `tokenizeSpanned` drops the SAME tokens (no span for the comment) — the SSoT pin extends.
#guard (tokenizeSpanned "let x = 3 -- note\nin x").map (·.1) == tokenize "let x = 3 -- note\nin x"
-- a token AFTER a comment reports its position on the FOLLOWING line, not inside the comment.
#guard (locateToken "let x = 3 -- note\nin x" "in").map (·.loc) == some "2:1"
-- a token on the SAME line, after a same-line comment closed by end-of-input, is unreachable
-- (the comment eats the rest of the line) — but a token on a line the comment does NOT touch
-- still locates correctly, showing comments don't perturb prior positions.
#guard (locateToken "let x = 3\n-- a comment line\nin x" "in").map (·.loc) == some "3:1"
-- METAMORPHIC (fmt-sanity #62): a commented program parses to the IDENTICAL `Surf` as its
-- uncommented twin — `--` is purely a lexical no-op on the parse result (and hence, since
-- `lower` is a pure function of `Surf`, on meaning too). `Comp` has no `BEq`, so the check
-- stops at the `Surf` the tokens elaborate to — the load-bearing rung for a lexer change.
#guard parse "let x = 3 -- three\nin x" == parse "let x = 3 \nin x"
#guard parse "-- leading comment\nlet f = fun x => x in f 1 -- trailing" == parse "\nlet f = fun x => x in f 1 "

/-! ### Declarations — `trait` / `impl` (issue #24 piece 1; ADR-0040 §5, ADR-0068)

A PROGRAM is a declaration prelude + a body expression (`Prog`), parsed by `parseProg`. The decl
forms are DATA consumed by the type-directed elaborator (the next unit) — nothing here changes the
untyped `parse → lower → eval` path. Grammar (Rust-ish, ADR-0040 §5):

    trait Add { fn add(a, b) -> Int ; law comm(a, b): add a b == add b a }
    impl Add for (Int * Int) { fn add(p, q) = p }
    <body expression>

v1 scope (ADR-0068): no trait hierarchy in source syntax; law bodies are Bool-valued expressions
(equations via `==`); impl target types are STRUCTURAL (`pTy`). Member separators `;` are optional
(the member keywords delimit, same convention as `match`'s optional comma). -/

/-- A trait operation SIGNATURE. Two surface forms, one record:
    · `fn add(a, b) -> Int` — params-all-`Self` (bite-2): `params` names them, `retTy` is the result,
      `methodTy` = `Self → … → retTy` (built by `selfArrows`).
    · `fmap : (a → b) → f a → f b` — a FULL method type (HKT, ADR-0082): `params = []`, `methodTy` is the
      parsed type, `retTy` its final result (`peelArrows`). The impl's `fn`-def supplies the param NAMES. -/
structure OpSig where
  name     : String
  params   : List String
  retTy    : Ty
  methodTy : Ty
  deriving Repr, Inhabited, DecidableEq

/-- `Self → Self → … → r` with `n` `Self` domains — the full type of a bite-2 params-all-`Self` op. -/
def selfArrows : Nat → Ty → Ty
  | 0,     r => r
  | n + 1, r => .tArr .tSelf (selfArrows n r)

/-- Peel every leading arrow, returning the final result type (`(a→b) → f a → f b` ↦ `f b`). -/
def peelArrows : Ty → Ty
  | .tArr _ b => peelArrows b
  | t         => t

/-- A trait LAW: `law comm(a, b): add a b == add b a`. `params` are the universally-quantified
variables; `body` is a Bool-valued expression over them + the trait's ops. Pure syntax here —
discharge (the ADR-0068 tested-rung elaboration) is the elaborator's job. -/
structure LawDecl where
  name   : String
  params : List String
  body   : Surf
  deriving Repr, Inhabited, DecidableEq

/-- An impl operation DEFINITION: `fn add(p, q) = e`. -/
structure OpDef where
  name   : String
  params : List String
  body   : Surf
  deriving Repr, Inhabited, DecidableEq

/-- A top-level declaration: a trait (ops + laws), an impl (op definitions for a structural
target type), a data type (named constructors over sums·products·μ, ADR-0069), or a user EFFECT
(ADR-0092 D1/D2 — a named interface of ops, each `name : ArgTy -> ResTy`; the elaborator allocates
its label and builds the program-derived `EffSig` instance, no kernel change). -/
inductive Decl where
  | traitD : String → List String → List OpSig → List LawDecl → Decl   -- trait N ā { fn … ; law … } (ā = HK trait params, [] = Self-only bite-2 trait)
  | implD  : String → Ty → List OpDef → Decl             -- impl N for τ { fn … }
  | dataD  : String → List String → List (String × List Ty) → Decl  -- data N ā = C₀ | C₁(T, …) | …  (ā = type params, [] = monomorphic; ADR-0069 generic)
  | fnD    : String → List String → Ty → String → String → Surf → Decl
    -- `fn name(params) : declaredTy where Trait tyVar = body` — a BOUNDED generic function
    -- (`fold : Monoid a => List a -> a`); monomorphized per concrete use (bite-2, ADR-0080).
  | effectD : String → List (String × Ty) → Decl
    -- `effect N { op1 : ArgTy -> ResTy, op2 : ResTy2, … }` (ADR-0092 D1) — a NAMED interface; each
    -- op's declared `Ty` is EITHER a bare result type (0-ary, `Unit` is Rust-`fn()`'s analogue —
    -- v1 requires an explicit arrow for any op taking an argument, no 0-ary sugar beyond a bare
    -- type) or a single `ArgTy -> ResTy` arrow (v1 monomorphic single-arg ops, matching the
    -- ADR-0085 D4 sketch `read : Int -> Str`). Multi-arg ops are OUT of v1 scope (not sketched by
    -- the ADR; a later bite can generalize the same way `capOpSig`'s ≤2-arity does for built-ins).
  | letD    : String → Option Ty → Surf → Decl
    -- `let name = expr` or `let name : Ty = expr` (NO trailing `in`) — a top-level PLAIN BINDING
    -- (ADR-0093 D5 operator ruling, 2026-07-09: the GENERAL form, not a main-only special case).
    -- The type ascription is OPTIONAL on plain `let` (ruling point (c) — required on `let rec`
    -- exactly as at expression level, ADR-0073). Disambiguated from the script-mode `let name =
    -- expr in body` by the ABSENCE of `in` after `expr` — deterministic lookahead (`isLetDecl`),
    -- never a guess (ADR-0046). Desugars at `Prog`-assembly time (`foldLetDecls`) to nested
    -- `Surf.lett`s wrapping the body (the ascription, when present, becomes an `annotS` around the
    -- bound expression — mirroring how an expression-level `(e : T)` ascription already works) —
    -- the SAME "wrap the body in a let" idiom `wrapFnSrcs`/`wrapGenericFns`/`mergeModules`'s
    -- `use`-hoist already use, so this is not a new mechanism, just its first SURFACE-visible
    -- (parseable, `pub`-able, formattable) use.
  | letRecD : String → Ty → Surf → Decl
    -- `let rec name : T = expr` (NO trailing `in`) — the recursive sibling, mirroring `letRecS`'s
    -- shape (ADR-0073's mandatory type annotation) at decl scope. `main` is now literally `let main
    -- = <body>` or `let rec main : T = <body>` — no special-cased entry-point form (D5, as ruled).
  deriving Repr, Inhabited, DecidableEq

/-- A declaration's NAME, for `pub`-set membership and module qualification (ADR-0093 D2/D3/D4) —
the single place that knows how to project a name out of every `Decl` variant, so the qualifier and
the visibility checker share one source of truth rather than re-deriving it. -/
def Decl.name : Decl → String
  | .traitD n _ _ _   => n
  | .implD n _ _      => n     -- an impl's "name" is its trait name (ADR-0093 doesn't export impls
                                -- independently — `pub impl` is accepted but the trait/data it's FOR
                                -- carries the real export surface; kept here only so `pub` parses
                                -- uniformly across every decl keyword, per the ADR's decl-prefix grammar)
  | .dataD n _ _       => n
  | .fnD n _ _ _ _ _   => n
  | .effectD n _       => n
  | .letD n _ _        => n
  | .letRecD n _ _     => n

/-- One `import` line: `import tokenizer` — brings `tokenizer` into scope as a qualifier prefix
(`tokenizer.lex`), no names hoisted unqualified. `modName` is the bare stem (no `.bang`, no path) —
resolution (same-dir-then-root, ADR-0093 D1) is Main.lean's job, not the parser's. -/
structure ImportDecl where
  modName : String
  deriving Repr, Inhabited, DecidableEq

/-- One `use` line: `use tokenizer (lex, Token)` — hoists exactly the named decls of `tokenizer`
into UNQUALIFIED scope (ADR-0093 D2; no glob form exists). `names` is the explicit list; a `data`
name in `names` brings its constructors along (D2's "ctors travel with their type"). -/
structure UseDecl where
  modName : String
  names   : List String
  deriving Repr, Inhabited, DecidableEq

/-- A whole program: the declaration prelude + the body expression (ADR-0068 decision 3), now with
a file's `import`/`use` header (ADR-0093 D1/D2) and the set of decl-names marked `pub` (D3). `pubNames`
is a flat set rather than a per-`Decl` field so every EXISTING `Decl` consumer (36 sites across
TypeCheck/Format/Surface as of ADR-0093) stays byte-identical — visibility is a property of the
PROGRAM's header, not the declaration's shape, matching how `pub` reads in source (a prefix token
consumed before the ordinary decl parse, not a new decl variant). -/
structure Prog where
  imports  : List ImportDecl := []
  uses     : List UseDecl    := []
  pubNames : List String     := []
  decls    : List Decl
  body     : Surf
  isLibrary : Bool := false
    -- `true` ⟺ no trailing body expression was present (D5's third case) — `body` then carries the
    -- UNOBSERVABLE `.lit 0` placeholder. Needed so `showProg` (Format.lean) can tell a genuine
    -- library file apart from a SCRIPT-mode program whose real body happens to BE `.lit 0` — without
    -- this, printing the placeholder unconditionally can round-trip to a DIFFERENT program when a
    -- top-level `let`'s bound expression is a bare atom (`let main = 42`, followed by the printed
    -- placeholder `0`, re-parses `42 0` as an APPLICATION — the same literal-adjacency ambiguity
    -- the `fn`-body corpus already works around, but here it strikes the FORMATTER's own output).
  deriving Repr, Inhabited, DecidableEq

/-- The comma-separated tail of a parameter list, up to and including `)`. -/
def pParamsLoop : Nat → P (List String)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts => do
      let (x, ts) ← pIdent ts
      match ts with
      | "," :: ts => do let (rest, ts) ← pParamsLoop f ts; .ok (x :: rest, ts)
      | ")" :: ts => .ok ([x], ts)
      | t :: r    => .error ⟨s!"expected ',' or ')' in a parameter list, got '{t}'", t :: r⟩
      | []        => .error "expected ',' or ')' in a parameter list, got end of input"

/-- A parenthesized parameter list `( x , y , … )` (`()` = a nullary op, e.g. `fn empty()`). -/
def pParams : Nat → P (List String)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts => do
      let (_, ts) ← expect "(" ts
      match ts with
      | ")" :: ts => .ok ([], ts)          -- nullary: `empty()` (a value op — Monoid's identity, #55)
      | _         => pParamsLoop f ts

/-- Trait members, up to and including `}`: `fn name(params) -> T` signatures and
`law name(params): e` laws, in any order. -/
def pTraitMembers : Nat → P (List OpSig × List LawDecl)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts =>
    match ts with
    | "}" :: ts => .ok (([], []), ts)
    | ";" :: ts => pTraitMembers f ts
    | "," :: ts => pTraitMembers f ts                              -- HKT: comma-separated method sigs (`pure : …, bind : …`)
    | "fn" :: ts => do
        let (n, ts) ← pIdent ts
        let (ps, ts) ← pParams f ts
        let (_, ts) ← expect "->" ts
        let (t, ts) ← pTy f ts
        let ((ops, laws), ts) ← pTraitMembers f ts
        .ok ((⟨n, ps, t, selfArrows ps.length t⟩ :: ops, laws), ts)   -- params-all-Self (bite-2)
    | "law" :: ts => do
        let (n, ts) ← pIdent ts
        let (ps, ts) ← pParams f ts
        let (_, ts) ← expect ":" ts
        let (b, ts) ← pExpr f ts
        let ((ops, laws), ts) ← pTraitMembers f ts
        .ok ((ops, ⟨n, ps, b⟩ :: laws), ts)
    | n :: ":" :: ts => do                                         -- HKT (ADR-0082): `fmap : (a→b) → f a → f b`
        let (t, ts) ← pTy f ts
        let ((ops, laws), ts) ← pTraitMembers f ts
        .ok ((⟨n, [], peelArrows t, t⟩ :: ops, laws), ts)
    | t :: r => .error ⟨s!"expected 'fn', 'law', a `name :` signature, or '}' in a trait body, got '{t}'", t :: r⟩
    | []     => .error "unterminated trait body"

/-- Impl members, up to and including `}`: `fn name(params) = e` definitions. -/
def pImplMembers : Nat → P (List OpDef)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts =>
    match ts with
    | "}" :: ts => .ok ([], ts)
    | ";" :: ts => pImplMembers f ts
    | "," :: ts => pImplMembers f ts                              -- HKT: comma-separated impl defs (`fn pure … , fn bind …`)
    | "fn" :: ts => do
        let (n, ts) ← pIdent ts
        let (ps, ts) ← pParams f ts
        let (_, ts) ← expect "=" ts
        let (b, ts) ← pExpr f ts
        let (rest, ts) ← pImplMembers f ts
        .ok (⟨n, ps, b⟩ :: rest, ts)
    | t :: r => .error ⟨s!"expected 'fn' or '}' in an impl body, got '{t}'", t :: r⟩
    | []     => .error "unterminated impl body"

/-- Effect members, up to and including `}`: `name : Ty` signatures, comma- or `;`-separated
(ADR-0092 D1) — the SAME `n : T` shape `pTraitMembers`'s HKT arm already parses, reused verbatim
(one construct per problem: a signature list is a signature list). Duplicate op NAMES within one
`effect` block are a parse-time LOUD error (ADR-0046) — caught here, before elaboration ever sees
them, so the error names the effect immediately rather than surfacing later as a silent overwrite
in the elaborator's op table. -/
def pEffectMembers : Nat → P (List (String × Ty))
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts =>
    match ts with
    | "}" :: ts => .ok ([], ts)
    | ";" :: ts => pEffectMembers f ts
    | "," :: ts => pEffectMembers f ts
    | n :: ":" :: ts => do
        let (t, ts) ← pTy f ts
        let (rest, ts) ← pEffectMembers f ts
        if rest.any (fun (n', _) => n' == n) then
          .error ⟨s!"effect: duplicate operation '{n}'", ts⟩
        else .ok ((n, t) :: rest, ts)
    | t :: r => .error ⟨s!"expected a `name : Ty` operation signature or '}' in an effect body, got '{t}'", t :: r⟩
    | []     => .error "unterminated effect body"

/-- The comma-separated payload types of a constructor, up to and including `)`. -/
def pCtorTysLoop : Nat → P (List Ty)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts => do
      let (t, ts) ← pTy f ts
      match ts with
      | "," :: r => do let (rest, ts) ← pCtorTysLoop f r; .ok (t :: rest, ts)
      | ")" :: r => .ok ([t], r)
      | t' :: r  => .error ⟨s!"expected ',' or ')' in a constructor payload, got '{t'}'", t' :: r⟩
      | []       => .error "unterminated constructor payload"

/-- One data constructor: `Name` (payload `Unit`) or `Name(T, …)` (arity ≤ 2 in v1). -/
def pCtor : Nat → P (String × List Ty)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts => do
      let (n, ts) ← pIdent ts
      match ts with
      | "(" :: r => do let (tys, ts) ← pCtorTysLoop f r; .ok ((n, tys), ts)
      | _        => .ok ((n, []), ts)

/-- `|`-separated constructors (≥ 1). -/
def pCtors : Nat → P (List (String × List Ty))
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts => do
      let (c, ts) ← pCtor f ts
      match ts with
      | "|" :: r => do let (rest, ts) ← pCtors f r; .ok (c :: rest, ts)
      | _        => .ok ([c], ts)

/-- Type parameters after a data name, up to (not consuming) `=`: `data List a b = …` ⇒ `[a, b]`. Each
is a bare lowercase-by-convention identifier (not enforced); `[]` for a monomorphic `data N = …`. -/
def pDataParams : Nat → P (List String)
  | 0,     ts => .ok ([], ts)
  | f + 1, ts => match ts with
    | "=" :: _ => .ok ([], ts)
    | p :: r   => do let (rest, ts) ← pDataParams f r; .ok (p :: rest, ts)
    | []       => .error "unterminated data declaration (expected '=')"

/-- HK trait parameters after a trait name, up to (not consuming) `{`: `trait Functor f {` ⇒ `[f]`.
Each is a bare identifier (the constructor-kinded var, ADR-0082); `[]` for a Self-only bite-2 trait. -/
def pTraitParams : Nat → P (List String)
  | 0,     ts => .ok ([], ts)
  | f + 1, ts => match ts with
    | "{" :: _ => .ok ([], ts)
    | p :: r   => do let (rest, ts) ← pTraitParams f r; .ok (p :: rest, ts)
    | []       => .error "unterminated trait declaration (expected '{')"

/-- One declaration: `trait N { … }`, `impl N for τ { … }`, or `data N ā = C | …`. -/
def pDecl : Nat → P Decl
  | 0,     _  => .error "parser out of fuel"
  | f + 1, "data" :: ts => do
      let (n, ts) ← pIdent ts
      let (ps, ts) ← pDataParams f ts        -- type params before `=` (`data List a`); [] = monomorphic
      let (_, ts) ← expect "=" ts
      let (cs, ts) ← pCtors f ts
      .ok (.dataD n ps cs, ts)
  | f + 1, "trait" :: ts => do
      let (n, ts) ← pIdent ts
      let (ps, ts) ← pTraitParams f ts        -- HK trait params before `{` (`trait Functor f`); [] = Self-only
      let (_, ts) ← expect "{" ts
      let ((ops, laws), ts) ← pTraitMembers f ts
      .ok (.traitD n ps ops laws, ts)
  | f + 1, "impl" :: ts => do
      let (n, ts) ← pIdent ts
      let (_, ts) ← expect "for" ts
      let (t, ts) ← pTy f ts
      let (_, ts) ← expect "{" ts
      let (ops, ts) ← pImplMembers f ts
      .ok (.implD n t ops, ts)
  | f + 1, "fn" :: ts => do                    -- bounded generic function (bite-2, ADR-0080)
      let (n, ts) ← pIdent ts
      let (ps, ts) ← pParams f ts
      let (_, ts) ← expect ":" ts
      let (ty, ts) ← pTy f ts                  -- declared type, mentioning the bound var (`List a -> a`)
      let (_, ts) ← expect "where" ts
      let (tr, ts) ← pIdent ts                 -- the bound: `Trait tyVar` (`Monoid a`)
      let (tv, ts) ← pIdent ts
      let (_, ts) ← expect "=" ts
      let (b, ts) ← pExpr f ts                 -- body (self-delimiting: end it at a `match`/`)` before the next decl)
      .ok (.fnD n ps ty tr tv b, ts)
  | f + 1, "effect" :: ts => do                -- ADR-0092 D1: `effect N { op1 : ArgTy -> ResTy, … }`
      let (n, ts) ← pIdent ts
      let (_, ts) ← expect "{" ts
      let (ops, ts) ← pEffectMembers f ts
      .ok (.effectD n ops, ts)
  | f + 1, "let" :: "rec" :: ts => do          -- ADR-0093 D5 (operator ruling): `let rec name : T = expr`
      let (n, ts) ← pIdent ts
      let (_, ts) ← expect ":" ts
      let (t, ts) ← pTy f ts
      let (_, ts) ← expect "=" ts
      let (e, ts) ← pExpr f ts
      .ok (.letRecD n t e, ts)
  | f + 1, "let" :: ts => do                   -- ADR-0093 D5 (operator ruling): `let name [: Ty] = expr` (no `in`)
      let (n, ts) ← pIdent ts
      match ts with
      | ":" :: ts => do
          let (t, ts) ← pTy f ts
          let (_, ts) ← expect "=" ts
          let (e, ts) ← pExpr f ts
          .ok (.letD n (some t) e, ts)
      | _ => do
          let (_, ts) ← expect "=" ts
          let (e, ts) ← pExpr f ts
          .ok (.letD n none e, ts)
  | _ + 1, t :: r => .error ⟨s!"expected 'trait', 'impl', 'data', 'fn', 'effect', or 'let', got '{t}'", t :: r⟩
  | _ + 1, []     => .error "expected a declaration, got end of input"

/-- Is `t` a decl-leading keyword (with or without a `pub` prefix already stripped)? Named once so
`pDecls`'s lookahead and `pDecl`'s `pub`-arm dispatch a single shared list (ADR-0093 D3: `pub` is
accepted before every decl keyword). `let` is DELIBERATELY excluded here — it is ambiguous with the
script-mode `let x = e in body` form, so its decl-vs-body disambiguation is `pDecls`'s OWN job
(`isLetDecl`, below), not a static membership test. -/
def isDeclStart : String → Bool
  | "trait" | "impl" | "data" | "fn" | "effect" => true
  | _ => false

/-- Does a `let`/`let rec` at the HEAD of `ts` parse as a top-level DECL (no trailing `in`), or is it
the script-mode `let … in …` body form? ADR-0093 D5 operator ruling (2026-07-09): disambiguate by
the presence of `in` AFTER the bound expression — deterministic lookahead, never a guess (ADR-0046).
Implemented by actually parsing the `let`/`let rec` HEAD (name, optional `: Ty`, `=`, the bound expr
— `pExpr` is already self-delimiting, so it stops cleanly at whatever token follows) and checking
that token: `in` ⟹ script mode (`none`, `pDecls` must NOT consume this — the caller re-parses the
SAME prefix as the trailing body via `pExpr`), anything else ⟹ a genuine decl (`some`, cheaply
re-derived by `pDecl` immediately after — reparsing here is simpler and no more costly than a
backtracking combinator would be, since `pExpr`'s work is O(expr length) either way).

`;` is ALSO script-mode (issue #68's multi-binding sugar): a top-level decl never has a `;`-
separated binding LIST — that shape only exists inside `let x = e1; y = e2 in body`'s expression
form — so `;` right after the first binding's RHS is exactly as decisive as `in` would be; a decl
lookahead never needs to walk the WHOLE binding chain, only distinguish "more script-mode follows"
from "this is a genuine decl". `let rec` has NO multi-binding form (only plain `let` does — #68's
own scope), so its arm is unchanged. -/
def isLetDecl (fuel : Nat) (ts : List String) : Bool :=
  match ts with
  | "let" :: "rec" :: nts => Id.run <| do
      match pIdent nts with
      | .error _ => pure false
      | .ok (_, nts) => match expect ":" nts with
        | .error _ => pure false
        | .ok (_, nts) => match pTy fuel nts with
          | .error _ => pure false
          | .ok (_, nts) => match expect "=" nts with
            | .error _ => pure false
            | .ok (_, nts) => match pExpr fuel nts with
              | .error _ => pure false
              | .ok (_, rest) => pure (rest.head? != some "in")
  | "let" :: nts => Id.run <| do
      match pIdent nts with
      | .error _ => pure false
      | .ok (_, nts) =>
          -- the optional `: Ty` ascription (D5 ruling point (c)) — skip it in the lookahead the
          -- SAME way `pDecl`'s own parse does, so the two never disagree on where `=` starts.
          let nts := match nts with
            | ":" :: rest => match pTy fuel rest with
                | .ok (_, rest') => rest'
                | .error _       => nts   -- malformed ascription: let the REAL parse surface the error
            | _ => nts
          match expect "=" nts with
          | .error _ => pure false
          | .ok (_, nts) => match pExpr fuel nts with
            | .error _ => pure false
            | .ok (_, rest) => pure (rest.head? != some "in" && rest.head? != some ";")
  | _ => false

/-- One declaration, `pub`-prefixable (ADR-0093 D3): `pub data …`, `pub fn …`, etc. mark the decl
exported; the bare form (no `pub`) is module-private by default. Returns the parsed `Decl` alongside
whether it was `pub` — `pDecls` folds that into `Prog.pubNames` by `Decl.name` so every existing
`Decl` consumer stays untouched (see the `Prog.pubNames` doc comment). -/
def pDeclPub : Nat → P (Decl × Bool)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, "pub" :: ts =>
      if let some t := ts.head? then
        if isDeclStart t || isLetDecl f ts then do let (d, ts) ← pDecl f ts; .ok ((d, true), ts)
        else .error ⟨s!"expected a declaration after 'pub', got '{t}'", ts⟩
      else .error "expected a declaration after 'pub', got end of input"
  | f + 1, ts => do let (d, ts) ← pDecl f ts; .ok ((d, false), ts)

/-- The declaration prelude: zero or more (optionally `pub`-prefixed) decls, delimited by their
leading keyword. Returns the decls plus the accumulated `pub` name set. A `let`/`let rec` decl is
included ONLY when `isLetDecl` confirms it is not the script-mode body form (ADR-0093 D5) — checked
BEFORE consuming anything, so a script-mode `let … in …` correctly falls through to `.ok (([], []),
ts)` with `ts` UNCONSUMED, letting `parseProgE`'s `pExpr fuel ts` parse it as the trailing body. -/
def pDecls : Nat → P (List Decl × List String)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, ts =>
    match ts with
    | "pub" :: rest =>
      if (rest.head?.map isDeclStart).getD false || isLetDecl f rest then do
        let ((d, isPub), ts) ← pDeclPub f ts
        let ((ds, pubs), ts) ← pDecls f ts
        .ok ((d :: ds, if isPub then d.name :: pubs else pubs), ts)
      else .ok (([], []), ts)
    | "let" :: _ =>
      if isLetDecl f ts then do
        let ((d, isPub), ts) ← pDeclPub f ts
        let ((ds, pubs), ts) ← pDecls f ts
        .ok ((d :: ds, if isPub then d.name :: pubs else pubs), ts)
      else .ok (([], []), ts)
    | t :: _ =>
      if isDeclStart t then do
        let ((d, isPub), ts) ← pDeclPub f ts
        let ((ds, pubs), ts) ← pDecls f ts
        .ok ((d :: ds, if isPub then d.name :: pubs else pubs), ts)
      else .ok (([], []), ts)
    | [] => .ok (([], []), ts)

/-- One `import name` line (ADR-0093 D1) — a bare module qualifier, no names hoisted. -/
def pImport : P ImportDecl
  | "import" :: ts => do let (n, ts) ← pIdent ts; .ok (⟨n⟩, ts)
  | t :: r          => .error ⟨s!"expected 'import', got '{t}'", t :: r⟩
  | []              => .error "expected 'import', got end of input"

/-- The comma-separated name list of a `use mod (a, b, C)` line, up to and including `)`. -/
def pUseNamesLoop : P (List String)
  | ts => Id.run do
      let rec go : Nat → List String → P (List String)
        | 0,     _,  ts => .error ⟨"parser out of fuel", ts⟩
        | f + 1, ts, cur => do
            let (n, ts) ← pIdent ts
            match ts with
            | "," :: ts => go f ts (cur ++ [n])
            | ")" :: ts => .ok (cur ++ [n], ts)
            | t :: r    => .error ⟨s!"expected ',' or ')' in a `use` name list, got '{t}'", t :: r⟩
            | []        => .error "unterminated `use` name list"
      go (ts.length + 1) ts []

/-- One `use name (a, b, C)` line (ADR-0093 D2) — hoists exactly the named decls of module `name`
into unqualified scope. -/
def pUse : P UseDecl
  | "use" :: ts => do
      let (n, ts) ← pIdent ts
      let (_, ts) ← expect "(" ts
      let (names, ts) ← pUseNamesLoop ts
      .ok (⟨n, names⟩, ts)
  | t :: r => .error ⟨s!"expected 'use', got '{t}'", t :: r⟩
  | []     => .error "expected 'use', got end of input"

/-- The file HEADER: zero or more `import`/`use` lines, in any order, before the decl prelude
(ADR-0093 D1/D2). Structural on the leading token — stops at the first token that is neither. -/
def pHeader : Nat → P (List ImportDecl × List UseDecl)
  | 0,     _  => .error "parser out of fuel"
  | f + 1, "import" :: ts => do
      let (imp, ts) ← pImport ("import" :: ts)
      let ((imps, uses), ts) ← pHeader f ts
      .ok ((imp :: imps, uses), ts)
  | f + 1, "use" :: ts => do
      let (u, ts) ← pUse ("use" :: ts)
      let ((imps, uses), ts) ← pHeader f ts
      .ok ((imps, u :: uses), ts)
  | _ + 1, ts => .ok (([], []), ts)

/-- Parse a whole PROGRAM: the `import`/`use` header (ADR-0093 D1/D2), the `pub`-prefixable decl
prelude, then EITHER a body expression (script mode, unchanged corpus) OR nothing (library mode —
a decls-only file, e.g. a module meant only to be imported, D5). Same fuel bound as `parse`; a
plain expression still parses identically (`decls = []`, `body` present). -/
def parseProgE (src : String) : Except PErr Prog := do
  let toks := tokenize src
  let fuel := toks.length * 6 + 1
  let ((imps, uses), ts) ← pHeader fuel toks
  let ((ds, pubs), ts) ← pDecls fuel ts
  if ts.isEmpty then .ok ⟨imps, uses, pubs, ds, .lit 0, true⟩    -- library mode: no trailing expr (D5)
  else
    let (e, rest) ← pExpr fuel ts
    if rest.isEmpty then .ok ⟨imps, uses, pubs, ds, e, false⟩
    else .error ⟨s!"trailing tokens after expression: {rest}", rest⟩

def parseProg (src : String) : Except String Prog := (parseProgE src).mapError (·.msg)

/-- Erase `.lettMulti` (issue #68) from EVERY `Surf`-carrying field of a `Decl` — the `Decl`-level
sibling of `eraseLettMulti`, mirroring `TypeCheck.lean`'s `qualifyDeclBody`'s exact per-variant
walk (the proven precedent for "map a `Surf`-recursive pass over every `Decl` field"). Needed
because a top-level `let`/`trait`/`impl`/`fn` decl's OWN bound expression can equally contain the
sugar, not just a program's trailing body. -/
def eraseLettMultiDecl : Decl → Decl
  | .traitD n ps ops laws => .traitD n ps ops (laws.map (fun l => { l with body := eraseLettMulti l.body }))
  | .implD n t ops        => .implD n t (ops.map (fun o => { o with body := eraseLettMulti o.body }))
  | .dataD n ps cs        => .dataD n ps cs
  | .effectD n ops        => .effectD n ops
  | .fnD n ps ty tr tv b  => .fnD n ps ty tr tv (eraseLettMulti b)
  | .letD n ty e          => .letD n ty (eraseLettMulti e)
  | .letRecD n t e        => .letRecD n t (eraseLettMulti e)

/-- Erase `.lettMulti` from a WHOLE parsed `Prog` — every decl's body (`eraseLettMultiDecl`) plus
the program's own trailing `body`. The ONE place this runs for the typed pipeline: `elabProg`'s
very first line (`Bang.Frontend.TypeCheck`), before `foldLetDecls`/`expandBFns`/`elabS`/qualification
ever see the tree — so none of THOSE functions need their own `.lettMulti` arm; they only ever
see the sugar already resolved, matching `letRecS`/`matchD`'s "should be pre-resolved" convention. -/
def eraseLettMultiProg (p : Prog) : Prog :=
  { p with decls := p.decls.map eraseLettMultiDecl, body := eraseLettMulti p.body }

#guard (eraseLettMultiProg { decls := [.letD "x" none (.lettMulti (.cons "a" (.lit 1) (.cons "b" (.lit 2) .nil)) (.binopS .add (.var "a") (.var "b")))], body := .lit 0, isLibrary := true }).decls
  == [.letD "x" none (.lett "a" (.lit 1) (.lett "b" (.lit 2) (.binopS .add (.var "a") (.var "b"))))]

/-- VIEW: the FULLY-located PROGRAM parse — the decl-aware sibling of `parseLocated`. Resolves each
`parseProgE` error to `(message, Span)` via `spanOfRest` (`parseProgE` tokenizes with `tokenize`, the
exact list `spanOfRest` indexes). PUBLIC: the `bang` CLI parses through this so a syntax error prints
`line:col` instead of a wall (ADR-0076 #51). `parseProg`'s bare-`String` result is this with the span
dropped — one code path (SSoT). -/
public def parseProgLocated (src : String) : Except (String × Option Span) Prog :=
  (parseProgE src).mapError (fun e => (e.msg, spanOfRest src e.rest))

-- located PROGRAM parse errors (ADR-0076 #51): a decl-prelude program reports the offending token's `line:col`.
#guard (match parseProgLocated "let x 3 in x" with | .error (_, some sp) => sp.loc == "1:7" | _ => false)
-- a well-formed program is `.ok` through the located path (a decl-free body parses to `⟨[], body⟩`).
#guard (match parseProgLocated "let x = 3 in x" with | .ok _ => true | .error _ => false)

/-- PUBLIC: parse a bare TYPE string (`Int`, `Int -> Int`, `Int ! {throws}`, …) — the type-level
sibling of `parse`/`parseProg`, no existing entry exposes `pTy` directly. Rejects trailing tokens
(mirrors `parseE`'s own "whole string is one term" contract). The intended consumer is a tool that
RENDERS a `Ty` via `Format.showTy`/`TypeCheck.showVTy`/`showCTy` and wants to round-trip it back
into a real `Ty` value (e.g. `bang annotate` re-parsing the checker's own inferred-type string
rather than re-deriving a second `Ty`-construction path) — `pTy`'s grammar is exactly `fmtTy`'s
own inverse for every constructor it can render (`Int`/`Unit`/`Thunk T`/`A -> B`/`A + B`/`A * B`/
`T ! {ρ}`), so this composition is sound by construction for that rendered subset. `Ty.tMu`/
`Ty.tApp`/`Ty.tSelf` are either unparseable in v1 (`tMu` — `fmtTy`'s own "INTERNAL" note) or parse
to a DIFFERENT constructor on the way back in (`tApp`/`tSelf` read as ordinary atoms/names) — a
caller round-tripping a RENDERED type must treat those as an honest non-round-trip, not assume
this function inverts every `Ty` shape. -/
public def parseTy (src : String) : Except String Ty :=
  let toks := tokenize src
  match pTy (toks.length * 4 + 1) toks with
  | .error e => .error e.msg
  | .ok (t, rest) =>
      if rest.isEmpty then .ok t
      else .error s!"trailing tokens after type: {rest}"

#guard parseTy "Int" == .ok .tInt
#guard parseTy "Unit" == .ok .tUnit
#guard parseTy "Int -> Int" == .ok (.tArr .tInt .tInt)
#guard parseTy "Thunk Int" == .ok (.tThunk .tInt)
#guard parseTy "Int ! {throws}" == .ok (.tEff ["throws"] .tInt)
#guard parseTy "Int ! {throws, state}" == .ok (.tEff ["throws", "state"] .tInt)
#guard (parseTy "Int Int").isOk == false   -- trailing tokens: not an application at the type level (v1)
-- round-trip on `fmtTy`'s OWN rendering grammar for a nested arrow+row shape (this module cannot
-- import `Format.lean` — a downstream leaf, see its module header — so the literal string here IS
-- `fmtTy`'s documented output for this `Ty`, asserted by hand rather than computed via the import;
-- `tools/test-annotate.sh` exercises the REAL `fmtTy ∘ parseTy` round-trip end-to-end via the CLI).
#guard parseTy "Int -> Int ! {throws}" == .ok (.tArr .tInt (.tEff ["throws"] .tInt))


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

/-! ### The `Outcome` assertion layer (issue #54).

The bespoke `runYieldsInt` PROJECTS the pipeline result onto ONE outcome and collapses everything
else to `false`, so a failure shows "not `n`" but never WHICH terminal (a wrong value / `oom` /
`stuck` / `escapedCap` are indistinguishable) and the exceptional terminals have no systematic
assertion. `Outcome` models the FULL pipeline result space as one total sum; the bespoke helpers are
re-derived as thin projections of it (`runYieldsInt` below; `runTypedYieldsInt` in `TypeCheck`), so
the whole `#guard` corpus rides ONE assertion construct. It REUSES the production entry points
(`runFrom` here, `checkAndLower`/`elaborateToComp` in `TypeCheck`) — it does NOT reimplement the
pipeline.

The REAL terminals, grounded in the source (NOT invented):
  · `Source.eval : … → Result Val`  where  `Result = done Val | oom | escapedCap | stuck` (Eval.lean).
  · two PRE-eval stage failures on the typed path: a located PARSE error (with a `Span`) and an
    elaboration/TYPE error. The untyped `runFrom` collapses both to `.stuck`, so `runOutcomeFrom`
    only ever produces `yields | oom | escaped | stuck`; `parseErr`/`typeErr` are reachable only
    through the typed runners in `TypeCheck`. -/
inductive Outcome where
  | parseErr : Option Span → String → Outcome   -- located parse error (span from `parseProgLocated`)
  | typeErr  : String → Outcome                 -- elaboration or type error (un-located in v1 ⇒ no span)
  | yields   : Val → Outcome                    -- `Result.done v`
  | oom      : Outcome                           -- `Result.oom`   (fuel exhausted / divergence)
  | escaped  : Outcome                           -- `Result.escapedCap` (ADR-0063 capability-escape)
  | stuck    : Outcome                           -- `Result.stuck` (genuine stuck)

-- (`Outcome.beq` / `BEq Outcome` / `outcomeIs` need `BEq Val`, defined later in this file; they
-- follow the `BEq Val` instance below.)

/-- The kernel `Result` → `Outcome` (the eval-terminal half; total over all four `Result` ctors). -/
def evalToOutcome : Result Val → Outcome
  | .done v     => .yields v
  | .oom        => .oom
  | .escapedCap => .escaped
  | .stuck      => .stuck

/-- The UNTYPED run (`parse >>= lower`, then eval) as a structured `Outcome`. Mirrors `runFrom`:
a parse/lower error is already collapsed to `.stuck` there, so this never returns `parseErr`/
`typeErr` (those are the typed runners' terminals). -/
def runOutcomeFrom (fuel : Nat) (src : String) : Outcome :=
  evalToOutcome (runFrom fuel src)

/-- Does the untyped run yield exactly `vint n`? A projection of `runOutcomeFrom` (matches the `vint`
and compares `Int`s — no `BEq Val` needed, so it lands before the `BEq Val` instance). -/
def assertYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  match runOutcomeFrom fuel src with | .yields (.vint m) => m == n | _ => false

/-- Does the untyped run get STUCK? (No oracle before; now systematic.) -/
def assertStuck (fuel : Nat) (src : String) : Bool :=
  match runOutcomeFrom fuel src with | .stuck => true | _ => false

/-- Does the untyped run hit the ADR-0063 capability-escape terminal? -/
def assertEscaped (fuel : Nat) (src : String) : Bool :=
  match runOutcomeFrom fuel src with | .escaped => true | _ => false

/-- Does the untyped run exhaust fuel (`oom`)? -/
def assertOom (fuel : Nat) (src : String) : Bool :=
  match runOutcomeFrom fuel src with | .oom => true | _ => false

/-- Does running `src` yield exactly `done (vint n)`? A `Bool` so `#guard` can check string-driven
runs without a `BEq` on kernel types. Now a thin PROJECTION of the `Outcome` layer (issue #54):
`runFrom` is untouched, so behaviour is identical — the green corpus below is the build-gated proof. -/
def runYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  assertYieldsInt fuel src n

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

/-! ### Exceptional terminals — the `Outcome` layer's NEW capability (issue #54).

`runYieldsInt` could only ever say "not a value"; the exceptional `Result` terminals had NO
systematic assertion. These name them directly on the untyped `runFrom` path. -/

-- STUCK: force a NON-thunk (`$3`) — `force` on a `vint` has no WHNF rule ⇒ the `.stuck` terminal.
#guard assertStuck 20 "$3"
-- ESCAPED (ADR-0063): a capability captured in a thunk and forced PAST its handler. `state 0 in {get}`
-- yields the thunk `{get}`; binding it OUT of the `state` scope and forcing (`$c`) dispatches `get`
-- after the `state` frame popped ⇒ the DEFINED `escapedCap` terminal (not `stuck`).
#guard assertEscaped 80 "let c = (state 0 in {get}) in $c"

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

/-! ### `Outcome` structural equality (issue #54) — the total `#guard` comparison.

Lands here (after `BEq Val`) because comparing `yields` payloads needs it. `Val` exposes only `BEq`
(not `DecidableEq`), so `deriving BEq` on `Outcome` can't fire; hand-written. -/
def Outcome.beq : Outcome → Outcome → Bool
  | .parseErr s1 m1, .parseErr s2 m2 =>
      -- `Span` derives `DecidableEq` (not `BEq`), so compare its fields, not `s1 == s2`.
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

/-- The total comparison a `#guard` checks (the typed runners in `TypeCheck` project through this). -/
def outcomeIs (o expected : Outcome) : Bool := o == expected


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
-- MULTI-BINDING LET SUGAR (issue #68): `let x = e1; y = e2 in body` parses to `.lettMulti` — the
-- SUGAR MARKER (not a bare `.lett` chain), which is what lets `bang fmt` distinguish it from a
-- hand-written nested chain (the operator's ruling). Tree-checked, not just parse-success.
#guard parsesTo "let x = 3; y = 4 in x + y"
  (.lettMulti (.cons "x" (.lit 3) (.cons "y" (.lit 4) .nil)) (.binopS .add (.var "x") (.var "y")))
#guard parsesTo "let a = 1; b = 2; c = 3 in a"
  (.lettMulti (.cons "a" (.lit 1) (.cons "b" (.lit 2) (.cons "c" (.lit 3) .nil))) (.var "a"))
-- `eraseLettMulti` recovers the IDENTICAL nested `.lett` chain a hand-written pyramid produces —
-- the semantic-equivalence half of the guard (every consumer but the printer sees THIS shape).
#guard (match parse "let x = 3; y = 4 in x + y" with
        | .ok e => eraseLettMulti e == .lett "x" (.lit 3) (.lett "y" (.lit 4) (.binopS .add (.var "x") (.var "y")))
        | .error _ => false)
#guard (match parse "let a = 1; b = 2; c = 3 in a" with
        | .ok e => eraseLettMulti e == .lett "a" (.lit 1) (.lett "b" (.lit 2) (.lett "c" (.lit 3) (.var "a")))
        | .error _ => false)
-- the n=1 case (no `;`) parses to the SAME tree the plain single-binding form always has —
-- confirms the sugar's base case did not accidentally change existing behavior.
#guard runYieldsInt 20 "let x = 3; y = 4 in x + y" 7
#guard runYieldsInt 20 "let x = 3 in x" 3
-- SEQUENTIAL SCOPING (the ruling's semantics, not Haskell's mutually-recursive let-block): a LATER
-- binding sees an EARLIER one; an earlier binding can NEVER see a later one (there is no such
-- binding to shadow yet — this would be an unbound-variable error if attempted, matching ordinary
-- `let` nesting order).
#guard runYieldsInt 20 "let x = 3; y = x + 1 in y" 4
#guard runYieldsInt 20 "let a = 1; b = 2; c = a + b in c" 3
#guard parsesTo "handle (raise 7)" (.handle (.raise (.lit 7)))
#guard parsesTo "state 0 in (let z = put 7 in get)"
  (.stateS (.lit 0) (.lett "z" (.putS (.lit 7)) .getS))
#guard parsesTo "state 5 in get" (.stateS (.lit 5) .getS)
#guard parsesTo "fun x => x" (.lam "x" (.var "x"))
-- STM forms (rung 3): `atomically`/`new`/`read`/`write` parse to their `Surf` constructors.
#guard parsesTo "atomically (let r = new 100 in (let z = write r 70 in read r))"
  (.atomS (.lett "r" (.newS (.lit 100))
    (.lett "z" (.writeS (.var "r") (.lit 70)) (.readS (.var "r")))))
-- #26 part-2: the effect ops are application-precedence prefix forms (like `get`), so their result
-- FEEDS the Pratt operator chain. `read a - 30` parses as `(read a) - 30`, NOT `read (a - 30)` — the
-- op binds tighter than `-`. Before the fix this was a keyword rule that returned before the operator
-- ("expected ')', got '-'"). `-` is `binopS Sub`; verify the tree, not just that it parses.
#guard parsesTo "read a - 30" (.binopS .sub (.readS (.var "a")) (.lit 30))
#guard parsesTo "new a + 1"   (.binopS .add (.newS (.var "a")) (.lit 1))
#guard parsesTo "write a (read a - 30)"
  (.writeS (.var "a") (.binopS .sub (.readS (.var "a")) (.lit 30)))

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
plus `if c then t else e` as sugar over `case` on `Bool = 1+1`. Whitespace-insensitive (ADR-0071 ④):
`a+b*c` tokenizes identically to `a + b * c`. -/

#guard runYieldsInt 20 "3 + 4" 7
#guard runYieldsInt 20 "2 + 3 * 4" 14            -- `*` binds tighter than `+`
#guard runYieldsInt 20 "10 - 3 - 2" 5            -- left-associative
#guard runYieldsInt 20 "(2 + 3) * 4" 20          -- parentheses override precedence
#guard runYieldsInt 30 "let x = 5 in x + 1" 6    -- the counter step, from source text
#guard runYieldsInt 30 "if 3 < 4 then 1 else 0" 1
#guard runYieldsInt 30 "if 4 < 3 then 1 else 0" 0
#guard runYieldsInt 30 "if 2 == 2 then 7 else 8" 7

-- UNARY MINUS (issue #64): `-e` desugars to `0 - e` (the same `.binopS .sub` node binary `-`
-- produces), so it binds to ONE atom — tighter than every binary operator, matching `-x + 1` and
-- `-x * y`'s conventional reading in every mainstream language.
#guard runYieldsInt 20 "-10" (-10)                    -- a negative literal at top level
#guard runYieldsInt 30 "let x = 5 in -x" (-5)         -- a bound variable
#guard runYieldsInt 30 "let x = 5 in -x + 1" (-4)      -- binds TIGHTER than `+`: (-x) + 1, not -(x+1)
#guard runYieldsInt 30 "let x = 5 in -x * 2" (-10)     -- binds TIGHTER than `*`: (-x) * 2
#guard runYieldsInt 20 "- -10" 10                     -- double negation
#guard runYieldsInt 20 "3 - -10" 13                   -- binary minus, unary minus as its RHS
#guard runYieldsInt 20 "3-(-10)" 13                   -- the same, unspaced + parenthesized
-- an unparenthesized bare application argument goes to the BINARY reading, not unary — the
-- Pratt loop's application-stop-set treats a bare `-` as "hand back to the enclosing binary
-- chain" (this is the conventional disambiguation every language with juxtaposition-application
-- + infix `-` makes; parenthesize the argument for the unary reading: `f (-1)`, not `f -1`).
#guard (match parse "let f = fun x => x in f -1" with
        | .ok (.app (.var "f") _) => false  -- would mean "f applied to -1" — NOT what this parses as
        | .ok _ => true                     -- "f - 1" (binary), the actual/correct parse
        | .error _ => false)
-- tree-checked (not just parse-success): `-10` really is `0 - 10`, the SAME shape binary `-`
-- produces — no bespoke unary-minus AST node exists.
#guard parsesTo "-10" (.binopS .sub (.lit 0) (.lit 10))
#guard parsesTo "-x" (.binopS .sub (.lit 0) (.var "x"))
#guard parsesTo "- -10" (.binopS .sub (.lit 0) (.binopS .sub (.lit 0) (.lit 10)))
#guard parsesTo "3 - -10" (.binopS .sub (.lit 3) (.binopS .sub (.lit 0) (.lit 10)))

-- the canonical COUNTER over a live state cell — blocked since rung-1, now written from source:
#guard runYieldsInt 50 "state 5 in (get + 1)" 6

-- parse-shape checks: precedence is structural, not eval-coincidence.
#guard parsesTo "a + b * c" (.binopS .add (.var "a") (.binopS .mul (.var "b") (.var "c")))
#guard parsesTo "if c then t else e" (.ifS (.var "c") (.var "t") (.var "e"))

-- ADR-0071 ④ — WHITESPACE-INSENSITIVE tokenization: an UNSPACED program tokenizes IDENTICALLY to
-- its spaced twin above. `a+b*c` parses to the SAME tree as `a + b * c` (structural proof); the
-- eval twins reuse their spaced counterparts' results. Maximal munch: `== => ->` before `= -`.
#guard parsesTo "a+b*c" (.binopS .add (.var "a") (.binopS .mul (.var "b") (.var "c")))  -- ≡ "a + b * c"
#guard runYieldsInt 20 "2+3*4" 14                 -- ≡ "2 + 3 * 4" (unspaced `+`/`*` split)
#guard runYieldsInt 20 "10-3-2" 5                 -- ≡ "10 - 3 - 2" (unspaced `-` splits, left-assoc)
#guard runYieldsInt 30 "let x=1 in x" 1           -- `x=1`: the let-binder `=` splits
#guard runYieldsInt 30 "if 3<4 then 1 else 0" 1   -- `3<4`: `<` splits
#guard runYieldsInt 20 "(fun x=>x : Int->Int) 5" 5  -- `=>` and `->` munch inside a type ascription (≡ spaced)

-- do-notation (issue #27): `x = e` → `lett x`, bare `e` → `lett "#do"`, last stmt = result.
#guard runYieldsInt 30 "do { x = 3; y = 4; x + y }" 7
#guard parsesTo "do { x = a; b; c }" (.lett "x" (.var "a") (.lett "#do" (.var "b") (.var "c")))

/-! ### Stage 2f — NAMED capabilities from source text (issue #3, ADR-0070; spelling ADR-0072).

A named handler is an optional `as <h>` binder on the effect form — `state <init> as <h> in <body>`,
`handle as <h> <body>`, `atomically as <h> <body>` (ADR-0072 dropped the old `with … as`). `h.op(args)`
performs on the bound cap. The headline is MULTIPLE COEXISTING instances — two state cells `a`/`b`,
which the ambient (nearest-sentinel) `get` cannot reach. Dispatch is identity-keyed (ADR-0052/0055),
so `a.get`/`b.get` hit their own cells. Runs via the untyped path (parse→lower→eval); the checker's
`Cap` typing is in TypeCheck. The `withCapS` tree is UNCHANGED from ADR-0070 — only the surface spelling. -/
-- a named state cap reads its cell.
#guard runYieldsInt 50 "state 5 as h in h.get" 5
-- put then get on the SAME named cap (resumptive).
#guard runYieldsInt 60 "state 5 as h in (let z = h.put(7) in h.get)" 7
-- ★ TWO state cells at once — the demo ambient `get` cannot write. a=1, b=2 ⟹ a.get + b.get = 3.
#guard runYieldsInt 90 "state 1 as a in (state 2 as b in (let x = a.get in (let y = b.get in x + y)))" 3
-- the inner cell is INDEPENDENT: mutate b, a is untouched. a=10, b:=20 ⟹ a.get = 10.
#guard runYieldsInt 120 "state 10 as a in (state 0 as b in (let z = b.put(20) in a.get))" 10
-- a named throws cap: h.raise aborts to its payload.
#guard runYieldsInt 50 "handle as h h.raise(9)" 9
-- a named transaction cap: new/write/read on `t` commit in-transaction.
#guard runYieldsInt 90 "atomically as t (let r = t.new(100) in (let z = t.write(r, 70) in t.read(r)))" 70
-- parse shape: `state <init> as h in body` + `h.op(arg)`.
#guard parsesTo "state 5 as h in h.get"
  (.withCapS "state" (.lit 5) "h" (.dotPerform (.var "h") "get" .none))
#guard parsesTo "h.put(7)" (.dotPerform (.var "h") "put" (.one (.lit 7)))
#guard parsesTo "t.write(r, w)" (.dotPerform (.var "t") "write" (.two (.var "r") (.var "w")))

-- implication sugar (#39): `P => Q` desugars to `let #p = P in if #p then Q else 0 == 0`.
#guard parsesTo "a < b => c"
  (.lett "#p" (.binopS .lt (.var "a") (.var "b"))
    (.ifS (.var "#p") (.var "c") (.binopS .eq (.lit 0) (.lit 0))))
-- right-associative: `p => q => r` = `p => (q => r)` (inner `#p` shadows — names are per-scope).
#guard parsesTo "p => q => r"
  (.lett "#p" (.var "p")
    (.ifS (.var "#p")
      (.lett "#p" (.var "q") (.ifS (.var "#p") (.var "r") (.binopS .eq (.lit 0) (.lit 0))))
      (.binopS .eq (.lit 0) (.lit 0))))
-- a TRUE implication with a false premise runs to true (vacuous — 5 < 3 => anything).
#guard runYieldsInt 30 "if (5 < 3 => 0 == 1) then 1 else 0" 1

/-! ### Stage ⑤ — `trait`/`impl` declarations parse (issue #24 piece 1; ADR-0040 §5, ADR-0068).

A program is a decl PRELUDE + body (`Prog`, `parseProg`). Pure syntax: the decls are inert data
until the type-directed elaborator (piece 2) consumes them; the untyped path (`parse`) is
untouched. -/

/-- Does `src` parse to exactly the program `p`? (`parsesTo`, lifted to `Prog`.) -/
def progParsesTo (src : String) (p : Prog) : Bool :=
  match parseProg src with
  | .ok p' => decide (p' = p)
  | .error _ => false

-- a trait with an op signature and a law parses to its decl form (the law body is an EQUATION
-- over the op, via `==` — Bool-valued, per ADR-0068's v1 law-body scope).
#guard progParsesTo "trait Add { fn add(a, b) -> Int ; law comm(a, b): add a b == add b a } 0"
  { decls := [.traitD "Add" [] [⟨"add", ["a", "b"], .tInt, .tArr .tSelf (.tArr .tSelf .tInt)⟩]
      [⟨"comm", ["a", "b"],
        .binopS .eq (.app (.app (.var "add") (.var "a")) (.var "b"))
                    (.app (.app (.var "add") (.var "b")) (.var "a"))⟩]],
    body := .lit 0 }
-- an impl for a STRUCTURAL target type (ADR-0068 decision 2): the target is a `pTy`.
#guard progParsesTo "impl Add for (Int * Int) { fn add(p, q) = p } 0"
  { decls := [.implD "Add" (.tProd .tInt .tInt) [⟨"add", ["p", "q"], .var "p"⟩]], body := .lit 0 }
-- member separators are optional (keywords delimit): two ops, no semicolon.
#guard progParsesTo "trait Ord { fn le(a, b) -> Int fn eq(a, b) -> Int } 0"
  { decls := [.traitD "Ord" [] [⟨"le", ["a", "b"], .tInt, .tArr .tSelf (.tArr .tSelf .tInt)⟩,
                      ⟨"eq", ["a", "b"], .tInt, .tArr .tSelf (.tArr .tSelf .tInt)⟩] []], body := .lit 0 }
-- the northstar program SHAPE parses end-to-end: trait + impl + a pair-addition body.
#guard (match parseProg "trait Add { fn add(a, b) -> Int } impl Add for (Int * Int) { fn add(p, q) = p } (1, 2) + (3, 4)" with
        | .ok p => p.decls.length == 2
        | .error _ => false)
-- with NO decls, `parseProg` agrees with `parse` — the untyped path is untouched.
#guard (match parseProg "let x = 3 in x + 1", parse "let x = 3 in x + 1" with
        | .ok p, .ok e => decide (p = { decls := [], body := e })
        | _, _ => false)
-- the new keywords are RESERVED: using one as a binder fails loud.
#guard (match parseProg "let fn = 3 in fn" with | .error _ => true | _ => false)
-- a malformed trait body fails loud (an expression where 'fn'/'law'/'}' was expected).
#guard (match parseProg "trait Add { 3 } 0" with | .error _ => true | _ => false)

/-! ### Stage ⑥ — modules: `import`/`use`/`pub` (ADR-0093 D1/D2/D3). Pure syntax here — resolution
(reading another file, name-qualification, visibility ENFORCEMENT) is the elaborator/CLI's job
(`TypeCheck.lean`/`Main.lean`); this stage only proves the header + `pub` prefix parse to the right
`Prog` shape. -/

-- a bare `import` line: qualifier-only, no names hoisted.
#guard progParsesTo "import tokenizer 0"
  { imports := [⟨"tokenizer"⟩], decls := [], body := .lit 0 }
-- a `use` line: the explicit name list, ctor-carrying names included verbatim (D2 — ctors travel
-- with their type is a RESOLUTION-time fact, not visible in the parsed `UseDecl` itself).
#guard progParsesTo "use tokenizer (lex, Token) 0"
  { uses := [⟨"tokenizer", ["lex", "Token"]⟩], decls := [], body := .lit 0 }
-- both header forms compose, any order, before the decl prelude.
#guard progParsesTo "import a use b (c) import d 0"
  { imports := [⟨"a"⟩, ⟨"d"⟩], uses := [⟨"b", ["c"]⟩], decls := [], body := .lit 0 }
-- `pub` prefixes every decl keyword and is recorded in `pubNames`; a bare (non-`pub`) decl is NOT.
#guard progParsesTo "pub data Json = JNull data Hidden = HNull 0"
  { pubNames := ["Json"],
    decls := [.dataD "Json" [] [("JNull", [])], .dataD "Hidden" [] [("HNull", [])]],
    body := .lit 0 }
#guard progParsesTo "pub fn id(x) : Int where Eq a = x data Hidden = HNull 0"
  { pubNames := ["id"],
    decls := [.fnD "id" ["x"] .tInt "Eq" "a" (.var "x"), .dataD "Hidden" [] [("HNull", [])]],
    body := .lit 0 }
-- a DECLS-ONLY file (no trailing expression) parses to library mode — D5's third case. The
-- placeholder body is `.lit 0` (unobservable — a library file is never itself RUN as a script;
-- `Main.lean`'s entry-mode detection, not this parser, decides what "no body" MEANS operationally).
#guard progParsesTo "data Json = JNull"
  { decls := [.dataD "Json" [] [("JNull", [])]], body := .lit 0, isLibrary := true }
-- `import`/`use`/`pub` are RESERVED: using one as a binder fails loud (ADR-0046, matching the
-- existing `let fn = …` reservation guard above).
#guard (match parseProg "let import = 3 in import" with | .error _ => true | _ => false)
#guard (match parseProg "let use = 3 in use" with | .error _ => true | _ => false)
#guard (match parseProg "let pub = 3 in pub" with | .error _ => true | _ => false)
-- `pub` before a SCRIPT-MODE `let … in …` (not a decl — `in` follows) fails loud: `pub` cannot
-- prefix the trailing body expression (ADR-0093 D5's operator ruling changed `let` from
-- unconditionally-not-a-decl to CONDITIONALLY a decl, so this guard's shape changed — it now
-- probes the disambiguator's OTHER branch, `isLetDecl` returning false because `in` follows).
#guard (match parseProg "pub let x = 3 in x" with | .error _ => true | _ => false)
-- `use` missing its name-list parens fails loud, not a silent partial parse.
#guard (match parseProg "use tokenizer 0" with | .error _ => true | _ => false)

/-! ### Stage ⑦ — top-level `let`/`let rec` DECLS (ADR-0093 D5, operator ruling 2026-07-09): the
GENERAL binding form subsuming both plain-function module exports and the `main` entry point — no
main-only special case. Disambiguated from the script-mode `let … in …` body by the ABSENCE of a
trailing `in` (`isLetDecl`'s deterministic lookahead). -/

-- a top-level `let name = expr` (no `in`) parses as a decl, not a script-mode body. The bound
-- expression is followed by ANOTHER decl keyword (not a bare literal) to avoid the SAME "value
-- followed by another atom parses as application" ambiguity the `fn`-body corpus already works
-- around — `let x = 3 0` would parse `3 0` as an application, swallowing the `0` into `x`'s bound
-- expression rather than leaving it as a separate trailing body.
#guard progParsesTo "let x = 3 data Hidden = HNull 0"
  { decls := [.letD "x" none (.lit 3), .dataD "Hidden" [] [("HNull", [])]], body := .lit 0 }
-- `pub let` exports it (D3's uniform `pub`-prefix machinery, now covering the NEW decl kind too).
#guard progParsesTo "pub let x = 3 data Hidden = HNull 0"
  { pubNames := ["x"], decls := [.letD "x" none (.lit 3), .dataD "Hidden" [] [("HNull", [])]], body := .lit 0 }
-- `let rec name : T = expr` (no `in`) parses as the recursive decl sibling.
#guard progParsesTo "let rec f : Int -> Int = fun n => n data Hidden = HNull 0"
  { decls := [.letRecD "f" (.tArr .tInt .tInt) (.lam "n" (.var "n")), .dataD "Hidden" [] [("HNull", [])]], body := .lit 0 }
#guard progParsesTo "pub let rec f : Int -> Int = fun n => n data Hidden = HNull 0"
  { pubNames := ["f"],
    decls := [.letRecD "f" (.tArr .tInt .tInt) (.lam "n" (.var "n")), .dataD "Hidden" [] [("HNull", [])]],
    body := .lit 0 }
-- MULTIPLE let decls compose, in order, mixed with other decl kinds.
#guard progParsesTo "let x = (3) data Hidden = HNull let y = 4 data Extra = ENull 0"
  { decls := [.letD "x" none (.lit 3), .dataD "Hidden" [] [("HNull", [])], .letD "y" none (.lit 4),
              .dataD "Extra" [] [("ENull", [])]],
    body := .lit 0 }
-- the SAME source text with a trailing `in` is UNCHANGED script-mode behavior (D5's own point:
-- the disambiguator must not touch the existing corpus) — `let x = 3 in x + 1` still parses as a
-- decl-free program whose body is that whole `let … in …` expression, byte-identical to before.
#guard (match parseProg "let x = 3 in x + 1", parse "let x = 3 in x + 1" with
        | .ok p, .ok e => decide (p = { decls := [], body := e })
        | _, _ => false)
-- MULTI-BINDING SUGAR (issue #68) at TOP LEVEL: `isLetDecl`'s D5 lookahead must recognize `;`
-- (not just `in`) as "still script-mode" — a decl NEVER has a `;`-separated binding chain (that
-- shape only exists inside the `let … in …` EXPRESSION form), so `;` right after the first
-- binding's RHS is exactly as decisive as `in` would be. Without this, a top-level program using
-- the sugar would be MISJUDGED as a decl (since `;` != "in"), leaving the file's OWN body
-- unconsumed and reporting library-mode nothing-to-run — this guard is the regression for that
-- exact misjudgment.
#guard (match parseProg "let x = 3; y = 4 in x + y", parse "let x = 3; y = 4 in x + y" with
        | .ok p, .ok e => decide (p = { decls := [], body := e })
        | _, _ => false)
-- a decls-ONLY file using a plain `let` (library mode, D5's third case, no trailing body at all).
#guard progParsesTo "let x = 3"
  { decls := [.letD "x" none (.lit 3)], body := .lit 0, isLibrary := true }
-- `main` is now literally a `let` decl — no special keyword, exactly the ruling's point.
#guard progParsesTo "let main = 42"
  { decls := [.letD "main" none (.lit 42)], body := .lit 0, isLibrary := true }
-- the OPTIONAL type ascription on plain `let` (D5 ruling point (c)): `let name : Ty = expr`.
#guard progParsesTo "let x : Int = 3"
  { decls := [.letD "x" (some .tInt) (.lit 3)], body := .lit 0, isLibrary := true }
-- WITHOUT the ascription, the decl still carries `none` (not a parse of `x` as a type — the `:`
-- is what triggers the ascription branch, so its ABSENCE must not be confused with a malformed one).
#guard progParsesTo "let x = 3"
  { decls := [.letD "x" none (.lit 3)], body := .lit 0, isLibrary := true }
-- REGRESSION (caught dogfooding the JSON split): `pub`/`import`/`use` were reserved in `pIdent`
-- (blocking their use as BINDERS) but NOT in `pAtom`'s OWN separate reserved-word list — so a
-- `let`-decl's bound expression, followed immediately by a SECOND `pub let ...` decl, silently
-- swallowed the `pub` keyword as an APPLICATION ARGUMENT (`{fun n => …} pub`) instead of stopping
-- there. Two adjacent `pub let` decls now correctly parse as TWO decls, not one decl whose body
-- absorbed the next decl's leading keyword.
#guard progParsesTo "pub let x = 3 pub let y = 4"
  { pubNames := ["x", "y"], decls := [.letD "x" none (.lit 3), .letD "y" none (.lit 4)], body := .lit 0, isLibrary := true }

end -- public section
end Bang.Surface
