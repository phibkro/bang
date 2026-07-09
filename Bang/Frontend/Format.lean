/-
  Bang/Frontend/Format.lean — the canonical formatter (`bang fmt`, issue #58).
  ─────────────────────────────────────────────────────────────────────────
  Agent-first lens (operator ruling, 2026-07-09): bang has zero training data, so an
  agent's output style is pure improvisation. A canonical formatter deletes that style
  entropy — one deterministic rendering per `Surf`/`Ty`/`Decl`/`Prog`, gofmt precedent
  (ZERO config, no options; ADR-0046 "elaboration is deterministic-or-loud" extends
  naturally to "printing is deterministic-or-not-done").

  v1 is a FLAT (single-line) printer: every corpus example today is written on one line
  or a hand-wrapped multi-line style with no consistent convention (`examples/parser-combinators`
  column-aligns `let`s, `examples/tokenizer` wraps long match arms, `examples/state` is one
  line) — so there is no majority multi-line house style to ride yet. A flat printer is also
  the form whose laws are cheapest to make watertight: minimal-parenthesization from the SAME
  precedence table the parser consults (`opInfo`, ADR-0071) is what the round-trip law tests
  directly. Multi-line/wrapped layout is a follow-up rung (issue #58 leaves it open), not a v1
  requirement.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 from the verified spine — the arch-check
  invariant): it reads `Surf`/`Ty`/`Decl`/`Prog` from `Bang.Frontend.Surface` and the `BinOp`
  spellings from `Bang.Core.IR`, and produces only strings. No kernel/typing-rule change.
-/
module

-- `#guard`s (§7, below) run `parseProg`/`parse` at the META phase → `meta import` (the cross-module
-- `#guard` codegen wall; mirrors `TypeCheck.lean`/`Examples.lean`). `public import` re-exports the
-- same module for ordinary def-level use (`fmtSurf`, `showTy`, …) — the dual-import idiom every
-- other leaf that both DEFINES over `Surf` and `#guard`s against it already uses.
meta import Bang.Frontend.Surface
public import Bang.Frontend.Surface

namespace Bang.Format

open Bang.Surface

/-! The two laws this module exists to prove (as `#guard`s over the corpus, at the bottom):

    idempotency  : fmt (fmt s) = fmt s          — formatting a formatted program is a no-op
    round-trip   : parse (fmt (parse s)) = parse s  — formatting NEVER changes the AST

`fmt` here operates on the PARSED `Surf`/`Prog`, not raw source text — "format" means
"canonical print of the AST", so both laws are really about the printer being a canonical
representative of its input's parse, which is what makes them checkable without re-parsing
the printed output through a second oracle. -/

/-! ## 1. Binary operator spellings

`BinOp` lives in the verified kernel IR (`Bang.BinOp`, `Bang/Core/IR.lean`) — this module only
PATTERN-MATCHES it (a leaf reading a Core type, same relationship `Bang.Frontend.Surface`
already has), never modifies it. Every spelling here is the exact token `opInfo` (Surface.lean)
maps FROM, so re-parsing a printed operator is a fixpoint. -/

/-- The surface token for a `BinOp` — inverse of `opInfo`'s builder table. -/
def binOpTok : Bang.BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .lt  => "<"
  | .eq  => "=="

/-! ## 2. Type printer

Mirrors `pTy`'s precedence exactly (loosest → tightest: `->` (right-assoc) > `+` (left-assoc) >
`*` (left-assoc) > atom/application), so a printed type re-parses to the same `Ty` with no
extra parens needed EXCEPT where precedence would otherwise change the parse — the classic
minimal-parenthesization printer, one precedence level per printer function. -/

/-- Precedence tiers, loosest first — mirrors `pTy`/`pTyAdd`/`pTyMul`/`pTyAtom`. -/
inductive TyPrec | arr | add | mul | atom
  deriving DecidableEq

def TyPrec.level : TyPrec → Nat
  | .arr => 0 | .add => 1 | .mul => 2 | .atom => 3

/-- Wrap `s` in parens iff the type's own tier binds looser than the CONTEXT requires
(`need`) — i.e. printing at a tighter slot than the type's natural precedence. -/
def parenIf (need own : TyPrec) (s : String) : String :=
  if own.level < need.level then s!"({s})" else s

mutual
partial def fmtTy (need : TyPrec) : Ty → String
  | .tInt        => "Int"
  | .tUnit       => "Unit"
  | .tSelf       => "Self"
  | .tName n     => n
  | .tVar n      => s!"#{n}"                          -- INTERNAL (μ-bound); never parsed, printed defensively
  | .tMu a       => s!"(mu. {fmtTy .atom a})"          -- INTERNAL; ditto
  | .tThunk t    => parenIf need .atom s!"Thunk {fmtTy .atom t}"
  | .tApp n args => parenIf need .atom (s!"{n} " ++ String.intercalate " " (fmtTyArgs args))
  | .tArr a b    => parenIf need .arr  s!"{fmtTy .add a} -> {fmtTy .arr b}"     -- right-assoc: rhs at OWN level
  | .tSum a b    => parenIf need .add  s!"{fmtTy .add a} + {fmtTy .mul b}"      -- left-assoc: lhs at OWN level
  | .tProd a b   => parenIf need .mul  s!"{fmtTy .mul a} * {fmtTy .atom b}"     -- left-assoc: lhs at OWN level
  | .tEff ns t   => parenIf need .atom s!"{fmtTy .atom t} ! \{{String.intercalate ", " ns}}"
partial def fmtTyArgs : TyArgs → List String
  | .one a   => [fmtTy .atom a]
  | .two a b => [fmtTy .atom a, fmtTy .atom b]
end

/-- Top-level entry: a type prints at the loosest tier (no defensive outer parens). -/
def showTy (t : Ty) : String := fmtTy .arr t

/-! ## 3. Surface expression printer

Precedence tiers mirror the Pratt table (`opInfo`, ADR-0071 — loosest first): `=>`-desugar
never round-trips through `Ty`/`Surf` printing (it only appears mid-parse, never in a parsed
tree — `pOp` immediately folds it into `lett`/`ifS`), `<`/`==` (comparison, left-assoc) loosest
real tier, then `+`/`-` (left-assoc), then `*`/`/` (left-assoc), then application (juxtaposition,
no token), tightest. Keyword-led forms (`let`, `if`, `match`, …) and atoms sit at `atom` tier —
they are self-delimiting (parens never needed around them EXCEPT as an application head/operand
per the grammar, handled by `atom`'s own callers demanding `.atom`). -/

inductive SPrec | cmp | add | mul | app | atom
  deriving DecidableEq

def SPrec.level : SPrec → Nat
  | .cmp => 0 | .add => 1 | .mul => 2 | .app => 3 | .atom => 4

def sParenIf (need own : SPrec) (s : String) : String :=
  if own.level < need.level then s!"({s})" else s

/-- Render a data-ctor call `SCons(a, b)` (an `.app f (.pairS a b)`) using call syntax when `f`'s
head IS a bare capitalized-or-lowercase identifier applied to a literal-tuple payload — the exact
shape the parser produces for `C(x, y)`/`C(x)` (`pAtom`'s `"("` case builds `pairS`, then `pApp`
applies it). Printing it back as `f(a, b)` re-tokenizes identically to `f (a, b)` (whitespace
before `(` is insignificant), so this is a pure STYLE choice riding the corpus convention
(`examples/tokenizer`: `TCons(SNil, TNil)`), not a parse requirement. -/
def isCtorHead : Surf → Option String
  | .var n => some n
  | _      => none

/-- Escape a code point back into `"…"` literal form — the INVERSE of `decodeEsc` (Surface.lean).
Only the characters `decodeEsc` treats specially need re-escaping; everything else (including
non-ASCII code points) passes through as its glyph, `String.singleton (Char.ofNat …)`. -/
def escapeCodepoint (n : Int) : String :=
  match n with
  | 10 => "\\n"    -- '\n'
  | 9  => "\\t"    -- '\t'
  | 34 => "\\\""   -- '"'
  | 92 => "\\\\"   -- '\'
  | _  => String.singleton (Char.ofNat n.toNat)

/-- Recognize the EXACT `Str` ctor-chain shape `strToSurf` builds (Surface.lean, ADR-0074):
`SNil` / `SCons(Char n, rest)` nested only through this shape. Returns the recovered glyph string
if the whole spine matches; `none` the moment a non-chain node appears (a real ctor call some other
`data` type happens to name `SCons`/`Char`, or a variable/computed sub-term, is left untouched —
this is a pure PRINT-SIDE sugar recovery, never changes the AST, so a false negative here just
prints the equivalent-but-verbose ctor-chain form, not a wrong tree). -/
partial def asStringLit : Surf → Option String
  | .var "SNil" => some ""
  | .app (.var "SCons") (.pairS (.app (.var "Char") (.lit n)) rest) => do
      let restStr ← asStringLit rest
      some (escapeCodepoint n ++ restStr)
  | _ => none

mutual
partial def fmtSurf (need : SPrec) : Surf → String
  | .lit n   => if n < 0 then s!"({n})" else toString n   -- the tokenizer has no unary '-': defensive only
  | .var x   => x
  | .unitS   => "()"
  | .getS    => "get"
  | .thunk e => s!"\{{fmtSurf .cmp e}}"
  | .force e => s!"${fmtSurf .atom e}"
  | .lett x e b => sParenIf need .cmp s!"let {x} = {fmtSurf .cmp e} in {fmtSurf .cmp b}"
  | .lam x b    => sParenIf need .cmp s!"fun {x} => {fmtSurf .cmp b}"
  -- `f(a, b)`-style ctor calls print `f`+the tuple with NO space (`SCons(a, b)`), matching the corpus
  -- (`examples/tokenizer`'s `TCons(SNil, TNil)`). But `SCons(a, b)` is STILL structurally `f (a, b)` —
  -- one juxtaposed atom (`f`) then another (the parenthesized pair) — so it is `.app`-tier, NOT atomic:
  -- as an application ARGUMENT (`g SCons(a, b)`) it would re-tokenize as `g SCons (a, b)` = `(g SCons)
  -- (a, b)`, a DIFFERENT tree (found by the round-trip law over the string-stdlib/tokenizer corpus —
  -- the exact failure this comment documents). Must `sParenIf need .app` like plain application.
  | e@(.app f a)    =>
      -- STRING-LITERAL recovery (ADR-0074): a non-empty `SCons(Char n, …)` chain prints back as
      -- `"…"` — a pure print-side sugar, checked FIRST (before the general ctor-call/app cases).
      -- A genuine LITERAL is a true grammar ATOM (one token), so it never needs defensive parens.
      match asStringLit e with
      | some s => "\"" ++ s ++ "\""
      | none   =>
      match a with
      | .pairS a1 a2 =>
          match isCtorHead f with
          | some n => sParenIf need .app s!"{n}({fmtSurf .cmp a1}, {fmtSurf .cmp a2})"   -- ctor-call: SCons(a, b)
          | none   => sParenIf need .app s!"{fmtSurf .app f} ({fmtSurf .cmp a1}, {fmtSurf .cmp a2})"
      | _ => sParenIf need .app s!"{fmtSurf .app f} {fmtSurf .atom a}"
  -- `raise`/`put`/`new`/`read`/`write` parse in APPLICATION position (`pApp`, atom arguments) — their
  -- own printed form IS an atom, so `need` may demand `.atom` and still print bare (`raise 7`, applied
  -- as `f (raise 7)`, needs parens the caller already supplies via `.app`'s arg tier). Their ARGUMENTS,
  -- though, are atom-tier (`pAtom`), so a non-atomic argument (e.g. `raise (let x = 3 in x)`) must be
  -- parenthesized — handled by printing the argument at `.atom` need, which the argument's own
  -- `sParenIf` resolves.
  | .raise e => sParenIf need .app s!"raise {fmtSurf .atom e}"
  | .putS e   => sParenIf need .app s!"put {fmtSurf .atom e}"
  | .newS e   => sParenIf need .app s!"new {fmtSurf .atom e}"
  | .readS e  => sParenIf need .app s!"read {fmtSurf .atom e}"
  | .writeS r w => sParenIf need .app s!"write {fmtSurf .atom r} {fmtSurf .atom w}"
  -- `handle`/`atomically` parse a FULL expression body (`.refE` in `keywordRule`) at `pExpr` top level —
  -- unlike `raise`/`put`/…, they are NOT reachable from inside `pApp`'s atom slot without explicit
  -- parens, so their OWN printed form is loosest-tier (`.cmp`), parenthesizing whenever `need` is
  -- anything tighter (matches `.lett`/`.lam`/`.ifS`/`.matchS`/keyword forms below).
  | .handle e => sParenIf need .cmp s!"handle {fmtSurf .atom e}"
  | .stateS e0 e => sParenIf need .cmp s!"state {fmtSurf .atom e0} in {fmtSurf .cmp e}"
  | .atomS e  => sParenIf need .cmp s!"atomically {fmtSurf .atom e}"
  | .inlS e   => s!"Left({fmtSurf .cmp e})"
  | .inrS e   => s!"Right({fmtSurf .cmp e})"
  | .pairS a b => s!"({fmtSurf .cmp a}, {fmtSurf .cmp b})"
  | .matchS s lx e1 rx e2 =>
      sParenIf need .cmp s!"match {fmtSurf .atom s} \{ Left({lx}) -> {fmtSurf .cmp e1}, Right({rx}) -> {fmtSurf .cmp e2} }"
  | .splitS a b p body =>
      sParenIf need .cmp s!"let ({a}, {b}) = {fmtSurf .cmp p} in {fmtSurf .cmp body}"
  | .binopS op a b =>
      match op with
      | .lt | .eq => sParenIf need .cmp s!"{fmtSurf .add a} {binOpTok op} {fmtSurf .add b}"
      | .add | .sub => sParenIf need .add s!"{fmtSurf .add a} {binOpTok op} {fmtSurf .mul b}"
      | .mul | .div => sParenIf need .mul s!"{fmtSurf .mul a} {binOpTok op} {fmtSurf .app b}"
  | .ifS c t e => sParenIf need .cmp s!"if {fmtSurf .cmp c} then {fmtSurf .cmp t} else {fmtSurf .cmp e}"
  | .annotS e t => s!"({fmtSurf .cmp e} : {showTy t})"
  | .foldS e   => s!"(fold {fmtSurf .atom e})"                              -- INTERNAL; printed defensively
  | .unfoldS e => s!"(unfold {fmtSurf .atom e})"                           -- INTERNAL; ditto
  | .matchD s arms => sParenIf need .cmp s!"match {fmtSurf .atom s} \{ {fmtDArms arms} }"
  -- `withCapS`'s internal `kind` tag is `"throws"`/`"state"`/`"atomically"` (`lowerC`'s cap-binder
  -- names), but the SURFACE keyword for `"throws"` is `handle` (ADR-0072's `handle as h e`, not
  -- `throws as h e` — there is no `throws` keyword in the grammar). `"state"`/`"atomically"` already
  -- match their surface spelling. All three bodies are `.refE` (a full expression, `keywordRule`),
  -- so `body` prints at `.cmp`, matching `handle`/`atomically`/`state`.
  | .withCapS kind e0 h body =>
      sParenIf need .cmp <|
        if kind = "state" then s!"state {fmtSurf .atom e0} as {h} in {fmtSurf .cmp body}"
        else if kind = "throws" then s!"handle as {h} {fmtSurf .cmp body}"
        else s!"{kind} as {h} {fmtSurf .cmp body}"
  -- `h.op(args)` is parsed by `pDotLoop`, invoked FROM `pDotted` right after `pAtom` — the whole
  -- chain result is itself an atom (feeds `pAppLoop`/`pOp` same as any other atom), so it never
  -- needs defensive parens even at `.atom` need.
  | .dotPerform recv op args =>
      match args with
      | .none      => s!"{fmtSurf .atom recv}.{op}"
      | .one a     => s!"{fmtSurf .atom recv}.{op}({fmtSurf .cmp a})"
      | .two a b   => s!"{fmtSurf .atom recv}.{op}({fmtSurf .cmp a}, {fmtSurf .cmp b})"
  | .letRecS f ty body b =>
      sParenIf need .cmp s!"let rec {f} : {showTy ty} = {fmtSurf .cmp body} in {fmtSurf .cmp b}"
  | .divMark e => fmtSurf need e                                          -- INTERNAL marker; transparent to printing
partial def fmtDArms : DArms → String
  | .nil            => ""
  | .cons c [] b .nil        => s!"{c} -> {fmtSurf .cmp b}"
  | .cons c bs b .nil        => s!"{c}({String.intercalate ", " bs}) -> {fmtSurf .cmp b}"
  | .cons c [] b rest        => s!"{c} -> {fmtSurf .cmp b}, {fmtDArms rest}"
  | .cons c bs b rest        => s!"{c}({String.intercalate ", " bs}) -> {fmtSurf .cmp b}, {fmtDArms rest}"
end

/-- Top-level entry: an expression prints at the loosest tier (no defensive outer parens). -/
def showSurf (e : Surf) : String := fmtSurf .cmp e

/-! ## 4. Declaration + program printer -/

def fmtCtors : List (String × List Ty) → String
  | []              => ""
  | [(c, [])]       => c
  | [(c, ts)]       => s!"{c}({String.intercalate ", " (ts.map showTy)})"
  | (c, []) :: rest => s!"{c} | {fmtCtors rest}"
  | (c, ts) :: rest => s!"{c}({String.intercalate ", " (ts.map showTy)}) | {fmtCtors rest}"

def fmtOpSig (s : OpSig) : String :=
  if s.params.isEmpty then s!"fn {s.name} : {showTy s.methodTy}"
  else s!"fn {s.name}({String.intercalate ", " s.params}) -> {showTy s.retTy}"

def fmtLawDecl (l : LawDecl) : String :=
  s!"law {l.name}({String.intercalate ", " l.params}): {showSurf l.body}"

def fmtOpDef (d : OpDef) : String :=
  s!"fn {d.name}({String.intercalate ", " d.params}) = {showSurf d.body}"

/-- One declaration, on one line — a `#`-comment-free canonical rendering (comments are not part
of `Surf`/`Decl`, ADR-0046: the surface has no semantics of its own beyond its elaboration, and a
comment carries none, so it is out of scope for this AST-driven printer). -/
def fmtDecl : Decl → String
  | .dataD n ps cs   =>
      let params := if ps.isEmpty then "" else " " ++ String.intercalate " " ps
      s!"data {n}{params} = {fmtCtors cs}"
  | .traitD n ps ops laws =>
      let params := if ps.isEmpty then "" else " " ++ String.intercalate " " ps
      let body := String.intercalate "; " ((ops.map fmtOpSig) ++ (laws.map fmtLawDecl))
      s!"trait {n}{params} \{ {body} }"
  | .implD n t ops   =>
      s!"impl {n} for {showTy t} \{ {String.intercalate "; " (ops.map fmtOpDef)} }"
  | .fnD n ps ty tr tv body =>
      s!"fn {n}({String.intercalate ", " ps}) : {showTy ty} where {tr} {tv} = {showSurf body}"

/-- A whole program: each decl on its own line, then the body expression. Matches every
`examples/*/main.bang` today (`data …` / `let rec …` lines followed by the body). -/
def showProg (p : Prog) : String :=
  let declLines := p.decls.map fmtDecl
  String.intercalate "\n" (declLines ++ [showSurf p.body])

/-! ## 5. `fmt` — the two public entry points `bang fmt` wraps

`fmtExpr`/`fmtProg` round-trip through the SAME parser the rest of the toolchain uses
(`Bang.Surface.parse`/`parseProg`), so a formatting failure on unparsable input is the identical
fail-loud parse error every other entry point gives — no silent pass-through of malformed source
(ADR-0046: deterministic function or a loud error, never a guess). -/

/-- Format a single bare expression (no decl prelude) — what `bang eval "…"` accepts.
`public`: the CLI (Main.lean, outside this module) wires `bang fmt` against these. -/
public def fmtExpr (src : String) : Except String String :=
  (parse src).map showSurf

/-- Format a whole program (decls + body) — what `bang fmt <file.bang>` reads. -/
public def fmtProg (src : String) : Except String String :=
  (parseProg src).map showProg

/-! ## 6. The two laws, as decidable predicates over a program string

`idempotentOn`/`roundTripsOn` are the DIRECT, computable statement of the issue #58 laws — every
`#guard` below is one of these two applied to a corpus string, so a false assertion (an unparsable
fmt output, a re-parse mismatch, or a fmt-of-fmt drift) FAILS `lake build` (the reliable oracle;
`lake env lean` #eval/#guard is NOT trustworthy for this fuel-adjacent recursive machinery per
repo lesson `lean-eval-reliable-only-compiled` — these are non-recursive string ops, but the
build-gate discipline is uniform regardless). -/

/-- Idempotency: `fmt` is a no-op on its own output. `false` on ANY failure (parse/fmt error at
either stage) — a failure is not vacuously "idempotent", it is a DISTINCT bug the `#guard` must
catch, not silently pass. -/
def idempotentOn (src : String) : Bool :=
  match fmtProg src with
  | .error _ => false
  | .ok out1 =>
      match fmtProg out1 with
      | .error _ => false
      | .ok out2 => out1 == out2

/-- Round-trip: formatting never changes the parsed AST — `parse (fmt (parse s)) = parse s`,
stated directly over `Prog` (`DecidableEq`-derived, so `==` is the real equality, not a stand-in).
`false` on any parse/fmt failure along the way. -/
def roundTripsOn (src : String) : Bool :=
  match parseProg src with
  | .error _ => false
  | .ok p0 =>
      match fmtProg src with
      | .error _ => false
      | .ok out =>
          match parseProg out with
          | .error _ => false
          | .ok p1 => p0 == p1

end Bang.Format

/-! ## 7. The corpus gate (issue #58, the hard gate)

Every string below is drawn from `examples/*/main.bang` (verbatim) plus the edge cases that
SURFACED real printer bugs during development (documented inline) — ctor-call precedence
(`f SCons(a, b)` vs `f(SCons(a, b))`), the atom-vs-full-expression split on keyword-led forms
(`raise`/`put`/`new`/`read`/`write` take ATOM arguments; `handle`/`atomically`/`state`/`let`/`if`/
`match`/`let rec` parse a FULL expression, so which side of that line a construct sits on changes
whether its printed form self-parenthesizes). A failure here is a FINDING (a parser/printer
disagreement), not a style nit — per the operator's ruling, report it, never paper over it. -/

open Bang.Format in
#guard roundTripsOn "let x = 3 in x" && idempotentOn "let x = 3 in x"
open Bang.Format in
#guard roundTripsOn "let x = 1 in (let x = 2 in x)" && idempotentOn "let x = 1 in (let x = 2 in x)"
open Bang.Format in
#guard roundTripsOn "let c = {7} in $c" && idempotentOn "let c = {7} in $c"
open Bang.Format in
#guard roundTripsOn "(fun x => x) 5" && idempotentOn "(fun x => x) 5"
open Bang.Format in
#guard roundTripsOn "handle (raise 7)" && idempotentOn "handle (raise 7)"
open Bang.Format in
#guard roundTripsOn "handle (let z = raise 7 in 99)" && idempotentOn "handle (let z = raise 7 in 99)"
open Bang.Format in
#guard roundTripsOn "state 5 in get" && idempotentOn "state 5 in get"
open Bang.Format in
#guard roundTripsOn "state 0 in (let z = put 7 in get)" && idempotentOn "state 0 in (let z = put 7 in get)"
open Bang.Format in
#guard roundTripsOn "state 0 in (let c = {get} in (let a = put 5 in (let b = put 9 in $c)))"
       && idempotentOn "state 0 in (let c = {get} in (let a = put 5 in (let b = put 9 in $c)))"
open Bang.Format in
#guard roundTripsOn "state 1 in (let c = {get} in (state 2 in $c))"
       && idempotentOn "state 1 in (let c = {get} in (state 2 in $c))"
open Bang.Format in
#guard roundTripsOn "atomically (let r = new 100 in (let z = write r 70 in read r))"
       && idempotentOn "atomically (let r = new 100 in (let z = write r 70 in read r))"
open Bang.Format in
#guard roundTripsOn "handle (atomically (let r = new 100 in (let z = write r 70 in raise 100)))"
       && idempotentOn "handle (atomically (let r = new 100 in (let z = write r 70 in raise 100)))"
open Bang.Format in
#guard roundTripsOn "match Right(7) { Left(a) -> 0 , Right(x) -> x }"
       && idempotentOn "match Right(7) { Left(a) -> 0 , Right(x) -> x }"
open Bang.Format in
#guard roundTripsOn "let (a, b) = (3, 4) in (let (c, d) = (b, a) in c)"
       && idempotentOn "let (a, b) = (3, 4) in (let (c, d) = (b, a) in c)"
open Bang.Format in
#guard roundTripsOn "let x = 3 in let y = 4 in x * x + y * y" && idempotentOn "let x = 3 in let y = 4 in x * x + y * y"
open Bang.Format in
#guard roundTripsOn "atomically (let a = new 100 in (let bal = read a in (let bal2 = bal - 30 in (let z = write a bal2 in read a))))"
       && idempotentOn "atomically (let a = new 100 in (let bal = read a in (let bal2 = bal - 30 in (let z = write a bal2 in read a))))"
open Bang.Format in
#guard roundTripsOn "state 4 in (let c = {get * get} in (let z = put 9 in $c))"
       && idempotentOn "state 4 in (let c = {get * get} in (let z = put 9 in $c))"
open Bang.Format in
#guard roundTripsOn "state 0 in (let z = put (get + 1) in get)" && idempotentOn "state 0 in (let z = put (get + 1) in get)"
open Bang.Format in
#guard roundTripsOn "atomically (let a = new 100 in read a - 30)" && idempotentOn "atomically (let a = new 100 in read a - 30)"
open Bang.Format in
#guard roundTripsOn "do { x = 3; y = 4; x + y }" && idempotentOn "do { x = 3; y = 4; x + y }"
open Bang.Format in
#guard roundTripsOn "state 5 in (do { x = get; put (x + 1); get })" && idempotentOn "state 5 in (do { x = get; put (x + 1); get })"
open Bang.Format in
#guard roundTripsOn "( fun x => x : Int -> Int ) 5" && idempotentOn "( fun x => x : Int -> Int ) 5"
open Bang.Format in
#guard roundTripsOn "state 5 as h in h.get" && idempotentOn "state 5 as h in h.get"
-- `raise` takes an ATOM argument (`pApp`): a non-atomic argument (`let`/`if`) MUST get defensive
-- parens in the printed form, or it re-tokenizes as a different application chain. Found live.
open Bang.Format in
#guard roundTripsOn "handle (raise (let x = 3 in x))" && idempotentOn "handle (raise (let x = 3 in x))"
open Bang.Format in
#guard roundTripsOn "handle (raise (if 1 < 2 then 3 else 4))" && idempotentOn "handle (raise (if 1 < 2 then 3 else 4))"
open Bang.Format in
#guard roundTripsOn "(fun x => fun y => x + y) 3 4" && idempotentOn "(fun x => fun y => x + y) 3 4"
-- The exact bug this file's `.app`/ctor-call comment documents: `f SCons(a, b)` (no parens on the
-- ctor-call ARGUMENT) re-tokenizes as `(f SCons) (a, b)`, a DIFFERENT tree. Also exercises the
-- string-literal print-recovery (`asStringLit`): `"ab"` round-trips through the `SCons`/`Char`
-- desugar and back to `"ab"`, not the verbose ctor-chain.
open Bang.Format in
#guard roundTripsOn "($tokCount) (($tokenize) \"ab\")" && idempotentOn "($tokCount) (($tokenize) \"ab\")"
-- `examples/tokenizer/main.bang` verbatim (#49 stage 5 — "writes its own tools").
open Bang.Format in
#guard roundTripsOn "data TokList = TNil | TCons(Str, TokList)\nlet rec tokenize : Str -> TokList = fun s => match s { SNil -> TCons(SNil, TNil), SCons(c, rest) -> if (match c { Char(n) -> n == 32 }) then TCons(SNil, ($tokenize) rest) else (match (($tokenize) rest) { TNil -> TCons(SCons(c, SNil), TNil), TCons(w, more) -> TCons(SCons(c, w), more) }) } in\nlet rec tokCount : TokList -> Int = fun tl => match tl { TNil -> 0, TCons(w, rest) -> 1 + ($tokCount) rest } in\n($tokCount) (($tokenize) \"ab cd ef\")"
       && idempotentOn "data TokList = TNil | TCons(Str, TokList)\nlet rec tokenize : Str -> TokList = fun s => match s { SNil -> TCons(SNil, TNil), SCons(c, rest) -> if (match c { Char(n) -> n == 32 }) then TCons(SNil, ($tokenize) rest) else (match (($tokenize) rest) { TNil -> TCons(SCons(c, SNil), TNil), TCons(w, more) -> TCons(SCons(c, w), more) }) } in\nlet rec tokCount : TokList -> Int = fun tl => match tl { TNil -> 0, TCons(w, rest) -> 1 + ($tokCount) rest } in\n($tokCount) (($tokenize) \"ab cd ef\")"
-- `examples/string-stdlib/main.bang` verbatim (ADR-0074).
open Bang.Format in
#guard roundTripsOn "if (($eq) (($reverse) \"dcba\") (($concat) \"ab\" \"cd\")) then 1 else 0"
       && idempotentOn "if (($eq) (($reverse) \"dcba\") (($concat) \"ab\" \"cd\")) then 1 else 0"
-- `examples/parser-combinators/main.bang` verbatim — the largest corpus entry (many `let`s, nested
-- `match`/`Option`/tuple patterns, `let rec many`, string-literal args to curried helpers).
open Bang.Format in
#guard roundTripsOn "let isDigit = { fun n => if 47 < n then (if n < 58 then 0 == 0 else 0 == 1) else 0 == 1 } in\nlet sub48   = { fun n => n - 48 } in\nlet satisfy = { fun pred => fun s => match (s : Str) {\n  SNil -> None,\n  SCons(c, rest) -> match c { Char(n) ->\n    if (($pred) n) then Some((n, rest)) else None } } } in\nlet char = { fun code => ($satisfy) { fun n => n == code } } in\nlet mapP = { fun f => fun p => fun s => match (($p) s) {\n  None -> None,\n  Some(r) -> let (v, rest) = r in let w = ($f) v in Some((w, rest)) } } in\nlet orElse = { fun p => fun q => fun s => match (($p) s) {\n  None -> (($q) s),\n  Some(r) -> Some(r) } } in\nlet andThen = { fun p => fun q => fun s => match (($p) s) {\n  None -> None,\n  Some(r1) -> let (v1, rest1) = r1 in match (($q) rest1) {\n    None -> None,\n    Some(r2) -> let (v2, rest2) = r2 in let sm = v1 + v2 in Some((sm, rest2)) } } } in\nlet rec many : Thunk (Str -> Option (Int * Str)) -> Str -> Int = fun p => fun s =>\n  match (($p) s) {\n    None -> 0,\n    Some(r) -> let (v, rest) = r in 1 + ($many) p rest } in\nlet firstVal = { fun p => fun s =>\n  match (($p) s) { None -> 0, Some(r) -> let (v, rest) = r in v } } in\nlet digit = { ($mapP) sub48 { ($satisfy) isDigit } } in\nlet nDigits = ($many) digit \"42abc\" in\nlet firstDigit = ($firstVal) digit \"7\" in\nlet choiceP = { ($orElse) { ($char) 122 } digit } in\nlet choice = ($firstVal) choiceP \"9x\" in\nlet seqP = { ($andThen) digit digit } in\nlet seqSum = ($firstVal) seqP \"34\" in\nlet toPair = { fun v => (v, v) } in\nlet pairP = { ($mapP) toPair digit } in\nlet pairSum = match (($pairP) \"5\") { None -> 0, Some(r) -> let (pv, rest) = r in let (x, y) = pv in x + y } in\nnDigits + firstDigit + choice + seqSum + pairSum"
       && idempotentOn "let isDigit = { fun n => if 47 < n then (if n < 58 then 0 == 0 else 0 == 1) else 0 == 1 } in\nlet sub48   = { fun n => n - 48 } in\nlet satisfy = { fun pred => fun s => match (s : Str) {\n  SNil -> None,\n  SCons(c, rest) -> match c { Char(n) ->\n    if (($pred) n) then Some((n, rest)) else None } } } in\nlet char = { fun code => ($satisfy) { fun n => n == code } } in\nlet mapP = { fun f => fun p => fun s => match (($p) s) {\n  None -> None,\n  Some(r) -> let (v, rest) = r in let w = ($f) v in Some((w, rest)) } } in\nlet orElse = { fun p => fun q => fun s => match (($p) s) {\n  None -> (($q) s),\n  Some(r) -> Some(r) } } in\nlet andThen = { fun p => fun q => fun s => match (($p) s) {\n  None -> None,\n  Some(r1) -> let (v1, rest1) = r1 in match (($q) rest1) {\n    None -> None,\n    Some(r2) -> let (v2, rest2) = r2 in let sm = v1 + v2 in Some((sm, rest2)) } } } in\nlet rec many : Thunk (Str -> Option (Int * Str)) -> Str -> Int = fun p => fun s =>\n  match (($p) s) {\n    None -> 0,\n    Some(r) -> let (v, rest) = r in 1 + ($many) p rest } in\nlet firstVal = { fun p => fun s =>\n  match (($p) s) { None -> 0, Some(r) -> let (v, rest) = r in v } } in\nlet digit = { ($mapP) sub48 { ($satisfy) isDigit } } in\nlet nDigits = ($many) digit \"42abc\" in\nlet firstDigit = ($firstVal) digit \"7\" in\nlet choiceP = { ($orElse) { ($char) 122 } digit } in\nlet choice = ($firstVal) choiceP \"9x\" in\nlet seqP = { ($andThen) digit digit } in\nlet seqSum = ($firstVal) seqP \"34\" in\nlet toPair = { fun v => (v, v) } in\nlet pairP = { ($mapP) toPair digit } in\nlet pairSum = match (($pairP) \"5\") { None -> 0, Some(r) -> let (pv, rest) = r in let (x, y) = pv in x + y } in\nnDigits + firstDigit + choice + seqSum + pairSum"

-- A ctor-call AS AN APPLICATION ARGUMENT, on a NON-`Str` data type (so `asStringLit`'s shortcut
-- cannot intercept it — this specifically exercises the `.app`-tier ctor-call print path), with
-- EXPLICIT source parens forcing `Mk(1, 2)` to be the single nested argument (`($f) (Mk(1, 2))`,
-- NOT the ambiguous unparenthesized `($f) Mk(1, 2)`, which the grammar itself already reads as TWO
-- separate arguments regardless of the printer). This is the load-bearing regression guard for the
-- bug this file's ctor-call comment documents: an earlier draft printed `SCons(a, b)`'s call form
-- as an unconditional ATOM (never parenthesizing), which re-tokenized `f Mk(1, 2)` as `(f Mk) (1,
-- 2)` — a DIFFERENT tree from `f (Mk(1, 2))`. Verified this guard FAILS the build without the
-- `sParenIf need .app` wrap (manually confirmed via `lake build` during development).
open Bang.Format in
#guard roundTripsOn "data Pair = Mk(Int, Int)\nlet f = fun x => x in\n($f) (Mk(1, 2))"
       && idempotentOn "data Pair = Mk(Int, Int)\nlet f = fun x => x in\n($f) (Mk(1, 2))"
