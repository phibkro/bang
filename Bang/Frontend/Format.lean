/-
  Bang/Frontend/Format.lean — the canonical formatter (`bang fmt`, issue #58).
  ─────────────────────────────────────────────────────────────────────────
  Agent-first lens (operator ruling, 2026-07-09): bang has zero training data, so an
  agent's output style is pure improvisation. A canonical formatter deletes that style
  entropy — one deterministic rendering per `Surf`/`Ty`/`Decl`/`Prog`, gofmt precedent
  (ZERO config, no options; ADR-0046 "elaboration is deterministic-or-loud" extends
  naturally to "printing is deterministic-or-not-done").

  Multi-line layout (ADR-0090, 2026-07-09 operator ruling: "Accept all, 100"): the printer
  builds a `Std.Format` DOCUMENT (Wadler Doc algebra, already in the Lean toolchain —
  `Init/Data/Format/Basic.lean`, self-cited to *A Prettier Printer*) rather than a `String`
  directly, and renders it via `Std.Format.pretty (width := defWidth)`. This ADDS multi-line
  layout WITHOUT hand-rolling a second Wadler kernel (one-construct-per-problem) and WITHOUT
  a user-facing width knob (D3: one fixed module constant, zero config — the same
  gofmt/dart_style/black lesson the header above already follows for parenthesization).
  `defWidth := 100`, `defIndent := 2` are the operator-ruled values (ADR-0090 D3) — the middle
  path between the survey's 80 (diff-pane classic) and Lean's host-default 120.

  The minimal-parenthesization logic (`parenIf`/`sParenIf`, driven by `opInfo`, ADR-0071) is
  UNCHANGED — it still decides WHETHER a paren is needed, exactly mirroring the parser's
  precedence table. What changed is the OUTPUT TYPE: printer functions build `Std.Format`
  documents (`text`/`append`/`group`/`nest`/`line`) instead of `String`s, so parens are `text`
  and breaks are `group`/`nest`/`line` — the two concerns compose without either one knowing
  about the other (ADR-0090 D1). `examples/*/main.bang` is NOT reformatted by this change (D6);
  only `fmt`'s OUTPUT changes, gated by the `#guard`s below (§7), not by rewriting the corpus.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 from the verified spine — the arch-check
  invariant): it reads `Surf`/`Ty`/`Decl`/`Prog` from `Bang.Frontend.Surface` and the `BinOp`
  spellings from `Bang.Core.IR`, and produces only strings (via `Std.Format`, host code on the
  tested-superset side of the ADR-0026 seam — the verified kernel never imports it). No
  kernel/typing-rule change.
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
open Std (Format)

/-! The two laws this module exists to prove (as `#guard`s over the corpus, at the bottom):

    idempotency  : fmt (fmt s) = fmt s          — formatting a formatted program is a no-op
    round-trip   : parse (fmt (parse s)) = parse s  — formatting NEVER changes the AST

`fmt` here operates on the PARSED `Surf`/`Prog`, not raw source text — "format" means
"canonical print of the AST", so both laws are really about the printer being a canonical
representative of its input's parse, which is what makes them checkable without re-parsing
the printed output through a second oracle. Both laws are AGNOSTIC to line structure (ADR-0090
D4): they are stated over the parsed `Prog`, so multi-line output must satisfy them exactly as
the v1 flat output did — a break decision that depended on anything but width+AST would show up
as an `idempotentOn` failure (the second `fmt` sees different input text, not the same AST). -/

/-! ## 0. Width — the ONE fixed module constant (ADR-0090 D3, zero-config)

Operator-ruled (2026-07-09): 100 columns, 2-space indent — no user-facing knob, no CLI flag.
Every `pretty` call in this module goes through `render`, which is the ONLY place `defWidth`/
`defIndent` are consulted, so changing the constant changes ALL output uniformly (single source
of truth for the layout budget). -/

/-- Canonical rendering width — ADR-0090 D3 operator ruling. Fixed; never a knob. -/
def defWidth : Nat := 100

/-- Canonical nest increment — ADR-0090 D3 operator ruling (matches Lean-host `Std.Format.defIndent`). -/
def defIndent : Int := 2

/-- Render a `Format` document to its canonical string — the ONE place `pretty`/`defWidth` are
called, so every printer entry point renders through the same budget. -/
def render (f : Format) : String := Format.pretty f defWidth

/-- `nest` at the canonical indent (mirrors `Std.Format.nestD`, pinned to OUR constant rather than
the host's `defIndent`, since D3 rules our own value). -/
def nestD (f : Format) : Format := Format.nest defIndent f

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
minimal-parenthesization printer, one precedence level per printer function.

Types stay on ONE line: D2's break table names `let`/`fun`/`if`/`match`/decl-body/application/
tuple as the multi-line nodes — a `Ty` is not among them (the corpus has no type long enough to
need wrapping, and a type's constituents are themselves short atoms/names). `fmtTy` therefore
still returns `String`, exactly as v1; it is lifted to `Format` (`Format.text`) only at its use
sites inside `Surf`/`Decl` printing. -/

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
  | .tCap ℓ      => s!"Cap #{ℓ}"                       -- #84 gap 1: already-RESOLVED (the source `Cap Net`
                                  -- name is gone by the time `resolveTyG` produces this — `Format.lean`
                                  -- has no `env.effects` to invert the label back, the SAME `tVar`/`tMu`
                                  -- "INTERNAL; printed defensively" precedent, not a round-trippable form)
  | .tVar n      => s!"#{n}"                          -- INTERNAL (μ-bound); never parsed, printed defensively
  | .tMu a       => s!"(mu. {fmtTy .atom a})"          -- INTERNAL; ditto
  | .tThunk t    => parenIf need .atom s!"Thunk {fmtTy .atom t}"
  | .tApp n args => parenIf need .atom (s!"{n} " ++ String.intercalate " " (fmtTyArgs args))
  | .tArr a b    => parenIf need .arr  s!"{fmtTy .add a} -> {fmtTy .arr b}"     -- right-assoc: rhs at OWN level
  | .tSum a b    => parenIf need .add  s!"{fmtTy .add a} + {fmtTy .mul b}"      -- left-assoc: lhs at OWN level
  | .tProd a b   => parenIf need .mul  s!"{fmtTy .mul a} * {fmtTy .atom b}"     -- left-assoc: lhs at OWN level
  | .tEff ns t   => parenIf need .atom s!"{fmtTy .atom t} ! \{{String.intercalate ", " ns}}"
  | .tEffR ls t  => parenIf need .atom       -- #90: already-RESOLVED (labels, not source names) —
      s!"{fmtTy .atom t} ! \{{String.intercalate ", " (ls.map (s!"#{·}"))}}"   -- same `tCap`
      -- defensive-rendering precedent: `Format.lean` has no `env.effects` to invert a label back
      -- to its declared name, so this form is NOT round-trippable — internal, printed for debugging.
partial def fmtTyArgs : TyArgs → List String
  | .one a   => [fmtTy .atom a]
  | .two a b => [fmtTy .atom a, fmtTy .atom b]
end

/-- Top-level entry: a type prints at the loosest tier (no defensive outer parens).
`public` for the #80 query seam (like `showSurf` for #60): `bang query symbols` renders
DECLARED `Ty` for trait/impl/data/effect decls — reusing this printer avoids a second,
potentially-diverging parenthesization-aware `Ty` printer in Query.lean. -/
public def showTy (t : Ty) : String := fmtTy .arr t

/-! ## 3. Surface expression printer — now a `Std.Format` DOCUMENT builder (ADR-0090 D1/D2)

Precedence tiers mirror the Pratt table (`opInfo`, ADR-0071 — loosest first): `=>`-desugar
never round-trips through `Ty`/`Surf` printing (it only appears mid-parse, never in a parsed
tree — `pOp` immediately folds it into `lett`/`ifS`), `<`/`==` (comparison, left-assoc) loosest
real tier, then `+`/`-` (left-assoc), then `*`/`/` (left-assoc), then application (juxtaposition,
no token), tightest. Keyword-led forms (`let`, `if`, `match`, …) and atoms sit at `atom` tier —
they are self-delimiting (parens never needed around them EXCEPT as an application head/operand
per the grammar, handled by `atom`'s own callers demanding `.atom`).

D2's canonical break table, as implemented below:
  · `let x = e in b` / `let rec` / `let (a,b) = p in b` — `group`, break before `in`, body `b`
    at BASE indent (NOT nested: the corpus's dominant let-chain-is-a-sequence idiom — a chain of
    lets reads as a flat sequence, not a staircase).
  · `fun x => b` — `group`, break after `=>`, body nested `+defIndent`.
  · `if c then t else e` — `group`, break before `then`/`else`, arms nested `+defIndent`.
  · `match s { arms }` — `group`, break after `{`, one arm per line nested `+defIndent`, `}` at base.
  · application spines / binops — `group` the whole spine; argument boundaries are plain spaces
    (juxtaposition has no natural break token in bang's grammar — unlike a comma-list, breaking
    mid-spine would need a continuation marker the grammar doesn't have, so the spine breaks only
    at its OWN top join, same shape as a binop chain).
  · tuples `(a, b)`, ctor calls `C(a, b)` — `group`, break after the comma when over width. -/

inductive SPrec | cmp | add | mul | app | atom
  deriving DecidableEq

def SPrec.level : SPrec → Nat
  | .cmp => 0 | .add => 1 | .mul => 2 | .app => 3 | .atom => 4

/-- Text-level paren wrap (used where the wrapped content is itself still plain text, e.g. inside
a `Format.text` literal or a defensively-printed internal node). -/
def sParenIf (need own : SPrec) (s : String) : String :=
  if own.level < need.level then s!"({s})" else s

/-- `Format`-level paren wrap — the direct analogue of `sParenIf` over documents: wraps `f` in
literal `(`/`)` `text` nodes (never re-groups/re-nests `f`, so a parenthesized sub-document keeps
whatever internal breaks it already chose). -/
def fParenIf (need own : SPrec) (f : Format) : Format :=
  if own.level < need.level then Format.text "(" ++ f ++ Format.text ")" else f

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

/-- A comma-separated `Format` list, `group`ed so it breaks after commas (only) when the whole
group doesn't fit — the D2 tuple/ctor-call/param-list shape. `align`-free (base-column-relative
via the surrounding `nest`), matching D2's "break after commas when over width". No leading/
trailing space — callers that need `(…)`/`{…}` wrapping compose it with `fmtTupleGroup`/
`fmtBraceBlock`, which supply their own boundary spacing. -/
def fmtCommaGroup (items : List Format) : Format :=
  Format.group (Format.joinSep items ("," ++ Format.line))

/-- `(items, …)` — a tuple/ctor-call/param payload: `group`ed, breaks after commas, no space
just inside the parens even when flat (`(a, b)` not `( a, b )`, matching v1's flat spelling). -/
def fmtTupleGroup (l r : String) (items : List Format) : Format :=
  Format.group (Format.nest defIndent (Format.text l ++ fmtCommaGroup items) ++ Format.text r)

/-- A `{ … }` BLOCK body (D2's `match`/`data`/`trait`/`impl` shape): breaks after `{` onto a
nested `+defIndent` line per item (comma-separated), then an UNINDENTED line before the closing
`}` — the classic Wadler "wrap block" (contrast `fmtTupleGroup`, which keeps the closer flush
against the last item). When flat, renders `{ item, item }` (one space padding either side,
matching v1's `"\{ {body} }"` spelling). -/
def fmtBraceBlock (items : List Format) : Format :=
  Format.group (
    Format.text "{" ++ Format.nest defIndent (Format.line ++ fmtCommaGroup items)
      ++ Format.line ++ Format.text "}")

mutual
partial def fmtSurf (need : SPrec) : Surf → Format
  | .lit n   => Format.text (if n < 0 then s!"({n})" else toString n)   -- the tokenizer has no unary '-': defensive only
  | .var x   => Format.text x
  | .unitS   => Format.text "()"
  | .getS    => Format.text "get"
  | .thunk e => Format.text "{" ++ fmtSurf .cmp e ++ Format.text "}"
  | .force e => Format.text "$" ++ fmtSurf .atom e
  -- `let … in …` (D2/#68/#71): the CANONICAL form is ONE `let` block over the maximal run of
  -- sequential bindings — `collectLetRun` walks the `.lett`/`.lettMulti` chain starting here and
  -- flattens it to a single `x = e1; y = e2; … in body` block (operator ruling, 2026-07-10: #71
  -- resolved always-sugar). A run of exactly ONE binding prints as plain `let x = e in body` (no
  -- trailing `;`, matching every corpus program today) — `fmtLetRun` below picks the shape. This
  -- is why `.lett` and `.lettMulti` share ONE arm: a hand-written nested chain (`.lett` all the
  -- way down) and a sugar-parsed chain (starts `.lettMulti`, possibly followed by more `.lett`s
  -- from an enclosing `let..in` outside the sugar) print IDENTICALLY once flattened — the
  -- `lettMulti` MARKER's only remaining job is upstream (elaboration erases it before typing;
  -- semantics never depend on it), not printing: the canonicalization here is print-side only.
  | .lett x e b => fParenIf need .cmp (fmtLetRun (collectLetRun (.lett x e b)))
  | .lettMulti binds b => fParenIf need .cmp (fmtLetRun (collectLetRun (.lettMulti binds b)))
  | .lam x b    =>
      fParenIf need .cmp <|
        Format.group (Format.text s!"fun {x} =>" ++ nestD (Format.line ++ fmtSurf .cmp b))
  -- `f(a, b)`-style ctor calls print `f`+the tuple with NO space (`SCons(a, b)`), matching the corpus
  -- (`examples/tokenizer`'s `TCons(SNil, TNil)`). But `SCons(a, b)` is STILL structurally `f (a, b)` —
  -- one juxtaposed atom (`f`) then another (the parenthesized pair) — so it is `.app`-tier, NOT atomic:
  -- as an application ARGUMENT (`g SCons(a, b)`) it would re-tokenize as `g SCons (a, b)` = `(g SCons)
  -- (a, b)`, a DIFFERENT tree (found by the round-trip law over the string-stdlib/tokenizer corpus —
  -- the exact failure this comment documents). Must `fParenIf need .app` like plain application.
  | e@(.app f a)    =>
      -- STRING-LITERAL recovery (ADR-0074): a non-empty `SCons(Char n, …)` chain prints back as
      -- `"…"` — a pure print-side sugar, checked FIRST (before the general ctor-call/app cases).
      -- A genuine LITERAL is a true grammar ATOM (one token), so it never needs defensive parens.
      match asStringLit e with
      | some s => Format.text ("\"" ++ s ++ "\"")
      | none   =>
      match a with
      | .pairS a1 a2 =>
          let tuple := fmtTupleGroup "(" ")" [fmtSurf .cmp a1, fmtSurf .cmp a2]
          match isCtorHead f with
          | some n => fParenIf need .app (Format.text n ++ tuple)                          -- ctor-call: SCons(a, b)
          | none   => fParenIf need .app (fmtSurf .app f ++ Format.text " " ++ tuple)
      | _ => fParenIf need .app (Format.group (fmtSurf .app f ++ Format.line ++ fmtSurf .atom a))
  -- `raise`/`put`/`new`/`read`/`write` parse in APPLICATION position (`pApp`, atom arguments) — their
  -- own printed form IS an atom, so `need` may demand `.atom` and still print bare (`raise 7`, applied
  -- as `f (raise 7)`, needs parens the caller already supplies via `.app`'s arg tier). Their ARGUMENTS,
  -- though, are atom-tier (`pAtom`), so a non-atomic argument (e.g. `raise (let x = 3 in x)`) must be
  -- parenthesized — handled by printing the argument at `.atom` need, which the argument's own
  -- `fParenIf` resolves.
  | .raise e => fParenIf need .app (Format.text "raise " ++ fmtSurf .atom e)
  | .putS e   => fParenIf need .app (Format.text "put " ++ fmtSurf .atom e)
  | .newS e   => fParenIf need .app (Format.text "new " ++ fmtSurf .atom e)
  | .readS e  => fParenIf need .app (Format.text "read " ++ fmtSurf .atom e)
  | .writeS r w => fParenIf need .app (Format.text "write " ++ fmtSurf .atom r ++ Format.text " " ++ fmtSurf .atom w)
  -- `handle`/`atomically` parse a FULL expression body (`.refE` in `keywordRule`) at `pExpr` top level —
  -- unlike `raise`/`put`/…, they are NOT reachable from inside `pApp`'s atom slot without explicit
  -- parens, so their OWN printed form is loosest-tier (`.cmp`), parenthesizing whenever `need` is
  -- anything tighter (matches `.lett`/`.lam`/`.ifS`/`.matchS`/keyword forms below).
  | .handle e => fParenIf need .cmp (Format.text "handle " ++ fmtSurf .atom e)
  -- `state e0 in e` (D2, same `let … in` shape as `.lett`): break before `in`, body at BASE indent.
  | .stateS e0 e =>
      fParenIf need .cmp <|
        Format.group (nestD (Format.text "state " ++ fmtSurf .atom e0 ++ Format.line ++ Format.text "in")
          ++ Format.line) ++ fmtSurf .cmp e
  | .atomS e  => fParenIf need .cmp (Format.text "atomically " ++ fmtSurf .atom e)
  | .inlS e   => Format.text "Left(" ++ fmtSurf .cmp e ++ Format.text ")"
  | .inrS e   => Format.text "Right(" ++ fmtSurf .cmp e ++ Format.text ")"
  | .pairS a b => fmtTupleGroup "(" ")" [fmtSurf .cmp a, fmtSurf .cmp b]
  | .matchS s lx e1 rx e2 =>
      fParenIf need .cmp <|
        Format.text "match " ++ fmtSurf .atom s ++ Format.text " " ++
          fmtBraceBlock
            [ Format.text s!"Left({lx}) -> " ++ fmtSurf .cmp e1
            , Format.text s!"Right({rx}) -> " ++ fmtSurf .cmp e2 ]
  | .splitS a b p body =>
      fParenIf need .cmp <|
        Format.group (nestD (Format.text s!"let ({a}, {b}) = " ++ fmtSurf .cmp p ++ Format.line ++ Format.text "in")
          ++ Format.line) ++ fmtSurf .cmp body
  | .binopS op a b =>
      match op with
      | .lt | .eq => fParenIf need .cmp (Format.group (fmtSurf .add a ++ Format.text s!" {binOpTok op}" ++ Format.line ++ fmtSurf .add b))
      | .add | .sub => fParenIf need .add (Format.group (fmtSurf .add a ++ Format.text s!" {binOpTok op}" ++ Format.line ++ fmtSurf .mul b))
      | .mul | .div => fParenIf need .mul (Format.group (fmtSurf .mul a ++ Format.text s!" {binOpTok op}" ++ Format.line ++ fmtSurf .app b))
  -- `if c then t else e` (D2): break before `then`/`else`, arms nested +2.
  | .ifS c t e =>
      fParenIf need .cmp <|
        Format.group (
          Format.text "if " ++ fmtSurf .cmp c
            ++ nestD (Format.line ++ Format.text "then " ++ fmtSurf .cmp t
                        ++ Format.line ++ Format.text "else " ++ fmtSurf .cmp e))
  | .annotS e t => Format.text "(" ++ fmtSurf .cmp e ++ Format.text s!" : {showTy t})"
  | .foldS e   => Format.text "(fold " ++ fmtSurf .atom e ++ Format.text ")"                              -- INTERNAL; printed defensively
  | .unfoldS e => Format.text "(unfold " ++ fmtSurf .atom e ++ Format.text ")"                           -- INTERNAL; ditto
  -- `match s { arms }` (D2): break after `{`, one arm per line nested +2, `}` at base.
  | .matchD s arms =>
      fParenIf need .cmp <|
        Format.text "match " ++ fmtSurf .atom s ++ Format.text " " ++
          fmtBraceBlock (fmtDArmList arms)
  -- `withCapS`'s internal `kind` tag is `"throws"`/`"state"`/`"atomically"` (`lowerC`'s cap-binder
  -- names), but the SURFACE keyword for `"throws"` is `handle` (ADR-0072's `handle as h e`, not
  -- `throws as h e` — there is no `throws` keyword in the grammar). `"state"`/`"atomically"` already
  -- match their surface spelling. All three bodies are `.refE` (a full expression, `keywordRule`),
  -- so `body` prints at `.cmp`, matching `handle`/`atomically`/`state`.
  | .withCapS kind e0 h body =>
      fParenIf need .cmp <|
        if kind = "state" then
          Format.group (nestD (Format.text s!"state " ++ fmtSurf .atom e0 ++ Format.text s!" as {h}" ++ Format.line ++ Format.text "in")
            ++ Format.line) ++ fmtSurf .cmp body
        else if kind = "throws" then
          Format.text s!"handle as {h} " ++ fmtSurf .cmp body
        else
          Format.text s!"{kind} as {h} " ++ fmtSurf .cmp body
  -- ADR-0095 D1 (RULED): `handle e with Name as h { op(x) => body, … }` — a PLACEHOLDER clause
  -- print (`{ … }`, not the real per-clause rendering) since `fmtSurf` has no `HClauses` arm yet
  -- (round-trip fidelity for the clause LIST is implementation-lane follow-up, not this probe's
  -- scope); the OUTER shape matches the ruled grammar exactly so a printed `handle` at least
  -- re-parses to something structurally sane.
  | .handleCustomS _lbl n p? h cls body =>
      fParenIf need .cmp <|
        Format.text "handle " ++ fmtSurf .cmp body ++ Format.text " with " ++
          (match p? with
            | .none    => fmtSurf .atom n
            | .one p   => Format.text "(" ++ fmtSurf .atom n ++ Format.text " " ++ fmtSurf .atom p ++ Format.text ")"
            | .two _ _ => fmtSurf .atom n) ++
          Format.text s!" as {h} " ++ fmtBraceBlock (fmtHClauseList cls)
  -- `h.op(args)` is parsed by `pDotLoop`, invoked FROM `pDotted` right after `pAtom` — the whole
  -- chain result is itself an atom (feeds `pAppLoop`/`pOp` same as any other atom), so it never
  -- needs defensive parens even at `.atom` need.
  | .dotPerform recv op args =>
      match args with
      | .none      => fmtSurf .atom recv ++ Format.text s!".{op}"
      | .one a     => fmtSurf .atom recv ++ Format.text s!".{op}" ++ fmtTupleGroup "(" ")" [fmtSurf .cmp a]
      | .two a b   => fmtSurf .atom recv ++ Format.text s!".{op}" ++ fmtTupleGroup "(" ")" [fmtSurf .cmp a, fmtSurf .cmp b]
  | .letRecS f ty body b =>
      fParenIf need .cmp <|
        Format.group (nestD (Format.text s!"let rec {f} : {showTy ty} = " ++ fmtSurf .cmp body ++ Format.line ++ Format.text "in")
          ++ Format.line) ++ fmtSurf .cmp b
  | .divMark e => fmtSurf need e                                          -- INTERNAL marker; transparent to printing
/-- `.lettMulti`'s `;`-separated binding list (issue #68): `x = e1; y = e2; …`, ONE line, joined
by `; ` (not one-per-line — the whole point of the sugar is compactness; contrast the EXPANDED
`.lett` chain's one-`let..in`-per-line convention above). -/
partial def fmtLetBindings : LetBindings → Format
  | .nil               => Format.nil
  | .cons n e .nil      => Format.text s!"{n} = " ++ fmtSurf .cmp e
  | .cons n e rest      => Format.text s!"{n} = " ++ fmtSurf .cmp e ++ Format.text "; " ++ fmtLetBindings rest
/-- The PLAIN-`List`-taking sibling of `fmtLetBindings`, over `collectLetRun`'s flattened output
(a `List (String × Surf)`, not the `LetBindings` mutual-inductive — repacking into `LetBindings`
just to print would be a needless round-trip through a SEPARATE representation of the same list). -/
partial def fmtLetBindingsList : List (String × Surf) → Format
  | []            => Format.nil
  | [(n, e)]      => Format.text s!"{n} = " ++ fmtSurf .cmp e
  -- `"; "` THEN `Format.line` (not a bare `"; "`) gives the pretty-printer a real break point
  -- BETWEEN bindings: when the whole block fits `defWidth`, `Format.line` renders as a single
  -- space (the flat case) and the block stays one line; when it doesn't, EVERY `;` becomes its
  -- own line (falling back to one-binding-per-line) INSTEAD of letting the printer break inside
  -- some binding's own value expression at an arbitrary, hard-to-read point (the bug this fixes —
  -- found by reformatting examples/json + examples/parser-combinators, whose long chains
  -- collapsed to unreadable mid-expression wraps before this fix).
  | (n, e) :: rest => Format.text s!"{n} = " ++ fmtSurf .cmp e ++ Format.text ";" ++ Format.line ++ fmtLetBindingsList rest
/-- Flatten a MAXIMAL run of sequential `let`-bindings starting at `s` — walking THROUGH both
`.lett` (a hand-written chain) and `.lettMulti` (an already-sugared sub-chain, e.g. nested inside
a bigger hand-written one) uniformly, since the canonical OUTPUT (#71, operator ruling 2026-07-10)
treats them identically: one block, regardless of how the input was written. Stops at the first
non-`let`-shaped node, which becomes the run's BODY. `.lettMulti`'s own bindings splice in as
ordinary list elements (its `LetBindings` shape is converted once via a local unpack, not a second
recursive walker) so a `.lett`-then-`.lettMulti`-then-`.lett` chain (hand-written wrapping already-
sugared wrapping hand-written — a real shape once fmt itself starts EMITTING sugar) flattens to
ONE run, not three separate ones. -/
partial def collectLetRun : Surf → List (String × Surf) × Surf
  | .lett n e b =>
      let (rest, body) := collectLetRun b
      ((n, e) :: rest, body)
  | .lettMulti binds b =>
      let rec unpack : LetBindings → List (String × Surf)
        | .nil           => []
        | .cons n e rest => (n, e) :: unpack rest
      let (restAfter, body) := collectLetRun b
      (unpack binds ++ restAfter, body)
  | s => ([], s)
/-- Print a flattened let-run: `n = 0` bindings is unreachable (a run always has ≥1, since
`collectLetRun` is only ever called from a `.lett`/`.lettMulti` node — both guarantee at least one
binding), `n = 1` prints PLAIN `let x = e in body` (matching every corpus program today — no
trailing `;`, so a single ordinary `let` is visually unchanged from pre-#71 output), `n ≥ 2` prints
the ONE-BLOCK canonical form (#71): `let x = e1; y = e2; … in body`. -/
partial def fmtLetRun : List (String × Surf) × Surf → Format
  | ([(n, e)], body) =>
      Format.group (nestD (Format.text s!"let {n} = " ++ fmtSurf .cmp e ++ Format.line ++ Format.text "in")
        ++ Format.line) ++ fmtSurf .cmp body
  | (binds, body) =>
      Format.group (nestD (Format.text "let " ++ fmtLetBindingsList binds ++ Format.line ++ Format.text "in")
        ++ Format.line) ++ fmtSurf .cmp body
/-- One `matchD` arm as a `Format` document (no trailing separator — `fmtCommaGroup`'s `joinSep`
supplies `,` + line between arms, matching D2's "one arm per line"). -/
partial def fmtDArm : String → List String → Surf → Format
  | c, [], b    => Format.text s!"{c} -> " ++ fmtSurf .cmp b
  | c, bs, b    => Format.text s!"{c}({String.intercalate ", " bs}) -> " ++ fmtSurf .cmp b
partial def fmtDArmList : DArms → List Format
  | .nil            => []
  | .cons c bs b rest => fmtDArm c bs b :: fmtDArmList rest
/-- ADR-0095 D1: one custom-handle clause `op(x) => body`, the `fmtDArm` precedent (D3's `=>`
arrow, not `->`). -/
partial def fmtHClause : String → String → Surf → Format
  | op, x, b => Format.text s!"{op}({x}) => " ++ fmtSurf .cmp b
partial def fmtHClauseList : HClauses → List Format
  | .nil               => []
  | .cons op x b rest  => fmtHClause op x b :: fmtHClauseList rest
end

/-- Top-level entry: an expression prints at the loosest tier (no defensive outer parens), rendered
through the ONE canonical width (`render`, `defWidth`/`defIndent`). PUBLIC (#60 seam): reused by
`TypeCheck.lawInstancesOf` to render a discovered law's body back to source text — additive
visibility only, no behavior change. -/
public def showSurf (e : Surf) : String := render (fmtSurf .cmp e)

/-! ## 4. Declaration + program printer

`data`/`trait`/`impl` bodies (D2): one ctor/op/clause per line when the decl doesn't fit,
`|`/`;` at line starts. Declarations are ALWAYS top-level (never nested inside an expression), so
their groups render relative to column 0 — `nestD` gives the +2 D2 asks for on the wrapped lines. -/

def fmtCtors : List (String × List Ty) → String
  | []              => ""
  | [(c, [])]       => c
  | [(c, ts)]       => s!"{c}({String.intercalate ", " (ts.map showTy)})"
  | (c, []) :: rest => s!"{c} | {fmtCtors rest}"
  | (c, ts) :: rest => s!"{c}({String.intercalate ", " (ts.map showTy)}) | {fmtCtors rest}"

/-- `data`'s ctor list as a `Format` list — one ctor per element, `|` prefixed on every element
AFTER the first so `fmtCommaGroup`-style `joinSep` can space/break it uniformly (D2: `|` at line
starts on the wrapped form). -/
def fmtCtorDoc : (String × List Ty) → Format
  | (c, [])  => Format.text c
  | (c, ts)  => Format.text s!"{c}({String.intercalate ", " (ts.map showTy)})"

def fmtCtorList (cs : List (String × List Ty)) : Format :=
  Format.group (Format.joinSep (cs.map fmtCtorDoc) (Format.line ++ Format.text "| "))

def fmtOpSig (s : OpSig) : String :=
  if s.params.isEmpty then s!"fn {s.name} : {showTy s.methodTy}"
  else s!"fn {s.name}({String.intercalate ", " s.params}) -> {showTy s.retTy}"

def fmtLawDecl (l : LawDecl) : String :=
  s!"law {l.name}({String.intercalate ", " l.params}): {showSurf l.body}"

def fmtOpDef (d : OpDef) : String :=
  s!"fn {d.name}({String.intercalate ", " d.params}) = {showSurf d.body}"

/-- One `effect` op signature (ADR-0092 D1) — `name : Ty`, the exact source shape `pEffectMembers`
parses (no `fn`/params-list wrapper, unlike a trait op). -/
def fmtEffectOp (op : String × Ty) : String :=
  s!"{op.1} : {showTy op.2}"

/-- `trait`/`impl` member lists (D2): one member per line when the decl doesn't fit, `;` at line
starts (matching the flat separator's own `"; "` token — only the BREAK point differs). Uses the
same wrap-block shape as `fmtBraceBlock`, with `;` in place of `,` as the join token. -/
def fmtMemberBlock (members : List String) : Format :=
  let sep : Format := ";" ++ Format.line
  Format.group (
    Format.text "{" ++ Format.nest defIndent (Format.line ++ Format.joinSep (members.map Format.text) sep)
      ++ Format.line ++ Format.text "}")

/-- One declaration — flat when it fits in `defWidth`, one member/ctor per line (D2) when it
doesn't. `data`/`trait`/`impl` bodies use `fmtCtorList`/`fmtMemberBlock` (the D2 multi-line decl
shape); `fnD` is comment-free canonical rendering (comments are not part of `Surf`/`Decl`,
ADR-0046: the surface has no semantics of its own beyond its elaboration, and a comment carries
none, so it is out of scope for this AST-driven printer). -/
def fmtDeclDoc : Decl → Format
  | .dataD n ps cs   =>
      let params := if ps.isEmpty then "" else " " ++ String.intercalate " " ps
      Format.text s!"data {n}{params} = " ++ fmtCtorList cs
  | .traitD n ps ops laws =>
      let params := if ps.isEmpty then "" else " " ++ String.intercalate " " ps
      let body := (ops.map fmtOpSig) ++ (laws.map fmtLawDecl)
      Format.text s!"trait {n}{params} " ++ fmtMemberBlock body
  | .implD n t ops   =>
      Format.text s!"impl {n} for {showTy t} " ++ fmtMemberBlock (ops.map fmtOpDef)
  | .fnD n ps ty tr tv body =>
      Format.group (nestD (
        Format.text s!"fn {n}({String.intercalate ", " ps}) : {showTy ty} where {tr} {tv} ="
          ++ Format.line ++ fmtSurf .cmp body))
  | .effectD n ops =>    -- ADR-0092 D1: `effect N { op1 : ArgTy -> ResTy, … }` — same member-block
                          -- shape as trait/impl (D2's flat-vs-wrapped rule applies uniformly).
      Format.text s!"effect {n} " ++ fmtMemberBlock (ops.map fmtEffectOp)
  | .letD n ty e =>       -- ADR-0093 D5 (operator ruling): `let name [: Ty] = expr` — NO trailing
                          -- `in`, the one visible difference from the ordinary `let`/EXPRESSION
                          -- printer. The OPTIONAL ascription (ruling point (c)) prints only when
                          -- present — an omitted one round-trips to `none` either way (Surface.lean).
      let head := match ty with
        | some t => s!"let {n} : {showTy t} ="
        | none   => s!"let {n} ="
      Format.group (nestD (Format.text head ++ Format.line ++ fmtSurf .cmp e))
  | .letRecD n t e =>     -- `let rec name : T = expr` — the recursive sibling, same no-`in` shape.
      Format.group (nestD (Format.text s!"let rec {n} : {showTy t} =" ++ Format.line ++ fmtSurf .cmp e))

def fmtDecl (d : Decl) : String := render (fmtDeclDoc d)

/-- One `import name` line (ADR-0093 D1). -/
def fmtImport (i : ImportDecl) : Format := Format.text s!"import {i.modName}"

/-- One `use name (a, b, C)` line (ADR-0093 D2). -/
def fmtUse (u : UseDecl) : Format :=
  Format.text s!"use {u.modName} ({String.intercalate ", " u.names})"

/-- One decl, `pub`-prefixed iff its name is in `pubNames` (ADR-0093 D3) — `pubNames` is a flat
set on `Prog`, not a per-`Decl` field (see `Prog.pubNames`'s doc comment), so the printer
re-attaches the prefix here rather than `fmtDeclDoc` carrying it. -/
def fmtDeclPub (pubNames : List String) (d : Decl) : Format :=
  if pubNames.contains d.name then Format.text "pub " ++ fmtDeclDoc d else fmtDeclDoc d

/-- A whole program: the `import`/`use` header (ADR-0093 D1/D2), then each decl on its own line
(`pub`-prefixed per D3), then the body expression. Matches every `examples/*/main.bang` today
(`data …` / `let rec …` lines followed by the body). Declarations are separated by HARD newlines
(`Format.line` inside a `group` would let them share a line if they fit — decls are always meant
one-per-line, so this uses literal `"\n"` text exactly as v1's `String.intercalate` did, preserved
unchanged since D2 does not name declaration SEPARATION as a group/break point, only each decl's
OWN internal layout). A library-mode program (D5: decls-only, placeholder `.lit 0` body) prints
its header+decls only — `Main.lean`'s entry-mode detection decides whether a bare `0` is real,
not this printer; re-parsing that output still round-trips to the SAME `Prog` either way.

`public` (#81): `fmtProg` below (this module) and `Bang.Rewrite`'s `fmt`/`rename` rewrites
(`Bang/Frontend/Rewrite.lean`) both render a `Prog` through this ONE function, so a rewrite
verb's diff and `bang fmt`'s own output stay visually consistent. CAVEAT unchanged from before
`public`: `Main.lean`'s resolver-aware `bang check` (ADR-0093 follow-up ruling) was tried against
a print-then-reparse of a RESOLVER-MERGED `Prog` through this function and found UNSOUND
(`applyEntryRule`'s synthesized `body := Surf.var "main"` prints as a bare trailing atom
immediately after a `main`-decl ending in one, which re-tokenizes as ONE application) —
`bang check`/`run` instead call `TypeCheck.checkAndLowerProg` directly on the `Prog`, never
re-stringifying. `Bang.Rewrite`'s CLI wiring (`Main.lean`'s `runRewriteFmt`/`runRewriteRename`)
is SINGLE-FILE only (no resolver path, matching `rename`'s own "requires a file, no multi-file
route" scope) — a caller reaching this function through a resolver-merged `Prog` still
inherits the SAME unsoundness this caveat names; a pre-existing, documented v1 ceiling, not a
new one #81 introduces. -/
public def showProg (p : Prog) : String :=
  let headerDocs := (p.imports.map fmtImport) ++ (p.uses.map fmtUse)
  let declDocs := p.decls.map (fmtDeclPub p.pubNames)
  -- `p.isLibrary` ⟹ `p.body` is the UNOBSERVABLE `.lit 0` placeholder (D5's third case) — printing
  -- it would append a REAL trailing `0` a re-parse cannot tell apart from the placeholder, and
  -- worse, a bare-atom-ending decl (`let main = 42`) would swallow that `0` as an APPLICATION
  -- argument (the SAME literal-adjacency ambiguity the `fn`-body corpus already works around) —
  -- so a genuine library file prints its header + decls ONLY, matching what it parsed FROM.
  let tailDocs := if p.isLibrary then [] else [fmtSurf .cmp p.body]
  render (Format.joinSep (headerDocs ++ declDocs ++ tailDocs) (Format.text "\n"))

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

/-- Round-trip: formatting never changes the MEANING of the parsed program — `parse (fmt (parse
s))` and `parse s` erase (`eraseLettMultiProg`) to the SAME `Prog`, stated over the erased form
(`DecidableEq`-derived, so `==` is real equality). Erasure, not raw structural equality (issue
#71, operator ruling 2026-07-10): the canonical-form printer COLLAPSES a hand-written nested
`let..in` chain into the ONE-BLOCK `;`-sugar form, so the two ASTs genuinely differ in RAW SHAPE
(`.lett` chain vs `.lettMulti`) while remaining semantically identical — `eraseLettMultiProg`
(`Bang.Surface`) is exactly the normalization that makes "round-trips" mean "same meaning," not
"byte-identical tree," matching how it already erases the marker before typing/lowering ever run.
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
          | .ok p1 => Bang.Surface.eraseLettMultiProg p0 == Bang.Surface.eraseLettMultiProg p1

/-- Canonicity: two DIFFERENT source strings that parse to the SAME AST must format to the SAME
output — the operational meaning of "canonical" (ADR-0090's D2 preamble: the multi-line shape is
a pure function of the AST, no input-format influence). `false` if either fails to parse, or if
they parse to different ASTs (not what this predicate is testing), or if their formatted outputs
differ. -/
def canonicalOn (src1 src2 : String) : Bool :=
  match parseProg src1, parseProg src2 with
  | .ok p1, .ok p2 =>
      if p1 != p2 then false else
      match fmtProg src1, fmtProg src2 with
      | .ok out1, .ok out2 => out1 == out2
      | _, _ => false
  | _, _ => false

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

/-! ## 8. Multi-line layout guards (ADR-0090) — flat-when-fits, breaks-when-not, canonicity

D4 requires the two laws above to extend unchanged to multi-line output (checked by the corpus
`#guard`s just above, all still passing with the new `Std.Format`-based printer). These NEW guards
additionally pin the LAYOUT itself: a program that fits `defWidth` stays ONE line (`group`
semantics), a program that doesn't gets the D2 canonical multi-line shape (pinned byte-for-byte so
a layout regression shows as a diff here), and two differently-formatted inputs parsing to the same
AST must format to the IDENTICAL output (canonicity — what "canonical" operationally means). -/

-- flat-when-fits: `examples/state/main.bang`'s program easily fits `defWidth := 100` on one line —
-- multi-line layout must not introduce a break where the flat printer had none. (The `let c`/`let
-- z` chain is now ONE canonical block, issue #71 — collapsing applies inside `state … in` bodies
-- exactly like everywhere else.)
open Bang.Format in
#guard fmtProg "state 0 in let c = {get} in let z = put 5 in $c"
       == .ok "state 0 in let c = {get}; z = put 5 in $c"

-- a long let-chain (each RHS individually short, but the CHAIN as a whole exceeds `defWidth`) must
-- break — now ONE canonical block (issue #71): every binding gets its OWN line (matching D2's
-- "flat sequence" convention, one binding per line, rather than one `let … in` per binding
-- staircasing). `fmtLetBindingsList` puts a `Format.line` (not a bare `"; "`) between bindings so
-- the pretty-printer has a REAL break point there — without it, a too-wide block breaks inside
-- some binding's OWN value expression at an arbitrary point instead (the bug this fixes; found
-- reformatting examples/json + examples/parser-combinators, whose long chains collapsed to
-- unreadable mid-expression wraps before it). Expected string pinned byte-for-byte against
-- `defWidth := 100`.
open Bang.Format in
#guard fmtProg "let aVeryLongVariableName1 = 111111111 in let aVeryLongVariableName2 = 222222222 in let aVeryLongVariableName3 = 333333333 in aVeryLongVariableName1 + aVeryLongVariableName2 + aVeryLongVariableName3"
       == .ok "let aVeryLongVariableName1 = 111111111;\n  aVeryLongVariableName2 = 222222222;\n  aVeryLongVariableName3 = 333333333\n  in\naVeryLongVariableName1 + aVeryLongVariableName2 + aVeryLongVariableName3"

-- idempotency + round-trip must ALSO hold on the wide let-chain above (the load-bearing case: a
-- break-decision that depended on input line-structure, not width+AST, would show up here first).
open Bang.Format in
#guard roundTripsOn "let aVeryLongVariableName1 = 111111111 in let aVeryLongVariableName2 = 222222222 in let aVeryLongVariableName3 = 333333333 in aVeryLongVariableName1 + aVeryLongVariableName2 + aVeryLongVariableName3"
       && idempotentOn "let aVeryLongVariableName1 = 111111111 in let aVeryLongVariableName2 = 222222222 in let aVeryLongVariableName3 = 333333333 in aVeryLongVariableName1 + aVeryLongVariableName2 + aVeryLongVariableName3"

-- a wide `match` (arms individually short, whole group exceeds `defWidth`) breaks after `{`, one
-- arm per line nested +2, `}` at base — D2's match shape.
open Bang.Format in
#guard fmtProg "match Right(777777777) { Left(aVeryLongBindingName) -> aVeryLongBindingName + 1111111111, Right(anotherLongBindingName) -> anotherLongBindingName + 2222222222 }"
       == .ok "match Right(777777777) {\n  Left(aVeryLongBindingName) -> aVeryLongBindingName + 1111111111,\n  Right(anotherLongBindingName) -> anotherLongBindingName + 2222222222\n}"

-- canonicity: two DIFFERENTLY-FORMATTED source strings (one hand-wrapped multi-line, one
-- collapsed to a single line) that parse to the SAME `Prog` must format to the SAME output — the
-- operational definition of "canonical" (D2 preamble: the shape is a pure function of the AST, no
-- input-format influence). Uses the wide let-chain from above, re-written with different manual
-- line breaks/indentation on the source side.
open Bang.Format in
#guard canonicalOn
  "let aVeryLongVariableName1 = 111111111 in let aVeryLongVariableName2 = 222222222 in let aVeryLongVariableName3 = 333333333 in aVeryLongVariableName1 + aVeryLongVariableName2 + aVeryLongVariableName3"
  "let aVeryLongVariableName1 = 111111111 in\n  let aVeryLongVariableName2 = 222222222 in\n    let aVeryLongVariableName3 = 333333333\n      in aVeryLongVariableName1 + aVeryLongVariableName2\n         + aVeryLongVariableName3"

-- canonicity, flat case: two differently-SPACED single-line inputs of the small `state` program
-- above must ALSO agree (the flat-when-fits path is canonical too, not just the multi-line path).
open Bang.Format in
#guard canonicalOn
  "state 0 in let c = {get} in let z = put 5 in $c"
  "state  0   in  let c = { get }  in  let  z  =  put  5  in  $c"

-- `effect` decls (ADR-0092 D1): a single-op interface round-trips + idempotent, same member-block
-- shape as trait/impl.
open Bang.Format in
#guard roundTripsOn "effect Net { read : Int -> Int } 0" && idempotentOn "effect Net { read : Int -> Int } 0"
-- a multi-op effect, comma-separated in source, round-trips too (the parser's `,`/`;` separators
-- are both accepted on input; the printer picks ONE canonical join token — zero-config, D2's own
-- "gofmt precedent, no options" carried over from Format.lean's original design).
open Bang.Format in
#guard roundTripsOn "effect Net { read : Int -> Int, write : Int -> Unit } 0"
       && idempotentOn "effect Net { read : Int -> Int, write : Int -> Unit } 0"
-- a 0-ary op (a bare result type, no arrow) round-trips too.
open Bang.Format in
#guard roundTripsOn "effect Ping { ping : Int } 0" && idempotentOn "effect Ping { ping : Int } 0"
-- MULTIPLE effect decls in one program (label-allocation-relevant — the printer must preserve
-- DECL ORDER, since ADR-0092 D1's label allocation is order-dependent; a printer that silently
-- reordered decls would be a SILENT source-of-truth change, not just a style choice).
open Bang.Format in
#guard roundTripsOn "effect Net { read : Int -> Int } effect Db { query : Int -> Int } 0"
       && idempotentOn "effect Net { read : Int -> Int } effect Db { query : Int -> Int } 0"
-- a WIDE effect (op count forces the multi-line member-block wrap, D2's break rule) round-trips +
-- idempotent too — the same falsification concern the wide let-chain/match cases above test for.
open Bang.Format in
#guard roundTripsOn
  "effect BigNet { readOp : Int -> Int, writeOp : Int -> Int, queryOp : Int -> Int, pingOp : Int -> Int, closeOp : Int -> Int } 0"
       && idempotentOn
  "effect BigNet { readOp : Int -> Int, writeOp : Int -> Int, queryOp : Int -> Int, pingOp : Int -> Int, closeOp : Int -> Int } 0"

-- ADR-0093 D1/D2/D3: `import`/`use`/`pub` round-trip + are idempotent.
open Bang.Format in
#guard roundTripsOn "import tokenizer 0" && idempotentOn "import tokenizer 0"
open Bang.Format in
#guard roundTripsOn "use tokenizer (lex, Token) 0" && idempotentOn "use tokenizer (lex, Token) 0"
-- both header forms, several of each, preserve ORDER (import-then-use here; the printer emits
-- imports before uses regardless of source interleaving — see the falsification note below).
open Bang.Format in
#guard roundTripsOn "import a import b use c (d, e) 0" && idempotentOn "import a import b use c (d, e) 0"
-- `pub` round-trips on every decl kind it can prefix.
open Bang.Format in
#guard roundTripsOn "pub data Json = JNull" && idempotentOn "pub data Json = JNull"
open Bang.Format in
#guard roundTripsOn "pub effect Net { read4 : Int -> Int } 0" && idempotentOn "pub effect Net { read4 : Int -> Int } 0"
-- a MIX of pub and private decls in one program preserves each decl's OWN visibility (the printer
-- must not leak `pub` onto a private neighbor, nor drop it from the one that has it).
open Bang.Format in
#guard roundTripsOn "pub data Json = JNull data Hidden = HNull 0"
       && idempotentOn "pub data Json = JNull data Hidden = HNull 0"
-- header + pub decls + body compose end-to-end (the split-json shape this ADR exists to enable).
open Bang.Format in
#guard roundTripsOn "import a use b (c) pub data Json = JNull 0"
       && idempotentOn "import a use b (c) pub data Json = JNull 0"

-- ADR-0093 D5 (operator ruling): top-level `let`/`let rec` DECLS round-trip + are idempotent —
-- the general binding form subsuming both plain-function exports and `main`.
open Bang.Format in
#guard roundTripsOn "let x = 3 data Hidden = HNull 0" && idempotentOn "let x = 3 data Hidden = HNull 0"
open Bang.Format in
#guard roundTripsOn "let rec f : Int -> Int = fun n => n data Hidden = HNull 0"
       && idempotentOn "let rec f : Int -> Int = fun n => n data Hidden = HNull 0"
-- `pub let`/`pub let rec` round-trip too (D3's uniform `pub` machinery over the new decl kind).
open Bang.Format in
#guard roundTripsOn "pub let x = 3 data Hidden = HNull 0" && idempotentOn "pub let x = 3 data Hidden = HNull 0"
-- `main` is just a `let` decl now — no special form, so it round-trips through the SAME guard.
open Bang.Format in
#guard roundTripsOn "let main = 42" && idempotentOn "let main = 42"
-- the OPTIONAL type ascription on plain `let` (D5 ruling point (c)) round-trips too.
open Bang.Format in
#guard roundTripsOn "let x : Int = 3" && idempotentOn "let x : Int = 3"

/-! ### Multi-binding `let` — the CANONICAL FORM (issues #68/#71, operator ruling 2026-07-10):
fmt renders every MAXIMAL RUN of sequential `let`-bindings as ONE `let x = e1; y = e2 in body`
block, regardless of how the input was written — a sugar-parsed `.lettMulti` block prints as
itself; a hand-written nested `.lett` chain COLLAPSES into the identical block. `n = 1` stays
plain `let x = e in body` (no trailing `;`). The `.lettMulti` MARKER (`Bang.Surface`) still exists
and is still what makes any of this possible (a sugar-parsed tree carries provenance a hand-
written one never does), but its role changed from "the printer's ONLY output-shape decision" to
"upstream-only" (elaboration erases it before typing/lowering) — canonicalization is now a
PRINT-SIDE pass (`collectLetRun`/`fmtLetRun`) that treats both shapes uniformly. -/

-- round-trips + idempotent, same as every other decl-level form above. `roundTripsOn` compares
-- via `eraseLettMultiProg` (semantic equivalence), not raw structural equality — the collapse
-- deliberately changes a hand-written chain's RAW AST shape (`.lett` chain → `.lettMulti`) while
-- preserving MEANING, so a byte-for-byte `Prog` comparison would (incorrectly) call that a
-- round-trip failure.
open Bang.Format in
#guard roundTripsOn "let x = 3; y = 4 in x + y" && idempotentOn "let x = 3; y = 4 in x + y"
open Bang.Format in
#guard roundTripsOn "let a = 1; b = 2; c = 3 in a" && idempotentOn "let a = 1; b = 2; c = 3 in a"

-- sugar-parsed input prints as sugar…
open Bang.Format in
#guard fmtExpr "let x = 3; y = 4 in x + y" == .ok "let x = 3; y = 4 in x + y"
-- … AND a HAND-WRITTEN nested chain COLLAPSES to the IDENTICAL one-block canonical form — the two
-- INPUT spellings converge on ONE output (canonicity: same meaning ⟹ same printed form).
open Bang.Format in
#guard fmtExpr "let x = 3 in let y = 4 in x + y" == .ok "let x = 3; y = 4 in x + y"
-- a run nested INSIDE another construct (not just at a program's top level) also collapses —
-- the printer walks to the `.lett`/`.lettMulti` wherever it occurs, not only at `fmtSurf`'s
-- outermost call.
open Bang.Format in
#guard fmtExpr "state 0 in (let c = {get} in (let z = put 5 in $c))" == .ok "state 0 in let c = {get}; z = put 5 in $c"

-- SEMANTICS RIDER (operator's explicit ask, 2026-07-10): does the collapse stay safe when a
-- chain SHADOWS — a later binding reusing an EARLIER binding's name? Verified empirically (not
-- assumed) that this codebase's grammar/elaborator impose NO duplicate-name restriction on the
-- `;`-block form (`pLetBindings` accepts any identifier, `desugarLettMulti`'s nesting preserves
-- sequential scoping exactly like a hand-written chain does), so the collapse is safe for EVERY
-- case tried — no exception was needed, unlike the operator's cautious hypothesis. These pin that
-- finding as a permanent regression, not just a one-off manual check.
#guard Bang.Surface.runYieldsInt 20 "let x = 1 in let x = 2 in x" 2
#guard Bang.Surface.runYieldsInt 20 "let x = 1; x = 2 in x" 2
-- a LATER same-named binding's RHS reading the EARLIER one (`x = x + 1`) — the sharpest version
-- of "does shadowing actually work", not just "does the later value win".
#guard Bang.Surface.runYieldsInt 20 "let x = 1 in let x = x + 1 in x" 2
#guard Bang.Surface.runYieldsInt 20 "let x = 1; x = x + 1 in x" 2
open Bang.Format in
#guard fmtExpr "let x = 1 in let x = x + 1 in x" == .ok "let x = 1; x = x + 1 in x"
open Bang.Format in
#guard roundTripsOn "let x = 1 in let x = x + 1 in x" && idempotentOn "let x = 1 in let x = x + 1 in x"
