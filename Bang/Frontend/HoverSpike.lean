/-
  Bang/Frontend/HoverSpike.lean — issue #52 design-probe SPIKE: decl-granularity hover.
  ──────────────────────────────────────────────────────────────────────────────────
  Minimal vertical proving the recommended #52 shape composes, WITHOUT touching `Surf` or the
  `P`-combinator signature (see `docs/notes/spanned-surf-design.md`). It answers "what decl is at
  line:col, and what is its type" — the `bang query` `refs`/hover ceiling documented at
  `docs/reference/language.md:699` ("position-addressing is OUT of v1, gated on #52's Spanned-Surf
  tier — `Surf` carries no per-node span today").

  THE SHAPE: reuse `tokenizeSpanned` (already landed, `ff49adb`) to locate each top-level decl's
  NAME TOKEN, then answer a cursor query by nearest-enclosing-decl (the span between one decl's
  name token and the next's, inclusive of everything in between — body, signature, the lot). This
  is coarser than a genuine per-node `Surf` span (a cursor inside decl `f`'s body resolves to `f`'s
  WHOLE type, not the exact sub-expression's), but it is the entire ADDITIVE cost of this spike:
  zero changes to `Surf`, zero changes to `P`, reusing `declFactOf`'s existing per-decl type
  machinery. This is Slice 1 of the migration order in the design note.

  Scoped, ADDITIVE, spike-only (not wired into `Main.lean`/the CLI — that is the implementation
  session's job, once the design note's slice map is accepted). LEAF: reads only the already-public
  `Bang.Surface`/`Bang.Query` surface, adds no checking.
-/
module

meta import Bang.Frontend.Query
public import Bang.Frontend.Query

open Bang Bang.Surface Bang.Query

namespace Bang.HoverSpike

/-- Is position `(line, col)` at-or-after the START of span `sp` (`sp`'s own start, 1-based,
half-open convention matching `Span` itself)? Used to find the LAST decl whose name token starts
at-or-before the cursor — the "nearest enclosing decl by name-token order" rule. -/
def atOrAfter (line col : Nat) (sp : Span) : Bool :=
  line > sp.line || (line == sp.line && col >= sp.col)

#guard atOrAfter 1 5 ⟨1, 5, 1, 6⟩
#guard atOrAfter 1 6 ⟨1, 5, 1, 6⟩
#guard ! atOrAfter 1 4 ⟨1, 5, 1, 6⟩
#guard atOrAfter 2 1 ⟨1, 5, 1, 6⟩

/-- One decl's hover-relevant fact: its name, the `Span` of its NAME TOKEN (the anchor a cursor
query compares against), and its rendered `type ! row` (or the checker's error, mirroring
`DeclFact`). -/
structure HoverFact where
  name : String
  nameSpan : Span
  typeStr : Option String
  typeError : Option String
  deriving Repr

/-- Every top-level decl's `HoverFact`, in SOURCE ORDER — `locateToken` finds each decl's OWN name
occurrence by construction (the FIRST occurrence of that string in `src`; a name that also occurs
earlier as some OTHER token's text — e.g. a decl literally named the same as a keyword-adjacent
string — is the same honest-approximation caveat `locateInMsg` already documents and accepts for
Stage B). `none` (decl's name has no locatable token — should not happen for a real parse, since
the decl was parsed FROM this exact source) is filtered out rather than guessed. -/
def hoverFactsOf (src : String) (p : Prog) : List HoverFact :=
  p.decls.filterMap (fun d =>
    (locateToken src d.name).map (fun sp =>
      let fact := declFactOf p d
      { name := d.name, nameSpan := sp, typeStr := fact.type, typeError := fact.typeError }))

/-- Render one `HoverFact` as the hover string a user/agent reads: `"name : type ! row"` for a
value-typed decl that checks, `"name : <error msg>"` when it doesn't, `"name"` bare for a
non-value decl (`trait`/`data`/`effect`/`impl` — `DeclFact.type`/`typeError` both `none`, same
`declFactOf` convention `dump`'s schema documents). -/
def HoverFact.render (f : HoverFact) : String :=
  match f.typeStr, f.typeError with
  | some t, _ => s!"{f.name} : {t}"
  | none, some e => s!"{f.name} : <error: {e}>"
  | none, none => f.name

/-- THE SPIKE ENTRY POINT: hover at `(line, col)` in `src` — the nearest-enclosing decl (the LAST
decl, in source order, whose name-token START is at-or-before the cursor), rendered. `none` when
the cursor sits before every decl's name (e.g. inside the `import`/`use` header, or the file is
empty) — an honest miss, not a guess at the wrong decl. Composes exactly the two landed #52
pieces: `tokenizeSpanned`/`locateToken` (Stage A's span substrate) and `declFactOf` (the `bang
query` per-decl type substrate, #80) — no new checking, no `Surf` change. -/
def hoverAt (src : String) (line col : Nat) : Option String := do
  let p ← Bang.Surface.parseProg src |>.toOption
  let facts := hoverFactsOf src p
  let candidates := facts.filter (fun f => atOrAfter line col f.nameSpan)
  -- last candidate in source order = nearest enclosing (decls are source-ordered, `declFactsOf`'s
  -- own documented invariant) — `List.getLast?` over the filtered prefix.
  (candidates.getLast?).map HoverFact.render

/-! ### `#guard`s — the spike's evidence.

Each expected string is either a structural fact (span position) or the value-typed render, which
mirrors `declFactOf`'s own already-`#guard`-pinned `typeStringOfDecl` behaviour (Query.lean) — no
new checker behaviour is introduced here, so these are read off the SAME rendering `bang query
type` already produces, not independently guessed. -/

-- SINGLE decl, cursor INSIDE its body: resolves to that decl, typed.
#guard hoverAt "let x = 3\nlet main = x + 1" 2 5 == some "main : Int"
-- cursor on the DECL'S OWN name token.
#guard hoverAt "let x = 3\nlet main = x + 1" 1 5 == some "x : Int"
-- cursor BEFORE any decl name (column 1 line 1 is `let`, before `x` at col 5) still resolves
-- to `x` — `let`/keyword text itself is never a candidate span, so "before the keyword" and
-- "before the name" agree here; the true miss case is exercised below.
#guard hoverAt "let x = 3\nlet main = x + 1" 1 1 == none

-- TWO decls: a cursor between them resolves to the EARLIER one (nearest enclosing, not nearest
-- overall) — the coarse decl-granularity approximation this spike is honest about.
#guard hoverAt "let a = 1\nlet b = 2" 1 8 == some "a : Int"
#guard hoverAt "let a = 1\nlet b = 2" 2 5 == some "b : Int"

-- a decl that FAILS to type-check renders its error, not a type (mirrors `declFactOf`'s
-- `typeError` branch — no new checker behaviour). `x : Unit = 3` mismatches its ascription;
-- `HoverFact.render` wraps the checker's own message in `<error: …>`.
#guard (match hoverAt "let x : Unit = 3\nlet main = 1" 1 5 with
        | some s => (s.splitOn "<error:").length > 1
        | none   => false)

-- a NON-VALUE decl (`data`) renders bare (no `type`/`typeError` — `DeclFact`'s documented
-- convention for trait/data/effect/impl).
#guard hoverAt "data Pair = P(Int, Int)\nlet main = 1" 1 6 == some "Pair"

end Bang.HoverSpike
