module

meta import Bang.Frontend.Query
public import Bang.Frontend.Query
public import Bang.Frontend.Format
meta import Bang.Frontend.Annotate
public import Bang.Frontend.Annotate

/-!
  Bang/Frontend/Rewrite.lean — the `bang rewrite` command side: pure `Prog → Prog` transforms
  over the QUERY fact base (#81, the CQS command half over #80's query/read-model half).
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Operator direction (2026-07-10): queries (#80) INSPECT — `dump` is the read model, flat
  relational facts regenerated from the program (sync by derivation, no update anomaly).
  Commands REWRITE — pure `Prog → Except String Prog` functions; the new program is EMITTED,
  never applied in-place silently. Applying is the CALLER's explicit act (the language's own
  description-until-forced thesis — `$`/force — applied to tooling, mirrored at the CLI layer
  by the `-w` flag: diff by default, write only on an explicit ask; `Main.lean`'s `runRewrite*`
  functions own that half, this module never touches a filesystem).

  TIER STRUCTURE (mirrors `Query.lean`'s three tiers, § headers below):

    TIER 0 — `fmt`, rewrite #0. Re-houses the canonical formatter (#58, `Bang.Format`) as the
      FIRST command rather than growing a parallel system (one construct per problem) — `fmt`
      was always semantically a `Prog → Prog` identity-on-AST rewrite (`Format.roundTripsOn`'s
      own law already says so: formatting changes PRINTED FORM, never the parsed `Prog`); this
      tier makes that fact the type. `Bang.Rewrite.fmt` is `Prog → Except String Prog` for
      UNIFORMITY with every other rewrite in this module (so `Main.lean`'s CLI dispatch is one
      shape for every verb, `fmt` included) even though it can never actually fail on an
      already-parsed `Prog` (see `fmt`'s own doc comment).

    TIER 1 — the PUBLIC LIBRARY API: each rewrite is `public`, documented as REUSABLE Lean-side
      (a script composes these directly), the SAME functions `Main.lean`'s CLI dispatch calls —
      the `Query.lean` precedent, applied to the command side.

    TIER 2 — the PRESERVATION GATE's pure half: `Prog`-level facts a caller compares BEFORE
      trusting a rewrite (name still resolves, no collision) live here; the GATE ITSELF —
      re-elaborating both programs and diffing kernel-oracle eval — needs `Bang.TypeCheck.
      checkAndLowerProg` + `Bang.Source.eval`, which only `Main.lean` (an unrestricted Apex-rank
      consumer) may reach without inverting the leaf's fan-in-0 invariant (`tools/arch-check.sh`)
      — so the ACTUAL differential check is `Main.lean`'s `runRewriteRename`, wired against this
      module's pure `rename`.

  RENAME'S CORE MOVE (shadowing-aware, capture-safe): `TypeCheck.lean` already has EXACTLY this
  shape of walk — `qualifyVars`/`qualifyDeclBody`/`qualifyDeclName` (its module-qualification
  pass, ADR-0093) renames a SET of top-level names to `modname_name` everywhere in a `Prog`,
  stopping at any binder that shadows one of them. `rename` here is the SAME walk specialized to
  ONE name and an arbitrary replacement (not a fixed `qualifyName` suffix) — but those functions
  are PRIVATE `TypeCheck.lean` internals, not `public`. Per `Query.lean`'s OWN documented
  precedent for `surfUsesVar` ("the source is a private internal and this is a small, CLOSED
  structural recursion over an already-public inductive — copied rather than imported, since the
  source cannot drift into a different SEMANTICS the way a re-derived TYPE rule could"), the walk
  is COPIED here, generalized from "rename a set to `modname_·`" to "rename one name to another" —
  same shadowing discipline, simpler substitution. Every `Surf`/`SurfArgs`/`DArms`/`LetBindings`
  constructor is listed (mirrors `qualifyVars`'s own exhaustive-arm shape, itself mirroring
  `surfUsesVar`'s), so a new AST constructor breaks this file's build (missing-arm error), not a
  silent miss.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 — the arch-check invariant): it reads the
  ALREADY-PUBLIC `Prog`/`Decl`/`Surf` shapes (`Bang.Frontend.Surface`) and `Bang.Query.
  declFactsOf`/`nameRefEdgesOf` (the read-model facts a rename consults to find the decl + its
  reference sites) and `Bang.Format.showProg` (fmt's re-housed core), and produces only `Prog`
  values (or a loud `Except String` on a diagnosable failure — missing name, ambiguous name,
  name collision). No kernel/typing-rule change, no new checking behavior — this module runs NO
  type checker itself (that is the PRESERVATION GATE's job, at the CLI layer, over the ALREADY-
  EXISTING `checkAndLowerProg`).
-/

open Bang
open Bang.Surface (Decl Prog Surf DArms SurfArgs LetBindings HClauses LetRecBindings Ty letRecBindingsNames)

namespace Bang.Rewrite

/-! ## 0. TIER 0 — `fmt`, rewrite #0 (#58 re-housed, one construct per problem).

`Bang.Format.fmtProg : String → Except String String` round-trips through the parser (its own
documented reason: formatting is stated over PARSED `Surf`/`Prog`, not raw text). A `Prog`-taking
rewrite has ALREADY parsed — reformatting an in-memory `Prog` is exactly `Bang.Format.showProg`,
which cannot itself fail (it is a total structural fold, no `Except` in its signature). `fmt`
below is `Except`-shaped ONLY for uniformity with `rename`'s signature (so `Main.lean`'s dispatch
treats every verb identically) — it is total in practice, `.ok` on every input. -/

/-- **PUBLIC (TIER 0):** rewrite #0 — the canonical formatter, re-housed as a `Prog → Prog`
rewrite. Semantically a NO-OP on the AST (`Format.roundTripsOn`'s law: fmt changes printed form,
never the parsed program) — `Main.lean`'s `-w`/diff machinery renders `p` and `fmt p` through
`Bang.Format.showProg` and diffs the TWO STRINGS, which is where fmt's actual effect (re-layout)
becomes visible; this function's job is only to be a first-class member of the rewrite tier so
`bang fmt` and `bang rewrite fmt` are ONE construct, not two. -/
public def fmt (p : Prog) : Except String Prog := .ok p

/-! ## 1. TIER 1 — the PUBLIC LIBRARY API: `rename`'s shadowing-aware AST walk.

Mirrors `TypeCheck.lean`'s `qualifyVars`/`qualifyDeclBody`/`qualifyDeclName` mutual-recursion
shape (see module header) — copied and generalized from a NAME-SET → fixed-suffix rename to a
single OLD-NAME → arbitrary NEW-NAME rename. A binder that shadows `old` stops the rename at
that subtree (ordinary lexical shadowing — the SAME rule `qualifyVars` documents at each of its
own binding arms). -/

mutual
/-- Rename every FREE occurrence of `old` to `new` in `e` — stops at any binder that shadows
`old` (the binder itself is never renamed; only `.var` LEAVES are, exactly `qualifyVars`'s own
documented invariant: "renaming only exact `.var` leaves is safe precisely because a binder can
only ever shadow a top-level name, never BE renamed by this pass"). -/
def renameVars (old new : String) : Surf → Surf
  | .lit n       => .lit n
  | .var x       => if x == old then .var new else .var x
  | .thunk e     => .thunk (renameVars old new e)
  | .force e     => .force (renameVars old new e)
  | .lett n a b  => if n == old then .lett n (renameVars old new a) b
                    else .lett n (renameVars old new a) (renameVars old new b)
  | .lam n e     => if n == old then .lam n e else .lam n (renameVars old new e)
  | .app a b     => .app (renameVars old new a) (renameVars old new b)
  | .raise e     => .raise (renameVars old new e)
  | .handle e    => .handle (renameVars old new e)
  | .getS        => .getS
  | .putS e      => .putS (renameVars old new e)
  | .stateS a b  => .stateS (renameVars old new a) (renameVars old new b)
  | .atomS e     => .atomS (renameVars old new e)
  | .newS e      => .newS (renameVars old new e)
  | .readS e     => .readS (renameVars old new e)
  | .writeS a b  => .writeS (renameVars old new a) (renameVars old new b)
  | .inlS e      => .inlS (renameVars old new e)
  | .inrS e      => .inrS (renameVars old new e)
  | .pairS a b   => .pairS (renameVars old new a) (renameVars old new b)
  | .matchS s lx e1 ry e2 =>
      .matchS (renameVars old new s) lx
        (if lx == old then e1 else renameVars old new e1) ry
        (if ry == old then e2 else renameVars old new e2)
  | .splitS a b p body =>
      .splitS a b (renameVars old new p)
        (if a == old || b == old then body else renameVars old new body)
  | .binopS op a b => .binopS op (renameVars old new a) (renameVars old new b)
  | .ifS c t e     => .ifS (renameVars old new c) (renameVars old new t) (renameVars old new e)
  | .annotS e t    => .annotS (renameVars old new e) t
  | .unitS         => .unitS
  | .foldS e       => .foldS (renameVars old new e)
  | .unfoldS e     => .unfoldS (renameVars old new e)
  | .matchD s arms => .matchD (renameVars old new s) (renameDArmsVars old new arms)
  | .withCapS k i n b =>
      .withCapS k (renameVars old new i) n (if n == old then b else renameVars old new b)
  | .dotPerform r op .none      => .dotPerform (renameVars old new r) op .none
  | .dotPerform r op (.one a)   => .dotPerform (renameVars old new r) op (.one (renameVars old new a))
  | .dotPerform r op (.two a b) => .dotPerform (renameVars old new r) op (.two (renameVars old new a) (renameVars old new b))
  | .letRecS n t f b => if n == old then .letRecS n t f b
                         else .letRecS n t (renameVars old new f) (renameVars old new b)
  -- #97 item 2: mirrors `qualifyVars`'s own `.letRecMultiS` arm — every sibling is SIMULTANEOUSLY
  -- in scope of every OTHER sibling's body, so if ANY sibling shadows `old`, `old` stops being
  -- renamed for EVERY sibling's RHS (not just the ones textually after it) and for `b`.
  | .letRecMultiS binds b =>
      if letRecBindingsNames binds |>.contains old then .letRecMultiS binds b
      else .letRecMultiS (renameLetRecBindingsVars old new binds) (renameVars old new b)
  | .divMark e     => .divMark (renameVars old new e)
  | .lettMulti binds b =>
      -- sequential shadowing through the `;`-chain, mirroring `qualifyVars`'s `.lettMulti` arm
      -- exactly: once a binding's name matches `old`, every LATER binding's RHS (and `b`) stop
      -- being renamed (the binding itself shadows `old` from there on).
      let (binds', shadowed) := renameLetBindingsVars old new binds
      .lettMulti binds' (if shadowed then b else renameVars old new b)
  -- ADR-0095 (Stage 7, `handle e with Name as h { … }`): `n` (the effect-name reference) and `p?`
  -- (the param-init expr) are always renamed (references, not binders); `h` (the mandatory cap
  -- binder) shadows exactly like `.withCapS`'s own binder — stops renaming in `b` alone; each
  -- clause's own arg binder shadows PER-CLAUSE (`renameHClausesVars`, the `renameDArmsVars`
  -- precedent) — mirrors `qualifyVars`'s OWN `.handleCustomS` arm exactly (TypeCheck.lean).
  | .handleCustomS lbl n p? h cls b =>
      .handleCustomS lbl (renameVars old new n)
        (match p? with
          | .none     => .none
          | .one p    => .one (renameVars old new p)
          | .two a b' => .two (renameVars old new a) (renameVars old new b'))
        h (renameHClausesVars old new cls)
        (if h == old then b else renameVars old new b)
def renameDArmsVars (old new : String) : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest =>
      .cons c ps (if ps.contains old then b else renameVars old new b) (renameDArmsVars old new rest)
/-- Rename a `;`-binding chain (issue #68 sugar), threading shadowing sequentially — mirrors
`qualifyLetBindingsVars`'s own doc comment: each binding's OWN rhs `e` is always renamed (it is
evaluated in the OUTER scope, before its own name binds); once a binding's name matches `old`,
every later binding (and the eventual body) stop being renamed. Returns the renamed chain plus
whether shadowing was ever triggered. -/
def renameLetBindingsVars (old new : String) : LetBindings → LetBindings × Bool
  | .nil            => (.nil, false)
  | .cons n e rest  =>
      let e' := renameVars old new e
      if n == old then (.cons n e' rest, true)
      else
        let (rest', shadowed) := renameLetBindingsVars old new rest
        (.cons n e' rest', shadowed)
/-- Rename an ADR-0095 clause list `op(argName) => body`, one binder per clause — EACH clause
shadows INDEPENDENTLY (unlike `.lettMulti`'s sequential chain: a clause's own arg binder has no
bearing on any OTHER clause, mirroring `renameDArmsVars`'s own per-arm independence and
`qualifyHClausesVars`'s documented precedent). -/
def renameHClausesVars (old new : String) : HClauses → HClauses
  | .nil               => .nil
  | .cons op x b rest  =>
      .cons op x (if x == old then b else renameVars old new b) (renameHClausesVars old new rest)
/-- Rename a `let rec … and …` sibling chain (#97 item 2) — the CALLER (`.letRecMultiS`'s own
arm above) has ALREADY checked no sibling shadows `old`, so every RHS renames unconditionally
(mirrors `qualifyLetRecBindingsVars`'s own precedent — no sequential threading needed, since
mutual siblings share ONE simultaneous scope). -/
def renameLetRecBindingsVars (old new : String) : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons n t e rest   => .cons n t (renameVars old new e) (renameLetRecBindingsVars old new rest)
end

#guard renameVars "x" "y" (.var "x") == .var "y"
#guard renameVars "x" "y" (.var "z") == .var "z"
#guard renameVars "x" "y" (.lam "x" (.var "x")) == .lam "x" (.var "x")   -- shadowed: binder untouched
#guard renameVars "x" "y" (.lett "z" (.var "x") (.var "x")) == .lett "z" (.var "y") (.var "y")
#guard renameVars "x" "y" (.lett "x" (.var "x") (.var "x")) == .lett "x" (.var "y") (.var "x")   -- rhs renames (outer scope), body shadowed
#guard renameVars "x" "y" (.lettMulti (.cons "x" (.var "x") .nil) (.var "x"))
     == .lettMulti (.cons "x" (.var "y") .nil) (.var "x")

-- ADR-0095 (Stage 7) regression: `handle e with Name as h { op(a) => body }` — `n`/`p?` are
-- references (always renamed); `h` shadows only in `body`; a clause's own arg binder shadows
-- ONLY that clause's own body (mirrors `handle-custom-tracer`'s worked example shape).
-- `n` (the effect-name REFERENCE, here deliberately named `net` too — a different SLOT from the
-- cap binder `h` even though it happens to share a string) renames normally; `h`'s OWN binder
-- shadows the rename inside `body`, so the `net` occurring THERE stays untouched — proves the two
-- `net`-shaped things are handled by genuinely different rules, not accidentally both surviving.
#guard renameVars "net" "conn"
    (.handleCustomS none (.var "net") .none "net" (.cons "fetch" "n" (.var "n") .nil)
      (.app (.var "net") (.var "x")))
  == .handleCustomS none (.var "conn") .none "net" (.cons "fetch" "n" (.var "n") .nil)
      (.app (.var "net") (.var "x"))
#guard renameVars "x" "y"
    (.handleCustomS none (.var "Net") .none "h" (.cons "fetch" "x" (.var "x") .nil)
      (.var "x"))
  == .handleCustomS none (.var "Net") .none "h" (.cons "fetch" "x" (.var "x") .nil)
      (.var "y")   -- the clause's `x` shadows ITS OWN body only; the outer `body`'s `x` still renames
#guard renameVars "x" "y"
    (.handleCustomS none (.var "Net") (.one (.var "x")) "h" .nil (.var "x"))
  == .handleCustomS none (.var "Net") (.one (.var "y")) "h" .nil (.var "y")   -- paramInit is a reference, always renamed

/-- Rename a `Decl`'s internal body/bodies (trait law bodies / impl op bodies / a bounded fn's
body / a plain `let`/`let rec`'s expression) — the "reference side" of a rename, applied to
every OTHER decl's body in the program (never the renamed decl's own name — see `renameDeclName`
for that half). Mirrors `qualifyDeclBody`'s per-constructor dispatch; `data`/`effect` carry no
`Surf` (pure type-level shape, so a VALUE rename never touches them — a `data`/`effect` renamed
BY NAME is the decl-name half, `renameDeclName`, not this one). -/
def renameDeclBody (old new : String) : Decl → Decl
  | .dataD n ps cs        => .dataD n ps cs
  | .effectD n ops        => .effectD n ops
  | .traitD n ps ops laws => .traitD n ps ops (laws.map (fun l => { l with body := renameVars old new l.body }))
  | .implD n t ops        => .implD n t (ops.map (fun o => { o with body := renameVars old new o.body }))
  | .fnD n ps ty tr tv b  => .fnD n ps ty tr tv (renameVars old new b)
  | .letD n ty e          => .letD n ty (renameVars old new e)
  | .letRecD n t e        => .letRecD n t (renameVars old new e)

/-- Rename a `Decl`'s OWN top-level name (only if it currently matches `old`) — the
"declaration side" of a rename, paired with `renameDeclBody`'s "reference side". `data`/`effect`
have no separate reference-body pass (their bodies never carry a `Surf`), so renaming them by
`Decl.name` alone is their WHOLE story. -/
def renameDeclName (old new : String) : Decl → Decl
  | .dataD n ps cs        => .dataD (if n == old then new else n) ps cs
  | .effectD n ops        => .effectD (if n == old then new else n) ops
  | .traitD n ps ops laws => .traitD (if n == old then new else n) ps ops laws
  | .implD n t ops        => .implD n t ops   -- an impl's "name" is its TRAIT (already handled via the trait's own decl, `qualifyDeclName`'s own precedent)
  | .fnD n ps ty tr tv b  => .fnD (if n == old then new else n) ps ty tr tv b
  | .letD n ty e          => .letD (if n == old then new else n) ty e
  | .letRecD n t e        => .letRecD (if n == old then new else n) t e

/-! ## 2. TIER 1 (continued) — `rename`'s PUBLIC entry: the diagnosable, loud-error command. -/

/-- Does `p` declare a top-level name equal to `n`? The rename precondition-check helper (a
`declFactsOf` scan — Tier-1 query-side reuse, per the operator's "consume the query side's public
facts" direction). -/
def declares (p : Prog) (n : String) : Bool :=
  (Bang.Query.declFactsOf p).any (·.name == n)

/-- **PUBLIC entry (TIER 1):** rename top-level declaration `old` to `new` everywhere in `p` —
the decl's own name (`renameDeclName`) AND every free reference to it in every OTHER decl's body
plus the program's trailing expression (`renameDeclBody`/`renameVars`). Three LOUD, distinct
failures (ADR-0046 — never a silent guess):

  - `old` is not declared anywhere in `p` (`declFactsOf` has no such name) — nothing to rename.
  - `old` is AMBIGUOUS: more than one decl shares that name. `Decl.name` is unique per DECL in a
    well-formed `Prog` (the parser/checker's own invariant), so this branch is a defensive
    diagnosis for a malformed program rather than an expected v1 path — still surfaced loudly
    rather than silently renaming the FIRST match, since "which one?" has no honest default.
  - `new` COLLIDES with an existing top-level name (renaming `old`→`new` would shadow/merge two
    distinct decls into one name — a silent identity collapse, never allowed).

`declares`/`declFactsOf` are the QUERY side's own read model (the operator's "consume the query
side's public facts" direction) — this function computes NO decl-name inventory of its own. -/
public def rename (old new : String) (p : Prog) : Except String Prog :=
  let hits := p.decls.filter (·.name == old)
  match hits with
  | []  => .error s!"rename: no top-level declaration named '{old}'"
  | [_] =>
      if old == new then .ok p   -- renaming to the same name is a no-op, not a collision (new == old is the SAME decl)
      else if declares p new then
        .error s!"rename: '{new}' already names a top-level declaration — rename would collide"
      else
        .ok { p with
          decls := p.decls.map (fun d =>
            if d.name == old then renameDeclName old new d else renameDeclBody old new d)
          body := renameVars old new p.body
          pubNames := p.pubNames.map (fun n => if n == old then new else n) }
  | _   => .error s!"rename: '{old}' names more than one top-level declaration (malformed program)"

#guard rename "double" "twice" { decls := [.letRecD "double" (Ty.tArr Ty.tInt Ty.tInt) (.lam "n" (.binopS .add (.var "n") (.var "n")))], body := .app (.force (.var "double")) (.lit 3) }
  == .ok { decls := [.letRecD "twice" (Ty.tArr Ty.tInt Ty.tInt) (.lam "n" (.binopS .add (.var "n") (.var "n")))], body := .app (.force (.var "twice")) (.lit 3) }
#guard (rename "nosuch" "y" ({ decls := [.letD "x" none (.lit 1)], body := .var "x" } : Prog)).isOk == false
#guard (rename "x" "y" ({ decls := [.letD "x" none (.lit 1), .letD "y" none (.lit 2)], body := .var "x" } : Prog)).isOk == false

end Bang.Rewrite
