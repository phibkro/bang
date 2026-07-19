module

meta import Bang.Frontend.Diagnostics
meta import Bang.Core.Fingerprint
public import Bang.Frontend.Diagnostics
public import Bang.Core.Fingerprint

/-!
  Bang/Frontend/Query.lean — the `bang query` fact base: a PUBLIC LIBRARY API + its CLI views (#80).
  ─────────────────────────────────────────────────────────────────────────────────────────────────
  Operator direction (2026-07-10, REFINED — API-first, three tiers): agents/users don't need a fixed
  menu of LSP-shaped operations; they need the FACTS, queryable however they like. This module is
  structured in three tiers, outward from the core:

    TIER 1 — the PUBLIC LIBRARY API (`declFactsOf`/`nameRefEdgesOf`/`lawFactsOf`, plus the resolver-
      supplied `ModuleFact`/`ModuleDepFact` records below): every
      fact-producing function is `public` and documented as a REUSABLE Lean-side API, not merely CLI
      plumbing — a Lean script (or a future in-process consumer) composes these directly, the SAME
      functions `Main.lean`'s CLI dispatch calls.

    TIER 2 — THE KEY OPERATION, `bang query dump <file> --json`: the COMPLETE fact base in ONE
      export — the resolved program's experimental elaborated-core fingerprint, every resolved
      logical module and direct dependency edge, every decl (name · kind · type · effect ROW ·
      visibility · module) as a `DeclFact`, every law instance, every name-reference edge, and the
      program's own import/use header. A user
      or agent composes ARBITRARY queries over this in any scripting language (`jq`, `python`, a
      Lean script) — v1 stops trying to predict which fixed verb matters; `dump` is the one export
      that lets a caller ask a question no verb below anticipates (`tools/test-query.sh`'s composed-
      query demo is exactly this: "every effectful decl whose row contains a user label", a
      5-line `jq` filter over `dump`'s own output, no new Lean code).

    TIER 3 — the CURATED CLI VERBS (`symbols`/`effects`/`type`/`laws`/`def`/`refs`): each is now a
      THIN PROJECTION/FILTER over Tier 1's fact lists (`declFactsOf`/`nameRefEdgesOf`/`lawFactsOf`),
      not an independent `p.decls` walk — ONE construct computes the facts, every surface (the full
      dump, or a narrow verb) reads the SAME list. `symbols` = `declFactsOf` rendered whole; `type`/
      `effects` = one `DeclFact` looked up by name; `def` = ditto, re-rendered as a single hit;
      `refs` = `nameRefEdgesOf` filtered to one target name.

  `bang check --json` (`Bang.Diagnostics`) is this module's schema/exit-code exemplar;
  `Bang.TypeCheck.lawInstancesOf` (#60) is the law-fact seam, reused directly. This module adds NO
  new checking/typing logic — every fact is a RE-RENDERING of what the existing pipeline (parse/
  elaborate/check) already computes. `--json` is the only v1 output.

  POSITION-ADDRESSING IS OUT (gated on #52's Spanned-Surf tier — `Surf` carries no per-node span
  today): `nameRefEdgesOf` reports DECL-granularity edges (which decl's body mentions which name),
  not a line/col occurrence list — the honest ceiling without that tier.

  PER-DECL TYPE QUERY: `checkProg`/`typeStringOfProg` (`TypeCheck.lean`) report the type of a whole
  program's TRAILING BODY, not of an arbitrary top-level binding — there is no seam for "the type of
  just this decl" upstream. The sound, print-then-reparse-free route (mirroring why
  `checkAndLowerProg` exists beside `checkAndLower`, and why `Main.lean`'s `runCheck` explicitly
  REJECTS print-then-reparse for a resolved `Prog`) is: build a `Prog` with the SAME `decls`/
  `imports`/`uses` and `body := Surf.var name`, then check it via `TypeCheck.typeStringOfProgP` (the
  markers-only seam requested of — and landed by — the file owner, mirroring `checkProgRow` beside
  `checkAndLowerProg`). This module never touches `TypeCheck.lean`'s internals otherwise.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 — the arch-check invariant): it reads the
  ALREADY-PUBLIC `Prog`/`Decl`/`Surf` shapes (`Bang.Frontend.Surface`), `Bang.TypeCheck.
  lawInstancesOf`/`typeStringOfProgP`/`checkProgRow`, and `Bang.Format.showSurf`/`showTy`, and
  produces only JSON strings (+ the plain module/decl/reference records Tier 1 exposes). No kernel/
  typing-rule change, no new checking behavior or second resolver walk.
-/

open Bang
open Bang.Surface (Decl Prog Surf DArms SurfArgs LetBindings HClauses LetRecBindings Span Ty OpSig OpDef)

namespace Bang.Query

/-! ## 0. JSON emitter — reuses `Diagnostics.jsonStr` (the ONE string-escaper, SSoT) plus a few
tiny array/object combinators in the same hand-rolled, no-dependency style (`Diagnostics.lean`'s
own rationale: a small fixed shape beats a new dependency). -/

/-- A JSON array from already-rendered element strings. -/
def jsonArr (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

/-- A JSON array of STRINGS (escapes each element via the one true escaper). -/
def jsonStrArr (items : List String) : String :=
  jsonArr (items.map Bang.Diagnostics.jsonStr)

/-- A JSON array of already-`jsonStr`-escaped OPTIONAL strings, `none` rendering as `null`. -/
def jsonOptStrArr (items : List (Option String)) : String :=
  jsonArr (items.map (fun | some s => Bang.Diagnostics.jsonStr s | none => "null"))

/-- One `"key":value` pair, value already rendered (caller supplies `jsonStr`-wrapped strings,
`jsonArr`-wrapped arrays, or a bare literal like `true`/`42`). -/
def jsonField (key value : String) : String :=
  Bang.Diagnostics.jsonStr key ++ ":" ++ value

/-- A JSON object from already-rendered `"key":value` fields. -/
def jsonObj (fields : List String) : String :=
  "{" ++ String.intercalate "," fields ++ "}"

/-- A `jsonStr`-escaped STRING field — the common case (`jsonField k (jsonStr v)`), factored out
since most facts below are raw strings, not pre-rendered JSON values. -/
def jsonStrField (key value : String) : String :=
  jsonField key (Bang.Diagnostics.jsonStr value)

/-- An OPTIONAL `jsonStr`-escaped string field: `none ↦ "key":null`, matching ADR-0046 ("absence
over a guessed default") rather than omitting the key — `dump`'s schema keeps every `DeclFact`
shape-uniform (every key always present) so a consumer's `jq '.decls[].type'` never has to branch
on key PRESENCE, only on `null`-ness. -/
def jsonOptStrField (key : String) (value : Option String) : String :=
  jsonField key (match value with | some s => Bang.Diagnostics.jsonStr s | none => "null")

/-- `{"error":"<msg>"}` — the TOOL-error shape (`Main.lean`'s unreadable-file case, exit 2 —
mirrors `check`'s convention of never folding a tool error into the ok/diagnostics schema). `msg`
is raw text, so it is `jsonStr`-escaped here (`jsonField`'s `value` parameter wants an
already-rendered JSON value, per its own doc comment). -/
def errorJson (msg : String) : String :=
  jsonObj [jsonStrField "error" msg]

/-- `{"ok":false,"error":"<msg>"}` — the uniform QUERY-FAILURE shape every op's `ok:true/false`
JSON body uses (parse error, elaboration failure, unresolvable name). Mirrors `Diagnostics.
checkFailJson`'s "one hand-assembled shape, `jsonStr` for the one string that needs escaping"
convention, extended with the `ok` discriminant every op here shares with `check --json`. `public`:
`Main.lean`'s resolver-aware dispatch (`readQuerySrc`/`resolveQueryProg`, #80) reuses this
directly for a PARSE/resolution failure discovered OUTSIDE any single entry's own pipeline (mirrors
why `Diagnostics.jsonStr`/`parseFailJson` are `public` for the SAME reason on `check --json`'s
resolver path). -/
public def errorJsonOk (msg : String) : String :=
  jsonObj [jsonField "ok" "false", jsonStrField "error" msg]

#guard errorJson "boom" == "{\"error\":\"boom\"}"
#guard errorJsonOk "boom" == "{\"ok\":false,\"error\":\"boom\"}"
#guard jsonArr ["1", "2"] == "[1,2]"
#guard jsonStrArr ["a", "b\"c"] == "[\"a\",\"b\\\"c\"]"
#guard jsonObj [jsonField "a" "1", jsonField "b" "\"x\""] == "{\"a\":1,\"b\":\"x\"}"
#guard jsonOptStrField "type" (some "Int") == "\"type\":\"Int\""
#guard jsonOptStrField "type" none == "\"type\":null"

/-! ## 1. TIER 1 — the PUBLIC LIBRARY API: fact-producing core, reusable outside the CLI.

`DeclFact` is the ONE record every downstream surface reads: `dump` renders the whole list, `symbols`
renders it unfiltered, `type`/`effects`/`def` filter it to one name. Fields are `Option` where a
decl kind genuinely has none (a `trait`/`data`/`effect` has no checker-computed value type) —
`dump`'s JSON keeps every key PRESENT with `null` (see `jsonOptStrField`'s doc comment), so a
consumer never branches on key existence, only nullness. -/

/-- The stable, additive-only machine key for a decl's SHAPE — one per `Decl` constructor (matching
`Diagnostics.DiagCode`'s own stability convention: a NEW kind is a schema addition, never a
renumbering). -/
public inductive DeclKind where
  | letD | letRecD | fnD | traitD | implD | dataD | effectD | handlerD
  deriving Repr, DecidableEq

/-- `DeclKind` from a `Decl` — the SINGLE place that knows the mapping (every fact/filter below
reads it from here, never re-derives it by re-matching `Decl` itself). -/
public def DeclKind.of : Decl → DeclKind
  | .letD ..    => .letD
  | .letRecD .. => .letRecD
  | .fnD ..     => .fnD
  | .traitD ..  => .traitD
  | .implD ..   => .implD
  | .dataD ..   => .dataD
  | .effectD .. => .effectD
  | .handlerD .. => .handlerD

/-- The JSON-schema STRING a `DeclKind` renders as (`"let"`/`"letRec"`/`"fn"`/`"trait"`/`"impl"`/
`"data"`/`"effect"`) — the schema's own stable vocabulary, unrelated to Lean's constructor names. -/
public def DeclKind.toJson : DeclKind → String
  | .letD    => "\"let\""
  | .letRecD => "\"letRec\""
  | .fnD     => "\"fn\""
  | .traitD  => "\"trait\""
  | .implD   => "\"impl\""
  | .dataD   => "\"data\""
  | .effectD => "\"effect\""
  | .handlerD => "\"handler\""

/-- A trait/impl/data/effect decl's STRUCTURAL summary (its ops/ctors/params, pre-rendered as one
JSON value) — the non-value-typed kinds' analogue of a `letD`'s checker type. `none` for `letD`/
`letRecD`/`fnD` (their fact carries `type`/`row` instead; see `DeclFact.shape`'s doc comment). -/
def declShapeJson : Decl → Option String
  | .traitD _ params sigs laws =>
      some <| jsonObj [jsonField "params" (jsonStrArr params),
               jsonField "ops" (jsonArr (sigs.map (fun o =>
                 jsonObj [jsonStrField "name" o.name, jsonStrField "type" (Bang.Format.showTy o.methodTy)]))),
               jsonField "laws" (jsonStrArr (laws.map (·.name)))]
  | .implD _ τ ops =>
      some <| jsonObj [jsonStrField "target" (Bang.Format.showTy τ),
               jsonField "ops" (jsonArr (ops.map (fun o => jsonObj [jsonStrField "name" o.name])))]
  | .dataD _ params ctors =>
      some <| jsonObj [jsonField "params" (jsonStrArr params),
               jsonField "ctors" (jsonArr (ctors.map (fun c =>
                 jsonObj [jsonStrField "name" c.1, jsonField "payload" (jsonStrArr (c.2.map Bang.Format.showTy))])))]
  | .effectD _ ops laws =>
      some <| jsonObj [jsonField "ops" (jsonArr (ops.map (fun o =>
                 jsonObj [jsonStrField "name" o.1, jsonStrField "type" (Bang.Format.showTy o.2)]))),
               jsonField "laws" (jsonStrArr (laws.map (·.name)))]
  | .handlerD _ eff cls =>
      some <| jsonObj [jsonStrField "implements" eff,
               jsonField "ops" (jsonStrArr ((Bang.Surface.hClausesToList cls).map (fun c => c.1)))]
  | .fnD _ ps _ tr tv _ =>
      -- `fnD`'s BOUND-generic header (trait/typeVar/params) is structural too, alongside its
      -- checker `type`/`row` (both present — a bounded fn is the one kind with BOTH).
      some <| jsonObj [jsonField "params" (jsonStrArr ps),
               jsonField "bound" (jsonObj [jsonStrField "trait" tr, jsonStrField "typeVar" tv])]
  | .letD .. | .letRecD .. => none

/-- Project ONE query name onto `p`: same `decls`/`imports`/`uses`, trailing body replaced by
`Surf.var name` — the sound `checkAndLowerProg`-style route (see module header) that never
reparses printed source. -/
def withQueryBody (p : Prog) (name : String) : Prog :=
  { p with body := .var name, isLibrary := false }

/-- **PUBLIC (TIER 1):** the checker's `type ! row` string for top-level binding `name` in program
`p`, or the checker's own error message on failure (an ill-typed program, or `name` not bound as a
VALUE — e.g. naming a `trait`/`data`/`effect`, which `Surf.var` can never resolve to). `public`:
`Bang.Rewrite.annotate` (#82) reuses this DIRECTLY (a `letD`'s own annotate-outcome needs exactly
this per-decl checked fact) rather than re-deriving a second `withQueryBody`-style projection. -/
public def typeStringOfDecl (p : Prog) (name : String) : Except String String :=
  Bang.TypeCheck.typeStringOfProgP (withQueryBody p name)

/-- **PUBLIC (TIER 1):** split a rendered `"T ! {row}"` (or bare `"T"`) into `(typeStr, rowStr)` —
`rowStr` is `"{}"` when no `" ! "` separator is present (`showType`'s empty-row convention: the
suffix is omitted entirely, not printed as `"! {}"`). Pure string surgery over `TypeCheck.showType`'s
ONE rendering convention (never re-derived from a second checker call). `public`: the SAME
`Bang.Rewrite.annotate` consumer as `typeStringOfDecl` above. -/
public def splitTypeRow (rendered : String) : String × String :=
  match rendered.splitOn " ! " with
  | [ty, row] => (ty, row)
  | _         => (rendered, "{}")

#guard splitTypeRow "Int ! {throws}" == ("Int", "{throws}")
#guard splitTypeRow "Int" == ("Int", "{}")

/-- **PUBLIC (TIER 1 library API):** the COMPLETE fact record for ONE top-level decl — the atom
`dump`/`symbols`/`type`/`effects`/`def` all read. `type`/`row` are `some` for a VALUE-typed decl
(`let`/`letRec`/`fn`) that TYPE-CHECKS, `none` otherwise (either the decl has no value-level type —
`trait`/`impl`/`data`/`effect` — or it does but the checker rejected the wrapping program;
`typeError` then carries the checker's message so a `dump` reader can distinguish "no type by
kind" from "type-checking failed", never conflating the two as one `null`). `shape` is `some` for
the non-value kinds' structural summary (`declShapeJson`) or a bounded `fnD`'s header — `none` for
a plain `let`/`letRec`. `module` is `none` at THIS layer (a flat `Prog` has no per-decl module
provenance post-merge — `Main.lean`'s resolver-aware dump threads it in separately, see
`moduleOfDecl` usage at the CLI layer) — `declFactsOf` alone (single-file, no resolver) is honest
with `module := none` throughout. -/
public structure DeclFact where
  /-- The decl's top-level name (`Decl.name`). -/
  name      : String
  /-- Which of the 7 `Decl` constructors this is (`DeclKind.of`). -/
  kind      : DeclKind
  /-- The decl's rendered type, `some` only for a VALUE-typed decl (`let`/`letRec`/`fn`) that
  type-checks — see this structure's own doc comment for the full `type`/`row`/`typeError`
  three-way split. -/
  type      : Option String
  /-- The decl's rendered effect row, alongside `type` (`some` under the same condition). -/
  row       : Option String
  /-- The checker's error message, `some` when a value-typed decl's `type`/`row` came back `none`
  because type-checking FAILED (as opposed to `none` because this decl kind has no value-level
  type at all) — the disambiguation this structure's own doc comment names. -/
  typeError : Option String
  /-- The non-value kinds' structural summary (`declShapeJson`), or a bounded `fnD`'s header;
  `none` for a plain `let`/`letRec`. -/
  shape     : Option String   -- pre-rendered JSON (already a value, not a raw string — see `toJson`)
  /-- Is this decl `pub` (exported)? -/
  pub       : Bool
  /-- The decl's owning module name, `none` at this layer (a flat `Prog` has no per-decl module
  provenance post-merge) — `Main.lean`'s resolver-aware dump overlays it separately. -/
  module    : Option String
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg; `prec` is the interface, not
-- a dead param (unusedArguments false-positive on derived instances).
attribute [nolint unusedArguments] instReprDeclFact.repr

/-- **PUBLIC (TIER 1):** the fact record for ONE decl `d` of program `p` (`p` supplies the checker
context every value-typed decl's `type`/`row` needs). `module` defaults to `none`; the CLI layer
(`Main.lean`, which has resolver provenance `Query.lean` itself does not) overlays it via
`DeclFact.withModule`. -/
public def declFactOf (p : Prog) (d : Decl) : DeclFact :=
  let name := d.name
  let pub := p.pubNames.contains name
  let shape := declShapeJson d
  match DeclKind.of d with
  | .letD | .letRecD | .fnD =>
      match typeStringOfDecl p name with
      | .ok rendered =>
          let (ty, row) := splitTypeRow rendered
          { name, kind := DeclKind.of d, type := some ty, row := some row, typeError := none, shape, pub, module := none }
      | .error e =>
          { name, kind := DeclKind.of d, type := none, row := none, typeError := some e, shape, pub, module := none }
  | k =>
      { name, kind := k, type := none, row := none, typeError := none, shape, pub, module := none }

/-- **PUBLIC (TIER 1):** every top-level decl of `p` as a `DeclFact`, in SOURCE ORDER (`p.decls`'s
own list order — the parser preserves it, no re-sort). THE core fact-producing function every
Tier-2/3 surface (`dump`/`symbols`/`type`/`effects`/`def`/`refs`) filters or renders. -/
public def declFactsOf (p : Prog) : List DeclFact :=
  p.decls.map (declFactOf p)

/-- Overlay a MODULE name onto a fact (the CLI resolver layer's own provenance, `Main.lean`'s
`declModuleOf` map — `Query.lean` itself never computes this, since a flat merged `Prog` has no
per-decl module field; see `DeclFact`'s own doc comment). -/
public def DeclFact.withModule (f : DeclFact) (m : Option String) : DeclFact :=
  { f with module := m }

/-- One `DeclFact` → its JSON object — every key ALWAYS present (`jsonOptStrField`'s "no branching
on presence" convention), so `dump`'s array is uniform. -/
public def DeclFact.toJson (f : DeclFact) : String :=
  jsonObj [jsonStrField "name" f.name, jsonField "kind" f.kind.toJson,
           jsonOptStrField "type" f.type, jsonOptStrField "row" f.row,
           jsonOptStrField "typeError" f.typeError,
           jsonField "shape" (f.shape.getD "null"),
           jsonField "pub" (if f.pub then "true" else "false"),
           jsonOptStrField "module" f.module]

/-- **PUBLIC (TIER 1):** every `Surf` body attached to `Decl` `d` (a trait's law bodies, an impl's
op bodies, a bounded `fn`'s body, a plain `let`/`let rec`'s bound expression) — the search space a
name-reference walk covers PER decl. A `traitD`'s own OP SIGNATURES carry no body (only a declared
`Ty`, never a `Surf`); `dataD`/`effectD` carry no `Surf` at all (pure type-level shape). -/
public def declBodies : Decl → List Surf
  | .traitD _ _ _ laws => laws.map (·.body)
  | .implD _ _ ops     => ops.map (·.body)
  | .dataD ..           => []
  | .fnD _ _ _ _ _ b    => [b]
  | .effectD _ _ laws    => laws.map (·.body)
  | .handlerD _ _ cls    => (Bang.Surface.hClausesToList cls).map (fun c => c.2.2)
  | .letD _ _ e         => [e]
  | .letRecD _ _ e      => [e]

/-- **PUBLIC (issue #83):** does `e` mention variable `nm` anywhere in its tree? A thin RE-EXPORT of
`Bang.TypeCheck.surfUsesVar` — ONE authoritative structural-walk home, not a second implementation.
This module used to carry a byte-identical COPY (the #73-walk precedent) on the belief that
importing `TypeCheck.lean`'s private original back here would cycle — but `Query.lean` already
imports `TypeCheck.lean` TRANSITIVELY (`Query.lean` → `Diagnostics.lean` → `TypeCheck.lean`), so
that import direction was never circular; only the ORIGINAL's own visibility (`private def`) was
the blocker, fixed by marking it `public` at its one true home. A copy's failure mode was silent
skew (`Stage-7`'s `handleCustomS` broke this file's exhaustive match on its own copy — fail-loud
caught it, but at the cost of a hand-sync every constructor addition now avoids). -/
public def surfUsesVar (nm : String) : Surf → Bool := Bang.TypeCheck.surfUsesVar nm

#guard surfUsesVar "x" (.var "x") == true
#guard surfUsesVar "x" (.var "y") == false
#guard surfUsesVar "x" (.lett "y" (.var "x") (.lit 0)) == true
#guard surfUsesVar "x" (.lettMulti (.cons "y" (.var "x") .nil) (.lit 0)) == true
#guard surfUsesVar "x" (.matchD (.var "s") (.cons "C" ["a"] (.var "x") .nil)) == true

/-- **PUBLIC (TIER 1):** does ANY body attached to `d` mention `nm`? -/
public def declMentionsVar (nm : String) (d : Decl) : Bool :=
  (declBodies d).any (surfUsesVar nm)

/-- **PUBLIC (TIER 1) library API:** ONE name-reference EDGE — `from` is a REFERENCING decl's own
name, `to` is the referenced name. DECL granularity (position-addressing is OUT, #52). -/
public structure RefEdge where
  /-- The REFERENCING decl's own name (`src`/`tgt` avoid the `from`/`to` reserved-word clash). -/
  src : String
  /-- The REFERENCED name. -/
  tgt : String
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg (unusedArguments false-positive).
attribute [nolint unusedArguments] instReprRefEdge.repr

/-- **PUBLIC (TIER 1):** every name-reference edge in `p` — for EACH decl, for EACH other
name any OTHER decl (or itself) defines, an edge if the FIRST decl's body mentions the SECOND's
name. `O(decls² )` (fine at bang-program scale; a differential/perf gate is the natural follow-up
if a corpus ever grows past it) — this is the WHOLE edge set `dump`/`refs` both read; `refs name`
is exactly `nameRefEdgesOf p |>.filter (·.tgt == name)`, ONE construct for both surfaces. -/
public def nameRefEdgesOf (p : Prog) : List RefEdge :=
  let names := p.decls.map Decl.name
  p.decls.flatMap (fun d => names.filterMap (fun n =>
    if declMentionsVar n d then some ⟨d.name, n⟩ else none))

/-- One `RefEdge` → its JSON object. -/
def RefEdge.toJson (e : RefEdge) : String :=
  jsonObj [jsonStrField "from" e.src, jsonStrField "to" e.tgt]

/-- Stable origin vocabulary for one logical module discovered by the resolver. No filesystem path
is part of this fact: `project` means resolver-owned source under an allowed project root, while
`bundled` means compiler-baked source such as `Io`. -/
public inductive ModuleOrigin where
  | entry | project | bundled
  deriving Repr, DecidableEq

/-- Public JSON spelling for `ModuleOrigin`. -/
public def ModuleOrigin.toJson : ModuleOrigin → String
  | .entry   => "\"entry\""
  | .project => "\"project\""
  | .bundled => "\"bundled\""

/-- **PUBLIC (TIER 1):** one logical node in the resolver's module DAG. `@entry` is a reserved,
path-free identity for the queried entry file; imported modules retain their language-level names. -/
public structure ModuleFact where
  name : String
  origin : ModuleOrigin
  deriving Repr

/-- **PUBLIC (TIER 1):** one logical module-dependency edge. `src` depends directly on `tgt`;
`import` and `use` both induce this build/invalidation relation. -/
public structure ModuleDepFact where
  src : String
  tgt : String
  deriving Repr

-- Generated `Repr` code ignores its precedence argument.
attribute [nolint unusedArguments] instReprModuleOrigin.repr instReprModuleFact.repr
  instReprModuleDepFact.repr

/-- The path-free entry node used by every source- and `Prog`-taking dump route. -/
public def entryModuleFact : ModuleFact := ⟨"@entry", .entry⟩

/-- One `ModuleFact` → its flat JSON row. -/
public def ModuleFact.toJson (f : ModuleFact) : String :=
  jsonObj [jsonStrField "name" f.name, jsonField "origin" f.origin.toJson]

/-- One `ModuleDepFact` → its flat JSON row. -/
public def ModuleDepFact.toJson (e : ModuleDepFact) : String :=
  jsonObj [jsonStrField "from" e.src, jsonStrField "to" e.tgt]

#guard entryModuleFact.toJson == "{\"name\":\"@entry\",\"origin\":\"entry\"}"
#guard (ModuleDepFact.mk "@entry" "Json").toJson == "{\"from\":\"@entry\",\"to\":\"Json\"}"

/-- **PUBLIC (TIER 1):** one law instance `(contractKey, law, params, body)` → its `LawFact` JSON.
For traits, `contractKey` is the historical trait name and `realization` is null. Effect-handler
instances use `Effect@Handler`; `contract`/`realization` expose those components while the old
`trait` field remains an additive-schema compatibility key. Discovery stays entirely in
`Bang.TypeCheck.lawInstancesOf` (#60) — zero new discovery logic. -/
def lawInstanceJson (inst : String × String × List String × String) : String :=
  let (trait, law, params, body) := inst
  let parts := trait.splitOn "@"
  let contract := parts.head?.getD trait
  let realization := if parts.length == 2 then parts[1]? else none
  jsonObj [jsonStrField "trait" trait, jsonStrField "contract" contract,
           jsonOptStrField "realization" realization, jsonStrField "law" law,
           jsonField "params" (jsonStrArr params), jsonStrField "body" body]

#guard lawInstanceJson ("Codec@Shift7", "roundtrip", ["x"], "handle body with Shift7 as codec") ==
  "{\"trait\":\"Codec@Shift7\",\"contract\":\"Codec\",\"realization\":\"Shift7\",\"law\":\"roundtrip\",\"params\":[\"x\"],\"body\":\"handle body with Shift7 as codec\"}"

/-- A resolver-stable declaration identity. `mergeModules` intentionally keeps a selected `use`
name bare for source readability, while qualifying its siblings. The resolver-supplied module map
lets the contract card restore one identity without changing those presentation names. -/
def stableDeclId (declModule : List (String × String)) (name : String) : String :=
  match declModule.lookup name with
  | none => name
  | some modName =>
      let modulePrefix := modName ++ "_"
      if name.startsWith modulePrefix then name else modulePrefix ++ name

/-- The concise source-level spelling paired with `stableDeclId`. Existing `name` fields remain
unchanged compatibility/presentation data; `displayName` is the explicitly local label. -/
def displayDeclName (declModule : List (String × String)) (name : String) : String :=
  match declModule.lookup name with
  | none => name
  | some modName =>
      let modulePrefix := modName ++ "_"
      if name.startsWith modulePrefix then (name.drop modulePrefix.length).toString else name

/-- Contract-card law evidence with stable relation keys. The historical fields remain byte-for-
byte in meaning; machines join on `id`/`contractId`/`realizationId`. -/
def contractLawJson (declModule : List (String × String))
    (inst : String × String × List String × String) : String :=
  let (trait, law, params, body) := inst
  let parts := trait.splitOn "@"
  let contract := parts.head?.getD trait
  let realization := if parts.length == 2 then parts[1]? else none
  let contractId := stableDeclId declModule contract
  let realizationId := realization.map (stableDeclId declModule)
  let id := match realizationId with
    | some rid => contractId ++ "@" ++ rid ++ ":" ++ law
    | none => contractId ++ ":" ++ law
  jsonObj [jsonStrField "id" id,
           jsonStrField "trait" trait, jsonStrField "contract" contract,
           jsonStrField "contractId" contractId,
           jsonOptStrField "realization" realization,
           jsonField "realizationId" (realizationId.map Bang.Diagnostics.jsonStr |>.getD "null"),
           jsonStrField "law" law, jsonField "params" (jsonStrArr params),
           jsonStrField "body" body]

/-! ## Semantic contract cards

The ordinary dump remains the complete relational fact base. A contract card is its focused
semantic-description view: declared effect contracts, handler realizations, quantitative use
obligations, law instances, and the compiler evidence attached to those facts. -/

public structure QuantityFact where
  owner    : String
  name     : String
  declared : QTT
  observed : QTT
  deriving Repr

def QuantityFact.toJson (f : QuantityFact) : String :=
  jsonObj [jsonStrField "owner" f.owner, jsonStrField "name" f.name,
           jsonStrField "declared" (Bang.Format.quantityTok f.declared),
           jsonStrField "observed" (Bang.Format.quantityTok f.observed),
           jsonStrField "enforcement" "exact-local-usage",
           jsonStrField "erasure" "before-lowering"]

mutual
def quantityFactsSurf (owner : String) : Surf → List QuantityFact
  | .lit _ | .var _ | .unitS | .getS => []
  | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
  | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ | .pledgeS _ e =>
      quantityFactsSurf owner e
  | .useS q name body =>
      ⟨owner, name, q, Bang.TypeCheck.surfaceUsage name body⟩ :: quantityFactsSurf owner body
  | .lett _ a b | .app a b | .stateS a b | .writeS a b | .pairS a b | .binopS _ a b =>
      quantityFactsSurf owner a ++ quantityFactsSurf owner b
  | .lam _ body => quantityFactsSurf owner body
  | .matchS s _ l _ r =>
      quantityFactsSurf owner s ++ quantityFactsSurf owner l ++ quantityFactsSurf owner r
  | .splitS _ _ p body => quantityFactsSurf owner p ++ quantityFactsSurf owner body
  | .ifS c t e => quantityFactsSurf owner c ++ quantityFactsSurf owner t ++ quantityFactsSurf owner e
  | .matchD s arms => quantityFactsSurf owner s ++ quantityFactsDArms owner arms
  | .withCapS _ init _ body => quantityFactsSurf owner init ++ quantityFactsSurf owner body
  | .dotPerform recv _ args => quantityFactsSurf owner recv ++ quantityFactsArgs owner args
  | .letRecS _ _ rhs body => quantityFactsSurf owner rhs ++ quantityFactsSurf owner body
  | .letRecMultiS binds body => quantityFactsLetRec owner binds ++ quantityFactsSurf owner body
  | .lettMulti binds body => quantityFactsLets owner binds ++ quantityFactsSurf owner body
  | .handleCustomS _ eff init _ clauses body =>
      quantityFactsSurf owner eff ++ quantityFactsArgs owner init ++
        quantityFactsHClauses owner clauses ++ quantityFactsSurf owner body
  | .hostPerformS _ eff _ args => quantityFactsSurf owner eff ++ quantityFactsArgs owner args
def quantityFactsArgs (owner : String) : SurfArgs → List QuantityFact
  | .none => []
  | .one a => quantityFactsSurf owner a
  | .two a b => quantityFactsSurf owner a ++ quantityFactsSurf owner b
def quantityFactsDArms (owner : String) : DArms → List QuantityFact
  | .nil => []
  | .cons _ _ body rest => quantityFactsSurf owner body ++ quantityFactsDArms owner rest
def quantityFactsLets (owner : String) : LetBindings → List QuantityFact
  | .nil => []
  | .cons _ rhs rest => quantityFactsSurf owner rhs ++ quantityFactsLets owner rest
def quantityFactsLetRec (owner : String) : LetRecBindings → List QuantityFact
  | .nil => []
  | .cons _ _ rhs rest => quantityFactsSurf owner rhs ++ quantityFactsLetRec owner rest
def quantityFactsHClauses (owner : String) : HClauses → List QuantityFact
  | .nil => []
  | .cons _ _ body rest | .consUpdating _ _ body rest =>
      quantityFactsSurf owner body ++ quantityFactsHClauses owner rest
end

public def quantityFactsOf (p : Prog) : List QuantityFact :=
  p.decls.flatMap (fun d => (declBodies d).flatMap (quantityFactsSurf d.name)) ++
    quantityFactsSurf "<body>" p.body

def contractDeclJson (declModule : List (String × String)) : Decl → Option String
  | .effectD name ops laws =>
      some <| jsonObj [jsonStrField "id" (stableDeclId declModule name),
        jsonStrField "name" name, jsonStrField "displayName" (displayDeclName declModule name),
        jsonField "operations" (jsonStrArr (ops.map (·.1))),
        jsonField "laws" (jsonStrArr (laws.map (·.name)))]
  | _ => none

def realizationDeclJson (declModule : List (String × String)) : Decl → Option String
  | .handlerD name eff clauses =>
      some <| jsonObj [jsonStrField "id" (stableDeclId declModule name),
        jsonStrField "name" name, jsonStrField "displayName" (displayDeclName declModule name),
        jsonStrField "contract" eff, jsonStrField "contractId" (stableDeclId declModule eff),
        jsonField "operations" (jsonStrArr ((Bang.Surface.hClausesToList clauses).map (·.1)))]
  | _ => none

/-- **PUBLIC entry, `Prog`-taking:** the focused semantic-description read model. `ok` says the
query operation ran; `subjectValid` independently says the described program passed the compiler
pipeline. Resolver callers should supply `declModule` so identities survive `use` selection. -/
public def contractJsonP (p : Prog) (declModule : List (String × String) := []) : String :=
  let laws := match Bang.TypeCheck.lawInstancesOfProg p with
    | .ok xs => xs.map (contractLawJson declModule)
    | .error _ => []
  let checked := Bang.TypeCheck.checkAndLowerProg p
  let subjectValid := match checked with | .ok _ => true | .error _ => false
  let evidence := match checked with
    | .ok _ => jsonObj [jsonField "typeChecked" "true",
        jsonStrField "quantityChecking" "exact-local",
        jsonStrField "quantityErasure" "before-lowering",
        jsonStrField "backendErasure" "manifest-unused-let-result"]
    | .error e => jsonObj [jsonField "typeChecked" "false", jsonStrField "error" e]
  jsonObj [jsonField "ok" "true", jsonField "subjectValid" (if subjectValid then "true" else "false"),
    jsonField "schemaVersion" "1",
    jsonField "contracts" (jsonArr (p.decls.filterMap (contractDeclJson declModule))),
    jsonField "realizations" (jsonArr (p.decls.filterMap (realizationDeclJson declModule))),
    jsonField "quantities" (jsonArr ((quantityFactsOf p).map QuantityFact.toJson)),
    jsonField "laws" (jsonArr laws), jsonField "evidence" evidence]

/-- **PUBLIC entry:** source-taking twin of `contractJsonP`. -/
public def contractJson (src : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p0 => contractJsonP ((Bang.TypeCheck.expandDerives p0).toOption.getD p0)

#guard (contractJson "let x = 1 in use [1] x in x" |>.splitOn "\"declared\":\"[1]\"").length == 2
#guard (contractJson "let x = 1 in use [1] x in x" |>.splitOn "\"observed\":\"[1]\"").length == 2

/-! ## 2. TIER 2 — `bang query dump <file>`: the COMPLETE fact base in one export.

Assembles resolver-supplied module topology + `declFactsOf` + `nameRefEdgesOf` + `lawInstancesOf` +
the program's own `import`/`use` header into ONE JSON object — the schema documented in
`docs/reference/language.md`'s `bang query`
section. A caller composes ARBITRARY queries over this (a `jq`/`python`/Lean script) rather than
waiting on a new fixed verb — `tools/test-query.sh`'s composed-query demo answers a question no
verb below anticipates, over THIS export alone.

SHAPE (operator-informed, the `compiler-as-dbms-survey.md` ruling): `dump` is a FLAT RELATIONAL
fact base — `modules`/`moduleDeps`/`decls`/`refs`/`laws`/`imports`/`uses` are top-level ARRAYS OF
FLAT RECORDS (Glean's
"predicates = tables, facts = rows" framing), never a nested tree; the concrete gate is that the
golden `dump` output loads into DuckDB with ONE `read_json` call (`tools/test-query.sh`'s
`golden-dump-duckdb-loadable` check) — no unnesting gymnastics. The curated verbs (`symbols`/
`type`/`effects`/`def`/`refs`/`laws`) are DERIVED PREDICATES (views) over this extensional base — Tier 3.

SCHEMA VERSIONING (the DBMS survey's ONE eager-adoption item, §6/§8 — REFINED, operator ruling,
2026-07-10): bang's 0.x "breaking changes allowed" policy collides with "agents write durable
scripts against `dump`'s JSON" — every schema change breaks every saved query. The fix is TWO
DISJOINT fields, never conflated:

  `schemaVersion` — a plain MONOTONIC INTEGER, the CONTRACT itself. Bumps ONLY on a BREAKING shape
    change (a field/table rename, removal, or MEANING change) — never for additive growth (a new
    field or table is non-breaking BY CONTRACT, see below). Consumers key their compatibility
    check on THIS field alone, never on `bangVersion`.
  `bangVersion` — PROVENANCE metadata (which compiler binary emitted this dump), sourced from
    `Main.lean`'s existing `bangVersion` constant and threaded in as a parameter (`Query.lean` is a
    LEAF, fan-in 0 from the verified spine — it cannot import `Main.lean` upward; provenance is the
    CALLER's fact to supply, not this module's to hardcode or reach for).

THE CONTRACT RULE (the protobuf/Kubernetes-API discipline, stated so it is UNMISSABLE): **consumers
MUST IGNORE UNKNOWN FIELDS.** This is what makes "additive ⟹ non-breaking" true by construction — a
durable agent script asserting `schemaVersion == 1` must survive twenty compiler releases that only
ADD facts, and a script that hard-fails on an unrecognized key breaks that guarantee itself. This
rule is the OTHER HALF of the contract (bang emits `schemaVersion`; the CONSUMER promises forward-
tolerance) — documented here AND in `docs/reference/language.md`'s `bang query` section, since it
binds the reader, not just the emitter.

`tools/test-query.sh`'s `golden-dump-schema-pinned` check fails CI on any un-versioned drift (a
golden `dump` snapshot of a corpus example, byte-exact) — the "test" rung of the derivation-
strength ladder applied to a public JSON contract. -/

/-- **PUBLIC (TIER 1):** `dump`'s schema version — a plain monotonic `Nat`, bumped ONLY on a
BREAKING shape change (rename/removal/meaning-change), never for additive growth (see this
section's header for the full contract, including the consumer-side "ignore unknown fields" half).
Starts at `1`. The SINGLE SOURCE every `dump*Json*` entry reads — bump here, in ONE place, at a
genuine breaking change. -/
public def schemaVersion : Nat := 1

/-- One `ImportDecl`/`UseDecl` header line → its JSON object (`{"module":"Name"}` for an `import`,
`{"module":"Name","names":[...]}` for a `use`). -/
def importJson (i : Bang.Surface.ImportDecl) : String := jsonObj [jsonStrField "module" i.modName]
def useJson (u : Bang.Surface.UseDecl) : String :=
  jsonObj [jsonStrField "module" u.modName, jsonField "names" (jsonStrArr u.names)]

/-! ### Resolved-program core fingerprint probe

This is the first RESULT-hash observation over the same typed lowering path `bang run` uses. Its
scope is deliberately the WHOLE resolved/merged `Prog`: modules still elaborate together to one flat
kernel `Comp`, so claiming per-module result hashes here would invent a separate-compilation boundary
that does not exist. The 64-bit structural digest is also explicitly NOT cache-key-safe; it probes
formatting/alpha invariance and semantic discrimination, while leaving collision resistance,
compiler-version domain separation, storage, and scheduling to later evidence.
-/

/-- **PUBLIC (TIER 1):** metadata for one successfully lowered resolved-program fingerprint. -/
public structure CoreFingerprintFact where
  scope : String
  algorithm : String
  digest : String
  cacheKeySafe : Bool
  deriving Repr

-- Generated `Repr` code ignores its precedence argument.
attribute [nolint unusedArguments] instReprCoreFingerprintFact.repr

/-- Flat JSON record for `CoreFingerprintFact`. -/
public def CoreFingerprintFact.toJson (f : CoreFingerprintFact) : String :=
  jsonObj [jsonStrField "scope" f.scope, jsonStrField "algorithm" f.algorithm,
    jsonStrField "digest" f.digest,
    jsonField "cacheKeySafe" (if f.cacheKeySafe then "true" else "false")]

/-- **PUBLIC (TIER 1):** lower `p` through the production typed pipeline and fingerprint the exact
flat kernel `Comp` it returns. `none` preserves dump's per-seam failure isolation: an invalid subject
still exposes its declaration/reference facts and their existing type errors. -/
public def coreFingerprintOf (p : Prog) : Option CoreFingerprintFact :=
  match Bang.TypeCheck.checkAndLowerProg p with
  | .error _ => none
  | .ok comp => some {
      scope := "resolved-program"
      algorithm := Bang.CoreFingerprint.algorithm
      digest := Bang.CoreFingerprint.fingerprint comp
      cacheKeySafe := false
    }

/-- JSON value for an already-computed optional fingerprint fact. -/
def coreFingerprintJson (fact : Option CoreFingerprintFact) : String :=
  match fact with
  | none => "null"
  | some fact => fact.toJson

/-! ### Resolved-module reachable body-slice probe

`withQueryBody` alone is NOT per-export: `checkAndLowerProg` folds every top-level `letD`/`letRecD`
into one lexical `Comp`. The projection below removes unreachable VALUE declarations before invoking
that unchanged production pipeline. It deliberately keeps the non-value environment whole. Because
impl/handler selection is type-directed rather than represented by `nameRefEdgesOf`, every retained
non-value declaration is also a closure root; this safely over-retains its value dependencies instead
of risking false preservation.

Only `letD`/`letRecD` exports have a concrete body at this seam. A bounded `fnD` is a generic template
that lowers only at a concrete instantiation, while the remaining kinds have no value body. Every
export still receives an explicit row so decided absence cannot be confused with missing coverage.
Any concrete slice that fails production lowering refuses the COMPLETE projection as `null`; partial
body coverage would be an integrity bug.
-/

/-- Which body observation exists for one public export. Stable additive-schema spellings. -/
public inductive ModuleBodyStatus where
  | sliced
  | unsupportedGenericFn
  | noBodyKind
  deriving Repr, DecidableEq

/-- Machine spelling for `ModuleBodyStatus`. -/
public def ModuleBodyStatus.toJson : ModuleBodyStatus → String
  | .sliced => "\"sliced\""
  | .unsupportedGenericFn => "\"unsupported-generic-fn\""
  | .noBodyKind => "\"no-body-kind\""

/-- One public export's environment-relative body observation. `digest` is present exactly for
`status=sliced`; the two decided-absence states carry `null`. -/
public structure ModuleBodyExportFact where
  id     : String
  name   : String
  kind   : DeclKind
  status : ModuleBodyStatus
  digest : Option String
  deriving Repr

/-- One logical module's complete export-body projection. `linkReady=false` is load-bearing: these
are measurements through a whole environment, not independently validated artifacts. -/
public structure ModuleBodyFact where
  module       : String
  scope        : String
  algorithm    : String
  cacheKeySafe : Bool
  linkReady    : Bool
  exports      : List ModuleBodyExportFact
  deriving Repr

attribute [nolint unusedArguments] instReprModuleBodyStatus.repr
  instReprModuleBodyExportFact.repr instReprModuleBodyFact.repr

/-- Versioned body-slice fingerprint name. The underlying `Comp` fold is
`CoreFingerprint.algorithm`; the outer fresh tag separates this projection from whole-program and
interface digest domains. Still only a 64-bit change detector. -/
public def moduleBodyAlgorithm : String := "bang-module-body-slice-comp-v1-uint64"

/-- Does `d` denote a value declaration that may be removed when unreachable? `fnD` is included:
it is retained when a concrete selected export reaches its generic template, but an exported `fnD`
itself has no standalone concrete instantiation in this tracer. -/
def isSliceValueDecl : Decl → Bool
  | .letD .. | .letRecD .. | .fnD .. => true
  | _ => false

/-- Plain forward closure over the ONE public `nameRefEdgesOf` graph. Roots are de-duplicated by the
worklist itself; the fuel bound is sufficient because each productive step adds a previously unseen
edge target. -/
def reachableSliceNames (edges : List RefEdge) (roots : List String) : List String :=
  go (edges.length + roots.length + 1) roots roots.eraseDups
where
  go : Nat → List String → List String → List String
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, name :: work, seen =>
      let next := edges.filterMap (fun edge =>
        if edge.src == name && !seen.contains edge.tgt then some edge.tgt else none)
      let next := next.eraseDups
      go fuel (next ++ work)
        (next.foldl (fun acc dep => if acc.contains dep then acc else dep :: acc) seen)

#guard (reachableSliceNames [⟨"selected", "helper"⟩, ⟨"helper", "base"⟩,
    ⟨"unused", "other"⟩] ["selected"] |>.contains "base")
#guard !(reachableSliceNames [⟨"selected", "helper"⟩, ⟨"unused", "other"⟩]
    ["selected"] |>.contains "other")

/-- Build the environment-relative value slice for one concrete export. Source order is preserved.
Every non-value declaration is retained AND rooted so helpers reachable only through implicit
impl/handler/generic-environment paths cannot be dropped. `pubNames` is narrowed to retained decls;
imports/uses and all other program metadata are unchanged. -/
public def reachableValueSliceProg (p : Prog) (name : String) : Prog :=
  let environmentRoots := p.decls.filterMap (fun d =>
    if isSliceValueDecl d then none else some d.name)
  let live := reachableSliceNames (nameRefEdgesOf p) (name :: environmentRoots)
  let decls := p.decls.filter (fun d => !isSliceValueDecl d || live.contains d.name)
  let keptNames := decls.map Decl.name
  let retainedPubs := p.pubNames.filter (fun n => keptNames.contains n)
  { p with pubNames := retainedPubs, decls := decls, body := .var name, isLibrary := false }

/-- Fresh-domain digest for one successfully lowered reachable body slice. -/
def moduleBodyDigest (comp : Bang.Comp) : String :=
  Bang.CoreFingerprint.toHex16
    (Bang.CoreFingerprint.step (Bang.CoreFingerprint.tag 71)
      (Bang.CoreFingerprint.hashComp comp))

/-- One export row rendered with every key present. -/
public def ModuleBodyExportFact.toJson (f : ModuleBodyExportFact) : String :=
  jsonObj [jsonStrField "id" f.id, jsonStrField "name" f.name,
    jsonField "kind" f.kind.toJson, jsonField "status" f.status.toJson,
    jsonOptStrField "digest" f.digest]

/-- One module body projection rendered independently from `moduleInterfaces`; nesting body facts
inside the interface record would make body edits destroy the checked-interface firewall. -/
public def ModuleBodyFact.toJson (f : ModuleBodyFact) : String :=
  jsonObj [jsonStrField "module" f.module, jsonStrField "scope" f.scope,
    jsonStrField "algorithm" f.algorithm,
    jsonField "cacheKeySafe" (if f.cacheKeySafe then "true" else "false"),
    jsonField "linkReady" (if f.linkReady then "true" else "false"),
    jsonField "exports" (jsonArr (f.exports.map ModuleBodyExportFact.toJson))]

/-- **PUBLIC (TIER 1):** project resolver-owned exports onto reachable concrete body slices. Every
export gets a row. A missing export or failed concrete slice refuses the whole result, so callers
cannot mistake partial coverage for completeness. -/
public def moduleBodyFactsOf (p : Prog) (declModule : List (String × String))
    (moduleExports : List (String × List String)) : Except String (List ModuleBodyFact) :=
  moduleExports.mapM fun (moduleName, names) => do
    let exports ← names.eraseDups.mapM fun name => do
      let d ← match p.decls.find? (·.name == name) with
        | some d => pure d
        | none => throw s!"module bodies '{moduleName}': exported declaration '{name}' is absent from the merged program"
      let localName := if moduleName == "@entry" then name else displayDeclName declModule name
      let id := moduleName ++ "::" ++ localName
      match d with
      | .letD .. | .letRecD .. =>
          match Bang.TypeCheck.checkAndLowerProg (reachableValueSliceProg p name) with
          | .error e => throw s!"module bodies '{moduleName}': slice for exported declaration '{name}' failed to lower: {e}"
          | .ok comp => pure ⟨id, localName, DeclKind.of d, .sliced, some (moduleBodyDigest comp)⟩
      | .fnD .. => pure ⟨id, localName, DeclKind.of d, .unsupportedGenericFn, none⟩
      | _ => pure ⟨id, localName, DeclKind.of d, .noBodyKind, none⟩
    pure ⟨moduleName, "resolved-program-module-body-slice", moduleBodyAlgorithm,
      false, false, exports⟩

/-- JSON value for complete module-body coverage. Whole-program invalidity and any projection
inconsistency both refuse this seam as `null`, while sibling dump facts remain available. -/
def moduleBodiesJson (core : Option CoreFingerprintFact) (p : Prog)
    (declModule : List (String × String))
    (moduleExports : List (String × List String)) : String :=
  if core.isNone then "null" else
    match moduleBodyFactsOf p declModule moduleExports with
    | .ok bodies => jsonArr (bodies.map ModuleBodyFact.toJson)
    | .error _ => "null"

/-! ### Resolved-module public-interface probe

The whole-program `Comp` fingerprint above is an implementation-result observation. A module's
PUBLIC INTERFACE is a different boundary: it contains the checked type/row or structural shape of
each exported declaration, but deliberately excludes implementation bodies. Consequently a body
edit may change `coreFingerprint` while leaving this interface unchanged. That is useful evidence
for future analysis/type-check invalidation, but it is not a separately compiled code artifact and
cannot by itself justify skipping link/code-generation work.

The resolver supplies the exact final declaration spellings exported by each original module.
`Query` then projects those names onto the same `DeclFact`s already emitted by `dump`; there is no
second declaration checker or reconstruction from source text.

`scope=resolved-program-module-interface` and `separateCompilationReady=false` are load-bearing.
The facts are grouped per source module, but their checked types still come from whole-program
elaboration; user-effect labels, for example, are allocated by global declaration order. This view
can measure an interface firewall, while explicitly exposing why it is not yet an independent
module artifact.
-/

/-- Stable algorithm name for the canonical interface-record fold. Version 2 adds owner-local
declared public-law contracts to each export. The digest remains an experimental 64-bit change
detector, not a persistent cache key. -/
public def moduleInterfaceAlgorithm : String := "bang-module-interface-json-v2-uint64"

/-- **PUBLIC (TIER 1):** one law statement declared by a trait/effect export. This is declaration
text, not the realization cross-product returned by `lawInstancesOf` and not evidence that the law
was proved or tested. -/
public structure DeclaredLawFact where
  id         : String
  contractId : String
  name   : String
  params : List String
  body   : String
  deriving Repr

/-- Project the owner-local law declarations from one surface declaration. `showSurf` is the same
canonical surface renderer used by the existing instance-law seam; no second body printer exists. -/
def declaredLawFactsOf (contractId : String) : Decl → List DeclaredLawFact
  | .traitD _ _ _ laws | .effectD _ _ laws =>
      laws.map (fun law =>
        ⟨contractId ++ ":" ++ law.name, contractId, law.name, law.params,
          Bang.Format.showSurf law.body⟩)
  | _ => []

/-- One declared public-law contract → its JSON object. -/
public def DeclaredLawFact.toJson (f : DeclaredLawFact) : String :=
  jsonObj [jsonStrField "id" f.id, jsonStrField "contractId" f.contractId,
    jsonStrField "name" f.name, jsonField "params" (jsonStrArr f.params),
    jsonStrField "body" f.body]

/-- **PUBLIC (TIER 1):** one exported declaration in a resolved module interface. `id` is path-free
and presentation-independent (`Module::localName`); implementation bodies are intentionally absent. -/
public structure ModuleExportFact where
  id        : String
  name      : String
  kind      : DeclKind
  type      : Option String
  row       : Option String
  typeError : Option String
  shape     : Option String
  laws      : List DeclaredLawFact
  deriving Repr

/-- **PUBLIC (TIER 1):** one resolved module's public interface and its experimental digest. -/
public structure ModuleInterfaceFact where
  module       : String
  scope        : String
  algorithm    : String
  digest       : String
  cacheKeySafe : Bool
  separateCompilationReady : Bool
  exports      : List ModuleExportFact
  deriving Repr

-- Generated `Repr` code ignores its precedence argument.
attribute [nolint unusedArguments] instReprDeclaredLawFact.repr instReprModuleExportFact.repr
  instReprModuleInterfaceFact.repr

/-- One module-export record → its canonical JSON object. -/
public def ModuleExportFact.toJson (f : ModuleExportFact) : String :=
  jsonObj [jsonStrField "id" f.id, jsonStrField "name" f.name,
    jsonField "kind" f.kind.toJson, jsonOptStrField "type" f.type,
    jsonOptStrField "row" f.row, jsonOptStrField "typeError" f.typeError,
    jsonField "shape" (f.shape.getD "null"),
    jsonField "laws" (jsonArr (f.laws.map DeclaredLawFact.toJson))]

/-- One module-interface record → its public JSON object. -/
public def ModuleInterfaceFact.toJson (f : ModuleInterfaceFact) : String :=
  jsonObj [jsonStrField "module" f.module, jsonStrField "scope" f.scope,
    jsonStrField "algorithm" f.algorithm,
    jsonStrField "digest" f.digest,
    jsonField "cacheKeySafe" (if f.cacheKeySafe then "true" else "false"),
    jsonField "separateCompilationReady" (if f.separateCompilationReady then "true" else "false"),
    jsonField "exports" (jsonArr (f.exports.map ModuleExportFact.toJson))]

/-- Convert one resolver-owned exported declaration name into the interface projection of the
already-computed `DeclFact`. -/
def moduleExportFactOf (declModule : List (String × String)) (moduleName : String)
    (f : DeclFact) (laws : List DeclaredLawFact) : ModuleExportFact :=
  let localName := if moduleName == "@entry" then f.name else displayDeclName declModule f.name
  { id := moduleName ++ "::" ++ localName, name := localName, kind := f.kind,
    type := f.type, row := f.row, typeError := f.typeError, shape := f.shape, laws }

/-- **PUBLIC (TIER 1):** project resolver-owned `(module, final exported declaration names)` onto
the dump's existing declaration facts. Missing names fail loudly at this pure seam; the JSON layer
isolates that inconsistency as `null` rather than emitting a silently incomplete interface. -/
public def moduleInterfaceFactsOf (decls : List Decl) (facts : List DeclFact)
    (declModule : List (String × String))
    (moduleExports : List (String × List String)) : Except String (List ModuleInterfaceFact) :=
  moduleExports.mapM fun (moduleName, names) => do
    let exports ← names.eraseDups.mapM fun name => do
      let f ← match facts.find? (·.name == name) with
        | some f => pure f
        | none => throw s!"module interface '{moduleName}': exported declaration '{name}' is absent from the merged fact base"
      let d ← match decls.find? (·.name == name) with
        | some d => pure d
        | none => throw s!"module interface '{moduleName}': exported declaration '{name}' is absent from the merged program"
      pure (moduleExportFactOf declModule moduleName f
        (declaredLawFactsOf (stableDeclId declModule f.name) d))
    let payload := jsonObj [jsonStrField "module" moduleName,
      jsonField "exports" (jsonArr (exports.map ModuleExportFact.toJson))]
    let digest := Bang.CoreFingerprint.toHex16
      (Bang.CoreFingerprint.hashTextWith (Bang.CoreFingerprint.tag 70) payload)
    pure (ModuleInterfaceFact.mk moduleName "resolved-program-module-interface"
      moduleInterfaceAlgorithm digest false false exports)

/-- JSON value for checked module interfaces. Whole-program lowering must succeed because this is a
checked-interface view, not a best-effort parse inventory. -/
def moduleInterfacesJson (core : Option CoreFingerprintFact) (decls : List Decl)
    (facts : List DeclFact) (declModule : List (String × String))
    (moduleExports : List (String × List String)) : String :=
  if core.isNone then "null" else
    match moduleInterfaceFactsOf decls facts declModule moduleExports with
    | .ok interfaces => jsonArr (interfaces.map ModuleInterfaceFact.toJson)
    | .error _ => "null"

/-- **PUBLIC entry, `Prog`-taking** (the RESOLVER-AWARE route — `Main.lean`'s multi-file path hands
an already-resolved-and-merged `Prog` here, optionally with a `declModule` provenance map from ITS
OWN pre-merge resolution walk — `none` per-name when unavailable, e.g. the single-file/stdin
route). `bangVersion` is `Main.lean`'s own version constant, threaded in (this module never
hardcodes it — see this section's header). `{"ok":true,"schemaVersion":1,"bangVersion":"0.1.1",
   "coreFingerprint":{...},"moduleInterfaces":[ModuleInterfaceFact,...],
   "moduleBodies":[ModuleBodyFact,...],
   "modules":[ModuleFact,...],"moduleDeps":[ModuleDepFact,...],"decls":[DeclFact,...],
"refs":[RefEdge,...],"laws":[...],"imports":[...],"uses":[...]}` — the
schema documented in `docs/reference/language.md`. -/
public def dumpJsonP (p : Prog) (bangVersion : String) (declModule : List (String × String) := [])
    (modules : List ModuleFact := [entryModuleFact])
    (moduleDeps : List ModuleDepFact := [])
    (moduleExports : List (String × List String) := [])
    (sourceImports : Option (List Bang.Surface.ImportDecl) := none)
    (sourceUses : Option (List Bang.Surface.UseDecl) := none) : String :=
  let facts := (declFactsOf p).map (fun f => f.withModule (declModule.lookup f.name))
  let core := coreFingerprintOf p
  let exports := if moduleExports.isEmpty then [("@entry", p.pubNames)] else moduleExports
  let imports := sourceImports.getD p.imports
  let uses := sourceUses.getD p.uses
  let lawsJ := match Bang.TypeCheck.lawInstancesOfProg p with
    | .ok insts => insts.map (contractLawJson declModule)
    | .error _  => []   -- same per-seam failure isolation as `dumpJson`: law discovery cannot hide
                         -- otherwise valid declaration/reference/header facts.
  jsonObj [jsonField "ok" "true", jsonField "schemaVersion" (toString schemaVersion),
           jsonStrField "bangVersion" bangVersion,
           jsonField "coreFingerprint" (coreFingerprintJson core),
           jsonField "moduleInterfaces" (moduleInterfacesJson core p.decls facts declModule exports),
           jsonField "moduleBodies" (moduleBodiesJson core p declModule exports),
           jsonField "modules" (jsonArr (modules.map ModuleFact.toJson)),
           jsonField "moduleDeps" (jsonArr (moduleDeps.map ModuleDepFact.toJson)),
           jsonField "decls" (jsonArr (facts.map DeclFact.toJson)),
           jsonField "refs" (jsonArr ((nameRefEdgesOf p).map RefEdge.toJson)),
           jsonField "laws" (jsonArr lawsJ),
           jsonField "imports" (jsonArr (imports.map importJson)),
           jsonField "uses" (jsonArr (uses.map useJson))]

/-- **PUBLIC entry**: `bang query dump <file>` — the single-file/stdin route: parse `src`, assemble
the full fact base INCLUDING law instances (this route has real source text `lawInstancesOf` can
re-derive from — unlike the multi-file resolver route, see `dumpJsonP`'s note). `bangVersion` is
`Main.lean`'s own version constant, threaded in (see this section's header).

`"decls"` is expanded through `Bang.TypeCheck.expandDerives` (#109, ADR-0097 §7) — same rule as
`lawInstancesOf` a few lines below: a `deriving`-generated `trait`/`impl` is real elaborator input
and should APPEAR in the fact base, even though `DeclFact` carries no provenance marker yet (§7's
named, non-blocking follow-up — "derived" vs "hand-written" is not yet distinguishable from the
output, only PRESENCE is asserted this slice). A `expandDerives` failure (e.g. a malformed
`deriving` target) falls back to the UN-expanded `p` rather than failing the whole dump — mirrors
the law-discovery-failure isolation immediately below (one bad seam doesn't hide everything else,
ADR-0046). -/
public def dumpJson (src : String) (bangVersion : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p0 =>
      let p := (Bang.TypeCheck.expandDerives p0).toOption.getD p0
      let facts := declFactsOf p
      let core := coreFingerprintOf p
      let lawsJ := match Bang.TypeCheck.lawInstancesOf src with
        | .ok insts => insts.map (contractLawJson [])
        | .error _  => []   -- a law-discovery failure never blanks the REST of the dump (ADR-0046:
                             -- one bad seam doesn't hide everything else — matches `symbols`'s own
                             -- per-decl `typeError` isolation, not an all-or-nothing gate).
      jsonObj [jsonField "ok" "true", jsonField "schemaVersion" (toString schemaVersion),
               jsonStrField "bangVersion" bangVersion,
               jsonField "coreFingerprint" (coreFingerprintJson core),
               jsonField "moduleInterfaces"
                 (moduleInterfacesJson core p.decls facts [] [("@entry", p.pubNames)]),
               jsonField "moduleBodies"
                 (moduleBodiesJson core p [] [("@entry", p.pubNames)]),
               jsonField "modules" (jsonArr [entryModuleFact.toJson]),
               jsonField "moduleDeps" (jsonArr []),
               jsonField "decls" (jsonArr (facts.map DeclFact.toJson)),
               jsonField "refs" (jsonArr ((nameRefEdgesOf p).map RefEdge.toJson)),
               jsonField "laws" (jsonArr lawsJ),
               jsonField "imports" (jsonArr (p.imports.map importJson)),
               jsonField "uses" (jsonArr (p.uses.map useJson))]

/-! ## 3. TIER 3 — the curated CLI verbs, now THIN PROJECTIONS of Tier 1's fact lists.

`symbols` = `declFactsOf` rendered whole (one construct with `dump`'s own `"decls"` field — the
SAME `DeclFact.toJson`). `type`/`effects` = one `DeclFact` looked up by name. `def` = ditto,
wrapped as a single hit. `refs` = `nameRefEdgesOf` filtered to one target. `laws` is the same
`lawInstancesOf{,Prog}` fact list `dump` exports, narrowed to its own top-level object. -/

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): every top-level decl of `p`, in SOURCE
ORDER, rendered via the SAME `DeclFact.toJson` `dump` uses — `symbols` is `dump` narrowed to just
the `"decls"` field. -/
public def symbolsJsonP (p : Prog) : String :=
  jsonObj [jsonField "ok" "true", jsonField "symbols" (jsonArr ((declFactsOf p).map DeclFact.toJson))]

/-- **PUBLIC entry**: `bang query symbols <file>` — the single-file/stdin route: parse `src` then
defer to `symbolsJsonP`. Expanded through `Bang.TypeCheck.expandDerives` first (#109, same rule +
same failure-isolation as `dumpJson`'s own "decls" field, this section's header comment). -/
public def symbolsJson (src : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p0        => symbolsJsonP ((Bang.TypeCheck.expandDerives p0).toOption.getD p0)

/-- Look up ONE `DeclFact` by name — the shared lookup `type`/`effects`/`def` all filter through
(the Tier-3 "thin projection" move applied uniformly). -/
def factByName (p : Prog) (name : String) : Option DeclFact :=
  (declFactsOf p).find? (·.name == name)

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route). `{"ok":true,"type":"T","row":"{...}"}`
for a `DeclFact` with a checker type, or `{"ok":false,"error":"..."}` (no such decl, or the decl
has no value-level type / failed to check — `DeclFact.typeError`/kind mismatch surfaced honestly). -/
public def typeJsonP (p : Prog) (name : String) : String :=
  match factByName p name with
  | none   => errorJsonOk s!"no top-level decl named '{name}'"
  | some f =>
      match f.type, f.row, f.typeError with
      | some ty, some row, _ => jsonObj [jsonField "ok" "true", jsonStrField "type" ty, jsonStrField "row" row]
      | _, _, some e          => errorJsonOk e
      | _, _, none            => errorJsonOk s!"'{name}' ({f.kind.toJson}) has no value-level type"

/-- **PUBLIC entry**: `bang query type <file> <name>` — the single-file/stdin route: parse `src`
then defer to `typeJsonP`. -/
public def typeJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => typeJsonP p name

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route). `{"ok":true,"row":"{...}"}`, the effect
ROW alone (paradigm-as-value, queryable — the bang-specific op no general LSP has; ADR-0076's "the
compiler is a queryable service" realized at CLI cost). Same lookup/failure shape as `typeJsonP`. -/
public def effectsJsonP (p : Prog) (name : String) : String :=
  match factByName p name with
  | none   => errorJsonOk s!"no top-level decl named '{name}'"
  | some f =>
      match f.row, f.typeError with
      | some row, _  => jsonObj [jsonField "ok" "true", jsonStrField "row" row]
      | _, some e    => errorJsonOk e
      | none, none   => errorJsonOk s!"'{name}' ({f.kind.toJson}) has no value-level type"

/-- **PUBLIC entry**: `bang query effects <name> <file>` — the single-file/stdin route. Same
failure shape as `typeJson`. -/
public def effectsJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => effectsJsonP p name

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): every law instance retained by an
already merged module graph. Thin rendering of `lawInstancesOfProg`; the same list `dumpJsonP`
places in its `laws` table. -/
public def lawsJsonP (p : Prog) (declModule : List (String × String) := []) : String :=
  match Bang.TypeCheck.lawInstancesOfProg p with
  | .error e  => errorJsonOk e
  | .ok insts => jsonObj [jsonField "ok" "true",
      jsonField "laws" (jsonArr (insts.map (contractLawJson declModule)))]

/-- **PUBLIC entry**: `bang query laws <file>` — `{"ok":true,"laws":[... ]}` for every discovered
law instance, or `{"ok":false,"error":"..."}` on a parse/elaboration failure. Source-taking twin
of resolver-aware `lawsJsonP`. -/
public def lawsJson (src : String) : String :=
  match Bang.TypeCheck.lawInstancesOf src with
  | .error e  => errorJsonOk e
  | .ok insts => jsonObj [jsonField "ok" "true",
      jsonField "laws" (jsonArr (insts.map (contractLawJson [])))]

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): the decl that DEFINES `name` (by
`Decl.name` — for `traitD`/`implD` this is the trait's own name, ADR-0093's documented convention),
rendered via the SAME `DeclFact.toJson` `dump`/`symbols` use. `{"ok":false,"error":"no top-level
decl named '<name>'"}` when nothing defines it (a LOUD miss, ADR-0046 — never a guessed
nearest-match).

MULTI-FILE NAMING (KNOWN v1 characteristic, not a bug — matches `check --json`'s own documented
multi-file limitation in spirit): `p` here is the RESOLVED, MERGED `Prog` on the resolver path
(`Main.lean`'s `resolveQueryProg`) — an imported (not `use`d) decl's name is QUALIFIED by the
merge (`Parse.bang`'s `dropWs` becomes `Parse_dropWs`, `TypeCheck.mergeModules`'s own convention),
so `def`/`refs`/`effects`/`type` on a multi-file program address the QUALIFIED name. `symbols`/
`dump` surface the qualified names directly, so this is discoverable by construction. -/
public def defJsonP (p : Prog) (name : String) : String :=
  match (p.decls.find? (fun d => d.name == name)) with
  | none   => errorJsonOk s!"no top-level decl named '{name}'"
  | some d => jsonObj [jsonField "ok" "true", jsonField "symbol" (declFactOf p d).toJson]

/-- **PUBLIC entry**: `bang query def <name> <file>` — the single-file/stdin route: parse `src`
then defer to `defJsonP`. -/
public def defJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => defJsonP p name

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): every REF EDGE targeting `name` —
`nameRefEdgesOf p |>.filter (·.tgt == name)`, the Tier-3 filter over Tier 1's own edge list (`refs`
and `dump`'s `"refs"` field are the SAME computation, one construct). `{"ok":true,"refs":[
{"name","kind"},...]}` (the FROM decl's name/kind — the historical shape this verb has always had,
kept for the CURATED surface even though `dump`'s own `"refs"` array is the flat `{from,to}` edge
list; a caller wanting edges reads `dump` directly). An EMPTY array is a valid, honest answer (the
name is defined but never referenced, or isn't bound anywhere — `refs` does not itself validate
`name` exists, unlike `def`). -/
public def refsJsonP (p : Prog) (name : String) : String :=
  let froms := (nameRefEdgesOf p).filterMap (fun e => if e.tgt == name then some e.src else none)
  let hits := froms.filterMap (fun fromName => p.decls.find? (·.name == fromName) |>.map (fun d =>
    jsonObj [jsonStrField "name" d.name, jsonField "kind" (DeclKind.of d).toJson]))
  jsonObj [jsonField "ok" "true", jsonField "refs" (jsonArr hits)]

/-- **PUBLIC entry**: `bang query refs <name> <file>` — the single-file/stdin route: parse `src`
then defer to `refsJsonP`. DECL granularity (see Tier-1 header for why). -/
public def refsJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => refsJsonP p name

/-! ## 4. `bang query hover <file> <line> <col>` (#52 slice 5) — decl-granularity hover.

Promoted from the design-probe spike (`docs/notes/spanned-surf-design.md` §5, formerly
`Bang/Frontend/HoverSpike.lean`, now deleted — this IS its adoption: the spike's helper becomes a
Tier-1/3 projection of the SAME `declFactOf`/`tokenizeSpanned`/`locateToken` machinery every other
verb already reads, not a new discovery mechanism). Answers "what decl is at `line:col`, and what
is its type" at DECL granularity — the honest ceiling documented at Q1/Q2 of the design note: no
`Surf`/`P` signature change, a cursor inside a decl's body resolves to that WHOLE decl (not the
exact sub-expression under the cursor). -/

/-- Is position `(line, col)` at-or-after the START of span `sp` (`sp`'s own start, 1-based,
half-open convention matching `Span` itself)? Used to find the LAST decl whose name token starts
at-or-before the cursor — the "nearest enclosing decl by name-token order" rule. -/
def atOrAfter (line col : Nat) (sp : Span) : Bool :=
  line > sp.line || (line == sp.line && col >= sp.col)

#guard atOrAfter 1 5 ⟨1, 5, 1, 6⟩
#guard atOrAfter 1 6 ⟨1, 5, 1, 6⟩
#guard ! atOrAfter 1 4 ⟨1, 5, 1, 6⟩
#guard atOrAfter 2 1 ⟨1, 5, 1, 6⟩

/-- One decl's hover-relevant fact: its `DeclFact` (the SAME per-decl type/error/kind rendering
`symbols`/`dump` use — zero new checking) paired with the `Span` of its NAME TOKEN, the anchor a
cursor query compares against. `public`: the return type of `hoverAtP`, a Tier-1 entry. -/
public structure HoverFact where
  /-- The decl's fact record — the SAME per-decl type/error/kind rendering `symbols`/`dump` use. -/
  fact     : DeclFact
  /-- The `Span` of the decl's NAME TOKEN — the anchor a cursor-position query compares against. -/
  nameSpan : Span
  deriving Repr

/-- Every top-level decl of `p` as a `HoverFact`, in SOURCE ORDER (`p.decls`'s own list order,
matching `declFactsOf`'s own invariant) — `locateToken` finds each decl's OWN name occurrence by
construction (the FIRST occurrence of that string in `src`; a name that also occurs earlier as
some OTHER token's text is the same honest-approximation caveat `locateInMsg` already documents
and accepts for Stage B). `none` (a decl's name has no locatable token — should not happen for a
real parse, since the decl was parsed FROM this exact source) is filtered out rather than guessed. -/
def hoverFactsOf (src : String) (p : Prog) : List HoverFact :=
  p.decls.filterMap (fun d =>
    (Bang.Surface.locateToken src d.name).map (fun sp => { fact := declFactOf p d, nameSpan := sp }))

/-- **PUBLIC (TIER 1):** hover at `(line, col)` in `p` (parsed from `src`) — the nearest-enclosing
decl (the LAST decl, in source order, whose name-token START is at-or-before the cursor). `none`
when the cursor sits before every decl's name (e.g. inside the `import`/`use` header, or the file
is empty) — an honest miss, not a guess at the wrong decl. -/
public def hoverAtP (src : String) (p : Prog) (line col : Nat) : Option HoverFact :=
  let facts := hoverFactsOf src p
  let candidates := facts.filter (fun f => atOrAfter line col f.nameSpan)
  candidates.getLast?

/-- One `HoverFact` → its JSON object: `{"name","kind","type","row","typeError","span":{...}}` —
the SAME `DeclFact` fields `dump`/`symbols` render, plus the name-token `span` that answers the
POSITION query. Reuses `Bang.Diagnostics.spanJson` (the ONE `Span`-rendering convention, SSoT — no
second `{"line":...}` shape invented here). -/
def HoverFact.toJson (f : HoverFact) : String :=
  jsonObj [jsonStrField "name" f.fact.name, jsonField "kind" f.fact.kind.toJson,
           jsonOptStrField "type" f.fact.type, jsonOptStrField "row" f.fact.row,
           jsonOptStrField "typeError" f.fact.typeError,
           jsonField "span" (Bang.Diagnostics.spanJson f.nameSpan)]

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): `{"ok":true,"decl":{...HoverFact...}}`
on a hit, `{"ok":false,"error":"no decl at <line>:<col>"}` on a miss (an honest, LOUD non-answer,
ADR-0046 — never a guessed nearest decl). `src` is required alongside `p` (unlike every other
`*JsonP` entry) because hover's decl→span resolution needs the ORIGINAL source text `locateToken`
scans — the resolver's merged `Prog` alone carries no span-locatable source. -/
public def hoverJsonP (src : String) (p : Prog) (line col : Nat) : String :=
  match hoverAtP src p line col with
  | some f => jsonObj [jsonField "ok" "true", jsonField "decl" f.toJson]
  | none   => errorJsonOk s!"no decl at {line}:{col}"

/-- **PUBLIC entry**: `bang query hover <file> <line> <col>` — the single-file/stdin route: parse
`src` then defer to `hoverJsonP`. 1-INDEXED line/col (matching `Span`'s own convention). -/
public def hoverJson (src : String) (line col : Nat) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => hoverJsonP src p line col

/-! ### `#guard`s — hover's evidence (adopted verbatim from the spike, now over the real API). -/

-- SINGLE decl, cursor INSIDE its body: resolves to that decl, typed.
#guard hoverJson "let x = 3\nlet main = x + 1" 2 5 ==
  "{\"ok\":true,\"decl\":{\"name\":\"main\",\"kind\":\"let\",\"type\":\"Int\",\"row\":\"{}\",\"typeError\":null,\"span\":{\"line\":2,\"col\":5,\"endLine\":2,\"endCol\":9}}}"
-- cursor on the DECL'S OWN name token.
#guard hoverJson "let x = 3\nlet main = x + 1" 1 5 ==
  "{\"ok\":true,\"decl\":{\"name\":\"x\",\"kind\":\"let\",\"type\":\"Int\",\"row\":\"{}\",\"typeError\":null,\"span\":{\"line\":1,\"col\":5,\"endLine\":1,\"endCol\":6}}}"
-- cursor BEFORE any decl name (column 1 line 1 is `let`, before `x` at col 5) — an honest miss.
#guard hoverJson "let x = 3\nlet main = x + 1" 1 1 ==
  "{\"ok\":false,\"error\":\"no decl at 1:1\"}"

-- TWO decls: a cursor between them resolves to the EARLIER one (nearest enclosing, not nearest
-- overall) — the coarse decl-granularity approximation this verb is honest about.
#guard (match hoverAtP "let a = 1\nlet b = 2" (Bang.Surface.parseProg "let a = 1\nlet b = 2" |>.toOption |>.get!) 1 8 with
        | some f => f.fact.name | none => "MISS") == "a"
#guard (match hoverAtP "let a = 1\nlet b = 2" (Bang.Surface.parseProg "let a = 1\nlet b = 2" |>.toOption |>.get!) 2 5 with
        | some f => f.fact.name | none => "MISS") == "b"

-- a decl that FAILS to type-check renders its error, not a type (mirrors `declFactOf`'s
-- `typeError` branch — no new checker behaviour).
#guard (hoverJson "let x : Unit = 3\nlet main = 1" 1 5 |>.splitOn "typeError\":null").length == 1

-- a NON-VALUE decl (`data`) renders `type`/`row`/`typeError` all `null` (mirrors `DeclFact`'s
-- documented convention for trait/data/effect/impl — no bare-name special case needed, `hover`'s
-- JSON is shape-uniform like `dump`'s).
#guard hoverJson "data Pair = P(Int, Int)\nlet main = 1" 1 6 ==
  "{\"ok\":true,\"decl\":{\"name\":\"Pair\",\"kind\":\"data\",\"type\":null,\"row\":null,\"typeError\":null,\"span\":{\"line\":1,\"col\":6,\"endLine\":1,\"endCol\":10}}}"

-- KNOWN INTERACTION (issue #100, open, NOT fixed here): a user `data` type's rendered `type`
-- string can leak an internal μ-encoding when hover resolves to a decl whose TYPE (not shape)
-- mentions it — this corpus deliberately sticks to Int-typed decls to avoid asserting on a
-- μ-string that #100 may change out from under this test.

/-! ## 5. `bang holes <file>` (#82 item 3) — residual/underdetermined positions.

bang has NO user-facing `_` hole syntax today (the issue's own "needs small parser support"),
but the checker DOES report underdetermined positions: a residual VALUE hole zonk-extracts to a
reserved-range `tvar` (`TypeCheck.extractV`, `.tvar (holeBase + n)`), which `Format.showTy`
renders as `#N` with `N ≥ TypeCheck.holeBase`. Those `#N` markers in a decl's already-computed
`type`/`row` string ARE the underdetermined positions — a bare `id = {fun x => x}` reports
`Thunk #1000003 -> #1000003`, two positions the checker could not pin down.

`holes` is therefore a THIN PROJECTION of the SAME `DeclFact` list every other verb reads: for
each decl, scan its `type`/`row` for `#N` markers with `N ≥ holeBase`, and report the ones found.
NO new checking logic (the `Query.lean` invariant) — the holes are already in the facts `symbols`/
`dump` surface; this verb just extracts + names them. DECL granularity (no per-node span, #52) —
the honest ceiling without a Spanned-Surf tier. -/

/-- Every `#N` marker in `s` with `N ≥ TypeCheck.holeBase` — a RESIDUAL hole, not a μ-bound
`tVar` (those render `#0`-`#2`, well below `holeBase`) nor a legitimate small index. Pure string
surgery over `showTy`'s ONE `#N` rendering convention, keyed on the SAME `holeBase` the extractor
uses (SSoT — no copied `1000000`). Returns the raw marker numbers (as `#N` strings, the form a
reader sees in the `type`/`row` field), de-duplicated in first-seen order. -/
public def holeMarkersIn (s : String) : List String :=
  -- Walk the chars ONE at a time (structural recursion on the tail — always decreasing). `cur`
  -- accumulates the digit run seen since the last `#`; `inHash` marks whether we are inside a
  -- `#`-introduced number. On a non-digit (or end), a completed run is committed iff `≥ holeBase`.
  let commit (cur : List Char) (acc : List String) : List String :=
    if cur.isEmpty then acc
    else
      let n := (String.ofList cur.reverse).toNat!
      let marker := "#" ++ String.ofList cur.reverse
      if n ≥ Bang.TypeCheck.holeBase && !acc.contains marker then marker :: acc else acc
  let rec go : List Char → Bool → List Char → List String → List String
    | [],        _,     cur, acc => (commit cur acc).reverse
    | '#' :: cs, _,     cur, acc => go cs true [] (commit cur acc)
    | c :: cs,   true,  cur, acc =>
        if c.isDigit then go cs true (c :: cur) acc
        else go cs false [] (commit cur acc)
    | _ :: cs,   false, cur, acc => go cs false cur acc
  go s.toList false [] []

#guard holeMarkersIn "Thunk #1000003 -> #1000003" == ["#1000003"]
#guard holeMarkersIn "(Int + #1000002)" == ["#1000002"]
#guard holeMarkersIn "Int" == []
#guard holeMarkersIn "(mu. #0)" == []          -- a μ-bound `#0` is NOT a hole (below holeBase)
#guard holeMarkersIn "#1000004 -> #1000003 -> #1000004" == ["#1000004", "#1000003"]

/-- **PUBLIC (TIER 1):** every decl of `p` that carries a residual hole, paired with the markers
found across its `type` AND `row` (in that order). A decl with no hole is omitted (the report is
the underdetermined SUBSET, not every decl). Reuses `declFactsOf` — ONE construct with every other
verb; `holes` never re-checks the program. -/
public def holesOf (p : Prog) : List (DeclFact × List String) :=
  (declFactsOf p).filterMap (fun f =>
    let markers := (f.type.map holeMarkersIn |>.getD []) ++ (f.row.map holeMarkersIn |>.getD [])
    if markers.isEmpty then none else some (f, markers))

/-- One hole finding → its JSON object: the decl's name/kind/type/row (so a reader sees WHERE the
`#N` sits) plus the `holes` array of markers. -/
def holeFindingJson (fm : DeclFact × List String) : String :=
  let (f, markers) := fm
  jsonObj [jsonStrField "name" f.name, jsonField "kind" f.kind.toJson,
           jsonOptStrField "type" f.type, jsonOptStrField "row" f.row,
           jsonField "holes" (jsonStrArr markers)]

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): `{"ok":true,"holes":[{name,kind,type,
row,holes},...]}` — every decl with a residual/underdetermined position, in SOURCE ORDER. An EMPTY
array is the honest "nothing underdetermined" answer (the program is fully pinned) — `ok:true`
either way, matching `symbols`/`refs`'s "the caller inspects the array" convention. -/
public def holesJsonP (p : Prog) : String :=
  jsonObj [jsonField "ok" "true", jsonField "holes" (jsonArr ((holesOf p).map holeFindingJson))]

/-- **PUBLIC entry**: `bang holes <file>` — the single-file/stdin route: parse `src` then defer to
`holesJsonP`. -/
public def holesJson (src : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => holesJsonP p

/-! ## 6. `bang impact <file> <decl>` (#82 item 5) — transitive DEPENDENTS of a decl.

The pre-edit blast-radius check: "what breaks if I change `decl`?" — the TRANSITIVE closure of
decls that reference it (directly or through a chain). This is the REVERSE of the import/use graph
`nameRefEdgesOf` already exposes: a forward edge `src → tgt` ("`src`'s body mentions `tgt`") read
backwards is "`src` DEPENDS ON `tgt`". So `impact tgt` = every `src` reachable by walking edges
`tgt`-ward.

#83 CONSTRAINT (honored): #83 documents THREE duplicated Surf-walks and forbids a fourth. `impact`
adds NONE — it reuses the SAME `nameRefEdgesOf` edge list `refs`/`dump` read (the ONE public
edge-producing Surf-walk `Query.lean` exposes); the reverse closure below is a plain worklist BFS
over that flat edge list, zero new tree recursion. DECL granularity (#52). -/

/-- **PUBLIC (TIER 1):** the TRANSITIVE dependents of `name` in `p` — every decl whose body reaches
`name` directly or through a chain, via reverse-BFS over `nameRefEdgesOf`'s `src → tgt` edges
(walking `tgt`-ward: from a target back to every `src` that mentions it). Excludes `name` itself
(the report is what DEPENDS ON it, not it). De-duplicated. `fuel`-bounded (LEAF module, no `partial`
— `edges.length + 1` always suffices: each step either drains the worklist or adds a name never
seen before, and there are at most `edges.length` distinct `src` names to ever add). -/
public def dependentsOf (p : Prog) (name : String) : List String :=
  let edges := nameRefEdgesOf p
  let fuel := edges.length + 1
  let rec go : Nat → List String → List String → List String
    | 0,     _,      seen => seen
    | _+1,   [],     seen => seen
    | f+1,   n::ws,  seen =>
        let callers := edges.filterMap (fun e =>
          if e.tgt == n && e.src != name && !seen.contains e.src then some e.src else none)
        go f (callers ++ ws) (callers.foldl (fun acc m => if acc.contains m then acc else m :: acc) seen)
  go fuel [name] []

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): `{"ok":true,"decl":"<name>","dependents":
[{"name","kind"},...]}` — the transitive blast radius of editing `name`, each dependent rendered as
its `{name,kind}` (the SAME shape `refs` uses). An EMPTY array is the honest "nothing depends on it,
safe to change in isolation" answer. `{"ok":false,"error":"no top-level decl named '<name>'"}` when
`name` isn't declared (a LOUD miss, ADR-0046 — matching `def`, unlike `refs`). -/
public def impactJsonP (p : Prog) (name : String) : String :=
  if !p.decls.any (·.name == name) then
    errorJsonOk s!"no top-level decl named '{name}'"
  else
    let deps := dependentsOf p name
    let hits := deps.filterMap (fun dn => p.decls.find? (·.name == dn) |>.map (fun d =>
      jsonObj [jsonStrField "name" d.name, jsonField "kind" (DeclKind.of d).toJson]))
    jsonObj [jsonField "ok" "true", jsonStrField "decl" name, jsonField "dependents" (jsonArr hits)]

/-- **PUBLIC entry**: `bang impact <file> <decl>` — the single-file/stdin route: parse `src` then
defer to `impactJsonP`. -/
public def impactJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => impactJsonP p name

/-! ## 7. `bang semver-diff <old> <new>` (#82 item 6) — the public-surface diff.

The release battery's future companion (#72's enforcement engine, elm-package precedent): diff the
PUBLIC (`pub`) `DeclFact` surface of two programs → which pub decls were ADDED, REMOVED, or CHANGED
(a type/row change on a decl present in both). A pure comparison of two `declFactsOf` lists filtered
to `pub` — ZERO new checking logic, the SAME facts `symbols`/`dump` surface, one per program.

VERSION-BUMP MAPPING (the semver contract, elm/#72): a REMOVED or CHANGED pub decl is BREAKING
(major); an ADDED pub decl is a feature (minor); no pub change is a patch. This verb reports the
RAW facts (added/removed/changed) + the derived `bump` field so a caller (#72's release gate) keys
its policy on ONE field, never re-deriving the classification. Non-`pub` decls are INVISIBLE here
(they are not the public contract — a private decl's churn never bumps a version). -/

/-- `(name, type, row)` public-surface signature of a `DeclFact` — the tuple `semver-diff` compares.
`type`/`row` are the checker's rendered strings (`none` for a non-value kind — a trait/data/effect,
whose `shape` is its contract; a shape change on those is a v1 KNOWN GAP, see `semverDiff`'s note). -/
def pubSig (f : DeclFact) : String × Option String × Option String := (f.name, f.type, f.row)

/-- **PUBLIC (TIER 1):** the public-surface diff of `old` → `new`: `(added, removed, changed)` decl
names, where `changed` is a pub decl present in BOTH whose `(type, row)` signature differs. Compares
`declFactsOf` filtered to `pub` — one construct with every other verb. NOTE (v1 known gap, honest):
only VALUE-typed decls' `type`/`row` are compared; a `trait`/`data`/`effect`'s structural `shape`
change is NOT yet a `changed` finding (its facts carry `type := none` so two versions compare equal
on the tuple) — a forward pointer for #72's full enforcement, not a silent miss (documented in
`docs/reference/language.md`'s `bang semver-diff` section). -/
public def semverDiff (old new : Prog) : List String × List String × List String :=
  let oldPub := (declFactsOf old).filter (·.pub)
  let newPub := (declFactsOf new).filter (·.pub)
  let oldNames := oldPub.map (·.name)
  let newNames := newPub.map (·.name)
  let added   := newNames.filter (!oldNames.contains ·)
  let removed := oldNames.filter (!newNames.contains ·)
  let changed := oldPub.filterMap (fun of =>
    match newPub.find? (·.name == of.name) with
    | some nf => if pubSig of != pubSig nf then some of.name else none
    | none    => none)
  (added, removed, changed)

/-- The semver BUMP a diff implies: `major` if anything was removed or changed (BREAKING), else
`minor` if anything was added (feature), else `patch` (no public change) — the elm-package/#72
contract, derived HERE so a caller reads ONE field. -/
def semverBump (added removed changed : List String) : String :=
  if !removed.isEmpty || !changed.isEmpty then "major"
  else if !added.isEmpty then "minor"
  else "patch"

/-- **PUBLIC (TIER 1):** `{"ok":true,"bump":"major|minor|patch","added":[...],"removed":[...],
"changed":[...]}` for two already-parsed programs — the public-surface diff + its derived bump. -/
public def semverDiffJsonP (old new : Prog) : String :=
  let (added, removed, changed) := semverDiff old new
  jsonObj [jsonField "ok" "true", jsonStrField "bump" (semverBump added removed changed),
           jsonField "added" (jsonStrArr added), jsonField "removed" (jsonStrArr removed),
           jsonField "changed" (jsonStrArr changed)]

/-- **PUBLIC entry**: `bang semver-diff <oldSrc> <newSrc>` — parse both, diff their public surfaces.
A parse failure on EITHER side is an op-level `errorJsonOk` (naming which side failed). -/
public def semverDiffJson (oldSrc newSrc : String) : String :=
  match Bang.Surface.parseProgLocated oldSrc with
  | .error (m, _) => errorJsonOk s!"OLD did not parse: {m}"
  | .ok old =>
      match Bang.Surface.parseProgLocated newSrc with
      | .error (m, _) => errorJsonOk s!"NEW did not parse: {m}"
      | .ok new       => semverDiffJsonP old new

end Bang.Query
