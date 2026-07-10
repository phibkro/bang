/-
  Bang/Frontend/Query.lean — the `bang query` fact base: a PUBLIC LIBRARY API + its CLI views (#80).
  ─────────────────────────────────────────────────────────────────────────────────────────────────
  Operator direction (2026-07-10, REFINED — API-first, three tiers): agents/users don't need a fixed
  menu of LSP-shaped operations; they need the FACTS, queryable however they like. This module is
  structured in three tiers, outward from the core:

    TIER 1 — the PUBLIC LIBRARY API (`declFactsOf`/`nameRefEdgesOf`/`lawFactsOf` below): every
      fact-producing function is `public` and documented as a REUSABLE Lean-side API, not merely CLI
      plumbing — a Lean script (or a future in-process consumer) composes these directly, the SAME
      functions `Main.lean`'s CLI dispatch calls.

    TIER 2 — THE KEY OPERATION, `bang query dump <file> --json`: the COMPLETE fact base in ONE
      export — every decl (name · kind · type · effect ROW · visibility · module) as a `DeclFact`,
      every law instance, every name-reference edge, and the program's own import/use header. A user
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
  produces only JSON strings (+ the plain `DeclFact`/`RefEdge` records Tier 1 exposes). No kernel/
  typing-rule change, no new checking behavior.
-/
module

meta import Bang.Frontend.Diagnostics
public import Bang.Frontend.Diagnostics

open Bang
open Bang.Surface (Decl Prog Surf DArms SurfArgs LetBindings HClauses Span Ty OpSig OpDef)

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
  | letD | letRecD | fnD | traitD | implD | dataD | effectD
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
  | .effectD _ ops =>
      some <| jsonObj [jsonField "ops" (jsonArr (ops.map (fun o =>
                 jsonObj [jsonStrField "name" o.1, jsonStrField "type" (Bang.Format.showTy o.2)])))]
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

/-- The checker's `type ! row` string for top-level binding `name` in program `p`, or the checker's
own error message on failure (an ill-typed program, or `name` not bound as a VALUE — e.g. naming a
`trait`/`data`/`effect`, which `Surf.var` can never resolve to). -/
def typeStringOfDecl (p : Prog) (name : String) : Except String String :=
  Bang.TypeCheck.typeStringOfProgP (withQueryBody p name)

/-- Split a rendered `"T ! {row}"` (or bare `"T"`) into `(typeStr, rowStr)` — `rowStr` is `"{}"`
when no `" ! "` separator is present (`showType`'s empty-row convention: the suffix is omitted
entirely, not printed as `"! {}"`). Pure string surgery over `TypeCheck.showType`'s ONE rendering
convention (never re-derived from a second checker call). -/
def splitTypeRow (rendered : String) : String × String :=
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
  name      : String
  kind      : DeclKind
  type      : Option String
  row       : Option String
  typeError : Option String
  shape     : Option String   -- pre-rendered JSON (already a value, not a raw string — see `toJson`)
  pub       : Bool
  module    : Option String
  deriving Repr

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
  | .effectD ..          => []
  | .letD _ _ e         => [e]
  | .letRecD _ _ e      => [e]

/-! Does `e` mention variable `nm` anywhere in its tree? Mirrors `TypeCheck.surfUsesVar`/
`dArmsUseVar`/`letBindingsUseVar` arm-for-arm (the #73-walk precedent, `TypeCheck.lean`) — copied
rather than imported since the source is a private `TypeCheck.lean` internal and this is a small,
CLOSED structural recursion over an already-public inductive (zero typing logic, so a copy cannot
drift into a different SEMANTICS the way a re-derived TYPE rule could). Covers EVERY `Surf`/
`DArms`/`SurfArgs`/`LetBindings` constructor, `lettMulti` included. -/
mutual
def surfUsesVar (nm : String) : Surf → Bool
  | .var x                         => x == nm
  | .lit _ | .getS | .unitS        => false
  | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
  | .lam _ e | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ => surfUsesVar nm e
  | .lett _ a b | .app a b | .stateS a b | .writeS a b | .pairS a b | .splitS _ _ a b
  | .binopS _ a b                  => surfUsesVar nm a || surfUsesVar nm b
  | .matchS s _ l _ r              => surfUsesVar nm s || surfUsesVar nm l || surfUsesVar nm r
  | .ifS c t e                     => surfUsesVar nm c || surfUsesVar nm t || surfUsesVar nm e
  | .matchD s arms                 => surfUsesVar nm s || dArmsUseVar nm arms
  | .withCapS _ i _ b              => surfUsesVar nm i || surfUsesVar nm b
  | .dotPerform r _ .none          => surfUsesVar nm r
  | .dotPerform r _ (.one a)       => surfUsesVar nm r || surfUsesVar nm a
  | .dotPerform r _ (.two a b)     => surfUsesVar nm r || surfUsesVar nm a || surfUsesVar nm b
  | .letRecS _ _ f b               => surfUsesVar nm f || surfUsesVar nm b
  | .lettMulti binds b             => letBindingsUseVar nm binds || surfUsesVar nm b
  -- ADR-0095 (landed post-copy, #21 s7probe rebase fix): `handleCustomS` mirrors
  -- `TypeCheck.surfUsesVar`'s own arm — `x`/`h` are binders (a clause's arg / the cap name),
  -- NOT modeled for shadowing, matching every other binder site in this copy.
  | .handleCustomS _lbl n .none _h cls b       => surfUsesVar nm n || hClausesUseVar nm cls || surfUsesVar nm b
  | .handleCustomS _lbl n (.one p) _h cls b    => surfUsesVar nm n || surfUsesVar nm p || hClausesUseVar nm cls || surfUsesVar nm b
  | .handleCustomS _lbl n (.two p q) _h cls b  => surfUsesVar nm n || surfUsesVar nm p || surfUsesVar nm q || hClausesUseVar nm cls || surfUsesVar nm b
def dArmsUseVar (nm : String) : DArms → Bool
  | .nil             => false
  | .cons _ _ b rest => surfUsesVar nm b || dArmsUseVar nm rest
def letBindingsUseVar (nm : String) : LetBindings → Bool
  | .nil            => false
  | .cons _ e rest  => surfUsesVar nm e || letBindingsUseVar nm rest
def hClausesUseVar (nm : String) : HClauses → Bool
  | .nil               => false
  | .cons _ _ b rest   => surfUsesVar nm b || hClausesUseVar nm rest
end

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
  src : String   -- the REFERENCING decl's own name (avoids the `from`/`to` reserved-word clash)
  tgt : String   -- the REFERENCED name
  deriving Repr

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

/-- **PUBLIC (TIER 1):** one law instance `(trait, law, params, body)` → its `LawFact`-shaped JSON.
Thin re-rendering of `Bang.TypeCheck.lawInstancesOf` (#60's own discovery seam) — zero new
discovery logic. -/
def lawInstanceJson (inst : String × String × List String × String) : String :=
  let (trait, law, params, body) := inst
  jsonObj [jsonStrField "trait" trait, jsonStrField "law" law,
           jsonField "params" (jsonStrArr params), jsonStrField "body" body]

/-! ## 2. TIER 2 — `bang query dump <file>`: the COMPLETE fact base in one export.

Assembles `declFactsOf` + `nameRefEdgesOf` + `lawInstancesOf` + the program's own `import`/`use`
header into ONE JSON object — the schema documented in `docs/reference/language.md`'s `bang query`
section. A caller composes ARBITRARY queries over this (a `jq`/`python`/Lean script) rather than
waiting on a new fixed verb — `tools/test-query.sh`'s composed-query demo answers a question no
verb below anticipates, over THIS export alone.

SHAPE (operator-informed, the `compiler-as-dbms-survey.md` ruling): `dump` is a FLAT RELATIONAL
fact base — `decls`/`refs`/`laws`/`imports`/`uses` are top-level ARRAYS OF FLAT RECORDS (Glean's
"predicates = tables, facts = rows" framing), never a nested tree; the concrete gate is that the
golden `dump` output loads into DuckDB with ONE `read_json` call (`tools/test-query.sh`'s
`golden-dump-duckdb-loadable` check) — no unnesting gymnastics. The curated verbs (`symbols`/
`type`/`effects`/`def`/`refs`) are DERIVED PREDICATES (views) over this extensional base — Tier 3.

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

/-- **PUBLIC entry, `Prog`-taking** (the RESOLVER-AWARE route — `Main.lean`'s multi-file path hands
an already-resolved-and-merged `Prog` here, optionally with a `declModule` provenance map from ITS
OWN pre-merge resolution walk — `none` per-name when unavailable, e.g. the single-file/stdin
route). `bangVersion` is `Main.lean`'s own version constant, threaded in (this module never
hardcodes it — see this section's header). `{"ok":true,"schemaVersion":1,"bangVersion":"0.1.0",
"decls":[DeclFact,...],"refs":[RefEdge,...],"laws":[...],"imports":[...],"uses":[...]}` — the
schema documented in `docs/reference/language.md`. -/
public def dumpJsonP (p : Prog) (bangVersion : String) (declModule : List (String × String) := []) :
    String :=
  let facts := (declFactsOf p).map (fun f => f.withModule (declModule.lookup f.name))
  -- NOTE: `lawInstancesOf` takes SOURCE TEXT, not a `Prog` (#60's own signature) — there is no
  -- `Prog`-taking sibling (matching `laws`'s own documented non-resolver-aware precedent below).
  -- `dump`'s law facts therefore come from the CALLER's original source string when available
  -- (`dumpJson`, the string-taking entry) and are an EMPTY (not absent) array on the `Prog`-only
  -- resolver route, where no single contiguous source exists to re-derive them from (the SAME
  -- `span:null`-class v1 grant `check --json`'s multi-file path already documents).
  jsonObj [jsonField "ok" "true", jsonField "schemaVersion" (toString schemaVersion),
           jsonStrField "bangVersion" bangVersion,
           jsonField "decls" (jsonArr (facts.map DeclFact.toJson)),
           jsonField "refs" (jsonArr ((nameRefEdgesOf p).map RefEdge.toJson)),
           jsonField "laws" "[]",
           jsonField "imports" (jsonArr (p.imports.map importJson)),
           jsonField "uses" (jsonArr (p.uses.map useJson))]

/-- **PUBLIC entry**: `bang query dump <file>` — the single-file/stdin route: parse `src`, assemble
the full fact base INCLUDING law instances (this route has real source text `lawInstancesOf` can
re-derive from — unlike the multi-file resolver route, see `dumpJsonP`'s note). `bangVersion` is
`Main.lean`'s own version constant, threaded in (see this section's header). -/
public def dumpJson (src : String) (bangVersion : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p =>
      let facts := declFactsOf p
      let lawsJ := match Bang.TypeCheck.lawInstancesOf src with
        | .ok insts => insts.map lawInstanceJson
        | .error _  => []   -- a law-discovery failure never blanks the REST of the dump (ADR-0046:
                             -- one bad seam doesn't hide everything else — matches `symbols`'s own
                             -- per-decl `typeError` isolation, not an all-or-nothing gate).
      jsonObj [jsonField "ok" "true", jsonField "schemaVersion" (toString schemaVersion),
               jsonStrField "bangVersion" bangVersion,
               jsonField "decls" (jsonArr (facts.map DeclFact.toJson)),
               jsonField "refs" (jsonArr ((nameRefEdgesOf p).map RefEdge.toJson)),
               jsonField "laws" (jsonArr lawsJ),
               jsonField "imports" (jsonArr (p.imports.map importJson)),
               jsonField "uses" (jsonArr (p.uses.map useJson))]

/-! ## 3. TIER 3 — the curated CLI verbs, now THIN PROJECTIONS of Tier 1's fact lists.

`symbols` = `declFactsOf` rendered whole (one construct with `dump`'s own `"decls"` field — the
SAME `DeclFact.toJson`). `type`/`effects` = one `DeclFact` looked up by name. `def` = ditto,
wrapped as a single hit. `refs` = `nameRefEdgesOf` filtered to one target. `laws` stays its own
thin wrapper (STRING-only — no `Prog`-taking sibling, matching `bang test`'s own documented
non-resolver-aware precedent: "no multi-file law-discovery need has arisen yet"). -/

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route): every top-level decl of `p`, in SOURCE
ORDER, rendered via the SAME `DeclFact.toJson` `dump` uses — `symbols` is `dump` narrowed to just
the `"decls"` field. -/
public def symbolsJsonP (p : Prog) : String :=
  jsonObj [jsonField "ok" "true", jsonField "symbols" (jsonArr ((declFactsOf p).map DeclFact.toJson))]

/-- **PUBLIC entry**: `bang query symbols <file>` — the single-file/stdin route: parse `src` then
defer to `symbolsJsonP`. -/
public def symbolsJson (src : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => symbolsJsonP p

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

/-- **PUBLIC entry**: `bang query laws <file>` — `{"ok":true,"laws":[{"trait","law","params","body"},
...]}` for every discovered law instance, or `{"ok":false,"error":"..."}` on a parse/elaboration
failure (`lawInstancesOf`'s own `Except String _`). STRING-only (no resolver — see this section's
header; matches `runTest`'s own documented precedent). -/
public def lawsJson (src : String) : String :=
  match Bang.TypeCheck.lawInstancesOf src with
  | .error e  => errorJsonOk e
  | .ok insts => jsonObj [jsonField "ok" "true", jsonField "laws" (jsonArr (insts.map lawInstanceJson))]

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

end Bang.Query
