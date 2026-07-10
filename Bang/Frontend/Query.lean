/-
  Bang/Frontend/Query.lean — `bang query <op>`, the agent LSP as stateless CLI subcommands (#80).
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Operator direction (2026-07-10): agents don't need LSP-the-protocol — they need the OPERATIONS,
  as stateless CLI calls with JSON output. `bang check --json` (`Bang.Diagnostics`) is the family's
  first member and this module's schema/exit-code exemplar; `Bang.TypeCheck.lawInstancesOf` (#60)
  is the second seam, reused here directly rather than re-derived. This module adds NO new checking
  or typing logic — every op is a RE-RENDERING of what the existing pipeline (parse/elaborate/
  check) already computes, to a stable JSON shape. `--json` is the default and, in v1, the ONLY
  output — a human-rendering may piggyback later (`Bang.Diagnostics`'s own precedent: the schema is
  versioned like `check --json`'s).

  V1 OPERATION SET (name-addressed; position-addressed hover is OUT — gated on #52's Spanned-Surf
  tier, a named follow-up, since `Surf` carries no per-node span today):
    1. `symbols`  — the outline: every top-level decl, its KIND, and (for value-typed decls) its
       checker-computed `type ! row`.
    2. `effects`  — the row of ONE declaration (paradigm-as-value, queryable).
    3. `type`     — type + row of ONE binding.
    4. `laws`     — the landed `lawInstancesOf` (#60) seam, rendered as JSON.
    5. `def`/`refs` — name-addressed definition/reference sites, at DECL granularity (the same
       granularity `refs` can honestly report without per-node spans — see `refSitesOf`'s doc
       comment). A Surf-tree walk in the `firstPrivateDotAccessProg`/`surfUsesVar` pattern
       (`TypeCheck.lean`), covering EVERY `Surf`/`DArms`/`SurfArgs`/`LetBindings` constructor
       (the #73-walk precedent this module's own walk mirrors, `lettMulti` included).

  PER-DECL TYPE QUERY (`symbols`'s value-decl field, `type`, `effects`): `checkProg`/
  `typeStringOfProg` (`TypeCheck.lean`) report the type of a whole program's TRAILING BODY, not of
  an arbitrary top-level binding — there is no existing seam for "the type of just this decl". The
  sound, print-then-reparse-free route (mirroring why `checkAndLowerProg` exists beside
  `checkAndLower` at all, and why `Main.lean`'s `runCheck` explicitly REJECTS the naive
  print-then-reparse alternative for a resolved `Prog`) is: build a `Prog` with the SAME `decls`/
  `imports`/`uses` and `body := Surf.var name`, then check it via `TypeCheck.typeStringOfProgP` (the
  markers-only seam requested of — and landed by — the file owner, mirroring `checkProgRow` beside
  `checkAndLowerProg`). This module never touches `TypeCheck.lean`'s internals otherwise.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 — the arch-check invariant): it reads the
  ALREADY-PUBLIC `Prog`/`Decl`/`Surf` shapes (`Bang.Frontend.Surface`), `Bang.TypeCheck.
  lawInstancesOf`/`typeStringOfProgP`/`checkProgRow`, and `Bang.Format.showSurf`/`showTy`, and
  produces only JSON strings. No kernel/typing-rule change, no new checking behavior.
-/
module

meta import Bang.Frontend.Diagnostics
public import Bang.Frontend.Diagnostics

open Bang
open Bang.Surface (Decl Prog Surf DArms SurfArgs LetBindings Span Ty OpSig OpDef)

namespace Bang.Query

/-! ## 1. JSON emitter — reuses `Diagnostics.jsonStr` (the ONE string-escaper, SSoT) plus a few
tiny array/object combinators in the same hand-rolled, no-dependency style (`Diagnostics.lean`'s
own rationale: a small fixed shape beats a new dependency). -/

/-- A JSON array from already-rendered element strings. -/
def jsonArr (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

/-- A JSON array of STRINGS (escapes each element via the one true escaper). -/
def jsonStrArr (items : List String) : String :=
  jsonArr (items.map Bang.Diagnostics.jsonStr)

/-- One `"key":value` pair, value already rendered (caller supplies `jsonStr`-wrapped strings,
`jsonArr`-wrapped arrays, or a bare literal like `true`/`42`). -/
def jsonField (key value : String) : String :=
  Bang.Diagnostics.jsonStr key ++ ":" ++ value

/-- A JSON object from already-rendered `"key":value` fields. -/
def jsonObj (fields : List String) : String :=
  "{" ++ String.intercalate "," fields ++ "}"

/-- `{"error":"<msg>"}` — the TOOL-error shape (`Main.lean`'s unreadable-file case, exit 2 —
mirrors `check`'s convention of never folding a tool error into the ok/diagnostics schema). `msg`
is raw text, so it is `jsonStr`-escaped here (`jsonField`'s `value` parameter wants an
already-rendered JSON value, per its own doc comment). -/
def errorJson (msg : String) : String :=
  jsonObj [jsonField "error" (Bang.Diagnostics.jsonStr msg)]

/-- `{"ok":false,"error":"<msg>"}` — the uniform QUERY-FAILURE shape every op's `ok:true/false`
JSON body uses (parse error, elaboration failure, unresolvable name). Mirrors `Diagnostics.
checkFailJson`'s "one hand-assembled shape, `jsonStr` for the one string that needs escaping"
convention, extended with the `ok` discriminant every op here shares with `check --json`. `public`:
`Main.lean`'s resolver-aware dispatch (`readQuerySrc`/`resolveQueryProg`, #80) reuses this
directly for a PARSE/resolution failure discovered OUTSIDE any single `*Json`/`*JsonP` entry's own
pipeline (mirrors why `Diagnostics.jsonStr`/`parseFailJson` are `public` for the SAME reason on
`check --json`'s resolver path). -/
public def errorJsonOk (msg : String) : String :=
  jsonObj [jsonField "ok" "false", jsonField "error" (Bang.Diagnostics.jsonStr msg)]

#guard errorJson "boom" == "{\"error\":\"boom\"}"
#guard errorJsonOk "boom" == "{\"ok\":false,\"error\":\"boom\"}"
#guard jsonArr ["1", "2"] == "[1,2]"
#guard jsonStrArr ["a", "b\"c"] == "[\"a\",\"b\\\"c\"]"
#guard jsonObj [jsonField "a" "1", jsonField "b" "\"x\""] == "{\"a\":1,\"b\":\"x\"}"

/-! ## 2. `symbols` — the outline: every top-level decl, its KIND, and a structural summary.

`kind` is a STABLE machine key (`"let" | "letRec" | "fn" | "trait" | "impl" | "data" | "effect"`,
one per `Decl` constructor) — additive-only, matching `Diagnostics.DiagCode`'s own stability
convention. Value-typed decls (`let`/`letRec`/`fn`) additionally carry `"type"` (the checker's
`type ! row` string, via `TypeCheck.typeStringOfProgP` on a `body := Surf.var name` projection) —
the OTHER kinds have no value-level type to report (a `trait`/`impl`/`data`/`effect` is a STATIC
env entry, never itself a value `synthSC` can assign a `CT` to; see `TypeCheck.buildEnv`'s own
`.letD .. | .letRecD .. => pure ()` split for why only decl-BINDERS carry a checker type at all).
Those kinds instead carry a structural summary (`Bang.Format.showTy`-rendered signatures/ctors). -/

/-- Project ONE query name onto `p`: same `decls`/`imports`/`uses`, trailing body replaced by
`Surf.var name` — the sound `checkAndLowerProg`-style route (see module header) that never
reparses printed source. -/
def withQueryBody (p : Prog) (name : String) : Prog :=
  { p with body := .var name, isLibrary := false }

/-- The checker's `type ! row` string for top-level binding `name` in program `p`, or the checker's
own error message on failure (an ill-typed program, or `name` not bound as a VALUE — e.g. naming a
`trait`/`data`/`effect`, which `Surf.var` can never resolve to). -/
def typeOfDecl (p : Prog) (name : String) : Except String String :=
  Bang.TypeCheck.typeStringOfProgP (withQueryBody p name)

/-- One `OpSig` (trait method signature) rendered `"name(params) : methodTy"` — a compact,
human/agent-readable summary; `methodTy` already carries the full `Self →` arrow shape
(`OpSig.methodTy`'s own doc comment). `name`/`type` are both raw strings here — `jsonStr`-escaped
at the call site, matching every other `jsonField` use in this module (`jsonField`'s own doc
comment: its `value` parameter wants an ALREADY-RENDERED JSON value, and a bare identifier or
`showTy`/`showSurf` result is source text, not one, until escaped). -/
def opSigJson (o : OpSig) : String :=
  jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr o.name),
           jsonField "type" (Bang.Diagnostics.jsonStr (Bang.Format.showTy o.methodTy))]

/-- One `OpDef` (impl method definition) — name only (the body is source-shaped, not a summary
field; a caller wanting the body uses `def`/`refs` or reads the file). -/
def opDefJson (o : OpDef) : String :=
  jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr o.name)]

/-- One data constructor `(name, payloadTys)` rendered as `{"name":..,"payload":[tyStr,...]}`. -/
def ctorJson (c : String × List Ty) : String :=
  jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr c.1),
           jsonField "payload" (jsonStrArr (c.2.map Bang.Format.showTy))]

/-- One effect op `(name, argTy?, resTy)` (the RAW declared `Ty`, pre-elaboration — `Decl.effectD`'s
own shape, not `TypeCheck.EffectInfo`'s post-elaboration `VT`, so this needs no `ElabEnv`). -/
def effectOpJson (o : String × Ty) : String :=
  jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr o.1),
           jsonField "type" (Bang.Diagnostics.jsonStr (Bang.Format.showTy o.2))]

/-- One `symbols` entry: `{"name","kind","type"?,"ops"?,"ctors"?,"params"?,"target"?}` — fields
beyond `name`/`kind` are PRESENT only for the decl kinds that carry them (never a null placeholder
for an inapplicable field — ADR-0046: absence over a guessed default). `p` is the WHOLE program
(for `typeOfDecl`'s projection); `d` is the one decl being rendered. -/
def symbolJson (p : Prog) (d : Decl) : String :=
  match d with
  | .letD n _ _ =>
      jsonObj <| [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"let\""] ++
        (match typeOfDecl p n with
         | .ok ty => [jsonField "type" (Bang.Diagnostics.jsonStr ty)]
         | .error e => [jsonField "typeError" (Bang.Diagnostics.jsonStr e)])
  | .letRecD n _ _ =>
      jsonObj <| [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"letRec\""] ++
        (match typeOfDecl p n with
         | .ok ty => [jsonField "type" (Bang.Diagnostics.jsonStr ty)]
         | .error e => [jsonField "typeError" (Bang.Diagnostics.jsonStr e)])
  | .fnD n ps _ tr tv _ =>
      jsonObj <| [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"fn\"",
                   jsonField "params" (jsonStrArr ps),
                   jsonField "bound" (jsonObj [jsonField "trait" (Bang.Diagnostics.jsonStr tr),
                                                jsonField "typeVar" (Bang.Diagnostics.jsonStr tv)])] ++
        (match typeOfDecl p n with
         | .ok ty => [jsonField "type" (Bang.Diagnostics.jsonStr ty)]
         | .error e => [jsonField "typeError" (Bang.Diagnostics.jsonStr e)])
  | .traitD n params sigs laws =>
      jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"trait\"",
               jsonField "params" (jsonStrArr params),
               jsonField "ops" (jsonArr (sigs.map opSigJson)),
               jsonField "laws" (jsonStrArr (laws.map (·.name)))]
  | .implD n τ ops =>
      jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"impl\"",
               jsonField "target" (Bang.Diagnostics.jsonStr (Bang.Format.showTy τ)),
               jsonField "ops" (jsonArr (ops.map opDefJson))]
  | .dataD n params ctors =>
      jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"data\"",
               jsonField "params" (jsonStrArr params),
               jsonField "ctors" (jsonArr (ctors.map ctorJson))]
  | .effectD n ops =>
      jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr n), jsonField "kind" "\"effect\"",
               jsonField "ops" (jsonArr (ops.map effectOpJson))]

/-- **PUBLIC entry, `Prog`-taking** (the RESOLVER-AWARE route — `Main.lean`'s multi-file path hands
an already-resolved-and-merged `Prog` here directly, the SAME `checkAndLowerProg`-beside-
`checkAndLower` split every resolver-aware op in this module follows): every top-level decl of `p`,
in SOURCE ORDER. `{"ok":true,"symbols":[...]}` always (a `Prog` is already known to parse — nothing
left to fail at this layer; a symbol's OWN `type` field may still carry a per-decl `typeError`, one
bad decl does not blank the whole outline). -/
public def symbolsJsonP (p : Prog) : String :=
  jsonObj [jsonField "ok" "true", jsonField "symbols" (jsonArr (p.decls.map (symbolJson p)))]

/-- **PUBLIC entry**: `bang query symbols <file>` — the single-file (STDIN-compatible) route: parse
`src` then defer to `symbolsJsonP`. `{"ok":false,"error":"..."}` on a program that doesn't even
PARSE (no decls to enumerate at all) — the one failure mode `symbolsJsonP` itself can't hit. -/
public def symbolsJson (src : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => symbolsJsonP p

/-! ## 3. `type` / `effects` — type + row (or just the row) of ONE named binding.

Both are thin projections of `typeOfDecl` (the SAME `withQueryBody`/`typeStringOfProgP` route
`symbols` uses per-decl) — `effects` further trims the rendered `"T ! {row}"` string down to just
the `{row}` part (string-level, not a second checker call: `showType`'s OWN rendering, reused
verbatim by `typeStringOfProgP`, is `"{ty}"` with NO `! {...}` suffix when the row is empty — see
`Diagnostics`/`TypeCheck.showType`'s convention — so "no `!`" ⟺ the row IS `{}`, an honest reading
of the SAME string rather than a re-derivation). -/

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

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route). `{"ok":true,"type":"T","row":"{...}"}`
for the checked type of top-level binding `name` in `p`, or `{"ok":false,"error":"..."}` (an
ill-typed program, or `name` naming something with no value-level type — see `typeOfDecl`'s doc
comment). -/
public def typeJsonP (p : Prog) (name : String) : String :=
  match typeOfDecl p name with
  | .error e  => errorJsonOk e
  | .ok rendered =>
      let (ty, row) := splitTypeRow rendered
      jsonObj [jsonField "ok" "true", jsonField "type" (Bang.Diagnostics.jsonStr ty),
               jsonField "row" (Bang.Diagnostics.jsonStr row)]

/-- **PUBLIC entry**: `bang query type <file> <name>` — the single-file/stdin route: parse `src`
then defer to `typeJsonP`. `{"ok":false,"error":"..."}` on a parse failure too (the one mode
`typeJsonP` can't hit). -/
public def typeJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => typeJsonP p name

/-- **PUBLIC entry, `Prog`-taking** (resolver-aware route). `{"ok":true,"row":"{...}"}`, the effect
ROW alone (paradigm-as-value, queryable — the bang-specific op no general LSP has; ADR-0076's "the
compiler is a queryable service" realized at CLI cost). -/
public def effectsJsonP (p : Prog) (name : String) : String :=
  match typeOfDecl p name with
  | .error e  => errorJsonOk e
  | .ok rendered =>
      let (_, row) := splitTypeRow rendered
      jsonObj [jsonField "ok" "true", jsonField "row" (Bang.Diagnostics.jsonStr row)]

/-- **PUBLIC entry**: `bang query effects <name> <file>` — the single-file/stdin route. Same
failure shape as `typeJson`. -/
public def effectsJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => effectsJsonP p name

/-! ## 4. `laws` — the landed `lawInstancesOf` (#60) seam, rendered as JSON.

`lawInstancesOf` already enumerates every (trait law × matching impl) pair as a PLAIN `(traitName,
lawName, params, bodySrc)` 4-tuple — this is a pure re-rendering, zero new discovery logic (the
SAME reuse discipline `Diagnostics.checkJson` follows over `checkAndLower`). -/

/-- One law instance `(trait, law, params, body)` → its JSON object. `body` is RAW source text
(`Bang.Format.showSurf`, `lawInstancesOf`'s own doc comment), so it goes through `jsonStr` at this
call site — `jsonField`'s `value` parameter wants an already-rendered JSON value, and a raw source
string is not one until escaped (the `trait`/`law` name strings get the same treatment). -/
def lawInstanceJson (inst : String × String × List String × String) : String :=
  let (trait, law, params, body) := inst
  jsonObj [jsonField "trait" (Bang.Diagnostics.jsonStr trait), jsonField "law" (Bang.Diagnostics.jsonStr law),
           jsonField "params" (jsonStrArr params), jsonField "body" (Bang.Diagnostics.jsonStr body)]

/-- **PUBLIC entry**: `bang query laws <file>` — `{"ok":true,"laws":[{"trait","law","params","body"},
...]}` for every discovered law instance, or `{"ok":false,"error":"..."}` on a parse/elaboration
failure (`lawInstancesOf`'s own `Except String _`, e.g. malformed decls — matching `runTest`'s SAME
underlying seam's failure mode). -/
public def lawsJson (src : String) : String :=
  match Bang.TypeCheck.lawInstancesOf src with
  | .error e  => errorJsonOk e
  | .ok insts => jsonObj [jsonField "ok" "true", jsonField "laws" (jsonArr (insts.map lawInstanceJson))]

/-! ## 5. `def` / `refs` — name-addressed definition/reference sites, at DECL granularity.

Position-addressed hover is OUT of v1 (gated on #52's Spanned-Surf tier — `Surf` carries no
per-node span today, only the TOKEN-level spans `Surface.tokenizeSpanned` produces before parsing
ever discards them). What IS honestly answerable without that tier: which DECL defines a name, and
which decls REFERENCE it — this module's own `surfUsesVar` (below) mirrors `TypeCheck.
surfUsesVar`/`dArmsUseVar`/`letBindingsUseVar` EXACTLY (the #73-walk precedent this module's header
cites), covering every `Surf`/`DArms`/`SurfArgs`/`LetBindings` constructor including `lettMulti` —
copied rather than imported since the source `surfUsesVar` is a private `TypeCheck.lean` internal
and this is a small, CLOSED structural recursion over an already-public inductive (zero typing
logic, so a copy cannot drift into a different semantics the way a re-derived TYPE rule could). -/

/-! Does `e` mention variable `nm` anywhere in its tree? Mirrors `TypeCheck.surfUsesVar` arm-for-arm
(see this section's header for why it's a copy, not a reuse). -/
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
def dArmsUseVar (nm : String) : DArms → Bool
  | .nil             => false
  | .cons _ _ b rest => surfUsesVar nm b || dArmsUseVar nm rest
def letBindingsUseVar (nm : String) : LetBindings → Bool
  | .nil            => false
  | .cons _ e rest  => surfUsesVar nm e || letBindingsUseVar nm rest
end

#guard surfUsesVar "x" (.var "x") == true
#guard surfUsesVar "x" (.var "y") == false
#guard surfUsesVar "x" (.lett "y" (.var "x") (.lit 0)) == true
#guard surfUsesVar "x" (.lettMulti (.cons "y" (.var "x") .nil) (.lit 0)) == true
#guard surfUsesVar "x" (.matchD (.var "s") (.cons "C" ["a"] (.var "x") .nil)) == true

/-- Every `Surf` body attached to a `Decl` (a trait's law bodies, an impl's op bodies, a bounded
`fn`'s body, a plain `let`/`let rec`'s bound expression) — the search space `refs`/`def` walk PER
decl. A `traitD`'s own OP SIGNATURES carry no body (only a declared `Ty`, never a `Surf` — a
signature cannot reference a value by name); `dataD`/`effectD` carry no `Surf` at all (pure type-
level shape). -/
def declBodies : Decl → List Surf
  | .traitD _ _ _ laws => laws.map (·.body)
  | .implD _ _ ops     => ops.map (·.body)
  | .dataD ..           => []
  | .fnD _ _ _ _ _ b    => [b]
  | .effectD ..          => []
  | .letD _ _ e         => [e]
  | .letRecD _ _ e      => [e]

/-- Does ANY body attached to `d` mention `nm`? (`refs`'s per-decl predicate.) -/
def declMentionsVar (nm : String) (d : Decl) : Bool :=
  (declBodies d).any (surfUsesVar nm)

/-- **PUBLIC entry**: `bang query def <name> <file>` — the decl that DEFINES `name` (by `Decl.name`
— for `traitD`/`implD` this is the trait's own name, matching `Decl.name`'s documented convention
that an impl's "name" is the trait it implements, ADR-0093). `{"ok":true,"kind":"...","name":"..."}`
on a hit; `{"ok":false,"error":"no top-level decl named '<name>'"}` when nothing in the file defines
it (a LOUD miss, ADR-0046 — never a guessed nearest-match). Multiple decls can share a `Decl.name`
ONLY for `traitD`+`implD` of the same trait (by design — `git grep` on the file finds the specific
`impl` block; `def` here answers "where is `name` FIRST introduced as a top-level decl", i.e. the
`traitD`/`letD`/etc. site) — the first SOURCE-ORDER match, consistent with `symbols`'s own ordering
guarantee.

MULTI-FILE NAMING (KNOWN v1 characteristic, not a bug — matches `check --json`'s own documented
multi-file limitation in spirit): `p` here is the RESOLVED, MERGED `Prog` on the resolver path
(`Main.lean`'s `resolveQueryProg`) — an imported (not `use`d) decl's name is QUALIFIED by the
merge (`Parse.bang`'s `dropWs` becomes `Parse_dropWs`, `TypeCheck.mergeModules`'s own convention),
so `def`/`refs`/`effects`/`type` on a multi-file program address the QUALIFIED name, matching
exactly what a `bang run`/`bang check` error message on the SAME program would name. `symbols`
surfaces the qualified names directly (visible in its own `"name"` field), so this is discoverable
by construction, not a silent gotcha. -/
public def defJsonP (p : Prog) (name : String) : String :=
  match p.decls.find? (fun d => d.name == name) with
  | none   => errorJsonOk s!"no top-level decl named '{name}'"
  | some d => jsonObj [jsonField "ok" "true", jsonField "symbol" (symbolJson p d)]

/-- **PUBLIC entry**: `bang query def <name> <file>` — the single-file/stdin route: parse `src`
then defer to `defJsonP`. -/
public def defJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => defJsonP p name

/-- The bare `"kind"` string a `Decl` renders as in `symbols`/`refs` (factored out so `refs` doesn't
need a full `symbolJson` — a REF site's `kind` is a cheap tag, not the full outline entry `def`'s
single-hit answer returns). -/
def declKindJson : Decl → String
  | .letD ..    => "\"let\""
  | .letRecD .. => "\"letRec\""
  | .fnD ..     => "\"fn\""
  | .traitD ..  => "\"trait\""
  | .implD ..   => "\"impl\""
  | .dataD ..   => "\"data\""
  | .effectD .. => "\"effect\""

public def refsJsonP (p : Prog) (name : String) : String :=
  let hits := p.decls.filter (declMentionsVar name) |>.map (fun d =>
    jsonObj [jsonField "name" (Bang.Diagnostics.jsonStr d.name),
             jsonField "kind" (declKindJson d)])
  jsonObj [jsonField "ok" "true", jsonField "refs" (jsonArr hits)]

/-- **PUBLIC entry**: `bang query refs <name> <file>` — the single-file/stdin route: parse `src`
then defer to `refsJsonP`. DECL granularity (see this section's header for why: no per-node span
tier exists to report an exact line/col occurrence, and fabricating one would be a guess,
ADR-0046). `{"ok":true,"refs":[{"name","kind"},...]}` — an EMPTY `refs` array is a valid, honest
answer (the name is defined but never referenced, or `name` isn't even bound anywhere — `refs`
does not itself validate that `name` is a real binding, unlike `def`; a caller wanting "does this
name exist at all" combines this with `def`). `{"ok":false,"error":...}` only on a PARSE failure
(there is no elaboration in this op's path at all). -/
public def refsJson (src name : String) : String :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, _) => errorJsonOk m
  | .ok p         => refsJsonP p name

end Bang.Query
