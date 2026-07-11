module

meta import Bang.Frontend.TypeCheck
public import Bang.Frontend.TypeCheck
meta import Bang.Frontend.DiagCodes
public import Bang.Frontend.DiagCodes

/-!
  Bang/Frontend/Diagnostics.lean — agent-facing structured diagnostics (`bang check --json`, #59).
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Agent-first lens (operator ruling 2026-07-09): the cheapest "LSP for agents" is not a server —
  it's the existing pipeline's diagnostics, emitted as stable JSON in one shot. This module adds
  NO new checking: it renders `TypeCheck.checkAndLower`'s result (already the production pipeline
  `bang run`/`eval` use) to the schema

      { "ok": bool, "diagnostics": [ { "severity", "code", "msg", "span" } ] }

  `span` is `{line, col, endLine, endCol}` or JSON `null` — the SAME `Option Span` the pipeline
  already produces (parse errors located by `parseProgLocated`; type/elaboration errors post-hoc
  located by `nameHint`/`locateInMsg`, #52 Stage B). `severity` is always `"error"` in v1 (the
  pipeline has no warnings yet) but the FIELD is in the schema now so adding warnings later is an
  addition, not a break.

  `code` is a COARSE, stable machine key derived from pipeline STAGE — "parse" | "type". `checkAndLower`
  itself collapses parse/elaboration/type-check/lower into one `Except (String × Option Span) Comp`
  (by design — the CLI's human path treats them uniformly), so this leaf recovers the stage the only
  way available from the PUBLIC surface: run `parseProgLocated` first (parse-only, no elaboration) — if
  THAT fails, the error is `"parse"`; otherwise `checkAndLower`'s failure (necessarily past parsing) is
  `"type"`. Two calls on the happy path re-parse once, but `parseProgLocated` is cheap (bounded fuel,
  no elaboration/unification) and this is a diagnostic tool, not the hot path.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 — the arch-check invariant): it reads the
  ALREADY-PUBLIC `checkAndLower`/`parseProgLocated`/`Span` and produces only a JSON string. No
  kernel/typing-rule change, no new checking behavior — a pure re-rendering of an existing `Except`.
-/

open Bang

namespace Bang.Diagnostics

/-! ## 1. A tiny hand-rolled JSON string emitter.

No JSON library in the tree (per the mission brief); diagnostics are a small, fixed shape, so a
~30-line emitter beats a new dependency. Escaping covers exactly what JSON requires for a string
literal: `"`, `\`, and the C0 control characters (`\n \t \r` get their short escapes; every other
control character — including the ones with no short form — gets `\u00XX`, so output is ALWAYS
valid JSON even on adversarial input, never a silent pass-through of a raw control byte). -/

/-- Escape one character for a JSON string body (the content between the quotes). -/
def jsonEscChar (c : Char) : String :=
  match c with
  | '"'  => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c    =>
    let n := c.toNat
    if n < 0x20 then
      -- control character with no short escape: \u00XX, zero-padded, lowercase hex.
      let hex := Nat.toDigits 16 n
      let hex := if hex.length < 2 then (List.replicate (2 - hex.length) '0') ++ hex else hex
      "\\u00" ++ String.ofList hex
    else
      String.singleton c

/-- A JSON string LITERAL (quotes included) for arbitrary input — total over every `String`,
including one containing `"`/`\`/control characters. The schema's byte-stability rests on this
being the ONLY place a `String` becomes JSON text. `public`: `Main.lean`'s resolver-aware `bang
check --json` (ADR-0093 follow-up ruling) reuses this to render a MODULE-RESOLUTION failure (a
stage `checkJson`'s own pipeline never sees, since resolution happens before any source string
exists to hand it) into the SAME schema, rather than hand-rolling a second escaper. -/
public def jsonStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map jsonEscChar) ++ "\""

#guard jsonStr "plain" == "\"plain\""
#guard jsonStr "" == "\"\""
#guard jsonStr "with \"quotes\" inside" == "\"with \\\"quotes\\\" inside\""
#guard jsonStr "back\\slash" == "\"back\\\\slash\""
#guard jsonStr "line\nbreak" == "\"line\\nbreak\""
#guard jsonStr "tab\ttab" == "\"tab\\ttab\""

/-! ## 2. The diagnostic schema. -/

/-- One diagnostic's SEVERITY. Only `.error` is reachable in v1 (the pipeline has no warnings) —
the constructor exists so the JSON `severity` field is already stable when a warning-producing
check lands (an addition to this `inductive`, not a schema break). -/
inductive Severity where
  | error
  deriving Repr, DecidableEq

def Severity.toJson : Severity → String
  | .error => "\"error\""

/-- A stable, coarse machine key for WHICH pipeline stage raised the diagnostic. `checkAndLower`
does not itself distinguish these (see the module header) — the caller determines the stage by
re-running `parseProgLocated` first. -/
inductive DiagCode where
  | parse
  | type
  deriving Repr, DecidableEq

def DiagCode.toJson : DiagCode → String
  | .parse => "\"parse\""
  | .type  => "\"type\""

/-- One structured diagnostic: the JSON-schema fields 1:1, `span` staying the SAME `Option Span`
the pipeline already computes (no re-derivation). -/
structure Diagnostic where
  severity : Severity
  code     : DiagCode
  msg      : String
  span     : Option Bang.Surface.Span
  deriving Repr

/-- Render one `Span` as its JSON object: `{"line":L,"col":C,"endLine":EL,"endCol":EC}`. Built with
`++` (not `s!"..."`) — Lean's string-interpolation syntax treats `{`/`}` as its OWN delimiters, so a
literal brace can't be escaped inside an `s!` template; plain concatenation sidesteps the ambiguity.
`public`: `Bang.Query`'s `hover` verb (#52 slice 5) reuses this DIRECTLY as the ONE `Span`-rendering
convention (SSoT) rather than inventing a second `{"line":...}` shape for its own `span` field. -/
public def spanJson (sp : Bang.Surface.Span) : String :=
  "{\"line\":" ++ toString sp.line ++ ",\"col\":" ++ toString sp.col ++
  ",\"endLine\":" ++ toString sp.endLine ++ ",\"endCol\":" ++ toString sp.endCol ++ "}"

/-- Render one `Diagnostic` as its JSON object. The `explainCode` field is the STABLE `bang explain`
code (`"B0xx"`) DERIVED from `msg` via `Bang.DiagCodes.codeForMsg` (SSoT — the registry, plan 013 s5),
or JSON `null` for an as-yet-uncoded diagnostic. It sits ALONGSIDE the pre-existing coarse `code`
(pipeline stage `"parse"`/`"type"`) — the two are orthogonal: `code` says WHICH stage, `explainCode`
says WHICH teachable family (feeds `bang explain`). Additive: an agent that ignored it before is
unaffected. -/
def Diagnostic.toJson (d : Diagnostic) : String :=
  let spanStr := match d.span with
    | some sp => spanJson sp
    | none    => "null"
  let explainStr := match Bang.DiagCodes.codeForMsg d.msg with
    | some c => jsonStr c
    | none   => "null"
  "{\"severity\":" ++ d.severity.toJson ++ ",\"code\":" ++ d.code.toJson ++
  ",\"explainCode\":" ++ explainStr ++
  ",\"msg\":" ++ jsonStr d.msg ++ ",\"span\":" ++ spanStr ++ "}"

/-- Render the whole result: `{"ok":bool,"diagnostics":[...]}` — exactly ONE JSON object, no
trailing content (the caller appends the single newline-terminator; this function stays a pure
string builder so it is `#guard`-able byte-exact without an `IO` harness). -/
def renderDiagnostics (ok : Bool) (diags : List Diagnostic) : String :=
  let boolStr := if ok then "true" else "false"
  let diagsStr := String.intercalate "," (diags.map Diagnostic.toJson)
  "{\"ok\":" ++ boolStr ++ ",\"diagnostics\":[" ++ diagsStr ++ "]}"

/-! ## 3. The pipeline → `Diagnostic` bridge.

`checkAndLower` collapses parse/elaborate/type-check/lower into one `Except (String × Option Span)
Comp` (SSoT with the CLI's human-readable path, `Main.runSource`'s DEFAULT arm). This function adds
NO new checking — it re-derives the STAGE by checking `parseProgLocated` first (see module header),
then renders the SAME error `checkAndLower` already produced. -/

/-- Diagnose one source string through the production TYPED pipeline (`checkAndLower` — the SAME
default `bang run`/`bang eval` use, so a diagnostic-JSON "ok" and a `bang run` success can never
disagree). `ok:true` ⟺ the program type-checks (the diagnostics list is then always empty — v1 has
no warnings to report on a passing program). `ok:false` carries exactly ONE diagnostic (the pipeline
stops at its first error; `checkAndLower` has no error-recovery/multi-error accumulation to draw
more from). -/
def diagnoseSrc (src : String) : Bool × List Diagnostic :=
  match Bang.Surface.parseProgLocated src with
  | .error (m, sp) => (false, [{ severity := .error, code := .parse, msg := m, span := sp }])
  | .ok _ =>
    match Bang.TypeCheck.checkAndLower src with
    | .error (m, sp) => (false, [{ severity := .error, code := .type, msg := m, span := sp }])
    | .ok _           => (true, [])

/-- PUBLIC entry: one source string → its exact `bang check --json` stdout line (the JSON object,
WITHOUT the trailing newline — `Main.lean` appends it via `IO.println`, keeping this a pure,
`#guard`-able function). -/
public def checkJson (src : String) : String :=
  let (ok, diags) := diagnoseSrc src
  renderDiagnostics ok diags

/-- PUBLIC: one `ok:false` diagnostic JSON object for a PARSE failure located OUTSIDE `checkJson`'s
own re-parse (#75 fix, 2026-07-10) — specifically `Main.runCheck`'s file-input header peek, which
must report a header parse error (a malformed `import`/`use` line) with its real span and
`code:"parse"`, the SAME schema `checkJson`'s own parse arm produces (`diagnoseSrc`'s `.error` case
above), rather than falling through to the `Prog`-taking path's hand-assembled `code:"type"`/
`span:null` `checkFailJson` (the #75 mislabel). Kept as its own tiny function (not a `Main.lean`
literal) so the ONE `Diagnostic`/`renderDiagnostics` schema plumbing stays inside this module —
`Main.lean` never hand-assembles JSON, mirroring why `checkFailJson` itself reuses `jsonStr` rather
than a second escaper. -/
public def parseFailJson (msg : String) (span : Option Bang.Surface.Span) : String :=
  renderDiagnostics false [{ severity := .error, code := .parse, msg := msg, span := span }]

#guard parseFailJson "expected '='" none ==
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"parse\",\"explainCode\":null,\"msg\":\"expected '='\",\"span\":null}]}"

/-! ## 4. Schema `#guard`s — byte-exact expected strings (the schema IS the contract). Each
expected string was COMPUTED via a compiled `#eval IO.println (checkJson …)` (a `lake build` run,
not an in-editor reduction — `checkAndLower` walks `bigFuel` row recursion, unreliable under
`lake env lean`/interactive `#eval` per repo lesson `lean-eval-reliable-only-compiled`; this file's
`#eval`s run compiled because `lake build` compiles the WHOLE module, this one included), never
guessed. -/

-- a clean program: ok:true, empty diagnostics.
#guard checkJson "let x = 3 in x" ==
  "{\"ok\":true,\"diagnostics\":[]}"

-- a located PARSE error: exact line/col, code "parse".
#guard checkJson "let x 3 in x" ==
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"parse\",\"explainCode\":null,\"msg\":\"expected '=', got '3'\",\"span\":{\"line\":1,\"col\":7,\"endLine\":1,\"endCol\":8}}]}"

-- a TYPE error carrying a nameHint span (forcing a plain Int names the culprit, #52 Stage B):
-- code "type", span non-null. `locateInMsg` finds the FIRST occurrence of the quoted name in
-- source — here the BINDER site (`let x`, col 5), not the later force-site (`$x`, col 14).
#guard checkJson "let x = 3 in $x" ==
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"type\",\"explainCode\":\"B004\",\"msg\":\"force: not a thunk ('x')\",\"span\":{\"line\":1,\"col\":5,\"endLine\":1,\"endCol\":6}}]}"

-- a TYPE error WITHOUT a locatable token (forcing a compound pair — no bare-var nameHint fires):
-- span is the honest `null` fallback, not a guess.
#guard checkJson "$(1, 2)" ==
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"type\",\"explainCode\":\"B004\",\"msg\":\"force: not a thunk\",\"span\":null}]}"

-- STRING-ESCAPING: a stray string-literal token surviving to "trailing tokens after expression:
-- [...]" carries REAL double-quote characters (the tokenizer keeps a string literal's delimiters
-- raw, `tokenize`'s `'"' :: rest` arm) — a naturally-occurring escaping case, byte-exact through
-- `jsonStr`'s `\"` escaping.
#guard checkJson "1, \"oops\"" ==
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"parse\",\"explainCode\":\"B008\",\"msg\":\"trailing tokens after expression: [,, \\\"oops\\\"]\",\"span\":{\"line\":1,\"col\":2,\"endLine\":1,\"endCol\":3}}]}"

end Bang.Diagnostics
