/-
  Bang/Frontend/Annotate.lean — the `bang annotate` rewrite (#82 item 1): infer types AND effect
  rows for top-level decls, emit explicit ascriptions.
  ─────────────────────────────────────────────────────────────────────────────────────────────
  ANNOTATE REGISTERS IN THE REWRITE ARCHITECTURE (#81) — it is a `Prog → Except String Prog`
  transform living beside `fmt`/`rename` in `Bang.Rewrite`'s own shape (this module is imported by
  and re-exported through `Rewrite.lean`, not a parallel command system): `Main.lean`'s CLI dispatch
  treats `bang rewrite annotate` identically to every other verb (diff by default, `-w` writes,
  no preservation gate needed — see below for why annotate is UNGATED like `fmt`, not gated like
  `rename`).

  THE TRIPLE WIN (operator framing, #82 item 1): checking is cheaper than inference (the elaborator
  ALREADY computed every decl's type+row via `bang query`'s own `declFactsOf`/`typeStringOfDecl` —
  annotate adds NO new checking, it is a pure re-rendering of that Tier-1 fact into a SOURCE
  ascription), explicit context for agents reading source (a decl's paradigm — which effects it
  performs — becomes visible without running the checker), and EFFECT CREEP BECOMES DIFF-VISIBLE
  (a PR that adds `Div`/`throws` to a previously-`{}` row shows as a one-line diff on `annotate`'s
  own re-run, the same "diff by default" contract every rewrite already has).

  SCOPE (only `letD` has annotate work to do): `letRecD`/`fnD` carry a MANDATORY type ascription
  already (`ADR-0073`/bite-2's own grammar) — annotate reports those as already-annotated, a no-op,
  and never overwrites an existing ascription (this is an ADD-MISSING-ASCRIPTIONS tool, not a
  retype tool; a human-written ascription is authoritative even if the checker would infer a
  DIFFERENT-looking but equivalent type, e.g. a narrower row than necessary). `traitD`/`implD`/
  `dataD`/`effectD` have no value-level type at all (`Query.DeclFact.type`'s own `none` case) —
  skipped, not applicable.

  THE HARD CONSTRAINT (task #40, s8's in-flight gap): user-effect labels cannot yet be NAMED in a
  row ascription that round-trips soundly — `TypeCheck.effNames` (the `T ! {ρ}` ascription's OWN
  checking-side inverse of `showRow`) maps only the four BUILTIN names (`throws`/`state`/`stm`/
  `Div`) to kernel labels; a user label token in a `! {…}` postfix silently falls through `effNames`
  and contributes NOTHING to the checked row (a real unsoundness if annotate ever emitted one: the
  ascription would look like it constrains the row but wouldn't). `Query.typeStringOfDecl`'s
  underlying `TypeCheck.typeStringOfProgP` calls `showType`/`showRow` with `effects := []` (the
  DEFAULT — no `EffectInfo` context threaded, matching that function's own doc comment), so a row
  containing a user label renders as a BARE kernel label `eN` (`effName`'s own fallthrough) rather
  than a source name — `rowHasOnlyBuiltins` below detects exactly this signature (a comma-token
  that is not one of the four builtin names) and is annotate's SKIP gate: emit the row ascription
  only when every token is builtin-expressible, skip-with-a-note otherwise (forward pointer: s8's
  `effNames`/`effOf` extension, once landed, is what lets this gate widen — annotate itself needs
  no change then, only the gate's own predicate loosening).

  THE TYPE HALF'S OWN ROUND-TRIP CEILING: `Query.declFactOf`'s `type` string is the CHECKER's
  rendering (`TypeCheck.showVTy`/`showCTy`) of the INFERRED value type — for a `data`-declared
  value this is a STRUCTURAL rendering (`resolveTy`/bite-1 monomorphizes every `tApp` BEFORE
  `tyBoth` ever runs, so a `data List a` value's checker type is a `mu`-former, never a `List Int`
  name) — and `Ty.tMu` is `fmtTy`'s own documented "INTERNAL... never parsed in v1" former, so
  `Surface.parseTy` genuinely CANNOT round-trip it (nor the `#998`/`#999` poison markers a leaked
  `Self`/`tApp` would render as, which should never occur for a well-typed decl but are a defensive
  signal if they ever do). `annotateDecl` below treats `parseTy`'s failure as the SAME kind of
  loud, honest skip as the row gate — never a guess, never a partial/wrong ascription (ADR-0046).

  NO PRESERVATION GATE NEEDED (unlike `rename`): an ADDED ascription that round-trips through
  `parseTy` is, BY THE CHECKER'S OWN TYPING RULE for `annotS`, either accepted (the inferred type
  IS what the ascription now states, so elaboration outcome is unchanged) or rejected outright by
  `checkAndLowerProg` at emit time — there is no THIRD outcome where it silently changes behavior
  the way a rename's local-shadowing hazard can — no kernel-oracle eval comparison is needed since
  the transform cannot change which VALUE a decl evaluates to (an ascription is erased at `tyBoth`,
  contributing nothing to the kernel `Comp`/`Val` shape beyond the row's own semantic bound).

  THE ROUND-TRIP CLAIM IS SELF-VERIFIED, PER DECL, NOT MERELY ASSERTED (`roundTripsClean` below): a
  candidate ascription is re-checked BEFORE `annotateDecl` ever returns `.annotated` — splice it
  into a throwaway copy of `p`, re-run `typeStringOfDecl`, and require the SAME `(typeStr, rowStr)`
  comes back out. This caught a REAL bug while building this slice: `TypeCheck.showVTy`'s `Thunk`
  arm (`s!"Thunk{…} {showCTy b}"`) renders `Thunk (Int -> Int)` and `(Thunk Int) -> Int` IDENTICALLY
  as the string `"Thunk Int -> Int"` (a missing-parens precedence gap in `showVTy` itself, pre-
  existing, out of THIS module's leaf scope to fix — `TypeCheck.lean` is kernel-adjacent) — a
  `parseTy` round-trip of that string silently produces the WRONG `Ty` (`(Thunk Int) -> Int`, an
  arrow, not a thunked arrow), which `roundTripsClean` catches by re-deriving the type string from
  the CANDIDATE `Ty` and finding it disagrees with what was actually inferred. `Main.lean`'s
  `runRewriteAnnotate` still re-elaborates the WHOLE rewritten `Prog` via `checkAndLowerProg` before
  emitting, as a belt-and-suspenders sanity check — but `roundTripsClean` is what makes that check
  EXPECTED to pass (a per-decl catch, not a whole-file abort on one bad decl).

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0): reads `Bang.Query`'s public Tier-1 facts
  (`declFactsOf`/`typeStringOfDecl`/`splitTypeRow`) and `Bang.Frontend.Surface`'s public `parseTy`,
  produces only `Prog` values (or a per-decl skip note, never a silent guess). No kernel/typing-rule
  change, no new checking behavior — every fact consumed here is already computed by the existing
  pipeline `bang query` exposes.
-/
module

meta import Bang.Frontend.Query
public import Bang.Frontend.Query

open Bang
open Bang.Surface (Decl Prog Surf Ty)

namespace Bang.Rewrite

/-! ## 1. The row-expressibility gate (the hard constraint's own predicate). -/

/-- The four BUILTIN effect names `TypeCheck.effNames` can round-trip through a `! {…}` ascription
today (mirrors that function's own name list exactly — the SSoT is `effNames`, this is a LEAF
module's necessarily-copied mirror of its finite name set, the same "small closed enumeration,
re-derivation risk is low, import direction forbids reuse" call `Rewrite.lean`'s own module header
already makes for `renameVars`/`surfUsesVar`). -/
def builtinEffNames : List String := ["throws", "state", "stm", "Div"]

/-- Every comma-separated token in a rendered row STRING (`showRow`'s own `", "`-joined format,
wrapped in `{…}` by `Query.splitTypeRow`'s OWN convention — `"{}"` is the empty row, zero tokens;
every other case is EXACTLY `"{" ++ String.intercalate ", " toks ++ "}"`, a machine-rendered value
never raw user input, so no trimming is needed at all — stripping exactly the first and last
character is total). `String.drop`/`.trimAscii` return a `String.Slice` in this toolchain (not a
plain `String`, unlike `.dropRight`, which stays `String → String`), so the LEADING strip goes via
`List Char` instead (`.toList`/`List.drop`/`List.dropLast`/`String.ofList`, all plain
`String`↔`List Char` conversions with no Slice indirection) — trimming each split token's own
leading space (`showRow`'s `", "` separator) uses the SAME `String.ofList ∘ List.dropWhile
(· == ' ') ∘ String.toList` route for the identical reason. -/
def rowTokens (rowStr : String) : List String :=
  if rowStr == "{}" then []
  else
    let inner := String.ofList ((rowStr.toList.drop 1).dropLast)
    if inner.isEmpty then []
    else (inner.splitOn ",").map (fun tok => String.ofList (tok.toList.dropWhile (· == ' ')))

#guard rowTokens "{}" == []
#guard rowTokens "{throws}" == ["throws"]
#guard rowTokens "{throws, state}" == ["throws", "state"]

/-- Does `rowStr` contain ONLY builtin-expressible tokens? `false` on a row carrying a bare kernel
label (`e4`, …) — the SIGNATURE `typeStringOfDecl`'s `effects := []` calling convention leaves on
a user label present in the row (see module header). The gate annotate's row-emission consults. -/
def rowHasOnlyBuiltins (rowStr : String) : Bool :=
  (rowTokens rowStr).all builtinEffNames.contains

#guard rowHasOnlyBuiltins "{}" == true
#guard rowHasOnlyBuiltins "{throws}" == true
#guard rowHasOnlyBuiltins "{throws, state}" == true
#guard rowHasOnlyBuiltins "{e4}" == false
#guard rowHasOnlyBuiltins "{throws, e4}" == false

/-! ## 2. Per-decl annotation: the checked `(typeStr, rowStr)` fact → an ascription, or a skip. -/

/-- Why a decl was SKIPPED (never silently — ADR-0046) — rendered into `annotateProg`'s report. -/
public inductive SkipReason where
  | alreadyAnnotated       -- `letRecD`/`fnD`/an already-ascribed `letD`: nothing to add
  | notValueTyped          -- `traitD`/`implD`/`dataD`/`effectD`: no value-level type to ascribe
  | typeCheckFailed (msg : String)   -- the decl doesn't type-check standalone (`DeclFact.typeError`)
  | userLabelInRow (rowStr : String) -- the row carries a label `annotate` cannot yet name (s8 gap)
  | typeNotRoundTrippable (typeStr : String)  -- `parseTy` rejects the checker's own rendering (a `mu`/poison shape)
  deriving Repr, DecidableEq

/-- One decl's annotate OUTCOME: `.annotated newTy` (the ascription to splice in) or `.skipped why`. -/
public inductive AnnotateOutcome where
  | annotated (ty : Ty)
  | skipped (why : SkipReason)
  deriving Repr

/-- Build the ascription `Ty` for a checked `(typeStr, rowStr)` pair: parse `typeStr` back into a
`Ty` (`Surface.parseTy` — the round-trip ceiling, module header), then wrap in `.tEff` ONLY when
the row is non-empty AND builtin-only (an empty row needs no `! {}` suffix at all — `pTyPostEff`'s
own grammar treats absence as the unconstrained/empty case, so omitting it round-trips identically
to writing `! {}`, and omitting is the more legible ascription). Returns the SkipReason on either
failure, in the PRIORITY order the checks below run (row gate before the type-parse attempt, since
a user-labeled row is the MORE actionable message — "annotate can't name this yet" beats a raw
parse-failure string for the same decl). -/
def buildAscription (typeStr rowStr : String) : Except SkipReason Ty := do
  if !rowHasOnlyBuiltins rowStr then throw (.userLabelInRow rowStr)
  match Bang.Surface.parseTy typeStr with
  | .error _ => throw (.typeNotRoundTrippable typeStr)
  | .ok baseTy =>
      let toks := rowTokens rowStr
      return if toks.isEmpty then baseTy else .tEff toks baseTy

#guard buildAscription "Int" "{}" == .ok .tInt
#guard buildAscription "Int" "{throws}" == .ok (.tEff ["throws"] .tInt)
#guard buildAscription "Int" "{e4}" == .error (.userLabelInRow "{e4}")
#guard buildAscription "Int" "{throws, e4}" == .error (.userLabelInRow "{throws, e4}")
#guard (buildAscription "(Int" "{}").isOk == false   -- unbalanced parens: an honest parse failure, never a guessed ascription

/-- The PER-DECL round-trip self-check: does re-checking `d` WITH the candidate ascription `ty`
spliced in reproduce the SAME `(typeStr, rowStr)` `annotateDecl` inferred it from? This is the
defensive half of the round-trip claim (module header's "no preservation gate needed" argument)
made ACTUALLY defensive rather than merely asserted — a `showVTy` precedence gap (a real one found
while building this slice: `Thunk T -> U` renders ambiguously for `Thunk (T -> U)`, parsing back as
`(Thunk T) -> U`, a DIFFERENT type) is exactly the class of bug this check exists to catch, PER
DECL (so one decl's round-trip failure skips only that decl, never aborts the whole rewrite —
`Query.declFactOf`'s own "one bad seam doesn't hide everything else" precedent, ADR-0046). -/
def roundTripsClean (p : Prog) (d : Decl) (ty : Ty) (wantTypeStr wantRowStr : String) : Bool :=
  let candidate : Decl := match d with
    | .letD n _ e => .letD n (some ty) e
    | _           => d
  let p' := { p with decls := p.decls.map (fun d' => if d'.name == d.name then candidate else d') }
  match Bang.Query.typeStringOfDecl p' d.name with
  | .error _ => false
  | .ok rendered =>
      let (ty', row') := Bang.Query.splitTypeRow rendered
      ty' == wantTypeStr && row' == wantRowStr

/-- **PUBLIC (TIER 1 library API):** the annotate outcome for ONE decl `d` of program `p` — reuses
`Bang.Query`'s own Tier-1 facts (`typeStringOfDecl`/`splitTypeRow`), computing NO new checking.
`letRecD`/`fnD` are always `.alreadyAnnotated` (mandatory-ascription kinds, module header); a
`letD` with an EXISTING `some ty` is likewise `.alreadyAnnotated` (never overwrite a human
ascription); `traitD`/`implD`/`dataD`/`effectD` are `.notValueTyped`; a bare `letD n none e` is
checked via `typeStringOfDecl`, and `.error`/`.ok` route to `typeCheckFailed`/`buildAscription`.
The FINAL step, `roundTripsClean`, re-verifies the candidate ascription BEFORE returning
`.annotated` — a failure there routes to `.typeNotRoundTrippable` (the SAME skip reason a raw
`parseTy` failure uses; from a caller's view "the checker's rendering doesn't round-trip" is one
category, whether the cause is an unparseable shape or a precedence-ambiguous one). -/
public def annotateDecl (p : Prog) (d : Decl) : AnnotateOutcome :=
  match d with
  | .letRecD .. | .fnD .. => .skipped .alreadyAnnotated
  | .traitD .. | .implD .. | .dataD .. | .effectD .. => .skipped .notValueTyped
  | .letD _ (some _) _ => .skipped .alreadyAnnotated
  | .letD n none _ =>
      match Bang.Query.typeStringOfDecl p n with
      | .error e => .skipped (.typeCheckFailed e)
      | .ok rendered =>
          let (typeStr, rowStr) := Bang.Query.splitTypeRow rendered
          match buildAscription typeStr rowStr with
          | .error why => .skipped why
          | .ok ty     =>
              if roundTripsClean p d ty typeStr rowStr then .annotated ty
              else .skipped (.typeNotRoundTrippable typeStr)

/-! ## 3. The PUBLIC entry: `annotate`, a `Prog → Except String Prog` rewrite over EVERY `letD`. -/

/-- Splice an `AnnotateOutcome` into `d` — `.annotated ty` becomes `letD n (some ty) e` (the SAME
`letD` shape a human-written ascription has, so `fmt`'s printer renders it identically); `.skipped`
leaves `d` untouched (annotate never DELETES or alters a decl it can't annotate — a partial rewrite
that silently drops content would violate ADR-0046 as badly as a wrong ascription would). -/
def spliceOutcome (d : Decl) (o : AnnotateOutcome) : Decl :=
  match d, o with
  | .letD n none e, .annotated ty => .letD n (some ty) e
  | _, _ => d

/-- **PUBLIC entry (TIER 1):** infer + ascribe every top-level `letD` in `p` lacking an explicit
type. NEVER fails outright (unlike `rename`'s loud three-way `Except`) — an individual decl's
skip is recorded, not surfaced as a whole-program error, mirroring `Query.declFactOf`'s own
per-decl `typeError` isolation ("one bad seam doesn't hide everything else", ADR-0046). The
`Except String` return shape stays for UNIFORMITY with every other rewrite in this module
(`Main.lean`'s dispatch, `Rewrite.fmt`'s own doc comment) — it is `.ok` on every input; the ACTUAL
per-decl skip detail is `Main.lean`'s `runRewriteAnnotate`'s job to render (it re-derives outcomes
via `annotateOutcomes` below for the human-readable report, since this function's `Prog` return
alone cannot distinguish "already annotated" from "skipped: row gate" from "skipped: type-parse"). -/
public def annotate (p : Prog) : Except String Prog :=
  .ok { p with decls := p.decls.map (fun d => spliceOutcome d (annotateDecl p d)) }

/-- **PUBLIC (TIER 1):** every decl's outcome, PAIRED with its name — the report-rendering sibling
of `annotate` (`Main.lean`'s `runRewriteAnnotate` reads this for the "N annotated, M skipped
(reasons)" summary; `annotate` itself only needs the SPLICED `Prog`). One construct computes both:
`annotate p = .ok { p with decls := (annotateOutcomes p).map (fun (d, o) => spliceOutcome d o) }`
would be the SAME fold, kept as two calls only because `annotate`'s signature must stay
`Prog → Except String Prog` (the uniform rewrite shape) while the report needs the outcome list
itself, not just its splice result. -/
public def annotateOutcomes (p : Prog) : List (Decl × AnnotateOutcome) :=
  p.decls.map (fun d => (d, annotateDecl p d))

end Bang.Rewrite
