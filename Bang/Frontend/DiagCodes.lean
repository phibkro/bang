module

/-!
  Bang/Frontend/DiagCodes.lean — stable diagnostic CODES + the `bang explain` registry (plan 013 s5).
  ─────────────────────────────────────────────────────────────────────────────────────────────────
  The rustc `error[E0499]` pattern: a diagnostic gets a STABLE, teachable code that outlives its
  message wording, and `bang explain B012` prints the code's teaching entry (summary · why · a
  minimal triggering example the battery can actually run).

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0 — the arch-check invariant): it reads NOTHING
  from the pipeline and adds NO checking. It is a pure REGISTRY — a table of `DiagEntry`s — plus two
  total functions over it:

    codeForMsg : String → Option String   -- "which code does this diagnostic message belong to?"
    explain    : String → Option DiagEntry -- "what does code B0xx mean?" (the `bang explain` verb)

  The registry is the SINGLE SOURCE OF TRUTH: `Main.lean` prefixes a diagnostic's code via
  `codeForMsg`, `bang explain` reads `explain`, and `gen-reference.py` derives the reference's
  diagnostic-codes section from this same table (drift unrepresentable — the doc is generated).

  MATCHING is by message FAMILY, not exact string: the actual diagnostic messages are dynamically
  formatted (`s!"constructor '{c}' expects {ci.arity} argument(s)"`), so an entry carries an `anchor`
  substring stable across the interpolation (`"expects"` + `"argument(s)"` via a two-key `anchors`
  list). A message matches a code ⟺ every anchor in that code's list is a substring of the message.
  The FIRST registry entry whose anchors all match wins (registry order = specificity order — the
  more-specific families are listed before the broader ones they'd otherwise shadow).

  Codes are RETROFITTED onto existing diagnostic strings only — this module invents no new checker
  behavior. The wording of a message may change freely; as long as its anchors survive, the code
  stays stable (that is the whole point of a code).
-/

public section

namespace Bang.DiagCodes

/-! ## 1. Substring test.

Lean core has no `String.isInfixOf`; `needle` is a substring of `hay` ⟺ splitting `hay` on `needle`
yields more than one piece (or `needle` is empty). Total over every input. -/

/-- `contains hay needle` — is `needle` a substring of `hay`? -/
def contains (hay needle : String) : Bool :=
  needle.isEmpty || (hay.splitOn needle).length > 1

#guard contains "constructor 'Foo' expects 2 argument(s)" "expects"
#guard contains "constructor 'Foo' expects 2 argument(s)" "argument(s)"
#guard ! contains "effect row mismatch" "not a thunk"

/-! ## 2. The registry entry + table. -/

/-- One diagnostic-code registry entry. `example?` is a minimal source string that TRIGGERS this
diagnostic (so the battery can run it and assert the code appears); `none` for a runtime-only
terminal (e.g. escaped-cap) whose trigger needs `bang run`, not `bang check`, noted in `teaching`. -/
structure DiagEntry where
  code     : String
  anchors  : List String   -- ALL must be substrings of a message for it to carry this code
  summary  : String        -- one line
  teaching : String        -- the explanation `bang explain` prints
  example? : Option String  -- a minimal triggering source string (for `check`), or none (runtime)
  deriving Repr

/-- The registry — the SINGLE SOURCE OF TRUTH for diagnostic codes. ORDER IS SPECIFICITY: an entry
whose anchors are a superset of a later entry's would shadow it, so the more-specific family is
listed first. Each `example?` is a real source string; the battery runs it and asserts the code. -/
def registry : List DiagEntry := [
  { code := "B001"
    anchors := ["keyword '"]
    summary := "a reserved keyword used where an identifier/binder is required"
    teaching :=
      "A reserved word (let, fun, handle, get, put, resume, param, with, …) cannot be used as a "
        ++ "binder or bare identifier. `resume` and `param` are reserved as binder names so the "
        ++ "explicit-resumption and carried-param forms slot in without colliding (ADR-0095 D5/#87). "
        ++ "Rename the binding to a non-keyword identifier."
    example? := some "let let = 3 in let" },
  { code := "B002"
    anchors := ["reserved by a built-in effect"]
    summary := "a custom effect declares an op name that a built-in effect already owns"
    teaching :=
      "A user `effect` cannot name an op that a built-in effect uses (get/put/raise/read/write/…) — "
        ++ "v1 has no per-effect namespacing (ADR-0092), so the names must not clash. Rename the op. "
        ++ "Real per-effect namespacing is the Q34/Q38 module-interface work, not v1."
    example? := some "effect E { get : Int -> Int }\nlet main = 3" },
  { code := "B003"
    anchors := ["effect row mismatch"]
    summary := "a computation's effect row does not match what the context expects"
    teaching :=
      "Effect rows are SETS (union = join, idempotent, unordered; ADR-0001). This fires when a "
        ++ "handler-installed or annotated row does not contain an effect a sub-computation performs, "
        ++ "or vice versa. Widen the annotation, or install the missing handler with a `with` block."
    example? := none },
  { code := "B004"
    anchors := ["not a thunk"]
    summary := "forcing (`$`) a value that is not a thunk"
    teaching :=
      "`$e` (force) evaluates a THUNK to a value; it is the only way to observe one (ADR-0007). "
        ++ "Forcing a plain Int/pair/etc. is a type error — the thing being forced was never a "
        ++ "deferred computation. Drop the `$`, or make the bound name a thunk."
    example? := some "let x = 3 in $x" },
  { code := "B005"
    anchors := ["ret", "shape value"]
    summary := "a handler clause body is not a `ret`-shape value (the ADR-0095 D4 gate)"
    teaching :=
      "In v1 a handler clause body must be a `ret`-shape value — no effects before resuming. A "
        ++ "compute-then-return body needs binop typing (ADR-0065) + resumption-grade surfacing "
        ++ "(Q27), tracked as the general-body entry gate (ADR-0095 D4). Restructure the clause so "
        ++ "it resumes with a pure value."
    example? := none },
  { code := "B007"
    anchors := ["unknown constructor"]
    summary := "a match arm names a constructor not in the scrutinee's data type"
    teaching :=
      "A `match` arm's constructor must belong to the scrutinee's `data` type. A typo, or matching a "
        ++ "constructor from a different type, fires this. Check the constructor name and that its "
        ++ "`data` declaration is in scope (imported if it lives in another module)."
    example? := none },
  { code := "B008"
    anchors := ["trailing tokens after expression"]
    summary := "the parser reached extra tokens after a complete expression"
    teaching :=
      "A complete expression was parsed but tokens remained. Usually a missing operator, a stray "
        ++ "literal, or an unclosed construct. The reported span points at the first leftover token. "
        ++ "Check for a missing `in`, `;`, operator, or delimiter."
    example? := some "1, 2" },
  { code := "B009"
    anchors := ["capability escaped its handler"]
    summary := "a capability was forced after its handler's block returned (runtime)"
    teaching :=
      "A capability (`vcap`) was forced (`$`/`!`) after the `with`/`atomically`/`state` block that "
        ++ "installed it had already returned. This is a defined fail-loud terminal (`escapedCap`, "
        ++ "ADR-0063), not corruption. Move the force inside the handler's scope, or restructure so "
        ++ "the capability does not outlive it. Triggers at RUNTIME (`bang run`), not `bang check`."
    example? := none },
  { code := "B010"
    anchors := ["no impl of '"]
    summary := "a trait bound is unsatisfied — no impl of the trait for the carrier"
    teaching :=
      "A bounded function or method needs an `impl Trait for Carrier`, and none is in scope for this "
        ++ "carrier. Provide the `impl`, or annotate the use so the carrier constructor resolves "
        ++ "(`… : Option Int`). Imports bring another module's impls into scope."
    example? := none },
  { code := "B011"
    anchors := ["payload arity ≤ 2"]
    summary := "a data constructor declares more than 2 payload fields"
    teaching :=
      "v1 caps a `data` constructor's payload at arity 2. Nest a tuple to carry more: "
        ++ "`Node((a, b), c)` instead of `Node(a, b, c)`. The cap keeps the elaboration's tuple "
        ++ "descent bounded (structOK / #50)."
    example? := some "data T = C(Int, Int, Int)\nlet main = 3" },
  { code := "B012"
    anchors := ["ambiguous constructor"]
    summary := "a bare constructor name is owned by two or more co-present `data` types"
    teaching :=
      "A constructor's true identity is `(dataName, ctorName)`, not the bare name alone (ADR-0099). "
        ++ "A bare reference resolves when exactly ONE in-scope `data` type owns that ctor name; two "
        ++ "or more sharing it is ambiguous. Write the type-qualified form `Type_Ctor` (e.g. "
        ++ "`IntList_Nil`) to disambiguate — an ordinary identifier, the same `Mod_Type` convention "
        ++ "module qualification already uses."
    example? := some "data List a = Nil | Cons(a, List a)\ndata IntList = Nil | Cons(Int, IntList)\nNil" },
  { code := "B013"
    anchors := ["is a sibling `let rec` defined later"]
    summary := "a nested `let rec` forward-references a sibling `let rec` bound later in the same block"
    teaching :=
      "A nested `let rec` (the pre-#97 mutual-recursion workaround) can only call EARLIER siblings — "
        ++ "each inner `let rec` is bound SEQUENTIALLY, so a forward reference to one bound later in "
        ++ "the same enclosing body is genuinely unbound at that point. Reorder so every sibling calls "
        ++ "only earlier siblings (leaf-level rules first), restructure into ONE self-recursive "
        ++ "function, or — the direct fix — use the mutual `let rec f : T1 = e1 and g : T2 = e2 in "
        ++ "body` form (#97 item 2), which gives every sibling simultaneous visibility of every other."
    example? := some
      "let rec outer : Int -> Int ! {Div} = fun n => let rec a : Int -> Int ! {Div} = fun m => ($b) m in let rec b : Int -> Int ! {Div} = fun m => ($a) m in ($a) n in ($outer) 3" },
  -- B006 is the BROAD constructor-arity family — listed LAST of the constructor cluster so the
  -- specific families above (B007 unknown, B011 payload) win their own messages before this
  -- `"constructor '"`-anchored catch-all would shadow them (registry order = specificity).
  { code := "B006"
    anchors := ["constructor '"]
    summary := "a data constructor is applied to the wrong number of arguments"
    teaching :=
      "A `data` constructor must be applied to EXACTLY its declared arity. `Cons(x)` when `Cons` "
        ++ "takes 2, or `Nil(x)` when `Nil` takes none, both fire this. Supply the right number of "
        ++ "arguments (nest a tuple if the payload is compound — v1 caps constructor payload at 2)."
    example? := none },
  { code := "B014"
    anchors := ["wildcard arm '_'"]
    summary := "a match's `_` wildcard arm is misplaced or covers nothing (issue #101)"
    teaching :=
      "A `_ -> body` wildcard arm expands to one fresh arm per constructor NOT already covered by "
        ++ "an earlier explicit arm (reusing `body`, ignoring the payload) — it must be the LAST arm "
        ++ "(arms after it can never fire, since it always matches), needs at least one explicit "
        ++ "constructor arm before it to name the match's data type, and must cover at least one "
        ++ "constructor (a wildcard over an already-exhaustive match is dead code). Move it last, "
        ++ "add an explicit arm to anchor the type, or drop it if every constructor is already named."
    example? := some "data Color = Red | Green | Blue\nmatch Red { _ -> 1, Green -> 2 }" },
  { code := "B015"
    anchors := ["a bare function is a computation"]
    summary := "a top-level `let` binds a bare `fun` directly — it must be thunked (issue #121)"
    teaching :=
      "`fun x => …` is a COMPUTATION (a \"returner\"), not a value, but a top-level `let` binds a "
        ++ "VALUE — bang's CBPV core (ADR-0007) draws this line at every `let`, not only top-level "
        ++ "ones. Suspend the function in a thunk: `let f = {fun x => …}`, then call it forced: "
        ++ "`($f) arg`. This is the single most common trigger of the older generic \"not a "
        ++ "returner\" message, which suggested `$f` — that doesn't parse here (`$` forces a THUNK "
        ++ "to a value; a bare `fun` was never a thunk to begin with)."
    example? := some "let double = fun x => x + x\nlet main = double" },
  { code := "B016"
    anchors := ["looks like it was folded in as an application argument"]
    summary := "a top-level `let` with no `in` absorbed the next line as an application (issue #129)"
    teaching :=
      "A top-level `let name = e` with no trailing `in` parses `e` with the SAME juxtaposition-"
        ++ "application grammar an ordinary call site uses — a bare newline carries no meaning "
        ++ "(ADR-0046). So `let x = 3` followed on the next line by `let y = 4` followed by `x + y` "
        ++ "folds `4` against the following line's leading token before that line's own `let` "
        ++ "boundary is found, producing `4 x` (`.app`) instead of two separate declarations. Add a "
        ++ "trailing `in` to end the RHS on the SAME line (`let name = e in …`, script mode), or make "
        ++ "sure the value after `=` is followed IMMEDIATELY by the next `let`/decl keyword with "
        ++ "nothing else on that line (top-level-decl mode, ADR-0093)."
    example? := some "let x = 3\nlet y = 4\nx + y" }
]

/-! ## 3. The two total functions over the registry. -/

/-- Does every anchor of this entry appear in `msg`? -/
def DiagEntry.matches (e : DiagEntry) (msg : String) : Bool :=
  e.anchors.all (contains msg ·)

/-- The stable code for a diagnostic message, or `none` if no family matches (an as-yet-uncoded
diagnostic — the long tail retrofits incrementally). FIRST match wins (registry order = specificity). -/
def codeForMsg (msg : String) : Option String :=
  (registry.find? (·.matches msg)).map (·.code)

/-- The registry entry for a code (the `bang explain B0xx` lookup), or `none` for an unknown code
(the caller reports a LOUD unknown-code error). Case-insensitive on the code so `explain b004` works. -/
def explain (code : String) : Option DiagEntry :=
  let norm := code.toUpper
  registry.find? (·.code.toUpper == norm)

/-! ## 4. `#guard`s — the registry contract. -/

-- every code matches its own example's diagnostic FAMILY (anchors chosen to survive interpolation).
#guard codeForMsg "expected an identifier, got keyword 'let'" == some "B001"
#guard codeForMsg "effect E: op 'get' is reserved by a built-in effect (v1 restriction — see ADR-0092)" == some "B002"
#guard codeForMsg "effect row mismatch" == some "B003"
#guard codeForMsg "force: not a thunk ('x')" == some "B004"
#guard codeForMsg "handle: clause 'op' body must be a `ret`-shape value in v1 (no effects before resuming)" == some "B005"
#guard codeForMsg "constructor 'Cons' expects 2 argument(s)" == some "B006"
#guard codeForMsg "constructor 'Nil' takes no arguments" == some "B006"
#guard codeForMsg "unknown constructor 'Foo' in match" == some "B007"
-- the specific constructor families are NOT shadowed by B006's broad `"constructor '"` anchor.
#guard codeForMsg "constructor 'C': payload arity ≤ 2 in v1 (nest tuples)" == some "B011"
#guard codeForMsg "ambiguous constructor 'Nil' — candidates: IntList (as 'IntList_Nil'), List (as 'List_Nil')" == some "B012"
#guard codeForMsg "trailing tokens after expression: [2]" == some "B008"
#guard codeForMsg "error: a capability escaped its handler — it was forced" == some "B009"
#guard codeForMsg "no impl of 'Eq' for 'Option' — the bound 'Eq a' is unsatisfied" == some "B010"
#guard codeForMsg "constructor 'C': payload arity ≤ 2 in v1 (nest tuples)" == some "B011"
#guard codeForMsg "'b' is a sibling `let rec` defined later — siblings cannot forward-reference…" == some "B013"
-- #101: all three wildcard-arm diagnostics share the `"wildcard arm '_'"` anchor.
#guard codeForMsg "wildcard arm '_' must be the LAST arm in a match — arms after it can never fire (unreachable)" == some "B014"
#guard codeForMsg "wildcard arm '_' needs at least one explicit constructor arm to name the match's data type" == some "B014"
#guard codeForMsg "wildcard arm '_' covers no constructors — every constructor of this data type already has an explicit arm (dead code)" == some "B014"
#guard codeForMsg "let-binding 'double': a bare function is a computation (a \"returner\"), not a value — a top-level `let` binds a VALUE, so wrap it in a thunk: `let double = {fun … => …}` (see `examples/caesar`)" == some "B015"
#guard codeForMsg "app: callee is not a function — '4' is a literal, never a callable; the next line's `x` looks like it was folded in as an application argument. A top-level `let` needs `in` to end its RHS on the SAME line" == some "B016"

-- a diagnostic outside every family carries no code (honest none, not a wrong guess).
#guard codeForMsg "some brand-new diagnostic nobody has coded yet" == none

-- explain round-trips, case-insensitively; unknown code → none (Main reports it loud).
#guard (explain "B004").map (·.code) == some "B004"
#guard (explain "b004").map (·.code) == some "B004"
#guard (explain "B999").isNone
#guard (explain "B015").map (·.code) == some "B015"
#guard (explain "B016").map (·.code) == some "B016"

-- codes are UNIQUE (a duplicate would make `explain` ambiguous).
#guard (registry.map (·.code)).eraseDups.length == registry.length

end Bang.DiagCodes
