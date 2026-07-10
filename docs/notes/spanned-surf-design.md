<!-- note-status: active -->
# Spanned-Surf design — located errors + LSP-hover tier (#52)

> **Status.** Design probe, not implementation. The full #52 signature ripple is its own
> fresh-context session (per the issue); this note de-risks it. **Headline finding: #52's
> Stage A (located parse errors) and Stage B (post-hoc located type errors) are ALREADY
> LANDED** (`77dec515`, `ef391650`, `95710a40`) via a cheaper post-hoc pattern than the issue
> text describes — the issue was written before that pattern was tried and shipped. What
> remains is narrower than "thread `Span` through ~30 combinators + wrap every `Surf` node":
> it is `refs`/hover POSITION-addressing (`docs/reference/language.md:699`) and located
> errors for COMPOUND (non-bare-variable) culprits. Both are addressable without a `Surf`
> signature change, at decl granularity, cheaply — see §4.

## 1. What's already landed vs what issue #52 originally scoped

The issue (filed before `ff49adb`) frames two ripples: (1) `P α` must carry spans through
~30 combinators for located PARSE errors, (2) `Surf` needs per-node spans for located TYPE
errors + hover. Both have since been addressed differently:

| Ripple as scoped by #52 | What actually shipped | Landed at |
|---|---|---|
| Thread `Span` through all ~30 `P` combinators | `PErr` carries `rest : List String` (the failure's token-list SUFFIX); `spanOfRest` resolves it to a `Span` by INDEX ARITHMETIC against `tokenizeSpanned` post-hoc — **zero signature change to any combinator** | `77dec515` |
| `Surf` carries a `Spanned` wrapper/field per node | `nameHint`/`locateInMsg`: a checker error message that NAMES its culprit (`force: not a thunk ('x')`) is resolved to a span by finding that name's token in source, post-hoc — **zero change to `Surf`** | `ef391650`, `95710a40` |

Both are wired end-to-end into `bang check`, `bang check --json`, `bang eval`, and
`bang explain` today (`Bang/Frontend/Diagnostics.lean`, `checkAndLower : Except (String ×
Option Span) Comp` in `TypeCheck.lean:3765`). `DiagCodes.lean` (plan 013 s5) retrofits a
STABLE code onto the same plain-`String` messages the same way — substring-anchor matching,
no structured error type. This is the same "message is DATA, a VIEW resolves it" shape run
three times independently (span, code, and — this note's spike — hover), which is itself
evidence the shape is right, not a coincidence to paper over.

**What genuinely remains**, confirmed by grepping the landed code for its own documented
ceiling:

1. `docs/reference/language.md:699` — `bang query`'s `refs` is DECL-granularity; **position-
   addressing (line/col → symbol) is explicitly gated on #52** and unimplemented.
2. `TypeCheck.lean:3957` (the `#guard` immediately after Stage B's tests) — a COMPOUND
   culprit (`$(1, 2)`, a nested `match`, …) has no single nameable token, so `locateInMsg`
   returns `none` and the diagnostic ships unlocated. This is the honest residual, not a bug.
3. LSP-style hover ("type at position") has zero implementation — no verb, no Lean function.

## 2. The four pinned questions

### Q1 — Span representation on `Surf`

**Recommendation: do NOT add a span to `Surf` at all, for v1's remaining scope.** Keep
resolving both (1) and (2) above the same way Stage A/B already do — post-hoc, from
`tokenizeSpanned` — rather than migrating the AST.

**Rejected alternative — `Spanned α` wrapper or a per-constructor span field.** Considered
in the original issue framing. Rejected because:
- It is a REAL ripple: ~40 `Surf` constructors, every one of the ~40 elaborator arms
  (`elabS`/`checkSC`/…), `Format.lean`'s printer, and the ENTIRE `#guard` corpus that
  constructs `Surf` literals by hand (hundreds of sites) would need updating to
  carry/ignore/thread a span — the fresh-context-session-sized cost the issue itself warns
  of — buying EXACT sub-expression location that nothing currently asks for (`refs`/hover
  need only DECL granularity per the existing `dump` schema).
- A side-table keyed by node id was considered and rejected on the SAME cost basis:
  assigning stable ids still requires annotating every `Surf` constructor at construction
  time (the parser) — it moves where the id lives, not the ripple's cost.
- Post-hoc resolution has a real ceiling (can't locate an anonymous compound sub-expression,
  O(occurrences) not O(1)) — but Stage A/B already accept this ceiling and it hasn't
  blocked a real diagnostic (the compound-culprit gap is DOCUMENTED, not hit in practice).

**If** a future need surfaces requiring EXACT sub-expression spans (e.g. an LSP server doing
real-time incremental hover on partial/invalid programs, where decl-granularity is too
coarse, or #104's comment-trivia wanting to reattach a comment to its EXACT syntactic
anchor rather than a decl) — that is a genuine operator fork, reversible now, expensive
later. Flag it as **ADR material at implementation time**, not decided here.

### Q2 — P-combinator threading

**Recommendation: no combinator signature ripple. Reuse the landed `PErr.rest`-index
pattern for the parse side (already done); reuse `tokenizeSpanned`/`locateToken` for
anything the checker needs (already done for bare-variable culprits).** For the hover verb
specifically (the one piece with no existing consumer), resolve a cursor position to a
DECL (not a sub-expression) by comparing the cursor against each decl's NAME-TOKEN span —
see the spike in §5. This needs zero parser changes: it is a post-processing step over
`Prog.decls` (already parsed) + `tokenizeSpanned` (already exists).

**Rejected alternative — state-carrying `P` (current-span threaded in parser state).** The
"real" fix giving exact per-node spans, matching Q1's rejected wrapper. Same ~30-combinator
cost, and it duplicates work `PErr.rest` already does for the one thing that needs it (error
position) — a current-span state machine serving a `Surf` span Q1 declines to store would be
work with no consumer. If Q1's ADR fork fires, this is its natural companion change — land
together, not alone first.

**Rejected alternative — `spanOfRest`-style suffix-index arithmetic for hover too.**
`spanOfRest` works because a parse failure's `rest` is exactly the unconsumed suffix — one
canonical boundary per failure. A hover query has no such boundary: the cursor can land
anywhere inside a decl's body, and nothing in the token stream marks sub-expression
boundaries post-parse (only decl boundaries do, via each decl's name). Decl-name-token
comparison is the correctly-shaped tool for this granularity; suffix arithmetic doesn't
generalize to it.

### Q3 — Error-value shape

**Recommendation: keep `Except String` (or `Except (String × Option Span)` where already
present) everywhere. Do not introduce a structured `{code, span, message}` error type.**
Layer BOTH the diagnostic code (`DiagCodes.codeForMsg`) and the span (`locateInMsg`) as
independent, composable POST-HOC views over the plain string, exactly as `Diagnostics.lean`
already does (`Diagnostic.toJson` calls `codeForMsg d.msg` fresh at render time — the code is
never stored, only derived). This is the strongest-precedent answer of the four: the
codebase has ALREADY chosen this shape twice (span-view, code-view) and both compose without
touching the ~25+ `Except String`-returning functions across `TypeCheck.lean`
(`synthV`/`checkV`/`synthC`/`checkC`/`elabS`/`checkSC`/`elabBind`/… — grepped, real count).

**Rejected alternative — a structured error type (`{code, span, msg}`) threaded through the
checker from the start.** The textbook "rustc-style diagnostic" shape, more principled in
isolation. Rejected here specifically because it forces the ONE migration this codebase has
twice avoided by choosing views-over-strings — every `throw s!"…"` site in `TypeCheck.lean`
would need to construct a code up front (`DiagCodes.lean`'s own header says codes are
RETROFITTED, deliberately decoupled from the throw site) or leave it `none` and have the
caller fill it in anyway — the SAME post-hoc pattern, with a needless extra field threaded
everywhere. Q3 doesn't need a fork flag — the existing precedent is unambiguous.

### Q4 — Migration order + slice map

Given Q1–Q3's recommendation (no `Surf`/`P` change, everything post-hoc), the "migration"
is small and additive. Slice map, each gated by the FULL `#guard` corpus (`lake build`,
unpiped exit code):

| Slice | What | Gate | Landed? |
|---|---|---|---|
| 0 | `Span`, `tokenizeSpanned`, `locateToken`, `unboundLocated` | `lake build` (Surface.lean's own `#guard`s) | YES (`ff49adb`) |
| 1 | `spanOfRest`, `parseLocated`/`parseProgLocated` — Stage A (parse errors located) | `lake build` | YES (`77dec515`) |
| 2 | `nameHint`, `locateInMsg`, `checkAndLower : Except (String × Option Span) Comp` — Stage B (bare-variable type errors located) | `lake build` | YES (`ef391650`, `95710a40`) |
| 3 | `Diagnostics.lean` schema wiring (`bang check --json`'s `span`/`explainCode` fields) | `lake build` + the byte-exact schema `#guard`s | YES (already in this checkout) |
| **4** | **decl-granularity hover** (`HoverFact`, `hoverFactsOf`, `hoverAt` — this note's spike, `Bang/Frontend/HoverSpike.lean`) | `lake build Bang.Frontend.HoverSpike` (targeted) + full `lake build` (no regression) | **spiked, not wired to CLI** |
| 5 | Wire slice 4 into `bang query hover <file> <line> <col>` (`Main.lean` dispatch + `Query.lean` JSON rendering, mirroring `symbols`/`type`) | targeted build + a `tools/test-query.sh`-style CLI smoke test | not started — **the implementation session's slice 1** |
| 6 (optional, only if a real need surfaces) | Full `Spanned Surf` + `P`-state-threading, for exact sub-expression hover/location | full corpus + new regression `#guard`s per touched arm | not started; gated on Q1's ADR fork actually firing |

Slice 5 is what the fresh-context implementation session should start with: it is CLI/JSON
plumbing over an already-proven Lean function (slice 4), the same shape `symbols`/`type`
already have. Slice 6 stays a possibility, not a commitment — only pursued if hover actually
needs sub-decl precision in practice (an ADR fork per Q1).

## 3. The #104 co-sequencing verdict

**Recommendation: do NOT sequence #104 (comment-preserving fmt) with this note's slice 4/5.**
#104's filing text assumes #52's "per-node source metadata" migration is still the big
`Spanned Surf` ripple (Q1's rejected alternative) and proposes riding it to attach trivia.
Given Q1's finding — that ripple is NOT needed for #52's remaining scope — #104 has no
shared migration left to ride. #104's real need (attach a leading/trailing COMMENT to a
token, re-emit it from `showProg`) is closer to a LEXER-level trivia-attachment problem than
a `Surf`-node-span one: comments are dropped at `tokenize` time, before any `Surf` node
exists to attach to. Fixing that means teaching the TOKENIZER to retain trivia (a comment
token type, filtered from the parser's stream but kept in a side list `showProg` can
consult) — narrower than either #52's original framing or this spike. **File #104 as
independently scoped**; a one-line comment there pointing at this note replaces the
"shared migration" framing, rather than blocking either on the other.

## 4. Genuine operator forks (flag for an ADR if implementation revisits them)

- **Q1's rejected alternative** (full `Spanned Surf`) — reversible now, expensive later. Only
  worth an ADR if a concrete consumer needs exact sub-decl spans (see §2 Q1's "if" clause).
- **Decl-granularity ceiling for hover** (this note's slice 4 choice) — a cursor inside a
  large multi-clause `fn`/`handle …with` body resolves to the WHOLE decl's type, not the
  clause/sub-expression under the cursor. Acceptable for v1's "type at position" ask (the
  issue's own phrasing), but worth flagging explicitly: if hover needs to answer "what's the
  type of THIS handler clause parameter" rather than "what decl am I in", that's the Q1 fork
  firing for real.

Everything else (Q2, Q3, the slice map, the #104 verdict) follows mechanically from the
codebase's existing precedent (Stage A/B, `DiagCodes.lean`) — not a coin-flip.

## 5. The spike — evidence

`Bang/Frontend/HoverSpike.lean` (additive, new module, `Bang.+` glob picks it up
automatically — no lakefile change). Threads the recommended shape end-to-end through ONE
vertical:

- **Combinator chain**: `tokenizeSpanned`/`locateToken` (Slice 0/1, unchanged, reused as-is).
- **Surf node kind carrying the span**: NONE — by design (Q1). Instead, `HoverFact` pairs a
  decl's NAME (`Decl.name`, already exists) with its name-token's `Span` (via `locateToken`)
  and its rendered type (`declFactOf`, already exists, #80's `bang query` substrate).
- **Checker error site emitting a span**: reuses `declFactOf`'s existing `typeError` field
  (itself already a location-free `String` — this spike doesn't add new checking, only a
  render).
- **The composition**: `hoverAt src line col` — filters every decl whose name-token starts
  at-or-before the cursor, takes the LAST (nearest enclosing, source order), renders it.

Proves: `tokenizeSpanned`'s span substrate and `Query.lean`'s per-decl type substrate (#80)
compose into a working hover WITHOUT touching `Surf`'s ~40 constructors, the ~30 `P`
combinators, or a single existing `#guard`.

**Evidence:** file `Bang/Frontend/HoverSpike.lean`. 9 `#guard`s: cursor inside a decl body,
cursor on a decl's own name token, cursor before any decl (honest `none`), two-decl
nearest-enclosing resolution, a type-error decl rendering its checker message, a non-value
(`data`) decl rendering bare. Targeted build `lake build Bang.Frontend.HoverSpike` — **exit
0** (all 9 guards pass). Full corpus `lake build` (unpiped) — **exit 0, 757 jobs**, no
regression.

## 6. Slice to hand the implementation session

**Slice 5** (§2's table): wire `hoverAt`/`hoverFactsOf` into `bang query hover <file> <line>
<col> [--json]`, mirroring the existing `symbols`/`type` verb plumbing in `Query.lean` +
`Main.lean`'s dispatch. The Lean-side logic (slice 4) is proven by this note's spike;
slice 5 is CLI/JSON rendering over it — the SAME `jsonObj`/`jsonStrField` machinery
`Query.lean` already has, no new pattern. Estimate: small, single-session, no `Surf`/`P`
touch, corpus-safe by construction (additive verb, existing verbs untouched).
