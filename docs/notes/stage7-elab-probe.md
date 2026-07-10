<!-- note-status: active -->

# Stage-7 `handle … with` elaboration mechanics probe (#21 s7probe)

**Status**: DONE — implemented against the RULED ADR-0095 grammar (accepted 2026-07-10,
`docs/decisions/0095-stage7-handler-surface.md`), e2e-verified. The original probe was built
against a provisional strawman; once ADR-0095 landed (all five decisions as recommended), the
manager upgraded this unit to a real implementation and ruled two open gaps (below). All three
`bang eval` reference programs — the ADR's own D1 tracer bullet plus the Stage-2 kernel's
`customResume`/`customAbortCoexist` #guards ported to source text — now produce the exact
expected values.

## What was built

`handle e with Name as h { op(x) => body, … }` (param-less) / `handle e with (Name init) as h
{ … }` (param-carrying), end to end through the frontend:

- `Bang/Frontend/Surface.lean`: `Surf.handleCustomS` (6 fields: a resolved-label slot, the
  effect-name reference, the param-init as `SurfArgs`, the mandatory cap binder, the clause
  list, the handled body) + `HClauses` mutual list (the `DArms` precedent), a bespoke `pExpr`
  parser arm (`pHandlerName`/`pHClause`/`pHClauses`), `with` newly RESERVED (§Finding 3), and a
  REAL `lowerC` arm building `Handler.custom` + `Comp.handle` (WALL 1 fixed — see below).
- `Bang/Frontend/TypeCheck.lean`: `synthSC`'s `.handleCustomS` typing arm (discharges the label,
  binds the cap, checks clause coverage + the D4 ret-shape/effect-free property), a
  `checkHClauses` mutual sibling, `elabS`'s `.handleCustomS` arm (RESOLVES the label against
  `env.effects` and REWRITES it into the tree's slot — the WALL-1 fix's real half), an
  `elabHClauses` sibling, and the exhaustive-match completions every other `Surf`-matching
  helper needed.
- `Bang/Frontend/Format.lean`: a printer arm matching the ruled grammar (clause-list rendering
  stays a placeholder — round-trip fidelity for `HClauses` is a follow-up, not blocking).

Full build green (749/749 jobs), kernel census untouched (26 constructors), no kernel/Backend/Meta
files touched.

## The two rulings that resolved this unit's open gaps

1. **D1 binding-order gap** (flagged by this probe against the ADR's own tracer-bullet text,
   which used an unbound `net` before any binder introduced it): **operator-ruled, reading (b)
   — `as h` is MANDATORY in v1**, no implicit lowercase-of-Name default (rejected: silently
   shadows a nested same-effect handler). Scope: `h` binds in the handled body `e`
   (elaborate the clause-map + install the binder first, then `e` under the extended Γ — reading
   (c)'s mechanics, reading (b)'s surface). The ADR is being amended with a D1a addendum
   recording this.
2. **WALL 1** (the resolved-label slot): **manager-ruled Option A** — add the slot directly to
   `handleCustomS`; `elabS` resolves + rewrites it; `lowerC` stays a pure function of the tree
   (no `ElabEnv` threading — rejected as polluting a structural pass with elaboration state, and
   the untyped `elaborateToComp` path lacks a full `ElabEnv` anyway).

## WALL 1 — RESOLVED (Option A, implemented)

`lowerC` gained no `ElabEnv` — instead `Surf.handleCustomS`'s first field is `Option Label`,
`none` at parse time, rewritten to `some ℓ` by `elabS`'s new arm (the ONE place with both the
tree and `env.effects` in scope). `lowerC` reads the slot directly and fails loud on `none`
(elaboration never ran, or the effect name never resolved). `Option Surf` was tried for the
param-init field first and REJECTED for an unrelated but load-bearing reason: Lean's
`deriving DecidableEq` cannot see through `Option <mutual-self-type>` across a mutual inductive
group (confirmed via isolated repro) — `SurfArgs` (already in the file, the `.dotPerform`
precedent) was reused instead, generalizing the SAME reason `SurfArgs`/`DArms`/`LetBindings`
are bespoke mutual types rather than `List`/`Option` of `Surf` in the first place.

## WALL 2 — mechanics lesson (unchanged from the strawman probe, still load-bearing)

Clause-list typing needs a mutual-sibling shape, not a `for`/`let rec`:

1. **A `for` loop over a converted `List`**: `sizeOf`-based termination can't see through the
   opaque conversion, so the inner `synthSV`/`synthSC` call fails `synthSC`'s own
   `termination_by` proof.
2. **A local `let rec`**: silently joins `synthSC`'s 4-way mutual group; Lean can't find a joint
   measure, breaking the WHOLE file's termination and cascading `sorry`-taint through every
   downstream `#guard`.

**The fix**: `checkHClauses` is a genuine THIRD mutual partner (the `elabS`/`elabArms`
precedent), structurally recursing on `HClauses` with its own `termination_by cls => (sizeOf
cls, 4)`. Generalizes to any future repeated-group `Surf` payload needing typing recursion.

## WALL 3 — RESOLVED, and found to be SYSTEMIC (two occurrences, not one)

`elabS`'s "throwaway inference" helpers seed a FRESH, effects-less `USt` (`.run' {}`) — invisible
until a user-effect construct exercised them, since no built-in `.dotPerform` op ever consults
`USt.effects`. Two independent occurrences, both fixed:

1. **`elabBind`** (the `.lett` arm's let-generalization decision): fixed first, threading
   `effects` (default `[]`) from `env.effects`.
2. **`zonkInferC`/`anfSplit`** (the A-normalization helper EVERY `elabS` arm with a
   computation-position operand calls — 19 call sites): found LIVE by the e2e probe's OWN tracer
   bullet (`net.fetch(1) + 1` — the `.binopS` arm's A-normalization of the left operand hits
   `anfSplit`, whose `zonkInferC` throwaway run rejected the already-well-typed `.dotPerform`
   with a wrong "not a declared effect" diagnostic). Fixed the SAME way: `zonkInferC` and
   `anfSplit` both gained an `effects` parameter (default `[]`), threaded from `env.effects` at
   all 19 call sites.

**Generalizes**: any "run `synthSC`/`synthSV` in a throwaway sub-inference" helper in this file
needs `effects` threaded, or it silently breaks the FIRST time a user-effect construct appears
under it. Worth an audit pass for any THIRD occurrence not yet exercised.

## WALL 4 — RESOLVED (was NOT a pipeline divergence — a genuine bug in the clause-typing arm)

The originally-reported "typed vs untyped path disagree on an identical tree" turned out to be a
RED HERRING from testing artifacts, not a real divergence. The actual bug: `checkHClauses`
checked each clause body via `synthSV` (VALUE synthesis) — but a clause body like `n * 10` is a
COMPUTATION (`.binopS` reduces via the kernel's `Comp.binop`, needing `Comp`/`synthSC` typing,
not `Val`/`synthSV`). `synthSV` has no `.binopS` arm, so ANY non-atomic clause body
unconditionally hit its catch-all `"not a value"` error — under BOTH typed and untyped framings
of my test harness, which is what made it look like a path divergence; the untyped path simply
never reached this check at all (no `synthSC`/`synthSV` runs there), so "worked" for the wrong
reason. **Fixed**: `checkHClauses` now uses `synthSC` (computation typing) + an EXPLICIT
ret-shape/effect-free check (`decide (φ.labels = ∅) && φ.tail.isNone` after `resolveRow` —
`Finset.isEmpty` is noncomputable on this path, the corpus-established `decide`-based workaround)
— ADR-0092 D4's "ret w is EFFECT-FREE" property is now checked DIRECTLY, and the ADR-0095 D4
teaching diagnostic fires exactly when a clause body performs before resuming (falsified live:
`fetch(n) => raise n` produces the exact D4 message naming ADR-0065 + Q27).

## The e2e verdict: three `bang eval` programs, all exact

1. **ADR-0095 D1's own tracer bullet** (renamed `read`→`fetch`, `net`.-perform syntax fixed to
   the parenthesized `net.fetch(1)` call form — see Finding 2 below):
   ```
   effect Net { fetch : Int -> Int }
   handle
     (net.fetch(1)) + (net.fetch(2))
   with Net as net {
     fetch(n) => n * 10
   }
   ```
   → `bang eval` = **30**, exactly as the ADR promises.
2. **Stage-2 kernel's `customResume`** ported to source:
   ```
   effect Reader { fetch : Int -> Int }
   handle
     (let r = net.fetch(5) in r + 1)
   with (Reader 100) as net {
     fetch(x) => x + 100
   }
   ```
   → `bang eval` = **106**, matching `Bang/Core/Semantics/Eval.lean`'s `customResume` #guard.
3. **Stage-2 kernel's `customAbortCoexist`** ported to source (nested `handle`, `raise`
   aborting past the custom frame):
   ```
   effect Reader { fetch : Int -> Int }
   handle
     (handle
       (let r = raise 42 in net.fetch(5))
     with (Reader 100) as net {
       fetch(x) => x + 100
     })
   ```
   → `bang eval` = **42**, matching `customAbortCoexist`'s #guard.

## Findings for the ADR / a future contributor (beyond the two already-ruled gaps)

1. **A clause list is a repeated group** — confirms ADR-0071 ②'s own documented `keywordRule`
   boundary generalizes here too; not a constraint on the spelling, but on the mechanism (any
   `handle … with { … }` syntax needs a bespoke parser arm, never a linear `Choice` rule).
2. **The ADR's own D1 example has a call-syntax slip**: `$net.read 1` does not parse/type the
   way the prose implies. `$` forces its ATOM argument (`pAtom`, not the dot-chain), so
   `$net.fetch(1)` parses as `(force net).fetch(1)` — `.dotPerform`'s receiver becomes a
   `.force`-computation, which `synthSV` (value-only) rejects outright ("not a value"). The cap
   binder `net`/`h` is ALREADY a value (`Cap ℓ`, bound directly by `handleCustomS`'s Γ
   extension) — it never needs forcing; the correct call is a bare `net.fetch(1)` (no `$`,
   matching ADR-0070's existing `h.op(args)` convention exactly). Separately, space-separated
   call syntax (`net.fetch 1`, no parens) parses as `(net.fetch) 1` — a NULLARY perform applied
   to `1` as a function call, not a 1-arg perform — the parenthesized form `net.fetch(1)` is
   REQUIRED; D3's "curried" framing describes the OP SIGNATURE convention (a single-arg arrow),
   not the CALL-SITE syntax, which stays `.op(args)` per ADR-0070. Worth a corrected example in
   the ADR amendment.
3. **`with` needed to become a reserved word.** Without reserving it, `e with Name { … }` parsed
   as ONE giant application chain (`pApp`'s juxtaposition fold happily consumed `with`/`Name`/the
   `{…}` thunk as successive atoms/arguments of `e`), since nothing marked `with` as a
   non-identifier boundary token. Fixed in both `pIdent` and `pAtom`'s reserved-word lists — the
   same class of fix #26 made for `read`/`write`/`get`, generalized to a new keyword.
4. **The carried param's binder name (`param`) is INTERNAL, not surface-writable** in the
   current implementation — a clause body cannot reference the carried param by any name (bound
   under an internal `"#param"` sentinel). The ADR's own worked example
   (`tick(u) => ret (param + 1)`) implies `param` should be a real, referenceable identifier.
   **This is a real gap**, not yet closed — a follow-up should either surface `param` as an
   actual bound name in `checkHClauses`'s/`elabHClauses`'s Γ (straightforward: add `("param", P)`
   under its real name alongside the `"#param"` sentinel, or replace the sentinel outright) or
   the ADR should clarify `param` is reserved-word sugar for the carried value. Flagged for the
   next slice, not blocking (the e2e programs above don't exercise param-referencing bodies).
5. **Reserved-keyword collision at the op level**: an `effect` op sharing a name with a built-in
   (`read`, `get`, …) fails at PARSE time (`pIdent` rejects the keyword) rather than the more
   informative "reserved" diagnostic `buildEnv` already gives for the DECL itself. Not a blocker
   (the decl already can't declare `read`, so a clause naming it is dead code either way) — a
   one-line ADR footnote would save a future contributor's confusion.

## Files touched (frontend-only)

- `Bang/Frontend/Surface.lean` — `Surf.handleCustomS` (final 6-field shape), `HClauses`,
  `pHandlerName`/`pHClause`/`pHClauses`, the `handle e with …` parser arm, `with` reservation,
  `hClausesToList`, `eraseLettMultiHClauses`, the real `lowerC`/`lowerHClauses` arms.
- `Bang/Frontend/TypeCheck.lean` — `synthSC`'s typing arm, `checkHClauses` (D4 ret-shape check),
  `elabS`'s arm (the label resolve+rewrite), `elabHClauses`, the exhaustive-match completions,
  the `elabBind` AND `zonkInferC`/`anfSplit` effects-threading fixes (WALL 3, both occurrences).
- `Bang/Frontend/Format.lean` — the printer arm (clause-list rendering stays placeholder).

No `Bang/Core`, `Bang/Backend`, or `Bang/Meta` file touched. Kernel census unchanged at 26.
