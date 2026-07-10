<!-- note-status: active -->

# Stage-7 `handle … with` elaboration mechanics probe (#21 s7probe)

**Status**: probe complete, findings banked. Syntax is explicitly PROVISIONAL (s7design's ADR-0095
owns the real spelling) — everything below characterizes the MECHANICS every syntax choice shares,
not the strawman's own grammar. **Post-probe rulings (2026-07-10): WALL 1 ruled — resolved-label
slot on `handleCustomS`, lowering stays `ElabEnv`-free; and the D1 binding gap ruled — REQUIRED
explicit `as h` binder, `handle e with Name as h { clauses }`. Both recorded in ADR-0095 §D1a;
the probe branch realigns to the ruled grammar.**

## What was built

A Flix-shaped strawman `handle N p with { op1(x) -> body1, op2(y) -> body2, … } as h in body`,
end to end through the frontend:

- `Bang/Frontend/Surface.lean`: a new `Surf.handleCustomS` node + `HClauses` mutual list (the
  `DArms` precedent), a bespoke `pExpr` parser arm (`pHClause`/`pHClauses`), and a documented
  `.error` in `lowerC` (see WALL 1 below).
- `Bang/Frontend/TypeCheck.lean`: `synthSC`'s `.handleCustomS` typing arm (discharges the label,
  binds the cap, checks clause coverage + ret-shape), a `checkHClauses` mutual sibling, `elabS`'s
  `.handleCustomS` arm (extends Γ with the cap binding, mirrors `.withCapS`), an `elabHClauses`
  sibling, and the ~9 exhaustive-match completions every other `Surf`-matching helper needed
  (`structOK`, `expandBFns`, `surfUsesVar`, `qualifyVars`, `qualifyDotAccess`,
  `firstPrivateDotAccess`, `firstBareOpCall`).
- `Bang/Frontend/Format.lean`: a placeholder print arm (exhaustiveness only — the printer is out of
  this probe's scope).

Full build green (749/749 jobs), kernel census untouched (26 constructors), no kernel/Backend/Meta
files touched.

## WALL 1 (structural, blocks a real implementation): `Surf` has no label-carrying slot

`lowerC : List String → Surf → Except String Comp` has **no `ElabEnv` parameter** — confirmed this
is true even on the fully-typed `checkAndLower` pipeline: it calls `elabProg` (which threads
`env.effects` through elaboration) and then calls `Bang.Surface.lower e` on the elaborated tree
**alone**, discarding `effects`. `lower`/`lowerC` never see the effect-name→label table, typed path
or not.

The three built-in handler kinds (`state`/`throws`/`atomically`) get away with this because
`capKindLabel : String → Option Label` is a **pure, program-independent** function — three hardcoded
constants, re-derivable identically at both elaboration time and lowering time with zero shared
state. A user effect's label has no such constant: `buildEnv`'s `.effectD` case allocates it as
`4 + effects.length`, **decl-order-dependent**, known only post-elaboration.

**Consequence**: a real implementation needs `elabS` (the ONE place with both the `Surf` tree and
`env.effects` in scope simultaneously) to **rewrite** the resolved label into the tree before `lower`
ever runs. `Surf` currently has no slot to rewrite into — no constructor carries a resolved
`Label : Nat` (`Ty.tEff` carries effect *names*, resolved only at the checker). This is an AST
change (`s7design`/implementation-lane territory), not something this probe invents unilaterally.
The strawman's `lowerC` arm fails loud naming this exact gap rather than crashing or guessing.

## WALL 2 (mechanics, SOLVED — read as a design lesson): a clause list can't type via `for`/`let rec`

The clause-list typing loop (checking each `op(x) -> body` clause's body against its declared
`resTy`) needs to call back into `synthSV`/`unifyV` — siblings of `synthSC` in its own 4-way
`mutual` block (`synthSV`/`checkSV`/`synthSC`/`checkSC`, ranked `(sizeOf e, 0..3)` to break the
`check t → synth t` subsumption tie).

Two natural-looking approaches both fail:

1. **A `for` loop over `hClausesToList cls`** (converted to a plain `List`): the `sizeOf`-based
   termination measure can't see through the opaque list-conversion call, so the `synthSV b` call
   inside the loop fails `synthSC`'s own `termination_by (sizeOf e, 1)` proof — Lean reports "failed
   to prove termination" pointing at the exact call.
2. **A local `let rec checkClauses`** inside the `handleCustomS` match arm: this silently JOINS
   `synthSC`'s own mutual-recursion group (since it calls `synthSV`), and Lean cannot find a joint
   decreasing measure across the join — it breaks the WHOLE file's termination proof, and every
   downstream `#guard` reports `uses 'sorry' and/or contains errors` (a scary-looking cascade that is
   really just this one root cause).

**The fix that works**: mirror the `elabS`/`elabArms` precedent already in the file (`elabArms`
recurses `DArms` for named-match arm bodies, genuinely mutual with `elabS`). `HClauses` becomes a
**third mutual partner** — `checkHClauses`, structurally recursing on `HClauses` itself with its own
`termination_by cls => (sizeOf cls, 4)` — called from `synthSC`'s arm as an ordinary sibling call.
This generalizes: **any repeated-group `Surf` payload needing typing-algorithm recursion back into
`synthSC`'s own mutual group needs a genuine mutual sibling, never a `for`/`let rec`.** Filed as a
structural note for whoever implements Stage 7 for real, and for any future construct with the same
shape (a clause list, an arm list, a binding list) that needs TYPING (not just elaboration/lowering)
recursion.

## WALL 3 (bug found LIVE by the e2e probe, FIXED): `elabBind`'s throwaway inference drops `effects`

`elabS`'s `.lett` arm calls `elabBind Γ e'` to decide whether the RHS generalizes — a documented
"throwaway inference" that runs `synthSC Γ e'` under a **freshly-seeded `USt`** (`.run' {}`).
Freshly-seeded meant `effects := []` by default. This was invisible before this probe: **no
built-in `.dotPerform` op ever consults `USt.effects`** (built-ins resolve via the pure,
state-free `capOpSig`), so nothing had ever exercised this gap.

The instant a user-effect `perform` (`h.fetch(5)`) appears as a `let`-RHS
(`let r = h.fetch(5) in body`), `elabBind`'s throwaway run hits the SAME `.dotPerform` D2 arm the
outer type-check does — but with an EMPTY effects table — and produces a **wrong diagnostic**
(`receiver's capability label is not a declared effect`, a false negative masking a program that
types fine everywhere else). Confirmed live via `bang check` on
`handle Reader 100 with { fetch(x) -> x } as h in let r = h.fetch(5) in r` (fails before the fix,
reaches lowering after).

**Fix landed** (`Bang/Frontend/TypeCheck.lean`): `elabBind` now takes an `effects` parameter
(default `[]`, preserving every existing non-effect call site byte-identical) and seeds its
throwaway `USt` with it; the one call site (`elabS`'s `.lett` arm) passes `env.effects`. This is a
genuine, narrow, load-bearing fix — not scope creep — since it blocks ANY future construct that
types against `env.effects` from ever appearing as a `let`-RHS.

## WALL 4 (bug found, NOT resolved — reported, not fixed): a clause body naming its own `arg` binder
## in an arithmetic expression fails ONLY on the typed path, differently from the untyped path

`handle Reader 100 with { fetch(x) -> x + 0 } as h in h.fetch(5)`:

- `elaborateToComp` (the `--no-typecheck` / untyped path: `elabProg` → `lower`, no `synthSC` at
  all) reaches the DOCUMENTED WALL-1 diagnostic cleanly — the mechanics work as far as they can
  without the label-rewrite.
- `checkAndLower` (the typed, PRODUCTION path: `elabProg` → `synthSC` → `lower`, discarding the
  type but keeping the SAME elaborated `e`) fails with `lowerV`'s generic catch-all `"expected a
  value (wrap a computation in braces)"` — a DIFFERENT error, from a DIFFERENT construct than the
  one under test, on the SAME `e`.

Isolated (not the label-rewrite wall — confirmed by testing `fetch(x) -> x` and `fetch(x) -> 5`,
both of which reach WALL 1 cleanly on EITHER path): the failure is specific to a clause body that is
a `.binopS` referencing the clause's own arg binder (`x + 0`). Ruled out: parse-tree shape (dumped
identical `Surf` AST both ways), `parseProg` vs `parseProgLocated` (dumped, structurally `==`),
`checkAndLower`/`elaborateToComp` calling `elabProg` differently (they don't — same call), stale
`.olean` caching (force-rebuilt, reproduces). **Not resolved within this probe's budget** — `lower e`
giving a different result depending on whether `synthSC` ran first on the SAME `e` should be
impossible for the pure, `Except`/`StateT`-based pipeline as understood; something in that
understanding is incomplete. Flagged for the implementation lane to re-derive from scratch with
fresh eyes (or a `sorry`-free `lean_run_code` REPL session, which this probe's CLI-only workflow
didn't have time to set up) — NOT blocking the mechanics verdict below, since it's a corpus/testing
gap on ONE narrow clause shape, not a wall on the overall pipeline shape.

## Does the mechanics constrain the syntax choices? (the point of this probe)

Findings that s7design's ADR should know:

1. **A clause list is a repeated group** — like `let`-multi/`match`/`do`, it structurally cannot fit
   `keywordRule`'s linear `Choice` grammar (confirmed: needed a bespoke `pExpr` arm + a
   `pArms`-precedent clause-list parser, exactly the class ADR-0071 ②'s own boundary note predicts).
   Any syntax choice for `handle … with { … }` needs a bespoke parser arm, full stop — not a
   constraint on the SPELLING, but confirms the mechanism.
2. **The label-rewrite step (WALL 1) is syntax-independent** but genuinely load-bearing: WHATEVER
   surface spelling lands, elaboration must gain a way to write a resolved `Label` into the AST
   before lowering. This likely means `Surf.handleCustomS` (or whatever it's finally named) carries
   an extra field — a `Label`/`Nat` slot, `none` until `elabS` fills it — OR lowering itself grows an
   `ElabEnv` parameter (a bigger, more invasive change touching every `lowerC`/`lowerV` call site).
   **This is a real design fork s7design's ADR should name explicitly**, since it is NOT free (either
   choice ripples).
3. **Clause typing needs a mutual-sibling shape (WALL 2)** — purely an IMPLEMENTATION concern, not
   surface-visible, but worth flagging to whoever lands Stage 7 for real: budget for it, it is not a
   one-line `for` loop.
4. **The carried param has no surface binder name in this strawman** — `handleCustomS`'s clause
   grammar (`op(x) -> body`) only captures the OP's argument binder, never a name for the carried
   param (`ADR-0092`'s `P@1`). The mechanics bound it under an internal `"#param"` sentinel
   (typeable, but UNWRITABLE from source) to get the e2e probe moving. **s7design's syntax needs an
   explicit answer**: either a second named binder in the clause head (`op(x, p) -> body`, doubling
   every clause's arity) or an implicit/ambient name (`self`/`param`) resolved specially. This is a
   genuine syntax decision the mechanics surfaced, not a mechanics-only concern — flagged as the
   single most concrete open question for the ADR.
5. **Reserved-keyword collision at the OP level, not just the effect-decl level**: `effect Net
   { read : … }` is already rejected at `buildEnv` (built-in names reserved v1-wide, ADR-0092
   D1/D2's own note), but a clause using a reserved word as its OP NAME (`{ read(x) -> … }`) fails
   at PARSE time (`pIdent` rejects the keyword token) — before elaboration ever gets a chance to
   produce the (arguably more informative) "reserved" diagnostic. Confirmed live
   (`error at 2:26: expected an identifier, got keyword 'read'`). Not a blocker (the effect decl
   itself already can't declare `read`, so a clause naming it is dead code either way) but worth a
   one-line ADR footnote so a future contributor doesn't mistake the parse error for a bug.

## Files touched (frontend-only, per brief)

- `Bang/Frontend/Surface.lean` — `Surf.handleCustomS`, `HClauses`, `pHClause`/`pHClauses`, the
  `handle N p with {…}` parser arm, `hClausesToList`, `eraseLettMultiHClauses`, the documented
  `lowerC` wall.
- `Bang/Frontend/TypeCheck.lean` — `synthSC`'s typing arm, `checkHClauses`, `elabS`'s arm,
  `elabHClauses`, the ~9 exhaustive-match completions, the `elabBind` effects-threading fix.
- `Bang/Frontend/Format.lean` — placeholder print arm (exhaustiveness only).

No `Bang/Core`, `Bang/Backend`, or `Bang/Meta` file touched. Kernel census unchanged at 26.
