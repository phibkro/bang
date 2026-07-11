# ADR-0097 · The prelude is a real `Prelude.bang` module, auto-`use`d

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: Issue #106 (operator-ruled 2026-07-11, unblocked same day when #97 item-3 turned out
  already fixed at `225f3f42`): the injected stdlib/generic-prelude functions — 21 entries across
  `stdlibFnSrcs` (`concat`/`reverse`/`eq`) and `genericPreludeFnSrcs` (`mapOption`/`mapResult`/
  `bimap`/the four `*To*` isos/`withDefault`/`fst`/`snd`/`abs`/`min`/`max`/`const`/the char kit) —
  move from source-STRING injection to a real `Prelude.bang` module at the repo root: ordinary bang
  source, checked/fmt'd/tested like any module, embedded into the binary at COMPILE time
  (`include_str`, ADR-0016's "the source file is the single source of truth" move applied to the
  stdlib itself) and auto-`use`d into every program that mentions one of its `pub` names — no
  `import`/`use` line needed. **Decision: (1) embed, not a runtime search path** — `include_str`
  bakes `Prelude.bang`'s bytes into the `.olean`/executable at compile time, so `bang` stays one
  self-contained binary with no install-location dependency; the SOURCE FILE stays the only single
  source of truth (the compiled bytes ARE its bytes, re-derived every build — no second copy to
  drift). **(2) auto-`use`, FILTERED to mentioned names, not unconditional** — `injectPrelude`
  reuses `mergeModules` (ADR-0093) with the prelude as a synthetic resolved module, but ONLY merges
  in the `pub` decls a program's `Surf` tree actually mentions (`progUsesVar`, a restored/adapted
  `surfUsesVar` walk) — an unconditional 21-decl merge would tax EVERY program ~21 evaluation-fuel
  steps for entries it never uses (`Config.run`'s CK machine spends one fuel unit per `letC` step
  regardless of whether the binder is forced), breaking the tight-fuel corpus outright; this was
  caught build-first, not designed up front. **(3) shadowing/suppression is now PER-NAME, for
  free** — `mergeModules`'s existing decl-ordering (`aliasDecls ++ entryDecls`, later binder wins)
  makes a user's own `abs`/`Option`/etc. shadow the prelude one with ZERO special-case code, one
  name at a time — strictly finer than the retired `injectStdlib`'s two coarse all-or-nothing
  buckets (`declared.contains "Str"/"Char"` / `"Option"/"Result"`). **(4) `strPrelude`/
  `genericPrelude` (the `Char`/`Str`/`Option`/`Result` `data` types) stay OUT of scope** — they are
  foundational to literal parsing (`"hi"`/`'a'` desugar straight to their ctor names) and
  annotation-free generic introduction (ADR-0081), so they remain injected `Decl` values ahead of
  `Prelude.bang`'s own elaboration, which references their ctors. **(5) `gen-reference.py` reads
  `Prelude.bang` directly** (regex over the committed module source, the SAME convention the retired
  string-extraction used) as the new SSoT for the Standard-library/Generic-prelude reference tables
  — not `bang query symbols` (would force building the binary before the docs generator can run, a
  worse bootstrap order for a Python-only tool that today needs no Lean build at all).
- **Depends-on**: 0093 (the module system this rides — file=module, `pub`/`use`, `mergeModules`),
  0074 (the string stdlib this retires), 0079/0081 (generic data + annotation-free introduction,
  why `Option`/`Result` stay out of scope), 0046 (deterministic-or-loud — no new error path)
- **Relates-to**: #106 (this ADR), #105 (the first-slice prelude these entries came from), #97 item
  3 (the `use`-hoist-`pub let rec` fix that unblocked this), `docs/notes/stdlib-prelude-survey.md`
  §3 (the injection-mechanism fork this resolves)

## Status

Proposed — implementation landed on branch `feat-prelude-module`; gated by `just verify` on a
committed sha (this ADR's own PR/merge names it). Not yet Accepted pending the operator's read of
the fuel-cost finding in decision point (2), which was NOT anticipated by the survey that scoped
this work and changes the shape of "auto-use" from "always-on" to "on-mention" — a live design
choice worth a second look before Accepted.

## Context

`docs/notes/stdlib-prelude-survey.md` §3 named the fork explicitly: today's prelude is 21 functions
as `let`/`let rec` SOURCE STRINGS, spliced into every program's scope at `elabProg` time
(`stdlibFnSrcs` unconditionally, `genericPreludeFnSrcs` conditionally on `surfUsesVar`). This works
but violates invariant #5 ("abstractions are ordinary library code, not kernel magic") in spirit —
the strings aren't type-checked in isolation, carry no module boundary, have no `pub`/private
distinction, and are re-parsed on every elaboration. The survey named the target (a real
`Prelude.bang` module, mechanism B) but flagged it blocked on #97 item 3 (`use` couldn't hoist a
self-recursive `pub let rec`, and most prelude entries recurse). The operator ruled B as the target
2026-07-11, then same-day corrected: #97 item 3 was ALREADY fixed (`225f3f42`, an implementation gap
in `qualifyDeclBody`'s `letRecD` arm, not designed intent) — so the migration had no remaining
blocker and was schedulable immediately.

## Decision detail

- **D1 — embed at compile time (`include_str`).** `Bang/Frontend/TypeCheck.lean` defines
  `preludeSrc : String := include_str "../../Prelude.bang"` — a path relative to the INCLUDING
  `.lean` file (Lean 4.30's own resolution rule, verified independent of build CWD: a test file
  inside `Bang/Frontend/` resolving `../../Prelude.bang` finds the repo-root file regardless of
  where `lake build` is invoked from). The alternative — a runtime search path the installed binary
  probes at startup — was rejected: v1 has no packaging story that fixes an install location the
  binary could search relative to, so a path-based prelude would need either a hardcoded absolute
  path (breaks on any install other than the dev tree) or an environment variable (a new
  configuration surface with a silent-default failure mode — exactly the "surprising default is a
  latent bug" smell). Embedding makes `Prelude.bang` the literal single source of truth: there is
  no second copy of its bytes anywhere, compiled or not — every build re-derives the embedded
  string from the committed file.
- **D2 — auto-`use`, filtered to mentioned names (`injectPrelude`).** `elabProg` calls
  `injectPrelude p` before `eraseLettMultiProg`/`foldLetDecls` (it needs `Prog`'s still-separate
  `imports`/`uses`/`decls`/`body` fields, which `mergeModules` operates over). `injectPrelude`
  computes `mentioned := preludePubNames.filter (progUsesVar · p)` — a syntactic
  over-approximation walk (mirrors the retired `wrapGenericFns`'s `surfUsesVar`, restored here since
  `Bang.Query`'s copy lives DOWNSTREAM of `TypeCheck.lean` and importing it back would cycle) over
  both the program's trailing body and every decl's own body (a name used only inside another
  top-level `let`'s definition, not the trailing expression, still counts). If `mentioned` is
  empty, `injectPrelude` is a no-op (zero fuel, zero decls — a program that mentions nothing pays
  nothing, matching a program with no `use` header at all). Otherwise it builds a TRIMMED
  `preludeProg` — containing only the mentioned decls — and merges it via the EXISTING
  `mergeModules [("Prelude", trimmedPrelude)] { p with uses := p.uses ++ [⟨"Prelude", mentioned⟩] }`.
  **Why trim the module's own decl list, not just the alias list**: `mergeModules` folds every
  decl of a resolved module into the merged program's `decls` UNCONDITIONALLY (`use`-selectivity
  only controls whether an unqualified ALIAS is added, not whether the qualified `Prelude_name`
  decl itself is merged in) and `foldLetDecls` wraps the body in one `let` PER decl in that list —
  so filtering only the alias list still pays the full 21-entry fuel cost. Trimming the SOURCE
  module is sound specifically for THIS prelude because no entry calls a sibling top-level entry
  (verified: `concat`/`eq` self-recurse, `reverse` nests a PRIVATE `revApp`, nothing references
  another `pub` name) — there is no cross-entry closure to compute.
- **D3 — the fuel-cost finding (build-first, not designed up front).** The FIRST implementation
  (unconditional auto-`use` of all 21 names, matching the survey's "as if the program began with
  `use Prelude (…all pubs…)`" framing literally) built clean but broke 14 pre-existing `#guard`s at
  tight fuel budgets (13 at fuel=20, one at fuel=60) — `Config.run`'s CK machine (`Bang/Core/
  Semantics/Eval.lean`) decrements fuel by exactly one per `Source.step`, and a `letC` push is one
  step regardless of whether the bound thunk is ever forced. An unconditional 21-`let` wrap costs
  ~21 fuel just to reach a program's real body. This is a genuinely NEW cost the retired
  `injectStdlib` never had for its conditional bucket (`genericPreludeFnSrcs`'s 18 entries), and
  WORSE than its unconditional bucket (`stdlibFnSrcs`'s 3 entries) by 6×. The fix (D2's filtering)
  restores the old conditional-injection fuel discipline exactly, verified by re-running the full
  corpus (`just check Bang/Frontend/TypeCheck.lean` clean) and hand-computing an independent
  module-form regression (21 entries, `use`-free, summing to the SAME `612` the corpus's own
  hand-picked constants predict).
- **D4 — shadowing/suppression, per-name, for free.** `mergeModules` already prepends `use`-hoisted
  aliases before the entry file's own decls (`mergedDecls ++ aliasDecls ++ entryDecls`); since
  `foldLetDecls` folds right-to-left (earlier = outer binder), a user's own top-level `let abs = …`
  is the INNERMOST binder and lexically shadows the auto-`use`d prelude `abs` — verified live (a
  user redefinition of `abs` yields `999`, the user's own sentinel, not the real absolute value).
  This required ZERO new code — it is the exact mechanism ADR-0093 D2 already built for ordinary
  `use`. It is also STRICTLY finer-grained than the retired `injectStdlib`'s two-bucket gate
  (`declared.contains "Str"/"Char"` skipped ALL of `stdlibFnSrcs`; `"Option"/"Result"` skipped ALL
  of `genericPreludeFnSrcs`): now each of the 21 names shadows independently. A name collision
  between the prelude and a module the user separately `use`s hits the SAME loud multi-`use` error
  `mergeModules` already gives (ADR-0046) — no new error path, and no `--no-prelude` flag was
  added (not needed: shadowing already gives a user full override per-name; a flag would be
  gold-plating an escape hatch nothing in the corpus or the survey asked for). A project that names
  its OWN module `Prelude.bang` (same directory as the entry file) is NOT silently shadowed by the
  built-in unless the user writes an explicit `use Prelude (…)`/`import Prelude` — verified live: a
  same-dir `Prelude.bang` defining its own `abs` sits inert with no `use` line (the built-in `abs`
  wins), but an explicit `use Prelude (abs)` resolves via the ordinary same-dir-then-root file
  search (ADR-0093 D1) BEFORE `injectPrelude` ever runs, so the user's own file wins — the same
  "later/innermost binder wins" rule as any other user-vs-prelude shadow, just triggered by an
  explicit reference instead of a bare name mention.
- **D5 — `Char`/`Str`/`Option`/`Result` stay OUT of scope.** These four `data` types (`strPrelude`/
  `genericPrelude`, `TypeCheck.lean`) are unaffected — they remain injected `Decl` values ahead of
  `Prelude.bang`'s own elaboration in `elabProg`, because (a) they are foundational to how literals
  PARSE (`"hi"` desugars directly to `SCons`/`Char` constructor applications inside the surface
  parser, not resolved by name lookup) and (b) `Prelude.bang`'s own `pub let`s reference their
  constructors (`mapOption` pattern-matches `None`/`Some`), so they must already be in `buildEnv`'s
  `ElabEnv` before `Prelude.bang` itself can type-check. Issue #106's own title scoped the migration
  to "the injected prelude" reading as the FUNCTION strings specifically (`stdlibFnSrcs`/
  `genericPreludeFnSrcs`); the data-type prelude is a separate, more foundational layer the survey
  never proposed moving.
- **D6 — the reference generator reads `Prelude.bang`, not `bang query symbols`.** `gen-reference.py`
  is a standalone Python tool with NO Lean-build dependency today (`just reference` can run before
  `lake build` ever completes); routing it through `bang query symbols Prelude.bang` would force
  building the binary first — a strictly worse bootstrap order for a docs generator. Instead
  `extract_prelude_section` regexes `Prelude.bang` directly for `pub let[ rec] NAME[ : SIG] = …`
  entries between the file's own `-- ── SECTION ──` header comments, falling back to a preceding
  `-- \`NAME ARGS : SIG\`` doc-comment line for un-annotated entries — the exact convention the
  retired string-extraction used, now pointed at the module instead of the Lean string list.

## Migration completeness

All 21 entries moved, byte-faithful to their original bodies (every `($f) x`-shaped forced
application preserved exactly — an early transcription pass "simplified" several to `$f x`, which a
live differential check caught as parsing to a DIFFERENT AST; restored before landing).
`stdlibFnSrcs`, `genericPreludeFnSrcs`, `wrapFnSrcs`, `wrapGenericFns`, and `injectStdlib` are
DELETED — no parallel string-injection path survives (one construct per problem). `surfUsesVar`'s
`TypeCheck.lean` copy, retired alongside `wrapGenericFns`, was RESTORED as `injectPrelude`'s own
mention-filter (the fuel finding, D3) — the copy still can't be replaced by an import of
`Bang.Query.surfUsesVar` (that module is downstream of `TypeCheck.lean`; importing it back cycles).

## The regression oracle

Every corpus `#guard` that exercised a prelude fn (`⑨h′`/`⑨j`/`⑨k` validations, ~40 guards) passes
unchanged post-migration — same expected values, same fuel budgets. An independent hand-built
module-form regression (21 calls, zero explicit `use`, matching the corpus's own literal test
expressions) sums to `612`, matching a hand-computed sum of the SAME 21 expected constants the
corpus's individual `#guard`s already assert. Shadowing verified live (a redefined `abs` wins). The
mention-filter verified live (`runOutcomeRaw 20 "$3"` — previously broken by the unconditional
first-pass implementation — passes at the SAME fuel=20 budget the pre-migration string-injected
version used).

## Revisit if

- `mergeModules`'s "merge every decl of a resolved module unconditionally" cost becomes a problem
  for ORDINARY (non-prelude) multi-file programs too — D2's fix trims the module fed to
  `mergeModules`, a narrow prelude-specific workaround; a general per-decl reachability trim inside
  `mergeModules` itself would be the more principled fix but is a bigger, riskier change to
  elaboration machinery shared by every module use, out of this migration's scope.
- The prelude outgrows 21 entries enough that even the FILTERED per-program fuel cost (one `letC`
  step per MENTIONED name — unavoidable, not a regression) starts to matter; nothing here changes
  that cost model, it only stops paying for UNMENTIONED entries.
- A consumer wants an escape hatch from the auto-`use` (a `--no-prelude` flag, or a module
  legitimately named `Prelude` the user wants precedence over) — no such need has surfaced; D4's
  per-name shadowing already covers the common case (redefine the one name you need different).

## Evidence

`docs/notes/stdlib-prelude-survey.md` §3 (the fork this resolves, and its "operator call, not
ruled" framing — now ruled), issue #106 + its two comments (the ruling and the unblock
correction), `225f3f42` (the #97 item-3 fix that unblocked this), ADR-0093 (the module machinery
this rides unmodified), `Bang/Core/Semantics/Eval.lean`'s `Config.run` (the fuel-per-step fact that
forced D2/D3), the corpus `#guard`s at `Bang/Frontend/TypeCheck.lean` validations ⑨h′/⑨j/⑨k (the
regression net).
