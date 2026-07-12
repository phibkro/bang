# 0107 — effect-row reuse: subeffecting at reuse sites, open-row ascription deferred (#94)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: #94 (`unifyRow`'s single-shared-row-var "first cut" rejected reusing ONE
  row-polymorphic binding at two genuinely different effect rows in one program, even though
  each use alone type-checks) is ruled: **adopt subeffecting (`φ_use ⊆ φ_bound`) at reuse
  sites**, via the ALREADY-PROVEN-SOUND `subRow` relation this checker already uses elsewhere
  (`checkSC`'s `.thunk`/`.annotS` arms, `subsumeAppV`'s own #119 precedent) — NOT full Rémy
  independent-tails row polymorphism, which stays deferred behind its own consumer gate (no
  program needs INCOMPARABLE-row reuse today). The kernel's row algebra (`Bang/EffectRow.lean`,
  ADR-0001/ADR-0018) is untouched; this is a purely FRONTEND widening of which programs the
  checker admits.
- **Depends-on**: ADR-0001 (rows are idempotent `Finset`s — the join-semilattice this ruling's
  own `⊆`/`∪` relations are stated over), ADR-0018 (the kernel's already-shipped
  lacks-constrained open row quantifiers — the machinery this ruling's OWN "no kernel change"
  claim rests on), #119 (the `subRow`/`subsumeAppV` fork-1 precedent this ruling's `S1` slice
  reuses verbatim, not reinvents)
- **Date**: 2026-07-12
- **Deciders**: operator (Frontend lane, `docs/notes/type-power-entry-design.md`'s Wave-E
  entry-slice design, ratified as task #164)
- **Ties**: docs/notes/type-power-entry-design.md (the full consumer-verdict + entry-slice
  design this ADR formalizes the S1 decision from), issue #94 (the isolated non-cap repro),
  `examples/stage-swap/README.md` §"Known gate" (the flagship-demo corpus witness), issue #84
  (the per-stage handler-swap thesis this reuse wall was found inside),
  `docs/notes/calc-typer-experiment-findings.md` (the independent theory corroboration —
  subeffecting is Cousot's consequence rule, derived not postulated)

## Context

Bang's checker infers a row-POLYMORPHIC type for any `let`-generalized binding whose body
forces two of its own function-typed parameters — `let compose = {fun p => fun q => fun x =>
($p)(($q) x)}` types as `∀ρ. (b→c!ρ)→(a→b!ρ)→(a→c!ρ)` (ADR-0075 bite-0b item 3). Two SEPARATE
uses of `compose`, each internally at one consistent row, already worked (`rowPolyDivSrc`'s own
`inc∘dbl` at `⊥` AND `countdown∘countdown` at `{Div}`, coexisting in one program — the row
POLYMORPHISM itself was proven, not the gap this ADR closes).

The gap: `joinRow`'s "single-ρ first cut" (`TypeCheck.lean:503`'s own doc comment) COLLAPSES
`compose`'s two internal row vars (`ρp`, `ρq`) to ONE shared var during `compose`'s own body
elaboration — a sound, deliberate over-approximation (ADR-0075's own scoping). The consequence:
`compose`'s domain for `p` and `q` share ONE row variable, so applying `compose` to a PURE
function (`inc`, row `⊥`) then a `{Div}`-rowed function (`cd`) WITHIN ONE `compose` application
pins that shared var to `⊥` on the first use, then demands EXACT equality against `{Div}` on the
second — `unifyRow`'s `EffectRow.unify` closed/closed case (`EffectRow.lean:120-121`) has no
leeway, so the reuse fails loud ("effect row mismatch"), even though `⊥ ⊆ {Div}` makes the
combination semantically unproblematic.

This is not a hypothetical: `examples/stage-swap`'s own flagship demo of the per-stage
handler-swap thesis (#84 — "the stage IS the handler") hits this WALL reusing its `test`
installer against an effectful `logic` body then a pure `pureBody` — the README's own "Known
gate" section names it, the checker's own `rowPolyDivSrc` corpus pins it as an expected FAIL,
and #94 reproduces it with ZERO capability/user-effect involvement (`compose incPure
<effectful>`), proving the wall is row-inference-GENERAL, not a capability-wrapper artifact.

## Decision

**Adopt subeffecting (`φ_use ⊆ φ_bound`) at row-polymorphic reuse sites.** `unifyRow`'s ONE call
site in the whole checker (`unifyV`'s `.U φ B, .U φ' B'` case — every `.U`-typed comparison in
the checker funnels through here) now falls back to subeffecting when `EffectRow.unify`'s exact
match fails:

1. If EITHER side's row, BEFORE resolution, carried an open tail variable (`.tail = some v`),
   re-bind that variable to the WIDER JOIN (`a.labels ∪ b.labels`) instead of failing. The
   narrower use was always `⊆` the join; `EffectRow.applyR`'s own resolve-time union
   (`EffectRow.lean:107`) is exactly the mechanism that then makes every SUBSEQUENT lookup of
   that variable see the widened set. `rassign`'s list-prepend semantics mean this shadows the
   earlier (narrower) binding going forward without retracting anything the earlier binding
   already committed to at ITS OWN call site.
2. If BOTH sides are already closed (a handler discharges the row before the two sides are ever
   compared — the stage-swap shape, where `test`'s return type is already `Int` with no row
   var), admit the JOIN directly when one side's label set is a `⊆` of the other's — the same
   subset relation, applied where there is no variable left to re-bind because the discharge
   already erased it.
3. If NEITHER condition holds (both sides closed, NEITHER a subset of the other — a genuinely
   INCOMPARABLE-row reuse, e.g. `{Net}` vs `{Log}`), fail loud with the #94-naming diagnostic
   (task #164's own S0 slice, landed first) — subeffecting only ever ADMITS more programs, it
   never silently accepts an actually-incompatible pair.

**Full Rémy independent-tails row polymorphism (open-row ascription, `∀(α # L). τ` surface
syntax over ADR-0018's kernel form) is the NAMED NEXT RUNG, deferred behind its own consumer
gate.** No program in the corpus needs INCOMPARABLE-row reuse today (subeffecting closes every
CITED consumer — the stage-swap witness, #94's repro, `rowPolyDivSrc`'s pinned corpus); building
the general independent-tail machinery ahead of a real consumer would be exactly the
speculative-generality the No-Free-Lunch discipline forbids (`docs/notes/type-power-entry-design.md`
§9's own slice map, S3).

## Rejected / staged

- **Status-quo single-ρ collapse (do nothing)** — REJECTED: it IS #94, a feature-gating
  incompleteness with FOUR independent, cited consumer signals (a corpus witness, a filed issue,
  an in-checker pinned expected-failure, and an independent theory corroboration —
  `type-power-entry-design.md` §2). Leaving it unfixed keeps a real demo (`examples/stage-swap`)
  artificially limited to separately-named installer bindings.
- **Full Rémy FIRST, before any subeffecting slice** — REJECTED: no incomparable-row consumer
  exists to justify the extra machinery (independent lacks-constrained tail variables, a real
  `∀(α # L)` surface binder, per-use fresh instantiation threading through `generalize`) ahead of
  demand. Subeffecting is STRICTLY cheaper (reuses `subRow`'s EXISTING soundness proof,
  `unify_sound`, rather than needing a new one) and closes every cited consumer on its own.
- **ρ-map / `lift`-based multi-instance rows** — REJECTED: ADR-0018's own accepted cost
  ("NOT via `lift`/ρ-maps, which would re-introduce a non-idempotent (multiset) row algebra and
  break everything below"). This ADR's own `∪`/`⊆` relations are stated over `Finset`, matching
  ADR-0001's idempotent-set invariant throughout — nothing here reintroduces ordering or
  multiplicity.
- **Retroactively re-checking every PAST use of a widened row var** — CONSIDERED, not needed: the
  earlier (narrower) use already type-checked CORRECTLY against the row it saw at that time
  (`⊥` for `inc`, in the worked example) — subeffecting never invalidates a PAST judgment, it
  only widens what a row var resolves to for FUTURE lookups. No re-verification pass is required
  because the earlier judgment's own soundness never depended on the row staying narrow forever.

## Consequences

- `examples/stage-swap`'s README "Known gate" section is now STALE (the program it names as
  failing now type-checks and runs) — a documentation follow-up, not gated by THIS ADR (the
  README itself is out of `Bang/**`'s own leaf discipline).
- The checker's `rowPolyDivSrc` corpus (renamed `rowSubeffectSrc`) and the stage-swap witness
  corpus (renamed `stageSwapReuseSrc`) both FLIPPED from pinned expected-FAILURE to pinned
  expected-SUCCESS, each with a `runTypedYieldsInt` differential check against `Source.eval` —
  the SAME corpus now documents the FIX instead of the gap.
- No kernel change, no census re-proof: the 18→20 headline theorem count (and every `just
  axioms` baseline) is UNCHANGED by this ADR — confirmed live (S0 and S1's own landing commits
  both show a byte-identical axiom census to the pre-change baseline).
- `unifyV`'s `.U` case is no longer a PURE unification call — it now has a fallback branch with
  its own (proven-sound-by-composition, not independently proven) soundness argument. Future work
  touching `unifyV`/`unifyRow` must preserve this fallback's own three-way disjunction (var-widen
  / closed-subset / fail), not just the exact-match fast path.

## Revisit if

A real program needs reuse at two GENUINELY INCOMPARABLE rows (neither `⊆` the other — e.g. a
binding genuinely needing `{Net}` in one use and `{Log}` in another, with neither row a subset)
— that is Slice B / S3's own trigger, `type-power-entry-design.md` §5's Slice B surface sketch
(`∀(α # L). … ! φ ⊔ α`) is the pre-designed next rung. OR a soundness gap is found in the
subeffecting fallback itself (the `subsumeAppV`/`subRow` precedent this ADR reuses has its OWN
soundness proof, `unify_sound`, but the NEW three-way disjunction in `unifyRow` composing that
relation with `EffectRow.unify`'s existing cases has not been independently re-proven — a
falsifier here would be a program the checker WRONGLY accepts, caught by the differential test
against `Source.eval`, per this project's own MGU-is-not-the-contract, soundness-via-differential-test
posture).
