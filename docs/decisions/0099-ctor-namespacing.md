# ADR-0099 · Constructors are type-namespaced — bare names resolve when unambiguous in scope

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: A data constructor's true identity is `(dataName, ctorName)`, not `ctorName` alone
  (issue #108, operator-ruled option (a) 2026-07-11 — the ML/Rust convention). **`env.ctors`
  changes from a flat `List (String × CtorInfo)` keyed on the bare name to a table that PERMITS
  multiple entries under one bare name, one per owning type** — registration-time `duplicate
  constructor` refusal is DELETED for the cross-type case (same-type duplicates, e.g. two `Nil`s
  in one `data` decl, still refuse — that collision is never resolvable). **Resolution moves from
  registration time to USE time**: a bare ctor reference (`Nil`, a pattern `Cons(h,t)`) resolves
  when EXACTLY ONE in-scope `data` type owns that name; two or more owners is a LOUD `B012` error
  naming every candidate type and its qualified spelling. **The qualified fallback follows the
  ADR-0093 `Mod_Type` hand-qualification precedent exactly: `Type_Ctor`** (`IntList_Nil`,
  `List_Cons`) — an ordinary identifier, parseable today with ZERO grammar change (ctor intro is
  already bare application per ADR-0069 decision 4; a pattern name is already a bare `String`).
  **Migration is mechanical and LOCAL**: the only corpus break is same-program cross-type ctor-name
  collision (empirically: `Cons`/`Nil` shared between `IntList` and any injected/user `List`/
  `List a` — census below), fixed by qualifying the ambiguous occurrences, never a program-wide
  rewrite. **This unblocks #105's List-family prelude entries**: `Prelude.bang` can now declare
  `data List a = Nil | Cons(a, List a)` without breaking any corpus program that separately
  declares its own list-shaped type, PROVIDED that program's own bare `Nil`/`Cons` uses stay
  unambiguous (only fires if the program actually MENTIONS a colliding bare name — ADR-0098's
  `injectPrelude` mention-filter means a program that never uses `Nil`/`Cons` never even sees the
  prelude `List` in its `env.ctors`, so most of the corpus is untouched twice over).
- **Resolves**: issue #108 (design probe; implementation is a follow-up slice, not this ADR)
- **Depends-on**: 0069 (ctor elaboration + `CtorInfo`/`buildEnv` — the exact site restructured),
  0079 (generic data — `CtorInfo.dataName`/monomorphization untouched, resolution is orthogonal to
  mono vs generic), 0093 (the `Mod_Type`/`qualifyName` hand-qualification convention this ADR's
  qualified form is a direct extension of), 0098 (the `Prelude.bang` mention-filter that makes the
  common case pay nothing)
- **Relates-to**: #105 (the blocked List-family prelude entries this unblocks), #97/ADR-0097 §6
  (the derive handler — verified namespacing-INDEPENDENT, §6 below), `docs/notes/
  stdlib-prelude-survey.md` §1 (the universal-prelude functions gated on this landing)

## Status

Proposed (2026-07-11) — a design probe for #108, not an implementation. Every claim below is
either machine-checked against the real `bang` binary (witnesses in `docs/decisions/
witness-0099/`, built from a clean `lake build bang` on `design-ctor-namespacing` @ `dd60564f`) or
explicitly marked as an implementation-time decision this ADR pins but does not build.

- **Layer:** F (frontend — parser is UNTOUCHED, only the elaborator: `Bang/Frontend/
  TypeCheck.lean`'s `CtorInfo`/`ElabEnv.ctors`/`buildEnv`/`elabS`/`elabArms`/`matchD` arms).
  Kernel untouched by construction (invariant #5) — namespacing is a RESOLUTION question, entirely
  pre-kernel; the elaborated `Surf` a resolved ctor produces (`ctorIntro`/`genCtorIntro`,
  `TypeCheck.lean:1870-1883`) is byte-identical to today's for every UNAMBIGUOUS reference.

## Context

`ElabEnv.ctors : List (String × CtorInfo)` (`TypeCheck.lean:1712`) is a single flat association
list keyed on the BARE constructor name, populated by `buildEnv`'s `.dataD` arms
(`TypeCheck.lean:2869-2892`), both of which throw `"duplicate constructor '{c}'"`
(`TypeCheck.lean:2878`, `2889`) the moment a SECOND `data` decl anywhere in the program declares a
ctor name already present — regardless of whether the two decls' bare uses ever actually collide
in the program body. This is genuinely global scope, confirmed live (see §Ground w0): a program
declaring both `data List a = Nil | Cons(a, List a)` and `data IntList = Nil | Cons(Int, IntList)`
back-to-back, with NO use of either type's ctors anywhere in the body, still fails to elaborate.

#105's first-slice lane hit this empirically trying to inject a free `data List a = Nil |
Cons(a, List a)` into the prelude: it broke 4 pre-existing corpus `#guard`s, all sharing the same
root cause — a corpus program declaring its own `IntList`/`List` (monomorphic) whose bare `Nil`/
`Cons` collide with the newly-omnipresent prelude `List a`'s. Operator ruled option (a) — the ML/
Rust convention: a ctor belongs to its type; a bare name resolves when unambiguous. This ADR pins
the resolution rules, the qualified fallback, the migration story, and the diagnostics; #109-style
implementation is a follow-up.

## Decision

### 1 — Resolution rules

**A constructor's true key is `(dataName, ctorName)`.** `env.ctors` changes shape from
`List (String × CtorInfo)` to a structure that supports MULTIPLE `CtorInfo`s under one bare name
— the minimal change is `List (String × CtorInfo)` UNCHANGED AS A REPRESENTATION (still a flat
assoc list of `(name, info)` pairs) but the DUPLICATE-KEY REFUSAL at registration
(`TypeCheck.lean:2878`/`2889`) is DELETED for the cross-type case; only a genuine same-type
duplicate (two ctors named `Nil` inside the SAME `data` decl's own `cs` list) still refuses — that
collision has no bare-name resolution story even post-#108 (which ctor would `Nil` even mean
within one type?), so it stays a decl-time error, unchanged. Every OTHER `env.ctors.lookup`
call site (`elabS`'s `.var`/`.app` ctor-intro arms, `matchD`'s arm-table lookups, `elabArms`'s
payload-typing) changes from `.lookup` (first-match-wins on a flat list, silently picking
whichever `data` decl came first) to a NEW `resolveCtor env x : Except String CtorInfo` that:

1. Filters `env.ctors` to every entry whose bare name equals `x` — call this `candidates`.
2. `candidates = []` → not a ctor at all (today's `none` case — falls through to ordinary
   variable/application handling, UNCHANGED).
3. `candidates = [ci]` → resolves to `ci`, UNCHANGED elaborated output (`ctorIntro`/
   `genCtorIntro` are pure functions of the ONE resolved `CtorInfo` — nothing downstream of
   resolution needs to change).
4. `candidates.length > 1` → **AMBIGUOUS**, `B012` (§4).

**The ambiguity set is every `data` decl's ctors currently reachable in `env.ctors`** — which,
by construction, is exactly "every `data` decl this program's `buildEnv` walk has processed so
far" (ADR-0069's forward-reference-only decl order, `TypeCheck.lean:2845-2846`) UNION the
mention-filtered prelude (`injectPrelude`, ADR-0098) UNION any `use`-hoisted imported ctors
(ADR-0093 D2's "ctors travel with their type" — already unqualified in `env.ctors` by the time
`buildEnv` runs, since `mergeModules` resolves cross-FILE qualification before `buildEnv` ever
sees the merged decl list). **This is a single, uniform set — v1 does NOT distinguish "prelude
ctor" from "user ctor" from "imported ctor" for ambiguity purposes**; whichever combination of
`data` decls is in scope at the reference site is what counts. This is deliberately the SIMPLEST
rule available (flat set membership, no priority tiers) — §2 covers the one place a priority
tier is ALREADY established (shadowing) and why it does not need to interact with ambiguity.

**Scrutinee-type-directed narrowing (fork (b) in #108's issue text) is NOT adopted as the primary
mechanism, but composes as free ADDITIONAL disambiguation where it already exists.** `matchD`'s
existing arm-table derivation (`genBinderTable`, `TypeCheck.lean:2731-2733`) already looks up the
FIRST arm's ctor name to seed `ci0` before the ambiguity question is even asked — so `resolveCtor`
naturally runs INSIDE that existing type-directed context for match arms specifically (§1a). For
ctor INTRODUCTION (`Cons(7, Nil)` in expression position), there is no scrutinee to direct
resolution — check-mode ascription (`: List Int`) is a SEPARATE, ADR-0079-precedented mechanism
(annotation-driven generic introduction) that narrows WHICH monomorphization of an already-
resolved ctor to build, not WHICH data type owns the bare name; conflating the two would mean a
single resolution function doing double duty for unrelated questions. **Recommendation: keep them
separate** — `resolveCtor` answers "which type does this bare name belong to" using ONLY the
static ambiguity-set membership rule above; annotation-driven monomorphization (ADR-0079) runs
strictly AFTER, unchanged, once a single `CtorInfo` is in hand.

**1a — Where resolution lives.** The issue text asks "parser has no type info → elaborator" —
confirmed: `pCtor`/`pCtors` (`Surface.lean:1929-1944`) parse a ctor as a bare `String` with zero
semantic lookup (the parser doesn't even have `env.ctors` in scope structurally). Every site listed
above (`elabS`'s `.var`/`.app` arms, `matchD`'s two `env.ctors.lookup c0` call sites plus the
per-arm-ordering `env.ctors.find?`, `elabArms`'s payload-typing lookup) lives in `elabS`/
`elabArms`/`buildEnv` — all elaborator-side, confirming the issue's own framing. No parser change.

### 2 — Shadowing / priority

**Bare-name AMBIGUITY and SHADOWING are different questions, already answered by different,
NON-INTERACTING mechanisms — this ADR does not need to invent a priority rule.** Shadowing (which
of two SAME-spelled things is "the" one when one hides the other) already has an answer for the
type-NAME case: `strPrelude`/`genericPrelude`'s "filtered out... when the user redeclares it"
(`TypeCheck.lean:3786`, `declared.contains n`) — verified live (§Ground w-shadow): a user's own
`data Option a = MyNone | MySome(a)` completely REPLACES the built-in `Option` (different ctor
names entirely; the built-in `Option`'s `None`/`Some` are never even registered), so there is
NOTHING left to be ambiguous with — the built-in decl is filtered OUT of the decl list before
`buildEnv` ever runs. **This is a same-TYPE-NAME shadow, orthogonal to #108's same-CTOR-NAME-
different-TYPE ambiguity** — #105's actual break (`IntList`'s `Nil` vs `List a`'s `Nil`) is TWO
DISTINCT type names both surviving into scope, each contributing a `Nil`. Shadowing's filter
never fires here (the type names differ), so the question is purely "do two DIFFERENT survivors
share a ctor name" — exactly §1's ambiguity-set membership question, no priority tier needed.
**A user's own `data` decl never automatically "wins" a ctor-name collision against a same-scope
prelude `data`** — both are just members of the ambiguity set; a colliding bare use is ambiguous
regardless of which one is "the prelude's" vs "the user's". This is the CORRECT default (silently
picking the user's decl would be exactly the "guess, don't error" move `Source.eval`'s discipline
forbids, ADR-0046) and it is what the migration story (§3) actually needs — a collision always
gets a LOUD, named, fixable error, never a silent semantic change depending on decl order.

**Does the Prelude.bang "user wins" contract extend per-ctor?** No — and this is not a
contradiction. ADR-0098 D4's "user wins" is `mergeModules`' EXISTING alias-shadowing for BARE
NAMES the user explicitly redeclares under the SAME spelling (`let abs = …` shadows the
auto-`use`d prelude `abs`, one name, one binder, innermost wins — an ordinary lexical-scoping
fact, not a namespacing decision). A ctor-name COLLISION between two DIFFERENTLY-NAMED types
(`IntList` vs `List`) is not that shape at all — there is no "redeclaration" (the user did not
write a second `data List a`; a `data IntList` is a wholly different decl), so there is nothing
for D4's shadow rule to apply TO. The ctor-namespacing ambiguity is a NEW kind of collision D4
never covered, and correctly gets a NEW answer (ambiguity error, not silent precedence).

### 3 — Migration

**The falsifier, run against the real binary (§Ground):** does any TODAY-passing corpus program
rely on a cross-type bare-ctor PUN (the same bare name meaning DIFFERENT things in different
scopes of ONE program, exploiting the fact that today's flat table's first-match-wins semantics
picks a specific one)? **Answer: no such program exists in the corpus** — today's registration-
time `duplicate constructor` refusal (unconditional, decl-time, `TypeCheck.lean:2878`) makes this
STRUCTURALLY IMPOSSIBLE: two `data` decls sharing a ctor name in ONE program is ALREADY a hard
compile error today, with ZERO exceptions (confirmed: `grep`ing the corpus for any TWO co-present
`data` decls sharing a ctor name found none — `IntList`'s `Nil`/`Cons` and `List a`'s `Nil`/`Cons`,
the ONLY same-name pair in the whole 45k-line corpus, never appear in the SAME `#guard`'s source
string; each `List`/`List a` test is its own standalone program). **Consequence: #108 cannot
possibly break an EXISTING corpus program** — every corpus program that compiles today has, by
construction, no cross-type ctor collision to become ambiguous. The only place #108 introduces new
possible failures is a genuinely NEW combination not previously expressible: a program that
declares/imports/uses TWO SEPARATE colliding types AT ONCE — which is exactly and ONLY what #105's
prelude injection does (adding a globally-present `List a` next to a program's own `IntList`/
`List`). **The migration is therefore not "fix N broken corpus programs"** (none break) **but "the
4 #105-blocked entries become expressible, with the qualified fallback as their fix"** — verified
by re-running the exact 3 corpus source-strings the #105 finding named (§Ground, "the exact break"
below): each fails IDENTICALLY today whether or not #108 has landed (both fail at the SAME
registration-time wall, confirmed live) and each is fixed the SAME mechanical way — replace the
colliding bare `Nil`/`Cons` in the AFFECTED program's own body with `IntList_Nil`/`IntList_Cons`
(or, if #105 additionally reorders so `IntList`'s decl comes textually after `List`'s, no source
change at all is needed for programs that already used a NON-colliding local type like `L`/
`LNil`/`LCons`, confirmed w3). **No corpus-wide rewrite; the fix is strictly LOCAL to whichever
individual program's bare ctor becomes ambiguous once the prelude's `List a` is added to its
scope** — and by ADR-0098's mention-filter, that scope-addition itself only happens for programs
that mention a `List`-family name in the first place (a program using neither `Nil` nor `Cons`
nor any other `List` name never sees the prelude `List a` merged in at all, so it can never become
ambiguous by mere prelude presence — verified structurally, `injectPrelude`'s `progUsesVar` walk).

### 4 — Diagnostics

**New code `B012`** (next free — the registry's highest is `B011`, `DiagCodes.lean:142`),
positioned BEFORE `B006`'s broad `"constructor '"` catch-all (same specificity-ordering discipline
the registry already documents for B007/B011 vs B006, `DiagCodes.lean:150-152` — an ambiguous-ctor
message necessarily also contains the substring `"constructor '"`, so it must be listed earlier or
B006 silently swallows it). Anchor: `["ambiguous constructor"]`. Message shape, matching the
existing `s!"..."` interpolation convention and the "error TEACHES the fix" discipline (ADR-0093
D2/D3's precedent):

```
error: ambiguous constructor 'Nil' — candidates: IntList (as 'IntList_Nil'), List (as 'List_Nil')
```

listing every candidate type name PAIRED with its qualified spelling (not just the type names) so
the message is directly actionable without a second lookup — the same "the error names the fix"
shape `firstPrivateUse`'s private-decl diagnostic already established (ADR-0093 D3,
`TypeCheck.lean:3263-3268`, "names BOTH the module and the specific private name"). `bang explain
B012` teaching text: ambiguity is a scope fact (two co-present `data` types share a ctor name),
resolved by writing the type-qualified form `Type_Ctor`.

### 5 — The acceptance spike

**Hand-simulated + machine-checked against the real binary** (witnesses in `docs/decisions/
witness-0099/`, run via `bang run` on `design-ctor-namespacing` @ `dd60564f`, `.lake/build/bin/
bang`, `lake build bang` → `Build completed successfully (1448 jobs)`):

| witness | shape | TODAY's result (do-not-regress baseline) | POST-#108 target |
|---|---|---|---|
| `w0-baseline-duplicate-today.bang` | `data List a`+`data IntList` co-present, ctors UNUSED | `error: duplicate constructor 'Nil'` | types + runs (`0`) — nothing is ambiguous, no bare use exists |
| `w1-coexist-qualified.bang` | same co-presence, `IntList`'s ctors used via qualified `IntList_Nil`/`IntList_Cons` | same `duplicate constructor` wall (registration never reaches use-time today) | types + runs, returns `7` — the #105/#108 acceptance case: prelude `List` + user `IntList` coexist, `IntList` matched correctly via its qualified ctors |
| `w2-ambiguous-bare-error.bang` | same co-presence, BARE `Nil` referenced | same `duplicate constructor` wall | `error[B012]: ambiguous constructor 'Nil' — candidates: IntList (as 'IntList_Nil'), List (as 'List_Nil')` — loud, not silent |
| `w3-unambiguous-bare-still-works.bang` | `data L`(`LNil`/`LCons`, no collision) + `data IntList`, BARE `Nil`/`Cons` used | **passes today** (`7`) — no collision exists | UNCHANGED (`7`) — the non-colliding common case is untouched |

`w0`–`w3` machine-confirmed at the stated "TODAY" column (all four run identically against the
real binary this session — the first three at the identical `duplicate constructor 'Nil'`
registration wall, confirming they are ONE root cause, not three; `w3` passes today, establishing
the non-regression floor). The "POST-#108 target" column is the falsifiable acceptance criterion
the implementation slice must satisfy — not yet built (this ADR is a design probe).

### 6 — Sequencing vs the derive handler (ADR-0097)

ADR-0097 §6 already analyzed this exact question and concluded the derive handler (issue #109) has
**no ordering dependency on #108's implementation**: a derive's emitted `match` arms name ONLY the
ctors of the ONE type being derived over, which is unambiguous by construction regardless of
whether OTHER co-present types share those ctor names. **This ADR does not revise that
conclusion** — §1's `resolveCtor` runs per-reference, and a derive-emitted reference is always
same-type-scoped, so it degrades gracefully whether #108 has landed or not, exactly as ADR-0097
predicted. Verified consistent: nothing in this ADR's resolution rule (§1) special-cases WHERE a
`Surf` node came from (hand-written vs derive-emitted) — resolution is purely a function of the
bare name + the ambiguity set, agnostic to provenance.

## Rejected alternatives

- **(b) Scrutinee-type-directed resolution ONLY, no type-namespacing** — narrower than what #108
  asks for (only disambiguates AT a `match`, not at ctor INTRODUCTION — `Cons(7, Nil)` in
  expression position has no scrutinee to direct by), and doesn't dissolve the REGISTRATION-time
  wall at all (today's refusal fires before any use exists, §Context) — the operator's ruling
  already selected (a) over this; recorded here because §1 explicitly folds (b)'s mechanism in as
  a compositional aid for match arms specifically, not as the primary rule.
- **(c) Prelude ships under non-colliding names (`LNil`/`LCons`)** — permanently ugly (the
  operator's own framing in the issue), and doesn't fix the underlying disease for USER programs
  that hit the same collision with each other (two unrelated libraries both naming a variant
  `Some`/`None`-shaped type) — only patches the ONE instance #105 happened to surface.
  Rejected per the ruling; not reconsidered here.
- **(d) Wait for Prelude.bang's `use`-selective import to make collisions user-managed** —
  `Prelude.bang` LANDED (ADR-0098) auto-`use`, MENTION-FILTERED, which is exactly the mechanism
  that makes §3's migration story cheap (a program not mentioning `List`-family names never even
  merges the prelude's `List a` in) — but auto-`use` is unconditional for MENTIONED names (no
  selective opt-out exists, and ADR-0098 explicitly declined to add one, "Revisit if" list) so a
  program that DOES mention a colliding name has no user-managed escape without #108's actual
  resolution rule. (d) is subsumed, not superseded — ADR-0098 already landed and its mention-
  filter is load-bearing for §3's "no corpus-wide cost" claim, but it alone does not dissolve
  ambiguity once a collision is actually mentioned.
- **A priority tier (user-declared ctors always beat prelude/imported ones on a bare collision)**
  — rejected in §2: silently picking a winner by provenance is the exact "guess, don't error" move
  ADR-0046 forbids; it would also make a program's meaning depend on DECL ORDER or import order in
  a way the qualified fallback makes structurally unnecessary (the fix is always available, cheap,
  and named by the error itself).
- **`Mod.Ctor` (dot syntax) instead of `Type_Ctor`** — rejected for the SAME reason ADR-0093 §
  "`Mod_Type`" rejected dot syntax for qualified types: `.` is the live `.dotPerform`/capability-
  call token (`h.get`, `Foo.op`), so `List.Cons(...)` would either need new grammar disambiguation
  or collide with the existing qualified-call parse; `Type_Ctor` needs ZERO grammar change (ctor
  intro is bare application, ADR-0069 decision 4; a match-arm ctor name is already a bare
  `String`) and is the DIRECT extension of the `Mod_Type` convention already documented in
  `docs/reference/language.md` — one qualification scheme for the whole language, not two.

## Ground (witnesses run against the real binary, this session)

Built from a clean checkout (`design-ctor-namespacing` @ `dd60564f`, `.lake/build` reflink-seeded
from the main checkout per `tools/seed-lake.sh`'s own logic — this is a standalone clone, not a
linked worktree, so the script's auto-detected `main_root` did not apply; the seed was done by
hand against the same source/target pair the script uses — `lake build bang` → `Build completed
successfully (1448 jobs)`, `.lake/build/bin/bang`).

| witness | result |
|---|---|
| `docs/decisions/witness-0099/w0-baseline-duplicate-today.bang` | `error: duplicate constructor 'Nil'` — the registration-time wall, confirmed live |
| `docs/decisions/witness-0099/w1-coexist-qualified.bang` | same wall (registration never reaches the qualified-use body) — confirms the wall is unconditional, not use-triggered |
| `docs/decisions/witness-0099/w2-ambiguous-bare-error.bang` | same wall |
| `docs/decisions/witness-0099/w3-unambiguous-bare-still-works.bang` | **passes today**, returns `7` — the non-colliding case, do-not-regress floor |
| the exact `IntList` `#guard` source strings (`listProg "let s = Cons(7, Nil) in match s { Nil -> 0, Cons(h, t) -> h }"`, `TypeCheck.lean:4357`) with `data List a = Nil \| Cons(a, List a)` prepended | `error: duplicate constructor 'Nil'` — reproduces the #105 finding directly against the exact corpus source |
| the `listRec`-shaped `let rec sum` source (`TypeCheck.lean:4490`) with the same prepend | `error: duplicate type name 'List'` — the ORTHOGONAL type-NAME collision (already solved today by `strPrelude`/`genericPrelude`'s redeclare-filter mechanism, `TypeCheck.lean:3786`; NOT in #108's scope, confirmed by the `Option`-redeclare witness below) |
| user `data Option a = MyNone \| MySome(a)` (ctors renamed, type name reused) | `bang run` → `7`, matched via `MySome(x) -> x` — confirms shadow-by-type-name-redeclaration already works, orthogonal to #108's ctor-collision-across-DIFFERENT-type-names problem |
| `data A = Foo(Int)` + `data B = Foo(Int)` (no use, just co-presence) | `error: duplicate constructor 'Foo'` — a second, independently-confirmed instance of the registration-time wall, generalizing beyond the `List`/`IntList` pair |
| ADR-0097 §6, `Bang/Frontend/TypeCheck.lean:2854-2929` (`buildEnv`'s ordering) | consulted, not re-verified this session (ADR-0097's own machine-checked finding, unrelated wall) |

Also consulted: `Bang/Frontend/Surface.lean:1929-1963` (`pCtor`/`pCtors`/`pDataParams` — the
grammar, confirmed untouched by this design), `Bang/Frontend/TypeCheck.lean:1645-1719` (`CtorInfo`/
`ElabEnv` field shapes), `:2534-2843` (`elabS`/`elabArms`, every `env.ctors.lookup`/`.find?`/
`.filter` call site enumerated), `:3013-3032` (`strPrelude`/`genericPrelude`, the type-name-
redeclare-filter precedent), `:3045-3260` (`qualifyName`/`qualifyDeclName`/`qualifyModule`/
`isPubName` — the `Mod_Type`/`ctorOwners` cross-FILE qualification machinery this ADR's
`Type_Ctor` form is a same-scheme, different-axis extension of — module qualification disambiguates
by FILE, ADR-0099 disambiguates by TYPE, both mangle via `name1_name2`), `docs/reference/
language.md:166-171` (the `Mod_Type` convention, the direct precedent), `Bang/Frontend/
DiagCodes.lean` (the B0xx registry + specificity-ordering discipline `B012` follows).

## Consequences

- #105's List-family prelude entries (`length`/`append`/`head`/`tail`/`take`/`drop`/`zip`) can ship
  once `Prelude.bang` declares `data List a = Nil | Cons(a, List a)` — this ADR's resolution rule
  is the ONLY blocker named in #108, and it is dissolved by construction for the common case (no
  collision) and by a named, local, mechanical fix for the colliding case.
- A future user-authored library sharing a ctor name with another library (or the prelude) gets
  the SAME treatment — ambiguity is a general property of the resolution rule, not a one-off patch
  for `List`/`IntList`.
- `ElabEnv.ctors`'s REPRESENTATION does not need to change shape (still `List (String × CtorInfo)`)
  — only the REFUSAL (deleted for cross-type dups) and every LOOKUP call site (replaced by
  `resolveCtor`'s ambiguity-counting wrapper) change. This keeps the implementation slice small and
  localized to `TypeCheck.lean`, no `Surface.lean`/parser change, no kernel change.

## Implementation slice map (sized, for the follow-up issue)

1. **`buildEnv`'s `.dataD` arms** (`TypeCheck.lean:2869-2892`, both mono + generic): delete the
   cross-type `duplicate constructor` throw; KEEP the same-type-duplicate check (a `data` decl's
   OWN `cs` list still can't repeat a ctor name — unrelated to #108, that collision has no
   resolution story). Small — two `if` conditions narrowed from "any prior owner" to "an owner
   with the SAME `dataName`".
2. **`resolveCtor : ElabEnv → String → Except String CtorInfo`** (new function): the §1 filter +
   count logic. Small, self-contained, no existing function's signature changes.
3. **Six call sites migrate from `env.ctors.lookup`/`.find?` to `resolveCtor`**: `elabS`'s `.var`
   arm (`:2537`), `.app (.var c) a` arm (`:2620`), `matchD`'s two `env.ctors.lookup c0` sites
   (`:2727`, `:2740`) plus the ordering `env.ctors.find?` (`:2762`, this one is POST-resolution
   bookkeeping over `dcs`, a DIFFERENT list already filtered to one `dataName` — likely unchanged,
   needs a close read at implementation time, not a blind swap), `elabArms`'s payload-typing
   lookup (`:2809`). Medium — six sites, each a small diff, but each needs its OWN `#guard`
   (positive: still resolves; negative: `B012` fires) per the "the corpus is the contract"
   discipline.
4. **`Type_Ctor` qualified-form PARSING**: NONE needed — `IntList_Nil` parses today as an ordinary
   identifier (confirmed: `pIdent`/`pCtor` have zero reserved-character handling for `_`,
   `TypeCheck.lean:3043-3045`'s own comment on `qualifyName` says so explicitly for the module
   axis, and the same tokenizer fact holds for this axis). Zero parser-slice cost — the entire
   qualified form is FREE once `resolveCtor`'s bare-name lookup also checks for an EXACT
   `dataName_ctorName` spelling as an equally-valid resolution path (a `CtorInfo.dataName`-prefixed
   literal match, not a NEW field — `resolveCtor` tries the bare-name ambiguity-set filter first,
   then falls back to checking whether the reference IS already one candidate's `Type_Ctor` form).
5. **`DiagCodes.lean` registry**: add `B012`, ordered before `B006` (mirroring the existing
   `B007`/`B011`-before-`B006` precedent verbatim) + its `#guard`. Small, mechanical.
6. **Regression `#guard`s**: the four witnesses (§5) promoted from `docs/decisions/witness-0099/`
   into `TypeCheck.lean`'s corpus (or a new `Bang/Frontend/CtorNamespacing` test module, matching
   how other multi-witness features got their own test home) — expectations COMPUTED from
   `Source.eval`, not guessed, per the corpus discipline. Small-medium (four cases, each already
   hand-verified against the real binary this session).
7. **`Prelude.bang`'s `data List a` declaration itself + the #105 List-family functions** — OUT OF
   SCOPE for this slice (a separate #105 follow-up once #108 lands; this ADR only unblocks it).

No kernel-adjacent touch anywhere in this map — entirely `Bang/Frontend/TypeCheck.lean` +
`Bang/Frontend/DiagCodes.lean`, both fan-in-0 leaves.

## Revisit if

- A future collision needs PRIORITY (not just qualification) — e.g. an ecosystem convention
  emerges where "the innermost/most-local `data` decl should silently win" — this ADR's §2
  explicitly rejects that as a default; revisit only with a concrete, named user need (none exists
  today, ADR-0098's own "no such need has surfaced" precedent for a similar ask).
  `qualifyName`/`Type_Ctor` becomes onerous with the `List` family PLURALIZED further (deep type
  hierarchies with many small collisions) — a `use`-style selective ctor-import within ONE file
  (not just across module boundaries) could reduce qualification noise; no evidence this is needed
  yet (v1's collision census is exactly one pair, `List`/`IntList`).
- #105's List-family prelude entries land and surface a SECOND real-world collision beyond
  `List`/`IntList` (e.g. a user's own `Result`-shaped type colliding with the prelude `Result`) —
  this ADR's rule already covers it identically (no type-name-specific logic anywhere in §1); no
  design revision expected, just confirms the rule generalizes.
