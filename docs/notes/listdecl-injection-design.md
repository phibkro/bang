<!-- note-status: active -->
# List-decl injection design — should the prelude ship `data List a`?

> Design probe for the residue ADR-0103 named on landing: a bound-free `let rec` (`take`/`drop`)
> works TODAY against a program's OWN `data List a`, but no kernel-provided `List` type exists —
> `Prelude.bang` cannot construct/consume a `List` for a program that declares none. This note
> answers whether the prelude should inject ONE canonical `List` decl, against the interactions
> named in the assignment: (a) a user program with a structurally-identical `List`, (b) a
> structurally-DIFFERENT user `List`, (c) B012 type-namespaced constructors (ADR-0099), (d)
> mechanism A (string injection) vs `Prelude.bang` (ADR-0098), (e) `length`'s fuel tax (#120/#105).
> Established 2026-07-11. Every claim below is witnessed against the real binary
> (`scratch/listdecl/w*.bang`, built from a clean `lake build bang` on this branch) or cites a
> line in the committed source — no reasoned-only verdicts.

## 0. What's already decided (read this first — most of the assignment is answered)

The assignment names five interaction axes as if they were open. Three of the five are **already
closed by prior ADRs**, landed and machine-verified before this probe started. Re-litigating them
here would violate "a question with an ADR is closed, not open." What's actually left is narrower
than the brief:

```
axis (from the assignment)              status                                    closed by
──────────────────────────────────────────────────────────────────────────────────────────────
(a) structurally-identical user List    ANSWERED: type-name shadow, zero-code,     ADR-0098 D4
                                         arity-agnostic (witnessed w10 below)
(b) structurally-different user List    ANSWERED: ADR-0099 B012 iff BARE ctor      ADR-0099
                                         names collide; type-name-only difference
                                         never collides at all (w3/w9/w11)
(c) B012 namespaced constructors        ANSWERED, LANDED, machine-verified live    ADR-0099
                                         (not a design question — an implemented
                                         mechanism this note re-confirms works)
(d) mechanism A vs B                    ANSWERED: B won (Prelude.bang, auto-use,   ADR-0098
                                         mention-filtered). Mechanism A is DELETED
                                         from the codebase — not a live fork.
(e) length's fuel tax                   REAL, OPEN — the one genuine residue       ADR-0103 (named,
                                                                                     not designed)
```

The genuinely open question — the one this note spends its budget on — is narrower than "should
the prelude inject a List decl": it is **how should the mention-filter (`progUsesVar`/
`injectPrelude`) see a TYPE-ONLY reference**, since that is the one mechanism gap ADR-0103's
Implementation section named and explicitly deferred (not designed). §3 below designs it. §4 covers
`length`'s fuel tax, the other named-but-undesigned residue.

## 1. The witnessed baseline (what works today, unconditionally)

```
witness                                  shape                                    result
──────────────────────────────────────────────────────────────────────────────────────────────
w1-take-own-list.bang                    user `data List a` + `$take`             1  (correct)
w3-collision-intlist-vs-list.bang        user `data List a` + `data IntList`,     1  (correct,
                                          co-present, bare uses touch only List    no ambiguity —
                                                                                    diff type names)
w4-collision-bare-ctor-clash.bang        `data IntList = Nil|Cons` +               B012, naming
                                          `data List a = Nil|Cons`, BARE `Cons`     BOTH candidates +
                                          used (simulates unconditional injection   qualified spelling
                                          colliding with a same-ctor-name type)
w9-samename-different-shape.bang         user's OWN monomorphic `data List`         3  (correct,
                                          (arity 0, not `List a`), no prelude       standalone)
                                          List in play at all
w10-option-arity-shadow.bang             user's own arity-0 `Option` (renamed       7  (correct —
                                          ctors) — probes whether TYPE-NAME          the type-name
                                          shadow is arity-agnostic for an           shadow already
                                          EXISTING generic-bucket type              works this way
                                                                                     for Option today)
w11-mapoption-plus-monolist.bang         built-in generic `Option a` (mapOption)    14 (correct —
                                          + user's own monomorphic `data List`,      11+3, both
                                          co-present and BOTH used                   families compose)
w6-length-collision.bang                 user's own `length : Int -> Int`,          3  (correct —
                                          same name as the (unshipped) List-        D4 shadow works
                                          family prelude entry                      by VALUE)
w12-str-length-shadow.bang               user's own `length : Str -> Int`,          2  (correct,
                                          same name, different domain               same shadow)
w2/w7/w8 (no local List decl at all)     `$take`/ctor `Cons`/annotation `List Int`  loud, distinct
                                          with ZERO `data List[ a]` anywhere in      errors at each
                                          scope                                     stage (§2)
```

**The headline finding**: candidate (c) below — adding `data List a = Nil | Cons(a, List a)` to
the UNCONDITIONAL `genericPrelude` bucket, exactly where `Option`/`Result` already live
(`Bang/Frontend/TypeCheck.lean:4417`, `genericPrelude`) — is **not actually blocked by any
correctness gap**. ADR-0099's B012 (w4) and ADR-0098 D4's type-name shadow (w10, generalizing the
existing `Option`/`Result` precedent to `List`) together already give it a sound landing: same-name
user types shadow for free, differently-named-but-colliding-ctor types get a loud, actionable
error, and differently-named-non-colliding types coexist silently. **ADR-0103's Implementation
note says this was "tried and reverted"** — but that attempt predates ADR-0099 (constructor
namespacing, landed the same day) and predates today's witnessed confirmation that the shadow
mechanism is arity-agnostic (w10, a fact not established in either landing ADR). The revert's
stated reason ("collide with SEVERAL pre-existing corpus fixtures") is the pre-ADR-0099 wall, now
dissolved for the type-name-shadow case and downgraded to a loud, local, one-line fix for the
bare-ctor-collision case. This is a genuine, machine-checked correction to ADR-0103's framing, not
a rediscovery of an already-closed question.

## 2. The three-layer wall a naive user hits with zero `data List` in scope

Even once B012 makes injection SAFE, injection alone does not automatically make `$take`
zero-declaration-cost. Three sequential, DISTINCT failure modes were found probing this (each its
own witness, distinguishing which layer is missing matters for scoping the fix):

```
layer        witness   symptom                                              cause
──────────────────────────────────────────────────────────────────────────────────────────────
1. mention   w7        "'Prelude_take': a use leaves a type variable         monoCallSpine can't
   discovery           unresolved — annotate the argument"                   discover an instantiation
                                                                              with no annotation present
2. type      w8        "unknown generic type 'List'" (even WITH the          `List` was never
   resolution          annotation `(... : List Int)`)                       DECLARED anywhere in
                                                                              scope — the annotation
                                                                              names a type that
                                                                              doesn't exist
3. mention-  (design,  a program whose ONLY `List` reference is inside a     `.annotS e _` DISCARDS
   filter    not       type ascription (`let rec f : List a -> Int = ...`)   its Ty argument
   blindness runnable  never even reaches layer 2 — `injectPrelude` never    (surfUsesVar,
             w/o edit) merges `List` in at all, so `List` genuinely doesn't  TypeCheck.lean:5016)
                       exist in scope, EVEN IF the prelude declares it
                       unconditionally in genericPrelude — wait, no: an
                       UNCONDITIONAL injection (genericPrelude bucket)
                       does NOT depend on the mention filter at all, so
                       layer 3 only matters for a MENTION-FILTERED design
```

Layer 3 is the crux distinction between the two live candidate designs (§3): an *unconditional*
injection (genericPrelude bucket, like `Option`/`Result`) sidesteps the mention-filter-blindness
question entirely, because it never consults `progUsesVar` in the first place — `List`/`Nil`/`Cons`
are simply always in `env.ctors`, the same way `None`/`Some` always are today. A
*mention-filtered* injection (the `Prelude.bang` `pub` mechanism `take`/`drop` already ride) would
need the type-scan fix layer 3 names, OR would need `List` split out into its own always-injected
bucket while `take`/`drop`/`length` stay mention-filtered — which is exactly what §3 below designs.

## 3. The candidate designs, priced

```
design                 mechanism                          cost                           verdict
──────────────────────────────────────────────────────────────────────────────────────────────────
(c) unconditional       add `List a = Nil|Cons(a,List a)`  ~1 letC fuel step EVERY         RECOMMENDED
    genericPrelude      to `genericPrelude`                program pays (genericPrelude   (see below)
    bucket                                                 is unconditional — same cost
                                                             model `Option`/`Result` already
                                                             impose today, D3's fuel
                                                             finding was about the FILTERED
                                                             `pub let` bucket, not this one)
(f) type-scan the       extend `surfUsesVar`'s `.annotS`   correctness-neutral (adds       VIABLE,
    mention-filter       arm to also walk the Ty's          detection, never removes it)   NOT preferred
    (fix layer 3)        `.tName`/`.tApp` head names         but couples List's injection    (over (c))
                          into the mention set                to the SAME fuel-cost
                                                              tradeoff ADR-0098 D3 already
                                                              fought once (mention-filter
                                                              exists BECAUSE unconditional
                                                              was too expensive for the
                                                              pub-let bucket) — reintroduces
                                                              that tension for a type
                                                              nobody asked to keep costly
(g) namespaced           ship as `Prelude_List`/            defeats the entire point —      REJECTED
    `Prelude.List`,       `Prelude_Nil`/`Prelude_Cons`,      #105's ask is exactly a BARE
    no bare names         never bare, forcing every          `Cons(h,t)`-shaped ergonomic
                          consumer to qualify                list, matching every peer
                                                              language's list literal
                                                              ergonomics (stdlib-prelude-
                                                              survey.md §1, 10/10 universal)
(h) no injection —       status quo: `take`/`drop`/          zero implementation cost,      REJECTED as
    keep requiring        `length` stay generic, work         zero corpus risk — but         the terminus
    user decls            only against a user's OWN List      leaves #105's "9-10/10          (viable as
                                                               universal, every list           the FALLBACK
                                                               program wants it" demand        if (c) proves
                                                               entirely unmet for the           to regress
                                                               zero-declaration case             something (c)
                                                                                                  §1 missed)
```

**Why (c) over (f).** Both dissolve the same problem (a zero-declaration `$take`/`$length` call).
(f) reaches it by making the mention-filter SEE type-only references, which is real, general
machinery useful beyond `List` (any future generic prelude entry referenced only by ascription
would benefit) — but it inherits the exact fuel-cost fight ADR-0098 D3 already had and resolved:
the mention filter EXISTS to avoid taxing every program ~21 fuel steps for prelude entries it never
uses. Extending it to type positions doesn't remove that tension, it just relocates where the
scan happens. (c) instead recognizes that `List a` is not actually the same KIND of prelude entry
as `take`/`length` — it's a **foundational data type** (like `Option`/`Result`/`Char`/`Str`), not a
**derived function** — and ADR-0098 D5 already drew exactly this line for `Option`/`Result`/`Char`/
`Str`, keeping them in the unconditional bucket precisely because they're "foundational to how
literals parse" / "referenced by the prelude's own elaboration." `List a` fits the same
description once `take`/`drop`/`length` need it foundationally. (c) is not a new mechanism — it is
applying an EXISTING, already-adopted decision (D5's foundational-vs-derived split) to a type that
was mistakenly left out of it.

**The one-time fuel cost (c) imposes.** ADR-0098 D3 measured the unconditional-bucket cost
precisely for `Option`/`Result`: it is already paid by every program today (2 ctors × 2 types,
`None`/`Some`/`Err`/`Ok` always registered) and D3's own finding was specifically about the
FILTERED `pub let` bucket's fuel (one `letC` per mentioned NAME, not per DATA TYPE — registering a
`data` decl in `env.ctors` costs zero runtime fuel; only WRAPPING a body in an extra `let` for a
`pub let`/`pub let rec` value costs a step). Adding `data List a` to `genericPrelude` costs
**zero additional runtime fuel** for programs that never construct/match a `List` — `buildEnv`
registering an unused ctor is a pure elaboration-time table entry, not a `Config.run` step. This is
confirmed structurally by `Bang/Core/Semantics/Eval.lean`'s `Config.run` (cited in ADR-0098 D3):
fuel decrements per `Source.step`, and a `data` declaration produces no `Source` term at all — only
`pub let`/`pub let rec` VALUES produce the `letC` wrapper D3 was measuring.

## 4. `length`'s fuel tax (#120/#105's other named residue)

Witnessed (w6, w12): D4's per-name shadow gives the CORRECT VALUE for a user's own `length`,
regardless of domain (`Int`, `Str`). The residue is narrower than "shadowing is broken" — it is
that **`progUsesVar "length"` is a syntactic over-approximation with no way to know the user's
`length` is unrelated to the prelude's**, so `injectPrelude` still merges `Prelude_length`'s
qualified decl and wraps the body in its `letC`, even though the merged decl is dead (shadowed,
never referenced). Every corpus `#guard` with its own `length` pays one extra fuel step it doesn't
need — at the corpus's TIGHTEST budgets (ADR-0103 cites "fuel=20... fuel=60"), one step is enough
to flip a `#guard`'s expected outcome from `.done v` to `.outOfFuel`.

Two independent fixes, NOT mutually exclusive:
1. **Rename the prelude entry** (`length` → e.g. `listLength`, mirroring how `Str`'s own length
   helper is spelled distinctly per-domain in the corpus already — `Bang/Frontend/
   TypeCheck.lean:6639`'s Str-length helper is locally named `length` too, so this is genuinely a
   two-namespace collision, not just corpus noise). Zero mechanism change, a naming decision —
   operator call.
2. **A fuel sweep**: bump the handful of tight-budget `#guard`s that would flip, by exactly the
   fuel `injectPrelude`'s extra `letC` costs (empirically 1 step per mentioned-but-shadowed name).
   Mechanical, but touches the corpus (the contract) — needs the SAME regression discipline as any
   `#guard` change (expectations computed from `Source.eval`, per this repo's constraint).

**Recommendation: (1) first.** A rename is strictly cheaper (zero corpus touch) and dissolves the
SAME wall this note's other findings don't require the corpus to be renamed for. The fuel-sweep
path stays as the fallback if the operator wants `length` to be the literal prelude spelling
despite the collision.

## 5. Recommended design (ADR-input)

**Ship `data List a = Nil | Cons(a, List a)` in the unconditional `genericPrelude` bucket**
(`Bang/Frontend/TypeCheck.lean:4417`, alongside `Char`/`Str`/`Option`/`Result`), NOT the
mention-filtered `Prelude.bang` module. This:

- Requires **zero new mechanism** — ADR-0099's B012 (landed, machine-verified) and ADR-0098 D4's
  type-name shadow (landed, now witnessed arity-agnostic, w10) already make it sound.
- Costs **zero runtime fuel** for programs that never touch `List` (data registration, not a
  `letC`-wrapped value).
- Makes `take`/`drop`/`length`'s existing `Prelude.bang` bodies work **with zero user declaration**
  — the `Prelude.bang` entries stay mention-filtered exactly as today (D2/D3 unchanged); only the
  underlying TYPE they consume moves to the always-available bucket, matching `Option a`'s own
  split (the `Option` type is unconditional; `mapOption`/`withDefault` are mention-filtered
  `Prelude.bang` entries operating over it) — **`List` should ride the identical two-tier pattern
  the codebase already uses for `Option`**, not a new pattern invented for this ADR.
- Composes with (e)'s fix independently (rename `length`, or sweep fuel) — orthogonal axes.

**Sequencing**: land `List a` in `genericPrelude` FIRST (unblocks zero-declaration `take`/`drop` +
any future List-family entry immediately, `length` excepted until its own name resolves), rename
`length` (or sweep) SECOND. Corpus regression net: every existing program with its own
`data List`/`data IntList`-shaped type must be re-run against the real binary once `List a` enters
scope (this note's w3/w4/w9/w11 are exactly that regression shape, pre-verified) — the ONLY
programs that need a source change are ones with a BARE-ctor-name collision against a
DIFFERENTLY-NAMED type (ADR-0099's migration story, §3 of that ADR, already priced as "strictly
local, mechanical, named by the error itself").

## 6. What was explicitly NOT re-opened

Per this repo's "grep docs/decisions/ first" discipline: ADR-0099's resolution rules, B012's
message shape, the `Type_Ctor` qualified-form convention, and ADR-0098's embed/auto-use/D4-shadow
mechanics are **treated as settled inputs**, not redesigned here. This note's only original
contribution is §3's genericPrelude-bucket placement decision (a scoping question ADR-0099/ADR-0098
individually didn't answer, because `List` didn't exist as a prelude type when either landed) and
§4's fuel-tax framing (naming ADR-0103's deferred residue precisely, without designing its fix in
new mechanism — a rename is not a design, it's an operator call).

## 7. Witness index

All under `scratch/listdecl/`, run via `.lake/build/bin/bang run <file>` against a clean
`lake build bang` on this branch (`design-listdecl-injection`):

```
w1-take-own-list.bang                  w7-take-called-no-decl.bang
w3-collision-intlist-vs-list.bang      w8-take-called-annotated-no-decl.bang
w4-collision-bare-ctor-clash.bang      w9-samename-different-shape.bang
w5-take-no-local-list.bang             w10-option-arity-shadow.bang
w6-length-collision.bang               w11-mapoption-plus-monolist.bang
                                        w12-str-length-shadow.bang
```

## References

`gh issue view 105`, `gh issue view 120` (both consulted in full incl. comments);
`docs/notes/stdlib-prelude-survey.md` §2–3; `docs/decisions/0098-prelude-module-auto-use.md`
(D2–D5); `docs/decisions/0099-ctor-namespacing.md` (§1–3, §5 witnesses w0–w3); `docs/decisions/
0103-forall-generalization.md` (Implementation note, the two residual gaps); `Bang/Frontend/
TypeCheck.lean:4417` (`genericPrelude`), `:5012` (`surfUsesVar`), `:5133` (`progUsesVar`),
`:5231` (`injectPrelude`), `:2695` (`resolveCtor`), `:5525-5526` (the `declared.contains`
type-name shadow filter); `Bang/Frontend/Surface.lean:129-161` (`Ty`/`TyArgs`, what a type-scan
fix would walk); `Prelude.bang` (current `take`/`drop` bodies, the ADR-0103 payoff this note
extends).
