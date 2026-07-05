# ADR-0072 · Named-capability syntax: drop `with`, fold the binder into the effect forms (`state 5 as h in e`)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Revise the named-capability surface syntax from ADR-0070's `with <kind> as h in b` to an optional `as <ident>` binder on the EXISTING per-effect forms: `state <init> [as h] in <body>` · `handle [as h] <body>` · `atomically [as h] <body>`. The `with` keyword is removed. Reads more naturally (the awkward two-keyword run-on becomes a binder on a form the user already knows) AND is grammar-regular (it folds into the already-reified `state`/`handle`/`atomically` rules instead of a bespoke keyword-pair construct — dissolving the hardest ②b case, ADR-0071). Surface-only: identical lowering, no kernel/semantics/proof/AST change.
- **Amends**: 0070
- **Depends-on**: 0070, 0071

- **Status:** Accepted (operator-requested 2026-07-05)
- **Date:** 2026-07-05
- **Layer:** C (surface concrete syntax — no kernel/lowering impact)
- **Builds on:** ADR-0070 (named capabilities — this revises only their SPELLING; the semantics,
  the `Cap ℓ` typing, identity dispatch, and the `h.op` perform syntax are unchanged). ADR-0071
  (the parser; this dissolves its hardest bespoke construct — the ②b `with` case).

## Context

ADR-0070 spelled a named handler `with <kind> as h in b` (`with state 5 as h in e`). Two problems,
one flagged by use, one by the parser refactor — and they are the SAME problem:

1. **Reads awkwardly.** `with state 5 as h in e` crams a leading keyword, a second keyword (the
   effect kind), an init, a mid-sentence binder, and a body into one run-on. The operator flagged
   `with x as X` as strange.
2. **Hardest to parse.** It was the one construct #30/②b could not reify cleanly — it needs a
   compound key (`with`+kind), a BP-parameterized init sub-parse, and alternation. That is not a
   coincidence: awkward surface syntax and grammar-irregularity are usually the same defect.

## Decision

Named capability = an **optional `as <ident>` binder right after the effect form's head**, on the
forms that already exist. Drop `with` entirely.

```
effect        ambient (unchanged)        named (new spelling)
──────────────────────────────────────────────────────────────
state         state <init> in <body>     state <init> as <h> in <body>
throws        handle <body>              handle as <h> <body>
transaction   atomically <body>          atomically as <h> <body>
```

- The named ops are unchanged: `h.get`, `h.put(v)`, `h.raise(v)`, `h.new(v)`, `h.read(r)`,
  `h.write(r, v)`.
- Lowering is IDENTICAL to ADR-0070's: `as h` binds the capability where the sentinel binder went;
  no `as` uses the ambient sentinel. No kernel, semantics, checker-typing, or proof change — this is
  the parser emitting the same `Surf`/`withCapS` shape from a cleaner surface.
- The multi-instance demo becomes: `state 1 as a in (state 2 as b in (a.get + b.get))` — no `with`.

## Rejected / out of scope

- **Keep `with … as`** (ADR-0070) — the awkward-and-hard form; the whole point is to remove it.
- **Rename `handle` → `throws`** for consistency (ambient throws is `handle`, ambient state is
  `state` — a pre-existing keyword inconsistency). Deferred: it renames a keyword users know, a
  bigger change than this binder revision. Noted for a future regularization pass, not done here.
- **A postfix `<body> as h`** (binder after the body) — inconsistent placement across the forms;
  the after-head position (`state <init> as h`, `handle as h`) keeps `as h` uniformly right after
  what the handler is parameterized by.

## Consequences

- The bespoke `with` parser construct (ADR-0071 ②b's hardest case) is REMOVED. The named-state form
  is now the reified `state` rule + an optional `as <ident>` slot. IMPLEMENTATION NOTE for #30: this
  needs the reified rule to admit an OPTIONAL segment — a mild DSL extension (present/absent), far
  short of the alternation the old `with` needed. If the linear rule DSL can't express "optional"
  cleanly, the three affected forms (`state`/`handle`/`atomically`) may go bespoke for the binder —
  still a net simplification (no `with`, no compound key). The implementer decides; escalate if it
  forces a real DSL fork.
- Migration: update the guards + Examples that use `with … as` (mechanical, `parsesTo`/`runYieldsInt`
  corpus is the oracle) and the generated reference. ADR-0070's prose examples get the new spelling.

## Revisit if

- Multiple named instances of throws/transaction (not just state) become common — the after-`handle`
  binder position may want reconsidering for readability.
- The `handle`/`state`/`atomically` keyword regularization (the deferred rename) is taken up.
