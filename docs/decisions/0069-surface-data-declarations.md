# ADR-0069 · Surface `data` declarations — named constructors as transparent sugar over sums · products · μ

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Recursive data surfaces as `data` declarations in the Prog prelude (`data IntList = Nil | Cons(Int, IntList)`): constructors are TRANSPARENT sugar over the kernel's existing sums/products/μ (right-nested sum by decl order, k-ary product payload, uniform `fold`-wrap), aliases are STRUCTURAL not nominal (consistent with ADR-0068 keying; nominal identity deferred to #23-proper), and the feature lives on the TYPED path only (ctor intro + named match need the decl env; the untyped path fail-louds). Recursive FUNCTIONS are out of scope — a separate bullet (fix + `Div` row).
- **Resolves**: the #2 surface fork (operator-ratified: data decls direct, not anonymous-μ-first)
- **Depends-on**: 0029, 0068, 0066

- **Status:** Accepted (operator-ratified 2026-07-05: option (b) direct)
- **Date:** 2026-07-05
- **Layer:** C (surface design — the data-type UX over the verified kernel)
- **Builds on:** ADR-0029 (iso-recursive sum/prod/μ — `Val.fold`/`Comp.unfold`/`VTy.unrollMu`, the
  kernel machinery this sugars; NO kernel change). ADR-0068 (the decl prelude + typed entry point
  this rides; structural keying). ADR-0066 (the bidirectional checker that gains `fold`/`unfold`
  arms).

## Context

The kernel has had recursive data since ADR-0029 (`fold v : μX.A` ⇐ `v : A[μX.A/X]`;
`unfold (fold v) ↦ ret v`, both runtime-erased iso-coercions), and the Lean-level Stack demo uses
it — but a USER cannot write a recursive type. The anonymous spelling (`mu. Unit + (Int * #0)` for
a list) is hostile; the decl layer that named constructors need did not exist until ADR-0068's
Prog prelude. Now it does, so the surface rung is `data` declarations directly.

## Decision

1. **Syntax** — a third decl form in the Prog prelude:
   `data IntList = Nil | Cons(Int, IntList)` — constructors capitalized-by-convention (not
   enforced), payload arity 0 (`Nil`, payload `Unit`), 1, or 2 (the tuple grammar is binary;
   n-ary via nesting — a v1 bound, not a design position). Recursion is spelled by the type's
   own name in payload position.
2. **Encoding (uniform)** — N constructors ⇒ a right-nested sum in decl order
   (`c₀ + (c₁ + …)`); payload = the k-ary right-nested product (`Unit` for 0-ary); the whole
   body μ-wrapped ALWAYS (even non-recursive data) — one lowering path, no special cases.
   `IntList` ⇒ `μX. Unit + (Int × X)`.
3. **Aliases are TRANSPARENT (structural, not nominal).** A data name in type position
   (`impl Add for IntList`, ascriptions) resolves to its structural μ-type at elaboration;
   instance keying stays structural (ADR-0068 decision 2). Nominal identity — distinct types
   with equal structure — is #23-proper, deferred; it layers on top without re-encoding.
4. **Typed-path-only.** Ctor intro parses as ordinary application (`Cons(3, xs)` is
   `app (var "Cons") (pair …)` — no parser form needed); the ELABORATOR rewrites it, via the
   decl env, into the annotated `fold`/injection. Named `match` arms parse to a `matchD` node
   the elaborator desugars into the existing `unfold`+`case`+`split` chain. On the UNTYPED path
   (no decl env) these fail loud — data is a `Prog`-level feature by construction.
5. **New surface nodes are internal plumbing**: `unitS` (the unit value literal `()` — a
   standing grammar gap this fills), `foldS`/`unfoldS` (emitted by elaboration; checker arms
   mirror T_Fold/T_Unfold via the kernel's own `VTy.unrollMu`), `matchD` (parse-only, always
   eliminated by elaboration), and type formers `tName`/`tMu`/`tVar` (`tName` parsed for any
   type-position identifier, resolved against the decl env at elaboration; `tMu`/`tVar` never
   parsed in v1).

## Out of scope (deliberately)

- **Recursive functions** (`sum(xs) = match xs { … Cons(h,t) -> h + sum(t) }`) — that is
  general recursion (`fix` + the `Div` row), a SEPARATE tracer bullet. v1 demos construct and
  destruct (the Stack shape: `pop (push 7 empty) = 7`) without self-reference.
- Exhaustiveness/overlap diagnostics beyond arity+name checks (fail-loud on mismatch; quality
  messages ride #10).

## Rejected alternatives

- **Anonymous-μ-first (option a/c)** — the checker plumbing is a strict subset of this work,
  and the anonymous surface spelling serves no user; staging it separately buys nothing now
  that the decl prelude exists.
- **Nominal identity now** — needs distinct-type checker keys + the #23 decl-name discipline;
  transparency gets the northstar `Vec` spelling today and nominal layers on later.
- **Parser-level ctor syntax** — application shape already parses ctor intros for free; a
  dedicated form would duplicate the app grammar.

## Consequences

- `Vec` becomes a real named type (`data Vec = Vec(Int, Int)`), upgrading the ADR-0068
  northstar demo to its intended spelling — `impl Add for Vec`.
- The checker gains T_Fold/T_Unfold mirrors (reusing `VTy.unrollMu` — no re-derivation).
- The enumeration discipline pays for itself: every new node fails to compile in
  `synthSC`/`lowerC`/`elabS` until armed.

## Revisit if

- #23 lands nominal types (clause 3's transparency becomes the compatibility floor).
- n-ary tuples land (clause 1's arity bound lifts).
- `fix`/`Div` surfaces (the out-of-scope recursion note retires).
