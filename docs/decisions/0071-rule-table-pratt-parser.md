# ADR-0071 · Rule-table Pratt parser — reify the grammar so parser · spec · tree-sitter generate from one root

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Adopt the Cheng-Parreaux (ECOOP'26) rule-table Pratt architecture for the surface parser: reify operator precedence as binding-power DATA and keyword-led constructs as first-class parsing RULES, so one Pratt-shaped loop consults the reified rules — and the SAME rule values generate the grammar spec (railroad + precedence table) and the tree-sitter grammar. Staged: (①) replace the fixed 4-level precedence chain with one binding-power loop over a reified operator table; (②) reify keyword-led rules; (③) generate the `language.md` grammar section (#38); (④) whitespace-insensitivity + `bang fmt` (Q24) fall out. The parser stays TOTAL (fuel-driven) so demo `#guard`s reduce under `rfl`.
- **Resolves**: the #30 parser-architecture decision (constrains #38 generated-grammar · #9 tree-sitter; unblocks the whitespace-insensitivity precondition — see the staging table; not itself a deferred-question resolution)
- **Depends-on**: 0068, 0069, 0070

- **Status:** Accepted (2026-07-05)
- **Date:** 2026-07-05
- **Layer:** C (surface — the concrete-syntax engine; no kernel change)
- **Builds on:** ADR-0068/0069/0070 (the decl prelude + data + named-cap grammar the rules must cover).
- **Reference:** Cheng & Parreaux, *A Simple Recipe for Writing Decent Recursive Descent Parsers*
  (ECOOP'26, `references/papers/adjacent/cheng-parreaux-ecoop26-parsing.pdf`; bib
  `cheng-parreaux-ecoop26-parsing`). The `Add x y` binding-power calculation (Fig. 1) is the direct
  template for stage ①; the first-class `Rule`/`Choice` representation (§3) for stage ②.

## Context

The surface parser (`Bang/Frontend/Surface.lean`) is hand-rolled recursive descent with a FIXED
precedence chain — `pExpr → pImp → pCompare → pAddSub → pMulDiv → pApp → pDotted → pAtom` — plus
keyword arms in `pExpr` and the decl parsers. Two problems, one use-attested:

- **The grammar is code-only** — there is no independent statement, so it drifts from any spec and
  has unstated corners (#31 bare atoms). A hand-written grammar section would be a second copy of the
  truth (SSoT violation).
- **Papercuts (dogfooding, 2026-07-05):** whitespace-sensitivity dominates (`x=1`, `->Self`, `a+b`
  glue into single tokens — every early failure was this); `match <ctor-app>` needs parens (the
  scrutinee must be atomic). Both trace to the ad-hoc hand-rolled structure.

## Decision

1. **Reify the operator table as binding-power DATA** and drive precedence with ONE Pratt loop
   (`parse(minBP)`: parse an application-operand, then `while nextOp.leftBP > minBP: consume;
   rhs = parse(nextOp.rightBP); fold`). This replaces `pImp/pCompare/pAddSub/pMulDiv` with a table +
   a loop. Binding powers per the paper's convention (left-assoc: leftBP < rightBP; right-assoc:
   leftBP > rightBP): `=>` (right, loosest) · `< ==` · `+ -` · `* /` · application (tightest) ·
   `.`-postfix (tighter than application).
2. **Reify keyword-led constructs as first-class `Rule`s** (§3 of the paper: a `Rule` is a list of
   `Choice`s — `Keyword kw rest` / `Ref kind bp rest` / `End value`). `if`/`let`/`match`/`with`/`do`
   become rule VALUES the same loop consults, not bespoke `pExpr` arms.
3. **Generate from the table**: a `gen-reference.py` leg renders the grammar section of
   `docs/reference/language.md` (precedence table + railroad-style diagrams) FROM the reified rules —
   parser behavior and grammar spec share one root, drift unrepresentable (#38). The tree-sitter
   grammar (#9) generates from the same table.
4. **The parser stays TOTAL** — fuel-driven structural recursion, never `partial` — so the demo
   `example`/`#guard`s reduce under `rfl` (the existing discipline; a `partial def` is opaque to the
   kernel's definitional unfolding). The rule-table loop is fuel-bounded like the current descent.

## Staging (each stage regression-gated by the existing `parsesTo` guards)

```
① operator layer   reified op-table + one Pratt loop replaces the 4-level chain.
                   GATE: every existing `parsesTo`/`runYieldsInt` guard passes UNCHANGED
                   (the structural parse trees are pinned — this is a behaviour-preserving refactor).
② keyword rules    if/let/match/with/do reified as Rules; the bespoke pExpr arms retire.
③ grammar spec     gen-reference.py grammar leg from the rules (closes #38).
④ whitespace + fmt whitespace-insensitive tokenizer + `bang fmt` canonical form (Q24) — now cheap.
```

Stage ① is the self-contained core and the safest first unit: it is a pure refactor (identical
output), it fixes the precedence-quirk papercuts, and the `parsesTo` corpus is the regression oracle.

## Rejected alternatives

- **Keep hand-rolling.** Drifts from any spec, keeps the papercuts, and each new construct is another
  bespoke arm. The dogfooding evidence (comment on #30) is the case against.
- **A parser generator (Yacc/ANTLR/Menhir).** The paper's thesis — and industrial practice — is that
  hand-written-but-principled recursive descent beats generators for real compilers (better errors,
  debuggability). And bang specifically needs TOTAL fuel-driven recursion for `#guard` reducibility,
  which a generator's runtime doesn't give.
- **A separate hand-written grammar doc.** A second copy of the truth (SSoT violation) — the whole
  point of the rule table is that the grammar is GENERATED from the parser's own rules.

## Consequences

- `#30` becomes a staged, regression-gated refactor rather than a rewrite-and-pray.
- `#38` (generated grammar), `#9` (tree-sitter), Q24 (whitespace + `bang fmt`), and #31 (bare atoms,
  fixed by construction when "what starts a program" is an explicit rule) all fall downstream of one
  root.
- The dogfooding papercuts (whitespace, atomic-scrutinee) are addressed at ① and ④.

## Revisit if

- The reified-rule representation forces a parse-tree change that breaks a `parsesTo` guard — that is
  the signal a construct's grammar is genuinely changing (relitigate that construct, not the ADR).
- Recursion / `fix` lands — its grammar becomes a new Rule, not a new bespoke arm.
