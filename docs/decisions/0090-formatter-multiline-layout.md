# ADR-0090 · #58 formatter multi-line layout — ride Lean's `Std.Format` Wadler engine, zero-config

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The v1 canonical formatter (`Bang/Frontend/Format.lean`, #58) is FLAT (single-line): it prints one deterministic line per `Surf`/`Ty`/`Decl`/`Prog`, with minimal-parenthesization driven by the shared `opInfo` precedence table (ADR-0071) and two corpus `#guard` laws (`roundTripsOn` = the AST never changes; `idempotentOn` = fmt-of-fmt is a no-op). Multi-line/wrapped layout was left open. This ADR settles HOW multi-line layout is added. **Decision: build the layout on Lean's host `Std.Format` — a Wadler Doc algebra (`group`/`nest`/`line`/`align`/`fill`, `pretty (width := 120)`) already in the toolchain — rather than hand-roll a second Wadler kernel (option B) or adopt the Final Pretty Printer's extensible-monadic architecture (option C, whose novelty — proportional fonts, interactive presentations, Web — is orthogonal to bang's monospace-`.bang`-file target). The printer stays ZERO-CONFIG (one fixed width constant, no user knobs — the gofmt/dart_style/black consensus, and the generative constraint that gives a canonical formatter its whole value). The two existing laws EXTEND unchanged: `roundTripsOn`/`idempotentOn` are stated over the parsed `Prog`, independent of whether the printed text is one line or many, so multi-line output must still satisfy both #guards. `examples/` are NOT reformatted by this ADR (the corpus's teaching role — hand-written idiomatic style — is preserved; a corpus entry is verbatim source, and reformatting it would destroy the very variety the round-trip #guards exercise). CLI `-w`/in-place is DEFERRED to a follow-up (the #58 CLI half wires `bang fmt` to stdout first).** Rejected: (B) hand-rolled Wadler kernel — a second layout engine beside `Std.Format`, violating one-construct-per-problem, buying `#guard`-able Doc laws bang doesn't need on a fan-in-0 leaf; (C) Final Pretty Printer — pays for extensibility bang's target makes moot; (biparsers/FliPpr, rung 3) — solve EXACT printing (recover source text), the deliberate opposite of bang's CANONICAL printing, at the cost of a full Pratt-parser rewrite. Layout engine is the recommendation; the width VALUE (survey recommends 80/2-space) is a preference the operator rules.
- **Depends-on**: 0046, 0071
- **Relates-to**: 0026 (the stratification seam this rides), #58, #30 (the Pratt-rule-table refactor the parser side tracks), #14 (the fuzz generator that could property-test the laws)

## Status

Accepted (2026-07-09, operator ruling: "Accept all, 100"). The multi-line layout rung of #58 is
DESIGNED but not built; this ADR is the research-grounded design input (survey:
`docs/notes/formatting-survey.md`). **Width VALUE ruled by the operator: `defWidth := 100`,
`indent := 2`** — the middle path between the survey's 80 (diff-pane classic) and Lean's
host-default 120; per D-zero-config it is a fixed module constant, never a knob.

## Context

The v1 formatter shipped FLAT deliberately (`Format.lean` module header, 2026-07-09 operator ruling):

- **Why flat first.** Every `examples/*/main.bang` today is either one line or a *hand-wrapped*
  multi-line style with **no consistent convention** (`parser-combinators` column-aligns `let`s,
  `tokenizer` wraps long match arms, `state` is one line). There is no majority multi-line house
  style to ride yet, and a flat printer is the form whose laws are cheapest to make watertight:
  minimal-parenthesization from the SAME `opInfo` table the parser consults (ADR-0071) is exactly
  what the round-trip #guard tests.
- **The two laws** (`Format.lean` §6-7), stated over the parsed `Prog`:
  - `roundTripsOn s` : `parseProg (fmt (parseProg s)) = parseProg s` — formatting never changes the AST.
  - `idempotentOn s` : `fmt (fmt s) = fmt s` — a formatted program is a fixpoint.
- **The seam.** `Format.lean` is a LEAF (`Bang/Frontend/*`, fan-in 0 from the verified spine — the
  arch-check invariant): it reads `Surf`/`Ty`/`Decl`/`Prog` and emits strings, no kernel/typing-rule
  change. Its correctness contract is the *tested* round-trip law, not a proof — the tested-superset
  side of the stratification seam (ADR-0026).

**What multi-line adds:** the flat printer emits `let x = e in b` on one line however long `e`/`b`
grow. Multi-line layout must decide *where* to break and indent — a layout-engine problem the
pretty-printing literature has solved since Oppen '80 / Wadler '03. The research pass
(`docs/notes/formatting-survey.md`) surveyed three engine choices and the exact-vs-canonical axis.
This ADR records the decision the survey feeds.

**The one hard constraint the survey surfaced:** the two operator-supplied papers (biparsers,
Final Pretty Printer) REFUTE nothing in the v1 design — biparsers target *exact* printing (the
opposite of bang's canonical printing), and the FPP's layout core is plain Wadler with its novelty in
axes bang doesn't touch. So multi-line is a *layout-engine* choice, not a redesign of the printer's
contract.

## Decision

### D1 — Layout engine: ride Lean's `Std.Format` (Wadler Doc algebra)

Build multi-line layout by mapping `Surf`/`Ty`/`Decl`/`Prog` to `Std.Format` documents and rendering
with `Std.Format.pretty`. `Std.Format` (`Init/Data/Format/Basic.lean`) is self-documented as "based
on Wadler's *A Prettier Printer*" and carries exactly the Doc constructors: `nil`/`line`/`align`/
`text`/`nest`/`append`/`group` (with `FlattenBehavior.allOrNone` = Wadler group, `fill` = Hughes
fill)/`tag`, plus `pretty (width := defWidth)`, `defWidth := 120`, `defIndent := 2`.

The current string-building printer becomes a `Surf → Std.Format.Format` builder; the leaf's public
entry points (`fmtExpr`/`fmtProg`) render that document to a `String` via `pretty`. The
minimal-parenthesization logic (`parenIf`/`sParenIf`, driven by `opInfo`) is UNCHANGED — it decides
parens; `Std.Format` decides breaks. The two concerns compose: parens are `text`, breaks are
`group`/`line`.

Rationale: bang already depends on Lean, so this adds ZERO new layout kernel (one-construct-per-problem;
rides-the-host-convention). Options B and C re-implement an engine the toolchain already ships (§D5).

### D2 — Where multi-line breaks canonically go

The Surf nodes that `group`/`nest` (break-and-indent when they don't fit), in the canonical style:

| Node | Canonical multi-line shape |
|---|---|
| `let x = e in b` / `let rec` / `let (a,b) = p in b` | break before `in`; the body `b` at the base indent (not nested) — the corpus's dominant `let … in`-chain-is-a-sequence idiom |
| `fun x => b` | break after `=>`, body nested +2 |
| `if c then t else e` | break before `then`/`else`, arms nested +2 |
| `match s { arms }` / `match s { c -> e, … }` (`matchD`) | break after `{`, one arm per line nested +2, `}` at base |
| `data`/`trait`/`impl` bodies | one ctor/op/clause per line when the decl doesn't fit, `|`/`;` at line starts |
| application `f a b`, binops | `group` the whole spine; break at argument boundaries only when over width (Hughes `fill` for argument lists) |
| tuples `(a, b)`, ctor calls `C(a, b)` | `group`; break after commas when over width |

The exact break points are a `group`/`nest` placement detail; D2 fixes the *canonical intent* (which
nodes are groups, where nesting increments). Because it is canonical, the shape is a pure function of
the AST — no input-format influence (ADR-0046).

### D3 — Width: one fixed constant, ZERO user knobs

The printer takes NO width option from the user. One module-level constant governs all rendering.
**RULED value (operator, 2026-07-09): 100 columns, `indent := 2`.** The survey's recommendation
was: **80 columns, `indent := 2`** (terminal/diff-friendly, the gofmt/dart_style/black
classic; more conservative than Lean's editor-oriented `defWidth := 120`). This VALUE is the
operator's preference call; the DECISION is that it is a fixed constant, not a knob (survey §4:
zero-config is the generative constraint that gives a canonical formatter its value — every knob
reintroduces the style entropy the formatter exists to delete).

### D4 — The two laws extend unchanged

`roundTripsOn`/`idempotentOn` are stated over the parsed `Prog` (`Format.lean` §6), NOT over the
printed text's line structure. So they are AGNOSTIC to flat-vs-multi-line: multi-line output must
still (a) re-parse to the same AST (`roundTripsOn`) and (b) be a fixpoint of `fmt` (`idempotentOn`).
The corpus `#guard`s (§7) carry over verbatim and must stay green; multi-line output that broke either
law would be a parser/printer disagreement — a FINDING, per the operator's standing ruling, not a
style nit. `idempotentOn` in particular becomes *more* load-bearing: a break-decision that depended
on the input's existing line breaks would violate it (the second `fmt` would see different text),
which is precisely the guard that keeps multi-line CANONICAL (breaks are a function of width + AST
only). **New corpus entries** should include programs long enough to actually trigger breaks (the v1
corpus is short-line; add a wide `match`/`let`-chain that exceeds the width constant), so the #guards
exercise the multi-line paths, not just re-confirm the flat ones.

### D5 — Considered options (rejected, with rationale)

**(B) Hand-rolled Wadler kernel.** A bang-local `Doc` inductive + `group`/`nest`/`flatten`/`ifFlat`
+ a fitting function, with `#guard`-able Wadler laws.
- *Why it's tempting:* bang could `#guard` the Doc laws directly (Wadler '03 gives them; the FPP
  proves them for any monad, Lemmas 7.1-7.4), keeping the layout engine inside the tested boundary.
- *Rejected because:* it stands up a SECOND Wadler engine beside `Std.Format` — the exact
  one-construct-per-problem violation the project forbids. The law-checkability it buys is wasted on a
  fan-in-0 leaf whose contract is the round-trip #guard, not a Doc-law proof. The verified spine never
  imports the layout engine either way (ADR-0026 seam), so re-proving Wadler's laws in bang buys
  nothing the host's tested impl doesn't already give.

**(C) Final Pretty Printer architecture** (`christiansen-darais-ma-final-pretty-printer`). MonadPretty
finally-tagless, extensible via monad transformers.
- *Why it's tempting:* correctness "derived solely from the laws governing standard FP abstractions"
  (§7); genuinely elegant extensibility.
- *Rejected because:* its value is in axes bang doesn't touch — proportional fonts (bang: monospace),
  interactive presentations (bang: a `.bang` text file), Web rendering, semantic annotations
  (`Std.Format.tag` already covers the last if ever needed). Its §5.2 precedence-environment `atLevel`
  (conditional parens per an env level) is EXACTLY what bang's `parenIf`/`sParenIf` already do
  structurally — bang has the one FPP extension that matters, without the monad stack. Paying for the
  rest is speculative complexity (invariant #7: no speculative machinery).

**(rung 3: biparsers / FliPpr / invertible syntax)** — make round-trip UNREPRESENTABLE by fusing
parser and printer into one artifact.
- *Why it's the "name the right answer first" candidate:* it is the top of the derivation ladder —
  drift between parser and printer becomes structurally impossible, not merely tested.
- *Rejected because:* (1) it requires a full Pratt-parser rewrite into the bidirectional DSL — a
  frontend rewrite for a leaf module; (2) it solves the WRONG problem — biparsers (Xie '25 §1-2)
  exist for *exact* printing, recovering whitespace/comments/format-variants via a complement, the
  deliberate OPPOSITE of bang's canonical printing (which destroys that information by design,
  ADR-0046). bang's canonical printer is already the degenerate biparser with a `Unit` complement, and
  its `roundTripsOn` #guard IS the biparser PrintParse law — so bang instantiates the useful corner of
  the framework without the rewrite. Named, and rejected for v1, with the cost stated. (Survey §2.)

### D6 — Corpus reformatting: NO

This ADR does NOT reformat `examples/*/main.bang`. A corpus entry is VERBATIM source that the
round-trip `#guard`s parse and re-print; its teaching role is to be *idiomatic hand-written* bang
across varied styles (the very variety that exercises `roundTripsOn`). Reformatting the corpus to the
canonical style would (a) destroy that variety, collapsing the #guards to trivially-canonical inputs,
and (b) couple the corpus (test fixtures) to the formatter (thing under test), so a formatter bug
could no longer be caught by a corpus that already matches its output. The corpus stays hand-written;
the formatter is tested AGAINST it, never rewrites it. (A separate `bang fmt`-the-examples convenience,
if ever wanted, is a tooling command, not a corpus change — deferred.)

### D7 — CLI `-w` / in-place: DEFERRED

The #58 CLI half (`bang fmt`, already wired to `fmtExpr`/`fmtProg`) writes to stdout. In-place
rewrite (`bang fmt -w file.bang`) and width-flag (`-w N`) are DEFERRED to a follow-up:
- in-place is an IO/filesystem concern (read → format → write-back) with its own fail-loud discipline
  (never write on a parse error — the same `Except` the entry points already return), orthogonal to
  the layout engine;
- a width *flag* would REINTRODUCE the config knob D3 rejects — if a width flag is ever added it needs
  its own justification against the zero-config decision, so it is explicitly out of scope here.

## Invariant compliance

- **#1 (proof rides the reference):** the formatter is a leaf; its oracle is the tested round-trip law
  (`roundTripsOn` against `parseProg`), unchanged by multi-line (D4). `Std.Format.pretty` is host
  code on the tested-superset side of the ADR-0026 seam — the verified kernel never imports it.
- **#5 (kernel stays at five primitives):** no kernel change; `Format.lean` reads `Surf`/`Core.IR`
  and emits strings. Confirmed leaf (fan-in 0), arch-check clean.
- **#7 (performance is second-class):** `Std.Format.pretty` is `O(nw)`, identical asymptotics to a
  hand-rolled Wadler/FPP engine; bang formats small programs. No engine chosen for speed.
- **ADR-0046 (deterministic-or-loud):** breaks are a pure function of width + AST (D2, D3); parse
  failure still yields the same loud `Except` error the flat printer gives (`fmtExpr`/`fmtProg`
  unchanged). Canonical printing = one output per AST is preserved by D2/D6.
- **ADR-0071 (shared `opInfo`):** minimal-parenthesization stays driven by the parser's precedence
  table; `Std.Format` composes with it (parens are `text`, breaks are `group`/`line`) — the
  single-source-of-truth for precedence is untouched.

## Revisit-if

- **The corpus grows a majority multi-line house style** that `Std.Format`'s greedy `group`/`fill`
  can't express (e.g. Bernardy-style *optimal* fewest-lines-narrowest layout) → revisit the engine
  (Bernardy '17 is the optimal-layout upgrade path; still rides a Doc algebra, so it's an engine swap,
  not an architecture change).
- **The Pratt-parser #30 refactor lands and makes a biparser rewrite cheap** → re-evaluate rung 3
  (bidirectional) — the cost that rejects it today is the parser rewrite; if #30 pays that down, the
  exact-vs-canonical mismatch (D5) is the *remaining* reason, which stands regardless.
- **`Std.Format`'s API changes across a Lean toolchain bump** → the leaf breaks loudly at build; pin
  the behaviour with the corpus #guards (they already gate the rendered strings).

## Evidence

- Survey: `docs/notes/formatting-survey.md` — the three-rung map, exact-vs-canonical analysis, the
  engine comparison (§3), zero-config corpus (§4).
- Host engine: `Std.Format` in `Init/Data/Format/Basic.lean` (Lean toolchain) — Wadler Doc algebra,
  `pretty (width := 120)`, `defIndent := 2`; self-cited to Wadler's *A Prettier Printer*.
- Papers: `xie-popl25-biparsers-exact-printing` (POPL 2025, exact-printing lens+complement, the
  PrintParse law bang instantiates), `christiansen-darais-ma-final-pretty-printer` (extensible
  effectful pretty printing, Wadler layout core + orthogonal novelty). Both in `references/refs.bib`.
- Current formatter: `Bang/Frontend/Format.lean` — the flat v1 printer, `opInfo`-mirrored
  parenthesization (§2-3), the two laws + corpus `#guard`s (§6-7) this ADR extends unchanged.
