<!-- note-status: active -->
# Formatting-techniques survey — the design inputs for bang's multi-line layout (#58)

> A research pass on formatting/pretty-printing techniques, commissioned BEFORE bang's
> multi-line layout is designed. The v1 FLAT formatter is landed (`Bang/Frontend/Format.lean`);
> this note maps the design space so the multi-line rung (ADR-0090) is chosen with the
> literature in view, not improvised. Companion to ADR-0090 (the decision); this is the *survey*
> (what exists, what each buys and costs FOR BANG). Established 2026-07-08.
>
> Grounding papers (in `references/`): `xie-popl25-biparsers-exact-printing` (POPL 2025),
> `christiansen-darais-ma-final-pretty-printer`, plus the Wadler/Hughes/Bernardy lineage and
> the gofmt/Prettier/dart_style practice corpus, and Lean's host `Std.Format`.

## TL;DR — the three sharpest findings

1. **The layout engine is a solved, host-provided problem.** Lean's `Std.Format`
   (`Init/Data/Format/Basic.lean`) *is* a Wadler Doc algebra — `group`/`nest`/`line`/`align`/
   `FlattenBehavior.allOrNone|fill`, `pretty (width := 120)` — self-documented as "based on
   Wadler's *A Prettier Printer*". bang already depends on Lean; hand-rolling a second Wadler
   kernel would violate one-construct-per-problem. **Ride the host.**
2. **The two operator-supplied papers REFUTE nothing in the v1 design; they confirm it.** Biparsers
   target *exact* printing (recover the original text) — the deliberate **opposite** of bang's
   *canonical* printing (destroy input format). The Final Pretty Printer's novelty (proportional
   fonts, interactive presentations, Web) is **orthogonal** to bang's monospace-`.bang`-file target;
   its *layout core* is plain Wadler.
3. **bang's `roundTripsOn` law IS the biparser PrintParse law**, and bang's canonical printer is the
   *degenerate biparser with a unit complement* (nothing to recover). So the lens framing does teach
   us something — it tells us exactly which of its two laws bang keeps (PrintParse) and which it
   deliberately drops (ParsePrint, the "recover source text" law bang has no use for).

---

## 1. The three-rung map (derivation-strength applied to formatting)

The project's derivation-strength ladder (drift **unrepresentable** > drift **caught at CI** >
drift by **convention**) recurs here. A formatter's correctness is "the printed text re-parses to
the same AST" — and the three research traditions differ in *how structurally* they guarantee it.

| Rung | Tradition | Guarantee mechanism | What it buys | What it costs FOR BANG |
|---|---|---|---|---|
| **ad-hoc + tested laws** | hand-written printer + corpus round-trip checks | drift **caught at CI** (a #guard fails) | minimal machinery; the printer is ordinary recursion over the AST | round-trip is *tested*, not structural — a shape the corpus misses can silently break |
| **Doc-algebra** | Hughes '95, Wadler '03, Oppen '80, Bernardy '17 | layout laws (`group`/`nest`/`flatten`) hold *by construction of the combinators*; width-fitting is the engine's job | multi-line layout with optimal/greedy line-breaking, indentation, all from a tiny law-abiding kernel | the *kernel*'s laws are structural; the *bang-printer over it* is still tested for round-trip |
| **invertible / bidirectional** | Rendel-Ostermann '10, FliPpr (Matsuda-Wang '18), **biparsers (Xie '25)** | parser and printer are ONE artifact (a lens / a single grammar), so round-trip is **unrepresentable-to-break** | drift *unrepresentable*: you cannot write a printer that disagrees with the parser | a full Pratt-parser rewrite into the bidirectional DSL; and it solves the *exact*-printing problem bang doesn't have |

**Where bang sits today (rung 1), with the pieces to climb:**

```
bang has                          →  which rung it enables
──────────────                       ─────────────────────
shared opInfo precedence table       rung-1 minimal-parenthesization is ALREADY law-abiding-by-
  (ADR-0071; Format.lean mirrors it)   construction: printer parens ⇔ parser precedence, one table
corpus + #guard round-trip/idem      rung-1 TESTED laws (roundTripsOn/idempotentOn, §6-7 of Format.lean)
a fuzz generator (#14)               could PROPERTY-test round-trip (rung-1.5: tested over generated
                                       ASTs, not just the fixed corpus) — the cheapest real strengthening
```

The **honest read**: bang is at rung 1 and already *exploits* a rung-1.5 structural fact for the
parenthesization sub-problem — the shared `opInfo` table (ADR-0071) means the printer's
`parenIf`/`sParenIf` decisions are a *function of the same precedence data the parser consults*, so
minimal-parenthesization can't drift from the grammar. That is the single-source-of-truth move
already banked. The corpus #guards test the rest.

### Why not climb to rung 3 (bidirectional) for v1

Rung 3 makes round-trip *unrepresentable*, which is the top of the ladder — so by "name the right
answer first" it must be named. Its real cost:

- **A Pratt-parser rewrite.** bang's parser is a Pratt rule-table (ADR-0071; the
  `cheng-parreaux-ecoop26-parsing` recipe is the planned #30 refactor). Biparsers/FliPpr replace that
  with a *combinator DSL where parser and printer are the same term*. That is a rewrite of the entire
  frontend parser, for a leaf module (`Format.lean`, fan-in 0).
- **It solves the wrong problem.** The whole point of biparsers (§1-2 of Xie '25) is *exact* printing
  — recovering whitespace/comments/format-variants via a **complement**. bang's canonical formatter
  *deliberately destroys* that information (Format.lean header, ADR-0046: "printing is
  deterministic-or-not-done"). See §2.

So rung 3 is the most-correct answer to a *different* question (source-preserving synchronisation),
and its cost (rewrite the parser) is real. **Named and rejected for v1**; the fuzz-property rung
(1.5) is the cheap real strengthening, and the Doc-algebra rung (2) is what multi-line needs.

---

## 2. Exact-printing (biparsers) vs canonical-printing — the lens still teaches, without force-fitting

This is the axis the operator flagged to analyse carefully. **bang and biparsers want opposite
things**, and saying so precisely is the finding.

| | **Exact-printing** (biparsers, FliPpr) | **Canonical-printing** (bang, gofmt) |
|---|---|---|
| Goal | recover the *original source text* after an edit | one deterministic rendering *per AST*, input format destroyed |
| Printer is a function of… | the AST **+ a complement** (whitespace, comments, chosen variant) | the AST **only** |
| Round-trip laws (Xie '25 §2.2) | **both** ParsePrint (`parse·print` recovers source) **and** PrintParse (`print·parse` recovers AST) | **only** PrintParse (bang's `roundTripsOn`) |
| Non-injectivity of parse | the *central problem* — many texts → one AST, the complement records which | a *non-problem* — bang picks one canonical text and discards the rest |
| bang's need | none (bang is not synchronising two source copies) | this is exactly bang's spec |

**What the lens framing genuinely teaches bang (not force-fit):**

- bang's canonical formatter is precisely the **degenerate biparser whose complement is `Unit`**
  (`⊤` in the paper). With no complement, ParsePrint becomes vacuous (there is no source text to
  recover — bang *generates* it), and only **PrintParse survives**. bang's `roundTripsOn` #guard
  (`parseProg (fmt (parseProg s)) = parseProg s`, Format.lean §6) **is** PrintParse for the
  unit-complement biparser. So bang's law framework is not ad-hoc — it is the trivial-complement
  corner of a published law framework.
- The paper's **PrintParse consistency conditions** for choice (`ParseConsistent`/`PrintParseConsistent`,
  §3.3) are the formal reason bang's `roundTripsOn` must hold *across every constructor case* — the
  same discipline Format.lean's per-case comments already enforce (the `.app`/ctor-call precedence
  case, the `raise`-atom-vs-`handle`-full-expr split). The paper names *why* those cases are load-bearing:
  a printer that self-parenthesizes on the wrong side of a grammar ambiguity violates PrintParse.
- The paper's **idempotence-of-canonical-form** intuition: biparsers allow the print-parse round-trip
  to return a *different* complement `c'` (§2.2) precisely when the source had multiple written forms.
  bang collapses all of those to one form — which is exactly what makes bang's *second* law,
  **`idempotentOn`** (`fmt (fmt s) = fmt s`), meaningful and provable: a canonical printer is a
  *retraction* onto its image, so formatting a formatted program is a no-op. Exact-printers have no
  such law (they preserve variety); canonical printers must have it. **This law is bang's, not the
  biparser's** — and the contrast is what explains why.

**Verdict on adopting biparsers for bang:** do **not**. Cited as the frontier definition of the
*exact*-printing problem, kept as the framework whose PrintParse law bang already instantiates. Its
adoption cost (parser rewrite) buys a capability (source-format recovery) bang's spec forbids.

---

## 3. Layout engine for multi-line — the load-bearing choice

Three candidates for the engine that decides *where newlines and indentation go*.

| Option | What it is | one-construct / rides-host | Laws | Verdict |
|---|---|---|---|---|
| **A. Lean `Std.Format`** | the host's Wadler Doc algebra: `group`/`nest`/`line`/`align`/`fill`, `pretty (width:=120)`, `defIndent:=2` (`Init/Data/Format/Basic.lean`) | **rides the host** — zero new kernel; bang already depends on Lean | Wadler's laws hold in the host impl (self-cited to *A Prettier Printer*); NOT re-proved in bang, but the layout engine is not on bang's verified spine (it's a leaf, fan-in 0) | **RECOMMENDED** |
| **B. hand-rolled Wadler kernel** | bang's own `Doc` inductive + `group`/`nest`/`flatten`/`ifFlat` + a fitting function, with `#guard`-able Wadler laws | a *second* Wadler engine beside `Std.Format` — violates one-construct-per-problem | bang could `#guard` the Doc laws (Wadler '03 gives them; the FPP proves them for *any* monad, Lemmas 7.1-7.4) | rejected — buys law-checkability bang doesn't need on a leaf, at the cost of a parallel engine |
| **C. Final Pretty Printer arch** | MonadPretty finally-tagless, extensible via monad transformers (Christiansen-Darais-Ma) | a *third* engine; its extension points (fonts/interactive/Web) are orthogonal to a `.bang` text file | correctness "derived solely from the laws governing standard FP abstractions" — elegant, but for capabilities bang lacks | rejected — pays for extensibility bang's target makes moot |

**The decisive facts:**

- **`Std.Format` is Wadler, already in the toolchain.** Its `Format` inductive carries exactly the
  Wadler/Oppen constructors (`nil`/`line`/`align`/`text`/`nest`/`append`/`group`/`tag`) with
  `FlattenBehavior.allOrNone` (Wadler group) and `fill` (Hughes fill). `pretty` picks the
  fewest-lines rendering under a width. This is the entire multi-line engine, host-provided and
  host-maintained. Choosing B or C re-implements it.
- **The FPP's own argument points at A.** The FPP *derives* its correctness from Wadler's Doc laws
  (§7) and adds value only in axes bang doesn't touch: proportional fonts (bang: monospace),
  interactive presentations (bang: a text file), Web rendering (bang: none), semantic annotations
  (`Std.Format` already has `tag` for this if ever needed). Its §5.2 precedence-environment `atLevel`
  (insert parens per an env level) is *exactly* what bang's `parenIf`/`sParenIf` do structurally
  today — bang already has the one FPP extension that would matter, without the monad stack.
- **Performance is second-class (invariant #7).** `Std.Format.pretty` is `O(nw)` worst case (same as
  Wadler/FPP); bang formats small programs. No reason to prefer B/C on speed.

**The one honest cost of A:** `Std.Format.pretty` is host code, not part of bang's verified core, and
its rendering is not re-proven in Lean. But the formatter is a **leaf** (`Bang/Frontend/*`, fan-in 0
from the verified spine — the arch-check invariant), and its correctness contract is the *tested*
round-trip law, not a proof. Depending on the host's tested Wadler engine is the same
tested-superset-over-verified-core seam the whole project runs on (the stratification principle):
the verified kernel never imports `Std.Format`; only the leaf printer does.

---

## 4. Width and style parameters — why zero-config won

The practice corpus (gofmt, dart_style, Prettier, black) converged on a strong lesson.

| Tool | Config surface | What they fixed | Why |
|---|---|---|---|
| **gofmt** | **zero** | tabs, one brace style, canonical spacing; impl *is* the spec | ended all Go formatting debate; "gofmt's style is no one's favorite, yet gofmt is everyone's favorite" |
| **dart_style** | effectively zero (width only, historically 80) | one line-splitting algorithm; no per-project knobs | same social outcome — no bikeshedding, tool output is authoritative |
| **Prettier** | a *few* knobs (printWidth, tabWidth, semi) — regretted breadth | a Doc IR (Wadler-lineage `group`/`indent`/`line`) | the IR is the right layer; the *knobs* are the part the community wishes were fewer |
| **black** | width only ("uncompromising") | one style, deliberately non-negotiable | explicit "zero-config" as a feature |

**The lesson for bang:** zero-config is not a limitation, it is the **generative constraint**
(constraints are generative, not only limiting). A canonical formatter's entire value is that
*there is one output* — every knob you add reintroduces the style entropy the formatter exists to
delete (Format.lean header: an agent's output style is pure improvisation; the formatter deletes it).
The v1 flat printer already exploits this (ZERO options). The multi-line rung should preserve it:
**one width constant, no user knobs.**

Width choice: Lean's `Std.Format.defWidth = 120`, `defIndent = 2`. A defensible bang default is
**80 columns, 2-space indent** (the terminal/diff-friendly classic gofmt/dart use, more conservative
than Lean's editor-oriented 120), but this is a *preference* call for the operator — the survey's
job is to name that it must be **one fixed constant, not a knob**, and that indentation should be
2-space to match Lean-host convention and the corpus. ADR-0090 recommends the value; the operator
rules.

---

## 5. The lineage, one line each (for the citations)

| Paper | The one thing it contributes to bang's decision |
|---|---|
| **Hughes '95** (Design of a Pretty-printing Library) | the algebraic-spec-then-derive method; the `fill` (greedy) layout `Std.Format` also offers |
| **Wadler '03** (A Prettier Printer) | the Doc algebra bang's engine (via `Std.Format`) *is* — `<>`/`nest`/`line`/`group`/`flatten` + their laws |
| **Oppen '80** | the first `O(n)` engine; the `group`+width-fitting shape all successors share |
| **Bernardy '17** (Pretty But Not Greedy) | *optimal* (fewest-lines, narrowest) layout via ranking — the upgrade path if bang ever wants optimal over greedy; not needed for v1 |
| **Rendel-Ostermann '10** (Invertible Syntax Descriptions) | one grammar → parser AND printer (rung 3 origin); the ancestor of biparsers |
| **FliPpr** (Matsuda-Wang '18) | invertible *pretty*-printing (a program → its parser); rung 3, pretty-printer-first |
| **Xie '25** (Biparsers) | rung 3 for *exact* printing with non-injective parsers; the lens+complement framing (see §2) |
| **Christiansen-Darais-Ma** (Final Pretty Printer) | extensible effectful pretty printing; layout core is Wadler, novelty orthogonal to bang (see §3) |
| **gofmt / dart_style / black** | zero-config canonical formatting is a social + technical win (see §4) |
| **Lean `Std.Format`** | the host's Wadler engine bang should ride (see §3) |

---

## 6. What this survey feeds

- **ADR-0090** (`docs/decisions/0090-formatter-multiline-layout.md`) — the multi-line layout
  decision: engine = `Std.Format` (option A), zero-config width constant, how the two existing laws
  extend, corpus reformatting question, CLI `-w` in-place question.
- The **#14 fuzz generator** as the cheap rung-1.5 strengthening: property-test `roundTripsOn` over
  generated `Surf`/`Prog`, not just the fixed corpus (survey §1). Recorded here as the named next
  strengthening, independent of the multi-line rung.
