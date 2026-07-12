<!-- note-status: active -->
# Type-power wave — entry-slice design (Wave E, ROADMAP §Pre-v1 type-power ladder)

> Established 2026-07-12. The operator approved opening the type-power wave (previously
> consumer-gated). This note picks WHICH of the three candidate rungs has the nearest real
> consumer and designs its entry slice. It is a **DESIGN-FIRST probe, docs-only** — no
> implementation, deliverable = a consumer-evidenced entry design. Companions (read for
> depth): `refinement-types-survey.md` (R5), `lambda-cube-ascent-survey.md` (R6),
> `traits-prelude-survey.md`, issue #94, and the two dogfood friction logs
> (`dogfood-json-findings.md`, `dogfood-calc-findings.md`).
>
> **Method (No-Free-Lunch discipline).** A constraint must buy *exploitable structure*, so
> each candidate gets a consumer VERDICT with cited evidence: a real program/diagnostic/proof
> that gets better, or "no consumer yet" — which ELIMINATES it. The winner then gets a proper
> entry-slice design; a candidate with no consumer is not forced into one. The `bang` binary
> was NOT built in this lane (docs-only) — every bang claim cites a file/issue/ADR, nothing
> here is empirically re-tested.

## 0 · The one-paragraph verdict

**Candidate (1) OPEN ROWS / subeffecting WINS on the consumer check by a wide margin; (2)
refinements and (3) λP-closed both fail it honestly and are eliminated for now.** (1) has a
`lake build`-gated corpus witness (`examples/stage-swap` §"Known gate"), a filed
type-system-design issue (#94) with an isolated non-cap repro, a `#guard`-pinned expected
failure in the checker itself (`rowPolyDivSrc`), AND an independent theory corroboration (the
calc-typer experiment identified the subeffecting side-condition as *Cousot's consequence
rule* — `calc-typer-experiment-findings.md`). (2) refinements have NO live consumer: the
kernel's `/` is **total** (`a / 0 = 0`, Euclidean — `IR.lean:186`, `WasmEmit.lean:73`), so a
`{d ≠ 0}` divisor refinement would guard against a *non-error*; `take`/`drop` are
`Int -> List a -> List a` total on negative args; the dogfood JSON parser's manual guards are
*shape/parse* checks a refinement rung-0 would not retire; and rung-0 is a runtime guard
(ADR-0063 shape) with zero static payoff the type system doesn't already give. (3) λP-closed
has NO consumer: the traits survey's dead-impl carrier check + Show-derive are ELABORATION
folds over the existing ADR-0069 μ-sum-of-products (a `DerivingHandler`, no type-level
indexing), and R6's own demand-probe expects zero roadmap hits. The winning entry slice for
(1): **plumb ADR-0018's already-shipped lacks-constrained row quantifiers from the kernel into
the frontend's `generalize`/instantiate path, fixing the documented single-ρ collapse in
`joinRow` — starting with the cheapest honest slice, subeffecting-only (`⊥ ⊆ ρ` via the
EXISTING `subRow`), kernel untouched.**

## 1 · The consumer verdicts (the elimination — evidence per candidate)

The No-Free-Lunch gate: a rung earns its complexity only if it makes a *real, cited* artifact
better TODAY (or retires a real diagnostic). Applied to each:

```
 candidate          live consumer?   the decisive evidence (cited)
 ────────────────   ──────────────   ───────────────────────────────────────────────────────
 (1) open rows /    ✅ YES            corpus WITNESS + issue + in-checker #guard + theory
     subeffecting                    corroboration — four independent signals (§2)
 (2) R5 rung-0      ✗ NO              div is TOTAL (no trap to retire); take/drop total on neg;
     refinements                     JSON guards are shape/parse not value-predicate;
                                     rung-0 = a runtime guard, zero static win (§3)
 (3) R6 λP-closed   ✗ NO             traits derive = a FOLD over the existing μ-sum-of-products
                                     (a DerivingHandler, no indexing); R6 demand-probe = 0 hits;
                                     no roadmap construct defeats the three elaboration dodges (§4)
```

Two of three fail — which is the *expected* shape under the discipline (a constraint you
can't point a consumer at is debt). The note does not force a winner; it happens that (1) has
an overwhelming one.

## 2 · Candidate (1) — the WINNER: four independent consumer signals

The row-reuse wall is the one type-power limitation with a *filed, reproduced, feature-gating*
consumer. The signals, each cited and each independent:

1. **A `lake build`-gated corpus witness.** `examples/stage-swap/README.md` §"Known gate:
   reusing ONE installer binding across differently-effectful bodies (#94)" ships the exact
   failing program:
   ```
   let pureBody = ( {fun net => 99} : Thunk (Cap Net -> Int) ) in
   (($test) logic) + (($test) pureBody)   -- `test` reused at {Net} then at {} → "effect row mismatch"
   ```
   `test` type-checks against `logic` (row `{Net}`) alone AND against `pureBody` (row `{}`)
   alone; only the REUSE in one program fails. This is the per-stage handler-swap thesis
   (#84's "the stage IS the handler") hitting its ceiling in the flagship demo of that thesis.

2. **A filed type-system-design issue with an ISOLATED non-cap repro.** Issue #94
   ("row-inference refinement: subeffecting or Rémy rows") reproduces the identical failure
   with ZERO capability/user-effect involvement — `compose incPure <effectful>`, entirely
   built-in-row — proving the wall is row-inference-GENERAL, not a wrapper-pattern or cap
   artifact. The issue explicitly frames it as `ctr`-style design-probe territory (this note),
   names the fork (subeffecting vs full Rémy), and scopes it Frontend-leaf (no kernel change).

3. **A `#guard`-pinned expected failure inside the checker.** `TypeCheck.lean`'s
   `rowPolyDivSrc` corpus pins `compose incPure <effectful>` as an EXPECTED loud failure with
   the doc-comment forecast: *"It needs subeffecting (⊥⊆ρ) or independent tails + a real join
   (full Rémy) — the deferred refinement"* (the `joinRow` "single-ρ first cut" comment,
   `TypeCheck.lean:499`). The limitation is not just felt in dogfooding — it is a
   build-gated, self-documented debt the checker carries.

4. **An independent THEORY corroboration.** The calc-typer porting experiment
   (`calc-typer-experiment-findings.md`) located the fix precisely: *"the subeffecting
   side-condition `e ≤ labelEff ℓ ⊔ φ` **is Cousot's consequence rule** = the over-approximation
   α, derivable not postulated."* The subeffecting rung is not an ad-hoc convenience — it is
   the abstract-interpretation consequence rule the effect algebra already wants, and it
   *derives* (join-preserving on the effect half, which sits in the sound-AND-complete
   idempotent corner). This is the No-Free-Lunch payoff made concrete: the constraint
   (subeffecting order on rows) buys the capability (reuse-across-rows) AND is theoretically
   forced, not invented.

**Verdict (1): OPEN — strongest possible consumer signal.** A demo, an issue, an in-checker
witness, and a theory result all point at the same rung. This is the entry slice designed in
§5–§10.

## 3 · Candidate (2) — refinements: NO live consumer (eliminated)

The brief's consumer check named three probes: guarded-div, take/drop negatives, the neg-div
example. All three come back negative:

- **Div-by-zero is not an error to guard.** The kernel's `/` is **total**: `BinOp.eval div`
  is `Int.ediv`, and `a / 0 = 0` by construction (`IR.lean:186` — *"Division by zero is Lean's
  total Int division (`a / 0 = 0`)"*; `WasmEmit.lean:73` — *"the kernel's `div` is TOTAL and
  EUCLIDEAN"*). A `{d : Int // d ≠ 0}` refinement would statically reject programs the language
  DEFINES to be well-behaved. There is no trap, no UB, no diagnostic to retire — the opposite
  of a consumer. (The `neg-div` example — issue #132 — is about Euclidean-vs-truncated
  SEMANTICS agreement between kernel and wasm, not a value-predicate; a refinement is
  irrelevant to it.)
- **`take`/`drop` are total on negative arguments.** They are stdlib
  `Int -> List a -> List a` (`TypeCheck.lean:5604`); a negative count is well-defined (yields
  the whole list / empty per the fold), so `{n // n ≥ 0}` guards a non-error again.
- **The JSON parser's manual guards are shape/parse checks, not value predicates.**
  `dogfood-json-findings.md`'s friction log is dominated by *structural* asks — mutual `data`,
  nested match patterns, `fst`/`snd`, unary minus, line comments, the sibling-`let rec` Div
  blocker — none of which a `{x // P x}` rung-0 refinement addresses. The "manual checks" the
  R5 survey's probe-1 hypothesized (§5) are, in the actual dogfood corpus, *tag dispatches and
  parse-position bounds threaded by hand through the recursive descent* — controlled by the
  parser's own logic, not by a divisor/index predicate a refinement erases.
- **Rung-0 is a runtime guard with zero static payoff.** The R5 survey's own ladder (§4) puts
  rung-0 = *runtime check, fail-loud, ADR-0063 shape* — a DESCENT that must be marked. It buys
  nothing the type system doesn't already give (the kernel already fail-louds); the static win
  starts at rung-1 (Decidable-instance discharge), which the survey itself scopes post-v1 and
  gates on the same JSON-guard residue that §3 just showed is shape-shaped, not value-shaped.

**Verdict (2): ELIMINATED (no consumer today).** The R5 survey already reached this
conclusion ("DEFER implementation; ADOPT the framing") and named the exact re-check trigger:
*"array/index safety, positivity, or div-by-zero pressure in dogfooding."* None is present.
The framing stays banked; the rung stays closed. **Re-check condition:** a dogfood program
whose manual guards are genuinely value-predicate-shaped (bounds/positivity threaded through
generic code where the type can't see them) AND where a runtime fail-loud is insufficient —
i.e., R5 probe-1's residue becoming a felt cost. (Note: even then, subeffecting/open-rows is
orthogonal and can land first.)

## 4 · Candidate (3) — λP-closed: NO consumer (eliminated)

The brief's consumer check pointed at the traits survey's dead-impl carrier check and Show
derive. Both are ELABORATION folds, not type-level indexing:

- **Deriving is a fold over the EXISTING data shape, not a λP feature.**
  `traits-prelude-survey.md` §2/§4: a `deriving (Eq, Ord)` handler is *"a fold over the
  ADR-0069 μ-sum-of-products"* — the elaborator already HAS this shape (`data T = C₀(…) | …`
  lowers to `μX. p₀ + (p₁ + …)`), and the derive mechanism is a Lean-`DerivingHandler`-style
  pass that reads the resolved ctor set and emits the impl. No `Vec n`, no const-generic value
  indexing, no type-level computation over a family — exactly the §2 dodge R6 already names
  (kinds-as-arity monomorphization, ADR-0082, is *already shipped* as a special case). The
  dead-impl carrier check is a guard on WHICH carrier the fold targets (user `data` only, not
  a built-in), not a dependent-type obligation.
- **R6's own demand-probe expects zero hits.** `lambda-cube-ascent-survey.md` §7 probe-3
  sweeps the R1–R4 notes + demo pack for any construct that defeats ALL of {λP-closed,
  sum-packaging, the R5 refinement face}; the expected result is *"zero hits (§3's residue is
  prover-shaped, and Q42 defers the prover)."* The traits work is the closest candidate and it
  is a fold, not a residue item.
- **The rung is already partly shipped where it's real.** F/Fω via elaborate-to-mono
  (ADR-0075/0082) already delivered the type-power the prelude/traits work needed; λP-closed
  is the NEXT rung up, and R6's verdict is *"the elaborate-to-mono licence extends to it
  conditional on the finiteness gate — but DEFER behind a pre-registered trigger."*

**Verdict (3): ELIMINATED (no consumer today).** **Re-check condition** (R6 probe-3's
falsifier): a roadmap construct that fails all three elaboration dodges — sized vectors whose
index FLOWS through generic code at runtime, schema-indexed deserialization over a runtime
schema, or the in-language prover (Q42). None is on the pre-v1 roadmap. If one appears, R6 has
the pre-written K-ADR shape (dCBPV⁻, Π over ⊥-row values, #47 prerequisite).

## 5 · The winner's entry slice — surface syntax sketch

The consumer (#94 / stage-swap) needs ONE thing: **a row-polymorphic binding reusable at
genuinely different effect rows in one program.** Two design points, and the note recommends
the cheaper one FIRST (it retires the actual corpus witness), with the general one as the
named next rung.

**Slice A (recommended first) — subeffecting, NO new surface syntax.** The stage-swap witness
reuses `test` at `{Net}` then `{}`; `{} ⊆ {Net}`, so a *subeffecting* order (`⊥ ⊆ ρ`, and more
generally `φ₁ ⊆ φ₂` at a use site that expects `φ₂`) makes the pure-body application accepted
against the effectful-body's inferred row. No surface change: the programmer writes exactly
the stage-swap program as-is; the checker stops rejecting it. This is the lightest fork named
in #94 and the one the calc-typer experiment identified as Cousot's consequence rule.

**Slice B (the general rung, named next) — open-row ascription for full Rémy reuse.** Where
subeffecting is insufficient (two uses at INCOMPARABLE rows, e.g. `{Net}` and `{Log}`, neither
⊆ the other), the binding needs an independent tail per use — genuine row polymorphism with a
lacks constraint. Surface syntax, mirroring ADR-0018's kernel form `∀(α # L). τ`:

```
-- an explicitly row-polymorphic installer: the row var `r` is open, lacks {Net}
let apply : Thunk (∀(r # {}). Thunk (Cap Net -> Int ! {Net} ⊔ r) -> Int ! r) = …
```

The `∀(α # L)` binder and the `φ ⊔ r` open-row form are the surface spelling of the kernel's
already-shipped machinery (ADR-0018, `EffectRow.Row.tail : Option RVar`). Most programs never
write it — let-generalization infers it (§7) — the way `∀` is invisible in `map`'s type today.

**What the surface does NOT gain:** ordered rows, ρ-maps, `lift`, or two handlers for one bare
label — all forbidden by ADR-0018/ADR-0001 (§10).

## 6 · The elaborate-to-mono story — the kernel stays untouched (argued)

This is a FRONTEND change, and the argument is direct: **ADR-0018 already put
lacks-constrained row quantifiers in the KERNEL** (`Bang/Spec.lean §0.5`
`rowinst_requires_disjoint`, `no_accidental_handling`; the row carrier
`EffectRow.Row = {labels : Finset Label, tail : Option RVar}` already has the open tail, and
`EffectRow.unify` already handles open/open unification with a fresh tail —
`EffectRow.lean:118`). The kernel does not need to LEARN row polymorphism; it already has it.
What is missing is entirely in `Bang/Frontend/TypeCheck.lean`:

- the frontend's `joinRow` (`TypeCheck.lean:503`) COLLAPSES two distinct open tails to one
  (*"the single-ρ first cut"*) — the documented incompleteness that IS #94;
- the frontend's `generalize`/instantiate (`TypeCheck.lean:815`) generalizes row vars but does
  not give each USE an independent instantiation with its own tail;
- there is no surface parser for the `∀(α # L)` binder (Slice B only).

The elaborate-to-mono discipline holds because **rows stay ground in the kernel** (the R6
survey's own ground truth: *"row-poly SHIPPED (first-class from bite 0); rows stay ground"*,
`lambda-cube-ascent-survey.md` §1). A row-polymorphic binding elaborates to its
per-use-site monomorphic instantiation exactly as F generics do — the same instantiation
machinery, one rung over. No new kernel type former, no census re-proof (the 18→20 headline
theorems are stated over the already-open kernel row algebra). **Falsifier to watch** (the R6
probe-2 shape): a row var that must flow through a `mu`/`sum` position where per-use
instantiation loses the tail identity — the ADR-0075 hole-id-collision class. If it fires, the
fix is frontend hole-management (the ADR-0075 pattern, `elabBind`), NOT a kernel change; §9's
slice order front-loads a differential test to catch it early.

## 7 · The checker delta — precise, per existing def

The change is scoped to named defs that already exist; the partial machinery is ALREADY THERE
(the #119 fork landed a check-mode subsumption comparator):

```
 def / site (TypeCheck.lean)     current behavior                    Slice-A delta (subeffecting)
 ─────────────────────────────   ────────────────────────────────   ──────────────────────────────
 subRow (526)                    actual ⊆ declared — EXISTS, used    reuse verbatim; it IS the
                                 in checkSC's declared-bound arm      subeffecting relation (⊆)
                                 (1061/1160/1352)
 subsumeAppV/subsumeAppC (612)   #119's nested-row subsumption in     the precedent: subsumption
                                 checkSC's .app arm                   already lives here, scoped
 joinRow (503)                   single-ρ collapse of two open        Slice B: give distinct uses
                                 tails — the #94 incompleteness       independent tails (Rémy join)
 synthSC .app arm (610 region)   where rowPolyDivSrc/#94 FAIL —       Slice A: at a reuse site, admit
                                 unifyRow exact-equality on the row   φ_use ⊆ φ_bound via subRow
                                 instead of a subeffecting ⊆
 generalize (815)                generalizes row vars, value-         Slice B: per-use instantiation
                                 restricted (isValueSurf, 1104)       with a fresh independent tail
```

Slice A's delta is small: the `.app`/reuse site that currently calls `unifyRow` (exact row
equality) instead admits `subRow φ_use φ_bound` (the actual ⊆ declared relation that ALREADY
EXISTS and is ALREADY used elsewhere in the checker). The soundness posture is preserved: per
the codebase's MGU stance (CLAUDE.md "Do NOT prove most-generality"), soundness is the
contract and the differential test (against `Source.eval`) covers completeness/MGU — so the
subeffecting relation needs `subRow`-soundness (already proven — `unify_sound`, delegated at
`TypeCheck.lean:468`), NOT a new MGU proof.

## 8 · The diagnostic story

Today the wall is a bare `"effect row mismatch"` at the second reuse — actionable only to
someone who knows #94. Two improvements, cheapest first:

1. **Slice-0 diagnostic (ships BEFORE any type-system change — pure win).** When `unifyRow`
   fails at a reuse of a let-bound row-polymorphic value, emit: *"'test' was used at effect row
   {Net}, then reused at {} — reusing one binding across different effect rows needs
   subeffecting (issue #94). Split into separately-named bindings, or ascribe an open row."*
   This turns the flagship demo's known-gate from a cryptic reject into a taught idiom
   TODAY, independent of the checker change. (Same class as the JSON round's ask for the
   metavariable-leak and "not a returner" diagnostics — `dogfood-json-findings.md`.)
2. **Post-Slice-A**: the reject only fires at genuinely incomparable rows (Slice B territory);
   the message names the incomparability explicitly (*"{Net} and {Log} are incomparable — this
   needs an open-row ascription `! {…} ⊔ r`"*).

## 9 · The slice map — cheapest honest first slice

```
 slice   what lands                                              gate / oracle                cost
 ─────   ────────────────────────────────────────────────────   ──────────────────────────   ──────
 S0      the diagnostic (§8.1) — NO type-system change; the      test-check-json + a new      hours
  (do     "effect row mismatch" at a row-poly reuse becomes a    negative example asserting
  FIRST)  #94-naming taught message                              the improved text
 S1      subeffecting at the reuse site: synthSC's .app/reuse    the stage-swap witness       days
  (the   admits φ_use ⊆ φ_bound via the EXISTING subRow;         (§2.1) flips from KNOWN-GATE
  prize) rowPolyDivSrc's `compose incPure <effectful>` flips     to PASSING; rowPolyDivSrc
         from expected-FAIL to PASSING                           #guard updated; DIFFERENTIAL
                                                                 test vs Source.eval on both
                                                                 the pure and effectful reuse
 S2      the ADR (§10) — subeffecting vs full-Rémy fork,         adr-check green               hours
         rejected alternatives recorded
 S3      Slice B (open-row surface + independent tails) —        a NEW example reusing one     weeks
  (next  ONLY if a corpus program needs INCOMPARABLE-row reuse   binding at {Net} and {Log};
  rung)  (none exists today — gated on a real consumer)          full Rémy differential test
```

**The cheapest honest first slice is S1 (subeffecting)** — it retires the actual, cited corpus
witness (`stage-swap` §"Known gate") and the in-checker `rowPolyDivSrc` expected-failure, using
a relation (`subRow`) and a soundness proof (`unify_sound`) that ALREADY EXIST. S0 (diagnostic)
ships even cheaper and is a strict prerequisite-free win. S3 (full Rémy) is deferred behind its
OWN consumer gate — no program needs incomparable-row reuse today, so building the general
machinery first would violate the same No-Free-Lunch discipline that eliminated (2) and (3).

## 10 · What it must NOT do (the rejected shapes, re-cited)

- **No ordered rows, no multiset, no `lift`/ρ-maps.** ADR-0001 (rows are idempotent `Finset`)
  + ADR-0018 (*"NOT via `lift` / `ρ`-maps, which would re-introduce a non-idempotent (multiset)
  row algebra and break everything below"*). Full Rémy here means *independent lacks-constrained
  tail variables over sets*, never Rémy's duplicate-label machinery.
- **No two handlers for one bare label.** ADR-0018's accepted cost; multi-instance is recovered
  via fresh effect labels (instances: `State#1, State#2`), still a set — NOT a row-algebra
  change.
- **No kernel change.** #94 is Frontend-leaf by construction (the kernel already has open
  lacks-constrained rows, §6); a slice that reaches into `Bang/Core` has overshot. The invariant
  `no_accidental_handling` (`Spec.lean §0.5`) is what the kernel's lacks-discipline already
  guarantees — the frontend must PRESERVE the disjointness side-condition when it instantiates,
  not weaken it.
- **No MGU proof obligation.** CLAUDE.md "Do NOT prove most-generality" — soundness (`subRow`
  via `unify_sound`) is the contract; MGU/completeness goes to the differential test vs
  `Source.eval`, per the codebase's standing posture.
- **Do not force refinements or λP in alongside.** They are eliminated (§3/§4) for lack of a
  consumer; bundling them would be exactly the speculative-generality the discipline forbids.

## 11 · The ADR this slice would need (input, not filed from this lane)

**"Effect-row reuse: subeffecting (⊆) at reuse sites; open-row ascription for the general
case; single-ρ collapse retired."** A genuine fork a future session could relitigate
(subeffecting-only vs full Rémy vs status-quo single-ρ), so it needs an ADR recording:

- **Decision**: adopt subeffecting (`φ_use ⊆ φ_bound`) at row-polymorphic reuse sites (S1),
  with open-row ascription (`∀(α # L). … ! φ ⊔ α`, ADR-0018 surface) as the general rung (S3,
  consumer-gated).
- **Rejected alternatives**: (a) status-quo single-ρ collapse (rejected: it IS #94, a
  feature-gating incompleteness with a live consumer); (b) full Rémy FIRST, before a
  subeffecting slice (rejected: no incomparable-row consumer exists — builds machinery ahead of
  demand); (c) ρ-map/lift-based multi-instance (rejected: ADR-0018, breaks the set algebra).
- **Corroboration**: the calc-typer experiment (subeffecting = Cousot's consequence rule,
  derivable not postulated).
- **Depends-on**: ADR-0001, ADR-0018 (extends the frontend consumption of their row algebra).

---

**Consulted** (2026-07-12, docs-only — bang binary NOT built): issue #94 (via `gh`, full
body); `examples/stage-swap/README.md` §"Known gate"; `examples/neg-div/README.md`;
`Bang/Core/IR.lean:186` (total div); `Bang/Backend/WasmEmit.lean:73` (Euclidean guarded div);
`Bang/Core/EffectRow.lean:54/118` (open row + unify); `Bang/Frontend/TypeCheck.lean`
(`subRow:526`, `unifyRow:489`, `joinRow:503`, `subsumeAppV:612`, `generalize:815`,
`take/drop:5604`, the `rowPolyDivSrc` corpus); `docs/decisions/0001` + `0018` (row algebra +
lacks constraints); `docs/notes/refinement-types-survey.md` (R5); `lambda-cube-ascent-survey.md`
(R6); `traits-prelude-survey.md` (deriving = a fold); `dogfood-json-findings.md`;
`dogfood-calc-findings.md`; `calc-typer-experiment-findings.md` (Cousot corroboration);
`stranger-test-{1..4}.md` (checked for row/refinement friction — NONE found). CLAUDE.md
invariants #2 (rows-as-sets) and the MGU posture. Nothing here empirically re-tested.
