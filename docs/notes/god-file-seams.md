<!-- note-status: active -->
# God-file seam map — split proposal for `TypeCheck.lean`/`AbstractMachine.lean`

> **Status.** Design proposal only. **Zero code moved.** This note produces the seam map so
> that when the split is executed, it is mechanical and behavior-identical, not a live
> re-design. Opening the PATH to execute it is the operator's call (see closing section).

## 0 · Why

`Bang/Frontend/TypeCheck.lean` (5770 lines) and `Bang/Backend/AbstractMachine.lean` (6849
lines) are together ~40% of the codebase and ~10× the repo's median module size. Costs:
navigation/review touch many subsystems at once, single-file Lean re-elaboration time grows
with file size, and parallel agent work on disjoint subsystems inside one file forces
one-writer serialization (`.claude/lane-discipline.md`). A split executed *without* a designed
seam risks the worse outcome: circular imports, types moved to the wrong stratum, or a broken
import-direction invariant (the `arch-check` fitness leg, ADR-0048).

Line-number anchors below are as of commit `f1cb2cf` (branch point for this plan). Re-anchor by
line CONTENT (the `/-! ## … -/` header text), not raw numbers, before executing — headers are
stable, line numbers drift with every edit.

## 1 · Section inventory + dependency table

**Methodology note.** Raw `grep -c`/occurrence counts for short, common identifiers
(`check`, `resolve`, `hget`, `instantiate`, …) are unreliable on this codebase — Lean proof
scripts reuse short hypothesis names (`hget` collides with an unrelated local in
`Bang/Meta/BinaryLR.lean`/`Bang/Core/Soundness.lean`) and prose comments reuse English words
that substring-match identifiers (`check` collides with "type-check"/"cross-check" in doc
comments). Every consumer claim below was re-verified by reading the actual matched line, not
just counting hits — where a first-pass grep sweep and the line-level re-check disagreed (this
happened once, on the TypeCheck `#guard` corpus's dependency surface, §1.1), the re-checked
finding is what's reported, with the correction called out explicitly rather than silently
overwritten.

### 1.1 `Bang/Frontend/TypeCheck.lean` (5770 lines, no `import Bang.*` — a leaf w.r.t. other
`Bang` modules; it is *itself* imported by 4 files, table in §1.3)

| region (line span) | header | load-bearing exports | consumers (outside TypeCheck.lean) |
|---|---|---|---|
| 45–182 | bidirectional checker (pure fragment) | `CT`/`Ctx` abbrevs (37–38, technically pre-header), the pure-fragment checker defs | Internal only — feeds the Surf-level checker (172+) and elaboration (2491+) within the same file. No external consumer found. |
| 182–421 | inference types `IVTy`/`ICTy` (ADR-0075) | `IVTy`, `ICTy`, the closed-kernel injection/zonk pair | Internal — consumed by the HM substrate (421+) and elaboration (2491+) in-file. No hit outside TypeCheck.lean. |
| 421–1536 | HM inference substrate | `Infer` (abbrev, 444), unification, row-variable inference, generalization | Internal only — consumed by elaboration (2491+) and later in-file sections. No external `Bang/` consumer found by name search. |
| 1536–2491 | HKT helpers (ADR-0082) | kind-check, carrier-head extraction, application-spine helpers | Internal — feeds elaboration (2491+) in-file only. |
| 2491–3120 | type-directed elaboration over `Surf` | the elaborator core (`elabHClauses`, `elabBind`, binop resolution) | Internal to TypeCheck.lean except where the corpus region (5146+) exercises it as a black box via `checkProg`/`checkAndLower`. |
| 3120–3931 | Modules (ADR-0093) merge-to-flat, PURE half | qualification/rename helpers, merge-to-flat folding | Internal only. |
| 3931–5146 | source LAWS discharge | law-body diagnosis, trait-op-by-name resolution | Internal only; feeds validation sections in the corpus region that exercise laws end-to-end via the public entry points. |
| 5146–5770 (EOF) | the `#guard` corpora / validations ⑨k onward | pure `#guard` test corpus | **Consumer of** `checkProg` (def at line 3738), `checkAndLower`, `parseProg`, `buildEnv` (the four public entry points) **PLUS a direct, non-trivial internal-name dependency** — see the correction below. |

**Answering the plan's key questions (corrected after direct verification, see note):**

- **Does the `#guard` corpus region depend on anything except `checkProg`/`checkAndLower`/
  `parseProg`/`buildEnv`? — NO, and this corrects the plan's stated hypothesis.** A direct
  word-boundary check of every pre-5146 top-level name against the corpus region's text
  (`awk`-extracted def list × `grep -oE '\b<name>\b'` over lines 5146–5770, each hit read at its
  source line to rule out comment/prose noise) found 20+ pre-5146 internal names directly
  referenced inside the corpus region, not just the four public entry points — among them
  `showCTy` (real function calls at lines 55/61/68 of the corpus region, not comments — verified
  by reading the matched lines), `checkPerformUnderCap` (13 occurrences), `elabHClauses`,
  `elabProg`, `elabS`, `synthSC`, `synthSV`, `qualifyModule`, `qualifyDotAccess`,
  `qualifyModuleOwnImports`, `resolve`/`resolveTy`/`resolveTyG`/`resolveEffName`, `unifyRow`,
  `zonkInferC`, `runInferC`, `effOf`/`effNames`, `foldLetDecls`, `capOpSig`, `curryBind`,
  `anfSplit`, `isValueSurf`, `check` (20 occurrences — the bidirectional-checker entry, not
  `checkProg`). Some hits (`checkHClauses`, `checkLaws`) are prose-comment references rather than
  calls, but the majority above are genuine calls, confirmed by reading matched lines directly.
  **The corpus is NOT the narrowly-isolated, cheapest extraction the plan hypothesized** — it
  reaches across the elaboration (2491+), Modules-merge (3120+), and LAWS-discharge (3931+)
  sections, not just the four public entry points. This reverses this note's own cut-order §5
  step 1 below; see the correction there.
- **Is the HM substrate (421–1536) consumed by anything except the elaborator sections below
  it?** No external-file consumer found (`grep`-confirmed no other `Bang/*.lean` file
  references `Infer`, the unification defs, or the row-inference defs by name). It is consumed
  *in-file* only, by the elaboration section (2491+) and later validation sections that invoke
  the checker through the public API (not the HM internals directly).

### 1.2 `Bang/Backend/AbstractMachine.lean` (6849 lines, no `import Bang.*`)

| region (line span) | header | load-bearing exports | consumers (outside AbstractMachine.lean) |
|---|---|---|---|
| 106–224 | the three stores: `SStore` (106), `THeap` (131), `CStore` (190) | `SStore`, `THeap`, `CStore` abbrevs (116/152/214) | `Bang/Backend/{Wasm,U5bComplete,EnvMachine}.lean`, `Bang/Witness/{AgreeOutcome,Fuzz}.lean`, `Bang/Examples.lean`, `Bang/Audit.lean` all import the whole module — these abbrevs are part of the public surface every downstream consumer sees. |
| 225–363 | the denotational source `evalD` | `evalD` | Same consumer set — `evalD` is the middle oracle (per CLAUDE.md glossary) that `Bang/Witness/AgreeOutcome.lean`'s diff test and `Bang/Audit.lean`'s gate both depend on. |
| 363–544 | the machine — derived, not designed | `Code` (406), `Stack` (410), `HStack` (422), `compile`, `exec` | Consumed by `Bang/Backend/{Wasm,U5bComplete}.lean` (the WasmFX lowering rides `Code`/`exec`) and by the proof sections *within this same file* (545+, 2158+, 3592+). |
| 545–1081 | correspondence + disjointness: Store↔HStack (545), Transaction↔HStack (594), Custom↔HStack (637), `StoresDisjoint` (670), preservation (703) | the three bridge invariants + `StoresDisjoint` | Consumed by the calculation-correctness proofs (2158+) and the D1-A bridge (3592+) *in-file*. `Bang/Meta/BinaryLR.lean` references `HStack`-shaped invariants transitively through `Bang.Core.Soundness`, not directly against this file (BinaryLR imports `Bang.Core.*` + `Bang.Meta.LR`, not `Bang.Backend.AbstractMachine` — confirmed no direct import edge, §4). |
| 1081–2158 | `HMut` + transaction-side lemmas + cross-projection stability | `HMut`, the txn service/correspondence lemma set | In-file only — feeds the calculation-correctness section below. |
| 2158–3447 | **the calculation is correct (proven)** | the headline `compile`/`exec` correctness theorems | Consumed downstream by `Bang/Audit.lean`'s `#print axioms` gate and cited by `Bang/Witness/*` diff tests as the theorem backing the executable spec. |
| 3447–3592 | the ◊3 diff-test battery (`exec ∘ compile ≡ Source.eval`) | the curated diff-test program set | Terminal — exercises the machine + `evalD` through public defs; not consumed further. |
| 3592–4958 | the D1-A bridge (`evalD ≡ Source.eval`) + `EvalCtx` correspondences (state/txn/custom) + K-side disjointness corollary | `evalD_agrees_source` and its supporting bridge lemmas | Cited (not imported-as-code) by `docs/notes/ctr-design.md` and other proof-design notes as the standing theorem; consumed structurally within `Bang/Meta/BinaryLR.lean`'s proof obligations via `Bang.Core.Soundness`, which itself is built to agree with this bridge — an *indirect*, spec-level dependency, not a Lean import edge. |
| 4958–6849 (EOF) | K-side store-disjointness corollary onward (tail of the file) | closing lemmas | In-file only, closes out the D1-A bridge cluster. |

**Answering the plan's key question:** *Do the proof sections (545+, 2158+, 3592+) consume the
executable sections (106–544: stores, evalD, the machine) only through a narrow set of
definitions?* Yes, narrowly: the proof sections reach into the executable sections primarily
through the same small vocabulary — `SStore`/`THeap`/`CStore`, `evalD`, `Code`/`Stack`/`HStack`,
`compile`/`exec` — rather than reaching past that surface into private helpers. This is the
load-bearing fact that makes a `Stores`/`Machine` vs `Proofs` cut plausible, **but** the proof
sections are large (2158–4958, roughly 2800 of the file's 6849 lines) and mutually
cross-reference each other extensively (calculation-correctness → diff-test battery → D1-A
bridge build on each other in sequence) — so while the *executable* surface they consume is
narrow, the *proof* sections themselves are not independently separable from one another without
finer-grained investigation this note does not attempt. See §4 stays-put.

### 1.3 Reverse edges — who imports each god file

| file | imports `TypeCheck` | imports `AbstractMachine` |
|---|---|---|
| `Bang/Frontend/Diagnostics.lean` | yes | no |
| `Bang/Witness/ProofExport.lean` | yes | no |
| `Bang/Witness/LawTest.lean` | yes | no |
| `Bang/Witness/ElabFuzz.lean` | yes | no |
| `Bang/Backend/EnvMachine.lean` | no | yes |
| `Bang/Backend/Wasm.lean` | no | yes |
| `Bang/Backend/U5bComplete.lean` | no | yes |
| `Bang/Witness/AgreeOutcome.lean` | no | yes |
| `Bang/Witness/Fuzz.lean` | no | yes |
| `Bang/Examples.lean` | no | yes |
| `Bang/Audit.lean` | no | yes |

**No file imports both** (checked both plain `import Bang.*` and the module-syntax
`public import Bang.*` forms across the whole tree). This is the confirmation the plan's STOP
condition #2 (a genuine cycle) does not fire — see §4.

## 2 · Proposed module set

Precedent for the shape: `Bang/Core/Semantics.lean` is already a thin hub re-exporting
`Bang/Core/Semantics/{Subst,Dispatch,Eval,Invariants}.lean` (a prior "split a fan-in hub into a
tier subdirectory" move, `docs/architecture/core-overview.md` §6, task #15/#17). The same shape
— hub file `public import`-ing siblings under a `<OldName>/` subdirectory — is the template
here, so `Bang.Frontend.TypeCheck` and `Bang.Backend.AbstractMachine` remain valid import
targets for existing consumers (no consumer-side import-line churn beyond what the hub already
absorbs).

### 2.1 `Bang/Frontend/TypeCheck/` split

None of these modules exist yet — they are named below in **dotted Lean-module form**
(e.g. `Bang.Tier.Old.New`), not slash-path form, precisely because they are proposed, not real
files (a slash-path claim asserts the file exists, which `tools/check-refs.py`'s fitness gate
correctly rejects as stale for a not-yet-created file — confirmed by triggering it once while
drafting this note). When the PATH executes a cut, the dotted name maps onto a subdirectory
exactly as the existing `Bang.Core.Semantics.Subst` precedent maps to
`Bang/Core/Semantics/Subst.lean`.

| proposed module | line-range provenance | imports (from §1.1 table only) |
|---|---|---|
| `Bang.Frontend.TypeCheck.Bidi` | 45–421 (bidirectional checker + `IVTy`/`ICTy`) | `Bang.Core.*` (unchanged upstream deps only — no TypeCheck-internal imports needed, this is the base layer) |
| `Bang.Frontend.TypeCheck.Infer` | 421–2491 (HM substrate + HKT helpers) | `Bang.Frontend.TypeCheck.Bidi` |
| `Bang.Frontend.TypeCheck.Elab` | 2491–3931 (elaboration + Modules-merge PURE half + LAWS discharge) | `Bang.Frontend.TypeCheck.{Bidi,Infer}` |
| `Bang.Frontend.TypeCheck.Corpus` | 5146–5770 (the `#guard` validation corpus) | the `Bang.Frontend.TypeCheck` hub — **NOT limited to the four public entry points**; also needs `checkPerformUnderCap`, `elabHClauses`/`elabProg`/`elabS`, `synthSC`/`synthSV`, `qualifyModule`/`qualifyDotAccess`/`qualifyModuleOwnImports`, `resolve`/`resolveTy`/`resolveTyG`/`resolveEffName`, `unifyRow`, `zonkInferC`, `runInferC`, `effOf`/`effNames`, `foldLetDecls`, `capOpSig`, `curryBind`, `anfSplit`, `isValueSurf`, and `showCTy` re-exported from the hub (verified §1.1 correction) — a substantially wider surface than the plan hypothesized |
| `Bang.Frontend.TypeCheck` (becomes the hub) | — | `public import` of `Bidi`, `Infer`, `Elab`; re-exports `checkProg` et al. as its public surface for the 4 existing consumers (§1.3) |

### 2.2 `Bang.Backend.AbstractMachine.*` split

| proposed module | line-range provenance | imports (from §1.2 table only) |
|---|---|---|
| `Bang.Backend.AbstractMachine.Stores` | 106–224 (`SStore`/`THeap`/`CStore`) | `Bang.Core.*` only |
| `Bang.Backend.AbstractMachine.EvalD` | 225–363 (the denotational `evalD`) | `Bang.Backend.AbstractMachine.Stores` |
| `Bang.Backend.AbstractMachine.Machine` | 363–544 (`Code`/`Stack`/`HStack`/`compile`/`exec`) | `Bang.Backend.AbstractMachine.{Stores,EvalD}` |
| `Bang.Backend.AbstractMachine` (becomes the hub) | — | `public import` of `Stores`, `EvalD`, `Machine`, **plus the proof sections kept in-place** (§4) |

**Note on the proof sections (545–6849):** per §1.2's answer, these sections consume the
executable layer only through the narrow `Stores`/`EvalD`/`Machine` vocabulary, so *in
principle* they could be extracted too. This note deliberately proposes leaving them in the hub
file for now — see §4 ("what deliberately stays") for the rationale; a finer split of the proof
sections themselves is future work this note does not size.

## 3 · Import-direction proof sketch

The binding rule, read directly from `tools/arch-check.sh` (comments lines 8–39, code lines
40–118):

```
RANKS:  Core = 0 (sink)  <  Frontend = Backend = 1 (siblings)  <  Meta/Witness/Reify = 2  <  Apex = 3
RULES:  (a) no module imports STRICTLY UPWARD (importer rank < imported rank is forbidden)
        (b) Frontend ⊥ Backend — the two rank-1 edges meet ONLY at Core (Frontend importing
            Backend, or vice versa, is forbidden regardless of rank)
LAYER:  path-derived — `Bang/<Tier>/...` decides layer, not a hand-maintained case map.
```

Checking every proposed edge in §2.1/§2.2 against this rule:

- All four new `Bang/Frontend/TypeCheck/*.lean` files are still under `Bang/Frontend/`, so
  `layer_of` maps them to `Frontend` (rank 1) exactly as `TypeCheck.lean` is today — **no rank
  change**. Same for all three new `Bang/Backend/AbstractMachine/*.lean` files under
  `Bang/Backend/` → `Backend` (rank 1).
- Internal edges (`Infer.lean` → `Bidi.lean`, `Elab.lean` → `{Bidi,Infer}`, `Corpus.lean` →
  the hub, `EvalD.lean` → `Stores.lean`, `Machine.lean` → `{Stores,EvalD}`) are all
  same-rank/same-tier (`Frontend` → `Frontend`, `Backend` → `Backend`) — same-tier imports are
  unrestricted by rule (a) (rank a < rank b is the forbidden case; a == b is fine, matching how
  `Bang/Core/Semantics/*.lean` siblings already import each other within `Core`).
- No proposed edge crosses `Frontend ↔ Backend` (rule (b)) — confirmed in §1.3, no file imports
  both today, and none of the proposed splits introduce such an edge (Frontend's split imports
  only other Frontend files + `Core`; Backend's split imports only other Backend files + `Core`).
- No proposed edge imports upward into `Meta`/`Witness`/`Reify`/`Apex` — all listed imports in
  §2.1/§2.2 stay within `Core` (rank 0, downward — allowed) or the same tier (rank 1).

**Verdict: every proposed edge is legal under the current `arch-check` rule as written.** No
change to `tools/arch-check.sh`'s `layer_of` case map is needed — `Bang/Frontend/TypeCheck/*`
and `Bang/Backend/AbstractMachine/*` both already match the `Bang.Frontend.*`/`Bang.Backend.*`
prefix patterns the script's `case` statement matches on (lines 48/50), because Lean dotted
module names preserve the directory path.

## 4 · Risk register

### `abbrev`/`notation`/`macro` crossing a proposed cut

Grepped directly (`^abbrev \|^notation\|^macro `, whole-file, both files — no `notation` or
`macro` declarations in either file):

| file | line | abbrev | crosses a proposed cut? |
|---|---|---|---|
| TypeCheck.lean | 37 | `CT` | No — falls at the very top, before the 45-line first header; stays in `Bidi.lean` alongside its first consumers. |
| TypeCheck.lean | 38 | `Ctx` | Same as `CT`. |
| TypeCheck.lean | 357 | `NCtx` | Inside 182–421 span → lands in `Bidi.lean` per the proposed 45–421 grouping; consumed by the HM substrate in `Infer.lean` → **crosses the `Bidi`/`Infer` cut**, needs `Bidi.lean` to export it and `Infer.lean` to import `Bidi.lean` (already in the import list, §2.1). |
| TypeCheck.lean | 444 | `Infer` | Inside 421–1536 → lands in `Infer.lean`, consumed only within the same span per §1.1 (no external hit) — does not cross a cut. |
| TypeCheck.lean | 1891 | `Slot` | Inside 1536–2491 (HKT helpers, grouped into `Infer.lean`) — consumed by elaboration (2491+, `Elab.lean`) → **crosses the `Infer`/`Elab` cut**, needs re-export. |
| AbstractMachine.lean | 116 | `SStore` | Inside 106–224 → `Stores.lean`; consumed by `EvalD.lean`, `Machine.lean`, and the in-place proof sections → **crosses into every downstream piece**, this is the load-bearing abbrev of the whole split — `Stores.lean` must export it cleanly. |
| AbstractMachine.lean | 152 | `THeap` | Same pattern as `SStore`. |
| AbstractMachine.lean | 214 | `CStore` | Same pattern as `SStore`. |
| AbstractMachine.lean | 406 | `Code` | Inside 363–544 → `Machine.lean`; consumed downstream by `Bang/Backend/{Wasm,U5bComplete}.lean` and the in-place proof sections. |
| AbstractMachine.lean | 410 | `Stack` | Same pattern as `Code`. |
| AbstractMachine.lean | 422 | `HStack` | Same pattern as `Code`; also the name the correspondence proofs (545+) are built around — highest-traffic abbrev in the file. |

**No `notation`/`macro` declarations exist in either file** — this eliminates the sharpest edge
of the incident-history risk (the `Membership ?m X` elaboration failure involved an imported
`abbrev` specifically; there is no `notation`/`macro` exposure here). Every `abbrev` above
crosses at least one proposed cut in the sense that it's *defined* in one piece and *consumed*
in a sibling — this is expected and mechanical (re-export via `public import`, same as
`Bang/Core/Semantics.lean`'s hub already does for its four siblings' `abbrev`s). The register
flags them so the execution PATH checks each one's elaborated type is IDENTICAL post-move (not
just "compiles") — the incident precedent was a *silent* behavior change, not a build error.

### `partial def`

**Zero `partial def` declarations in either file** (grepped, whole-file). No termination/wf
context risk from this category — a clean negative finding for the risk register.

### The `#guard`s

TypeCheck.lean's corpus region (5146–5770) and AbstractMachine.lean's diff-test battery
(3447–3592) are both compiled `#guard`s (per CLAUDE.md: "only compiled `lake build` #guards are
reliable"). Wherever they land post-split, they must remain in a module that still gets
compiled by `lake build` (not orphaned into a module excluded from the build) — the execution
PATH's Step-per-cut verification (§5) must include `just build` succeeding AND the guard count
being unchanged (grep-count `#guard` occurrences before/after each cut as an explicit
regression check, not just "the build is green").

## 5 · Cut order

Safest-first, each landing independently `just verify`-green before the next starts. **Revised
from the plan's hypothesized order**: §1.1's direct verification found the TypeCheck corpus is
NOT narrowly coupled (it calls 20+ internal names beyond the four public entry points), so it
does not lead — the `AbstractMachine.lean` stores extraction leads instead, being the only cut
in either file confirmed to touch a genuinely narrow, low-traffic dependency surface (simple
`abbrev`s over already-defined kernel types, not the machine's derived calculation):

1. **`AbstractMachine.lean` stores extraction** (`Stores.lean`, §2.2) — the #1 safest cut.
   `SStore`/`THeap`/`CStore` are simple `abbrev`s over already-defined kernel types
   (`Bang.EffectRow.Label`, `Val`, `Bang.OpId`/`Comp`), not derived through the machine's
   calculation, and the region (106–224) itself calls nothing outside `Bang.Core.*`. Verify:
   `just verify` green, guard-count and axiom-state unchanged (`just axioms`).
2. **`TypeCheck.lean` corpus extraction** (`Corpus.lean`, §2.1) — demoted from the plan's
   assumed #1 slot after direct verification (§1.1) showed real coupling to ~20 internal names
   across elaboration/Modules/LAWS. Still tractable — the corpus's own logic doesn't grow, only
   its import list does — but requires the hub (`TypeCheck.lean`) to re-export a wider surface
   than `checkProg`/`checkAndLower`/`parseProg`/`buildEnv` alone, which raises the odds an
   `abbrev` (`CT`/`Ctx`/`Infer`, §4) crosses the cut in a way that needs the same
   identical-elaborated-type check as the AbstractMachine abbrevs. Verify: `just verify` green,
   `#guard` count in `Corpus.lean` == pre-cut count in that line range, axiom state unchanged.
3. **`AbstractMachine.lean` evalD + machine extraction** (`EvalD.lean`, `Machine.lean`, §2.2) —
   depends on step 1 landing first (imports `Stores.lean`). Higher risk than steps 1–2 because
   `evalD`/`compile`/`exec` are the objects the *proof* sections (kept in-place, §4 below) reach
   into — a botched extraction here breaks the in-place proofs even though no proof code moved.
   Verify: same triple, PLUS confirm `just axioms` shows the SAME headline theorems' axiom sets
   as pre-cut (not just "some axiom set") — the proof sections are the highest-value code in the
   repo and must not silently degrade.
4. **`TypeCheck.lean` Bidi/Infer/Elab three-way split** (§2.1) — deferred to last among the
   TypeCheck cuts because it is the least externally-motivated (no external consumer touches
   these internals, §1.1) and the internal coupling between the three pieces is the densest in
   either file (HM substrate feeds elaboration feeds LAWS discharge, all mutually referential).
   This is real work with real risk and comparatively low external payoff — candidate for
   "do it only if the file-size pain persists after cuts 1–3," not a must-do in the same PATH.

Each landing's success criterion, restated: `just verify` (selfcheck + `lake build` + audit)
green, `docs/notes/README.md`/`CLAUDE.md` untouched by the code move itself (docs update
separately), `#guard`/theorem-count parity confirmed by grep before/after, and `just axioms`
output byte-identical for every headline theorem the cut's region touches.

## 6 · What deliberately stays

- **The proof sections of `AbstractMachine.lean` (545–6849, ~6300 of 6849 lines) stay together
  and stay in the hub file for now.** Rationale: per §1.2, "the calculation is correct" (2158+),
  the diff-test battery (3447+), and the D1-A bridge (3592+) build on each other *sequentially*
  within the file — the calculation IS the module, in the same sense CLAUDE.md's invariant #4
  ("the machine is an output of the calculation, never hand-designed") treats derivation and
  proof as one artifact. Splitting these apart is a substantially harder, finer-grained
  investigation than this note attempts (see §2.2's note) — proposing it without that
  investigation would be exactly the "trivial extraction" the plan's scope explicitly warns
  against.
- **TypeCheck.lean's `Bidi`/`Infer`/`Elab` three-way split (§2.1, cut 4)** is proposed but
  explicitly sequenced last and flagged as possibly not worth doing — the internal coupling is
  the densest of any region in either file and the payoff (no external consumer touches these
  internals) is the lowest of the four cuts.
- **Neither file's `import Bang.*` list needs to change** for consumers — the hub-file pattern
  (`Bang/Core/Semantics.lean` precedent) means `Bang/Frontend/TypeCheck.lean` and
  `Bang/Backend/AbstractMachine.lean` continue to exist as thin re-exporting hubs, so the 4 + 7
  existing consumer files (§1.3) need zero import-line changes.

## 7 · Closing note

**This note is a proposal — the split needs an ADR + operator sequencing after the parked LR
census unit lands.** The census unit at branch `feat-lr-carrier-stackinc-wip` touches
`Bang/Meta/BinaryLR.lean`, which — while it does not import `Bang.Backend.AbstractMachine`
directly (§1.3, confirmed no direct edge) — depends structurally on `Bang.Core.Soundness`,
which is built to agree with the D1-A bridge (`evalD_agrees_source`) proven in
`AbstractMachine.lean`'s 3592+ region. Splitting `AbstractMachine.lean` (especially cut 3,
§5) while that branch is unmerged invites rebase pain the moment it lands, even without a
direct import-edge collision. Sequence: let the census unit land (or get explicitly
abandoned) first, then open a PATH for cuts 1–3 (cut 4 optional/deferred per §6), each cut its
own commit gated by the verification triple in §5.
