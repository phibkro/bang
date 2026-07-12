<!-- note-status: skeleton — ◊6 paper draft, NOT full prose -->
# Paper 2 skeleton — *A Binary Logical Relation for Graded Effect Rows with Identity Dispatch*

> **One-sentence claim.** A step-indexed **biorthogonal binary logical relation** for a graded
> call-by-push-value language with effect handlers, whose continuation relation is **answer-
> typed** (`KrelS`) and whose central design tension — *typing is by label, dispatch is by
> identity* — is resolved by a **typed + static (capability) pivot** (ADR-0045) that dissolves
> the resume-through-a-wrap edge structurally rather than proving around it.
>
> **Riskiest related-work overlap.** Biernacki et al. "Handle with care" (POPL'18) already give
> a step-indexed biorthogonal LR for algebraic effects and handlers with effect rows. Our delta
> is *not* "an LR for handlers" — it is (a) the **CBPV-arrow adaptation** of the continuation
> relation (Biernacki's arrow is a *value* type; ours is a *computation* type, so `Krel` needs a
> peeling arrow clause — ADR-0038), (b) the **identity/lexical dispatch** discipline and the
> build-proven divergence that motivates it (ADR-0052), and (c) the **answer-typed `KrelS`** re-
> index that makes the typed-static kernel's `staticSplit` dissolve the `no-recovery` edge. The
> paper must lead with these three or it reads as a re-implementation of Biernacki.

Status: SKELETON. Outline + precise claims + exact Lean theorem names/files/**real** axiom sets
+ related-work map + honest what-remains. Not prose. Target: **CPP** (operator-ruled, ADR-0096
④), POPL/ICFP if the residual ever closes. All theorem citations re-checked against the repo at
the base sha via `just axioms` (census in §7 — **21 clean · 6 flagged · 53 sorries** at
`62335411`). **Note (load-bearing honesty): the two LR headlines this paper is named for —
`lr_sound` and `lr_fundamental` — are FLAGGED (`sorryAx`), and the operator has ruled the `lr_*`
unit CLOSED-AS-PARKED** (five machine-arbitrated rounds hit a statement-level answer-determinacy
wall, ADR-0096 amendment ④). This paper is CPP-framed with that ONE named residual front and
centre; §8 states exactly what is closed and what is the single parked residual.

---

## 0. Metadata / framing

- **What an LR buys here.** The compiler paper (Paper 1) proves *one-directional* forward
  simulation. Two-sided **contextual equivalence** (`c₁ ≈ c₂`: interchangeable in every context
  `C`) is a different theorem — it is what licenses source-level equational reasoning and
  optimizations, and it needs the ⊤⊤-closed biorthogonal LR (ADR-0035). This paper is that LR.
- **The relations** (`Bang/LR.lean`, `Bang/Meta/*`): `Vrel` (values), `Crel`/`CrelK`
  (computations, biorthogonal), `Krel`/`KrelS` (continuations/stacks, answer-typed), `Srel`
  (resumptions). Step-indexed `Nat → Prop`; biorthogonality = `Crel` co-behaves against every
  `Krel`-related stack, `Krel` closes back over `Crel`/`Srel` (the ⊤⊤-closure).
- **The three genuinely-new pieces** (defend in §5/§6):
  1. **The CBPV-arrow peeling clause** (ADR-0038) — a computation-typed arrow forced a
     *peeling/existential* `Krel(arr)` clause + returner-restricted empty-stack adequacy; both
     "pure" forms (extending, peeling-alone) were **build-refuted**.
  2. **Typing-by-label / dispatch-by-identity**, and the **typed-static pivot** that resolves
     the resume-edge by construction (ADR-0045/0052/0055).
  3. **Answer-typed `KrelS`** — the continuation relation re-indexed by the type structure
     (`Vτ/Cτ/Tτ`) so `staticSplit`'s cap-counting *dissolves* the `◊4.5b` MISS edge
     (`krelS_staticSplit_decomp`), replacing the untyped LR's missing-recovery hole.

---

## 1. Introduction — the two gradings and the dispatch gap

- **Hook.** In a language where "your paradigm is which effects are in your row," program
  equivalence must respect *both* gradings: the effect row `φ` (a join-semilattice) and the QTT
  multiplicity `q`. The LR's index set is the type structure, so the relation *is* graded.
- **The dispatch gap (the paper's spine).** A capability's **type** tracks its *label* `ℓ`
  (what the effect row sees); its **runtime dispatch** matches its *identity* `n` (which
  installed handler it names). Typing-by-label / dispatch-by-identity is the seam every hard
  proof in this development turns on. The LR must relate programs that agree on labels but whose
  identity-dispatch could differ — and get it right.
- **Why the naive (dynamic, untyped) LR fails.** Under dynamic nearest-label dispatch, a
  captured continuation can contain a *non-catching* handler (the `splitAt` walk-past), which
  puts an un-recoverable frame into the relation — the "resume-through-a-wrap edge"
  (ADR-0043). ADR-0045's finding: **the edge exists *because* dispatch is dynamic.** Pivot to
  static/identity dispatch and it dissolves structurally.
- **Contribution list** = §0's three pieces. Plus the honest ◊4/◊4.5 seam narrative (§4): what
  lands axiom-clean and what is a single named residual.

## 2. The relations — biorthogonal, step-indexed, graded

- **2.1 Substrate.** Plain `Nat`-step-indexed `Vrel/Crel/Krel/Srel` with the `▷` later-modality
  where resumption/recursion needs it. Biernacki-style biorthogonality (⊤⊤). Cite
  benton-hur-icfp09 (biorthogonal adequacy), pitts-step-indexed, ahmed-esop06 (identity
  extension).
- **2.2 The value relation** `Vrel n A`: base types flat; `U φ C` drops to `Crel`; `μ` drops the
  payload to index `n` (the ▷ site).
- **2.3 The computation relation** `Crel = CrelK` (answer-typed): `c₁ ~ c₂` iff for every
  `Krel`-related stack pair, the two configs co-converge. Biorthogonal.
- **2.4 The continuation relation** `Krel/KrelS`, **answer-typed** (`F qo Ao` returner answer,
  ADR-0038 restriction). This is the re-indexed relation (ADR-0045 axis 2) — the substrate is
  unchanged from the untyped LR; only the index set moves to `Vτ/Cτ/Tτ`.

## 3. The CBPV-arrow adaptation (ADR-0038) — a build-arbitrated clause

- **3.1 The problem.** Biernacki makes the arrow a *value* type (his `K⟦·⟧` has no arrow
  clause). Our kernel makes `arr q A B` a **computation** type, so `Vrel` cannot host it and
  `Krel`'s F-keyed return-half is vacuous at `arr` — the `lam`/`app` congruence cannot close.
  This is a CBPV *adaptation*, not a Biernacki transcription.
- **3.2 Both pure forms fail (the load-bearing part — a reviewer-facing story of build-as-
  arbiter).**
  - **Extending** (`Krel(arr) ⟺ ∀ Vrel w, Krel(B)(appF w :: K)`) — refuted by `compat_app`:
    the builder demands a **double-`appF`** that never bottoms out (non-terminating).
  - **Peeling alone** — refuted by `krel_nil_succ`: the empty stack `[] ≠ appF`-capped, so the
    existential fails, yet `Krel(arr) [] []` is semantically true-vacuous.
- **3.3 Resolution = peeling + F-restriction.** `Krel n (arr q A B)` holds iff the stacks are
  `appF`-capped with a closed `Vrel`-related argument and `Krel`-related codomain tails
  (existential/peeling form). Empty-stack adequacy restricted to returners (`C = F q A`),
  because an arrow-typed *whole program* is a bare `lam`, stuck at `[]` ⇒ `¬Converges` ⇒ `⊑`
  vacuously true at arrow type. This is **more faithful**, not a hack — the excluded contexts
  observe arrow terms vacuously. Landed sorry-free at `f0aebb1` (`krel_appF_intro`, `compat_app`,
  `compat_lam`).

## 4. The ◊4/◊4.5 seam — what lands clean, what defers (ADR-0039)

**The honest architecture section.** The LR foundation lands sorry-free for the **non-▷
fragment**; the cohesive **▷-subsystem** defers to ◊4.5.

- **4.1 What is proven ▷-free (◊4).** All value cases + `ret`/`letC`/`force`/`case`/`split`/
  `lam`/`app`/`handleThrows`. `throws` (zero-shot abort, no resume) closes end-to-end — the
  caught op is consumed *inside* the body's biorthogonal run, needing no `Krel` handled-op
  clause.
- **4.2 What defers (◊4.5) and why.** The ▷-subsystem — `fold`/`unfold` (μ recursion), `up`
  (performing under a handling stack), resumptive handlers (`handleState`/`handleTransaction`,
  RESUME = reinstall frame + continue at the next index). The **build-confirmed root cause**:
  our relations are plain `Nat → Prop`, but μ + resume soundness needs the **IxFree `∀k≤n`
  Kripke-monotone** reading, and **no uniform monotonicity retrofits** — `Krel`'s return-half
  needs `Vrel`-covariant while `Srel`'s resume clause needs `Vrel`-contravariant (same
  relations, opposite directions; the `*_mono` block reverts as false). Cross-checked against
  ahmed-esop06 (downward-closed + direct step-counting) — to have *both* biorthogonal-effects
  (Biernacki) and iso-recursive-μ, the `∀k≤n` wrapping must be designed in, not retrofitted.
- **4.3 Honest scope.** The deferred fragment is **not a corner case** — it is the resumptive-
  effects + recursive-data half (state, STM, reactive, recursive ADTs). ◊4.5 is the *next unit*,
  designed with the Kripke phrasing built in.

## 5. The typed-static pivot — the resume-edge dissolves (ADR-0045/0052/0055)

- **5.1 The two coupled axes.** (1) **Static/capability dispatch**: `up ℓ op v` +
  `splitAt`-search → `perform cap op v` + `staticSplit` (dispatch *counts a de-Bruijn/identity
  capability into the runtime stack*; it never tests `handlesOp` to decide skipping). (2)
  **Typed LR**: re-index from raw untyped stacks to `Vτ/Cτ/Tτ` (the Nat-step + `▷` substrate
  unchanged).
- **5.2 Dispatch is lexical — the build-proven divergence (ADR-0052).** On a well-*typed* same-
  label-shadowing program:
  ```
  handle (state 1 → 10) ( handle (state 1 → 20) ( perform cap=1 "get" ) )
    kernel (cap dispatch):  10   ← cap=1 names the OUTER handler it was bound at  (LEXICAL)
    evalD  (dynamic):       20   ← nearest enclosing label-1 handler              (DYNAMIC)
    both rfl — a genuine, build-proven semantic divergence
  ```
  Decision: **bang's dispatch is LEXICAL** — the cap names *one specific* handler regardless of
  what's dynamically nearest. This is the concrete motivating example for the pivot (the LR-paper
  analog of Paper 1's store-shadow witness).
- **5.3 Identity dispatch + global freshness (ADR-0054/0055).** A capability is an ordinary
  value `vcap n ℓ`; `perform` dispatches by identity match (`splitAtId n`), not label search.
  Identity is global-fresh (monotonic Config counter). The **cross-extent collision** the naive
  depth-based scheme admitted (`progB`: an escaped cap re-resolves to a same-depth impostor →
  `done` reading the wrong handler's state) is made **unrepresentable** by never-reused ids →
  an escaped cap resolves to ITS handler or to NOTHING (stuck, fail-loud). Witnesses:
  `Bang/Witness/…` (progB → STUCK on the reworked kernel).
- **5.4 `KrelS` dissolves the MISS edge — the payoff.** Under `staticSplit` (cap-counting, no
  `handlesOp` walk-past), the ◊4.5b MISS edge dissolves **by construction**: at cap=0 (nearest
  handler, the common case) the captured continuation is handler-free structurally; at cap>0
  (resume-into-outer) the strip relocates but is **cap-indexed** — the static count *is* the
  answer-type witness, so it never reintroduces the untyped LR's missing recovery.
  `krelS_staticSplit_decomp` (the `:1590` sorry deleted); one bounded cap>0 resume-relocation
  residual remains (§8).
- **5.5 Why the LR cap-discipline is CONTEXTUAL (build-refuted framings).** Two naive framings
  were refuted before the faithful one: (A) `Val.CapClosed` on LR values — OVER-STRONG (a
  returned `vthunk (perform 0 …)` has live context-relative caps); (B-naive) `VrelK` shiftCap-
  stability same-stack — FALSE (`shiftCap c` dispatches differently). **FAITHFUL: the shift ↔
  handleF-extension CANCELLATION** — `shiftCap c` in `handleF h :: K` dispatches identically to
  `c` in `K` (+1 cap and +1 handler cancel), threaded at the `compatK_handle*` refocus.

## 6. The NoWrapMiss resolution and the typed+static seam

- **6.1 NoWrapMiss.** The scoped-seam residual (`krelS_splitAt_decomp` MISS) — `NoWrapMiss`
  landed with ONE sorry; sorryAx-zero needs `CrelK` re-indexed by `HasCTy`/`HasStack` (typed-
  CrelK). This is the current live edge of the ◊4.5b work and should be stated as such, not
  papered over.
- **6.2 The typed+static seam narrative.** The pivot (ADR-0045) is the resolution of a fork
  ADR-0043 had declared "verified-final" for the *dynamic* kernel: the resume-edge was an
  artifact of dynamic dispatch, and a static-link kernel dissolves it — build-gated
  (`static-dispatch-spike@b1330db`, `setrow-tension-spike@f92a504`), preserving set-rows (the
  cap is a *separate* `Nat` absent from the row premise; the row stays `Finset Label`, invariant
  #2 untouched) with no rank-2 polymorphism. This refutes the Koka-evidence-vector / named-
  handler-polymorphism pressure.

## 7. Verification / reproducibility — the axiom census (checked at base sha)

Gate: `lake env lean Bang/Audit.lean` (PASS ⟺ each headline ⊆ `{propext, Classical.choice,
Quot.sound}`; any `sorryAx` = FAIL). **Real** axiom sets (reproduced from the census):

| theorem | file:line | axiom set | status |
|---|---|---|---|
| `lr_sound` | `Spec.lean:237` | `propext, sorryAx, Classical.choice, Quot.sound` | **FLAGGED** |
| `lr_fundamental` | `Spec.lean:268` | `propext, sorryAx, Classical.choice, Quot.sound` | **FLAGGED** |
| `lr_fundamental_closed` | `Spec.lean:278` | `propext, sorryAx, Classical.choice, Quot.sound` | **FLAGGED** (inherits from `lr_fundamental`) |
| `zero_usage_erasable` | `Spec.lean:165` | `propext, sorryAx` | **FLAGGED** |
| `seq_unit` | `Spec.lean:294` | `propext, Classical.choice, Quot.sound` | **CLEAN** (discharged — see §8.5) |
| `effect_sound` | `Spec.lean:191` | `sorryAx, Trace, traceWithin, Source.evalTrace` | **FLAGGED** (bare `sorry` + carrier axioms) |
| `no_accidental_handling` | `Spec.lean:60` | *none* | clean (structural — the ADR-0018 licensor) |
| `rowinst_requires_disjoint` | `Spec.lean:49` | *none* | clean |

**Census SoT** (CONTEXT.md generated proof-state block, `62335411`): **21 clean · 6 flagged ·
53 sorries.** The 6 flagged: `lr_sound`, `lr_fundamental`, `lr_fundamental_closed`,
`handler_compiles` (Paper 1), `effect_sound`, `zero_usage_erasable`. Note `seq_unit` is NOT in
the flagged set — it was part of the 20→21 clean move (§8.5).

## 8. What is NOT proven (the honest scope section — mandatory)

- **8.1 `lr_sound` carries a single named residual** (`Spec.lean:237`, `[…, sorryAx, …]`). The
  proof is complete up to ONE `sorry`: the **reshape↔raw-focus bridge**. The biorthogonal
  closure observes the RAW focus `(g, C, cᵢ)`, but `converges_plug_iff` observes the CAP-
  SUBSTITUTED, RESHAPED config `(handlerCount C, canonStack C cᵢ, capSubstInto C cᵢ)`; no `CrelK`
  instantiation reaches the substituted focus when `cᵢ` uses `C`'s caps (i.e. exactly the
  effectful programs). `AdequacySpike.adequacy_bridge_attempt2` build-confirms the bridge closes
  IFF `capSubstInto C cᵢ = cᵢ` — the labelling-vs-closure cap-rep seam (OPEN_QUESTIONS Q22 /
  ADR-0058 route-1). This is a **definition-shape concern**, not a grind. State it as the one
  open architectural residual of `lr_sound`. **Operator ruling (2026-07-11, ADR-0096 amendment
  ④): this `lr_*` residual is CLOSED-AS-PARKED** — five machine-arbitrated rounds refuted every
  route (both the def-conclusion-strengthening and the fuel-indexed re-index survivors fail at
  the same inter-derivation ANSWER-DETERMINACY wall, a statement-level gap not a proof technique).
  The paper goes **CPP-framed with this ONE named residual** front-and-center; the resume bar is
  "answer-determined-by-construction only." §8.5's `seq_unit` is the *positive* boundary of this
  exact bridge (the cap-inert case closes; the cap-live case is the wall).
- **8.2 `lr_fundamental` is partial** (`Spec.lean:268`, wired to `crelK_fund`). THROWS closes
  end-to-end; documented `sorry`s remain ONLY in the **state/transaction producer arms** (the
  `krelS_append` + ▷-metering research crux). So `lr_fundamental`'s `sorryAx` traces *solely* to
  that one crux. `lr_fundamental_closed` is the `Γ=[]` corollary and inherits the flag.
- **8.3 `zero_usage_erasable` (grade-0 coeffect erasure) blocks on `lr_fundamental`.** It is
  irreducibly two-sided (two distinct fillers ⇒ `≈`-equal computations) and routes through the
  LR; its `sorry` is downstream of §8.2. Its *definition* `NotEvaluated` is axiom-free.
- **8.4 `effect_sound` is a bare `sorry`** (`Spec.lean:191`) with additional carrier axioms
  (`Trace, traceWithin, Source.evalTrace` — at the base sha). "Static grade over-approximates
  every observed trace" is stated, not proven. Do not claim it. (A re-foundation that replaces
  the three carrier axioms with definitions, then discharges the `sorry`, is in-flight in a
  sibling lane; if it lands, re-run `just axioms` and update this row — but until the committed
  sha shows it clean, report it as flagged.) It is a *sibling obligation*, separate from the LR
  spine — likely cut from this paper's claims (§11 item 4).
- **8.5 `seq_unit` is now DISCHARGED — axiom-clean** (left-unit law for sequencing,
  `Spec.lean:294`, `[propext, Classical.choice, Quot.sound]`; was `sorryAx` at the prior census).
  Part of the 20→21 clean move. The proof (`seq_unit_proof`, `Meta/LR.lean:1185`) is purely
  OPERATIONAL — no LR machinery: both foci `seqComp (ret v) c` and `c` reshape under the same
  observation context `C` to configs that share stack + counter and differ only by a 2-step head
  reduction, closed through `converges_plug_iff` in both `⊑` directions
  (`seqComp_capSubst_run`). **Methodologically load-bearing for §8.1:** this reshape machinery
  (`RunPlugReshape.capSubstInto`/`canonStack` + `converges_plug_iff`) is *exactly* the
  raw↔reshaped-focus bridge that `lr_sound`'s residual turns on — `seq_unit` demonstrates the
  bridge closes for the cap-inert case (`capSubstInto C c = c` when `c` uses none of `C`'s caps),
  which is the boundary §8.1's `capSubstInto C cᵢ = cᵢ` names. It is a *worked instance* of the
  open `lr_sound` bridge, not an unrelated lemma — a good figure for the paper. (`group_recovers`
  was RETIRED, ADR-0032 — false-as-stated + vacuous; v1 rollback is the transaction handler,
  demonstrated by the Surface `ledgerAbort` #guard, not a spine theorem.)
- **8.6 W1/W2 `lr_sound` deferral.** The two-witness `lr_sound` closure (the deferred W1/W2
  legs of the ◊4.5 grind) is not landed; §8.1's bridge is the gating residual.
- **8.7 The ▷-subsystem (§4.2) is the bulk of the deferred work.** μ + resume + resumptive
  handlers need the IxFree `∀k≤n` Kripke re-phrasing. This is designed-in ◊4.5, not done.

## 9. Related work map (positioning — defend the delta for each)

| work | what they do | our delta |
|---|---|---|
| **Biernacki, Piróg, Polesiuk, Sieczkowski, "Handle with care"** (POPL'18) | first step-indexed biorthogonal binary LR for algebraic effects + handlers, effect rows + polymorphism | our template — but their arrow is a *value* type (no `Krel` arrow clause); ours is CBPV-computation, forcing the peeling clause (§3); and we add identity/lexical dispatch (§5) + the answer-typed `KrelS` that dissolves the resume edge |
| **Benton & Hur** (ICFP'09, biorthogonal cross-language adequacy) | ⊤⊤-closed relational model for compiler correctness | the biorthogonal substrate we reuse; we apply it to a *graded, handler* source and use it for the source equational theory (not the compile hop — that's forward sim, Paper 1) |
| **Ahmed** (ESOP'06, step-indexed relations for recursive/impredicative types) | `∀i≤j` downward-closed relations, direct step-counting | the μ-recursion index discipline; our ◊4.5 root-cause analysis is a direct comparison (why biorthogonal-effects + iso-recursive-μ needs the `∀k≤n` wrapping) |
| **Pitts** (step-indexed / operational LRs) | foundational step-indexing | substrate citation |
| **Zhang & Myers, "Abstraction-safe effect handlers via tunneling"** (POPL'19) | tunneling / no-accidental-handling | our `no_accidental_handling` (0-axiom, structural) restates this faithfully in the label-indexed CK machine (ADR-0024) |
| **Lexa / Effekt (lexical/second-class capabilities)** | lexical handler dispatch, capabilities as evidence | our identity dispatch *searches* (`splitAtId`) where they *dereference*; the typed-static pivot adopts the lexical discipline (a `perform` must have its handler in scope at its author site) — but keeps dynamic dispatch as a tested shell macro |
| **Koka / evidence passing** (Xie–Leijen) | evidence vectors for dispatch + compilation | build-refuted here as a *typing* pressure (§6.2): our cap is a separate `Nat`, rows stay `Finset`, no evidence vector / rank-2 polymorphism in the row |
| **Torczon et al.** (OOPSLA'24, graded/QTT) | the grading we index the LR by | `zero_usage_erasable` is Torczon's grade-0 erasure as an LR corollary (§8.3) |

## 10. Venue candidates (fit notes — operator picks, do NOT commit)

**Operator ruling (ADR-0096 amendment ④): the `lr_*` unit is CLOSED-AS-PARKED — this paper
goes CPP-framed with one named residual, NOT held for POPL-after-close.** The residual is a
*statement-level* answer-determinacy wall five machine-arbitrated rounds could not route past,
not a proof-effort backlog, so "wait until it closes" is not the plan.

- **CPP — the ruled venue.** Frame the paper as the *machine-checked LR construction + the seam
  analysis* (the build-as-arbiter methodology, §3.2/§5.5, is a CPP-shaped contribution) with the
  §8.1 residual stated as the ONE open architectural obligation, and `seq_unit` (§8.5) as the
  positive boundary of that exact bridge. The honest §8 residuals are acceptable at CPP as
  stated open obligations. Lowest-risk and the operator-ruled target.
- **POPL** — the natural home for a *closed* binary LR / contextual-equivalence result for a
  novel effect-dispatch discipline (the Biernacki lineage is POPL). Off the table until the
  answer-determinacy wall is dissolved by construction (the resume bar: an answer-in-the-frame,
  kernel-adjacent re-statement — no background lane is chasing it). Record as the *if-it-closes*
  aspiration, not the plan.
- **ICFP** — a middle option: good fit for the CBPV-arrow adaptation (§3) as a build-arbitrated
  design story + the typed-static pivot, more tolerant of a "here is the design + what closed"
  framing than POPL. Still wants the core LR closed, so CPP is the safer read given the ruling.

## 11. What remains to write (author TODO before submission — proof AND prose)

1. **Write `lr_sound`'s residual AS the CPP contribution, not as a TODO to close.** Given the
   ADR-0096 ④ parked ruling (§8.1/§10), the prose leads with the reshape↔raw-focus bridge (§8.1)
   and the labelling-vs-closure cap-rep seam (Q22) as the *one named, honestly-bounded* open
   obligation — the five-rounds refutation IS the finding. Pair it with `seq_unit` (§8.5) as the
   worked positive boundary (cap-inert closes; cap-live is the wall).
2. **`lr_fundamental`'s state/txn arms** (§8.2) — the `krelS_append` + ▷-metering crux, inside
   the ◊4.5 ▷-subsystem (§4.2), needs the IxFree Kripke re-phrasing. Also parked; state it as a
   sibling residual, not a pre-submission blocker under the CPP framing.
3. Full prose for §3 (the two refuted arrow forms as a worked build-arbitration narrative — the
   paper's cleanest "the build is the arbiter" story).
4. Decide whether `effect_sound`/`seq_unit` (§8.4/8.5) are in-scope contributions or explicitly
   out. `seq_unit` is now a *proven, axiom-clean* lemma and is the best figure for the §8.1
   bridge — keep it in. `effect_sound` is a separate flagged sibling obligation — likely cut.
5. A figure for the §5.2 lexical-dispatch divergence and the §5.3 collision witness (two-column
   traces), mirroring Paper 1's store-shadow figure — the two papers share the "typing-by-label /
   dispatch-by-identity" gap and should cross-reference it. Add a `seq_unit` reshape-bridge
   figure (§8.5) as the positive companion to the §8.1 residual.
6. ~~Reconcile venue choice with the ◊4.5 landing timeline.~~ **Ruled: CPP-with-one-residual**
   (ADR-0096 ④, §10). Remaining author work: make the residual read as a contribution boundary,
   not an apology.
