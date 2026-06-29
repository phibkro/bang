# 0057 — The non-escape discipline: answer-type label-freedom at the kernel (B-occ)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: ADR-0056 recorded that the language is unsound — a capability can escape its handler and
  get stuck in a well-typed-at-⊥ program (`progB`), because **typing is by LABEL, dispatch is by
  IDENTITY**, and the ⊥-row gate cannot see the identity-escape. This ADR surveys how effect-handler /
  capability languages prevent capability/handler-reference escape and recommends the fix. The escape in
  `progB` is concretely a **value carrying the handled label `ℓ` out of the handler in its result type**
  (`U {1} (F 1 unit)` returned past the `state 1` handler — `ℓ=1` rides as a *latent* effect inside a
  thunk). The literature's monomorphic, kernel-local answer is the **lexically-scoped-handler discipline:
  the handled label must not occur in the handler's answer type** (option **B-occ**). This makes `progB`
  UNTYPEABLE at the kernel, closes the inc-5 diagonal *by construction*, needs **no polymorphism, no 6th
  primitive, no new judgment** — a side-condition premise on the 3 `handle` typing rules — and is the
  monomorphic projection of the principled "right answer" (Koka's rank-2 scoped named handlers / Effekt
  System-C capture sets), which BANG can adopt post-v1 when polymorphism lands (ADR-0027). **RECOMMEND
  B-occ now; System-C capture-tracking as the named post-v1 upgrade; surface-second-class as the cheaper
  fallback that gives up kernel soundness.**
- **Refines**: 0056, 0054
- **Depends-on**: 0056, 0055, 0054, 0030, 0027, 0023
- **See-also**: 0016, 0026, 0028, 0001, 0018

## Status

Accepted (2026-06-26). Operator ratified B-occ ("build-confirm first") per the ADR-0056 ruling; the
build-confirm (`bocc-spike`, the `BoccSpike` probe @ `39455a7`, axiom-clean ⊆ the gate set) returned
**GO** on all four load-bearing claims — see *Build-confirm result* below. **Phase 1 LANDED axiom-clean**
(`bocc-spike` @ `075f894`, 2026-06-26): the kernel premise + `LabelOccurs` (a `Prop`, no `Decidable` footprint)
+ regression lemmas (`escapeB_not_typeable` — the bug witness untypeable for ANY `EffSig`, purely structural;
`safe_handle_typeable`). Fixups: Metatheory ~43 / Operational 0 / Compat 5 (Compat unverified pending the LR
re-key). The standalone dissolution WALLS (Build-confirm #3) — B-occ *enables* inc-5's diagonal, doesn't replace
it; phase 3 (LR threading) follows the inc-5 re-key. The witness `progB`
(`DiagonalFalsifyProbe` / `IdentityCollisionProbe` / `CapEscapeWitness`) is the regression oracle:
whatever is ratified must make `progB` untypeable or un-elaboratable, then the diagonal
(`HasConfigTy ⊥ ∧ VcapFree → NonEscape`) closes.

## Context

### The gap (from ADR-0056), stated structurally

`progB = letC (handle (state 1) (ret (thunk (perform (vvar 0) "get" unit))))`
`             (handle (state 1) (force (vvar 1)))`

The inner `handle (state 1)` binds a capability `Cap 1` (at de Bruijn 0); its body **returns a thunk**
`thunk (perform (vvar 0) "get" unit)` that closes over that capability. The thunk's type is
`U {1} (F 1 unit)` — the handled label `1` rides **latently** inside the `U`. The handle discharges `1`
from the body's *effect row*, but the *result type* `A = U {1} (F 1 unit)` still carries `1`. So a value
that needs handler-1 escapes handler-1's dynamic extent, is forced under a fresh same-label handler
(id 1 under global-fresh, ADR-0055), and `splitAtId [handleF 1] 0 = none` → **stuck**, in a program that
types at ⊥ (both effects are label-1).

```
ROOT (ADR-0056):  typing sees LABELS (ℓ),  dispatch matches IDENTITIES (n).
ESCAPE CHANNEL:   the handler's RESULT TYPE A — a value leaves the handler carrying the handled
                  label ℓ, either directly (A = Cap ℓ) or latently (A = U {…ℓ…} C).
WHY THE GATE MISSES IT:  the ⊥-row gate only checks ℓ is discharged SOMEWHERE; it never checks the
                  escaping VALUE doesn't still name the discharged handler.
```

Two facts pin the channel:
- `HasVTy.vcap` (Syntax.lean:71) types *any* `vcap n ℓ : Cap ℓ` unconditionally — typing is
  cap-identity-blind (this is why `VcapFree` is a separate diagonal precondition).
- **The answer type is the only EXIT channel** — and (build-confirmed, bocc-spike) NOT because cells are
  `int`: that wording was imprecise. Only `handleTransaction` cells are int-pinned (`Syntax.lean:237`);
  `handleState`'s stored state is general type `S` (`Syntax.lean:208`) and could itself be cap-carrying.
  The real reason is structural: **handlers DISCARD their frame and stored state on pop**
  (`Operational.lean:229`: `⟨handleF h :: K, ret v⟩ ↦ ⟨K, ret v⟩`, identity-return), so the only value
  crossing outward is `v`, typed at the answer type `A`. A cap stored in a state cell exits only via
  `get`→answer-type (dispatch reinstalls the frame) and is then caught by its OWN label's B-occ premise.
  No store/closure bypass exists. This is what makes a single answer-type side-condition sufficient.

### Why this is the same failure shape as ADR-0053 / ADR-0054

An *assumed* soundness rationale, build-refuted. ADR-0054 asserted escape was "ruled out by the EXISTING
`LWT` non-escape gate, NOT by second-class thunks." ADR-0056 build-refuted that: the gate
(`NonEscape`-as-`FocusResolves`, `preservation_returnEscape_TODO`) only checks *resolves-to-something*,
never *the escaping value names a live handler*. The intent of ADR-0054 was right ("ruled out by
typing"); the **missing typing rule** is what this ADR supplies.

## Literature survey (how neighbour languages prevent capability/handler-reference escape)

Eleven mechanisms, grouped by family. `TYPE` = enforced in the type system; `SURFACE` = scope/elaborator
check; cost = what expressiveness or machinery it buys with.

| # | mechanism / source | enforcement | core move | cost |
|---|---|---|---|---|
| 1 | **Effekt 2020** second-class blocks (Brachthäuser et al, POPL'20) | TYPE | blocks (carry capabilities) **cannot be returned/stored**; value/block type split | no first-class functions |
| 2 | **Effekt System C / boxing** (Brachthäuser-Schuster-Lee-Boruch-Gruszecki, OOPSLA'22) | TYPE | `box`/`unbox`: a boxed block's type tracks a **capture set** `at {…}` (a coeffect); first-class recovered, re-handleable where caps are back in scope | capture-set coeffect on thunk types |
| 3 | **Koka first-class named handlers + scoped effects** (Xie-Cong-Osvald-Leijen, OOPSLA'22) | TYPE | handler *names* are first-class values; a **rank-2 scope variable** (the `runST` trick) forbids the name escaping; names guaranteed not to escape by parametricity | rank-2 polymorphism |
| 4 | **Koka `mask` / scoped labels** (Leijen, "Effect Handlers, Evidently") | TYPE | controls *which* handler an op targets (skip-count) | doesn't stop escape by itself |
| 5 | **Region typing / `runST`** (Tofte-Talpin; Launchbury-Peyton-Jones) | TYPE | rank-2 region var `∀s.`; allocations tagged `s` can't appear in the result type | rank-2 polymorphism |
| 6 | **Zhang-Myers tunneling** (POPL'19) | TYPE | effects *tunnel* through effect-polymorphic code → no **accidental handling** (BANG's `no_accidental_handling`) | effect polymorphism |
| 7 | **Osvald et al second-class values** (OOPSLA'16, the basis of #1) | TYPE (lightweight) | a `@local`-style privilege annotation; a value **cannot escape its defining scope** (a coeffect) | a scope/privilege annotation |
| 8 | **Coeffect / graded** (Granule — Orchard-Liepelt-Eades; Petricek-Orchard-Mycroft) | TYPE | grade *how the context is used*; capture-tracking IS a coeffect | richer grades than 0/1/ω |
| 9 | **Lexically-scoped handlers — answer-type effect-freedom** (Biernacki et al; the classic handler discipline) | TYPE | **the handled effect must not occur in the answer type** — the *monomorphic special case* of #3/#5 | a syntactic occurrence side-condition |
| 10 | **Modal effect types** (Tang-White-Dolan-Hillerström-Lindley-Lorenzen, OOPSLA'25) | TYPE | modalities track effect scope, reducing the need for effect-polymorphism annotations | a modal (coeffect-like) layer |
| 11 | **Frank effect adjustments** (Lindley-McBride-McLaughlin) | TYPE | no first-class capability values → escape doesn't arise | no named/first-class handlers |

**The convergent finding.** Every kernel-sound mechanism is the same idea at different expressiveness
points: *a value that leaves a handler must not still depend on that handler's capability/effect, unless
that dependence is reflected in its type (capture set) and discharged where it lands.* The richest forms
(#2 capture sets, #3/#5 rank-2 scopes) **track** the dependence and permit re-handling; the
monomorphic floor (#9) simply **forbids** the dependence in the answer type. #9 is what #3/#5/#2
*degenerate to* when there is no polymorphism to quantify the scope variable over.

## Mapping onto BANG (scored against THIS kernel)

Constraints that gate the options: identity dispatch + global-fresh caps (ADR-0054/0055); the
**5-primitive** invariant (a 6th needs an ADR, inv #5); effect-rows-are-SETS (ADR-0001/0018); v1 is
**monomorphic** (ADR-0027 stages polymorphism → HM → System F); the **stratification** principle
(verified core / tested surface, CLAUDE.md); the LR re-derivation is **in flight** (inc-5, ~80%), so a
`HasCTy` change re-touches the LR's handle compat arms + the STD block.

Scoring axes: **(a)** closes the diagonal (`progB` untypeable/un-elaboratable)? · **(b)** KERNEL
(touches `HasCTy`/LR/STD) vs SURFACE (localizes to inc-7)? · **(c)** cost / blast radius · **(d)** fit
with ADR-0054 (lexical capability-passing; "resolution is a typing property").

| option | (a) closes diagonal | (b) layer | (c) blast radius | (d) ADR-0054 fit | verdict |
|---|---|---|---|---|---|
| **A. Surface second-class** (inc-7 elaborator forbids returning a live-cap thunk; kernel permissive) | at SURFACE only — kernel diagonal stays FALSE; safety = *well-elaborated source → safe* | SURFACE | small; localizes to inc-7; kernel/LR untouched | **reverses** "not by second-class thunks"; central promise rests on an unbuilt surface layer | **fallback** |
| **B-occ. Kernel answer-type label-freedom** (premise `¬ LabelOccurs ℓ A` on the 3 `handle` HasCTy arms + 3 HasStack frames) | **YES at the kernel** — `progB`'s inner handle needs `A = U {1}(F 1 unit)`, `LabelOccurs 1 A` → UNTYPEABLE; diagonal becomes a corollary of preservation | KERNEL (local to handle rules) | moderate: 3+3 arms + inversions + LR handle-compat re-touch; **additive premise, not restructuring**; **no polymorphism, no 6th primitive** | **FULFILLS** "escape ruled out by typing"; does NOT make thunks second-class; continues the WC→typing collapse | **RECOMMEND (now)** |
| **C. System-C capture tracking** (capture set on `U`; rank-2 scoped caps) | YES, and permits safe **re-handling** of escaped caps | KERNEL (deep: new coeffect + polymorphism) | largest: capture-set coeffect on thunk types + rank-2 quantified `handle`; contradicts v1 monomorphism | the *most* faithful to ADR-0054's research arc (it cites System C as the post-v1 upgrade) | **right answer, post-v1** |
| **D. Strengthen `NonEscape` at runtime** (track extent-uniqueness) | detects, doesn't prevent | KERNEL (invariant) | the ADR-0055-rejected "runtime-check-over-structural" smell | — | rejected |

### Why B-occ is the right monomorphic answer (the discrimination it gets right)

`LabelOccurs ℓ A` := `ℓ` appears in `A` as `VTy.cap ℓ` **or** as a latent effect `ℓ ∈ φ` inside any
`U φ C` sub-term of `A`. Add `¬ LabelOccurs ℓ A` to `handleThrows`/`handleState`/`handleTransaction`
(and the mirror `HasStack` frames). Checked against the existing witnesses:

```
program (NonEscapeProbe / IdentityCollisionProbe)   B-occ verdict      correct?
─────────────────────────────────────────────────────────────────────────────────
progB         (re-handle escape, → stuck)            REJECT (1 ∈ A)     ✓ (the bug, now untypeable)
escapeWitness (direct-force escape, → stuck)         REJECT (1 ∈ A)     ✓
migrateWitness  (thunk handles its OWN state)         ACCEPT (A = F q int)  ✓ (safe, stays typeable)
migrateWitness1 (force UNDER the binding handler)     ACCEPT (A = F q int)  ✓ (safe, stays typeable)
```

It rejects exactly the escaping programs and accepts exactly the safe migrations — the same
discrimination `NonEscapeProbe`'s `firstPerformResolves` draws operationally, now drawn **statically by
construction**. Crucially B-occ does **not** make thunks second-class (ADR-0054's red line): a
*fully-handled* thunk (effect `⊥`, or all labels bound by enclosing handlers) escapes freely; only a
thunk still carrying *this* handler's label is forbidden to leave. That is the lexical-handler
discipline (#9), not the second-class-values discipline (#1).

### The bonus: B-occ may DISSOLVE `NonEscape`

ADR-0054 collapsed `WellCapped` into typing (`HasConfig = HasConfigTy ∧ NonEscape`). B-occ extends that
collapse: if no well-typed program can return a cap past its handler, then **no escaped `vcap` is ever
produced at runtime**, so every reachable `perform (vcap n)` resolves — i.e. `HasConfigTy → NonEscape`
is *derivable*, and `NonEscape` stops being a separately-carried invariant. The inc-5 diagonal
(currently a false/stubbed `sorry`) becomes a corollary of type preservation. **This is a hypothesis to
build-confirm, not an assertion** — it is the single biggest reason to prefer B-occ over A, but it must
be proven, not promised.

## Decision (RECOMMENDATION — pending operator ratification)

1. **Adopt B-occ now**: add the answer-type label-freedom premise to the kernel `handle` typing rules
   (and the `HasStack` frame mirrors). This is the v1, monomorphic, kernel-sound fix. It closes the
   diagonal by construction, needs no polymorphism and no 6th primitive, and is faithful to ADR-0054's
   "escape is ruled out by typing."
2. **Companion (task #18): make raw source `vcap` untypeable.** B-occ forbids *escape* (a cap leaving a
   handler) but not a *dangling raw* `vcap 5 1` written directly in source (no binder at all).
   Separating source typing from runtime typing — so only `handle` binders introduce caps, and `vcap n`
   is runtime-only — lets the diagonal drop its `VcapFree` precondition entirely. B-occ + task-#18
   together fully close it; B-occ alone still needs `VcapFree` (or the runtime-only `vcap` restriction).
3. **Record System-C capture tracking (option C) as the named post-v1 upgrade** (already foreshadowed in
   ADR-0054's "System C boxing post-v1"). When polymorphism lands (ADR-0027 HM/System F rung), escaped
   capabilities become first-class and re-handleable by tracking a capture set on `U`; B-occ's hard
   "no latent ℓ in A" relaxes to "ℓ in A's capture set, dischargeable where it lands." B-occ is forward
   compatible — it is the empty-capture-set special case.
4. **Fallback if the mid-flight LR re-touch is judged too costly now (option A)**: enforce non-escape in
   the inc-7 elaborator, kernel stays permissive. Safety degrades to *well-elaborated source → safe*;
   the kernel's central promise rests on the unbuilt surface layer (the exact objection ADR-0055 raised
   against this). Choose this only as a deliberate, documented descent on the stratification seam.

## Consequences (if B-occ is ratified)

- **Kernel**: `HasCTy.handleThrows/handleState/handleTransaction` and `HasStack.handleF/stateF/
  transactionF` each gain a `¬ LabelOccurs ℓ A` premise (or a positive `AnswerWellScoped Γ ℓ A`). New
  decidable predicate `LabelOccurs : Label → VTy → Prop` over `VTy`/`CTy`/`EffRow`.
- **Inversion lemmas**: `HasCTy.handle*_inv` / the perform-cap inversions gain the premise; mechanical.
- **LR (inc-5, in flight)**: the handle compat arms thread the new premise; **in return** the diagonal's
  carried obligation (`lrDiag_supplies_nonEscape`, today a `sorry`) becomes provable — B-occ converts the
  blocked obligation into a discharge. Net effect on inc-5 is **plausibly negative LOC** (a false sorry
  removed), but this must be build-measured.
- **`NonEscape`**: candidate for dissolution (see bonus above) — verify, don't assume.
- **Regression oracle**: `progB` / `escapeWitness` must become `HasCTy`-UNTYPEABLE (a new
  `*_not_typeable` lemma per witness), and `migrateWitness*` must stay typeable (keep their typed
  witnesses green). Add a `handle`-arm with a latent-effect answer type to the untypeable suite.
- **No invariant breach**: rows stay sets (the premise is on the answer *type*, not the row order);
  five primitives unchanged; STM privilege untouched; performance second-class respected (a static
  check, zero runtime cost).

## Alternatives considered (rejected / deferred)

- **A. Surface second-class** — deferred to fallback. Cheapest, but kernel stays unsound; reverses
  ADR-0054 and rests soundness on an unbuilt layer (ADR-0055's rejection still stands).
- **C. System-C capture tracking now** — the *most general* answer, but needs polymorphism (rank-2) and a
  capture-set coeffect that v1's monomorphic budget (ADR-0027) doesn't have. **Deferred to post-v1**,
  recorded as the upgrade B-occ is forward-compatible with.
- **D. Strengthen `NonEscape` to track extent-uniqueness at runtime** — detect-not-prevent; the
  ADR-0055-rejected runtime-check-over-structural smell.
- **Koka rank-2 scoped named handlers (#3) directly** — exactly BANG's cap-by-identity == named handler,
  and the right model, but rank-2 = polymorphism = post-v1. B-occ is its monomorphic shadow; C is its
  full adoption.
- **Weaken `NonEscape` so `progB` satisfies it** — already rejected in ADR-0056 (`progB` genuinely
  escapes; the fix belongs in typing/surface, not in weakening the safety predicate).

## Build-confirm result (bocc-spike @ `39455a7`, the `BoccSpike` probe, axiom-clean) — GO

All four pre-ratification open questions resolved build-grounded; **GO on B-occ**:

1. **Only-channel — CONFIRMED (corrected rationale).** Not int-cells (false for `handleState`'s general
   `S`, `Syntax.lean:208`) but **discard-on-pop + identity-return** (`Operational.lean:229`). The answer
   type is the only EXIT channel; a cap stored in a state cell is caught by its own label's B-occ premise
   on `get`-exit. No store/closure bypass.
2. **Discrimination — CONFIRMED (built, not asserted).** `bug_progB_rejected : LabelOccurs 1 (U {1}(F 1 unit))`
   rejects both `progB` and `escapeWitness` (same mechanism); `safe_*_accepted : ¬LabelOccurs ℓ int` accepts
   both `migrateWitness`/`migrateWitness1`. The sharp point: `migrateWitness1` constructs the SAME `U {1}`
   thunk as `progB` but is ACCEPTED — B-occ constrains only handle ANSWER types; within a live extent caps
   flow freely. Exactly the right discriminator.
3. **NonEscape-dissolution — ATTEMPTED in phase 1, WALLS standalone (`075f894`, bocc-impl).** The natural
   bridge "B-occ ⟹ label-free answer type ⟹ no escaping cap" is FALSE at the VALUE level: a `vthunk` can
   carry-then-DROP a free cap of a label-free type — `vthunk (letC (ret (vcap n ℓ)) (ret vunit)) : U φ (F _ unit)`
   is label-free yet names `vcap n ℓ` — so `NonEscape` CANNOT be a structural value predicate. B-occ correctly
   kills the HARMFUL case (PERFORMING an escaped cap needs `labelEff ℓ ≤ φ` ⟹ `LabelOccurs`) but not the
   benign carry-drop. So B-occ is the necessary **ENABLER** (perform-after-pop becomes contradictory) — the
   diagonal still closes, but via **inc-5's typed-LR fundamental theorem** (`NonEscape` = the unary reachability
   projection over `StepStar`, Shape B, exactly ADR-0056's own consequence), NOT as a free standalone corollary.
   inc-5's LR is still required; B-occ *unblocks* its diagonal rather than replacing it. The provable half
   (`perform_vcap_label_in_effect`) is banked.
4. **LR blast radius — MANAGEABLE, sequence it.** Adding the premise as a constructor field breaks ~55
   positional matches (Metatheory ~43, Operational ~6, Compat arms — almost all mechanical one-binder `_`
   insertions in currently-GREEN files); the *consumed* threading is small (~2 LR handle-compat arms + a
   few Compat theorems). **SEQUENCING: land the Syntax premise + the ~55 mechanical green-file fixups FIRST
   (additive, independent), thread the LR LAST after the inc-5 re-key settles — do NOT perturb the
   ~80%-done RED LR blind.** `LabelOccurs` (Q3) recurses through nested `U`/`F`/`arr`/`sum`/`prod`/`mu`;
   total + decidable.

Scoping (unchanged): B-occ closes *escape*; a raw dangling `vcap 5 1` still types (`HasVTy.vcap`,
`Syntax.lean:71`), so the diagonal keeps `VcapFree` under B-occ alone — dropping it needs task #18 (Decision §2).

## Sources

- Brachthäuser, Schuster, Ostermann, "Effects as Capabilities" / Effekt (POPL'20) — second-class blocks.
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki, "Effects, Capabilities, and Boxes" (OOPSLA'22) — System
  C, boxing, capture sets `at {…}`. https://dl.acm.org/doi/pdf/10.1145/3527320
- Xie, Cong, Osvald, Leijen, "First-Class Names for Effect Handlers" (OOPSLA'22) — named handlers +
  rank-2 scoped effects (runST trick). https://xnning.github.io/papers/oopsla22namedh.pdf ;
  escape-is-unsound-if-unscoped confirmed by koka-lang/koka#356.
- Zhang, Myers, "Abstraction-Safe Effect Handlers via Tunneling" (POPL'19) — accidental-handling /
  tunneling. https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf
- Osvald, Essertel, Wu, González Alayón, Rompf, "Gentrification Gone too Far? Affordable 2nd-Class Values
  for Fun and (Co-)Effect" (OOPSLA'16) — second-class values, can't escape defining scope.
- Tofte, Talpin, region inference; Launchbury, Peyton Jones, `runST` rank-2 region escape.
- Orchard, Liepelt, Eades, Granule; Petricek, Orchard, Mycroft, coeffects.
- Tang, White, Dolan, Hillerström, Lindley, Lorenzen, "Modal Effect Types" (OOPSLA'25). 
  https://arxiv.org/abs/2407.11816
- BANG internal: ADR-0056 (the gap), ADR-0054/0055 (identity + global-fresh), `Bang/Witness/CapEscapeWitness.lean`,
  `scratch/IdentityCollisionProbe.lean`, `scratch/NonEscapeProbe.lean` (the discrimination probe).
