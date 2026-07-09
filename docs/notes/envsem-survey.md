<!-- note-status: active -->
# Environment / closure semantics — the design-space survey for #61's fix

> **One-sentence recommendation.** Keep `Source.eval` as the substitution SPEC,
> unchanged; introduce an **environment/closure representation in the calculated
> machine layer** (`evalD` → `exec`) and prove it corresponds to the spec — the
> two-hop architecture (ADR-0016) absorbs the whole fork without a spec rebase,
> exactly as PureCake's verified back end introduces environments as one IL-local
> pass below a substitution spec (`@kanabar-pldi23-purecake`).

Grounds: [`hang-61-diagnosis.md`](hang-61-diagnosis.md) (the measured ~1 ms/step
`Comp.subst` cost — O(knot-body-size) per unfold, both engines), issue #61,
`Bang/Core/Semantics/Eval.lean` (`Source.step`), `Bang/Backend/AbstractMachine.lean:57`
("substitution-based with a CLOSED focus — there is NO environment and NO closure").
This note is **research input for the future env-semantics ADR** (task #75), NOT an ADR;
the operator rules on the fork.

---

## 0 · The premise, checked (does bang even need this?)

The premise **survives**. Two ways it could have been a false alarm, both ruled out:

- *Could the fix live in the frontend?* No. The diagnosis §1 refuted term-blowup
  (elaboration is linear, +54 nodes/sibling). The cost is the **reduction strategy**,
  not the encoding. Frontend can't touch it.
- *Could an interim non-fix suffice?* Partially (§4 below), but the interim is itself
  a shift away from whole-term substitution — so it does not refute the direction, it
  is a cheaper point on the same axis.

The one genuine caveat that *narrows* (not refutes) the fix: `bang run` **defaults to
the kernel `Source.eval`** (`Main.lean:24`), the substitution engine. So if the fix
lands only in the machine (the recommendation), the **default `bang run` stays slow**
until the default flips to `--compiled`, or `Source.eval` itself is memoized. Called
out in §3 and the ADR-INPUTS.

---

## 1 · The design space

Five options, each priced against bang's actual proof spine (the `subst`-token weave:
Soundness 427, BinaryLR 327, AbstractMachine 191, Wasm 136, LR 126, Freshness 103 —
~1900 occurrences across 16 files; this is the blast-radius denominator).

| # | option | what changes | proof-tax | perf gain | who did it | verdict for bang |
|---|--------|--------------|-----------|-----------|------------|------------------|
| **A** | **Env machine in the derivation** (`evalD`/`exec` gain env+closures; `Source.eval` stays subst SPEC; prove correspondence) | machine layer + one correspondence lemma; **spec + Soundness + LR untouched** | **medium** — new env-wellformed invariant + `γ≈ₑσ` lemma; but the expensive `subst` cluster (soundness/LR) is *preserved*, not rebuilt | **full** — O(1) lookup replaces O(body) subst; dissolves the cliff | **PureCake** (EnvLang is one pass below a subst spec); **PLFA BigStep** (the correspondence proof itself) | **RECOMMENDED** — the two-hop architecture is *for* exactly this |
| **B** | **Env semantics in the spec** (`Source.eval` itself becomes a CEK/CESK env machine) | `Source.eval` + **every** `subst`-indexed proof re-based | **large** — re-bases Soundness (427), both LRs (453), Freshness (103); new env-wf side conditions throughout | full | CakeML/CompCert (env from day one — but they never *paid the subst tax first*) | **rejected** — throws away ~1900 lines of paid-for substitution metatheory; violates invariant #4's spirit (spec is the reference, machine is derived) |
| **C** | **Explicit-substitution calculus** (λσ: substitutions become first-class syntax, composed lazily) | new `subst`-syntax + composition rules in the spec | **large + subtle** — λσ famously *lacks* preservation-of-strong-normalization (a simply-typed term with an infinite λσ-path exists; `@explicit-subst-jfp`-lineage); new confluence/termination burden | partial (defers, doesn't eliminate, the copy) | Suspension calculus, λs | **rejected** — buys a new metatheory headache (SN failure) to solve a perf problem environments solve cleanly |
| **D** | **Thunk-sharing / memo at the knot** (interim; don't re-copy `funBody'` per unfold — share via a heap cell / recursive-closure) | narrower reduction-relation change | **small–medium** — one sharing invariant; still touches the reduction relation + its metatheory | **large but not full** — kills the *per-unfold re-copy*, not all subst | lazy-language runtimes (thunk update-in-place) | **fallback interim** — a cheap stopgap if A is too big for the current milestone; see §4 |
| **E** | **Term-graph / hash-consing** (share identical subterms so `subst` doesn't duplicate) | representation swap under the reducer | medium | partial (helps sharing, not the O(body) walk itself) | GHC STG-ish sharing | **rejected as primary** — doesn't fix the *walk*; the reducer still traverses the body per step |

**The axis.** A, B, C, E all move away from "reduce by rebuilding the whole term."
A does it in the machine only; B/C do it in the spec; D memoizes the worst offender.
The literature verdict is unambiguous: environments are the state-of-art
("the substitution model is a correct but notoriously slow implementation of static
binding … a more efficient technique is to explicitly thread environments through
machine states and form closures when necessary"). The only real question for bang is
**which layer** pays for it — which is Q3.

---

## 2 · What verified/mechanized projects chose, and what it cost

- **PureCake** (`@kanabar-pldi23-purecake`) — **the load-bearing parallel.** Its
  verified back end is a *tower* of ILs: `PureLang` (call-by-name, **substitution**
  spec) → `ThunkLang` (call-by-value, **substitution**, with `delay`/`force` = bang's
  `thunk`/`$`) → `EnvLang` (call-by-value, **environment**) → `StateLang` (impure,
  environment, CESK). The substitution→environment switch is **one pass**, and EnvLang
  is "**only a minor stepping stone … closely mirrors ThunkLang, except its semantics
  relies on environments rather than substitution**" (§5.3). Two teachings transfer
  verbatim:
  1. **The switch is IL-local and cheap.** They did NOT re-base the top-level spec;
     they added a lower language and proved the pass. → bang's Option A.
  2. **Memoized `force` breaks step-monotonicity.** When they later compile `delay`/
     `force` to a two-cell **thunk-array** (flag + payload) so repeated forcing is
     memoized, step counts no longer move monotonically, forcing them to prove that
     pass by **both forward AND backward simulation** (§5.4). → a concrete warning for
     bang's Option D (§4): memoization is not free in the proof.

- **CakeML** (`@kumar-popl14-cakeml`) — **environment semantics from day one**
  (functional big-step with a clock). Relevant *contrast*: CakeML never paid a
  substitution-metatheory tax to later discard, so "just use environments" was free
  for them and is NOT free for bang (bang already spent ~1900 lines on `subst`). This
  is the argument *against* Option B: bang is not greenfield.

- **CompCert** (Clight/Cminor) — **environments throughout**: a global env, a local env
  (vars → memory blocks), a temp env (vars → values), a store, and a continuation for
  the call stack. Verdict: "continuation-based semantics are the privileged style to
  facilitate compiler-correctness proofs." bang's machine already has the continuation
  (`K` stack) and effect-state stores (`SStore`/`THeap`); it is **missing only the
  variable environment** — Option A adds exactly that one component.

- **PLFA `BigStep`** (`@wadler-kokke-plfa-bigstep`) — **the mechanized exemplar for the
  correspondence proof** bang would owe under Option A. It defines an env-based big-step
  machine (values are closures `clos M γ`) and proves it equivalent to substitution
  reduction. The load-bearing lemma:
  > if `γ ⊢ M ⇓ V` and `γ ≈ₑ σ`, then `subst σ M —↠ N` and `V ≈ N`.

  with `γ ≈ₑ σ` = "for any variable `x`, the closure `γ x` is equivalent to the term
  `σ x`" — this **is** the environment-well-formedness invariant bang would carry.
  PLFA's own note on effort: "*as is often necessary, one must generalize the statement
  to get the induction to go through*" (generalize from the empty env to an arbitrary
  `γ` plus the `≈ₑ` premise). **The proof is a known pattern, not an invention.**

- **CEK/CESK derivation** (`@vanhorn-might-icfp10-abstracting-abstract-machines`,
  `@ager-biernacki-danvy-midtgaard-03-interp-to-compiler-vm`) — the environment machine
  is **derived from the reduction semantics** ("extensionally equivalent but more
  realistic … amenable to efficient implementation"). This is **invariant #4 stated in
  the literature**: the env-machine is the *calculated output* of the spec, not a rival
  spec. bang's Bahr–Hutton derivation is the same discipline; the CESK is where it lands
  when you add environments.

**The proof-tax asymmetry, stated plainly.** Environments cost you *one* new invariant
(env/closure well-formedness: every free var of a closed-over term is bound in its env,
the `γ≈ₑσ` agreement) and the weakening lemmas that ride it. Substitution costs you the
*whole* `subst`-lemma cluster (commutation, `subst`-under-shift, closedness-preservation
— the 427-line Soundness weave). bang has **already paid** the substitution tax. Option
A **keeps that payment** (spec stays substitution) and adds the *single* env invariant
only in the machine. Option B **discards** the paid substitution tax and pays the env
tax spec-wide. That asymmetry is the whole argument.

---

## 3 · Spec-vs-derivation — the framing that dissolves the fork

This is the decisive section. The question that looks like "rewrite the semantics?" is
really "**which layer gets environments?**" — and bang's two-hop structure already
answers it.

```
                     THE TWO-HOP ARCHITECTURE (ADR-0016), with #61's fix placed
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │  Source.eval          evalD  ────────►  (compile, Code, exec)                 │
  │  (kernel oracle)       (CalcVM ref)      (calculated machine)                 │
  │  SUBSTITUTION          SUBSTITUTION       SUBSTITUTION   ← today: all three    │
  │      SPEC              (Bahr-Hutton        (derived)        share Comp.subst   │
  │   — UNCHANGED —         start point)                        → the #61 cost     │
  │                                                                               │
  │  SUBSTITUTION    ≈    ENVIRONMENT   ────►  ENVIRONMENT   ← Option A: env enters │
  │      SPEC        │     (evalD gains         (closures)      at evalD; a NEW    │
  │   — UNCHANGED —  │      an env + closures)                  correspondence     │
  │                  └── evalD_agrees_source becomes the        `evalD_agrees_source`│
  │                      substitution↔environment bridge         is the γ≈ₑσ lemma │
  └─────────────────────────────────────────────────────────────────────────────┘
```

bang **already has** the two things this needs:

1. **A spec/machine split with a proven bridge.** `evalD_agrees_source` already ties
   the stateful lowering `evalD` back to the substitution kernel `Source.eval`. Today
   both sides substitute, so the bridge is "same reduction." Under Option A, `evalD`
   reduces by environment lookup while `Source.eval` still substitutes, and
   `evalD_agrees_source` **becomes the PLFA `γ≈ₑσ` correspondence lemma** — the same
   theorem, re-proved across the new representation gap. This is where the medium-tax
   sits, and it is a *localized, known-pattern* proof, not a spec-wide re-base.

2. **A machine with continuation + state stores, missing only the var-env.** The
   CalcVM's `SStore`/`THeap` (`AbstractMachine.lean:116,152`) are **effect-state**
   stores keyed by *label* — NOT variable environments (the file says so explicitly:
   "there is NO environment and NO closure", line 57). So Option A is *additive*: add a
   variable environment `ρ` + closure values alongside the existing `SStore`; the
   effect machinery is untouched.

**Where the #61 cost then lives.** Honestly: in the **oracle path**, if `Source.eval`
stays substitution *and* `bang run` keeps defaulting to it. Two sub-options:

- **(A1) Machine-only fix, flip the default.** Land env in `evalD`/`exec`; make the fast
  `--compiled` engine the `bang run` default. `Source.eval` stays the slow, simple,
  *verified reference* — invoked in proofs and as the differential oracle, never on the
  hot path. This is the cleanest: the spec is allowed to be slow (it is a reference), the
  machine is fast. Matches invariant #7 (perf is a machine concern) exactly.
- **(A2) Machine fix + memoize the oracle.** Additionally give `Source.eval` thunk-
  sharing (Option D) so even the reference is tolerable. More work, only if the oracle
  path must be fast for dogfooding.

**Recommendation is A1.** It is the minimal change that dissolves #61 for real programs
(`bang run --compiled` / the flipped default) while touching **zero** of the substitution
spec + soundness + LR proof spine.

---

## 4 · Interims — the cheap version (Q4)

If Option A is too large for the current milestone, the fallback is **Option D:
thunk-sharing at the knot** — stop re-copying `funBody'` on every unfold by sharing the
body through a heap cell / recursive closure the reducer dereferences.

What lazy-language runtimes teach (and PureCake confirms): a thunk becomes an
**update-in-place cell** — first force evaluates and overwrites the cell with the result;
subsequent forces read it. That is precisely what collapses the knot cost: the giant
`funBody'` is traversed *once*, not per call.

**The proof warning, from PureCake §5.4 (cited above):** memoized `force` makes the
compiled program *skip* steps a naive one takes, so step-count monotonicity fails and you
need **both forward and backward simulation** to relate the two. bang's `compile_forward_sim`
(ADR-0035) is forward-only; Option D would owe the converse direction too. So D is
"small–medium," not "small" — cheaper than A's representation change, but not free.

**Verdict on interims:** D is a legitimate *stopgap* that buys most of the perf at a
narrower blast radius, but it is a detour, not the destination — it still leaves the
reducer substitution-shaped. If the ADR commits to A anyway, skip D and go straight to
environments (the PLFA/PureCake pattern is well-trodden enough that A is not much more
than D once you account for D's backward-simulation tax).

---

## 5 · Performance envelope (Q5) — does the fix actually dissolve the cliff?

Yes, by ~4–5 orders of magnitude on the per-step constant.

| | today (substitution) | environment machine |
|---|---|---|
| per-step cost | **~1 ms** (O(knot-body-size); measured, diagnosis §2) | **~10–40 ns** (O(1)/O(depth) var lookup; measured for tree-walkers) |
| what a step does | rebuild the whole function body | look up a variable in a map |
| JSON parse `[1]` | ~1.05 s | predicted **sub-ms** |

Empirical anchors: benchmarked variable-access at **16–38 ns**; environment lookup is
O(list-size) but collapses to O(1) with a resolver pass (de Bruijn indices — which bang
*already uses*, so the env is index-addressed, not name-searched). The diagnosis measured
each bang step traversing ~10⁵–10⁶ term nodes; replacing that with an index lookup is the
~10⁴–10⁵× that turns the 16.85 s JSON run into the tens-of-ms range. **The fix dissolves
the cliff; it does not merely soften it.**

Caveat: this is the *per-step* constant. Step *count* (linear in work, diagnosis §2) is
unchanged — environments fix the constant, not the algorithm. That is exactly right: #61
is a constant-factor cliff, not a complexity bug.

---

## ADR-INPUTS

Lift-ready for the future env-semantics ADR (task #75). The ADR records the choice + the
rejected alternatives + rationale; here they are.

**Decision (recommended):** Introduce environment/closure representation in the
**calculated-machine layer** (`evalD` → `exec`), leaving `Source.eval` as the unchanged
substitution SPEC. Re-prove `evalD_agrees_source` as a substitution↔environment
**correspondence** lemma (the PLFA `γ≈ₑσ` pattern). Make `--compiled` the `bang run`
default so real programs hit the fast engine (Option **A1**).

**Named costs:**
- One new **environment/closure well-formedness invariant** (`γ≈ₑσ`: every closed-over
  term's free vars bound in its env) + the weakening lemmas riding it. Localized to the
  machine layer.
- Re-proving `evalD_agrees_source` across a representation gap (medium; **known pattern**,
  PLFA + PureCake both mechanized it).
- Additive machine change: a variable environment `ρ` + closure values alongside the
  existing `SStore`/`THeap` (which are untouched — they are effect-state, not var-env).
- The substitution spec + Soundness (427) + both LRs (453) + Freshness (103) proof spine
  is **preserved, not rebased** — this is the point.
- Residual: the **oracle `Source.eval` stays O(body) per step**; acceptable because
  (a) it is a reference, not the hot path, and (b) the default flips to `--compiled`.
  If the oracle must also be fast, add Option D memoization (A2).

**Rejected alternatives:**
- **(B) Environment semantics in the spec** — rejected: re-bases ~1900 lines of paid-for
  substitution metatheory (Soundness/LRs/Freshness); bang is not greenfield (unlike
  CakeML), so it would *discard* a tax already paid. Also weakens the invariant-#4 clean
  split (spec = reference, machine = derived).
- **(C) Explicit-substitution calculus (λσ)** — rejected: buys a new metatheory hazard
  (λσ lacks preservation-of-strong-normalization) to solve a perf problem environments
  solve without it.
- **(E) Term-graph / hash-consing** — rejected as primary: shares subterms but the
  reducer still *walks* the body per step; doesn't fix the O(body) traversal.
- **(D) Thunk-sharing/memo interim** — **not rejected; deferred as the fallback stopgap**
  if A is too large this milestone. Named cost: owes backward simulation (PureCake §5.4)
  because memoized force breaks step-monotonicity, so it is small–medium, not small.

**Supersedes framing:** this refines ADR-0073 §5 ("TCO deferred / slow-correct first"),
which anticipated deep-recursion `oom` but not the per-*shallow*-step O(body) cost that
#61 measured. The perf concern is no longer "deep recursion ooms" but "every step is
O(body)"; the fix is env-in-the-machine, not TCO.
