# Lean 4 tactics + tooling survey (for bang-lang verification)

> One-time research pass on what's useful in the contemporary Lean 4 ecosystem
> (mid-2026) for the bang-lang verification work. Filed for durable reference;
> cross-check against `references/README.md` for cited papers.
>
> Top-3 recommendations:
> 1. **`grind`** — Lean's SMT-style closer (new in 4.28-4.29). Saves ~7 LoC per
>    theorem on CS-flavored proofs. CSLib reports it closes Hennessy-Milner
>    bisimulation cases with one-line hints.
> 2. **`iris-lean`** — provides ▷ (later modality), UPred/IProp, and MoSeL
>    proof mode in Lean 4 v4.29+. Exactly the substrate the Biernacki-style
>    LR needs (alternative is rolling our own well-founded recursion).
> 3. **Aesop custom rule sets** — tag ~15-20 typing-rule constructors with
>    `@[aesop safe constructors]`; case analysis on `HasVTy`/`HasCTy`
>    derivations becomes near-automatic. Pair with `register_grind_attr`
>    (new in 4.28) for a typing-specific grind variant.

---

## (A) Tactics beyond the obvious

| Tactic | What it does | When to reach for it |
|---|---|---|
| **`grind`** | SMT-inspired closer: congruence closure + E-matching + LIA + ring + case-splitting. New in Lean core, matured through 4.28-4.29. | First thing to try at goal leaves. CSLib reports grind closes Hennessy-Milner bisimulation cases with a one-line hint. Avoid for combinatorially exploding goals — use `bv_decide` there. |
| **`register_grind_attr`** (4.28+) | Define your own grind attribute, e.g. `@[bang_grind]`, scoping lemma sets per domain. | Build a `bang_grind` for effect-row algebra (idempotent commutative `+`, lacks-quantifier side-conditions) so you can call `grind only [bang_grind]` on row-discharge goals. |
| **`gcongr`** | Generalized congruence for inequalities; applies the `@[gcongr]`-tagged lemmas to break a `f a ≤ f b` into `a ≤ b`. | Step-index monotonicity (`n' ≤ n → Vrel n' ... → Vrel n ...`) and any "if subterms shrink, whole shrinks" goal. |
| **`mono`** | Mathlib's monotonicity prover, complements `gcongr`. | Same niche, sometimes wins where `gcongr` doesn't. |
| **`fin_cases`** / **`interval_cases`** | Exhaustive case analysis over finite types / bounded intervals. | `Finset Label` membership reasoning; fuel-bound case analysis. |
| **`simp_all`**, **`simp only [...]`**, **`simp_arith`** | The usual, but `simp_all` is dramatically more powerful than `simp` on hypothesis-heavy goals from `rcases` on derivations. | After `cases h <;> ...` on a typing derivation, follow with `simp_all` not `simp`. |
| **`positivity`**, **`bound`**, **`linarith`**, **`nlinarith`** | Real-valued positivity; bounded arithmetic; (non)linear inequalities. | Less central for us — `omega` covers most integer arithmetic. `bound` is useful for step-index bookkeeping like `n - 1 ≤ n`. |
| **`cbv` / `decide_cbv`** (new in 4.29) | Call-by-value evaluation tactic outside conv-mode. | Useful for executing `Source.step` symbolically inside a proof. |
| **`simpArrowTelescope`** (new in 4.29) | Simplifies long `p₁ → p₂ → ... → q` chains without quadratic blowup. | Helpful for proofs over our ~15-20 constructor typing relations where IHs are deeply nested arrows. |
| **`conv ⇒ lhs/rhs/ext/...`** | Targeted rewriting at subterms or under binders. | Necessary for Bahr-Hutton calculations: rewriting the RHS of `⟦e⟧ = ...` under stack-machine continuation binders. |
| **`first_par`** (new in 4.28) | Run several tactics in parallel, take first to succeed. | Speeds up `aesop`-or-`grind`-or-`decide` cascades during exploration. |
| **`<;>` combinator, `all_goals`, `any_goals`** | Apply a tactic to every subgoal at once. | Standard pattern for typing-derivation case work: `cases h <;> (first | grind | aesop)`. |

`Mathlib.Tactic.Group` is **NOT relevant** to bang-lang (it's literal group-theory
normalization, not "group rewriting") — the name was a false lead.

## (B) Substitution / binder support

No mature Lean 4 equivalent of Autosubst / LNgen. Concretely:

- **CSLib** ([cslib.io](https://cslib.io), [github](https://github.com/leanprover/cslib))
  provides reusable plumbing for substitution and references both Urban-style
  nominal techniques and Charguéraud locally-nameless, but no
  `deriving Substitution` macro. If we switch to de Bruijn it's the closest
  off-the-shelf option.
- Several individual projects roll their own. Community consensus (Zulip):
  for ~3 binder forms (ours: λ, fix, let), hand-rolled substitution with a
  `Subst.lean` file plus `@[simp]`-tagged `subst_var_neq`, `subst_subst_assoc`
  lemmas is cleaner than a generic framework.
- For named-variable representation, practical advice: keep it named for the
  spec layer, write a separate de Bruijn IR (or locally nameless) for the
  proof layer, and prove a one-shot translation. Don't fight Lean's binders.

## (C) Step-indexed LRs / guarded recursion

**[iris-lean](https://github.com/leanprover-community/iris-lean)** is the
find. Status as of June 2026:

- Builds on Lean v4.29.0+ (matches us); tags down to v4.24.
- Later modality (▷) infrastructure is "largely complete" — `ofe.v` port at
  69%, including `later`, `laterO`, `later_map`, `dist_later`.
- `cofe_solver.v` at 91%, so guarded-fixpoint construction is usable.
- `stepindex.v` itself at 0% but `stepindex_finite.v` at 36%; the *finite*
  (= fuel-indexed) machinery is partial and the most relevant slice for our
  AOT WasmFX simulation.
- MoSeL proof mode, UPred, IProp, invariants, later credits are landed.

**Practical advice for our LR** (Vrel/Srel/Krel/Crel): two viable paths:

1. **Hand-rolled** with `termination_by` on lexicographic `(n, sizeOf type)`
   and the `decreasing_by` tactic. Mathlib's `WellFoundedRecursion` +
   `Prod.lex` give the order; recent improvements to `termination_by`'s
   lexicographic guessing may mean we don't even need to spell the measure.
   What most ad-hoc Lean PL formalizations do.
2. **Iris-lean** with ▷ — buy the modal discipline, get guarded recursion
   essentially for free. Worth it if we'll grow the LR (concurrent effects,
   separation-flavored handlers). Possibly overkill for a single LR.

**Recommendation**: start with (1); migrate to (2) if we find ourselves
re-proving monotonicity / down-closure / anti-monotonicity laws repeatedly.

## (D) Inductive Prop manipulation

- **`rcases h with ⟨a, b, c⟩ | ⟨d, e⟩`** for nested existentials/disjunctions
  from `Exists`/`And`/`Or` in derivation conclusions.
- **`obtain ⟨a, h⟩ := proof_of_exists`** — same as `rcases` with `have`-style
  syntax; preferred when introducing a new fact, not destructuring.
- **`induction'`** (Mathlib): like `induction` but names constructor
  arguments and IHs, with `case`-syntax for each branch. Use over plain
  `induction` for our 15-20-constructor `HasVTy`/`HasCTy`.
- **`cases h <;> simp_all`** is the workhorse pattern. With grind:
  `cases h <;> grind` is often shorter.
- **`induction h using HasVTy.rec` with `case` blocks** when we want to name
  each typing rule explicitly in the proof script — pays for itself when
  typing rules change.

## (E) Domain-specific Lean 4 libraries

- **[iris-lean](https://github.com/leanprover-community/iris-lean)** —
  covered above. The MoSeL fragment alone is useful even without separation
  logic, as a proof-mode for first-class implication-style reasoning over
  effect-row constraints.
- **[CSLib](https://cslib.io)** ([Henson & Montesi, 2026](https://arxiv.org/abs/2602.04846),
  spine paper [arxiv.org/abs/2602.15078](https://arxiv.org/abs/2602.15078))
  — Lean 4 PL library: LTS structures, bisimulation/simulation as lattice,
  CCS. Their tactic culture is grind-first. Worth reading their proofs as
  a style reference. Repo: `github.com/leanprover/cslib`.
- **[Aesop](https://github.com/leanprover-community/aesop)** — we have it
  via Mathlib. The high-leverage use is registering each typing rule as
  `@[aesop safe constructors]` so `aesop` becomes a proof-search-style
  typing oracle. Combined with norm rules for our substitution lemmas this
  can auto-close 30-50% of "well-typed under extended context" obligations.
- **[Plausible](https://github.com/leanprover-community/plausible)** —
  already in our deps. Use it for round-trips:
  `#test ∀ e n, Source.run e n = Wasm.run (compile e) n` to catch compiler
  bugs before formal proof.
- **[lean-smt](https://arxiv.org/abs/2505.15796)** — Lean 4 SMT tactic with
  proof reconstruction. Useful for effect-row algebra obligations if `grind`
  doesn't close them.

## (F) Comparable mechanizations

- **plclub/cbpv-effects-coeffects (Coq)** — uses standard Coq tactics:
  `induction`, `inversion`, `eauto`, custom `Hint` databases per typing rule.
  Lean 4 equivalents: `induction'`, `cases` (Lean has no direct `inversion`
  analogue — `cases h` does it), `aesop` with `@[aesop safe constructors]`,
  custom Aesop rule sets ≈ Hint databases.
- **aleff-logrel (Biernacki, Coq)** — uses IxFree. No Lean port exists.
  Iris-lean's later modality + MoSeL is the closest substrate. Their tactic
  flow (`iIntros`, `iApply`, `iModIntro`) maps onto MoSeL.
- **CakeML (HOL4)** — not portable; CakeML-in-Lean attempts have not landed.
  Stick to Benton-Hur ICFP'09 forward simulation style for WasmFX.
- **Bahr-Hutton calculating compilers** — Coq formalizations exist
  ([github.com/Marcoj776/Calculating-Compilers](https://github.com/Marcoj776/Calculating-Compilers)).
  Lean 4 port: none known. Their `=⟨ ... ⟩` calculation idiom translates to
  Lean's `calc` blocks plus `conv` for targeted rewrites — direct port
  should be mechanical.

## (G) Surprising things

- **`set_option profiler true`** — built-in proof-step profiler, surfaces
  which tactic invocation is eating elaboration time. Essential when
  grind/aesop start to slow our build.
- **`set_option trace.grind true`** / `trace.aesop.proof` — proof-search
  debugging.
- **`set_option maxHeartbeats N`** per-declaration when grind is borderline.
- **`exact?`, `apply?`, `rw?`, `decide?`** — terminal "what would close this"
  suggestions; treat as exploratory, paste their output as the real proof.
- **`#check` / `#print` / `#reduce`** at top-level and `#guard_msgs in` for
  golden-output tests on tactic behaviour — pin the proof shape so a future
  refactor breaks loudly.
- **`mvcgen` improvements (4.28-29)** — monadic verification condition
  generator, mostly for Std `Do` programs. Probably not relevant unless our
  interpreter is monadic.
- **`@[simp ←]` and `simp +instances`** behaviour changed in 4.29 — instances
  no longer simplified by default. May affect existing proofs if upgrading.
- **`omega`** handles `Nat`/`Int` linear arithmetic *including* `Nat`
  subtraction truncation — use for all fuel/index arithmetic obligations.

## Don't bother

- **`Mathlib.Tactic.Group`** — group-theory normalization, irrelevant despite
  the name.
- **`field_simp` / `ring`** — our domain has no rings/fields outside
  arithmetic; `omega` suffices.
- **`polyrith` / `linear_combination`** — polynomial identities over `ℚ`/`ℝ`;
  not relevant.
- **`fun_prop`** — for continuous/measurable/differentiable; not our domain.
- **`norm_num`** — closes numeric literal equalities; covered by `decide` for
  our purposes.
- **`Mathlib.Combinatorics.Quiver.*`** — quiver theory is graph-shaped
  category theory, *not* a substitution framework despite the name overlap
  with "binder graphs".
- **`Lean4Lean`** — verifies *Lean's* typechecker, not a general TT library.
  Don't pull it in.
- **Lean-SMT** — useful as a fallback but adds an external solver dependency
  (cvc5). Try `grind` first; only escalate if there are residual algebraic
  obligations grind can't close.

## Version pins to be aware of

- **iris-lean**: tracks Lean closely; the `lean4:v4.29.0` tag exists; v4.30
  compatibility likely current. Add as a lake dependency with the matching
  revision. ([reservoir](https://reservoir.lean-lang.org/@leanprover-community/iris-lean))
- **Mathlib v4.30.0** (our current) — `grind` improvements through 4.29
  require it; `register_grind_attr` from 4.28; Miller-pattern e-matching new
  in 4.29.
- **Aesop** — bundled with Mathlib; no separate pin needed.
- **Plausible** — already in deps.
- **CSLib** — independent lake dependency from `github.com/leanprover/cslib`;
  v4.29.0-compatible.

## When to revisit this doc

- **Lean toolchain bumps** — check that `grind` / `simp_arith` / new tactics
  haven't shifted behaviour; verify iris-lean / CSLib still compile.
- **Phase A part 2 (typing rules concretized)** — apply (D)'s pattern;
  register `@[aesop safe constructors]` on each typing rule; try `grind` on
  the easy compat lemmas before writing them by hand.
- **Phase B PROOF_ORDER #1 (LR foundation)** — decide between hand-rolled
  step-indexing (C.1) and iris-lean adoption (C.2).
- **Phase B PROOF_ORDER #3 (compile_forward_sim)** — Bahr-Hutton calculation
  via `calc` + `conv`; consider porting the Calculating-Compilers Coq style.

## Sources

- [iris-lean GitHub](https://github.com/leanprover-community/iris-lean)
- [iris-lean Reservoir](https://reservoir.lean-lang.org/@leanprover-community/iris-lean)
- [iris-lean porting status](https://leanprover-community.github.io/iris-lean/)
- [Lean 4 grind tactic reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)
- [Lean 4.29.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.29.0/)
- [Lean 4.28.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.28.0/)
- [CSLib spine paper (arXiv 2602.15078)](https://arxiv.org/abs/2602.15078)
- [CSLib paper (arXiv 2602.04846)](https://arxiv.org/abs/2602.04846)
- [Hennessy-Milner in CSLib (arXiv 2602.15409)](https://arxiv.org/abs/2602.15409)
- [Aesop GitHub](https://github.com/leanprover-community/aesop)
- [Plausible GitHub](https://github.com/leanprover-community/plausible)
- [Lean-SMT (arXiv 2505.15796)](https://arxiv.org/abs/2505.15796)
- [Mathlib4 GitHub](https://github.com/leanprover-community/mathlib4)
- [Lean 4 conv tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/)
- [Lean 4 well-founded recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
- [Lean 4 tactic cheatsheet (Oct 2025)](https://leanprover-community.github.io/papers/lean-tactics.pdf)
- [Calculating Compilers Coq supplement](https://github.com/Marcoj776/Calculating-Compilers)
