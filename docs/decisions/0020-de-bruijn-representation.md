# ADR-0020 · De Bruijn indices for the term representation

- **Status:** Accepted
- **Date:** 2026-06-21
- **Layer:** K (kernel — term syntax, substitution, typing context)
- **Supersedes:** the implicit named-variable choice in `PATH-graded-cbpv-eval.md`
- **Amends:** ADR-0019 (the Finsupp grade-vector split was the *named*-encoding fix for context alignment; de Bruijn fixes it positionally, so the grade context reverts to a positional structure — see Consequences)
- **Resolves:** OPEN_QUESTIONS Q11 (open-term substitution) → option C
- **Related:** Torczon et al. OOPSLA 2024 (`resource/CBPV/`, de Bruijn + autosubst2 — the port source we now match)

## Context

The kernel used **named variables** (`Var := String`): `Val.vvar : Var`,
`Comp.lam : Var → Comp`, typing context keyed by name. Proving the *first*
metatheory theorem — `subst_value`, graded value substitution — exposed that this
representation is wrong for the job. Getting the lemma merely *true* required a
cascade of side-conditions, **four of them caught by machine-checked
`example : False`** (commits b853dde → e1e4920):

| # | side-condition the named encoding forced | what de Bruijn gives |
|---|---|---|
| 1 | `v` closed (typed in `[]`) — `Comp.subst` isn't capture-avoiding | bound indices shadow positionally; no capture |
| 2 | `γ_Γ x = 0` — `single x ρ + γ_Γ` doesn't pin `x`'s grade | `ρ .: γ` cons separates grades structurally |
| 3 | `∀ C, (x,C) ∉ Γ` — duplicate keys mis-type `vvar` | positions are unique by construction |
| 4 | `γ y = 0` on `lam`/`letC` — bound-var-grade invariant | the cons carries it for free |
| 5 | `vvar` lookup is **non-deterministic** under shadowing (`lam x (… vvar x …)` resolves `x` to the binder *or* a deep slot, at different types) | de Bruijn index 0 *is* the nearest binder; deterministic |

Each fix made the rules heavier and the proof more conditional; #5 would have
changed `vvar`'s *lookup semantics* (touching every typing proof). The proof
machinery itself was sound — 12 lemmas closed axiom-clean — but it was fighting
the representation at every binder. This is precisely why the mechanized
reference (Torczon, `resource/CBPV/`) uses de Bruijn + autosubst2.

The named encoding bought readable terms; it cost correctness-by-construction at
every binder. The trade is wrong for a *verification* kernel: here, terms are read
through the proof assistant, and the binder invariants are the whole game.

## Decision

**Represent variables as de Bruijn indices.** Concretely:

```
Val.vvar : Nat → Val                 -- a de Bruijn index, not a name
Comp.lam : Comp → Comp               -- binder name dropped (position 0 = the arg)
Comp.letC : Comp → Comp → Comp       -- binder name dropped
Comp.subst → de Bruijn substitution  -- single subst at index 0 with shift/lift
```

The typing context becomes **positional** (index `i` ↦ the `i`-th entry), so it
needs no names and no well-formedness side-condition. Keeping ADR-0019's "grades
split, types ambient" insight, the cleanest shape is a positional grade vector
alongside a positional type context — the de-Bruijn cons `ρ .: γ` is just `::`.
The exact carrier (`List (Mult × VTy)` combined, or separate `List Mult` /
`List VTy`, or `Fin n → _` à la Torczon's `gradeVec`/`context`) is an
implementation choice to settle when the rewrite lands; `List`-based is simplest
in Lean and `Ctx.scale`/`Ctx.add` (zipWith/map) become **correct** because de
Bruijn contexts extend in lockstep.

`subst_value` then loses **all** side-conditions — its honest statement is the
clean graded substitution lemma:

```
HasVTy (q .: γ) ... → HasCTy ... → HasCTy ... (subst at 0)
```

## Rationale

- **Correctness by construction.** All five binder invariants become structural
  — unrepresentable-illegal-state, not checked-side-condition. This is the
  project's root value (`SOUL.md`), applied to syntax.
- **Matches the port source.** Torczon's Coq is de Bruijn; substitution,
  renaming, and preservation port near-directly instead of being re-derived
  against a hostile representation.
- **The tax compounds downstream.** `preservation`'s β-case calls `subst_value`;
  `progress`, `type_safety`, `effect_sound`, and the LR all thread the context
  discipline. Five side-conditions on one lemma would have become five on every
  theorem. Paying once, structurally, is cheaper than paying per-theorem.
- **The evidence is empirical, not aesthetic.** Four machine-checked `False`s
  (history `b853dde`..`e1e4920`) are the justification; this is not a
  speculative refactor.

## Rejected alternatives

| option | why not |
|--------|---------|
| Keep named + deterministic `vvar` (first-match) + the four side-conditions | The 5-fix path. Closes `subst_value`, but every downstream theorem re-pays the named tax, and `vvar`-lookup-semantics changes touch every typing proof. Premature pragmatism — finishes the lemma, degrades the kernel. |
| Named + a unified `WfCtx` invariant (Barendregt convention) | Replaces scattered side-conditions with one threaded predicate — but you still *thread* it everywhere de Bruijn makes it structural. Half-measure. |
| Locally nameless (de Bruijn bound, names free) | Avoids some shifting, but adds the open/close (`instantiate`/`abstract`) bureaucracy and a second representation to reason about. Pure de Bruijn matches the port source with one discipline. Reconsider only if open-term ergonomics bite. |

## Consequences

- (+) `subst_value` and all metatheory statements shed their side-conditions;
  the kernel rules shed the `γ y = 0` / context-wf premises added in `e1e4920`.
- (+) `preservation`/`progress`/`type_safety` proofs start from a clean base.
- (−) **Rewrite scope** (the real cost): `Bang/Core.lean` (syntax + context),
  `Bang/Operational.lean` (de Bruijn `subst` with shift/lift, `step`, `eval`),
  `Bang/Syntax.lean` (all typing rules), `Bang/Spec.lean` (statements simplify),
  `Bang/Metatheory.lean` (redo — the grade arithmetic and proof structure port;
  weakening becomes a shift lemma). ~ADR-0019-sized, concentrated in the kernel.
- (−/~) **ADR-0019 partially superseded.** The Finsupp `Var →₀ Mult` grade-vector
  solved the *named*-key alignment problem; de Bruijn solves it positionally, so
  the grade context reverts to a positional list/vector and `Ctx.scale`/`Ctx.add`
  (retired by 0019) return — now correct by construction. The "grades split,
  types ambient" insight from 0019 carries over; only the carrier changes.
- (~) **Readability.** Terms become index-bearing. Mitigation: a pretty-printer /
  named-surface layer at the edges if needed (post-kernel); the kernel itself is
  read through proofs, where indices are fine.
- (=) **Unaffected:** the effect-row unifier (`Bang/EffectRow.lean`, `Finset
  Label`) and `tools/selfcheck.mjs` test the *row algebra*, not the term language.
  `OpId`/`Label` stay as-is. The legacy `Bang.Eval` / `Calc*` machines are a
  separate namespace and untouched.

## Revisit if

- Open-term *surface* ergonomics (examples, error messages, differential tests at
  the term level) become painful enough to want locally-nameless — re-weigh then,
  with the kernel already de Bruijn underneath.
- A future binder form (e.g. a richer handler that binds) needs multi-variable
  abstraction — extend the shift/lift discipline, don't revert.
