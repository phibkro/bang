# ADR-0032 · `group_recovers` RETIRED — rollback is a handler mechanism, not an effect-algebra inverse

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: `group_recovers` RETIRED — the rollback law is false-as-`≈`, vacuous, and redundant; v1 rollback is the txn handler. Supersedes 0018's group-row.
- **Resolves**: Q8
- **Depends-on**: 0018, 0030, 0031, 0001

- **Status:** Accepted + **LANDED** (2026-06-23, this retirement commit) — `group_recovers` DELETED from
  `Bang/Spec.lean` §6 and its `#print axioms` line from `Bang/Audit.lean`. `≈` UNCHANGED (the whole point —
  no LR-spine re-derivation). Supersedes the "group ⇒ rollback" row of ADR-0018's Trinity. NOTE: `Bang/LR.lean`'s
  §6 algebra (`seqComp`/`idComp`/`recover`) was concretized from axioms to defs by ◊4 U1 (`a58a396`) — so the
  spike's original "`LR.lean` UNCHANGED" framing is superseded; `recover` is now an unused def, retained pending
  a later cleanup.
- **Date:** 2026-06-23
- **Layer:** P (proof / spec semantics — the observational-equivalence `≈` and the §6 recovery algebra). Couples to `lr_sound` (stated over `≈`).
- **Resolves:** OPEN_QUESTIONS Q8 (`Eff` group ⇒ `F` dagger-Frobenius?) — verdict: the bridge as stated is **unsupported by the literature**; Q8 stays unresolved-but-bounded.
- **Reference:** Heunen–Karvonen, *Reversible Monadic Computing* (`references/papers/adjacent/heunen-karvonen-reversible-monadic.pdf`), abstract + §4 + §5; ADR-0001/0018 (rows are a join-semilattice with OrderBot); ADR-0016 §risks (flagged `group_recovers` may force revising `≈`).

## Context — the statement and what it actually asserts

`group_recovers` (`Bang/Spec.lean:157`, FROZEN):
```
theorem group_recovers [AddGroup Eff] {c : Comp} : seqComp c (recover c) ≈ idComp
```
stated inside a section with `variable {Eff} [Lattice Eff] [OrderBot Eff]`. So its full
hypothesis set is `[Lattice Eff] [OrderBot Eff] [AddGroup Eff]`.

The §6 recovery algebra is **defined**, not axiomatized (`Bang/LR.lean:34–46`):
- `seqComp c₁ c₂ := Comp.letC c₁ (Comp.shift c₂)`  — run `c₁`, discard its value, run `c₂`
- `idComp := Comp.ret Val.vunit`                    — the pure no-op `ret ()`
- `recover _c := idComp`                            — recovery scaffold is the IDENTITY

`≈` is plain contextual equivalence over fuel-bounded convergence
(`ctxEquiv`, `Bang/LR.lean`): quantify over all `Cxt = EvalCtx`, compare `Converges`.

Unfolding the conclusion: `seqComp c (recover c) = seqComp c idComp = (c ; ret ())`.
So the claim is **`(c ; ret ()) ≈ ret ()`** — "running `c`, discarding its result, then
returning unit, is observationally indistinguishable from just returning unit."

## The three findings (each sourced + machine-checked)

### 1. The conclusion is `Eff`-free; the `[AddGroup Eff]` hypothesis cannot reach it.
`Comp` is a plain `inductive Comp : Type` (`Bang/Core.lean:91`) — **not parametric in
`Eff`**. `seqComp`/`recover`/`idComp : Comp → …` carry no `Eff`. So no instance on `Eff`
can constrain the conclusion. `group_recovers` is therefore NOT dischargeable by exploiting
the hypothesis — the hypothesis is inert. (This rules out a cheap ex-falso/vacuity close.)

### 2. The conclusion is FALSE as a plain equivalence.
`(c ; ret ()) ≈ ret ()` fails for any `c` that (a) diverges — then LHS never converges in
any context where RHS does — or (b) performs an observable effect a context can witness.
A genuine rollback law must SAY the effect of `c` is undone; this definition's `recover`
discards `c` entirely and asserts `c` was unobservable. The `recover _c := idComp` comment
(`Bang/LR.lean:38`) admits the inversion is meant to be "carried by the relation" — but `≈`
has no group structure to carry it. **The proof gap is real and the statement-as-`≈` is wrong**,
not merely hard.

### 3. The hypothesis triple is SATISFIABLE — but only by the trivial one-point effect algebra.
Machine-checked (`nix develop`, Lean):
- `AddGroup (Finset ℕ)` — **synthInstanceFailed**. The concrete `EffRow := Finset Label`
  (`Bang/EffectRow.lean:43`) has **no** `AddGroup` instance, and none can exist nontrivially
  (Finset union is idempotent ⇒ no inverses). So for the SHIPPING effect type the theorem
  cannot be instantiated at all.
- `[Lattice PUnit] [OrderBot PUnit] [AddGroup PUnit]` — **all synthesize** (OrderBot
  constructed by `bot := unit`). So the triple is consistent, satisfied ONLY by the one-point
  algebra (⊥ = ⊤ = the single effect = "no effect"). A bounded lattice that is also a group
  is forced trivial. The hypothesis is **vacuous-but-consistent**, not contradictory.

Net: `group_recovers` is **conditionally stated for a structure no v1 effect inhabits**, and
its conclusion is independently false as a plain `≈`. It is honestly bounded, not load-bearing.

## Q8 verdict — the Heunen–Karvonen bridge does NOT hold as stated

Q8 asks: `Eff` a group ⇒ graded monad `F` dagger-Frobenius (⇒ `group_recovers` a corollary)?

H-K's actual result (abstract; §4–§5): effectful (Kleisli) computations are reversible
**iff the monad is a FROBENIUS monad**; and "any monoid gives a strong monad, **Frobenius
MONOIDS give strong Frobenius monads**" — an adjunction, converse only in the Frobenius setting.

So the honest condition is **much stronger than "group"**: the effect monoid must be a
**Frobenius monoid** — involutive AND satisfying the Frobenius coherence law (1.1) between
multiplication and its dagger-comultiplication. A group is an involutive monoid (inverse =
involution) but that does NOT discharge the Frobenius law. **The bridge "group ⇒ dagger-
Frobenius ⇒ rollback" is unsupported.** Q8 stays unresolved; the literature says the right
notion is Frobenius monoid, which our join-semilattice `Eff` (idempotent, no inverse) is
even further from than a group.

## Decision

**RETIRE `group_recovers`** (orchestrator decision 2026-06-23, sharpening the spike's (C)):

1. **DELETE the theorem** from `Bang/Spec.lean` §6 + its `#print axioms` line from `Bang/Audit.lean`.
   The spike recommended *keeping* it `sorry`, but finding #2 shows it is **FALSE-as-stated**, not merely
   vacuous — and a false frozen theorem left `sorry` is a permanent landmine: it can never be honestly
   discharged, and it misrepresents the spec (a future session could mis-"prove" it or read it as intended
   law). A false statement is removed, not parked.
2. **Do NOT add a side-condition to `≈`** (rejected — see below). `≈` stays exactly as `lr_sound`/
   `lr_fundamental` need it ⇒ **zero LR-spine re-derivation** — preserved by retirement just as by (C).
3. **The real v1 rollback law already exists**: `all_or_nothing_abort` (ADR-0030/0031, PROVEN axiom-clean
   `84e3ab3`). STM rollback is a HANDLER mechanism (abort = a `throws` escaping the `transaction` frame,
   dropping its heap with it), NOT an effect-algebra inverse — so `group_recovers` was redundant as well
   as false.
4. **Q8 stays unresolved-but-bounded** (the H-K Frobenius-monoid bridge is unsupported for our idempotent
   join-semilattice `Eff`; see below). If group-effect rollback is ever revisited post-v1, restate it
   correctly (a Frobenius condition, not merely `AddGroup`) as a NEW theorem — do not resurrect this one.

## Rejected alternatives

- **(A) provable as-is.** Rejected: finding #2 — false as a plain `≈`; finding #1 — hypothesis
  inert. No lemma/paper closes it without changing the statement or `≈`.
- **(B) add an observability side-condition to `≈`.** The minimal patch would be to weaken `≈`
  to a `RowMonotone`/effect-free–restricted equivalence under which `(c;ret()) ≈ ret()` holds
  only for unobservable `c`. **Rejected** because: (i) it changes `≈`, which `lr_sound` is
  stated over (`Bang/Spec.lean:139`), forcing re-derivation of the LR spine — high cost paid
  for a theorem that constrains NO v1 effect (finding #3); (ii) it is a side-condition on the
  *spec notion of equality* to rescue a law about a structure nothing inhabits — the tail
  wagging the dog. The honest floor is to bound the claim, not to bend `≈`.
- **Materialize `recover` as a real inverse-effect term.** Rejected: needs group-effect
  operations the kernel lacks, i.e. a 6th primitive — violates CLAUDE.md invariant #5.

## Consequence for `lr_sound` / `≈`

**None.** This is the point of choosing (C): `≈` is untouched, so the Unit 5 `lr_sound`/
`lr_fundamental` derivations proceed over the existing definition with no amendment. Had we
taken (B), every theorem stated over `≈` would re-derive. Sequencing `group_recovers` early
(PROOF_ORDER #2) did its job: it surfaced that the rollback law is empty for v1 BEFORE the LR
spine committed to any `≈`-shape change.
