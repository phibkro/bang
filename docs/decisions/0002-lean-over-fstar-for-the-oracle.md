# ADR-0002 · Verify the reference in Lean 4 + Mathlib, not F\*

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0001 (Mathlib gives the row algebra free), 0004 (the reference is what the VM is calculated against)

## Context

The verified reference / oracle needs a proof-language substrate. F\* was the initial pick (SMT auto-discharge, first-class OCaml extraction). The amnesiac-team model makes **agent-maintainability of the proofs** the dominant constraint: a fresh session must be able to read and repair the proofs.

## Decision

Use **Lean 4 + Mathlib** as the verified-reference substrate. Keep F\* only as an optional alternate oracle (the harness is language-agnostic, so both can coexist as a differential check).

## Rationale

- **Agent fluency:** Lean is the center of gravity for AI/proof work (large corpus, strong tooling, proof-state introspection). A fresh agent can actually maintain Lean proofs — the whole point of the model.
- **Proof stability:** no Z3 timeout/trigger roulette. Lean proofs are more stable across sessions; SMT brittleness is the amnesiac killer.
- **Mathlib gives the algebra free** (ADR-0001): `Finset` is already a `Lattice`/`OrderBot`; `canon_unique` is definitional via `Finset.ext`.
- **Term-mode proofs are local and legible**; Lean compiles to C, so the reference is itself a runnable binary.

## Rejected alternatives

| option | why not |
|--------|---------|
| **F\*** | SMT brittleness across sessions; sparse training corpus. (Kept as alternate: auto-discharges arithmetic with less manual proof; OCaml extraction first-class) |
| OCaml/Coq(Rocq)/Agda | weaker corpus/tooling/explicitness tradeoffs for an agent (see roadmap reading + the language ranking) |
| Dafny / Idris 2 | tiny corpus; Dafny's SMT can silently weaken specs to "pass" |

## Consequences

- (−) More manual proof for arithmetic-flavored obligations. (`unify_sound` is now **proven** — it needed a freshness precondition on the open/open case; see `EffectRow.lean`.)
- (−) Divergence/coinduction (partiality monad, bisimilarity) is more effortful in Lean than in Rocq — relevant at K3.
- (+) The harness doesn't care what language the oracle is in; switching cost was one `.fst` → `.lean` file, everything else stood.

## Revisit if

You need the oracle as an **OCaml module** (not a binary) for direct linking, **or** Lean's coinduction story blocks the K3 divergence proofs badly enough to outweigh the agent-fluency win. In either case F\* (already scaffolded) is the fallback.
