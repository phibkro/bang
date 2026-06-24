# ADR-0017 · K3 calculated-machine retrospective (supersedes ADRs 0010–0014)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: K3 calculated-machine retrospective — composition-mechanism map + methodology; replaces the five per-machine ADRs.
- **Supersedes**: 0010, 0011, 0012, 0013, 0014
- **Depends-on**: 0009, 0008

- **Status:** Accepted (retrospective; replaces five per-machine ADRs that were execution records)
- **Date:** 2026-06-21
- **Layer:** C (compiler methodology — what the K3 staging taught)
- **Replaces:** 0010 (CalcHO/CalcCBN), 0011 (CalcEff/CalcSt), 0012 (CalcCBNEff), 0013 (CalcCBNSt), 0014 (CalcCBNEffSt) — DELETED
- **Related:** 0009 (calculation method, staged), 0008 (free-monad reference), 0015 (reification frontier, the genuine open), 0016 (two-hop architecture; the ◊3 port re-unifies these machines)

## Context

K3 (effects-over-closures, calculated machines) was staged across five increments, one per machine, each with its own ADR. With the third design revision (ADR-0016) moving to graded CBPV, the five per-machine machines collapse into a single unified graded-CBPV calculated machine at checkpoint ◊3 (see `ROADMAP.md`). The five ADRs documenting each machine in isolation are no longer load-bearing — they were *execution records* of a methodology, not enduring decisions.

This retrospective replaces them, preserving the **insights** (which carry forward) without the per-machine implementation diary (which doesn't).

## What's preserved — the load-bearing learnings

### 1. Methodology: calculate one construct at a time, then compose

(Was the through-line of all five ADRs; rooted in ADR-0009.) Bahr–Hutton monad-swap; spec-guided definition + post-hoc `exec ∘ compile ≡ eval` proof (the derivation lives in `-- derived, not designed` comments). Differential-test each machine against `eval`. The harness earned its keep: built defs-first, the fuzz found the eager-int-check divergence in `CalcCBNEff`'s `add` *before* any proof effort was spent.

### 2. Fuel-indexed `Option`, not partiality monad

Faithful to the operational reference (ADR-0008). Structural recursion on fuel; fuel insufficiency is an honest "don't know" returning `none`, not a divergence claim. Honest delta from Bahr–Hutton 2022 (which uses the partiality monad).

### 3. Shared `Value` type → correctness is equality, not logical relation

(Was the load-bearing decision of original ADR-0010.) Source-closures carry the source body + captured env, and the **same** `Value` is used by `eval` and the machine. Correctness becomes an *equality* of values, not a cross-representation logical relation. The usual pain of higher-order compiler correctness simply doesn't arise.

### 4. Effect-shape → composition-mechanism map (the real intellectual output)

The five-way staging *answered* the question "what's the minimum machinery for each kind of effect?" — and the answer is structural, not per-effect:

| effect shape | composition mechanism over the closure core |
|---|---|
| **zero-shot** (abandons continuation; e.g. Throws) | Nested meta-run with empty handler stack; re-throw `uncaught` at the meta-call boundary |
| **one-shot tail** (resumes in tail position; e.g. State) | Thread the register through the nested meta-runs; no re-throw, no flatten |
| **non-tail / multi-shot** (reifies the continuation) | Flatten to a control stack + reify the resumption as data |

This map *answered* the open question "does composing State force a CEK-style flatten?" — **no, it doesn't.** Only reification triggers the flatten. The flatten is solely a consequence of non-tail/multi-shot semantics, not of effect composition in general.

### 5. State + Throws interaction: persist, not rollback

(Was original ADR-0014's central decision.) State threads through unwinding; a write before a throw is kept. **Rationale:** STM is the privileged transactional primitive (preserved by ADR-0016); ordinary State is the simple threaded mutable register. Rollback is exactly what STM is for, not a property of plain `get`/`put`.

## What's NOT preserved (deprecated by the ◊3 port)

- **The five-way machine split** (CalcHO, CalcCBN, CalcEff, CalcSt, CalcCBNEff, CalcCBNSt, CalcCBNEffSt). These collapse into one graded-CBPV calculated machine under ADR-0016. The five proven theorems become **historical evidence** that the methodology works; the new unified machine reproves its own equivalence.
- **The per-effect-machine instruction sets** (`MARK`/`UNMARK`/`THROW`, `GET`/`PUT`/`ENTER`/`LEAVE`). Graded CBPV's substrate surfaces effects uniformly; per-effect specialization (if any) moves to the WasmFX lowering, not the canonical machine.
- **CBV / CBN as a calculation-time choice.** Graded CBPV unifies them via the value/computation split and grades on binders. The original ADR-0010 noted "CBN + thunk/force later" as a deferral; under graded CBPV the question dissolves.

## Open follow-up: `runState × throw` semantics

(Deferred from original ADR-0014.) When a throw escapes a `runState`, does the inner state leak (current default, by virtue of the threaded register) or is the outer cell restored on unwind? The decision is independent of the graded-CBPV port; pin it as a focused follow-up when reified handlers land, likely by making `runState` install an unwind-restoring frame.

## Archival reference

The proofs themselves stay in the repo while the ◊3 port is in flight:

- `effectrow-oracle/oracle-lean/Bang/CalcHO.lean` — CBV closures + fuel
- `effectrow-oracle/oracle-lean/Bang/CalcCBN.lean` — CBN over closures (mutual `eval`/`forceV`)
- `effectrow-oracle/oracle-lean/Bang/CalcEff.lean` — Throws as unwinding
- `effectrow-oracle/oracle-lean/Bang/CalcSt.lean` — State as register
- `effectrow-oracle/oracle-lean/Bang/CalcCBNEff.lean` — Throws + CBN closures
- `effectrow-oracle/oracle-lean/Bang/CalcCBNSt.lean` — State + CBN closures
- `effectrow-oracle/oracle-lean/Bang/CalcCBNEffSt.lean` — Throws + State + CBN closures

All remain proven and diff-tested under `make check-lean` (102 tests green at the time of this retrospective). When ◊3 lands and the graded-CBPV unified machine replaces them, they will be archived (a directory move, not a delete) so the proven-evidence corpus survives as a reference.

## Revisit if

- The graded-CBPV port at ◊3 reveals a composition mechanism not anticipated by the map above — likely candidates: cost-grading interacting with effect ordering, or multi-shot interacting with side-effects in ways the per-machine staging never exercised.
- A real effect needs multi-shot or non-tail resumption → triggers the reification/flatten row of the table (the deferred frontier; see ADR-0015).
