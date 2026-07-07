---
type: design-question
title: "FBIP (Functional But In Place): static in-place reuse justified by the value-grade (verified enabler, compiled-path optimization)"
description: "turn functional updates into in-place reuse, justified STATICALLY by the value-grade (grade-1 = unique)"
status: open
area: tooling
ties: ["Q27", "Q33", "ADR-0066"]
see-also: ["docs/notes/design-space-map.md"]
---
**Question**: should BANG support FBIP — turning functional data updates (build a new constructor from
an old one) into IN-PLACE memory reuse (O(1) instead of O(n) allocation) — and if so, HOW, given
bang's verified-compilation discipline?

**Why it matters** — FBIP (Koka / Perceus: Reinking-Xie-de Moura-Leijen) is what makes purely-functional
data structures competitive with imperative ones: `map`/tree-update/etc. reuse the consumed
constructor's memory instead of allocating. It is the perf story for a language whose data is
immutable by default. The operator's intuition is right — **FBIP is a COMPILATION-PATH optimization,
not a reference-semantics change**: a program with FBIP computes the SAME values (Source.eval, a pure
functional interpreter, has no memory model), just with less allocation.

**The bang-specific twist (load-bearing):** FBIP's CORRECTNESS requires UNIQUENESS — you may only reuse
a constructor in place if its old value is DEAD (no other live reference). Koka proves this DYNAMICALLY
(Perceus = precise reference counting at runtime). **BANG already has the type-level uniqueness: the
value-GRADE** (QTT multiplicities 0/1/ω — the value-grade of Q27, `HasVTy`/`HasCTy`'s resource
discipline). A value used LINEARLY (grade 1) is provably the last reference — EXACTLY FBIP's
precondition. So bang's grade (a verified invariant) is the ENABLER for FBIP: "the constraint is
generative" (SOUL) — the grade is what lets the reuse fire, PROVABLY. Potentially an ADVANTAGE over
Koka: **STATIC grade-justified reuse** (compile-time, no runtime RC) vs Koka's dynamic RC-based FBIP.

**Where it sits (the stratification):** the OPTIMIZATION is compiled-path (CalcVM→WasmFX / the
runtime's memory reuse — invariant #7, performance second-class); the ENABLING INVARIANT is the
verified value-grade (kernel-path). The grade is the SEAM — verified core (uniqueness) + optimized
output (in-place reuse). This is the exact stratification pattern, applied to memory.

**Detail / dependencies**:
- Needs the value-GRADE surfaced/enforced (currently defaulted to ω, ADR-0066; Q27 is "surface the
  grade axis"). FBIP wants the grade-1 (linear) case reliably tracked.
- Interacts with the MEMORY MODEL (design-space-map #10: grades give use-once, not borrowing — FBIP is
  the use-once payoff).
- A verified FBIP would be a COMPILED-PATH proof: the reuse preserves the reference semantics *given*
  the grade-1 uniqueness. Koka's Perceus is the reference (but RC-based, dynamic); the grade-based
  static variant is the bang-native question.

**Options**: (1) **static grade-justified reuse** (recommended direction — compile-time, no runtime
RC, leans on bang's existing grades; the on-thesis version). (2) Perceus-style dynamic RC (Koka's
proven approach; a runtime, not grade-based — less on-thesis but battle-tested). (3) no FBIP
(functional-immutable, accept the allocation cost — invariant #7 says a slow correct path is fine
until it touches the user).

**Recommended**: record (1) as the direction; it's post-v1 perf, gated on the value-grade being real
(Q27) and the memory-model choice (#10). Design-first when perf on immutable data actually bites.

**Blocked on**: the value-grade surfaced + enforced (Q27); a memory-model decision (#10). Both post-v1.

**Revisit signal**: perf pressure on immutable data-structure updates (map/tree/list rebuild); OR
taking up Q27 (the grade axis) — FBIP is the concrete payoff that motivates surfacing the value-grade;
OR the memory-model / borrowing decision (#10).
