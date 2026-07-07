---
type: design-question
title: "Data types: ADTs, inductive/coinductive, law attachment"
description: "iso-recursive ADTs (sum/product/μ), inductive-only; laws via assert + plausible"
status: decided
area: type-system
resolved-by: ["ADR-0029"]
ties: ["Q16", "Q19", "ADR-0026", "ADR-0028", "ADR-0029"]
see-also: []
---
**Resolution**: **Iso-recursive ADTs** — extend `VTy` with sum (`+`), positive product (`×`), and
iso-recursive μ (`fold`/`unfold`, which erase). **Inductive only** (coinductive → the Div fragment,
ADR-0028). μ-recursion variables are **not** polymorphism (a fixpoint binder, not `∀`), so ADR-0027's
monomorphic v1 is preserved. User-definable (the moat needs it): `List = μX. 1 + (Int × X)`. Laws via
assert + `plausible` (ADR-0026). Iso over equi because the functional difference is zero but
equi-recursive type equality is coinductive (brutal metatheory); the surface hides `fold`/`unfold` in
constructors/patterns (Q20). See **ADR-0029**. Original deliberation below.

**Question**: the kernel has `unit` + `int` only. How do users define data types — products, sums,
recursive (μ) types, GADTs — and how do **inductive** (terminating, total) vs **coinductive**
(productive, the event loop) types lower to graded CBPV? How do a type's **laws** (Q19) attach to it?

**Why it matters**: rung 2 (verified stack) needs at least products/lists; the moat (laws between
operations) needs user-defined types to attach laws to. Coinduction is needed for productive
non-termination (Q16 — the xv6 scheduler loop, reactive streams rung 4).

**Detail**: CBPV already splits value/computation; ADTs are *value* types (sums + products), with
recursion via a μ/fixpoint. Inductive = least fixpoint (total, foldable); coinductive = greatest
fixpoint (productive, the `Div`/stream side of Q16). The grades index data too (a linear pair vs an
unrestricted one). Open: whether bang has full inductive *families* (dependent, Agda-style) or simple
ADTs (Haskell/OCaml-style) + refinement — this is gated by ADR-0026 (the ladder: structural ADTs +
laws-on-the-ladder, NOT full dependent inductive families in the kernel).

**Options**: (1) simple ADTs (sum/product/μ) + laws via assertions on the ladder (ADR-0026-consistent;
recommended); (2) full dependent inductive families (Agda/Lean) — rejected per ADR-0026 (proof-assistant
in the kernel); (3) Church/CBPV-encoded data (no new kernel types, encode via `U`/functions) — elegant
but poor ergonomics + performance; possibly an *internal* lowering target.

**Blocked on**: nothing structural; forced at rung 2.

**Revisit signal**: building rung 2 (the verified stack) — it needs the first user data type.
