---
type: design-question
title: "Memory model: immutability + QTT + refcounting vs ownership/lifetimes; substrings, copies-vs-refs, the three axes"
description: "immutability makes aliasing free (substrings = views); QTT carries only the optimization axis — no lifetimes"
status: open
area: tooling
ties: ["Q27", "Q30", "Q31", "ADR-0074"]
see-also: []
---
**Question**: what memory model does BANG need — copies vs references, when a reference becomes a copy,
substrings/slices — and is QTT (the grades, Q27) ENOUGH, or do we want Rust-style ownership + lifetimes?

**Why it matters** — strings (ADR-0074) surface it concretely (a substring: copy the buffer, or a view
into it?), but it's the general data-representation question. The answer decides how much type-system
machinery BANG carries for memory safety + performance.

**The reframe (load-bearing): immutability dissolves most of Rust's problem.** Rust's borrow checker
exists for ONE reason — prevent *mutation through one alias while another observes*. BANG is
immutable-by-default, so **aliasing is ALWAYS safe** (nobody mutates it out from under you) ⟹ a
substring is a free VIEW (pointer + offset + len), no copy, no borrow checker needed for safety. The
"exclusivity XOR sharing" discipline that makes Rust hard evaporates.

**The three ORTHOGONAL axes (the key structural insight — don't bundle them into "ownership"):**
```
axis          question                    tool                             notes
────────────────────────────────────────────────────────────────────────────────────────
SAFETY        can I share/alias?          immutability                     FREE (always yes); substrings = views
RECLAMATION   when do I free it?          refcount / GC (RUNTIME concern)   a slice holds a ref → buffer outlives
                                                                            it → no use-after-free; NOT lifetimes
OPTIMIZATION  in-place / avoid a copy?    QTT grades (mult. 1 = unique)     THIS is where the grade earns its
                                                                            keep → FBIP (Q30)
```

**Ref → copy: at the MUTATION boundary, decided by the GRADE.** Mutation is opt-in; there ref-vs-copy is
decided: **grade 1 (unique/linear) → in-place update, NO copy (= FBIP, Q30); grade ω (shared) →
copy-on-write.** The QTT multiplicity IS the ref→copy switch — the same mechanism as Q30.

**Is QTT ENOUGH? — YES.** Three axes, three tools; QTT carries only the OPTIMIZATION axis (uniqueness),
not safety. Immutability removes mutation → safety free. Refcounting reclaims functional data → no
lifetimes. QTT grades carry uniqueness → in-place. So **Rust-style ownership/lifetimes are NOT needed
for CORRECTNESS.** They'd return only for GC-FREE DETERMINISTIC memory (embedded/real-time — freeing
without refcount overhead), addable as an OPT-IN region/linear discipline LAYERED over the QTT base —
later, second-class (invariant #7), if it bites.

**⚠ The honest caveat (reclamation axis):** refcounting is precise only for ACYCLIC data. BANG's
`let rec` desugars to Landin's knot (ADR-0073), which creates a genuine HEAP CYCLE (the knot references
itself) → plain refcounting would leak recursive closures. Perceus/Koka handle this (mostly-acyclic +
a cycle fallback); the μ-knot sharpens it. NOT a reason to reach for lifetimes — a reason the
reclamation strategy is not a pure free lunch. Open sub-question.

**The other two attributes:**
- **Constant length** (fixed-size string/array) → tracked via DEPENDENT/refinement types (`Vec n`,
  length in the type — Q31). Buys bounds-safety by construction + stack allocation. A CORRECTNESS
  feature on the Q31 road, not now.
- **Space locality** (contiguity) → a RUNTIME REPRESENTATION concern (packed buffer vs cons-list —
  ADR-0074's deferred packed runtime), NOT a type-tracked correctness attribute. A layout HINT (à la
  Rust `#[repr]`) could surface later; second-class (invariant #7).

**Options**: (1) **immutability + QTT + refcounting** (recommended — no ownership/lifetimes; the three
tools cover the three axes; on-thesis). (2) add Rust-style ownership/lifetimes (rejected for correctness
— immutability makes it unnecessary; reconsider only for GC-free memory as opt-in). (3) tracing GC (a
reclamation option that sidesteps the cycle caveat, at pause-time cost).

**Recommended**: (1). Substrings = views (immutability dividend); ref→copy at the grade-decided mutation
boundary (Q30 FBIP); constant-length via Q31; locality a deferred runtime concern. Resolve the
reclamation-of-cycles sub-question (refcount+fallback vs GC) when a real runtime is built.

**Blocked on**: the value-grade surfaced/enforced (Q27); a real runtime (reclamation is a runtime
concern — the interpreter/calculated-machine has none yet); Q31 for constant-length. All post-v1.

**Revisit signal**: building a real runtime / GC (the reclamation axis goes live — settle refcount vs
GC + the μ-knot cycle); OR perf on immutable data / substrings (the view-vs-copy + FBIP payoff, Q30);
OR GC-free deterministic-memory need (the one case ownership/lifetimes return, opt-in). Ties
[[Q27 grades]], [[Q30 FBIP]], [[Q31 refinement/dependent]], ADR-0074 (strings).
