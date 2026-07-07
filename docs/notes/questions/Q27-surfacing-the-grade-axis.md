---
type: design-question
title: "Surfacing the grade axis: declare effect shape AND grade (resumption grade → compilation)"
description: "declare the effect ROW + the GRADE; surface the resumption grade (→ the compilation strategy)"
status: open
area: type-system
ties: ["Q30", "ADR-0001", "ADR-0066"]
see-also: ["#35", "#36", "docs/notes/design-space-map.md"]
---
**Question**: should the surface let a program declare, alongside its effect ROW (`! {ρ}`, WHICH
capabilities it depends on), the GRADE it wants (HOW those effects/resources are used)? The kernel
already tracks both axes (`HasCTy` carries `EffRow = Finset Label` AND `GradeVec Mult`, separately);
the surface hides the grade (ADR-0066 defaults it to `ω`). This asks whether — and where — to expose it.

**Why it matters**: the row and the grade are ORTHOGONAL and bang is unusually positioned to surface
both (it is *graded* CBPV — most effect languages have rows XOR quantitative types; Granule is the
one neighbour with both). The payoff is concentrated in ONE of the grades (below): the **resumption
grade** determines the compilation strategy, which is the generative-constraint move — a declared
invariant that lets the machine-calculation fire a cheaper machine.

**Detail** — "the grade" is THREE distinct notions; conflating them is the trap:
```
grade attaches to…    means…                                buys…
──────────────────────────────────────────────────────────────────────────────────
a VALUE / variable    QTT use-count of `x` (0/1/ω)          linear resources: use-once tokens,
  (coeffect)                                                  in-place update (design-map #10:
                                                              grades give use-once, NOT borrow)
RESUMPTION            how many times a handler invokes `k`   THE compilation strategy ← the win
  (handler property)    abort=0 / tail=1 / general=ω           (see table); #35/#36
an EFFECT's use        per-label multiplicity in the row     quantitative effect bounds — ★ THE TRAP
  (a graded row)                                              (see below)
```
The resumption-grade payoff — why it is the killer:
```
declared grade   handler behaves like    compiles to
0 (abort)        exception               a jump — no continuation saved
1 (tail)         state / reader          a plain stack frame — no copy
ω (general)      generators / backtrack  heap-allocated resumable closure (expensive)
```
Without the declaration every handler compiles as the ω worst case (copy the continuation); with it,
`state`/`throws` compile to a stack discipline. Koka (`fun`/`ctl`/`brk`), Effekt (2nd-class handlers),
OCaml-5 (one-shot conts) all found declaring resumption multiplicity worth it.

**THE TRAP — do not grade the ROW.** Making the row carry a per-label multiplicity (`state ↦ 3`) is a
graded monad, and it is FORECLOSED by invariant #2 / ADR-0001: rows are SETS (idempotent, union=join,
never a multiset), and the set structure is load-bearing for `no_accidental_handling` + the
join-semilattice effect-safety (Yoshioka ICFP'24, cited in the kernel). A per-label-weighted row IS
the forbidden multiset. So the grade must live BESIDE the row (on resumption / handler / value),
never INSIDE it — keep the two axes orthogonal exactly as the kernel already does
(`Finset Label × GradeVec Mult`). "Declare both" = two separate declarations, not one fused graded row.

**Options**: (1) **surface the resumption grade only** (a `tail`/`abort`/general annotation on a
handler; unlocks the no-copy compile) — highest value, tightest scope, aligns with #35/#36. (2) also
**surface value-grades** (a `once` on a consumable capability / linear thunk) — real but more
speculative for v1 (grades give use-once, not borrowing). (3) **status quo** (default ω, hide grades)
— the current pragmatic floor.

**Recommended**: (1) opt-in, exactly where it buys the machine strategy — a resumption annotation on
a handler clause, feeding the calculated-machine choice. Do NOT surface grades everywhere (inference
is HARD — design-space-map; ω-default is the right floor). Value-grades (2) wait for a concrete
resource use-case. The row stays a set (never option-graded-row).

**Blocked on**: #35/#36 (the resumption-grade multiplicity: abort/tail/general in the kernel/machine)
— surfacing needs the kernel distinction to exist first.

**Revisit signal**: #35/#36 landing (resumption grades in the machine); OR a compilation pass that
wants to avoid continuation-copying for tail-resumptive handlers; OR a consumable-capability
use-case that wants linear (use-once) effect typing.
