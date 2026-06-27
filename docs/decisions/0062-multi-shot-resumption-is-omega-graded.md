# 0062 — Multi-shot resumption is ω-graded by construction; the affine fragment is gradeable

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The "grade the resumption" frontier (**task #35**) asks what multiplicity grade `r` a handler frame carries for how many times it invokes its captured continuation. Decision: record the resumption grade as a stack-grade **homomorphism** `gradeOf : Stack → (Mult, *, 1)` with `resumeMult` (throws=0, state/transaction=1) read off `dispatchOn`'s reinstall behaviour. QTT's `{0,1,ω}` trichotomy settles it: `0` = `*`-zero (throws — frame absent), `1` = `*`-unit (one-shot — **transparent**, vanishes), `ω` = `*`-top (multi-shot — **absorbing**). bang's built-in handlers are all **affine** (throws zero-shot, state/transaction one-shot; genuine multi-shot lives only in `CalcReify`). So **multi-shot resumption is ω-graded BY CONSTRUCTION — a closed mathematical boundary** (Cousot POPL'24 Th II.3.9: no finite variant for unbounded invocation; = the non-idempotence `1+1=ω`), NOT an open `sorry`. The **affine fragment is gradeable by reflexivity** (`one_mul`) — engineering, not research. Declines the transfer-function-grade escape hatch (Ivašković FSCD'20) that *would* recover finite multi-shot grades, because it abandons the scalar QTT the rest of the system is built on (let-rule `(q_or_1 q2)•γ₁ + γ₂`, `F q A` returner grade) for a construct the built-in handlers — and the WasmFX target (ADR-0035) for the affine fragment — do not use.
- **Depends-on**: 0054, 0035, 0030, 0023
- **See-also**: 0059, 0060, 0058

## Status

Accepted (2026-06-27). Records as a **closed design decision** the quantitative half of the "grade the
resumption" frontier (task #35). The qualitative half (effect discharge) and the affine grade-completion are
engineering items routed to inc-6; the multi-shot ω boundary is closed here, not deferred.

## Context

QTT is `{0, 1, ω}`. The resumption-grade question: what finite grade is recoverable, for which handlers?
Three facts settle it, all **verified against the live tree** (`compfresh`/`inc5-comp-grind`):

1. **The built-in handlers are already one-shot.** `dispatchOn` (`Bang/Operational.lean:329`) reinstalls and
   resumes exactly once: `throws → (Kₒ, ret v)` discards `Kᵢ` (**zero-shot**); `state`/`transaction →
   (Kᵢ ++ handleF n h' :: Kₒ, ret …)` keeps `Kᵢ`, reinstalls once, single `ret` (**one-shot**). Genuine
   multi-shot exists only in `CalcReify` (the K3 reification machine, where a `vcont` may run the captured
   continuation twice or more) — a separate development.

2. **QTT carries no order.** `Bang/Mult.lean` provides `CommSemiring QTT` and nothing else; the only
   grade-massaging is `q_or_1 q := if q = 0 then 1 else q` (`Bang/Syntax.lean`), a floor *function*, not a `≤`.
   There is **no subgrading relation**, so any grade obligation is an **equation**, not an inequality. (This
   retracts the `r ⊑ 1` framing of earlier discussion — there is no `⊑`.)

3. **The `+` that combines resumption counts is non-idempotent** (`1 + 1 = ω`, `Bang/Mult.lean`). The only
   fixed point of `γ ↦ γ + γ` is the absorbing `ω`; unbounded invocation has no finite QTT value.

This is Cousot's least-fixpoint-under-approximation-with-a-variant theorem (POPL 2024, Th II.3.8) and its
incompleteness counterexample (Th II.3.9). The relevant variant **already exists in the proof tree**:
`krelS_append` (`Bang/Compat.lean:1146`) recurses on `termination_by (m, Kᵢ.length)`, whose `decreasing_by`
splits along Cousot's two descent mechanisms — `Prod.Lex.right` (structural progress inside one iterate) and
`Prod.Lex.left _ _ hk`, `hk : k < m` (the cross-iterate variant, one drop per resume).

## Decision

Record the resumption grade as a stack-grade homomorphism, and accept the trichotomy it forces.

```lean
/-- Resumption multiplicity, read off `dispatchOn`'s reinstall behaviour. -/
def resumeMult : Handler → Mult
  | .throws _        => 0   -- ABORT: Kᵢ discarded
  | .state _ _       => 1   -- RESUME once, reinstall
  | .transaction _ _ => 1   -- RESUME once, reinstall

/-- Stack resumption-grade: the monoid hom (Stack, ++, []) → (Mult, *, 1).
    `handleF` carries a Nat capability id (ADR-0054); gradeOf ignores it. -/
def gradeOf : Stack → Mult
  | []                       => 1
  | Frame.letF    _   :: K   => gradeOf K
  | Frame.appF    _   :: K   => gradeOf K
  | Frame.handleF _ h :: K   => resumeMult h * gradeOf K

theorem gradeOf_append (S T : Stack) : gradeOf (S ++ T) = gradeOf S * gradeOf T
/-- A one-shot handler frame is GRADE-TRANSPARENT: it contributes the *-unit. -/
theorem gradeOf_handleF_oneShot (n) (h) (K) (hone : resumeMult h = 1) :
    gradeOf (Frame.handleF n h :: K) = gradeOf K   -- by simp [gradeOf, hone, one_mul]
```

Both proofs rely only on `one_mul` and `mul_assoc`, *proven* in `CommSemiring QTT` (`Bang/Mult.lean`).

| handler | `resumeMult` | frame's grade role | `mul`-table fact |
|---|---|---|---|
| `throws` (zero-shot) | `0` | annihilator; `Kᵢ` discarded ⟹ frame absent | `0·x = 0` |
| `state`/`transaction` (one-shot) | `1` | **transparent** (vanishes) | `1·x = x` |
| `CalcReify` multi-shot | `ω` | **absorbing** | `ω·x = ω` (x ≠ 0) |

The one-shot frame lands on the `*`-unit, so appending it across a resume introduces no multiplicity: the
conjunct `gradeOf (Sᵢ ++ handleF n h :: K) = gradeOf Sᵢ * gradeOf K` is reflexivity modulo `one_mul`. The only
QTT value that is not `*`-transparent is `ω`, and one-shot handlers provably never produce it. Multi-shot lands
on `*`-top: a `vcont` invoked `c ≥ 2` times collapses to `ω` (there is no `2` in QTT) — Cousot II.3.9 verbatim
(`P = N`, `fⁿ = {0..n}`, no finite `δ`).

**Therefore:**
- **Multi-shot resumption is ω-graded by construction. Closed, not open** — a mathematical boundary (the
  `*`-top = the non-idempotence of `+` = the failure of Th II.3.8's finite-`δ` clause), not a `sorry`. The proof
  method correctly refuses to certify a finite grade for an unbounded-invocation continuation.
- **The affine (one-shot) fragment is gradeable, and that is engineering, not research.**

## Consequences

### Affine fragment: the remaining engineering (inc-6)
The one-shot conjunct is the reflexivity above. It is gated only on the **binary LR** (`krelS_append` / the
Compat deep block), deferred to inc-6 (ADR-0058) — off the v1 (diagonal) critical path. When inc-6 resumes:
1. Add the `gradeOf` conjunct (`gradeOf_append` + `gradeOf_handleF_oneShot`) to `krelS_append`'s resume clause;
   it discharges by `one_mul`. The conjunct rides `dispatchOn_append_outer` (`Bang/Compat.lean:1085`).
2. Verify no decomp-miss residual remains in that resume path (the `krelS_splitAt_decomp` MISS lineage).

*(The ADR-0054 arity migration the earlier draft listed is already DONE in the live tree — `krelS_handleF`
(`LR.lean:1587`) is the 2-arg `Frame.handleF nh h` form and `dispatchOn_append_outer` threads the cap id `n`.)*

### Rejected alternative: transfer-function grades
A finite multi-shot grade *is* recoverable if the grade generalises from a QTT scalar to a **transfer function**
over resources (Ivašković–Mycroft–Orchard, FSCD 2020, §4.3.2: trivial → refined graded monad). We **decline**
it: it abandons the scalar QTT the rest of the system is built on, to express a construct (multi-shot) the
built-in handlers do not use and the WasmFX affine fragment does not require. If a future analysis needs
flow-sensitive resource grades, reopen against this ADR with the transfer-function pomonoid as the structure.

### Net status
| handler | inhabitation (`KrelS`) | grade `r` | Cousot | tree status |
|---|---|---|---|---|
| `throws` (zero-shot) | proven (`krelS_append`) | `0` | trivial (`P = ⊥`) | done |
| `state`/`transaction` (one-shot) | proven (`krelS_append`) | `1` | Th II.3.8(4) = existing `Prod.Lex.left hk` | one `gradeOf` conjunct from done (inc-6) |
| `CalcReify` multi-shot | relatedness holds | `ω` | Th II.3.9 (no finite δ) | **closed boundary** |

Relatedness is provable for all shot counts (`krelS_append` never mentions a grade); the grade is a
side-computation along that recursion — one-shot keeps it finite, multi-shot forces `ω`.

## References
- Patrick Cousot. *Calculational Design of [In]Correctness Transformational Program Logics by Abstract
  Interpretation.* POPL 2024. — Th II.3.8 (variant under-approximation), Th II.3.9 (incompleteness when finite
  `δ` is forced). (`refs.bib`: `cousot-calculational-incorrectness-logics`.)
- Ivašković, Mycroft, Orchard. *Data-Flow Analyses as Effects and Graded Monads.* FSCD 2020. — §4.3.2 (the
  declined escape hatch). (`refs.bib`: `ivaskovic-fscd20-dataflow-effects-graded-monads`.)
- Source: `Bang/Mult.lean` (`CommSemiring QTT`), `Bang/Syntax.lean` (`q_or_1`), `Bang/Operational.lean`
  (`dispatchOn`), `Bang/Compat.lean` (`krelS_append`, `dispatchOn_append_outer`), `Bang/Core.lean`
  (`Frame.handleF`). Lines drift; cite by name.
