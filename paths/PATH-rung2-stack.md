# PATH · Rung 2 — a verified Stack (the first moat demo)

> The first **user-defined data type with laws** running on the verified kernel. Ladder rung 2
> (PRD §3.1). Status: **READY** (scoped 2026-06-23, not started). **The first concrete demonstration of
> the moat** — "laws between operations" stops being a claim and runs.

## Why this is the pivotal rung

rungs 0–1 proved the kernel *runs* and that a *paradigm* (State) is a library. Rung 2 proves the
**moat**: a user defines a data type (`Stack`), its operations (`push`/`pop`), and the **laws relating
them** (`pop (push x s) = (x, s)`), and the laws are *checked* — on the ADR-0026 ladder (assert +
property-test via `plausible`). This is where "proof by construction" becomes visible.

It is also the **largest** rung so far: it adds the **data layer** (iso-recursive ADTs, ADR-0029) to the
kernel — bigger than rung 1's single handler. Kernel-first, like rung 1, but with more metatheory.

## GOAL (verifiable)

1. A `Stack Int` program runs: `push 1 (push 2 empty)` then `pop` ⟶ `(2, push 1 empty)` (or the chosen
   shape), green via `Source.eval` (`rfl`/`#guard`).
2. The **stack laws property-test green** via `plausible` (the first ADR-0026 *tested*-rung use):
   - `pop (push x s) = some (x, s)`            (push/pop round-trip)
   - `pop empty = none`                         (empty)
   - (optionally) `push x (push y s)` ordering / LIFO.
   When (1)+(2) are green, "a user-defined type with verified-on-the-ladder laws runs" is **true**.

## SCOPE — kernel-first, three layers (monomorphic, ADR-0027)

**K — kernel data layer (ADR-0029, the bulk):**
- `VTy`: `+ sum`, `+ prod`, `+ mu` (iso-recursive; type-level de Bruijn recursion var — **not**
  polymorphism), `+ tvar`.
- `Val`: `+ inl`/`inr` (sum), `+ pair ⟨v,w⟩` (product), `+ fold` (μ).
- `Comp`: `+ case` (sum elim), `+ split` (product elim), `+ unfold` (μ elim). `unfold (fold v) ↦ v`;
  fold/unfold ERASE at runtime.
- Typing (`Bang/Syntax.lean`): `HasVTy`/`HasCTy` cases for the new formers + eliminators (syntactic
  type-matching — the iso payoff).
- Machine (`Bang/Operational.lean`): CK steps for `case`/`split`/`unfold` (push/reduce, like the
  existing letC/app frames).
- Metatheory (`Bang/Metatheory.lean`): extend `preservation`/`progress` with the new cases. Keep axiom
  set ⊆ {propext, Classical.choice, Quot.sound}; **`no_accidental_handling` stays 0-axiom** (◊2 gate).

**L — library/surface (`Bang/Surface.lean`):** define `Stack = μX. 1 + (Int × X)`; `empty = fold (inl
unit)`; `push x s = fold (inr ⟨x, s⟩)`; `pop s = case (unfold s) …`. The surface hides `fold`/`unfold`
in the `push`/`pop`/`empty` forms (a Q20 pseudoinstruction; the user writes `push`/`pop`, not coercions).
Add `#guard`/`rfl` demos running a stack program from source text.

**Q19 — the laws (the moat demo):** state the push/pop laws as **`plausible`** properties (Lean
QuickCheck — ADR-0028's adopt-at-rung-2). Generators: arbitrary `Int`, arbitrary `Stack Int` (bounded
depth). Property-test them green. This is the surface of Q19; a user-facing *law syntax* is a later
refinement (the laws here are stated in Lean directly).

## OUT OF SCOPE

Polymorphism (`Stack a` — monomorphic `Stack Int` only, ADR-0027) · coinductive data (streams →
Div fragment, ADR-0028) · dependent types · a user-facing law-declaration syntax (Q19 surface — laws
stated in Lean for now) · SMT/proof discharge of laws (stay on the `plausible` *tested* rung unless a
law demands the climb) · the WasmFX/CalcVM path.

## DELIVERABLE

- Kernel: iso-recursive ADTs land (ADR-0029); `just verify` green, axiom-clean, `no_accidental_handling`
  0-axiom.
- Library/surface: `Stack` + `push`/`pop`/`empty`; a stack program runs from source (green).
- Laws: push/pop laws **property-test green via `plausible`** — the first moat demo + first ladder
  *tested*-rung use.
- Finding appended here: what the data layer cost (μ metatheory, fold/unfold erasure, the surface
  coercion-hiding), and whether `plausible` integrates cleanly as the tested rung.

## OWNER

**kernel-engineer + proof-engineer** (the K + metatheory layer is the bulk — bigger than rung 1).
The L/Q19 layers are a follow-on (surface + `plausible`). NOT a surface-only issue.

## POINTERS

- **ADR-0029** (iso-recursive ADTs — the decision + why iso) · ADR-0027 (monomorphic; μ ≠ poly) ·
  ADR-0026 (laws on the ladder) · ADR-0028 (adopt `plausible`; inductive=verified, coinductive→Div).
- Q18 (resolved → ADR-0029), Q19 (laws surface — partial: discharge decided, syntax open).
- Kernel: `Bang/Core.lean` (`VTy`/`Val`/`Comp` — extend), `Bang/Operational.lean` (CK machine — add
  case/split/unfold steps), `Bang/Syntax.lean` (typing), `Bang/Metatheory.lean` §E (preservation/
  progress — add cases). Pattern: rungs 0/1 added formers + machine steps + metatheory cases the same way.
- `plausible`: already a `lake` dependency (`lake-manifest.json`); Lean's QuickCheck.
- Surface: `Bang/Surface.lean` — add `Stack`/`push`/`pop`/`empty` + demos.
