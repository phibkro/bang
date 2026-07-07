---
type: design-question
title: "Graded state handlers: how does `state ℓ s` thread grades?"
description: "how state ℓ s threads grades — the closed focus dissolves the tension (no ω-restriction needed)"
status: decided
area: effects
resolved-by: ["ADR-0025"]
ties: ["Q6", "ADR-0023", "ADR-0025"]
see-also: ["Bang/Core/Soundness.lean", "Bang/Frontend/Surface.lean"]
---
**Resolution**: the CK machine (ADR-0023) keeps the FOCUS CLOSED (substitution-based binding), and
that dissolves the grade tension below — **no `ω`-restriction on the state type `S` is needed**
(rejecting Q12 option 1; the closed focus is Q12 option 2 *subsuming* it). The `state` dispatch RESUMES
(keeps `Kᵢ`, reinstalls a deep `state ℓ s'` frame); `get` returns the stored `s`, `put w` stores `w`.
The stored/threaded state is always a CLOSED value (grade vector `[]`), so duplicating it at `get`
costs zero variable budget for any `S`. Machine + typing (`HasCTy.handleState` / `HasStack.stateF`) +
`progress` are axiom-clean and the state CELL (`put 7; get ⟶ 7`) runs green (`Bang/Frontend/Surface.lean`).
The **preservation** state-resume cases (typing the resumed stack `Kᵢ ++ handleF (state ℓ s') :: Kₒ`)
are marked `RUNG1-OBLIGATION` in `Bang/Core/Soundness.lean` for the proof-engineer. See **ADR-0025**.
Original deliberation preserved below.

**Question (historical)**: the `state` handler's `Source.step` reductions don't thread grades cleanly,
so `state`-handler typing was deferred from ADR-0022's Unit 2 (which does `up` + `throws`).

**Detail**: two grade mismatches in the simplified (Q6) reductions:
- `get`: `handle (state ℓ s)(up ℓ "get" u) ↦ handle (state ℓ s)(ret s)` — the reduct's grade
  is `q • γ_s` (from `ret s`) but the redex's is `q • γ_u` (from `up`'s unit arg `u`).
  Preservation needs `γ_s = γ_u`; only holds if both are `zeros` (closed).
- `put`: `handle (state ℓ _)(up ℓ "put" v) ↦ handle (state ℓ v)(ret unit)` — stores the
  *program* value `v` (typed in the ambient `γ Γ`, NOT closed) as the new handler state, but
  the handler-state typing wants it closed. Open-term preservation breaks.

The root: a stateful handler *threads a resource* (the state) across operations, and QTT grades
track resource usage — the two interact non-trivially. `throws` avoids this (zero-shot, no
threading).

**Options**: (1) require the state type `S` to be unrestricted (grade `ω`, freely
copyable/discardable) so grades don't constrain threading; (2) move to the CK-machine handler
semantics (Q6) where the continuation is captured and the state threads through the frame, not
by substitution; (3) a dedicated graded-state metatheory (literature: graded state / coeffectful
references).

**Blocked on**: Q6 (handler operational semantics) is the likely real fix — graded state wants
the continuation reified, not the substitution shortcut.

**Revisit signal**: `state`-using programs need type safety; or the CK-machine migration (Q6).
