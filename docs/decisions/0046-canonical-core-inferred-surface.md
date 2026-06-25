# 0046 — The surface architecture: a canonical explicit core + an inference-bridged sugar surface

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: bang has TWO syntaxes for ONE core. The CANONICAL CORE is fully explicit — every label/capability, grade, effect row, and type spelled out — ergonomic to the machine; it is where the semantics and the proofs live, and it is a first-class WRITABLE surface (not a hidden IR). The SUGAR SURFACE (the "language API") omits what can be inferred; ergonomic to humans and agents. A deterministic ELABORATOR bridges them by inference. The surface has no semantics of its own — its meaning IS its elaboration to the core; you verify the small core once, the surface is correct-by-elaboration. The elaborator is tested-not-verified (shell), differential-tested against the core. Load-bearing constraint: inference is a deterministic function or a LOUD ERROR — never a guess — so every surface program elaborates to a UNIQUE core term (no ambiguity). North-star: infer as much as possible.
- **Depends-on**: 0026, 0045, 0016, 0007

## Context

The machine is the spec (the calculated VM, ADR-0016). So the language's semantics are not designed — they FALL OUT of the five primitives + the static/lexical dispatch (ADR-0045). The open question was the SURFACE: how should syntax communicate those semantics?

The answer is a constraint, not a free choice: the surface must be an **honest projection** of the machine. Two failure modes are forbidden — syntax that HIDES a distinction the machine makes (dishonest), and syntax that IMPLIES a distinction the machine doesn't (a lie). "Make the bad state unrepresentable" applies to syntax too: a machine-illegal program should be UNWRITABLE.

The cap-assignment elaborator (ADR-0045, the shell side / `cap-assignment-elaborator.md`) is the first instance: the surface writes `state s in (get)`, the elaborator infers the de-Bruijn capability, and the core carries `perform cap ℓ op v`. Generalising that one move — infer every explicit label from context — is the surface architecture, and the north-star stated by the operator: **infer as much as possible; keep the explicit core writable.**

## Decision

**Two syntaxes for one core, bridged by a deterministic elaborator.**

```
HUMAN/AGENT ──► SUGAR SURFACE ──elaborate (infer)──► CANONICAL CORE ──► machine / proofs
   writes        the "language API"                  explicit everywhere
  (concise)      ergonomic to people + agents        ergonomic to the machine
```

1. **The canonical core is fully explicit AND a first-class writable surface.** Every label/capability, grade, effect row, and type is spelled out. It is the verification + execution target. It is NOT a hidden IR — you can write it directly (the *precision* mode).

2. **The surface omits what the elaborator can infer.** Each inference is a deterministic function from context; the core carries the result:

   | inferred (surface omits) | from | explicit in the core |
   |---|---|---|
   | capabilities / labels | lexical handler scope | `perform cap ℓ op v` (done, ADR-0045) |
   | effect rows | union of what the body performs | `… with {state, throws}` |
   | grades (QTT) | usage count (0/1/ω) | the multiplicity on each binder |
   | types | bidirectional / staged (ADR-0027) | full type annotations |
   | capability passing | which handler is in scope | named-handler arguments |

3. **Semantics are defined ONLY on the core.** The surface has no independent meaning — its meaning IS its elaboration. So the small core is verified once; the surface is correct-*by-elaboration*. This is the **stratification principle** (ADR-0026) projected onto syntax — verified core + tested superset, the elaborator the seam — and the **kernel/shell layering** (`kernel-shell-library.md`): the core is kernel-facing, the sugar is shell.

4. **The discipline (correctness-by-construction for the elaborator):**
   - **deterministic-or-loud-error** — inference is a function, not a search. Genuine ambiguity is REJECTED (a lowering error), never silently disambiguated. (Already enforced: a capability-escape is a lowering error — ADR-0045 Resolution.)
   - **inspectable** — "show me the elaboration" always works; no magic, inference is checkable.
   - **tested-not-verified** — the elaborator is shell, too complex to verify; it is differential-tested against the core oracle (a surface program's behaviour = its elaboration's behaviour). It rides the ADR-0026 *tested* rung.
   - **sugar never enters the core** — invariant #5 (five primitives) for syntax. All expressiveness lives in the elaborator; the core stays minimal + explicit, or the "true shape" stops being true and the verification surface grows.

## Rejected alternatives

- **A single surface (no core/surface split).** Couples sugar directly to the verified semantics — every sugar form enlarges the verification surface, and "infer vs explicit" becomes ad-hoc. Breaks the stratification (the proofs would ride a large, sugar-rich language).
- **A hidden core (an IR, not writable).** The usual elaborator design (Lean/Idris keep the core internal). Rejected for bang specifically: making the explicit core WRITABLE *is* the agent-precision mode — an agent that needs certainty drops to the unambiguous core and checks what its concise code became. That is the "safe to generate into" moat made concrete (PRD).
- **Non-deterministic inference (search / silent defaulting).** Lets ambiguous surface programs elaborate to SOME core term. Reintroduces ambiguity into the *meaning* — exactly what a human or agent cannot safely generate into. Deterministic-or-error is the contract.

## Consequences

- The surface layer is built as an elaborator onto the existing core; it adds no semantics. The verification spine is unchanged (it rides the core).
- **Two modes** for humans + agents: PRECISION (write explicit core, zero inference to get wrong) and CONCISION (write sugar, inspect the elaboration), with a checkable bridge between them.
- The open **grades** question resolves: inferred-by-default, explicit-in-core, surfaced-on-demand.
- **Anchor for every future surface decision:** any sugar must (a) elaborate deterministically to the core, (b) add no core primitive, (c) be inspectable. A sugar that can't is rejected — and this ADR is the reference, so the question isn't re-derived per feature.
