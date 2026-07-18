<!-- note-status: active -->
<!-- describes: none -->
# Prospective systemic review — expected regret before debt hardens

> A judgment gate for doing the right work early without turning every possible future into
> present scope. The governing question is: **how likely is it that not doing this work now will
> become an issue, and how much more expensive will it be after the surrounding system hardens?**

## Why this review exists

Project pull remains the primary scheduling rule: build a feature when a real program demands it.
That rule prevents speculative completeness, but it does not by itself catch work whose value is
mostly preventative—stable identifiers before external tools consume them, a migration seam before
data accumulates, or a security boundary before ambient authority spreads.

The review makes that second judgment explicit. “Do it right the first time” does **not** mean
maximal generality or polish. It means paying now when deferral is likely to create a larger,
less-reversible correction later, and otherwise preserving the cheapest useful door.

## The expected-regret heuristic

For a candidate piece of work, reason about:

```
expected regret of deferral
  ≈ likelihood within a named horizon
    × impact if it occurs
    × later-cost multiplier
    − cost of the smallest sufficient action now
```

This is an ordering aid, not a fake-precision score. Every factor needs evidence:

| factor | evidence to seek |
|---|---|
| likelihood | a named next consumer, repeated workaround, user/agent trace, incident, roadmap dependency, known scaling threshold |
| impact | unsound result, security exposure, data loss, broken automation, migration burden, user dead end, material latency/cost |
| later-cost multiplier | public compatibility, persisted data, identifier fan-out, cross-layer coupling, downstream proofs, installed base |
| cost now | smallest end-to-end slice, including tests, migration, docs, and maintenance—not only code lines |
| reversibility | whether a local future edit suffices or existing users/data/proofs must migrate |

Always name the horizon: **this PATH**, **before the next public release**, **before the next project
consumer**, or a specific ◊ checkpoint. “Someday” is not a likelihood estimate.

## The four dispositions

Every material concern ends in one of four states:

1. **Implement now.** The future pressure is evidenced, impact is meaningful, and later correction
   multiplies. Prefer the smallest end-to-end action that removes the risk.
2. **Preserve the door.** The full mechanism is premature, but a cheap choice now keeps it possible:
   an extensible representation, stable ID, explicit invariant, observation point, compatibility
   field, source location, test seam, or deliberately unclaimed namespace.
3. **Defer with a trigger.** The work is local/reversible or weakly evidenced. Record the observation
   that would reopen it and where that evidence will appear; do not create an ownerless TODO.
4. **Reject.** The concern is not on the intended route, conflicts with an invariant, or has no
   plausible consumer. Record the reason when future contributors are likely to re-propose it.

“Preserve the door” is not permission to add an abstraction layer just in case. It asks for the
**smallest option-preserving action**. Often that is a stable boundary, a refusal, or one sentence
and a trigger—not a framework.

## Lenses

Review the changed seam, not the whole universe, through the lenses that can make later correction
expensive:

| lens | ask |
|---|---|
| correctness and data integrity | Could this silently accept, corrupt, misidentify, or lose meaning? |
| security and authority | Does it widen authority, trust unvalidated input, leak information, or make later attenuation incompatible? |
| user experience and accessibility | Can a newcomer recover? Are errors, codes, locations, names, and examples consistent across routes? |
| reliability and recovery | What happens on partial failure, retry, interruption, or replay? Is failure explicit? |
| performance and scale | Is there a named workload or measured threshold? Would today’s representation force a future rewrite? |
| compatibility and evolution | Are schemas, IDs, syntax, persisted data, or public behavior about to harden? |
| observability and toolability | Can a human or agent determine validity, provenance, evidence grade, and the next action? |
| maintainability and verification | Will one local decision fan out across duplicated logic, generated artifacts, or proof obligations? |

Performance still follows BANG invariant #7: no optimization without a user-facing measurement or a
named representation wall. The performance lens exists to preserve doors and install measurements,
not to speculate about speed.

## Lifecycle triggers

| event | required review |
|---|---|
| a PATH is scoped | run the delta screen; record material dispositions in the PATH before the plan freezes |
| a public schema, stable diagnostic, identifier, syntax, persisted format, or authority boundary changes | full review of compatibility, security, toolability, and migration; an ADR if the choice is architectural |
| a checkpoint or release boundary moves | review the full route, update the product map/current cursor, and re-grade the loop audit |
| user/agent inspection, incident, benchmark, or repeated workaround produces evidence | reopen the affected disposition; evidence outranks the earlier estimate |
| a routine local and reversible edit | answer the delta screen; no review artifact is needed when no material future pressure appears |

The **delta screen** is five questions:

1. What boundary or assumption does this change make harder to reverse?
2. Which named future consumer, adversary, scale, or failure mode will pressure it?
3. What concrete evidence makes that pressure plausible within the named horizon?
4. What becomes more expensive if the work waits?
5. What is the smallest implement-now or option-preserving action?

## Where the result lives

- The current unit’s judgment lives under `## Prospective systemic review` in its `PATH-*.md`.
- A durable architecture choice lives in an ADR; an unresolved choice lives in the question ledger.
- A changed project sequence lives in `docs/roadmap/project-roadmap.md`; the live cursor moves in
  `CONTEXT.md`.
- A checkpoint change also refreshes `ROADMAP.md` and `docs/notes/loop-audit.md` together.
- Findings from a study or incident retain their raw evidence in the study/incident artifact; the
  PATH links rather than copying it.

Use this compact record:

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| … | … | … | implement / preserve / defer / reject | observable event, or “closed” |

## Anti-patterns

- **Possibility masquerading as likelihood.** “We may need it” without a named consumer is not evidence.
- **A numeric score as authority.** The argument and cited evidence matter; arithmetic does not decide.
- **Preserving every door.** Each seam has carrying cost. Preserve only plausible route options.
- **Mechanism before observation.** Add a benchmark, stable diagnostic, trace, or refusal before a
  speculative optimizer or general policy engine.
- **Deferral without a trigger.** A backlog item with no reopening evidence is avoidance, not a decision.
- **Gold-plating the local fix.** High expected regret justifies removing the future trap, not solving
  adjacent hypothetical problems.

## Current example: the resource-contract evidence seam

Round 6 (`stranger-test-6.md`) supplied direct evidence that the newly public contract view can say
top-level `ok:true` for an invalid subject, that realization identities churn when selection changes,
and that B018 loses its stable code on one resolved human route. These are **implement now** because
automation and external users are the next consumers, while compatibility cost is still low.

Full ownership, borrowing, and actor-transfer machinery remain premature. The surfaced local
`0/1/omega` quantity, stable evidence identities, explicit escape refusal, and consumer-gated PATHs
preserve that door until the allocator or actor project supplies a real protocol to type.
