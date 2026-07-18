<!-- note-status: archival -->
<!-- describes: none -->
# Semantic-packages lifecycle review — selective adoption into bang-lang

> Read-only comparison of `phibkro/semantic-packages@a9914e2` (worktree
> `/tmp/semantic-packages-wave5`, inspected 2026-07-18). This records evidence for a bounded lifecycle
> experiment; it does not make semantic-packages an authority over bang-lang.

## Scope and evidence boundary

The review read the constitution, architecture, core/system/evidence/lifecycle/tracer designs, actor
journeys, ADR 0011, multi-provider runbook, active ExecPlan 0002, representative Wave 4 tests, and git
history. The semantic-packages tree remained unmodified. Its full repository check was not executed
because the request required strict read-only inspection and language/build tools may create caches or
artifacts; conclusions about executable state use committed tests, evidence, history, and explicit plan
status rather than a fresh run.

The history contains 33 commits. It shows real red-first/successor behavior, not merely prose:

- `20610f1` adds loader falsifiers before loader convergence `095dbb4`;
- `f4cc917` freezes campaign controls before implementation;
- `1c7ccf9` records a green-but-rejected checkpoint after independent review found false support and
  attribution/provenance defects;
- `7129dca` freezes successor controls, `90e5996` retains a second rejected checkpoint, and
  `3872b5a` freezes final controls before `986989d` closes the campaign;
- `473a21f` freezes cross-language candidate controls before `e895b86` lands independent Rust and
  TypeScript realizations with bound declaration Evidence.

Wave 5 is a design checkpoint, not yet actor-complete execution. At `a9914e2`, the planned journey-test
tree, `semantic_packages.publication`/`semantic_packages.resolver` modules, and curated product registry
described by ExecPlan 0002 are absent. Its four actor journeys and J1–J5 commands are precise planned
acceptance contracts. We should adopt that framing while retaining the distinction between designed and
demonstrated practice.

## Convergence with bang-lang

Both projects already prefer:

- a thin end-to-end tracer before layer optimization;
- public semantics over representation commitments;
- refute-first probes and negative fixtures;
- evidence scope and explicit exclusions instead of a context-free “verified” badge;
- generated/checked projections over duplicate sources of truth;
- bounded autonomous implementation with protected intent left to the operator; and
- user/agent observations that reopen earlier estimates.

Bang-lang is stronger today in verified-language execution, differential engine routes, generated
documentation gates, and calibrated agentic usability inspection. Semantic-packages is clearer about
actor-terminal acceptance, retained review successors, proportional change profiles, and recursive
multi-provider governance.

## Practices adopted

| practice | adoption in bang-lang | why / boundary |
|---|---|---|
| actor-terminal acceptance | add an actor/public-start/terminal/adverse-route contract to the PATH template | prevents layer-green work from masquerading as product completion |
| one vertical tracer bullet per actor-visible feature | make the smallest public E2E route the feature unit, then thicken it | preserves bang's project-pull discipline and existing tracer history |
| mistake/recovery as first-class E2E evidence | require a negative or recovery observation beside the happy path | aligns compiler diagnostics with real use rather than only successful examples |
| retained failed gates and explicit successors | preserve rejected observations in the PATH; name successors only at consequential boundaries | avoids history rewriting without turning every micro-iteration into DAG ceremony |
| proportional change evidence | distinguish feature, defect, refactor, optimization, and governance minima | keeps rigor while avoiding a 12-profile checklist for routine work |
| recursive process experiments | baseline + hypothesis + canary + safety invariants + independent review + observation + rollback | lets the lifecycle improve itself without weakening or ratifying its own gate |
| model/provider diversity as a probe | independently frame concerns; fuse evidence, never votes or model reputation | diversifies failure modes without inventing an assurance grade |

Executable journey tests, agentic inspections, and organic human testing stay separate evidence types.
Calling all three “E2E user testing” would erase exactly the claim boundary round 6 established.

## Practices adapted or rejected

- Do not import semantic-packages' product-specific six-record identity/Evidence graph into project
  governance; bang's proof/docfacts/query schemas already own their respective evidence boundaries.
- Do not require a 992-line ExecPlan or node-level provenance for every PATH. Promote an explicit node
  only when it releases another owner, changes a shared contract, crosses authority, or preserves a
  consequential failed review.
- Do not add a second generic repository-memory gate: lang-bang's `just fitness` already checks required
  references, generated projections, note status/reachability, PATH reachability, and fact freshness.
  Extend that gate only after a concrete drift escapes it.
- Do not count independent model review as convergence, user validation, or deterministic evidence.
- Do not claim actor-journey execution until a real public journey gate exists and runs.

## Canary, observation, and rollback

`PATH-organic-resource-validation` is the first canary for the expanded template. The next actor-visible
feature—the spreadsheet/reactivity project—is the second. The experiment succeeds if both PATHs can name
one public terminal outcome, one realistic adverse/recovery route, exact evidence, and a reopen trigger;
if a material failed review occurs, its successor remains visible.

After those two PATHs, compare planning overhead, escaped route defects, recovery findings, and handoff
clarity. Keep the actor/evidence fields if they expose otherwise-missed work. Collapse or remove fields
that only duplicate plans or create ceremony without changing a decision. Protected proof, compatibility,
security, and organic-validation gates remain unchanged throughout the experiment.

## Multi-provider observation

An exact read-only Anthropic review was requested through `agent-dispatch` with a bounded disclosure
brief. The first launch was denied by external-data policy before disclosure; after the operator gave
explicit post-warning approval, one retry completed in 20 turns without permission denials or writes.
Structured dispatcher output resolves the primary model as `claude-fable-5`; the auxiliary model usage
also names `claude-haiku-4-5-20251001`. The disclosed scope was only the semantic-packages worktree at
`a9914e2` and the review brief; no lang-bang tree, secrets, environment dump, or network research was
authorized.

The independent result converged on three lived practices: executable repository gates, retained failed
reviews/successor history, and refute-first breaker fixtures. It classified actor-terminal journeys as a
useful but design-only adaptation, because their planned files and commands do not yet exist, and advised
against importing the full 12-class change taxonomy. It challenged ceremony and procedural independence:
four review rounds were needed to accept governance prose, plan-level blocking remains documentary, and
model diversity has not yet shown measured defect-detection lift. Those concerns define this experiment's
observation/rollback bar; the review is advisory and does not ratify the adoption.

Runtime packet: `agent-dispatch --read-only`, high effort, strict read-only PWD
`/tmp/semantic-packages-wave5`; requested/resolved primary `claude-fable-5`; auxiliary
`claude-haiku-4-5-20251001`; no project commands, writes, network research, or permission denials. The
lead independently spot-checked the report's commit sequence and absent Wave-5 implementation paths.
