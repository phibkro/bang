# PATH-<slug> — <one-line title>

> One path between two checkpoints. Copy this template to start a new path.
> Filename: `PATH-<slug>.md`. Delete or archive when checkpoint reached.

## Seam
- **From checkpoint**: ◊<n> <name>
- **To checkpoint**: ◊<n+1> <name>
- **Contract preserved**: <what must remain true across the path>

## Layer
- [ ] Kernel  [ ] Compiler  [ ] Surface  [ ] Meta (docs/process)

## Actor journey / observable outcome

<!-- For actor-visible work, name the public journey—not an internal layer completion. For proof or
     infrastructure work, name the downstream actor journey this unit releases. -->
- **Actor / need**: <who can accomplish what that they cannot reliably accomplish now?>
- **Public starting point**: <document, command, API, source program, or artifact>
- **Terminal observation**: <the externally observable result that closes the journey>
- **Adverse / recovery route**: <realistic mistake, refusal, interruption, or transfer case>
- **Downstream journey released**: <only for non-actor-visible work; otherwise “this journey”>

## Feeds the constraint
<!-- TOC check (required; check-paths.sh enforces the header). Name the binding
     constraint this path feeds and CITE the artifact that shows it binds (a flagged
     headline, an issue, a gate) — not a restated goal. One or two lines. -->
- **Binding constraint now**: <what limits progress, with citation>
- **How this path feeds it**: <the mechanism>

## Prospective systemic review

<!-- Use docs/notes/prospective-systemic-review.md. Review the changed seam, cite
     evidence, and remove rows that are immaterial. -->

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| <future pressure> | <named horizon + evidence> | <reasoned assessment> | implement / preserve / defer / reject | <observable event, or closed> |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: <current failure, missing capability, or inherited evidence>
- **Smallest tracer bullet**: <the thinnest public end-to-end route that can turn it green>
- **Positive evidence**: <proof/test/trace/artifact and exact expected observation>
- **Negative or recovery evidence**: <counterexample, refusal, mistake-and-recovery, or sensitivity control>
- **Broader convergence gate**: <relevant `just` gate, differential suite, schema replay, or outside observation>
- **Assumptions / exclusions**: <what this evidence does not establish>

## Plan
1. <substep>
2. <substep>
3. <substep>

## Status
- [ ] Started YYYY-MM-DD
- [ ] In flight: <what's currently being worked on>
- [ ] Blockers: <list, with what unblocks each>
- [ ] Completed YYYY-MM-DD
- Retained failed gates / successors: <none yet, or named predecessor observation → successor step>
- Reopen / observe: <post-landing observation, owner, and trigger>

## Owner
- Agent / human: <name or null>

## Notes
<free-form working notes; deletable once path completes>
