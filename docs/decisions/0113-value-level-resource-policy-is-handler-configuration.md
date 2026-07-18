# 0113 — value-level resource policy is handler configuration

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Keep resource identities as effect-operation values and enforce allowlists in
  runtime-configured handler installers. Rows and `pledge` bound which effects may occur; handlers
  decide which values an admitted operation may act on. Do not add refinements or a kernel policy
  primitive until a consumer exceeds this mechanism.
- **Depends-on**: [0095](0095-stage7-handler-surface.md) (parameter-carrying custom handlers),
  [0111](0111-effect-contracts-static-handler-realizations.md) (contract/realization split),
  [0112](0112-row-attenuation-as-erased-pledge.md) (effect-label ceilings)
- **Date**: 2026-07-18
- **Deciders**: operator + Codex, from the value-level policy consumer in
  `paths/PATH-semantic-contracts.md`
- **Ties**: `examples/policy-host-allowlist/`, `docs/notes/os-inspiration-survey.md`

## Context

ADR-0112 deliberately stopped at effect labels. A pledge can prove that a plugin uses only `Net`,
but both `net.connect(7)` and `net.connect(9)` inhabit that same row. The next path item asked a
real consumer to decide whether Bang now needed refinement types, operation-subset capabilities, or
another runtime primitive to express host/path/quota policy.

The smallest host-allowlist consumer needs none of them. Bang's existing custom handler form can
carry a runtime value through `(Effect init)` and expose it read-only to every clause as `param`.
Installer functions are already first-class and runtime-selectable, so policy configuration can be
chosen dynamically without making handlers kernel values.

## Decision

Use this division of responsibility:

```text
effect row / pledge     which classes of operation may occur
capability identity    which installed handler receives the operation
handler parameter      runtime policy configuration
handler clause         interpretation and value-level admission decision
```

The worked installer is ordinary Bang:

```bang
let install = {fun allowed => fun body =>
  handle (($body)(net)) with (Net allowed) as net {
    connect(host) => if host == param then 1 else 0
  }}
```

The plugin remains typed only against `Cap Net` and `! {Net}`. It neither receives the policy value
nor changes when the allowed host changes. `pledge {Net}` remains useful around the plugin, but it
does not participate in the `host == param` decision.

The operation's result type owns the denial protocol. The minimal consumer uses `0`/`1` so the
admission decisions are observable; a production contract should use an explicit `Result` or a
separate declared failure effect when denial details matter.

## Why this model

1. It follows the project's microkernel rule: dispatch mechanism stays fixed while policy remains
   replaceable userland code.
2. It preserves one stable plugin contract across policy configurations. Moving the allowlist into
   the plugin would make policy non-swappable; moving it into the row would confuse labels with
   predicates over values.
3. Runtime policy selection already composes through ordinary functions. No first-class handler
   value, new surface syntax, or kernel constructor is needed.
4. The handler is the complete mediation point for operations performed through its capability.
   The policy check therefore sits at the point that already interprets each request.

## Consequences

- Bang can demonstrate Deno/OpenBSD-shaped value admission without claiming OS isolation: checked
  plugin code receives a capability, and the installed handler validates each operation argument.
- Policies can change at runtime while plugin source and effect rows remain unchanged.
- Host identifiers in the first consumer are forgeable `Int` values. The capability is still
  required to request `Net`, but this example does not provide nominal host types, filesystem
  canonicalization, unforgeable resource handles, or protection against code outside Bang.
- At this decision's landing point, the handler parameter was read-only and clause bodies were
  ret-shaped. The quota follow-up exposed that constraint and ADR-0114 subsequently added explicit,
  still-ret-shaped parameter updates; effectful denial paths remain outside that envelope.
- Shared effect laws should state contract-wide behavior. A realization-specific allowlist is
  policy configuration, not automatically a law of every `Net` realization.

## Rejected or deferred

- **Refinement/dependent types now** — deferred: the allowlist consumer is already expressible and
  gives no evidence that statically proving a particular host predicate is worth the added type
  system.
- **Put host values in the effect row** — rejected: rows are idempotent sets of labels, not a
  predicate language over operation arguments.
- **A global runtime filter outside the handler** — rejected: it duplicates the complete mediation
  point and creates ordering questions between filtering and interpretation.
- **Parameterized named-handler declarations** — deferred: the first-class installer function
  cleanly supplies runtime configuration around the existing inline parameterized handler.
- **Claim `pledge` is `unveil`** — rejected: `pledge` covers the syscall/effect-class half;
  handler policy covers the resource-value half.

## Confirmation

- `examples/policy-host-allowlist/` runs one unchanged pledged plugin under allow-host-`7` and
  allow-host-`9` configurations. The observations are `10` and `1`, combined into the committed
  oracle value `1001`.
- `tools/check-examples.sh`, the environment-machine differential, module resolver sweep, and JSON
  query/check sweeps discover the example automatically.
- No core, machine, backend, or frontend implementation changes are part of this decision.

## Revisit if

A consumer needs effectful denial/auditing inside a clause, unforgeable resource names, or a static
theorem about which operation values can reach a handler. Stateful quotas and irreversible
revocation now use ADR-0114's explicit update clauses; structured immutable allowlists remain
ordinary configuration.
