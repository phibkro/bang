# External-consumer options — report for a manager decision

> Fleet-maturity-audit gap (2026-07-22): lang-bang has no use outside its own `examples/`/dogfood
> corpus (36+ diff-tested programs, all internal). Product-direction call — decision needed, not
> made here.

## Option A — in-repo real tool
Rewrite one existing internal script (`tools/*.py`/`*.sh`) as a compiled bang program wired into
`just`/CI, backed by bang's own axiom gate instead of an untested script.
**Cost:** ~1 session, no coordination. **Weakness:** still internal — answers "does bang do real
work," not "does someone else depend on it."

## Option B — cross-repo dependent
Concrete candidate: **pagu-box / agent-orchestration's need for a resource-jailed,
no-ambient-IO computation cartridge.** Bang's fuel-bounded `Source.eval` has no fs/net/ambient-IO
effect ops at all — structurally jailed, not policy-jailed. Wedge: a bounded validation/scoring
rule inside `agent-eval` or `agent-orchestration`'s dispatch path, in bang instead of a hand-rolled
sandboxed script.
**Cost:** medium-high, needs a concrete host task named by that repo's owner first (two-repo
decision, not unilateral). **This is the option that actually closes the audit's gap** — a real
outside dependency.

## Option C — public benchmark
A real-world-shaped program corpus, compiled via the WasmGC backend, run on wasmtime in CI,
published to the existing docs site as continuously re-verified evidence. Reuses existing
site-deploy + wasm-backend infra; executes the strategy already settled in
`docs/notes/copy-kit.md`/`docs/notes/traction-survey.md`.
**Cost:** medium. **Weakness:** grows audience, not a dependent — closes the traction/marketing
gap, not the external-consumer gap.

## Recommendation
A now (cheap, no blocker) → B once a host task is named (the actual audit fix) → C independent,
no ordering dependency. B needs one input from the manager: which host task, in which repo.
