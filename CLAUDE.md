# AGENTS.md — read this first

You are a fresh session. **This repo is your only memory.** Anything not written here did not happen. Read this file, then `CONTEXT.md`, then `ROADMAP.md`, before changing anything.

**First time in this repo?** Read `ONBOARDING.md` for setup + a tighter reference index.

## Reference index (progressive disclosure)

This file is the always-loaded core: invariants, glossary, architecture-in-force,
verify-command. Everything else is on-demand — consult the relevant doc when
its trigger arises.

| When you need… | Read |
|---|---|
| **Current session position** (where we are RIGHT NOW) | `CONTEXT.md` |
| **Long-term checkpoint map** (◊1 → ◊6) | `ROADMAP.md` |
| **First-time setup + reference table** | `ONBOARDING.md` |
| **How work flows** (lifecycle + feedback loops + quality gates) | `docs/notes/development-lifecycle.md` |
| **Active in-flight work** | `paths/PATH-*.md` |
| **Architecture in force** | `docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md` |
| **All ADRs** (why-we-chose-X log) | `docs/decisions/README.md` |
| **Deferred design questions** | `docs/notes/OPEN_QUESTIONS.md` |
| **Proof discipline** (PROOF_ORDER, sorry rules, axiom hygiene) | `docs/notes/spec-proof-discipline.md` |
| **Why the wasmfx spec is engineer-ready** | `docs/notes/spec-handover.md` |
| **Lean 4 tactics for this work** | `docs/notes/tactics-survey.md` |
| **K2/K3 calculation proof patterns** (legacy) | `docs/notes/k2-calculation-playbook.md` |
| **K3 historical status** (pre-pivot narrative + composition-mechanism map) | `docs/notes/k3-historical-status.md` |
| **Dev environment** (Nix flake, scripts, gotchas) | `docs/notes/dev-env.md` |
| **Original design thesis** (v0/v1; partially superseded by ADR-0016) | `docs/spec/bang-lang-design.md`, `docs/spec/bang-lang-description-value.md` |
| **K-keyframe research roadmap** (complementary to ROADMAP.md) | `docs/roadmap/bang-northstar-roadmap.md` |
| **References library** (cited papers + refs.bib) | `references/README.md` |
| **Subagent roles** | `.claude/agents/{kernel-engineer,proof-engineer}.md` |
| **Run any task** | `just` (lists recipes); see `justfile` |

## What BANG is

A small language whose **paradigm and runtime are values, not language features**. The kernel is thunks + effects + STM; everything else (mutability, IO, async, actors, signals) is ordinary library code over it. Programs are **descriptions** until forced with `$` (ADR-0007; `!` is actor-send); a function's **paradigm** is which effects are in its row; a program's **runtime** is a handler installed at the use site.

## Architecture in force (third design revision)

Two-hop verified compilation per **ADR-0016**:

```
  source → graded-CBPV semantics → CalcVM (Bahr-Hutton) → WasmFX (Benton-Hur LR)
```

The CalcVM is the executable spec; WasmFX is the verified compiler output.
ADRs 0003 and 0004 were deleted, subsumed by 0016. See `CONTEXT.md` for
where the implementation stands; `docs/notes/k3-historical-status.md` for
what the K3 work taught (preserved as input to the graded-CBPV port at ◊3).

## Invariants — never break these

1. **Proof rides the reference.** Anything that runs is either `exec` itself or differential-tested against it. Never ship an execution path with no oracle behind it.
2. **Effect rows are sets** — idempotent, union = join. Never ordered, never a multiset. (ADR-0001) Post-Q1: `[Lattice Eff] [OrderBot Eff]` (ADR-0018).
3. **STM is the *only* privileged kernel primitive.** Everything else is effect + handler. (design doc; preserved by ADR-0016)
4. **The machine is an *output* of the calculation**, never hand-designed. Calculate, don't verify-after-the-fact. (ADR-0016, formerly ADR-0004)
5. **Kernel stays at five primitives:** thunk · force · effect rows · handlers · STM. Adding a sixth is a spec change requiring an ADR.
6. **No implicit capture; reactivity is the operator, not a keyword.** (ADR-0005, ADR-0006)
7. **Performance is second-class.** Optimize only where it touches the user; a slow correct path beats a fast unverified one.
8. **Effect TS is not the target.** The calculated VM is canonical; the WasmFX backend is the verified compiler target. (ADR-0016, formerly ADR-0004; supersedes ADR-0003)

## Do NOT

- add a kernel primitive · make rows ordered · reintroduce `sig` · add implicit lexical capture
- make Effect TS (or any borrowed runtime) the canonical target
- hand-design the VM, then justify a compiler against it
- optimize speculatively, or add a feature the spec's Non-Features section forbids
- prove most-generality (MGU) for unification — soundness is the contract; MGU goes to the differential test

## Ubiquitous language (glossary)

| term | meaning |
|------|---------|
| **thunk** | a deferred computation; every value is one until forced |
| **force** `$` | evaluate a thunk to WHNF; the only way to observe a value (ADR-0007). bare `name` = description, `$name` = value. `(e)` *groups* without forcing; `$(e)` groups then forces. `!` is **not** force — it's actor-send |
| **`:` / `=`** | `:` introduces a binding (silent); `=` equates (live sync if RHS is a live description, sampled if `$`-forced). reactivity = equality over thunks (ADR-0005) |
| **effect row** | the set of effects a function may perform, carried in its type after `with`. composes by union (join) |
| **handler** | a value implementing an effect's operations; installed with a `with` block; runtimes are handlers |
| **STM / TVar** | the one privileged primitive; transactional memory with journal/retry. TVars usable only inside `atomically` |
| **oracle** | the verified reference an implementation is checked against |
| **calculated VM** | the `(compile, Code, exec)` triple *derived* from `eval` by Bahr–Hutton equational reasoning |
| **checkpoint (◊)** | a stable pose in the project map; see `ROADMAP.md` |
| **PATH** | a unit of in-flight work between two checkpoints; see `paths/` |
| **ADR** | architecture decision record; see `docs/decisions/` |

## Doc discipline

- **History lives in git, not in docs.** When a fact is no longer current
  (e.g., "K3 was in progress until the pivot"), the commit history preserves it.
  Docs describe present state. Past-tense narrative belongs in commit messages
  or `docs/notes/<topic>-historical-*.md` for genuine archival value.
- **Genuine design decisions** that future sessions might reverse → **ADR**
  in `docs/decisions/`. ADRs record the alternative considered AND rejected
  with rationale (not just the chosen path). ADRs are forks-in-the-road,
  not changelogs.
- **Volatile state** (current position, active path, blockers) → `CONTEXT.md`
  or `paths/PATH-*.md`.
- **Always-useful** (invariants, glossary, architecture-in-force) → here
  (CLAUDE.md). Every token in this file is loaded into every session;
  bloat is expensive.
- **On-demand reference** → `docs/notes/*` indexed in the Reference Index above.

## How to verify (the cheapest orientation)

```
nix develop          # ENTER THE DEV SHELL FIRST — bare `lake`/`just`/`node` are NOT on PATH
just verify          # selfcheck (Node) + lake build + tools/audit.sh
# or piecemeal:
just check FILE      # fast single-file Lean error check
just build           # lake exe cache get && lake build  (cold first time: minutes)
just audit           # bash tools/audit.sh
just burndown        # Phase B sorry/axiom counts per module
just axioms          # lake env lean Bang/Audit.lean — #print axioms per theorem
```

First `lake` build pulls Mathlib via `lake exe cache get` (network; minutes).
Green means: lake build clean, axiom set per headline theorem ⊆ {`propext`,
`Classical.choice`, `Quot.sound`}. If you can express a new invariant as a
runnable check, do that instead of writing it in prose — checkable beats described.

## When you make a decision

If you make a choice that a future session could reasonably reverse or relitigate, **write an ADR** in `docs/decisions/` (copy the format of an existing one; `0016` is a good exemplar). Record the *rationale* and the *rejected alternatives*, not just the choice. Anti-drift is mostly anti-reversion, and reversion happens when the "why" is missing.
