# bang-lang

A small effect-typed language whose **paradigm and runtime are values, not
language features**. The kernel is thunks + effects + STM; everything else
(mutability, IO, async, actors, signals) is ordinary library code over it.

> **AI agents / Claude Code**: read [`CLAUDE.md`](CLAUDE.md) first — invariants,
> glossary, current playhead, what not to do. Then [`CONTEXT.md`](CONTEXT.md)
> and [`ROADMAP.md`](ROADMAP.md). This README is the human-facing intro.

## Architecture

Two-hop verified compilation (ADR-0016):

```
  source  ─►  graded-CBPV semantics  ─Bahr-Hutton calc─►  CalcVM
                                                              │
                                                              └─Benton-Hur LR─►  WasmFX
```

The **graded-CBPV reference** (`Bang/Eval.lean`, `Bang/Spec.lean`) is the
specification. The **CalcVM** is the executable interpreter — canonical
operational meaning, derived by calculation, not designed. The **WasmFX
backend** is the optimized compiler output, proven to preserve contextual
equivalence (CakeML / Benton-Hur model). See `docs/notes/spec-handover.md`
for why this is engineer-ready, not still-in-design.

## Layout

```
Bang/                    Lean library — semantics, calc machines, spec, LR
tools/                   audit.sh (axiom gate) + selfcheck.mjs (Node smoke)
docs/
  decisions/             ADRs (governance) — see docs/decisions/README.md
  spec/                  language design notes
  roadmap/               K-keyframe research roadmap (research-grade)
  notes/                 spec-proof-discipline, spec-handover, calc-playbook
references/              cited papers (organized by topic) + refs.bib
paths/                   per-path working docs (PATH-<slug>.md)
.claude/agents/          domain-specific subagent definitions
CLAUDE.md                read-first orientation for agents
ROADMAP.md               long-term map of checkpoints (◊1 → ◊6)
CONTEXT.md               volatile current position on the map
```

## Quickstart

```bash
nix develop          # dev shell with Lean via elan
just verify          # selfcheck + lake build + tools/audit.sh
```

First `lake` build pulls Mathlib (`lake exe cache get`; network, minutes).

Piecemeal:
```bash
just selfcheck       # zero-dep Node check on the row unifier algorithm
just build           # lake build the Bang library
just audit           # static cheat-grep + lake build clean
lake env lean Bang/Audit.lean   # the real gate — #print axioms
```

## Where things stand

- **K1 unifier** proven (`Bang/EffectRow.lean`)
- **K2 reference `eval`** built (`Bang/Eval.lean`) — to be ported to graded
  CBPV at ◊2
- **K3 calculated machines** (eight) proven (`Bang/Calc*.lean`) — collapsing
  into one graded-CBPV machine at ◊3 (see ADR-0017)
- **Wasmfx spec** in place (`Bang/Spec.lean`, `Bang/Compat.lean`,
  `Bang/Audit.lean`) — theorem statements frozen; proof bodies awaiting Phase A
  + Phase B per `docs/notes/spec-proof-discipline.md`

Current checkpoint: **◊1 (Reconciliation landed)**. Next: **◊2 (Kernel frozen v1)**.

See `CONTEXT.md` for live state, blockers, and active paths.

## Contributing as a builder

1. Read `CLAUDE.md`, `CONTEXT.md`, `ROADMAP.md`, then skim
   `docs/decisions/README.md`.
2. Read the ADR most relevant to what you're touching (ADRs document the
   *why*, not just the *what*).
3. For kernel work: invoke the `kernel-engineer` subagent. For proofs:
   invoke `proof-engineer`. Both are at `.claude/agents/`.
4. When you make a decision a future session could reasonably reverse, write
   an ADR (copy the format of an existing one; tag layer K / C / S).
