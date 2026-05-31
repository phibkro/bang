# bang-lang

A small language whose **paradigm and runtime are values, not language features**. The kernel is thunks + effects + STM; everything else (mutability, IO, async, actors, signals) is ordinary library code. Programs are **descriptions** until forced with `$`; a function's **paradigm** is which effects are in its row; a program's **runtime** is a handler installed at the use site.

> **AI agents / Claude Code: read [`AGENTS.md`](AGENTS.md) first.** It is the read-first orientation file — invariants, glossary, current playhead, what not to do. This README is the human-facing intro.

## What exists vs what's next

This repo is currently a **design corpus + one verified component**, not a working language yet.

- ✅ **Spec** — `docs/spec/` (two design notes: the kernel/effects/runtimes design, and the description/value distinction)
- ✅ **Decisions** — `docs/decisions/` (ADR-0001…0007, each with rationale + rejected alternatives + revisit-if)
- ✅ **Roadmap** — `docs/roadmap/` (keyframes K0→K7; dense `.md` + visual `.html`)
- ✅ **Rep 1 — effect-row oracle** — `effectrow-oracle/` (verified unifier in Lean 4 + Mathlib, F\* alternate, differential harness; the `$`-force/`:`-`=`-reactivity syntax is decided but not yet implemented)
- ⬜ **Rep 2 — definitional interpreter (K2)** — **not built yet.** This is the next thing to make: a fuel-bounded Lean `eval` for the thunk + `$`-force + first-order-effect core, wired into the existing harness as a bigger oracle. See the roadmap and `AGENTS.md` "Current playhead".

## Layout

```
AGENTS.md                 read-first for agents
docs/
  spec/                   what the language is
  roadmap/                where it's going (K0–K7)
  decisions/              why — ADRs (start at README.md)
effectrow-oracle/         rep 1 — verified effect-row unifier + harness
```

## Quickstart (rep 1)

```
cd effectrow-oracle
make selfcheck      # zero-dep algorithm check, Node only — start here
# full pipeline (needs Nix): nix develop ; make check-lean
```

## Start here as a builder

1. Read `AGENTS.md`, then `docs/roadmap/bang-northstar-roadmap.md`, then skim `docs/decisions/`.
2. The next deliverable is **K2** (the definitional interpreter). Do not start by writing a transpiler or a hand-designed VM — see ADR-0004.
3. When you make a reversible decision, write an ADR (copy the format of an existing one).
