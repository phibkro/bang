# BACKLOG — durable open work items

> The in-repo source of truth for **what's open**. Hand-rolled + agent-first: grep by
> `#N`, `type`, or `status`; no external tracker. **Completed items are pruned to git
> history** (the doc-discipline "history lives in git, not docs"); this file holds only
> open/in-flight work.
>
> **SSoT — one home per fact, link don't duplicate:** this file owns *what's open* · the
> agent TaskList is the live *session slice* hydrated from here · `CONTEXT.md` owns *where
> we are now* · `ADRs` own *decisions* · `paths/PATH-*.md` own *in-flight detail* ·
> `ROADMAP.md` owns the *◊ strategic map* · `OPEN_QUESTIONS.md` owns *deferred design
> questions*. An item links those; it does not restate them.
>
> **Conventions:** IDs continue the historical `#N` sequence (next new = **#113**). `type`
> ∈ {proof, cli, test, tooling, infra, surface, docs}. `status` ∈ {in-flight, queued,
> design-first, deferred, blocked, ready}. **No secrets / tokens / PII in this file** (repo
> is private + history email-scrubbed, but keep it leak-safe regardless).

## Open

| # | item | type | status | links / notes |
|---|------|------|--------|---------------|
| 109 | bang runner CLI (`lake exe bang run/eval`) | cli | in-flight | Tier-1 keystone; wraps `Surface.run` (worktree `runner-cli`) |
| 80 | stress-test harness — corpus (A) + Comp generator + differential fuzz (B) | test | in-flight | A on `examples-corpus`; B retires the PropTest non-module exception |
| 110 | bang REPL (interactive eval) | cli | queued | builds on #109 |
| 111 | tree-sitter grammar → syntax highlighting | tooling | queued | `lang-bang-tree-sitter` worktree exists — check its state first |
| 112 | elaborator error-message quality | surface | queued | ADR-0046/0047; touches Surface/NamedCore — gate carefully |
| 98 | fold shell fitness checks → Lean `Bang.Audit.Conformance` meta-check | tooling | ready | the "declarative tooling" fold |
| 72 | `lr_sound` ◊4 reshape seam (CrelK-reshape vs plug-congruence) | proof | design-first | ADR-0058; Q22; clarify v1-scope. NOT a grind |
| 65 | U5b-handler completeness via Route 1 (invert `run_evalD`) | proof | deferred | post-v1; ADR-0058; clears `compile_forward_sim`'s sorryAx |
| 35 | grade the resumption multiplicity (the "ahead of Lexa" extension) | proof | deferred | abort/tail/general static derivation; ADR-0059 |
| 36 | verify post-v1 general-leg cross-step partition (store-preservation) | proof | deferred | ADR-0059 open sub-clause |
| 52 | VM calc spike: is identity-dispatch/gensym forced or introduced? | proof | open-question | OPEN_QUESTIONS Q22; the labelling-vs-closure fork |
| 53 | promote `HasVTy.subst_gen` to `Soundness` (single-source value-subst) | proof | ready | refactor; do at keystone reconciliation |
| 18 | make raw source `vcap` untypeable (drop the `VcapFree` precondition) | proof | ready | soundness hardening; the post-v1 scoped-cap-types move |
| 73 | OPEN_QUESTIONS.md duplicate Q22 numbering (orElse + labelling-vs-closure) | docs | ready | small fix |
| 4 | add behavioral guards to the Audit gate | tooling | ready | re-confirm relevance vs the current gate |

## Hygiene (housekeeping, low-risk, do on a quiet tree)

- Delete the now-redundant branches `consolidate-r104` + `typed-static-r1` (both ⊆ `main`).
- Triage the 4 unpushed spike worktrees: `lang-bang-{compfresh,rename,runplug,shellspike}` — push-or-drop (hold local-only commits).
- `#19` (loogle re-clone hazard) appears resolved by the dependency removal merged to main — verify, then prune.
