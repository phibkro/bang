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
> **Conventions:** IDs continue the historical `#N` sequence (next new = **#117**). `type`
> ∈ {proof, cli, test, tooling, infra, surface, docs}. `status` ∈ {in-flight, queued,
> design-first, deferred, blocked, ready}. **No secrets / tokens / PII in this file** (repo
> is private + history email-scrubbed, but keep it leak-safe regardless).

## Open

| # | item | type | status | links / notes |
|---|------|------|--------|---------------|
| 80 | stress-test harness — Comp generator + differential fuzz (B) | test | ready | **A DONE** (`Bang/Examples.lean`, 16 #guards, on main); B = the generator, retires the PropTest non-module exception |
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
| 4 | add behavioral guards to the Audit gate | tooling | ready | re-confirm relevance vs the current gate |
| 115 | Bang/ dead-code sweep — **DONE: #115a STD chain (148ln) + #115b 8 sim lemmas (153ln), census byte-identical**. REMAINING: private grade/coherence helpers (Soundness/CapCoh/Dispatch), LR/BinaryLR zero-ref lemmas, the vestigial `maxHeartbeats` on `crelK_fund_up` (~100ln, smaller batches) | proof | in-flight | each batch: verify zero-ref → delete → `lake build` + `#print axioms` census-identical. Conflict resolved: the unprimed STD trio WAS dead (build-confirmed) |

## Hygiene (housekeeping, low-risk, do on a quiet tree)

- DONE: pruned 19 merged branches (local+remote, 36→19) + the corruption-ghost worktrees.
- Triage the 17 remaining `--no-merged` branches (old spikes w/ unique commits) + the unpushed spike worktrees `lang-bang-{compfresh,rename,runplug,shellspike}` — push-or-drop (needs a call on whether the experiments are worth keeping).
- `#19` (loogle re-clone hazard) appears resolved by the dependency removal merged to main — verify, then prune.

## /simplify follow-ups (2026-06-29 8-agent pass — minor + discussion)

APPLIED: burndown recursive glob · proof-state `--check` sha short-circuit (gate 2.9s→0.93s) · dead `check-bang-root` recipe (`e337a68`) · **#113 genblock helper** (`69b4062`) · **#114 audit.sh→fitness SSoT + no double-build** (`cbe3abd`). Still open in the table: #115 (Bang/ dead-code), #116 (ADR-0061 dup). The rest:
- **Minor reuse / DRY (build-free, low value):** a shared `tools/` bash lib (set-equality + a `status()` PASS/FAIL helper — 3 output vocabularies today) · one canonical "enumerate Bang/*.lean" helper (5 spellings) · unify the tier→layer source (`gen-import-graph.py` hardcoded `TIER` dict vs `arch-check.sh` path-derived) · two Reference-index tables (CLAUDE.md ↔ ONBOARDING.md) drift-watch · `Bang/Examples.lean`↔`Surface.lean` duplicate `#guard`s — pick one home (Bang/-touching, do with #115).
- **Design-discussion → ADR (do NOT auto-apply):** the STATE/TXN parallel lemma families in `AbstractMachine.lean` (~40 mirror lemmas — `SStore`/`THeap` as one indexed-store abstraction) is the one genuine "should-have-generalized" but it's load-bearing on the ADR-0031 D3/D4 bridges → ADR-scale eval, not cleanup · record the in-repo-tracking + fitness-tooling-direction decisions as ADRs (currently prose-only; #98 would relitigate the latter with no recorded rationale).
- **Trivial Bang/ tidies (with #115):** delete the vestigial `set_option maxHeartbeats 1000000 in` on the `sorry`-bodied `crelK_fund_up` (no-op) · `audit.sh:24-28` disabled axiom-check stub narrated as a comment → delete (the real gate is Audit.lean).
- Verdict: the hand-rolled surface + verified spine are **already high on the derivation ladder** (generate>test deliberately lived); the concentrated debt is *construct duplication* (the generation machinery isn't yet one construct — #113) not altitude drop. Full agent reports were the source.
