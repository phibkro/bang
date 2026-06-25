# Codebase maintenance — lang-bang instance

> The per-repo instance the `/codebase-maintenance` skill loads. Records THIS repo's
> gate, its maintenance objects (object · rung · cadence · debt), the guards already in
> place, and the survey-residue that could still climb. Authored 2026-06-24 from a
> full survey; update when the machinery changes.

This repo's whole stance is **correctness-by-construction** (make the bad state
unrepresentable) + the **derivation ladder** (generate > test > survey). It already sits
high on the ladder — most derived facts are *generated* or *tested*, so the hand-survey is
small. The maintenance instinct here is **keep it that way**: when a new derived fact
appears, climb it; don't let it land on survey.

## The gate

```
nix develop          # ENTER FIRST — bare lake/just/node/python3 are NOT on PATH
just verify          # = selfcheck · build · audit · adr-check   (the 4-leg verify gate)
just fitness         # the no-build fitness bundle (gates EVERY commit via the hook):
                     #   check-primitives (#3/#5) + check-adr-links + arch-check (the V,
                     #   ADR-0048) + check-refs (stale *.md path/link refs)
just axioms          # lake env lean Bang/Audit.lean — #print axioms per headline theorem
just burndown        # sorry/axiom census (the SATD chart)
```

**Read the gate's real result, not its exit code** — three traps live here:
- **Piped exit** (`lake build … | head` returns head's 0). Use the unpiped exit / `$PIPESTATUS[0]` / a store-path check. (Burned 2026-06-21; memory `nix-build-verify-exit-codes`.)
- **The pre-commit hook runs the fast FITNESS bundle on EVERY commit, then `just verify` (the build) for `.lean` commits.** The loogle dep periodically re-clones with local changes, breaking the build leg on an *unrelated* network/tree issue. Escape the BUILD with `BANGLANG_SKIP_VERIFY_REASON="…" git commit` — **fitness still gates** (check-refs/arch-check/adr-links/primitives are not skipped) — BUT then **run the full `nix develop -c lake build` yourself** before trusting green (per-module `lake build Bang.X` can miss cross-module breakage). `git commit --no-verify` is the HARD escape that skips fitness too — avoid it except for genuine emergencies.
- **`adr-check` / `audit` are verify-rung** (read-only, safe at every checkpoint). There is **no mutating apply/deploy step** in this repo — nothing here rebuilds a machine or ships a release, so the whole gate is safe to run.

**Gate the committed content on a clean tree**, never a dirty working tree or an agent's
summary. For a proof claim, the artifact is `#print axioms` on the *committed* sha — a green
build with a hidden `sorryAx` is a false done.

## Maintenance objects — rung · cadence · debt-risk · guard

| Object | Rung | Cadence | Debt if it rots | Guard / how |
|---|---|---|---|---|
| **Axiom set** per headline theorem (⊆ {propext, Classical.choice, Quot.sound}) | TEST | every commit | hidden `sorryAx`, a 4th axiom (trust creep) | `just audit` / `Bang/Audit.lean` #print axioms |
| **Build** (`lake build`) | TEST | every commit | untrue code | `just build` |
| **Differential tests** (`Agree` battery, `#guard`/`#test`/`example` batteries, §7b handler probes, `selfcheck.mjs` third-impl) | TEST | every commit | a stub goes stale / a test that can't fail | the rfl/`#guard` batteries (0-axiom) + `selfcheck` |
| **Kernel invariants #3 & #5** (5 primitives; STM-only-privileged) | TEST (fitness) | every commit (`just fitness`) | a 6th primitive sneaks in (prose invariant violated) | `tools/check-primitives.sh` — prose invariant made STRUCTURAL |
| **Frozen theorem statements** (`Bang/Spec.lean` — the acceptance criteria) | TEST (hook) | every commit | a frozen statement silently weakened/reshaped | pre-commit `STATEMENT_CHANGE_OK="why"` guard (a frozen-stmt diff blocks the commit unless justified) |
| **Secrets** | TEST (hook) | every commit | leaked credential | pre-commit `gitleaks` (skips loudly if it can't run) |
| **ADR decided-ledger** (README index · Q⟺ADR resolution · Status copies) | GENERATE + TEST | per ADR add/supersede/status-change | stale index, Q-status drift, dual-Status drift | `gen-adr-index.py` generates README from frontmatter; `just adr-check` (3-leg) fails CI on drift. ADR-0042. |
| **ADR cross-links** | TEST (fitness) | every commit | broken `[NNNN](file)` refs | `tools/check-adr-links.sh` |
| **Import-direction V** (Frontend→Core←Backend) | TEST (fitness) | every commit | a tier imports across the V (tangle) | `tools/arch-check.sh` (ADR-0048) |
| **Doc cross-references** (path/link refs in `*.md`) | TEST (fitness) | every commit | stale path after a rename/move/delete | `tools/check-refs.py` + `tools/refs-allow.txt` (intentional-historical refs documented once) |
| **Burndown** (sorry/axiom census) | GENERATE | on demand | — (purely derived) | `tools/burndown.sh` |
| **Orientation docs** (`CONTEXT.md`, `ROADMAP.md`) | SURVEY | every checkpoint / wrap | stale status (the classic drift) | hand-survey; update when a ◊ closes. *Climb candidate — see below.* |
| **`CLAUDE.md`** (always-loaded core) | SURVEY | rare (invariant/arch change) | bloat (every token loaded every session) + stale file/recipe refs | hand-survey; keep list-shaped, ~2–4k tokens |
| **PATHs** (`paths/PATH-*.md`) | SURVEY | on work-unit completion | stale PATH describing finished work (litter) | prune/archive on completion. *Climb candidate.* |
| **`OPEN_QUESTIONS.md`** Q-statuses | TEST | per ADR resolving a Q | a resolved Q still reads OPEN (→ re-derivation, as happened with Q19) | `adr-check` cross-ref (ADR `Resolves: Qn` ⟺ Qn non-OPEN) |
| **`references/` + `refs.bib`** | SURVEY | on citation add | mis-cited paper (e.g. the Garby-Hutton-Bahr mislabel) | hand-survey. *Climb candidate.* |
| **Worktrees / branches** (multi-agent isolation) | OP | on agent completion / quiesce | sprawl (dead worktrees + branches) **AND silent discard of a live writer's uncommitted WIP** | teardown-safety RULE below; one-writer-per-tree |
| **git object store** | OP (operator-gated) | when ALL writers quiesce | dangling-object bloat (benign corruption from concurrent-git races) | `git gc`/repack — NEVER while a worktree has a live writer |
| **`archive/`** — REMOVED 2026-06-25 (was the retired K2 matrix) | — | — | a second copy of history (git is the SSoT) | deleted; recover via `git show <sha>:archive/<file>` (ADR-0017 amendment) |

## Technical-debt sources — and how each is prevented (preemptively, by construction)

The debt categories in this repo and the rung that makes each *unrepresentable* rather than *detected*:

```
DEBT SOURCE                         PREVENTED BY (the construction that forbids it)
─────────────────────────────────────────────────────────────────────────────────
proof debt (a sorry)                every sorry is DOCUMENTED + TRACKED (Spec.lean header +
                                    burndown); the axiom gate requires sorryAx to trace ONLY to
                                    those documented sorries. An UNtracked sorry fails the audit.
                                    Model: the append-crux sorry — single, named, gated.
trust debt (an axiom)               #print axioms gate: a 4th axiom beyond trusted-three is a SPEC
                                    CHANGE requiring an ADR (invariant #5-style discipline).
oracle debt (stub / can't-fail test) invariant #1 "proof rides the reference": every exec path is
                                    `exec` itself or differential-tested against it. No oracle-less path.
SSoT debt (two copies of a fact)    generate (the fact's home is the root; everything else derived)
                                    or cross-ref-test. The ADR ledger is the worked example: index +
                                    Q-status + Status are all generated/tested from ADR frontmatter,
                                    so they CANNOT disagree. (Dual-Status drift → adr-check Status leg.)
frozen-statement debt (silent weaken) pre-commit STATEMENT_CHANGE_OK guard — a frozen-stmt diff blocks
                                    the commit unless explicitly justified.
kernel-creep debt (6th primitive)   check-primitives.sh fitness function — invariant #5 made structural.
doc-drift debt (stale prose)        climb to generate/test where possible; the residue (CONTEXT/ROADMAP)
                                    is survey — update at every ◊ close, not "later".
worktree/branch sprawl              one-writer-per-tree (collision unrepresentable) + cleanup on
                                    agent completion. Don't let dead worktrees accumulate.
```

**The preemptive instinct (the operator's question, answered):** debt is prevented *before
creation* by refusing to let a derived fact land on the survey rung when it could be
generated or tested. Concretely, when you add X, ask "what fact does X derive, and which rung
enforces it?" — and climb:
- a new invariant in prose → a fitness function (like `check-primitives.sh`), not a comment.
- a new derived doc/index → generate it + a `--check` in `just verify` (like the ADR ledger).
- a new theorem → its axiom set is auto-audited; a new sorry → document + track it or it fails the gate.
- a new cross-reference between two docs → a cross-ref test (like Q⟺ADR), not "remember to sync".

## Worktree teardown safety (hard-won 2026-06-24 — a force-remove discarded a live writer's WIP)

Worktree cleanup is a **destructive op**, and the multi-agent setup makes "is this worktree done?"
genuinely hard (agents can't be reliably stopped; idle ≠ stopped; stand-down messages are async). The
rule, structural not remembered:

```
1. NEVER blanket `--force` a destructive git op (worktree remove, branch -D, reset --hard, prune,
   gc --prune=now). Default to the NON-forcing form — `git worktree remove` REFUSES on a dirty tree,
   which is the fail-loud guardrail. Force ONE target only after `git status` on THAT worktree confirms
   its dirtiness is expendable.
2. Teardown-safety = working-tree CLEAN (`git status`) + writer CONFIRMED-STOPPED. NOT committed-
   subsumption (`git rev-list ^trunk = 0`) — that answers "are the commits redundant", and says NOTHING
   about uncommitted work or whether a writer is live. Uncommitted WIP is invisible to rev-list.
3. If a worktree has uncommitted changes, STOP — assume a live writer. Removing it silently discards
   their work (this is exactly what happened: `rev-list = 0` looked safe, but ~1hr of uncommitted
   reshape WIP was force-discarded).
```

The friction of a command that *refuses* is the safety feature — don't suppress it. (Cross-project
memory: `parallel-agent-writes-need-worktrees`.)

## Survey-residue that could still climb (the maintenance backlog for the machinery itself)

These three facts are currently hand-surveyed but have a clear test/generate rung available:

1. **Orientation-doc status (CONTEXT/ROADMAP)** → PARTIAL GENERATE. The *proof-state* lines
   (which ◊ is axiom-clean, the sorry count, which sha) are derivable from `Audit.lean` +
   `burndown.sh` + `git`. A generated "status header" would leave only the *narrative* on
   survey. (The 2026-06-24 hand-fix of these is exactly the drift this would prevent.)
2. **PATH lifecycle** → TEST. A check that no `paths/PATH-*.md` references a ◊ that CONTEXT
   marks closed (or: a PATH whose checkpoint is done must be archived) — catches stale PATHs.
3. **Citation integrity** → TEST. A lint that every `\cite`/inline citation resolves to a
   `refs.bib` entry (doctest-style) — catches the mislabel class.

Until they climb, they are the G2 survey shortlist: confirm-or-update them whenever the
proof state or an ADR moves.

## Grades for this repo

- **G0** (per-edit): `just check FILE` — fast single-file Lean error check.
- **G1** (per-commit): the pre-commit hook runs gitleaks + STATEMENT_CHANGE_OK, then the fast **fitness** bundle (no build) on EVERY commit — so check-refs/arch-check gate docs-only and build-skipped commits, not just `.lean` ones; `just verify` (the full build) runs for `.lean` commits unless `BANGLANG_SKIP_VERIFY_REASON`. Tree committed.
- **G2** (feature / checkpoint / wrap): G1 + the survey shortlist above (CONTEXT/ROADMAP/PATHs/refs) + `just fitness`.
- **G3** (release / ◊ close): full sweep + `just axioms` per headline + cold-agent dogfood (a fresh agent reading CLAUDE.md + CONTEXT.md + `git log` orients correctly).

## Anti-triggers

A pure rename, a comment typo, a `docs:` commit with no status/ADR/interface surface → G0/G1,
skip the survey. A proof-only commit that doesn't touch a frozen statement or add a sorry →
the axiom gate is the whole survey. Scale the pass to the change.
