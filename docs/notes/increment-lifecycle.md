# the `incN` lifecycle

> What an **increment** is, how one runs start-to-finish, and how the numbers
> are assigned. The vocabulary (`inc-4`/`inc-5`/`inc-6`) is load-bearing across
> `CONTEXT.md` and `paths/PATH-*.md` but was never defined — this is the
> definition. Companion to `development-lifecycle.md` (the whole-project frame);
> an `inc` is the *unit* that frame's CONSTRUCTION/INTEGRATION phases run on.

## What an `inc` is

```
◊ checkpoint  ── a stable architectural pose (ROADMAP.md ◊1…◊6)
   └─ inc-N    ── ONE proof/work unit advancing toward that pose
        ├─ scoped by a   paths/PATH-*.md   (the gated statement + unit plan)
        ├─ usually on its own  worktree + branch  (incN-slug)
        └─ a sequence of commits at clean seams
```

An `inc` is **NOT** a branch, a commit, or a proof on its own — it is the *unit
of work* between two stable poses, of which those are the artifacts. One `inc`
typically spans several sessions and a handful of commits.

Concretely, the current reshape's increments each got a worktree+branch (one
writer per tree — `parallel-agent-writes-need-worktrees`):

| inc | scope | branch / worktree |
|---|---|---|
| inc-5 | LR / Compat re-index → Model | `inc5-comp-grind`, `inc5-lr-reindex` |
| inc-6 | CalcVM route-B re-derivation | `inc6-u3-bridge` |

A long `inc` decomposes further into **units** (U1, U2, …) inside its PATH —
leaf-first, each a clean seam to commit and resume at (see PATH-inc6 §3).

## Lifecycle of one increment

```
  SCOPED ──► DE-RISKED ──► GROUND ──► DONE ──► MERGED
    │           │            │         │         │
  PATH +     refute-first  multi-    green     to the
  gated      probe: the    session,  seam +    reshape
  statement  statement is  commit    axiom-    trunk
  (frozen)   guilty until  at clean  clean     (then main)
             proven true   seams     gate
```

| stage | what happens | evidence it is real |
|---|---|---|
| **scoped** | write `PATH-*.md`: the frozen statement, unit plan, wall-risk | the PATH exists + names the gated theorem |
| **de-risked** | refute-first — try to break the statement *before* investing; a machine-checked `False` is a first-class deliverable (e.g. ADR-0056 found the inc-5 diagonal FALSE) | a green de-risk probe / a refuted alternative |
| **ground** | turn opaques → defs, discharge sorrys, across sessions; commit at every clean seam (the build arbitrates the def shape — invariant #4) | commits banked at green frontiers |
| **done** | the gated statement closes on a **green seam** with an **axiom-clean** gate | `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` |
| **merged** | the worktree's branch folds into the reshape trunk; the ◊ advances | the branch is in the trunk's history |

**Done = green seam + axiom-clean gate** — never a summary, never a quiet tree.
Gate the *committed* content (`gate-committed-content-not-worktree`), via the
axiom set, never `grep sorry` (`gate-sorries-via-axioms-not-grep`).

## Numbering

Sequential within the **ADR-0045 typed-static reshape** (the trunk is
`typed-static-r1` for docs/design; proof branches fold into it, then to `main`).
Each `inc` re-keys one layer of the stack to the new identity-dispatch AST:

```
inc-4   AST + soundness     metatheory: preservation/progress over the new AST
inc-5   LR / Compat         logical-relation + Compat re-index → Model (the diagonal)
inc-6   CalcVM route-B      re-derive evalD cap-keyed (the Bahr–Hutton calculation)
inc-7   Surface / NamedCore elaborator re-key (the frontend edge)
```

The numbers are a *re-key order*, leaf-toward-apex: the kernel AST (inc-4) must
settle before the LR over it (inc-5), before the calculated VM (inc-6), before
the surface that targets it (inc-7). They are not freely parallel — `Spec`
greens only when inc-5 AND inc-6 both land; `Audit` also needs inc-7.

## Where an `inc` sits among the docs

| element | home |
|---|---|
| the increment's gated statement + unit plan | `paths/PATH-incN-*.md` |
| current increment + what's left | `CONTEXT.md` (the lead ★ section) |
| the checkpoint it advances | `ROADMAP.md` (◊) |
| a decision the increment forced | an ADR in `docs/decisions/` |
| the whole-project phase frame | `docs/notes/development-lifecycle.md` |
