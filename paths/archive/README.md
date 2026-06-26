# paths/archive — completed + superseded PATHs

A PATH is a unit of in-flight work between two checkpoints (see `paths/README.md`).
Once its work lands or is superseded, the durable record is the seam test + git
history; the PATH itself becomes litter in the live `paths/` listing. These are
kept (not deleted) because retrospective ADRs and `CONTEXT.md`'s ◊ narrative still
reference them — the reference resolves here rather than dangling into git-only.

Live PATHs stay in `paths/`. Currently the only live umbrella is
`PATH-identity-representation.md` (inc 5–7 remain).

| Archived PATH | Status | Why archived |
|---|---|---|
| `PATH-tracer-bullet.md` | DONE | rung 0 — surface→`Source.eval`→value shipped. |
| `PATH-rung1-state.md` | DONE | rung 1 — State paradigm, axiom-clean. v1 spine. |
| `PATH-rung2-stack.md` | DONE | rung 2 — `Stack Int` + iso-recursive ADTs, tested rung. |
| `PATH-rung3-ledger.md` | DONE | rung 3 — STM-as-handler, `all_or_nothing_abort` verified. |
| `PATH-rung4-reactive.md` | DONE | rung 4 — reactive cell, `cell_reflects_latest` verified. Last v1 MVP rung. |
| `PATH-graded-cbpv-eval.md` | DONE | ◊2 gate met — STD block + `no_accidental_handling` axiom-clean. |
| `PATH-calcvm-port.md` | DONE | ◊3 gate met — K2 matrix collapsed into one calculated machine. |
| `PATH-lr-foundation.md` | DONE | ◊4 gate met — LR foundation (defs + non-▷ spine). |
| `PATH-cap45-finish.md` | SUPERSEDED | ◊4.5 scoped-seam finish; superseded by the typed-static pivot then the identity rework (ADR-0054/0055). |
| `PATH-cap45-rebuild.md` | SUPERSEDED | ◊4.5 answer-typed KrelS rebuild; landed, then superseded by the pivot. |
| `PATH-cap45-resume-composition.md` | SUPERSEDED | ◊4.5 resume-composition; subsumed by the scoped-seam landing + pivot. |
| `PATH-cap5-dispatch.md` | DONE | ◊5 GAP-2 dispatch transfer lemma; `compile_forward_sim` merged to main. |
| `PATH-cap-assignment-spike.md` | DONE (spike) | ADR-0045 cap-assignment de-risk spike; findings fed ADR-0052/0053/0054. |
| `PATH-typed-static-pivot.md` | SUPERSEDED | ADR-0045 pivot build sequence; superseded by the identity rework (ADR-0054/0055). |
| `PATH-typed-lr-reindex.md` | SUPERSEDED | ADR-0053 absolute-caps LR re-index; REVERTED by the identity representation (ADR-0054/0055). The inc-5 work in `PATH-identity-representation.md` is the live successor. |

Recover full history of any PATH: `git log --follow -- paths/archive/PATH-<name>.md`.
