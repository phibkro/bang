<!-- note-status: active -->
# Loop audit — feedback loops by radius

> The cybernetic instrument: every correction loop the project runs, ordered by radius
> (inner = at the desk, outer = the environment), with cycle time and state. Refreshed at
> each **checkpoint (◊)** — `tools/check-loop-audit.sh` fails fitness when ROADMAP.md has
> moved more recently than this file, so the audit cannot silently go stale. The question
> it answers: **which loop is missing or slowest, and is it inside or outside the desk?**
> (Origin: the 2026-07-08 multi-lens project evaluation — SDLC validation gap, VSM S4,
> Meadows L6 all converge on the outer-loop asymmetry this table tracks.)

_Position: post-MVP · polymorphism arc closed (`cea8ae2`) · edge = #44 banked at Stage 1/2 (ADR-0085) · 2026-07-08._

| loop (what corrects what) | cycle time | state |
|---|---|---|
| types / elaborator | seconds | ✔ excellent |
| `lake build` · `#guard` oracles | minutes | ✔ excellent |
| axiom gate (`just axioms`, Audit.lean census) | minutes | ✔ ungameable by design |
| refute-first witnesses (`Bang/Witness/`) | hours | ✔ institutionalized |
| increment gate · banking discipline | days | ✔ caught #44 Stage-2 pre-land |
| doc fitness (`just fitness` generated legs) | days | ✔ (+ prose-claim leg 2026-07-08) |
| **— the desk's edge —** | | |
| CI on main (`.github/workflows/verify.yml`) | per-push | ◑ NEW 2026-07-08 — first runs unproven |
| a user running bang | — | ✘ absent (no LICENSE, no outsider install path) |
| external review (paper, peers) | — | ✘ absent (◊6 names paper drafts; none started) |
| performance measurement | — | ✘ absent (invariant #7 defers it; unquantified) |

## How to refresh (at each ◊)

1. Re-grade each row from evidence (a loop's state is what it *caught* lately, not what it could).
2. Move/add rows if new loops exist (e.g. first outsider issue → the user loop goes ◑).
3. Update the `_Position:` stamp line + commit together with the ROADMAP checkpoint edit.
4. The deliverable is the ONE sentence answer to: which loop is now the weakest, and does the
   next arc feed it? (If three ◊ in a row answer "the same outer loop", that's the escalation.)
