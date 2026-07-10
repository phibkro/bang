<!-- note-status: active -->
# Loop audit — feedback loops by radius

> The cybernetic instrument: every correction loop the project runs, ordered by radius
> (inner = at the desk, outer = the environment), with cycle time and state. Refreshed at
> each **checkpoint (◊)** — `tools/check-loop-audit.sh` fails fitness when ROADMAP.md has
> moved more recently than this file, so the audit cannot silently go stale. The question
> it answers: **which loop is missing or slowest, and is it inside or outside the desk?**
> (Origin: the 2026-07-08 multi-lens project evaluation — SDLC validation gap, VSM S4,
> Meadows L6 all converge on the outer-loop asymmetry this table tracks.)

_Position: post-MVP · v0.1.0 RELEASED (env engine default, `bbca771`) · #44 moat ARC COMPLETE end-to-end (Stage 7 surface `handle … with` landed, `1284c8e`, ADR-0095) · next edge operator-sequenced · 2026-07-10._

| loop (what corrects what) | cycle time | state |
|---|---|---|
| types / elaborator | seconds | ✔ excellent |
| `lake build` · `#guard` oracles | minutes | ✔ excellent |
| axiom gate (`just axioms`, Audit.lean census) | minutes | ✔ ungameable by design |
| refute-first witnesses (`Bang/Witness/`) | hours | ✔ institutionalized |
| differential fuzz (`Bang/Witness/Fuzz.lean`, #14) | per-build | ✔ NEW 2026-07-09 — 200 seeded samples, handler-fragment-biased, `#guard`-gated (a counterexample is a red build) |
| increment gate · banking discipline | days | ✔ caught #44 Stage-2 pre-land |
| doc fitness (`just fitness` generated legs) | days | ✔ (+ prose-claim leg 2026-07-08) |
| **— the desk's edge —** | | |
| CI on main (`.github/workflows/verify.yml`) | per-push | ✔ live — 4 green runs incl. `.lean` builds; 3 real catches (gc posture, changelog fixpoint, guard evasion) before its first green |
| a user running bang | per-◊ (stranger test) | ◑ OPEN — LICENSE + install path landed; stranger tests ran twice (round 1 8.5/10 · round 2 7/10, fed the #73–#76 fix wave; see stranger-test-{1,2}.md); still no ORGANIC outside user |
| external review (paper, peers) | — | ◑ OPENED 2026-07-10 — ◊6 paper skeletons drafted (`docs/papers/`, `055f7f7`: calculated-machine + binary-LR, census-checked claims); no external peer read yet |
| performance measurement | — | ✘ absent (invariant #7 defers it; unquantified) |

## How to refresh (at each ◊)

1. Re-grade each row from evidence (a loop's state is what it *caught* lately, not what it could).
2. Move/add rows if new loops exist (e.g. first outsider issue → the user loop goes ◑).
3. Update the `_Position:` stamp line + commit together with the ROADMAP checkpoint edit.
4. The deliverable is the ONE sentence answer to: which loop is now the weakest, and does the
   next arc feed it? (If three ◊ in a row answer "the same outer loop", that's the escalation.)
