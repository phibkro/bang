<!-- note-status: active -->
# Loop audit — feedback loops by radius

> The cybernetic instrument: every correction loop the project runs, ordered by radius
> (inner = at the desk, outer = the environment), with cycle time and state. Refreshed at
> each **checkpoint (◊)** — `tools/check-loop-audit.sh` fails fitness when ROADMAP.md has
> moved more recently than this file, so the audit cannot silently go stale. The question
> it answers: **which loop is missing or slowest, and is it inside or outside the desk?**
> (Origin: the 2026-07-08 multi-lens project evaluation — SDLC validation gap, VSM S4,
> Meadows L6 all converge on the outer-loop asymmetry this table tracks.)

_Position: post-MVP · v0.1.0 RELEASED (env engine default, `bbca771`) · #44 moat ARC COMPLETE · the ROADMAP's emission arc (◊5.25→◊5.5→◊6) + pre-v1 research ladder R1–R6 ADOPTED with the PUBLIC-EARLY policy (every ◊ ships a public v0.x tag; outsider exposure starts during ◊5.5) · 2026-07-10 (second refresh this date)._

| loop (what corrects what) | cycle time | state |
|---|---|---|
| types / elaborator | seconds | ✔ excellent |
| `lake build` · `#guard` oracles | minutes | ✔ excellent |
| axiom gate (`just axioms`, Audit.lean census) | minutes | ✔ ungameable by design |
| refute-first witnesses (`Bang/Witness/`) | hours | ✔ institutionalized |
| differential fuzz (`Bang/Witness/Fuzz.lean`, #14) | per-build | ✔ 200 seeded samples, handler-fragment-biased, `#guard`-gated |
| commit integrity (pre-commit hook) | per-commit | ✔ REPAIRED 2026-07-10 — the 11-incident worktree-index ghost ROOT-CAUSED (hook leaked `GIT_INDEX_FILE` into lake's git-in-mathlib) and fixed (plan 008 `env -u` sanitization, exercised live) |
| test batteries (`just verify` / `lake test`) | ~10 s warm | ✔ 3× faster 2026-07-10 (plan 004 concurrent driver; `test-modules` gate-wired; `lake test` standard entry) |
| increment gate · banking discipline | days | ✔ caught #44 Stage-2 pre-land |
| doc fitness (`just fitness` generated legs) | days | ✔ caught 4 staleness classes at the 2026-07-10 landings |
| advisor audit → plan → executor → review (plans/) | days | ✔ NEW 2026-07-10 — 8 plans, 6 landed; the loop CAUGHT its own defects (exec007 barrel wall, exec005's wrong containment premise, plan-002's refuted corpus-dependency hypothesis) — review-with-STOP-conditions works |
| **— the desk's edge —** | | |
| CI on main (`.github/workflows/verify.yml`) | per-push | ✔ live; green through the 2026-07-10 merge wave |
| a user running bang | per-◊ (stranger test) | ◑ OPEN — three rounds now (8.5 · 7 · 7/10; r3 fed #85–#94); the score PLATEAU at 7 says internal simulation has hit its ceiling — still no ORGANIC outside user |
| external review (paper, peers) | — | ◑ ◊6 paper skeletons drafted; no external peer read yet |
| performance measurement | — | ✘ absent (invariant #7 defers it) — first instrument in flight: `lake exe pole` wiring + critical-path report (plan 007) |

## How to refresh (at each ◊)

1. Re-grade each row from evidence (a loop's state is what it *caught* lately, not what it could).
2. Move/add rows if new loops exist (e.g. first outsider issue → the user loop goes ◑).
3. Update the `_Position:` stamp line + commit together with the ROADMAP checkpoint edit.
4. The deliverable is the ONE sentence answer to: which loop is now the weakest, and does the
   next arc feed it? (If three ◊ in a row answer "the same outer loop", that's the escalation.)

**2026-07-10 answer:** the weakest loop is still the organic-outside-user one — the stranger-test
plateau at 7/10 across two rounds says internal simulation has extracted what it can — and the
adopted arc feeds it DIRECTLY for the first time: the public-early policy makes outsider exposure
a ◊5.5-DURING obligation rather than a ◊6 afterthought. (Second consecutive ◊ naming this loop;
a third triggers the escalation rule above.)
