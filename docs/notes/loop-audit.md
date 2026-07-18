<!-- note-status: active -->
# Loop audit — feedback loops by radius

> The cybernetic instrument: every correction loop the project runs, ordered by radius
> (inner = at the desk, outer = the environment), with cycle time and state. Refreshed at
> each **checkpoint (◊)** — `tools/check-loop-audit.sh` fails fitness when ROADMAP.md has
> moved more recently than this file, so the audit cannot silently go stale. The question
> it answers: **which loop is missing or slowest, and is it inside or outside the desk?**
> (Origin: the 2026-07-08 multi-lens project evaluation — SDLC validation gap, VSM S4,
> Meadows L6 all converge on the outer-loop asymmetry this table tracks.)

_Position: the evidence seam is repaired; organic outsider exposure remains the weakest loop but was consciously deferred by the operator while the spreadsheet tracer advances, so no human-validation credit is claimed._

| loop (what corrects what) | cycle time | state |
|---|---|---|
| types / elaborator | seconds | ✔ excellent |
| `lake build` · `#guard` oracles | minutes | ✔ excellent |
| axiom gate (`just axioms`, Audit.lean census) | minutes | ✔ ungameable by design |
| refute-first witnesses (`Bang/Witness/`) | hours | ✔ institutionalized |
| differential fuzz (`Bang/Witness/Fuzz.lean`, #14) | per-build | ✔ 200 seeded samples, handler-fragment-biased, `#guard`-gated |
| commit integrity (pre-commit hook) | per-commit | ✔ REPAIRED 2026-07-10 — the 11-incident worktree-index ghost ROOT-CAUSED (hook leaked `GIT_INDEX_FILE` into lake's git-in-mathlib) and fixed (plan 008 `env -u` sanitization, exercised live) |
| test batteries (`just verify` / `lake test`) | minutes | ✔ 31/31 batteries; resource acceptance/refusals/query/Wasm erasure, concrete Wasm build/engine checks, and explicit host-authority cases run in the standing gate |
| increment gate · banking discipline | days | ✔ caught #44 Stage-2 pre-land |
| doc fitness (`just fitness` generated legs) | days | ✔ caught stale proof-dashboard consumption, abstract/concrete target collapse, and this ROADMAP-coupled loop-audit refresh in the 2026-07-16 wave |
| advisor audit → plan → executor → review (plans/) | days | ✔ 11 plans, 9 landed; exact-head independent review caught residual Route-B overclaims before publication |
| prospective systemic review | per-PATH / checkpoint | ◑ INSTITUTIONALIZED 2026-07-18 — expected-regret dispositions now separate implement-now, option-preserving, triggered deferral, and rejection; first live application scopes the evidence-integrity path |
| **— the desk's edge —** | | |
| CI on main (`.github/workflows/verify.yml`) | per-push | ✔ Verify, Site, and Pages green through the 2026-07-16 remediation wave |
| a user running bang | per-◊ (stranger test) | ◑ OPEN / DEFERRED 2026-07-18 — five earlier internal rounds plus one explicit three-session agentic inspection fed concrete fixes, but still no ORGANIC outside user; spreadsheet work does not satisfy this gate, which must reopen before ◊6/release |
| external review (paper, peers) | — | ◑ ◊6 paper skeletons drafted; no external peer read yet |
| performance measurement | — | ✘ absent (invariant #7 defers it) — first instrument in flight: `lake exe pole` wiring + critical-path report (plan 007) |

## How to refresh (at each ◊)

1. Re-grade each row from evidence (a loop's state is what it *caught* lately, not what it could).
2. Move/add rows if new loops exist (e.g. first outsider issue → the user loop goes ◑).
3. Update the `_Position:` stamp line + commit together with the ROADMAP checkpoint edit.
4. The deliverable is the ONE sentence answer to: which loop is now the weakest, and does the
   next arc feed it? (If three ◊ in a row answer "the same outer loop", that's the escalation.)

**2026-07-18 answer:** the weakest loop is still the organic-outside-user one, outside the desk. The
operator explicitly deferred it and released the spreadsheet sequence; queryable formula facts and the
active recomputation measurement improve the internal product/performance loop but are not evidence that
the outside loop ran. Keep the prepared packet reachable and reopen it before ◊6/release or when an
unfamiliar participant becomes available. Do not describe agentic inspection, query gates, or spreadsheet
journey gates as organic validation.
