<!-- note-status: active -->
# Loop audit — feedback loops by radius

> The cybernetic instrument: every correction loop the project runs, ordered by radius
> (inner = at the desk, outer = the environment), with cycle time and state. Refreshed at
> each **checkpoint (◊)** — `tools/check-loop-audit.sh` fails fitness when ROADMAP.md has
> moved more recently than this file, so the audit cannot silently go stale. The question
> it answers: **which loop is missing or slowest, and is it inside or outside the desk?**
> (Origin: the 2026-07-08 multi-lens project evaluation — SDLC validation gap, VSM S4,
> Meadows L6 all converge on the outer-loop asymmetry this table tracks.)

_Position: ◊5.75 closes the last internally reachable pre-◊6 product checkpoint with a real-browser
journey. Organic outsider exposure remains the weakest loop and is still consciously deferred by the
operator; no browser automation, agentic review, or internal differential earns human-validation credit._

| loop (what corrects what) | cycle time | state |
|---|---|---|
| types / elaborator | seconds | ✔ excellent |
| `lake build` · `#guard` oracles | minutes | ✔ excellent |
| axiom gate (`just axioms`, Audit.lean census) | minutes | ✔ ungameable by design |
| refute-first witnesses (`Bang/Witness/`) | hours | ✔ institutionalized |
| differential fuzz (`Bang/Witness/Fuzz.lean`, #14) | per-build | ✔ 200 seeded samples, handler-fragment-biased, `#guard`-gated |
| commit integrity (pre-commit hook) | per-commit | ✔ REPAIRED 2026-07-10 — the 11-incident worktree-index ghost ROOT-CAUSED (hook leaked `GIT_INDEX_FILE` into lake's git-in-mathlib) and fixed (plan 008 `env -u` sanitization, exercised live) |
| test batteries (`just verify` / `lake test`) | minutes | ✔ 34/34 batteries; the new committed-browser-artifact battery adds source/provenance/hash/live-oracle/Node agreement and host-import refusal poles to the standing suite |
| increment gate · banking discipline | days | ✔ caught #44 Stage-2 pre-land |
| doc fitness (`just fitness` generated legs) | days | ✔ caught the new battery's wrong executable boundary and then forced this ◊5.75 refresh after ROADMAP became committed evidence |
| advisor audit → plan → executor → review (plans/) | days | ✔ persistent Fable 5 advisor selected the browser kill shot, audited the completed exact staged boundary, and returned ACCEPT before publication |
| prospective systemic review | per-PATH / checkpoint | ✔ the ◊5.75 PATH separated artifact freshness, browser-compatibility claims, host authority, playground scope, proof scope, and xv6/IO deferral before implementation |
| production-site browser journey | per site build | ✔ `/bang` deployment shape serves 279 modeled routes and runs all five provenance-pinned demos in real Chromium; catches MIME/base-path/static-copy/runtime drift |
| **— the desk's edge —** | | |
| CI on main (`.github/workflows/verify.yml`) | per-push | ✔ Verify, Site, and Pages green through the 2026-07-16 remediation wave |
| a user running bang | per-◊ (stranger test) | ◑ OPEN / DEFERRED 2026-07-19 — five earlier internal rounds plus agentic/systemic inspections and the compiled browser journey fed concrete fixes, but still no ORGANIC outside user; automation does not satisfy this gate, which must reopen before ◊6/release |
| external review (paper, peers) | — | ◑ ◊6 paper skeletons drafted; no external peer read yet |
| performance measurement | — | ✘ absent (invariant #7 defers it); `lake exe pole` reports dependency shape, not timing, and the compiled-demo checkpoint makes no performance claim |

## How to refresh (at each ◊)

1. Re-grade each row from evidence (a loop's state is what it *caught* lately, not what it could).
2. Move/add rows if new loops exist (e.g. first outsider issue → the user loop goes ◑).
3. Update the `_Position:` stamp line + commit together with the ROADMAP checkpoint edit.
4. The deliverable is the ONE sentence answer to: which loop is now the weakest, and does the
   next arc feed it? (If three ◊ in a row answer "the same outer loop", that's the escalation.)

**2026-07-18 answer:** the weakest loop is still the organic-outside-user one, outside the desk. The
operator explicitly deferred it and released the spreadsheet sequence; the capability tracer that its
natural interface exposed improves the internal product/backend-compatibility loop but is not evidence
that the outside loop ran. Keep the prepared packet reachable and reopen it before ◊6/release or when an
unfamiliar participant becomes available. Do not describe agentic inspection, query gates, or spreadsheet
journey gates as organic validation.

**2026-07-19 answer:** the weakest loop is unchanged: organic outside use, outside the desk. The compiled
demo pack materially strengthens the inner product/deployment loop—it caught battery wiring drift and now
runs the public artifact boundary in a real browser—but it does not feed the human loop. This is the
escalation named by the refresh protocol: internal work has reached the final pre-◊6 checkpoint, so no
further internal tracer may be presented as progress on the binding validation constraint. The operator's
deferral remains binding; reopen the prepared outside journey before ◊6/release or when an unfamiliar
participant becomes available.
