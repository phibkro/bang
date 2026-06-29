/-
  scratch/IdentityCollisionProbe.lean — ADR-0054 WC keystone-2c, concretely witnessed.
  ─────────────────────────────────────────────────────────────────────────────────
  ★ HISTORICAL — the collision below was the bug under `handlerCount` (DEPTH) minting (ADR-0054).
  ADR-0055 (global-fresh identity, merged) FIXES it: the real `Source.step` now mints from a monotone
  Config counter, so a popped depth is never reused → `progB` is now STUCK (fail-loud), not `done`.
  The `#guard`s below are kept as a LIVE REGRESSION on the merged kernel (both escapes → STUCK); the
  ROOT-CAUSE analysis is retained because it motivates the fix. The de-risk of the chosen scheme is
  `scratch/GlobalFreshProbe.lean` (a mirror counter-machine); this file pins the REAL `Source.eval`.

  THE FINDING (lead-reproduced on merged main, 2026-06-26 — under the SUPERSEDED `handlerCount` rep): a
  capability that ESCAPES its handler and is RE-HANDLED resolves to the WRONG handler instead of going
  stuck — a soundness gap in the capability-resolution TRANSPARENCY (abstraction safety), NOT in
  type-safety's no-stuck guarantee.

  ROOT CAUSE: `Source.step`'s `handle` arm mints the capability identity as `n = handlerCount K` — a
  DEPTH-from-root counter. When an inner handler at stack-depth d pops and a FRESH handler is later
  installed at the SAME depth d, the fresh handler re-uses identity d. An escaped cap `vcap d ℓ` (named
  for the popped handler) then COLLIDES with the fresh handler's identity → `splitAtId` resolves it →
  the op runs against the WRONG handler. The old kernel's de-Bruijn cap SHIFT made this same program go
  STUCK; that stuckness was a representation artifact (gone under identity caps), so the regression
  oracle moved with it.

  WHY NonEscape DOESN'T CATCH IT: `NonEscape cfg = ∀ reachable cfg', FocusResolves cfg'`, and
  `FocusResolves` only asserts the cap resolves to SOMETHING (`CapResolves` = `splitAtId` finds a
  handling frame). The collision RESOLVES (to the wrong frame), so `FocusResolves` HOLDS → the escape
  appears to SATISFY NonEscape. "resolves-to-something" ≠ "resolves-to-the-right-one". NonEscape as
  defined is TOO WEAK — it re-admits the ADR-0053 escape bug.

  THE FIX (CHOSEN + MERGED, ADR-0055): GLOBAL-FRESH identity (a monotone Config counter, never reused) —
  kills depth-collision by construction; an escaped cap resolves to ITS handler or to NOTHING (stuck),
  so `NonEscape`-as-`FocusResolves` becomes adequate. The two alternatives considered and rejected:
  STRENGTHEN NonEscape (identity uniqueness across dynamic extents — more invariant to carry than
  global-fresh removes), and SURFACE-ENFORCED scoping (elaborator forbids returning a live-cap thunk —
  pushes the guarantee out of the verified kernel).

  Behavioral facts below are VERIFIED via a COMPILED `#guard` build (Bang-lib temp; the project oracle
  per `lean-eval-reliable-only-compiled` / LWRegress header). `lake env lean` on this scratch file
  reduces them too, but the COMPILED build is the authority.
-/
import Bang.Operational

namespace Bang.IdentityCollisionProbe
open Bang

/-- progB — the RE-HANDLE escape. The `{get}`-thunk captures the inner `state 1` handler's cap
(`vvar 0`), is RETURNED out (inner handler pops), then forced under a FRESH `state 1` handler (N's
`handle` binder shifts the letC-bound thunk to `vvar 1`). Under the OLD `handlerCount` rep both
handlers minted identity 0, so the escaped `vcap 0 1` COLLIDED → `done .vunit` (the bug). Under
ADR-0055 global-fresh the re-handler mints id 1 (counter advanced, never reused), so `vcap 0` matches
NO live frame → STUCK. -/
def progB : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.handle (.state 1 .vunit) (.force (.vvar 1)))

/-- progB' — the DIRECT-FORCE escape (no re-handler): the escaped thunk is forced at top level, where
there is no same-depth handler to collide with. `splitAtId [] 0 = none` → fail-loud → STUCK. This is the
form that still witnesses the escape (= NonEscapeProbe's `escapeWitness`). -/
def progB' : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))

-- POST-FIX REGRESSION (ADR-0055): the re-handle escape is now STUCK (was `done .vunit` under
-- `handlerCount` minting) — global-fresh ids make the cross-extent collision unrepresentable.
#guard (match Source.eval 300 progB  with | .stuck => true | _ => false)
-- THE STUCK form: the direct-force escape has no same-depth handler to collide with (unchanged).
#guard (match Source.eval 300 progB' with | .stuck => true | _ => false)

end Bang.IdentityCollisionProbe
