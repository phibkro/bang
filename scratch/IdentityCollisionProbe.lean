/-
  scratch/IdentityCollisionProbe.lean — ADR-0054 WC keystone-2c, concretely witnessed.
  ─────────────────────────────────────────────────────────────────────────────────
  THE FINDING (lead-reproduced on merged main, 2026-06-26): under ADR-0054 IDENTITY dispatch, a
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

  THE FIX IS AN OPERATOR DESIGN CALL (do NOT change the identity scheme here). Options on the table:
    - GLOBAL-FRESH identity (a monotone counter, never reused) — kills depth-collision by construction;
    - STRENGTHEN NonEscape (identity uniqueness across dynamic extents, not just resolves-to-something);
    - SURFACE-ENFORCED scoping (the elaborator forbids returning a live-cap thunk past its handler).

  Behavioral facts below are VERIFIED via a COMPILED `#guard` build (Bang-lib temp; the project oracle
  per `lean-eval-reliable-only-compiled` / LWRegress header). `lake env lean` on this scratch file
  reduces them too, but the COMPILED build is the authority.
-/
import Bang.Operational

namespace Bang.IdentityCollisionProbe
open Bang

/-- progB — the RE-HANDLE escape. The `{get}`-thunk captures the inner `state 1` handler's cap
(`vvar 0`), is RETURNED out (inner handler pops), then forced under a FRESH `state 1` handler (N's
`handle` binder shifts the letC-bound thunk to `vvar 1`). Both handlers mint identity 0
(`handlerCount [] = 0`), so the escaped `vcap 0 1` COLLIDES with the fresh handler → resolves (WRONG)
→ `done .vunit`. NOT stuck. -/
def progB : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.handle (.state 1 .vunit) (.force (.vvar 1)))

/-- progB' — the DIRECT-FORCE escape (no re-handler): the escaped thunk is forced at top level, where
there is no same-depth handler to collide with. `splitAtId [] 0 = none` → fail-loud → STUCK. This is the
form that still witnesses the escape (= NonEscapeProbe's `escapeWitness`). -/
def progB' : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))

-- THE COLLISION: the re-handle escape resolves to the wrong handler and RETURNS (unit), not stuck.
#guard (match Source.eval 300 progB  with | .done .vunit => true | _ => false)
-- THE STUCK form: the direct-force escape has no same-depth handler to collide with.
#guard (match Source.eval 300 progB' with | .stuck => true | _ => false)

end Bang.IdentityCollisionProbe
