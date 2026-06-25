# 0055 — Global-fresh capability identity (reverse Fork-ii's `handlerCount`)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: ADR-0054 fixed the representation (handler reference = a capability VALUE, dispatched by identity match) but left the identity-MINTING scheme open and chose **Fork-ii**: identity = `handlerCount K` at install (depth-from-root, NO Config counter). Build-verified this session that depth-based minting admits a **cross-extent collision**: a capability that escapes its (popped) handler, then is forced under a FRESH handler installed at the SAME depth, resolves to that same-depth impostor instead of being stuck. Witness `progB` (re-handled escape) → `done` reading the wrong handler's state; `progB'` (direct-force escape, no re-handler) → `stuck`. The inc-4 metatheory (`preservation`/`progress`/`type_safety`) remains SOUND — it proves no-stuck, which `progB` (`done`) does not violate — but capability **resolution-transparency** (a cap names ITS handler, not a same-typed impostor) is NOT achieved, and `NonEscape`-as-`FocusResolves` ("the cap resolves to something") is too weak: the collision makes it satisfiable for a genuinely-escaping program. This is the long-flagged **WC keystone-2c**, now concretely witnessed. Fix: mint identity from a **monotonic Config counter** (global-fresh / gensym) — never reused, so no two handlers ever share an identity → an escaped cap resolves to ITS handler or to NOTHING (stuck, fail-loud); collisions become UNREPRESENTABLE and `NonEscape`'s simple form becomes adequate. Reverses Fork-ii's "no Config counter" simplicity bet, which this finding build-refuted.
- **Refines**: 0054
- **Depends-on**: 0054, 0030, 0023
- **See-also**: 0016, 0052

## Status

Accepted (2026-06-26, operator ruling after a build-verified cross-extent identity collision). The
DECISION (global-fresh identity via a Config counter) is recorded; IMPLEMENTATION is pending — the
merged inc-4 kernel (`6cadd6b`) still mints `handlerCount K` (collision-prone) until the rework lands.
The inc-4 metatheory achievement (the STD block axiom-clean over identity dispatch) is to be
**re-established** under global-fresh minting, not discarded — the re-shape is incremental (thread a
counter; add a freshness lemma), not a redesign.

## Context

ADR-0054 chose **Fork-ii** for identity minting — `n = handlerCount K` at `handle`-install — explicitly
to avoid a Config counter ("identity = handlerCount-at-install, NO Config counter"). The PATH flagged the
residual risk: *"the identity is unique only among simultaneously-live handlers; a popped-then-reused
count is the escape case the gate forbids."* The inc-4 de-risk validated `NonEscape := ∀ cfg', StepStar
cfg cfg' → FocusResolves cfg'` (with `FocusResolves` = "a `perform (vcap n ℓ)` focus resolves via
`splitAtId`+`handlesOp`") as sufficient for `progress`/`preservation`/`type_safety`, all axiom-clean.

**The collision (build-verified, reproduced independently on merged main `6cadd6b`):**

```
progB  = letC (handle (state 1 ()) (ret (vthunk (perform (vvar 0) "get" ()))))   -- inner handler: id = handlerCount = 0
              (handle (state 1 ()) (force (vvar 1)))                              -- re-handler:    id = handlerCount = 0 AGAIN
       ⇒ Source.eval = done ()        -- the escaped cap vcap0 COLLIDES with the fresh id-0 handler → reads its state
progB' = letC (handle (state 1 ()) (ret (vthunk (perform (vvar 0) "get" ()))))
              (force (vvar 0))                                                    -- no re-handler
       ⇒ Source.eval = stuck          -- correct: the escaped cap resolves to nothing
```

Evidence: `scratch/IdentityCollisionProbe.lean` (committed). Root cause: `handlerCount K` is a DEPTH;
a `handle` that pops and a later `handle` at the same depth mint the same identity, so an escaped
`vcap n` whose handler is gone can re-resolve to a same-depth impostor of the same kind/label.

**Why this matters even though the inc-4 theorems are sound.** `progB` is well-typed (`HasVTy.vcap`
types any `vcap n ℓ` unconditionally), and its escaped cap RESOLVES (via collision), so `FocusResolves`
holds at every reachable config → `NonEscape ([], progB)` HOLDS → `progB` is admitted as `HasConfig`
and runs to `done`. `type_safety` (no-stuck) is not violated. But the identity representation exists to
guarantee **a capability names its own handler**; the collision breaks that. `NonEscape`-as-`FocusResolves`
is too weak because under depth-based ids, "resolves-to-something" ≠ "resolves-to-the-right-one".

## Decision

Mint capability identity from a **monotonic, never-reused counter carried in the machine state** (the
config), incremented at every `handle`-install. Global freshness makes the bad state unrepresentable:

- No two handler instances ever share an identity (the counter only grows; a pop does not decrement it).
- An escaped capability resolves to ITS handler (if still on the stack) or to NOTHING → `splitAtId = none`
  → **stuck** (fail-loud). The collision is structurally impossible.
- `NonEscape := ∀ cfg', StepStar cfg cfg' → FocusResolves cfg'` becomes **adequate** unchanged:
  resolves-to-something now means resolves-to-the-unique-right-one. A genuinely-escaping program (`progB`)
  correctly FAILS `NonEscape` (its cap resolves to nothing) → excluded from `HasConfig` → the theorems do
  not falsely admit it. `progB` ⇒ stuck (correct, fail-loud).

This is **correctness by construction** (make the collision unrepresentable, not detected), the SOUL root
move. It reverses Fork-ii's "no Config counter" — a simplicity bet this finding build-refuted; the counter
is precisely the structure that buys collision-freedom.

## Consequences

- **`Config` gains a counter** (e.g. `Config := Nat × EvalCtx × Comp`, the `Nat` = next fresh id). The
  re-shape ripples through `Source.step` (handle-arm mints `nextId`, pushes `handleF nextId h`, increments),
  `NonEscape`/`FocusResolves`/`StepStar`, and the metatheory inductions — mostly mechanical counter-threading.
- **One real new proof obligation**: a *freshness* lemma — the minted id is not on the current stack (nor
  reachable in any escaped value). This is what makes `NonEscape` adequate; it replaces the (impossible)
  extent-uniqueness reasoning of the depth scheme.
- **Re-establish the inc-4 STD block** (`preservation`/`progress`/`type_safety`) over the counter-`Config`.
  The merged `handlerCount` proofs (`6cadd6b`) are superseded by this rework (the NEXT unit, with this ADR
  as spec). The structure (identity dispatch, `splitAtId`, the resume re-typing) carries over unchanged;
  only the minting + freshness are new.
- **The initial-config obligation** (well-typed `([],c) → NonEscape ([],c)`, the LR diagonal at inc 5) is
  now provable with teeth: under global-fresh, a well-typed closed program's caps cannot escape-and-collide.

## Alternatives considered (rejected)

- **Strengthen `NonEscape` to track extent-uniqueness, keep `handlerCount`.** Detect the collision via a
  stronger invariant (the cap's id ≡ its handler's live dynamic extent, not just resolves-to-something).
  This is the original "hard WC keystone" — extent-identity is complex to state structurally, the
  foundation stays subtle, and the proof cost is higher than threading a counter. Rejected: detecting a
  hazard a counter makes unrepresentable is the runtime-check-over-structural smell.
- **Accept the kernel gap; enforce non-escape at the surface (Effekt second-class capabilities).** Document
  the limitation; the inc-7 surface elaborator forbids escaping capabilities. Cheapest now, but
  resolution-transparency is NOT kernel-guaranteed — the kernel's central promise would rest on an unbuilt
  surface layer. Rejected: pushes a soundness-of-abstraction property out of the verified core.
