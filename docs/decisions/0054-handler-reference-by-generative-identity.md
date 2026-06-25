# 0054 — Handler reference by generative IDENTITY (re-base as data), not an integer cap

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Reverse ADR-0053's absolute caps (build-verified UNSOUND: a first-class thunk that locally handles its own effect, forced under an unrelated handler, mis-dispatches its own `perform` to the outer handler — a well-typed, `LWConfig`-valid program evaluating to a wrong-typed value). Root cause is structural: a SINGLE INTEGER cap cannot be both migration-stable and shift-free, and `closeC ≡ Comp.subst` couples them (a substitution-time shift for migration soundness re-shifts `closeC_handle*` = the ADR-0050 LR wall). Fix (deep-research-grounded, Lexa/Effekt/Koka): the `perform`'s handler reference is a generative IDENTITY (a fresh label/capability travelling WITH the thunk), and any handler-crossing re-base is carried as explicit DATA on the value, not proof-internal index arithmetic. Identity-as-value needs NO 6th primitive (a label/capability is an ordinary value; `handler` already primitive) — refining ADR-0044's hesitation. Keep the step-indexed LR (route B, Effekt System Ξ shows lexical capability-passing admits a closeable LR); Leroy forward-simulation (Lexa, no LR) is a recorded alternative. First-class-thunk escape is ruled out by the EXISTING `LWT` non-escape gate (`preservation_returnEscape_TODO`), not by second-class thunks. Representation redesign in SHAPE (Core/Syntax + VM dispatch re-derivation); replaces an unsound kernel, not an upgrade.
- **Supersedes**: 0053
- **Depends-on**: 0044, 0045, 0046, 0050, 0052, 0053, 0016
- **See-also**: 0023, 0024, 0030

## Status
Accepted (2026-06-25, operator ruling after a build-verified soundness counterexample + a fan-out
literature deep-research, 22/25 claims confirmed 3-0 against primary peer-reviewed sources). The
DECISION (representation = generative identity) is recorded; IMPLEMENTATION is pending — the kernel
still carries ADR-0053 absolute caps (unsound) until the redesign lands. The LR-layer achievement
ADR-0053 reported (seam 5→2) is to be **re-established** under the new representation, not discarded.

## Context

ADR-0053 adopted **absolute/level caps** (the `perform` cap counts handlers from the program root) to
dissolve the ADR-0050 de-Bruijn-shift LR wall and land the LR seam 5→2. Its soundness rationale was
*"a cap-carrying thunk cannot escape its handler; migration only pushes handlers ABOVE the target,
never below it."* **That rationale has a hole**, build-verified this session:

- **The counterexample (`scratch/MigrationSoundnessProbe.lean`, `scratch/MigrationTypingProbe.lean`).**
  `migrate vFragile = (λx. handle (throws 2) (force x)) { handle (state 1 7) (perform 0 1 "get" ()) }`.
  A thunk that locally handles its OWN `state`, forced under an unrelated `throws`. Build-verified:
  - `HasCTy [] [] (migrate vFragile) ⊥ (F 1 int)` — **well-typed, axiom-clean** `[propext, Classical.choice, Quot.sound]`
    (`HasCTy.perform` leaves `cap` UNCONSTRAINED, Syntax.lean:163 — typing is cap-irrelevant by design).
  - `LWConfig ([], migrate vFragile)` — **proven** (the live invariant ACCEPTS it).
  - `Source.eval (migrate vFragile) = done(non-int)` — a wrong-TYPED value (the `get` mis-dispatches to
    the `throws`), while `force vFragile` (no migration) = `done 7` and the migration-aware cap-1 variant
    = `done 7`. **type_safety is violated.**
  The missed case: the thunk targets its OWN internal handler (not an ambient one), so forcing it under
  another handler is an **insert-BELOW-the-target** migration. The regression suite (`capMigrate1/2`)
  only tested insert-ABOVE-target, so the build stayed green. ADR-0053's "duty #3 of the multi-duty
  shift" (WC below-insert compensation) was framed as a proof artifact; it is **runtime soundness**.

- **Why no integer cap works, and why the minimal patch is dead.** `closeC` (the LR's environment-
  closing) **IS** `Comp.subst` folded (LR.lean:931; the `closeC_handle*` proofs at Compat.lean:218-252
  consume `substFrom`'s no-shift handle case verbatim). So the cap shift is ONE shared knob:

  ```
                   substFrom shifts on handle?   migration sound?   LR 5→2 closes?
  absolute caps    NO                            ✗ (the bug)        ✓
  restore shift    YES                           ✓                  ✗ (closeC_handle* re-shift = ADR-0050 wall)
  ```

  Migration-soundness and the LR win are the same knob in opposite positions. The "minimal patch"
  (keep dispatch absolute, restore a substitution-time re-base) reintroduces exactly the wall.

## Decision

**The `perform`'s handler reference is a generative IDENTITY, and any handler-crossing re-base is
carried as explicit DATA on the value — not a single integer counted from anywhere.**

- **Identity, not position.** A `handle` mints a fresh generative label/capability; a `perform` targets
  that identity directly. The identity is captured WITH the thunk, so dispatch follows it regardless of
  the forcing context → migration-sound by construction; shadowing = ordinary lexical scoping.
- **Re-base as data (the literature's key refinement).** The handler-crossing adjustment is NOT
  eliminated — it is RELOCATED out of proof-internal index arithmetic into first-class data (Koka's
  `under`/third-evidence-component; Effekt's `lift`; Koka's `open`). The concrete BANG shape: store the
  thunk's defining handler-context as an explicit field, **re-based at CAPTURE, not recomputed at
  force**. This is WHY the LR closes — the shift becomes a term/data transform the relation quantifies
  over, instead of an opaque re-index inside its closing/substitution lemmas.
- **No 6th primitive (invariant #5 preserved).** A generative label / capability is an ordinary value;
  `handler` is already a primitive. Identity-by-value is expressible over `{thunk, force, effect-row,
  handler, STM}`. (Deep-research, 3-0: this refutes ADR-0044's worry that direct dispatch "may be a
  6th-primitive-class change.")
- **Proof route = keep the step-indexed LR (route B).** Effekt's System Ξ shows lexical capability-
  passing admits a CLOSEABLE step-indexed LR (mechanized in Coq) — the opposite of the relative-cap
  shift wall. This **preserves the banked `lr_sound` infrastructure** (the 5→2 is re-established, not
  rebuilt from scratch). Route A (Leroy-style forward simulation, à la Lexa, which has NO step-indexed
  LR so the obstruction never arises) is a recorded alternative — clean-slate, discards `lr_sound`.
- **First-class-thunk escape = the EXISTING `LWT` non-escape gate.** A thunk whose target identity has
  escaped its handler's extent → stuck unless ruled out by typing. We already have the gate: the two-
  context `LWT S R` discipline (a returned value's caps must resolve where it LANDS) — closing
  `preservation_returnEscape_TODO` IS this. We do NOT make thunks second-class (Effekt's 2020 move,
  incompatible with BANG's first-class thunks). Effekt's System C boxing (capture-set types, OOPSLA'22)
  is the recorded post-v1 expressiveness upgrade if escaped capabilities must be re-usable.

## Amendment (2026-06-25, during implementation) — the invariant COLLAPSE

Implementing inc 2/3 surfaced a major simplification (operator-approved). ADR-0045 introduced the separate
`WellCapped`/`LWConfig` structural invariant *because* "typing is cap-irrelevant" — the positional cap was
a bare `Nat`, invisible to typing, so cap-resolution needed its own invariant. **Under identity caps that
premise is false:** the capability is a value `c : Cap ℓ` and `HasCTy.perform` *requires* it, so typing is
now cap-RELEVANT. Resolution becomes a TYPING + lexical-scoping property (a `vvar : Cap ℓ` in scope ⟹ its
binding `handle` lexically encloses the `perform` ⟹ that handler is on the stack when it fires; runtime
`vcap n` names the just-installed `handleF n`).

**Decision: COLLAPSE the well-cappedness invariant into typing.**
```
HasConfig = HasConfigTy ∧ LWConfig (positional resolution + WC keystone + absResolvesKind + shiftCap)
      ↓
HasConfig = HasConfigTy ∧ NonEscape        — NonEscape = capabilities don't outlive their handler
```
The ENTIRE positional well-cappedness machinery dissolves (the WC keystone — the session-long hard piece —
`absResolvesKind`/`CapResolves`/`staticSplit`/`absSplit` and the shift theory are DELETED). The sole
remaining structural obligation is **non-escape**, which IS the existing `preservation_returnEscape_TODO`,
now promoted from one clause to the whole invariant. Mirrors the research (Effekt: capability-passing makes
resolution lexical, not a runtime-searched invariant). The exact `NonEscape` definition is the inc-4
metatheory crux (revealed by what `preservation`/`progress` need; the thunk-escape case is the subtle part,
gated as before). Frozen-statement-safe: `preservation`/`progress`/`type_safety` stay stated over `HasConfig`.

## Confirmation

- Build-gated unsoundness witnesses (this session): `scratch/MigrationSoundnessProbe.lean` (the
  mis-evaluation + `LWConfig` validity), `scratch/MigrationTypingProbe.lean` (`migrate_vFragile_well_typed`,
  axiom-clean), `scratch/archive/WCKeystoneCounterProbe.lean` (the `absSplit` cap-0 mis-resolution under
  below-insert). These pin the ADR-0053 hole so a future "fixed" claim is gated against a run, not prose.
- Implementation fitness (future): a generative-identity `perform` dispatches CORRECTLY on the
  `migrate vFragile` witness; the re-established `closeC_handle*` distribute without a positional shift;
  `#print axioms lr_sound` re-closes to the descent set; `preservation_returnEscape_TODO` discharges via
  the `LWT` gate. The `capMigrate` suite gains an **insert-below-target** case (the gap that hid this).

## Rejected alternatives

- **Absolute / level caps (ADR-0053).** Build-verified UNSOUND (above). Superseded.
- **Relative de-Bruijn caps + handler-crossing shift (ADR-0046/0050).** Migration-sound but the shift
  crosses handler binders and walls the LR (`δ.map shiftCap` mismatch in the 3 handler arms).
- **Minimal patch (absolute dispatch + restore the substitution-time shift).** Structurally dead:
  `closeC ≡ subst`, so shifting `subst` re-shifts `closeC_handle*` = the ADR-0050 wall. The shared knob
  cannot be in two positions at once.
- **Leroy-style forward simulation, no step-indexed LR (Lexa).** Sound + the index-shift obstruction
  never arises — but discards the already-built `lr_sound` (the 5→2). **Recorded as a viable alternative
  route**, not chosen now (keep the LR investment).
- **Second-class capabilities (Effekt 2020).** Makes the bad migration unrepresentable by forbidding
  capabilities from being returned/stored — incompatible with BANG's FIRST-CLASS thunks.
- **System C boxing now (Effekt OOPSLA'22).** Recovers first-class escaped capabilities via capture-set
  types — more machinery than v1 needs; deferred (the `LWT` gate suffices to FORBID escape for v1).

## More information

**Deep-research synthesis** (fan-out web search → 23 sources → 25 claims adversarially verified 3-0;
full report in the session transcript). The convergent finding across four surface forms — generative
labels as lexical capabilities (Lexa), capability-passing typed by an ordered stack shape (Effekt/λCap),
evidence vectors with a data re-base (Koka), protocol reasoning (Hazel) — is: reference by identity,
carry the re-base as data. Primary sources:

- Ma, Ge, Lee, Zhang, **"Lexical Effect Handlers, Directly" (OOPSLA'24)** — generative labels, Leroy
  forward-simulation compiler correctness (no step-indexed LR).
- Brachthäuser, Schuster, Ostermann, **Effekt / "Effects as Capabilities" (POPL'20)** + Schuster et al
  **λCap (ICFP'20)** — capability-passing, `lift`, ordered stack shape; System Ξ closeable LR (ICFP'22);
  **System C boxing (OOPSLA'22)** for first-class blocks.
- Xie, Leijen, **"Generalized Evidence Passing for Effect Handlers" (ICFP'21)** — evidence triple
  `(marker, handler, defining-vector)`; the `under` frame's third component is the re-base-as-data.
- Biernacki, Piróg, Polesiuk, Sieczkowski, **"Handle with Care" (POPL'18)** — step-indexed biorthogonal
  LR; label-select + `lift`-skip (the label+skip-count hybrid our single-int cap collapsed).
- de Vilhena, Pottier, **"A Separation Logic for Effect Handlers" / Hazel (POPL'21)** — protocol (not
  cap) dispatch; unary, single-unnamed-effect (partial data point; the relational/named extension is
  the frontier the compiler-correctness LR needs).

**Open questions carried forward** (deep-research + internal): (1) Does "spine cap vs thunk-internal
cap" map exactly onto Koka's third-evidence-component (defining-context stored on the thunk, re-based at
CAPTURE)? (2) The binary/relational LR for compiling MULTIPLE generative handlers (Hazel is unary; the
2026-POPL "blaze" relational separation logic is the closest closeable-binary-relation candidate).
(3) Does System C boxing port to graded-CBPV if first-class escaped capabilities are later needed?

**Inherited from ADR-0053** (carries forward as input, not reversed): the multi-duty-shift analysis;
that the LR layer (Compat) is independent of the WC/`WellCapped` machinery; that the CalcVM is the
orthogonal deferred route-B (ADR-0052). The keystone-2c (`WCComp.shiftCap_insert`) and the now-dead
`WellCapped` are subsumed — the live path is `LWConfig`/`LWT`, which the identity representation rebuilds.
