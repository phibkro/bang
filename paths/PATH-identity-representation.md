# PATH — implement the identity representation (ADR-0054)

> Replace absolute caps (build-verified UNSOUND, ADR-0053) with capability-passing: the `perform`'s
> handler reference is a generative IDENTITY (a value), dispatched by MATCH. Branch `typed-static-r1`.
> SoT = ADR-0054 + `docs/architecture/core-overview.md`. Design **validated end-to-end** + operator-signed-off.

## Status: design done, validated, signed off — IMPLEMENTATION not yet started

- **De-risked** (scratch, `a9af7bb`): `scratch/IdentityDispatchProbe.lean` (match dispatch fixes the
  witness, migration-invariant) + `scratch/IdentityKernelProbe.lean` (standalone mini-kernel: the
  `migrate vFragile` witness returns 7 under capability-passing + Fork-ii + Fork-a).
- **Forks chosen** (operator): **(ii)** identity = `handlerCount`-at-install (NO Config counter);
  **(a)** dispatch by label/identity MATCH via `splitAt` (keeps the ADR-0043 wrap edge as the existing
  seam; direct-dispatch 5→0 is a follow-on). Frozen `perform`/`handle` statement changes signed off.

## The representation (the design)

```
handle h M      M BINDS a capability var at index 0 (like lam). Installing mints identity n = hcount K,
                pushes handleF n h, substitutes `vcap n` for var 0 in M.
perform c op v  c : Val is the capability (a vvar referencing a handle's binding; vcap n at runtime).
                NO positional cap, NO term-level label — the label/effect comes from c's TYPE.
vcap n : Val    the runtime identity — an ordinary value (NOT a 6th primitive, like vint).
dispatch        perform (vcap n) op v ⇒ splitAt-by-identity n ⇒ the matched handler services op.
```

**Why it closes the LR:** the capability is a VALUE, so substitution carries it UNCHANGED → `closeC_handle*`
becomes a standard binder case (shift the env under the binder, like `lam`), NO special cap-shift → the
ADR-0050 wall dissolves by construction. Escape (capability whose handler is gone) → the EXISTING `LWT`
non-escape gate (`preservation_returnEscape_TODO`).

## AST changes (Core.lean — the foundation; everything ripples from here)

```
ADD     Val.vcap   : Nat → Val
CHANGE  Comp.perform : Val → OpId → Val → Comp        (was: Nat → Label → OpId → Val)
CHANGE  Frame.handleF : Nat → Handler → Frame         (was: Handler → Frame) — carries the runtime identity
KEEP    Comp.handle : Handler → Comp → Comp           (structurally same; now BINDS index 0 in M)
KEEP    Handler.state/throws/transaction (Label …)    (the Label is TYPING-only now; runtime matches identity)
NEW typing: a `Cap ℓ` value type (HasVTy.vcap : the capability's type carries the effect label ℓ)
```

## Increment sequence (each build-gated; green subset = `lake build Bang.Compat`)

> NOTE: an AST change takes the WHOLE green subset RED until Core+Operational+Metatheory+LR+Compat are
> all ported. Expect red-WIP across increments 1–5; the first GREEN checkpoint is the end of increment 5.

1. **Core AST** — the three changes above. (Trivial edit; breaks everything downstream.)
2. **Operational** — `shiftFrom`/`substFrom` (handle now binds → `+1` cutoff; perform carries a Val cap);
   `Source.step` (handle mints `hcount K`, substitutes `vcap`; perform dispatches by identity via
   `splitAt`); `handlerCount`/`splitAt`/`handlesOp` re-keyed to the identity-carrying `handleF`; the
   `LWT`/`LWConfig` author-resolution re-keyed (perform's capability resolves; handle binds). Delete the
   absolute-cap machinery (`absSplit`/`absResolves`/`absResolvesKind` + the orphaned WC helpers left from
   `d1f0916`). Rewrite the `capMigrate1/2` #guards to the new shape + ADD the insert-below-target case.
3. **Syntax (FROZEN typing)** — `HasCTy.perform` (capability-typed) + `handleThrows/State/Transaction`
   (body typed under the bound `Cap ℓ`) + `HasVTy.vcap` + the `Cap` value type. STOP-and-SHOW the exact
   statements landed (operator pre-approved the shape; confirm the text).
4. **Metatheory** — `preservation`/`progress` over the new `perform`/`handle` (handle's binder case; the
   identity-dispatch step). The escape gate (`preservation_returnEscape_TODO`) now also guards the
   capability-escape for the identity rep.
5. **LR + Compat** — `Vrel`/`Crel`/`closeC` over the new AST; `closeC_handle*` re-establish UNSHIFTED (now
   a standard binder case); the `crelK_fund` handler arms close; `splitAt`-keyed dispatch in `krelS_*`.
   **First GREEN checkpoint** = `lake build Bang.Compat` green again, `#print axioms lr_sound` traces
   `sorryAx` only to `hcatch`+`:1801` (the ADR-0043 descents, unchanged by this rep).
6. **CalcVM / Compile** — re-key `evalD`/`compile` (ADR-0052 route-B, now identity-keyed). Whole-tree green.
7. **Surface / NamedCore** — the elaborator emits `handle`-binds-capability + `perform (vvar i)` (the
   author-site assignment, ADR-0053). The `cap`-inference stage (NamedCore candidate ②) is subsumed.

## Risks / watch
- **handleF gaining a field** ripples every `handleF` pattern-match (Operational/Metatheory/LR/CalcVM/
  Compile) — the biggest mechanical surface. Do it with the AST change (inc 1) so the compiler lists every site.
- **The `Cap ℓ` value type** (inc 3): a new `VTy` former, OR encode the capability type as `U (labelEff ℓ) …`
  — decide at inc 3 (affects the frozen `HasVTy.vcap` shape). STOP-and-SHOW.
- **Fork (ii) soundness rides the `LWT` gate** — the identity (= hcount-at-install) is unique only among
  simultaneously-live handlers; a popped-then-reused count is the escape case the gate forbids. Keep the
  gate (`preservation_returnEscape_TODO`) on the critical path.
- The **restructuring** (`core-overview.md §6`) is best folded into this port (the Operational split lands
  naturally as inc 2 re-organises the hub) — but only once green; don't block the port on it.
