# PATH — implement the identity representation (ADR-0054)

> Replace absolute caps (build-verified UNSOUND, ADR-0053) with capability-passing: the `perform`'s
> handler reference is a generative IDENTITY (a value), dispatched by MATCH. Branch `typed-static-r1`.
> SoT = ADR-0054 + `docs/architecture/core-overview.md`. Design **validated end-to-end** + operator-signed-off.

## Status: inc 1–4 DONE + merged AXIOM-CLEAN (`2a7f5c1`, 2026-06-26). ⚠ NEXT UNIT PIVOTED — see banner.

> **★ inc 1 Core · 2 Syntax · 3 Operational · 4 Metatheory — ALL DONE + merged, axiom-clean.** NonEscape
> frozen (Shape B operational closure); the STD block (`preservation`/`progress`/`type_safety`) re-proven
> over identity dispatch, 0 sorries, ⊆ {propext, Classical.choice, Quot.sound}; ~1225 LOC positional
> machinery deleted; `type_safety` unified under `HasConfig` (Option X).
> **⚠ Fork-ii below (identity = `handlerCount`) was build-REFUTED** — depth-based ids admit a CROSS-EXTENT
> COLLISION (an escaped cap re-resolves to a same-depth impostor; `scratch/IdentityCollisionProbe.lean`;
> `NonEscape`-as-`FocusResolves` too weak). The operator chose **global-fresh identity (a monotonic Config
> counter) — `docs/decisions/0055-global-fresh-capability-identity.md` is the NEXT unit's spec** (supersedes
> Fork-ii). Then inc 5 (LR/Compat) · 6 (CalcVM route-B, ADR-0052) · 7 (Surface) remain. The inc-by-inc map
> below is the RECORD of how inc 1–4 landed — read it as history, not as the live plan.

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

## Resume state — inc 3 (Operational) IN PROGRESS

Commits so far: `05f6e45` (inc 1 Core, green) · `e5ef635` (inc 2 Syntax, green) · then Operational WIP.

**Operational port — DONE:** `shiftFrom`/`substFrom` ported (`vcap` case · `perform` shifts/substs its
capability VALUE · `handle` is a BINDER → body at cutoff `+1` with lifted filler, like `lam`). The entire
`shiftCapFrom`/`shiftCap` machinery DELETED (no positional cap to shift under identity caps). 72 → 62 errors.

**Operational port — REMAINING (62 errors, by cluster):**
1. **Substitution proof lemmas** (`substFrom_shiftFrom`, `shiftFrom_substFrom`, `_closed` family): port the
   `perform`/`handle` cases (handle now binds → `+1`); add `vcap` cases. Mechanical.
2. **Dispatch** (`handlesOp`/`staticSplit`/`splitAt`/`dispatchOn` + `handlerCount`): `handleF` now `handleF n h`
   (re-key every pattern). REWRITE dispatch to IDENTITY MATCH (`splitAt` by the capability's `n`, mirror
   `scratch/IdentityKernelProbe.splitAtId`). DELETE `absSplit`/`absResolves`/`absResolvesKind` (absolute-cap
   machinery, gone).
3. **`Source.step`**: handle case mints identity `= handlerCount K`, pushes `handleF n h`, substitutes
   `vcap n ℓ` (ℓ = h's label) for var 0 (`subst0`); perform case dispatches by identity; handleF-return drops `n`.
4. **`LWT`/`LWConfig`**: `perform` author-resolution re-keys to the capability identity; `handle` BINDS (its
   LWT body context extends); `retCtx`/`LWStack`/`handlersOf` over `handleF n h`. `preservation_returnEscape_TODO`
   stays (the escape gate, now also the capability-escape guard).
5. **Orphaned WC helpers** (`hframes`/`CtxKindEq`/`CapResolvesKind.insert`/`handlesOp_shiftCapFrom`/…, left from
   `d1f0916`): DELETE — they reference the now-gone `shiftCapFrom` and are dead.
6. **`capMigrate1/2` #guards**: rewrite to the new `perform`/`handle` shape + ADD the insert-below-target case
   (the witness that broke absolute caps; should now read its own state).

Then inc 4 (Metatheory) → inc 5 (LR/Compat, first green) → inc 6/7.

### inc 3 dispatch layer — PRECISE map (worked out; the delicate core)

DONE additionally: `substFrom_shiftFrom` proof family ported (perform/handle/vcap cases).

The dispatch rewrite, by operation (use `scratch/IdentityKernelProbe` as the blueprint):
- **DELETE (absolute-cap machinery, all dead under identity):** defs `staticSplit` · `CapResolves` ·
  `CapResolvesKind` · `absSplit` · `absResolves` · `absResolvesKind` · `staticDispatch`; AND the dead proof
  block (~L595–616 `staticSplit_*` lemmas, ~L624–713 `CapResolvesKind.*`/`CtxKindEq`/`hframes`/
  `handlesOp_shiftCapFrom` — the WC orphans left from d1f0916). ⚠ INTERLEAVED with LIVE `LWConfig`
  preservation lemmas (~L565–594) — delete per-lemma, do NOT sed a range.
- **ADD:** `splitAtId : EvalCtx → Nat → Option (EvalCtx × Handler × EvalCtx)` (match handleF by identity n,
  mirror IdentityKernelProbe.splitAtId) · `idResolvesKind : EvalCtx → Nat → Label → OpId → Prop` (the
  handleF at id n exists ∧ handlesOp (ℓ,op) — for LWT) · `idDispatch K n op v := (splitAtId K n).bind
  (dispatchOn n op v)`.
- **THREAD IDENTITY through `dispatchOn`:** signature gains `(n : Nat)`; the state/transaction RESUME arms
  reinstall `Frame.handleF n (.state …)` / `.transaction …` (the resumed continuation's performs still
  target n). The legacy label-search `dispatch` (L383) is LR-only → delete from Operational (LR re-keys inc 5).
- **RE-KEY handleF patterns** (`handleF h` → `handleF n h`, n often `_`): `splitAt` · `handlerCount`(+its 3
  simp lemmas) · `handlersOf` · `retCtx` · `LWStack` · `NoWrapMiss`.
- **LWT perform clause:** `absResolvesKind S cap ℓ op` → `idResolvesKind S (the capability's id) ℓ op`; the
  `perform` AST is `perform c op v` with `c = vcap n ℓ` (or a vvar before install — LWT sees post-subst).
  `LWVal`/`LWHandler` gain a `vcap` case (inert, like vunit).
- **Source.step:** handle `(K, handle h M) ↦ (handleF (handlerCount K) h :: K, subst0 (vcap (handlerCount K)
  h.label) M)`; perform `(K, perform (vcap n _) op v) ↦ idDispatch K n op v`; handleF-return drops n.
- **capMigrate1/2 #guards:** rewrite to the new shape + ADD the insert-below-target witness (reads its own state).

### inc 3/4 — the INVARIANT COLLAPSE (operator-approved; ADR-0054 amendment)

Major simplification: under identity caps, resolution is TYPED (`c : Cap ℓ`), so the separate positional
`WellCapped`/`LWConfig` invariant DISSOLVES. `HasConfig = HasConfigTy ∧ NonEscape`.

Revised inc-3 deletions (the collapse drops MORE than before):
- DELETE all positional resolution: `staticSplit`/`CapResolves`/`CapResolvesKind`/`absSplit`/`absResolves`/
  `absResolvesKind`/`staticDispatch` + their proof lemmas + the WC orphans (as before) AND the OLD
  `LWT`/`LWVal`/`LWHandler`/`LWStack`/`LWConfig`/`retCtx` positional machinery.
- ADD identity dispatch (`splitAtId`/`idDispatch`, dispatchOn threads `n` for resume reinstall) + `Source.step`.
- DEFINE `HasConfig := HasConfigTy ∧ NonEscape`. NonEscape = capabilities don't outlive their handler (the
  identity-non-escape; the thunk-escape case is the subtle bit). For inc 3, a first-cut `NonEscape` to compile;
  **inc 4 (Metatheory) pins its exact form** — preservation/progress reveal what's needed (the thunk-escape =
  the old `preservation_returnEscape_TODO`, now the sole structural obligation, gated as before).
- progress's perform case: typing gives `Cap ℓ` + NonEscape gives `handleF n` on-stack → `idDispatch` succeeds.

Net effect on the metatheory: the WC keystone (the session-long hardest piece) + the entire positional
cap-resolution theory are GONE; the only structural invariant left is non-escape.

### inc 3 — dispatch/step rewrite DONE; collapse-deletion remaining

DONE (commit pending): `dispatchOn` threads identity `n` (resume reinstall) · `splitAtId` (identity match)
+ `idDispatch` added · legacy `dispatch` → `idDispatch` · `Source.step` handle mints `n = handlerCount K`
+ substitutes `vcap n h.label`; perform `(.vcap n _)` → `idDispatch K n` · handleF re-keys (splitAt,
handlerCount(+simp), handlersOf, NoWrapMiss, wrapStep, plug) · `staticSplit`/`CapResolves`/`CapResolvesKind`
block DELETED.

REMAINING (the collapse-deletion — interleaved, build-guided per-block):
- DELETE the absolute section (`absSplit`/`absResolves`/`absResolvesKind`/`staticDispatch`, ~L366-428) +
  `CapResolvesKind_handlersOf`/`absResolvesKind_handlersOf` (KEEP `handlersOf`(+`_append`/`handlerCount_*`)).
- DELETE the LWT block (`LWT`/`LWVal`/`LWHandler`/`retCtx`/`LWStack`/`LWConfig`, ~L474-547) + the LWConfig
  preservation lemmas + WC structural/orphan blocks (~L556-716).
- DEFINE `NonEscape : Config → Prop` (first cut, inc-4 refines) + `HasConfig := HasConfigTy ∧ NonEscape`.
- `preservation_returnEscape_TODO` (~L797): re-key to `NonEscape` (the sole obligation now).
- capMigrate1/2 #guards (~L815): rewrite to the capability-passing shape (handle-binds-cap, perform vvar)
  + ADD the insert-below-target witness.

### inc 3 COMPLETE (Operational green, 708 jobs)

Collapse-deletion DONE: absolute section + LWT/LWConfig + WC-orphan proof blocks DELETED;
`HasConfig := HasConfigTy ∧ NonEscape`; `NonEscape := True` (FIRST CUT — inc 4 gives it real content);
`preservation_returnEscape_TODO` re-keyed to `NonEscape` (`trivial` for now); capMigrate guards rewritten
to capability-passing + ADDED `capMigrateInternal` (the ADR-0053 insert-below witness) → #guard reads 7.
`lake build Bang.Operational` green; the three migration #guards pass IN-KERNEL.

★ inc 4 (Metatheory) NEXT: pin `NonEscape`'s real form + re-prove `preservation`/`progress` over the new
AST (handle-binder + identity dispatch). The thunk-escape case is the sole genuine obligation (the old
`returnEscape` content). Then inc 5 (LR/Compat — first whole-LR green) · inc 6/7.

### inc 4 — the fail-loud / kind-check finding (from /simplify altitude review, 90fa70d)

Under identity dispatch the kernel step LOST its op-kind safety net: `splitAtId` matches the capability's
identity `n` ONLY (no `handlesOp` test), and `dispatchOn` then interprets `op` by string. So a capability
that lands on a WRONG-KIND handler (an escaped/ill-typed cap, or — with depth-based ids, Fork ii — a
cross-extent identity COLLISION) is read by `dispatchOn` against the wrong handler and fails **silently-
wrong** rather than stuck: e.g. `op = "get"` on a `.throws` frame hits the throws arm → `some (Kₒ, ret v)`
(a silent ABORT / wrong value), not `none`. The old label search would have SKIPPED the wrong-kind frame.

**This is a real input to pinning `NonEscape`.** Two non-exclusive options for inc 4:
- (a) make `NonEscape` strong enough that a mis-identified/colliding capability can NEVER reach `dispatchOn`
  (i.e. every reachable `vcap n ℓ` names an on-stack `handleF n` whose handler handles `(ℓ, op)`) — then
  progress's perform case closes and the kind-check is genuinely redundant; OR
- (b) restore fail-LOUD at the seam: add an op-kind guard in `dispatchOn`/`idDispatch` (`handlesOp h ℓ op`
  ⟹ else `none`), so a mis-dispatch is STUCK (fail-loud) not wrong-valued. Cheap; behaviour-changing on
  ill-typed inputs only (well-typed programs unaffected — the migration #guards still pass).
Decide as part of the `NonEscape` design (the well-typed witnesses don't exercise this — it's the
ill-typed/escape boundary). Deferred from /simplify (behaviour-changing, not a quality fix).
