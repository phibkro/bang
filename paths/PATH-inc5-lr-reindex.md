# PATH — inc-5: the LR/Compat re-index (ADR-0054/0055 → identity + counter)

> Re-key the step-indexed LR (`Bang/LR.lean` + `Bang/Compat.lean`) to the identity-dispatch + global-fresh
> counter kernel, and close the initial-config NonEscape **diagonal**. First whole-LR green.
> Branch `inc5-lr-reindex`. SoT = ADR-0054/0055 + this PATH. (Supersedes the archived `PATH-typed-lr-reindex`,
> which was the reverted ADR-0053 absolute-caps era.)

## Decisions — ALL build-arbitrated in de-risk (don't relitigate)
- **Diagonal route β** (unary `WellScoped` reachability invariant; `nonEscape_of_fwd_invariant` proven green) —
  NOT the binary-LR α path. The diagonal is a UNARY reachability fact (every reachable `perform` resolves).
- **Machine-shaped KrelS** — observes `(counter, K, c)` with cap-substituted focus + canonical ids (what the
  machine reaches), NOT source-shaped. `krelS_refl` from id-agnostic `HasStack` adapts cleanly.
- **id-renaming invariance** for the `plug`/`run_plug` bridge (over re-base [reopens the ADR-0041 +K.length wall]
  / restrict [bakes normalization]). Primitives `plug_reId` (§2) + `splitAtId_rename` (§3) proven green.
- **`VcapFree c` side-condition** on the diagonal: `HasConfigTy (0,[],c) ⊥ (F q A) ∧ VcapFree c → NonEscape`.
  The bare form is FALSE (a hand-written `vcap 5` literal types but runs stuck); VcapFree is true-by-construction
  (elaborator emits `vvar` not `vcap`, Core:86), discharged by the elaborator at inc-7. (Operator-deferred (b):
  make raw source `vcap` untypeable so the precondition vanishes — task #18, post-(a), likely inc-7.)
- **`closeC_handle*` → lam-shape binder-descent** (the ADR-0054 no-shift win materializes; de-risked in DiagonalProbe).

## State @ `19798fb` (red-WIP by design; LR builds RED, 41 errors)
- De-risk probes (committed): `2282ac2` DiagonalProbe (route β · closeC_handle · VcapFree) · `4005e52`
  PlugMintWall + RenameInvarianceProbe (renaming primitives §2/§3).
- DONE + CLEAN: form-(b) machine-shaped KrelS def core (LR 433–647) + metering-spine re-key (`2ed9078`) ·
  downstream `KrelS_mono`/eff handleF lemmas (`19798fb`). Nice simplification: `dispatchOn` outputs stay the
  2-tuple `EvalCtx × Comp`, so the counter lives only in the nil/CrelK metering configs.
- IN FLIGHT: kernel-engineer `runplug` (worktree `kernel-runplug` @ `4005e52`) proving `run_plug_reshape` +
  the bridge in its `RunPlugReshapeProbe` scratch probe (lands on main when integrated). Contract:
  `Config.run (n + C.length) (0,[],plug C c) = Config.run n (handlerCount C, canonStack C, capSubstInto C c)`
  + renaming-invariance bridging `canonStack C ↔ C`. When it delivers, transcribe `canonStack`/`capSubstInto`/
  `run_plug_reshape` into LR.lean's `run_plug` (~207), discharging the `run_plug`/`converges_plug_iff` sorries.

## Remaining surface (41 errors — the continuation worklist)
1. **Mechanical config-tuple re-keys** (quick): `crelK_ret` (~791), `not_convergesC_le_of_stuck` (782),
   `lr_sound_closed` (1042, the adequacy capstone) — thread `([],c)`/`(K,c)` → 3-tuples (counter = `handlerCount K`
   or `0` for nil).
2. **Positional-cap stuck-half cluster** (~952–1019: `not_converges_up_nil`, `config_stuck_up_splitNone`,
   `not_convergesC_le_up_splitNone`): use old `cap : Nat` + DELETED `absSplit` → NAMED-SORRY them (they reconnect
   via the diagonal's WellScoped/`splitAtId` story, not the core LR — don't re-key the dead `absSplit`).
3. **`crelK_fund` + `krelS_refl` handleF arms** (deepest downstream): re-key to the machine-shaped handleF clause
   (id binder · `n₁=n₂` · `dispatchOn n` · the resume conjunct's new shape). `krelS_refl` supplies `nh=nh'` (rfl,
   self-relation). `crelK_fund` up/perform case is reshape-adjacent → named-sorry until run_plug + diagonal land.

## Finish line
integrate `run_plug` → `lake build Bang.LR` green-with-named-sorries → `Bang.Compat` re-key (incl. the
`closeC_handle` lam-shape rewrite) → **diagonal Phase 3** (`HasConfigTy ∧ VcapFree → NonEscape` via WellScoped
[DiagonalProbe §B] + the run_plug bridge) → ADR cluster (renaming-invariance over re-base/restrict + machine-shaped
KrelS + VcapFree side-condition). Whole-LR-green = builds + the 2 seamed `:1741`/`:1809` (ADR-0043 descents, stay
seamed) + the diagonal CLOSED. Then inc-6 (CalcVM route-B → whole-tree green) · inc-7 (Surface).
