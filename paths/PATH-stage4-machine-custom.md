# PATH-stage4-machine-custom — #44 ADR-0085 Stage 4: derive the machine's `custom` arm, drop both scaffolding premises

> One path, resumable across sessions. The kernel dispatches `Handler.custom` for real
> (`Source.step`, landed `6413281`); the CalcVM (`evalD`/`compile`/`exec`) still bails on custom
> (`evalD custom = none`). This PATH makes the machine catch up — DERIVE the custom arm (invariant #4),
> then DROP the two named-expiry scaffolding premises (`NoCustomFrame`, `CustomFree`). Lane: s4,
> branch `feat-44-stage4`.

## Seam
- **From checkpoint**: ◊4 (the CalcVM bridge, identity-keyed, custom-inert)
- **To checkpoint**: ◊5-adjacent (the machine speaks custom; `compile_forward_sim` unpremised of `CustomFree`)
- **Contract preserved**: the clean set (`run_evalD`, `sim`, `compile_correct`, `evalD_agrees_source`,
  `compile_forward_sim`, `compile_forward_sim_pure`, `source_eval_to_exec`) stays ⊆ trusted-three; the
  built-in arms (state/throws/transaction) stay byte-identical; frozen `Spec.lean` statements change
  ONLY by the pre-authorized premise-DROPS (ADR-0086/0085 named expiries — consumer-safe strengthenings,
  no re-freeze ritual).

## Layer
- [x] Kernel (the `evalD` arm is a kernel-semantics lowering)  [x] Compiler (the machine arm + bridge)

## Feeds the constraint
- **Binding constraint now**: two scaffolding premises gate the spine — `NoCustomFrame K` on
  `run_evalD`/`perform_miss_raises`/`evalD_complete_gen_full` (ADR-0087 rung-2 status, named expiry =
  THIS path) and `CustomFree c` on `compile_forward_sim` + `evalD_complete_gen` (ADR-0086, named expiry
  = THIS path). Both exist ONLY because `evalD custom = none` (`AbstractMachine.lean:282`) inverts the
  completeness direction.
- **How this path feeds it**: deriving the `evalD` custom arm makes those premises droppable — the
  payoff is a machine that dispatches user-defined effects and a spine free of the staging scaffolding.

## The derivation (DONE — probe-verified, banked)
The custom arm is **inline clause-service**, the structural sibling of `evalD`'s `state` arm with USER
clause logic in the resume focus (ADR-0085 D3, as anticipated). Derived against the kernel's `dispatchOn`
custom arm (`Bang/Core/Semantics/Dispatch.lean:177`):

- **`handle (custom ℓ p cls) M`**: mint `id := g`, subst `vcap id ℓ`, PUSH `(id ↦ (p, cls))` on a THIRD
  per-kind store `κ : CStore`, recurse `M'`, POP (`κ'.tail`) on exit; a raise FORWARDS (pop entry).
- **`perform (vcap n ℓ) op v`** (custom op): resolve `(p, cls) := κ.get? n`; `cls.find? op`; INLINE-
  SERVICE — run `evalD … κ (subst p (subst (shift v) clause.2))` against the LIVE store (κ unchanged:
  frame stays live, so nested ops are handled; param READ-ONLY in v1). Resume with the clause's terminal
  value. No frame / no matching clause ⇒ raise to `n`.

`CStore := List (Nat × (Val × List (OpId × Comp)))` — a per-kind store (kind-first idiom), sibling of
`SStore`/`THeap`, justified by the SAME op-disjointness argument (user ops are disjoint from
`{get,put}`/`{newTVar,readTVar,writeTVar}`). The ADR-0085 D3 single-store COLLAPSE is a DEFERRED
census-preserving refactor (same status as the ADR-0085 D5 handler-collapse) — operator ruling
2026-07-09. **The exact edit is banked**: `scratch/stage4-evalD-custom-arm.patch` (`git apply` it).

### Probe witnesses (the de-risk battery — `scratch/CustomArmShadowProbe.lean`, compiled `#guard`, GREEN)
A minimal identity-keyed `evalDc` with the derived arm agrees with the kernel `Source.eval` on:

| witness | value | what it de-risks |
|---|---|---|
| `customResume` | 106 | basic dispatch + one-shot tail resume (the continuation IS reached) |
| `customAbortCoexist` | 42 | zero-shot abort past a live custom frame to a coexisting `throws` |
| `nestedCustom` | 115 | TWO coexisting custom frames, dispatch by IDENTITY (not label) |
| `customForwardsRaise` | 77 | **a custom frame FORWARDS a raise UNRESUMED** — the `NoResume` 5th-conjunct witness (the run_evalD-side risk) |

Either verdict was a deliverable; all four are GREEN. The architecture is not doomed on any probed class.
Kernel-side confirmations for `customResume`/`customAbortCoexist` live in `Bang/Core/Semantics/Eval.lean`
(the Stage-2 `#guard`s); the other two are cross-checked in the probe against `Source.eval`.

## THE COUPLED-UNIT FINDING (verbatim — why this is ONE atomic commit, not a slice)
**The arm-definition and the `NoCustomFrame` drop CANNOT land separately.** In `run_evalD`, the
`handle (.custom ℓ p cls) M` case must recurse into the substituted body `M'` via the term IH `ihT`.
`ihT` demands `NoCustomFrame (Frame.handleF g (custom …) :: K')` — which unfolds to `False`
(`NoCustomFrame`'s custom-handleF arm, `AbstractMachine.lean:3744`). So:
- while `NoCustomFrame` is KEPT as a premise, the custom `handle` case's IH is UNAVAILABLE → making the
  arm real (non-`none`) makes that case UNPROVABLE;
- dropping `NoCustomFrame` is EXACTLY what makes the custom-frame context's IH available.

Therefore (arm-def + `NoCustomFrame` drop + `CustomFree` drop + machine arm) land together. There is no
green intermediate that defines the real arm while keeping the premise.

**Second finding (2026-07-09): the SIGNATURE THREADING is itself atomic across files.** `evalD`'s
result tuple gains a 5th component (`× CStore`), which breaks every consumer that destructures its
output the instant the signature changes — **103 errors in `AbstractMachine.lean` alone** (measured on
the applied edit), all cascading from the tuple arity, plus the cross-file ripple in `Wasm.lean` (134
store mentions) and `U5bComplete.lean` (219). The FIRST green point is only after the ENTIRE
`evalD`-consumer set re-threads. So even the "mechanical threading slice" the lead scoped is NOT
green-incrementable — it is atomic across `sim` + `run_evalD` + their helpers + Wasm + U5b. Budget the
whole unit as one fresh-session atomic commit (ADR-0085's "L / weeks, spine-touching").

## The atomic unit (dependency-ordered; (a) is banked, rest OPEN)
- **(a) `evalD` custom arm + `CStore`** — DONE, banked at `scratch/stage4-evalD-custom-arm.patch`.
  `git apply` it to reinstate. **DONE + LANDED (applied on main, `2167217`)** — no longer needs apply.
- **(b) `Corr` machinery** — DONE (`15555c0`+`d748fe6`). Machine-side: `customUpdate` (HStack analog of
  `stateUpdate`/`txnUpdate`) + the `exec` OP custom-dispatch arm (`2167217`). Bridge: `hsCustom`/
  `hsCustoms`/`CCorr`/`updateCustoms` + `get?_hsCustoms`/`CCorr.get?`/`customUpdate_service` +
  `CCorr_install`/`CCorr_install_noncustom`/`CCorr_pop_custom`/`CCorr_pop_noncustom` +
  `hsCustoms_stateUpdate_put`/`hsCustoms_txnUpdate`/`hsCustoms_netEffect`. All compile.
- **(c) `sim` — FULLY DONE** (`313ecc7`): the entire two-part simulation (term + raised) κ-threaded and
  proven, incl. ALL novel custom cases: perform-service (inline clause ↔ `customUpdate`), perform-raise
  (no-frame/clause-miss via `customUpdate_none_of_*`), **custom clause-body-RAISES** (a custom clause that
  itself performs a raise, via `ihR` on the clause body), custom handle install/pop, custom handle
  raise-FORWARD. The op-priority resolution (A) is LANDED (`isBuiltinOp` guards the `exec` OP arm,
  `c1fba11`). KEY REUSE confirmed: `raisedTriple_pop_nontxn` handles custom frames (`:1190`).
- **`compile_correct` — DONE** (`f603941`, rides `sim`). **Agree diff-test battery — DONE** (`2a8d962`,
  the direct `evalD` examples gain the empty custom store).
- **(d) `run_evalD` (~1080 lines) — THE DELICATE ONE, start FRESH. Assessed 2026-07-09:** uses
  `NoCustomFrame`/`hncf` in 31 places. Threading κ is mechanical, BUT dropping `NoCustomFrame` is the
  coupled wall: (i) the built-in `handle` cases use `hncf.cons_handleF (by intro ℓ p cl; simp)` (works
  only because non-custom); the CUSTOM `handle` case needs a genuinely NEW proof — install a custom frame
  IN `K`, thread `CtxCorr`/`CapLabelCoh`/`FreshCfg`/`NoResume` through it. (ii) the `perform` raise case
  uses `hncf.not_custom hsp` to discharge the custom-resolved subcase by ABSURDITY; this becomes a REAL
  `NoResume`/dispatch proof. **PREREQUISITE machinery NOT yet built (do first):** the EvalCtx-side custom
  bridge — `ctxCustoms` (sibling of `ctxStates`/`ctxTxns` on `Bang.EvalCtx`, NOT the HStack `hsCustoms`
  which IS built), `CtxCorr`-custom install/pop, `CapLabelCoh`/`FreshCfg` custom-frame preservation, and
  `NoResume` for a custom frame. Templates: the `ctxStates` EvalCtx machinery + the HStack `CCorr` family
  already built this session. `perform_miss_raises` /
  `evalD_complete_gen_full` lose `NoCustomFrame` too.
- **(e) `evalD_agrees_source`** — drop the `NoCustomFrame []` argument (now unconditional).
- **(f) `Wasm.lean`** — thread `κ` through `evalD_mono`/`evalD_add`/`evalD_some_le` + `evalD_complete_gen`;
  **DROP `CustomFree`** from `compile_forward_sim` + `evalD_complete_gen` (ADR-0086 named expiry — CITE
  it in the commit; consumer-safe strengthening, no `STATEMENT_CHANGE_OK` re-freeze ritual).
- **(g) `U5bComplete.lean`** — thread `κ` through the `CFStore`/`CFHeap` spine + the ~15 completeness
  arms; the `CFComp`/`CustomFree` scaffolding RETIRES where the custom arm is now defined.
- **(h) machine `compile`/`exec` arm** — `Instr.HANDLE` already carries any `Handler` (HANDLE-defer-
  recompile); `exec`'s dispatch on a custom frame value = `cls.find?` at runtime, mirroring the `evalD`
  perform arm. DERIVE from the extended `evalD` RHS (`compile_correct` custom case).
- **(i) Agree battery + new `#guard`s** — custom→106 / abort→42 through `exec∘compile` (not just
  `Source.eval`); keep `Witness/Fuzz` + `AgreeOutcome` green (they observe the change).
- **(j) census gate** — every clean headline ⊆ trusted-three; record the premise-drops in ADR-0087
  §Status + ADR-0085 Stage-4 note + ADR-0086 (consumer-safe strengthening, no re-freeze).

## Do-not-retry ledger (probe-eliminated / discipline-ruled)
- **Single generalized param store (ADR-0085 D3 collapse) — DEFERRED, not now.** Operator ruling
  2026-07-09: mid-derivation store-collapse is a beautification that inverts invariant #4 (designing the
  elegant machine, then justifying it). Same status as the D5 handler-collapse; take it later,
  census-preserving. Use the 3rd per-kind `CStore`.
- **"Green push-per-slice for the signature change" — DISPROVEN (build-measured, 103 errors).** The
  threading is atomic across files (see Second finding). Do not attempt to bank a partial thread green.
- **Keeping `NoCustomFrame` while defining the arm — DISPROVEN (the coupled-unit finding).** The custom
  `handle` case's term IH needs `NoCustomFrame (custom :: K') = False`.
- **Read-only param is sufficient for v1.** The probe's `customResume`/`nestedCustom` confirm a
  read-only carried param services reader/config/Net. A `put`-like param MUTATION (the pair-return
  protocol, ADR-0087 §Open) is a post-v1 concern — do NOT add it (scope creep past one-shot ⇒
  STOP-and-SHOW).
- **Multi-shot / first-class `k` — OUT OF SCOPE (Q22/Q27).** If the calculation seems to demand
  `CalcReify`/closure cap-rep, STOP-and-SHOW (the labelling-vs-closure fork).

## DESIGN QUESTION — RESOLVED(A) (op-priority vs frame-priority) — operator-approved 2026-07-09
**Resolution A APPROVED** (operator ruling): the machine's `isBuiltinOp` guard on the `exec` OP arm is
the derivation-faithful image of evalD's op-priority perform arm (invariant #4). Evidence pinning the
fork against regression: the `Agree 200 (handle (state 5 7) (handle (custom keyed-"get") (get on state
cap)))` = 7 `#guard` in the (i) battery (`AbstractMachine.lean`, right after the state-get example) —
a built-in `get` is serviced by the state frame, the like-named custom `"get"` clause is BYPASSED; both
`exec∘compile` and `Source.eval` yield 7. Kernel-verified now; the `Agree` half validates when the
module greens (post run_evalD). Original analysis (kept for the record):


`evalD`'s perform arm is OP-PRIORITY: `if get / elif put / elif isTxnOp / else custom`. So a built-in
op (e.g. `get`) that finds no state frame RAISES — it NEVER reaches the custom arm. The machine's `exec`
OP arm is currently FRAME-PRIORITY: stateUpdate → txnUpdate → customUpdate → unwindFind. For a `get`
that raised (no state frame), the machine reaches `customUpdate n "get" v hs` — and if a custom frame at
`n` had a clause keyed `"get"`, it would SERVICE it, DIVERGING from evalD (which raised). Two clean
resolutions (pick before finishing the raised part):
- **(A) mirror evalD's op-priority in the exec OP arm** — guard the customUpdate call by
  `¬(op = "get" ∨ op = "put" ∨ isTxnOp op)`, so the machine reaches custom only in evalD's `else`. This
  is the DERIVATION-FAITHFUL move (the machine falls out of evalD's RHS, invariant #4) and needs no
  cross-frame op-disjointness assumption. Cost: re-touch the `exec` OP arm + `exec_succ` OP case + the
  term-part custom perform case's `hcu` witness. RECOMMENDED.
- **(B) assume/enforce op-disjointness** — custom clause lists never key built-in ops, so
  `customUpdate n "get" v hs = none` holds. Needs the invariant THREADED (a `WfCustomOps` predicate on
  the HStack), reintroducing exactly the premise-creep ADR-0087 dissolved. NOT recommended.
Until resolved, the sim RAISED part's `customUpdate_none_of_*` lemmas (for built-in ops) can't be proven
cleanly. (A) makes them trivial (`customUpdate` guarded off for built-ins).

## Rung-2 lemma templates the induction re-prove leans on (predecessor's ground)
- `capsCls_find?` (`Bang/Core/Freshness.lean:106`) — a `find?`-matched clause's caps land in `capsCls`
  (the honest custom `capsH` bounds them). The custom `CapLabelCoh` preservation at the perform seam
  rides this.
- `NoCustomFrame.not_custom` (`AbstractMachine.lean:3814`) — currently discharges the (vacuous) custom
  `NoResume`/`dispatchRun` arms via absurdity; these become the REAL `dispatch_custom_*` proofs. The
  shape (splitAtId returns a frame FROM K) is the template for the ctxCustoms inversion.
- The `ctxStates`/`splitAtId_of_ctxStates_get` state-side inversion + `updateCtxStates`/`hsStates`
  projections — the mechanical siblings for `ctxCustoms`/`updateCtxCustoms`.

## Status
- [x] Started 2026-07-09 (s4 lane).
- [x] De-risk DONE (`3562cc2`): 4 witnesses green (`scratch/CustomArmShadowProbe.lean`).
- [x] **FORWARD DIRECTION DONE + compiling** (through commit with the op-priority `#guard`, on
      `feat-44-stage4`): (a) evalD custom arm + CStore · (b) all bridge machinery + machine `exec` custom
      dispatch (h) · (c) **`sim` FULLY PROVEN** — the two-part simulation with EVERY novel custom case
      (perform inline-clause-service, perform-raise, custom clause-body-RAISES, custom handle install/pop,
      custom handle raise-FORWARD) · `compile_correct` · the Agree diff-test battery + the op-priority
      regression `#guard`. Op-priority resolution (A) is APPROVED + guard-pinned.
- [ ] **RESUME HERE (converse tail, fresh full budget):** (d) `run_evalD` — see §Plan (d) for the
      ASSESSED wall (31 `NoCustomFrame` uses; custom handle needs a NEW proof; PREREQ = build the
      EvalCtx-side `ctxCustoms` bridge FIRST; the HStack-side `CCorr` family + `raisedTriple_pop_nontxn`
      (handles custom frames, `:1190`) are templates). Then (e) `evalD_agrees_source` · (f) Wasm + drop
      `CustomFree` · (g) U5b · (i) custom `exec∘compile` `#guard`s (custom→106, abort→42) · (j) census.
- [ ] Blockers: the module is RED at the `run_evalD` wall (`AbstractMachine.lean:4813`) — expected
      (atomic re-thread). Gates only on the final green sha. Do NOT start (d) half-depleted.
- [ ] Completed: —

## Owner
- Agent: s4 (compiler-engineer, `feat-44-stage4`). Resume same lane; this doc + the banked patch make it
  work whether the s4 thread is resumed or a fresh s4 opens.

## WIP-push protocol (the next session needs this — this unit is ATOMIC)
Because there is NO green intermediate (both findings above), the fresh session works a long red
stretch across `sim`/`run_evalD`/Wasm/U5b before the first re-compile. That is expected and sanctioned:
- **Intermediate commits on `feat-44-stage4` MAY be red** (the build does not compile mid-thread). To
  commit them, skip ONLY the slow/possibly-red build leg with
  `BANGLANG_SKIP_VERIFY_REASON="stage4 atomic re-thread WIP, final sha gates clean" git commit …`
  (the pre-commit fitness/drift checks STILL run — `tools/git-hooks/pre-commit:109`; this env var gates
  only the `just verify` build, not the ledger/arch checks). Push WIP freely to bank against a lost tree.
- **The LANDING gate is UNCHANGED**: the manager gates the FINAL sha on a clean clone — `just verify`
  EXIT 0 unpiped + `just axioms` (every touched clean headline ⊆ trusted-three, `NoCustomFrame`/
  `CustomFree` OFF the named headlines) + the Agree/`#guard` battery (incl. the new custom→106 /
  abort→42 through `exec∘compile`) + Witness/Fuzz/AgreeOutcome green. A red WIP commit NEVER lands as
  the gate sha; only the green final does.
- **Atomicity still holds**: bank WIP for safety, but do NOT declare the unit done until the whole file
  group re-compiles green. A half-re-keyed `run_evalD` induction pushed red is a checkpoint, not a
  deliverable.

## FINDINGS — op-priority (A) SUPERSEDED by operator ruling (3) id-first; the id-uniqueness wall (2026-07-09)

> This branch (`feat-44-stage4`) is the RECORDED FALLBACK; it does NOT land. The mainline Stage-4 lane
> is `feat-44-stage4-idfirst` (clone `lang-bang-s4x`), which implements the operator's route (3). This
> section records the wall that motivated (3) — worth writing down verbatim, per the lead's ruling.

**What superseded (A).** The §DESIGN QUESTION above ruled (A): mirror evalD's OP-PRIORITY perform arm
in the machine (`isBuiltinOp` guards the `exec` OP arm). The operator later ruled that op-priority is an
UNFAITHFUL lowering of the kernel: `Source.step`'s `idDispatch` is ID-FIRST — it resolves the cap's
identity to ONE frame (via `splitAtId`), then a `handlesOp` gate, then `dispatchOn`; the op name never
disambiguates WHICH frame. Route (3): re-derive evalD's perform arm id-first — `match σ.get? n, τ.get? n,
κ.get? n` (which per-kind store holds the identity, disjoint by StratFresh), then op-within-kind — and
drop the machine's `isBuiltinOp` prefilter. A custom frame keyed `"get"`, addressed by identity, SERVICES
its clause (the exact opposite of (A)'s bypass). No `WfCustomOps`; no store-value premise chain.

**The id-uniqueness wall (route-independent, load-bearing for TRUTH — not proof convenience).** Under
id-first, the `sim` (evalD↔machine) correspondence is FALSE without machine-hs cross-kind id-uniqueness.
Witness, verbatim:

    hs = [ state-frame  id=n2 (s := …) ]      -- shallower
         [ txn-frame    id=n2 (Θ := …) ]      -- SAME identity n2, deeper
    perform (vcap n2 ℓ) "newTVar" v            -- a txn op, addressed to n2

    evalD:   σ.get? n2 = some s  → STATE arm → op ∉ {get, put} → RAISE n2 "newTVar" v
    machine: stateUpdate n2 "newTVar" v hs = none  (state frame, wrong op ⇒ `else none`)
             txnUpdate   n2 "newTVar" v hs        walks PAST the state frame, finds the
                                                  same-id txn shadow, SERVICES it → RESUME
    RAISE (evalD) vs RESUME (machine) = divergence.

Why op-first (A) hid it: the op-name prefilter never resolved by store-membership, so it never exposed a
same-id cross-kind shadow. `Corr`/`TCorr`/`CCorr` are projection EQUALITIES (`σ = hsStates hs`, …) that
do NOT forbid the pathological same-id-different-kind `hs`. INDEPENDENTLY CORROBORATED: the mainline lane
(`feat-44-stage4-idfirst`) hit this identical gap with the identical witness from a separate id-first
rework — evidence the invariant is real, not an artifact of one derivation.

**Resolution (mainline, lead-ruled 2026-07-09).** `sim` gains the CONJUNCTION `StoresBelow g ∧
StoresDisjoint`: `StoresDisjoint` = no identity in two per-kind stores (the id-uniqueness premise);
`StoresBelow` = every store identity `< g` (the fresh counter — the machine twin of `WellCounted`,
needed for push-stability of the conjunction). Threaded STRUCTURALLY from `FreshCfg` (the discharge),
stated as a `sim` premise (the form). Trivially true at the empty-store entry configs ⇒ consumers
(`compile_correct`/`Agree`) discharge it for free. INTERNAL to `sim` — headlines stay VcapFree-only;
nothing frozen moves. The machine-reshape alternative (make the OP arm mutually-exclusive by
construction) was REJECTED: larger churn, and the invariant is real on both sides already — state it,
don't rebuild the machine around it.

**This fallback's state.** `feat-44-stage4` tip `761299a` carries: the complete axiom-clean (1')
forward half (WfCustomOps route, earlier in history) AND a partial route-(3) id-first attempt (evalD/
exec/sim-term id-first green; sim-raised reshaped but RED at this wall, banked as sanctioned WIP). It is
the recovery branch if (3) hits an unforeseeable wall; it will not merge.

## Notes
- All frozen-statement changes in this unit are pre-authorized premise-DROPS (ADR-0086 `CustomFree`,
  ADR-0087 `NoCustomFrame`) — consumer-safe strengthenings, no `STATEMENT_CHANGE_OK`. Anything ELSE
  frozen-statement-touching is a STOP-and-SHOW.
- Method: refute-first is DONE for the witness class; the grind is the induction re-prove. Gate each
  green re-compile of the whole file group with `just axioms` on force-rebuilt oleans; NEVER grep-for-
  sorry. `lake build` exit 0 unpiped. Custom `#guard`s must run through `exec∘compile`, not only
  `Source.eval`.
