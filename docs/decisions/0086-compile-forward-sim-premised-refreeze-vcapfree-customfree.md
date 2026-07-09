# ADR-0086 · `compile_forward_sim` re-freeze: `VcapFree` + `CustomFree` premises (true-but-unprovable, made provable)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The ◊5 headline `compile_forward_sim` (Spec.lean:292) quantifies over RAW `Comp` with no premise, and the #16 completeness spine (the converse-of-`run_evalD` bridge, `origin/inc6-u5b2`) proved its only known proof architecture CANNOT reach two program classes the statement includes: (i) non-`VcapFree` programs (a buried never-forced `vcap` completes in the kernel while failing the `FreshCfg` the evalD-bridge needs — machine-checked, `scratch/VcapFreeRefute.lean`) and (ii) `Handler.custom`-containing programs (`evalD custom = none` by ADR-0085 Stage-1, while the kernel and the WASM machine both handle custom generically). Both witnesses ALSO machine-check that the headline is **TRUE on those classes** (both sides complete identically, all `rfl`) — so this is "premise an unprovable true statement," NOT "repair a false one." **Decision (operator ruling 2026-07-09, option a2): re-freeze `compile_forward_sim` with BOTH premises — `VcapFree c → CustomFree c → …` — making the headline provable sorryAx-ZERO from the banked spine.** Both premises are vacuously true for every elaborator-produced program (the elaborator emits `vvar` not `vcap`; no surface form produces `custom` until ADR-0085 Stage 7), so the product-facing meaning of ◊5 is unchanged. `CustomFree` is TEMPORARY scaffolding: ADR-0085 Stage 4 (the derived custom machine arm) DROPS it — a premise-drop is a consumer-safe strengthening. `VcapFree` persists until raw `vcap` becomes untypeable (#21 scoped capability types), after which it is derivable. Rejected: (a1) `VcapFree`-only (same re-freeze ritual, strictly weaker endpoint — the custom arm stays a sorryAx); (b) no re-freeze (the heart-of-the-contribution headline stays flagged until the full #44 metatheory arc); proving the unpremised form (no known architecture; the bridge NEEDS `FreshCfg`, witness-refuted derivable).
- **Depends-on**: 0016, 0035, 0052, 0063, 0085
- **Relates-to**: 0056 (VcapFree lineage: "elaborator emits vvar, discharged at inc-7"), #16 (the completeness spine this unblocks), #21 (scoped capability types — makes `VcapFree` derivable later), Q22/Q27 (multi-shot — Stage-4 context)

## Status

Accepted (2026-07-09, operator ruling "(a2)"). Statement change executes with `STATEMENT_CHANGE_OK=ADR-0086`.

- **Layer:** C (compiler — the ◊5 headline statement). Frozen-statement change: this ADR is the required governance artifact.

## Context

Issue #16 (U5b-handler completeness) delivered the converse-of-`run_evalD` spine — 1226 lines, every
arm closed for the three built-in handler kinds, K=[] adapter included (`origin/inc6-u5b2`, gated
2026-07-08). Wiring it into the frozen headline exposed that the statement's generality exceeds what
any known proof can reach, in exactly two places:

1. **`VcapFree`** — the bridge routes through `FreshCfg (0,[],c)`, which unfolds to `capsC c = []`.
   `Source.eval fuel c = done v` does NOT imply it: `scratch/VcapFreeRefute.lean` (all `rfl`) shows
   `letC (ret (vthunk (perform (vcap 99 0) "get" unit))) (ret unit)` completes while failing
   `VcapFree` and `FreshCfg`. The premise is statement-necessary for the architecture. The SAME
   witness also shows `Wasmfx.run 100 (compileC cWitness) = done unit` — the headline HOLDS there
   (the dead thunk is discarded by both sides). Precedent: `evalD_agrees_source` already carries
   `VcapFree` for the same reason.
2. **`CustomFree`** — ADR-0085 Stage-1 left `evalD (handle (.custom …) M) = none` (the machine arm
   is Stage-4 output), while the kernel's `handle`/pop arms are handler-agnostic. The Stage-1
   "vacuous discharge" bet protects SOUNDNESS-direction proofs (hypothesis `evalD = some` is absurd)
   but INVERTS for completeness (hypothesis is the kernel run). `scratch/CustomStage1Refute.lean`
   (all `rfl`): on `handle (custom 0 unit (fun _ => none)) (ret 5)`, `Source.eval 50 = done 5` AND
   `Wasmfx.run 100 (compileC c) = done (int 5)` — the headline HOLDS (the WASM HANDLE is also
   handler-agnostic); a custom-SERVICING body escapes in the kernel (dispatch inert) ⟹ vacuous.
   No custom counterexample exists; the gap is proof-route-only.

So the evidence situation is: **headline true on every probed class, provable on none of the
excluded ones.** The honest theorem is the premised one.

## Decision

Re-freeze the ◊5 headline (Spec.lean:292) as:

```
theorem compile_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
    VcapFree c → CustomFree c →
    Source.eval fuel c = Result.done v →
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v)
```

with the internal `evalD_complete_gen` (Bang/Backend/Wasm.lean) premised identically. `CustomFree`
(no `Handler.custom` node — the `CFComp`/`CFVal`/`CFHandler` family with shift/subst preservation,
proven @ `3783d4d`) is PROMOTED from scratch into a Core module per arch-check placement.

**Premise lifecycle (the load-bearing nuance):**
- `CustomFree` is scaffolding with a NAMED expiry: ADR-0085 Stage 4 derives the custom machine arm,
  after which the premise is DROPPED. Dropping a premise strengthens the theorem — consumer-safe,
  no second re-freeze ritual (record the drop in ADR-0085's status).
- `VcapFree` expires when #21 (scoped capability types) makes a raw source `vcap` untypeable; until
  then it is the same honest boundary `evalD_agrees_source` already carries. Every elaborated
  program satisfies both premises by construction (ADR-0056 lineage: the elaborator emits `vvar`,
  never `vcap`; no surface form emits `custom` until Stage 7).

**Execution (task #11 + wire-in, one atomic IC unit):**
1. `CompletesTo` gains the CFVal-of-result field; an `evalD`-preserves-`CustomFree` fact; re-thread
   the ~15 spine arms (design mapped and banked @ `3783d4d`).
2. Promote `CustomFree` into the built tree; transplant the spine from scratch into
   `Bang/Backend/Wasm.lean`; amend `evalD_complete_gen`; adjust its one call site.
3. Spec.lean statement change under `STATEMENT_CHANGE_OK=ADR-0086`; wire
   `compile_forward_sim_proof`; gate: `#print axioms compile_forward_sim` ⊆ {propext,
   Classical.choice, Quot.sound} on a force-rebuilt olean; `compile_forward_sim_pure` /
   `source_eval_to_exec` / `sim` / `run_evalD` unchanged-clean; both witnesses kept as
   do-not-weaken regression files.

## Considered options

- **(a2) both premises — CHOSEN.** SorryAx-ZERO headline now; scaffold premise dropped at Stage 4.
- **(a1) `VcapFree` only — REJECTED.** Identical re-freeze ritual and ADR cost, strictly weaker
  endpoint (the custom arm stays a documented sorryAx, like `handler_compiles`).
- **(b) no re-freeze — REJECTED.** Keeps the paper-headline flagged until the full #44 Stage-4 arc;
  the banked spine sits unwired for months.
- **Stage-4 now — REJECTED.** The custom machine-arm derivation is the riskiest #44 obligation
  (ADR-0085), a dedicated arc; pulling it forward to un-flag one headline inverts the sequencing.
- **Prove the unpremised form — REJECTED as unavailable.** The only known completeness architecture
  (store-threaded converse, congruence and determinism routes build-refuted — PATH-inc6
  do-not-retry ledger) requires `FreshCfg`; witness `VcapFreeRefute` proves it undeliverable from
  the eval hypothesis.

## Invariant compliance

- **#1 (proof rides the reference):** strengthened — completeness closes the reference↔machine
  bridge in the remaining direction, premised honestly.
- **#4 (machine = output of calculation):** preserved — no hand-patched custom arm; the premise
  EXCLUDES custom until Stage 4 calculates it.
- Frozen-statement discipline: this ADR + `STATEMENT_CHANGE_OK` is the sanctioned path (ROADMAP
  "frozen things change only via ADR + downstream re-validation"). Downstream re-validation =
  the gate suite in Execution §3.

## Revisit if

- ADR-0085 Stage 4 lands → DROP `CustomFree` from the statement (consumer-safe; note in 0085).
- #21 scoped capability types land → `VcapFree` becomes derivable for all typed programs; keep the
  premise but add the discharging lemma (or drop it for the typed corollary).
- A proof architecture not needing `FreshCfg` emerges → the unpremised form may return; the
  witnesses bound what any such architecture must handle.

## Evidence

Machine-checked witnesses `scratch/VcapFreeRefute.lean` (corrected characterization @ `e24b005`:
premise-necessary + headline-true) and `scratch/CustomStage1Refute.lean` (@ `3b03927`: no
refutation, headline-true, proof-gap-only) on `origin/inc6-u5b2`; the completeness spine + K=[]
adapter + `CustomFree` machinery (@ `3783d4d`, manager-gated on committed content: EXIT 0, exactly
1 custom sorry); unchanged-clean census on `compile_forward_sim_pure` / `source_eval_to_exec` /
`CalcVM.sim` / `CalcVM.run_evalD` throughout. Frozen-statement read of Spec.lean:292 (raw-`Comp`
quantification, 2026-07-08 survey). Full IC reports: session transcript 2026-07-08.
