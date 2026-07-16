<!-- note-status: active -->
# Rung-5 S5 proof-grade — the obligation, RE-FRAMED (one half done, one half unstateable in v1)

> **Verdict (one sentence).** The S5 slice as written ("extend the `wexec ≡ Source.eval`
> obligation over the S0–S4 effectful WasmGC path, with the `$env`-slot↔store bijection")
> splits into a half that is **already a proven axiom-clean theorem** (`compile_forward_sim`
> over the whole v1 effect set, on the CalcVM→`wexec` backend) and a half that is
> **unstateable in v1** (the `$env`-slot↔store bijection lives only on the `emitModuleGC`
> text emitter, which has NO Lean operational semantics — stating `≡ Source.eval` against it
> requires building the post-v1 ADR-0059 GC abstract machine, out of scope). The honest S5
> deliverable is: re-export the proven half under the S5 name (done, `Bang/Backend/
> Rung5ProofGrade.lean`), and PRICE the other half as a named wall (this note).

Skeleton: `Bang/Backend/Rung5ProofGrade.lean` (builds; both re-exports axiom-clean). Design
note this refines: `emission-rung5-design.md` §(a) (the two backends), §(c) (frame-chain = post-v1).

---

## The load-bearing fact: rung 5 has TWO disjoint backends, only one carries a proof

The rung-5 design note §(a) already documents that the effect fragment (rungs 1-3, inline) and
the closure fragment (rung 4, GC) are "two different machines for the SAME kernel". S5 forces the
question of WHICH machine the proof-grade obligation attaches to — and the answer is that the two
backends have entirely different verification stories:

```
                proof-carrying backend                  text-emission backend
                (Bang/Backend/Wasm.lean)                (Bang/Backend/WasmEmit.lean)
                ────────────────────────                ────────────────────────────
  entry         compileC : Comp → Wasmfx.Module         emitModuleGC : Comp → EmitGC  (EmitGC wraps String)
  abstract      wexec : Nat→Nat→Code→VStack→HStack       — NONE — the .wat text is executed
   machine        → Option VStack  (a Lean def)            by REAL wasmtime, off-Lean
  value rep     Wasmfx.Val (int / unit / ref-tagged)     $val GC supertype ($ival/$sum/$pair/$clos)
  env + handler HStack that SHARES the CalcVM `Handler`   $env cons-list + $ref box + $txbox journal
  effect arms   markH · unmarkH · opH (opH = the 4-way   handle→mint $ref/tag env slot;
                 state/txn/custom/unwindFind dispatch)    perform→struct.get/set / call_ref / try_table
  S0–S4 built?  effect arms landed pre-rung-5             YES — S0–S4 built exactly here
  oracle        Source.eval — a Lean THEOREM             Source.eval — a differential HARNESS
                                                          (emit-rung5-effects-diff.sh: wasmtime==bang run)
```

The `$env`-slot↔store bijection that S5 names is a relation between the CalcVM STORE and the GC
VALUE rep of the RIGHT column. But the right column has no machine to relate. The LEFT column has
the machine and the theorem — and there the "bijection" degenerates to the IDENTITY injection
(`injHStack`), because `wexec`'s HStack literally holds the CalcVM `Handler`; a `state` cell, a
`txn` Θ, a `custom` clause list are the SAME objects on both sides, not bijection-mediated images.

## Half 1 — the effectful `wexec ≡ Source.eval` obligation is ALREADY DISCHARGED (axiom-clean)

On the proof-carrying backend the S5 headline is a COMPLETED theorem, dated at the shas below:

- `Bang.Wasmfx.exec_wexec_sim_ok` (`Wasm.lean:1954`) — the FULL effectful `exec ≡ wexec`
  lockstep. Its OP arm is the 4-way `stateUpdate → txnUpdate → customUpdate → unwindFind` dispatch
  (state · transaction · custom · throws-abort); its HANDLE arm mints `id := g` exactly as `exec`.
  `#print axioms` = `[propext, Quot.sound]`.
- `Bang.compile_forward_sim` (`Spec.lean:365`) — composes it with the reverse CalcVM bridge:
  `Source.eval fuel c = done v ⇒ ∃ f', Wasmfx.run f' (compileC c) = some (compileV v)`, premised on
  `VcapFree c` ONLY (the `CustomFree` scaffolding was dropped at #62 slice 3, ADR-0085 Stage 4).
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

Both cover the WHOLE v1 handler set. The `CustomFree` drop means user-defined/custom effects — the
S4 fragment — are INSIDE this theorem already. `Bang/Backend/Rung5ProofGrade.lean` re-exports both
under the S5 name (`s5_effectful_forward_sim`, `s5_exec_wexec_lockstep`), both re-checked axiom-clean.
`Wasmfx.run` returns `Option Wasmfx.Val`: only a singleton successful final value is `some`; the
abstract runner intentionally leaves fuel, stack-shape, handler-state, and unhandled-operation
non-values unclassified as `none` rather than borrowing the source evaluator's `Result` cases.

### What `VcapFree` excludes — the host-IO boundary, named precisely

`VcapFree c := capsC c = []` (`Bang/Core/Freshness.lean:129`) forbids a `vcap` LITERAL in the source
term. It does NOT restrict any effect FORMER — `capsH` recurses INTO `.custom`/`.state`/
`.transaction` handler payloads (`Freshness.lean:84`), so a program using the full v1 effect set is
`VcapFree` as long as it contains no raw `vcap` node. The natural question is what emits such a node.
Since #126 (ADR-0104 §4), exactly ONE program class does: an ambient module-qualified host perform
(`Io.print`, `Clock.now`, …) lowers via `hostPerformS` to a literal `perform (vcap hostCapId ℓ) op …`
(`Bang/Frontend/Surface.lean:213`, `hostCapId = 999999999999`). Such a program is therefore NOT
`VcapFree` (`capsC` returns `[(hostCapId, ℓ)]`) and sits OUTSIDE `compile_forward_sim`'s class — BY
CONSTRUCTION, which is the correct and intended behaviour: host-IO is the deliberate ADR-0104 tested-
stratum boundary. The raw-vcap Comp is emitted UNCONDITIONALLY (not host-mode-gated), so it CAN
reach `compileC` — measured: `--compiled` on `ambient.bang` collapses fail-loud (exit 5, no value)
and the oracle gives `escapedCap` (exit 3, ADR-0063) — the theorem simply says nothing about that
class, and the runtime never lies about it. Its CORRECT runtime is
`evalEHost` (`Bang/Backend/EnvMachine.lean:3323`), a byte-for-byte sibling of `evalE` gated by
`test-hostio-seam.sh` + the `hostReplay_agrees_pure` `#guard`s, and the rung-5 emitter independently
lists `hostio-echo` as a named refusal. So the coverage claim holds not because "the elaborator never
emits a `vcap`" (it does, for host-IO — that phrasing is retired) but because `VcapFree` is precisely
the predicate that excludes the one class that does, keeping it on the tested stratum where ADR-0104
places it. The exclusion is now a visible PREMISE CONSEQUENCE, not only a design intention.

## Half 2 — the `$env`-slot↔store bijection over `emitModuleGC` is UNSTATEABLE in v1

The obligation the note literally names would read (informally):

```
    ∀ c, EffectfulS0S4 c  →  ⟦ emitModuleGC c ⟧_wasmgc  ≡  Source.eval c      (under $env-slot↔store)
```

- `⟦·⟧_wasmgc` — a Lean operational semantics over the emitted `.wat` — **does not exist**.
  `emitModuleGC`/`emitModuleGCPrint` are `partial def : Comp → EmitGC` where `EmitGC` wraps a
  `String`. There is no `wexec`-analog over that string (grep: zero `def wexec/run/exec` in
  `WasmEmit.lean`). The codomain is TEXT; the only handle on its meaning is RUNNING it.
- Building `⟦·⟧_wasmgc` IS the ADR-0059 GC-frame abstract machine ($val heap, $env cons-list,
  struct.get/set on $ref/$txbox, call_ref clause-resume, try_table/throw_ref rollback). The rung-5
  design note §(c) itself declares this **post-v1, out of scope** ("Rung 5 needs no switch/resume,
  no reified frame chain … the ADR-0059 GC-frame-chain slot is the POST-v1 multi-shot fast-path").
- And it would be a **hand-designed** machine unless CALCULATED from `evalD` — building it to verify
  `emitModuleGC` after the fact inverts **invariant #4** (the machine is the calculation's output,
  never verified-after-the-fact). A faithful proof-grade GC path would re-derive `emitModuleGC` as
  the lowering of a calculated `$val`/`$env` machine — a rung-5-scale calculation, not an S5 slice.

So `emitModuleGC` stays verified per **invariant #1** by the differential harness
(`tools/emit-rung5-effects-diff.sh`: real wasmtime stdout == `bang run` == `Source.eval`, 34 whole
programs, 22 effectful). That is the sanctioned tested-stratum oracle for a path with no calculated
machine — exactly the stratification principle (verified core = the `compileC`→`wexec` backend;
tested superset = the `emitModuleGC` text backend; the seam is which backend a program routes through).

## What WOULD unlock the proof-grade GC bijection (the priced future slice — NOT S5, NOT v1)

1. **Calculate** a `$val`/`$env` GC abstract machine `wgcexec` from `evalD` (Bahr–Hutton, as the
   inline `exec` was) — its handler arms carry `$ref`/`$txbox` cells. Cost: a rung-5-scale
   calculation (comparable to the original CalcVM derivation), gated on ADR-0059 landing.
2. Prove `wgcexec ≡ wexec` (or directly `≡ exec`) — HERE the `$env`-slot↔store bijection becomes a
   real definition (`envSlotStore : GCEnv ≃ (SStore × THeap × CStore)`) and the theorem is stateable.
3. Show `emitModuleGC` is the faithful text image of `wgcexec` (an `exec_wexec`-style lowering sim).

This is the same three-step shape the inline path already has (calculate → lockstep → lower-to-text),
re-run for the GC rep. It is additive and post-v1; opening it before ADR-0059 lands would be a
hand-designed machine (inv #4 violation) or a stateless bijection over text (meaningless).

## One-glance status

```
S5 AS "extend the effectful wexec≡Source.eval obligation"  →  DONE. compile_forward_sim +
        exec_wexec_sim_ok cover state/throws/txn/custom, axiom-clean. Re-exported in
        Bang/Backend/Rung5ProofGrade.lean (s5_effectful_forward_sim, s5_exec_wexec_lockstep).
S5 AS "$env-slot↔store bijection over emitModuleGC"        →  UNSTATEABLE in v1. emitModuleGC is a
        Comp→String text emitter with NO Lean machine; the bijection needs the post-v1 ADR-0059 GC
        abstract machine, which must be CALCULATED (inv #4), not built to verify-after-the-fact.
SEAM          the emitModuleGC backend stays differential-tested (emit-rung5-effects-diff.sh, inv #1)
              — the sanctioned tested-stratum oracle for a path with no calculated machine.
UNLOCK        calculate wgcexec from evalD → prove ≡ → show emitModuleGC is its text image
              (3 steps, post-v1, gated on ADR-0059). NOT an S5 slice.
```
