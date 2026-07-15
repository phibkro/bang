module

public import Bang.Backend.Wasm
public import Bang.Backend.WasmEmit

/-!
  Rung5ProofGrade.lean — the ◊5.5 rung-5 S5 "proof-grade" obligation, STATED (Phase 1).
  ═══════════════════════════════════════════════════════════════════════════════════════

  S5 (design note `emission-rung5-design.md`) asks to "extend the `wexec ≡ Source.eval`
  correctness obligation over the S0–S4 effectful WasmGC path … with the `$env`-slot↔store
  bijection". Sinking proof effort requires first FREEZING what is claimed, against WHICH
  machine, over WHICH program class. Doing that here surfaces a structural fact that REDIRECTS
  the slice: **the machine has two disjoint backends, and the effectful `wexec ≡ Source.eval`
  obligation is ALREADY discharged on the one that carries a proof, while the `$env`-slot↔store
  bijection only exists on the one that carries NO Lean semantics.**

  ## The two backends (rung-5 design note §(a) names them; this file pins the proof consequence)

  ```
                  proof-carrying backend                 text-emission backend
                  ───────────────────────                ─────────────────────
    entry         compileC : Comp → Wasmfx.Module        emitModuleGC : Comp → EmitGC (String)
    machine       wexec : … → Option VStack              — NONE — (the .wat is run by wasmtime)
    value rep     Wasmfx.Val (int/unit/ref-tagged)       $val GC supertype ($ival/$sum/$pair/$clos)
    env / handler HStack SHARES CalcVM `Handler`          $env cons-list + $ref box + $txbox journal
    effect arms   markH/unmarkH/opH (state/txn/           handle→mint $ref/tag slot; perform→
                  custom/throws — the 4-way OP dispatch)  struct.get/set/call_ref/try_table
    oracle        Source.eval (a Lean THEOREM)            Source.eval (a differential HARNESS)
    S5 target?    ALREADY PROVEN (see below)              UNSTATEABLE without building a machine
  ```

  ### (1) The effectful `wexec ≡ Source.eval` obligation is ALREADY DISCHARGED — axiom-clean.

  `Bang.Wasmfx.exec_wexec_sim_ok` (Wasm.lean:1953) proves the FULL effectful lockstep
  `exec ≡ wexec` — its OP arm is the 4-way `stateUpdate → txnUpdate → customUpdate → unwindFind`
  dispatch, its HANDLE arm mints `id := g` exactly as `exec` does, over the WHOLE v1 handler set
  (state · throws · transaction · custom). `Bang.compile_forward_sim` (Spec.lean:324) composes it
  with the reverse CalcVM bridge to yield the end-to-end
  `Source.eval fuel c = done v ⇒ ∃ f', Wasmfx.run f' (compileC c) = done (compileV v)`, premised on
  `VcapFree c` ONLY (the `CustomFree` scaffolding was DROPPED at #62 slice 3 — ADR-0085 Stage 4).
  `#print axioms` on BOTH ⊆ {propext, Classical.choice, Quot.sound}.

  So the S5 headline, read against the machine that HAS a machine, is a COMPLETED theorem, not a
  new obligation. This file re-exports it under the S5 name to make that explicit.

  ### (2) The `$env`-slot↔store bijection is UNSTATEABLE in v1 — a priced honest wall.

  The bijection S5 names ("`$env` slot ↔ store", "`$ref` box ↔ state cell", "`$txbox` journal ↔
  Θ") is a relation between the CalcVM STORE and the GC-text VALUE rep of the OTHER backend
  (`emitModuleGC`). To STATE `wexec_gc ≡ Source.eval` one first needs a `wexec_gc` — a Lean
  operational semantics over the emitted `.wat`: a `$val` heap, an `$env` cons-list machine,
  `struct.get`/`struct.set` on `$ref`/`$txbox`, `call_ref` for clause resume, `try_table`/
  `throw_ref` for rollback. `emitModuleGC` (WasmEmit.lean) is a `partial def : Comp → String`
  text emitter with NO such machine (grep: zero `def wexec`/`run`/`exec` over its output).

  Building that machine IS the ADR-0059 GC-frame abstract machine — which the rung-5 design note
  §(c) itself declares POST-v1, out of scope ("Rung 5 needs no `switch`/`resume`, no reified frame
  chain … the ADR-0059 GC-frame-chain slot is the POST-v1 multi-shot fast-path"). And it would be
  a HAND-DESIGNED machine unless calculated from `evalD` — which inverts invariant #4. The
  `emitModuleGC` backend is verified per invariant #1 by the DIFFERENTIAL HARNESS
  (`tools/emit-rung5-effects-diff.sh`: real `wasmtime` stdout == `bang run` == `Source.eval`),
  which is the sanctioned tested-stratum oracle for a path with no calculated machine. Promoting
  it to proof-grade is a machine-build gated on post-v1 ADR-0059, NOT an S5 slice.

  ### Verdict (Phase 1)

  S5 as "extend the effectful `wexec ≡ Source.eval` obligation" = DONE (re-exported below,
  axiom-clean). S5 as "prove the `$env`-slot↔store bijection over `emitModuleGC`" = UNSTATEABLE
  in v1 (needs the post-v1 ADR-0059 GC machine; the emitter stays differential-tested per inv #1).
  See `docs/notes/rung5-s5-proofgrade-refutation.md` for the full priced wall + what WOULD unlock it.
-/

namespace Bang.Rung5ProofGrade

-- Module reveal: these are theorem statements re-exported for downstream reference (the S5
-- headline record). `public section` makes them cross-module reachable; no `@[expose]` (no
-- definitional consumer needs them unfolded).
public section

open Bang

/-! ## (1) S5 re-export — the effectful obligation, already proven. -/

/-- **S5 (statable half) — the effectful `wexec ≡ Source.eval` obligation, on the PROOF-CARRYING
backend.** This is `compile_forward_sim` under the S5 name: for the whole v1 effect set
(state · throws · transaction · custom, all carried by `compileC`→`wexec`'s handler opcodes), a
`Source.eval` success is matched by a `Wasmfx.run` of the compiled module. Premised on `VcapFree c`
(= `capsC c = []`, i.e. the source term carries no `vcap` LITERAL). This holds for ordinary
elaborator output (which binds caps as `vvar` and mints identities only at runtime `handle`) but is
NOT vacuous: since #126, an ambient module-qualified host perform (`hostPerformS`) lowers to a
literal `perform (vcap hostCapId ℓ) …` (`Bang/Frontend/Surface.lean`), so a host-IO program is NOT
`VcapFree` and sits OUTSIDE this theorem's class by construction — the deliberate ADR-0104 tested-
stratum boundary, now visible as a premise consequence rather than only a design intention. The
raw-vcap Comp CAN reach `compileC` (e.g. `--compiled`), where this theorem says nothing about it and
the runtime fails LOUD (no-value collapse / oracle `escapedCap`, ADR-0063) — never silently wrong;
it runs CORRECTLY only on the `evalEHost` driver (`--env=real`/`--record`/`--replay`). Axiom-clean — inherits `compile_forward_sim`'s
{propext, Classical.choice, Quot.sound}. The `$env`-slot↔store bijection is NOT part of this
statement: the `wexec` HStack SHARES the CalcVM `Handler`, so state/txn/custom cells are the SAME
objects, related by the identity injection (`injHStack`), not a bijection. -/
theorem s5_effectful_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
    Bang.Model.VcapFree c →
    Source.eval fuel c = Result.done v →
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) :=
  compile_forward_sim_proof

/-- The effectful lockstep the S5 obligation rests on, re-exported for the record: the WASM
abstract machine `wexec` matches the calculated `exec` over the FULL handler set (its OP arm is
the 4-way state/txn/custom/abort dispatch). Axiom-clean ([propext, Quot.sound]). -/
theorem s5_exec_wexec_lockstep :
    ∀ (f g : Nat) (code : CalcVM.Code) (s s' : CalcVM.Stack) (hs : CalcVM.HStack),
      Wasmfx.CodeOk code → Wasmfx.HStackOk hs →
      CalcVM.exec f g code s hs = some s' →
      Wasmfx.wexec f g (lowerCode code) (Wasmfx.injStack s) (Wasmfx.injHStack hs)
        = some (Wasmfx.injStack s') :=
  Wasmfx.exec_wexec_sim_ok

/-! ## (2) S5 unstateable half — the `$env`-slot↔store bijection over `emitModuleGC`.

The obligation the design note literally names would read (informally):

    ∀ c, EffectfulS0S4 c → ⟦ emitModuleGC c ⟧_wasmgc ≡ Source.eval c   (under $env-slot↔store)

but `⟦·⟧_wasmgc` — a Lean operational semantics over the emitted `.wat` — DOES NOT EXIST, and its
domain `EmitGC` is `String`. There is no way to write the `≡` without first building that machine
(the post-v1 ADR-0059 GC-frame machine). We DEMONSTRATE the gap is real by naming the only handle
we have on the emitter's output: it is text.  -/

/-- The `emitModuleGC` backend's codomain is `String` (an `EmitGC.ok`/`.unsup` wrapper), NOT a
value in any machine — this is the concrete reason a `≡ Source.eval` theorem is unstateable against
it. `emitModuleGC c` reduces to a `String`-carrying `EmitGC`; there is nothing to relate to `v`
except by RUNNING it (the differential harness), which is a meta-level check, not a Lean theorem. -/
example (c : Comp) : (WasmEmit.emitModuleGC c).isOk = true ∨ (WasmEmit.emitModuleGC c).isOk = false := by
  cases (WasmEmit.emitModuleGC c).isOk <;> simp

-- The `≡`-over-bijection theorem is intentionally ABSENT — writing it requires a machine that is
-- out of v1 scope (ADR-0059, post-v1). An admitted stub here would be a lie (it would claim the
-- statement is meaningful); the honest artifact is its ABSENCE plus the refutation note. §(2) above.

end -- public section

end Bang.Rung5ProofGrade
