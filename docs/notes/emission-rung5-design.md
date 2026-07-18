<!-- note-status: active -->
<!-- describes: Bang/Backend/WasmEmit.lean tools/emit-rung5-print-diff.sh tools/emit-rung5-effects-diff.sh @ 569cca42fa09aeae47529aafc9cd2d7c68831d60 -->
# Emission rung-5 design — unifying effects onto the GC path (the "closures + handlers" rung)

> **Re-audit (2026-07-18, `569cca42`):** `emit-rung5-effects-diff.sh` reports 46 emitted whole
> programs matching `bang run`, 23 of them effectful, plus the raw typed-IR stateful custom update
> witness. `emit-rung5-print-diff.sh` reports 23/23 readback and module-aware programs matching,
> including `calc` and `json`. The four-case escape differential is also hard-green.

> **Verdict (one sentence).** Rung 5 unifies the two disjoint lowerings (inline rungs 1-3 for the
> effect fragment, GC rung 4 for the closure fragment) onto **one `$val`/`$env` GC representation** —
> and the load-bearing finding is that **v1 needs NO reified continuations and NO ADR-0059 GC
> frame-chain**: every v1 handler form (throws · state · transaction · one-shot custom) resumes
> **one-shot in-place** (ADR-0025 D1: "no continuation value, no multi-shot reification"), so the
> unified rep keeps rung 4's never-reify property for the whole v1 effect set. The wall is smaller
> than feared: it is a REPRESENTATION merge (compile-time `Slot` stack → runtime `$env` cons-list with
> effect-carrying slots), not a continuation-machine build. A hand-unified witness (a closure reading
> a state cell) runs on wasmtime 45 == the kernel value.

Design probe only — maps the slices for the implementation lane; no emitter change lands here (Part 1,
the `$val` readback, landed separately). Witnesses: `scratch/rung5-unified-closure-state.wat` (⇒ 8),
`scratch/rung5-put-through-closure.wat` (⇒ 20).

---

## (a) · Where the two lowerings genuinely disagree

The inline path (rungs 1-3) and the GC path (rung 4) are two different machines for the SAME kernel:

| axis | inline (rungs 1-3) | GC (rung 4) | disagreement |
|---|---|---|---|
| **value rep** | bare `i64` on the wasm stack / in locals | `$val` GC supertype (`$ival`/`$sum`/`$pair`/`$clos`) | a value is unboxed on one path, a heap ref on the other |
| **environment** | COMPILE-TIME `Slot` list (`.val local`, `.cap tag`, `.state local`, `.txn heaplen`) | RUNTIME `$env` cons-list of `$val` refs | the de-Bruijn env is STATIC metadata vs a heap value |
| **handler frame** | the `Slot` stack IS the frame stack — one slot per open `handle`, resolved at emit time | no handler arm exists (rung 4 refuses `handle`/`perform`) | closures can't see compile-time slots; slots can't be captured |
| **`throws`** | `try_table (catch $exn_t)` + `throw $exn_t` (tag = handler identity) | — | control-flow, rep-agnostic — SURVIVES unchanged |
| **`state`** | one mutable wasm LOCAL, `get`/`put` = `local.get/set` (resume in place) | — | a local can't be captured by a lifted closure |
| **transaction** | linear MEMORY (`8·i` per cell) + `$heaplen` + `catch_all_ref`/`throw_ref` rollback | — | a raw memory heap is orthogonal to the GC heap |

The ONE hard conflict: **a `state`/`txn` cell lives in a wasm LOCAL / linear memory, but a closure
lambda-lifted out of the handled region captures only the `$env` cons-list** — it cannot reach a
compile-time local. So `handle (state 7) { let f = {fun _ => get}; … }` refuses on both paths: the
inline path has no `$clos`; the GC path has no `state` arm. `throws` is the exception — it is pure
control flow (`try_table`/`throw`), independent of the value rep, so it ports to the GC path verbatim.

## (b) · Unification candidates (priced)

**Candidate 1 — lift the inline fragment onto the `$val`/`$env` rep (RECOMMENDED).** One machine: the
GC path gains effect arms; effects become GC-native.

| kernel form | unified `$val`/`$env` image |
|---|---|
| `state` cell | a `$ref` = `(struct (field (mut (ref null $val))))` — a mutable BOX pushed as an `$env` SLOT. `get` = `struct.get`, `put` = `struct.set` (one-shot in-place, mutation visible through any closure that captured the env). |
| `throws` cap | a `try_table`/`throw` as today; the cap `$env` slot carries the tag identity (a small `$val`-boxed tag, or the tag stays compile-time and only the SLOT existence is runtime). Control flow unchanged. |
| transaction | the TVar heap becomes a GC LIST/array of `$ref` cells (rung-3 note Q1 option B, already named as "the right rep when a TVar holds a closure/ADT"); journal = the pre-image list; rollback drops it. `catch_all_ref`/`throw_ref` unchanged. |
| `custom` clause | the clause body is an ordinary `Comp` lifted to a `$fn`; a one-shot resume is a straight `call_ref` back into the continuation closure (no reification — see (c)). |

Cost: rewrite the four effect arms against `$val`/`$env` (the `Slot` variants collapse into "an `$env`
slot that happens to hold a `$ref`/tag"). The `throws` and rollback CONTROL flow is reused as-is. This
is the "correctness by construction" move — ONE env, so a closure capturing a handler's env just works
(the witness proves it). Bignum/i64 fidelity gap is inherited, unchanged.

**Candidate 2 — keep two reps, convert at handler edges (REJECTED).** Emit inline for the effect
fragment, GC for the closure fragment, and marshal `$val ↔ i64` + `$env ↔ Slot` at every `handle`/
closure boundary. Priced and rejected: a value flowing from a handled region into a captured closure
would need boxing/unboxing at each crossing, and a `state` local can't be marshalled into a captured
`$env` at all without... making it a heap box — i.e. collapsing into Candidate 1 for that cell. Two
reps buy nothing and multiply the seam count; the boundary conversion for the load-bearing case (a
closure over a state cell) IS the Candidate-1 box. Rejected as strictly more machinery for less.

## (c) · Does v1 need the ADR-0059 GC frame-chain? — NO (the load-bearing question)

**No.** Every v1 handler form resumes **one-shot in-place**; none reifies a continuation:

- **throws** — zero-shot: `raise` aborts to the enclosing handler (`try_table`/`throw`), never resumes.
- **state** — ADR-0025 D1 is explicit: "one-shot resume: the continuation is re-entered exactly once,
  in place — there is no continuation value, no multi-shot reification (that stays the ADR-0015
  frontier)." `get`/`put` = read/write a cell, then straight-line continue.
- **transaction** — rung-3 note §Q4: "No general (multi-shot) resumption. v1 transaction is one-shot
  in-place resume (ADR-0025) … nothing in v1's three handler forms reifies."
- **custom (user effects)** — the clause body is a tail-resume: it continues the SAME continuation once
  (a `call_ref`, straight-line), not a captured `cont` value.

The kernel (`Source.eval`) the emitter images never builds a reified `Kᵢ` for any v1 handler; the
frame stack IS the continuation and it is consumed in place. Therefore the unified `$val`/`$env` rep
inherits the never-reify property FOR FREE — the same reason rung 4's `app`/`force`/recursion run on
the plain wasm CALL STACK. **Rung 5 needs no `switch`/`resume`, no reified frame chain.** The ADR-0059
GC-frame-chain slot is the POST-v1 multi-shot fast-path (the ADR-0015 frontier: reify `Kᵢ` as a `cont`
`$val`); it is additive and out of the v1 rung-5 scope. The wall is a rep merge, not a machine build.

## (d) · Minimal witness (a closure + a state handler through a hand-unified path)

`scratch/rung5-unified-closure-state.wat` — `handle (state 7) { let f = {fun _ => get}; ($f ()) + 1 }`:
the state cell is a `$ref` box in the `$env` cons-list; the closure `$fn0` captures that env and reads
the cell via the SAME `$lookup` rung 4 uses. Runs on wasmtime 45 (`-W gc=y,function-references=y`) ⇒
**8** (= `get` 7, +1), matching the kernel. `scratch/rung5-put-through-closure.wat` ⇒ **20**: a `put 20`
`struct.set`s the box, and the captured closure reads 20 — proving the mutable-box rep is load-bearing
(one-shot in-place `put` is visible through the shared env, exactly the resume-in-place semantics).

These are HAND witnesses (the shape proof), not emitter output — the emitter change is the slice map
below. They confirm Candidate 1 is structurally sound on a real engine before the implementation grind.

## The implementation-lane slice map

```
S0  [DONE] $env effect slots   add a $ref (mutable box) $val subtype; the emitter's env becomes uniform
                          $env (rung-4 already has it) — a handler pushes a $ref/tag slot, get/put =
                          struct.get/set. Refute-first: the two hand witnesses (DONE) fix the shape.
S1  [DONE] state on GC path   port the rung-2b `.state` arm to $env: handle (state s₀) mints a $ref box,
                          get/put read/write it; closures capture it for free (the S0 witness).
                          LANDED: `state` example emits emitModuleGC + runs 5 == bang run on wasmtime 45.
S2  [DONE] throws on GC path port rung-2's try_table/throw verbatim (control flow, rep-agnostic); the
                          cap slot carries the tag identity (a compile-time `CapSlot` context threaded
                          alongside the runtime $env). LANDED: `handle` example (raise 7 caught) emits
                          emitModuleGC + runs 7 == bang run; result type is $val not i64. Tag decls
                          `(tag $exnT (param (ref null $val)))` per minted handle.
S3  [DONE] transaction     TVar heap = a $txbox mutable pointer to an $env list of $ref cells (rung-3
                          Q1 option B); newTVar prepends + returns the old length (index), read/write
                          walk to the cell ($txcell) and struct.get/set in place, rollback resets the
                          box to null. catch_all_ref/throw_ref reused. LANDED: stm=70, effect-op-arith=70
                          == bang run on wasmtime 45; the ABORT path (raise inside a txn) verified 42 ==
                          bang run — the explicit rollback (struct.set $txbox null + throw_ref) FIRES.
S4  [DONE] custom effects   clause body lifted to a lam-style $fn capturing (p :: handlerEnv); a custom
                          op call_refs its clause with the op-value ⇒ body env (v :: p :: handlerEnv) =
                          the image of subst p (subst (shift v) clause.2) — one-shot resume, no
                          reification (design (c)). The clause closures live in a $txbox in the cap's
                          ENV slot (env-reachable via $lookup + $clausecell), so a NESTED closure that
                          performs the op works (dst-rounds). LANDED: logger-counting=3, logger-silent=0,
                          handle-custom-{resume=106,tracer=30,nested=210,abort-coexist=42}, dst-rounds-
                          {const=16,lcg=9}, ndet-{sim,replicated,rep}-kv all == bang run on wasmtime 45.
                          NAMED REFUSAL: a cap threaded as a first-class runtime VALUE (vcap passed into
                          a closure as an arg — stage-swap) has no GC $val rep in v1; refused loudly.
S5  proof-grade           extend the wexec≡Source.eval obligation with the $env-slot↔store bijection;
                          per-former, same seam as rungs 1-4 (tested stratum until then).
                          RE-FRAMED (`rung5-s5-proofgrade-refutation.md`): the obligation SPLITS —
                          the effectful wexec≡Source.eval half is ALREADY PROVEN axiom-clean on the
                          proof-carrying backend (compileC→wexec: exec_wexec_sim_ok +
                          compile_forward_sim cover state/throws/txn/custom), re-exported in
                          `Bang/Backend/Rung5ProofGrade.lean`; the $env-slot↔store bijection half is
                          UNSTATEABLE in v1 (emitModuleGC is a Comp→String text emitter with no Lean
                          machine — needs the post-v1 ADR-0059 GC machine, CALCULATED not verified-
                          after per inv#4). emitModuleGC stays differential-tested (inv#1).
```

> **S5 status (2026-07-11): re-framed and landed.** See
> [`rung5-s5-proofgrade-refutation.md`](rung5-s5-proofgrade-refutation.md) for the full split (proven
> half vs unstateable half), the axiom evidence, and the host-IO/`VcapFree` premise boundary.

`S0`–`S2` are the small win (state + throws + closures coexisting); `S3`–`S4` finish the v1 effect set
on one rep. NO frame-chain slice appears — it is post-v1 (multi-shot, ADR-0015). Corpus target: the
effect-using examples (logger/state/txn) join the GC harness once they can also carry closures.

## One-glance status

```
VERDICT       unify onto ONE $val/$env GC rep (Candidate 1); two-reps-with-conversion REJECTED (it
              collapses into Candidate 1 for the load-bearing case, for more seams).
LOAD-BEARING  v1 needs NO GC frame-chain — every v1 handler (throws/state/txn/custom) is ONE-SHOT
              in-place (ADR-0025 D1, rung-3 §Q4); the unified rep inherits rung 4's never-reify.
KEY MERGE     compile-time Slot stack → runtime $env cons-list with effect slots; a state cell = a
              $ref MUTABLE BOX in the env, so a captured closure reads/sees put through $lookup.
WITNESS       closure-over-state ⇒ 8; put-through-closure ⇒ 20 on wasmtime 45 (hand-unified, ==kernel).
SURVIVES      throws (try_table/throw) + rollback (catch_all_ref/throw_ref) are control flow — port
              verbatim, rep-agnostic. Only the VALUE/ENV rep merges.
SLICES        S0 $ref slot · S1 state · S2 throws · S3 txn(GC heap) · S4 custom · S5 proof-grade.
              No frame-chain slice (post-v1, the ADR-0015 multi-shot frontier).
LANDED        S0-S4 DONE (feat-rung5-effects): 46 whole programs → WasmGC → wasmtime == bang run, of
              which 23 are EFFECTFUL (state/stm/throws/logger/custom/dst-rounds/ndet, including the
              ADR-0114 stateful-quota surface witness). The rung-4
              blanket effect-refusal is REPLACED — effectful corpus programs now compile via
              emitModuleGC. Gate = tools/emit-rung5-effects-diff.sh (auto-discovering, both-direction).
NAMED WALLS   a first-class capability (vcap) threaded as a runtime VALUE (passed into a closure as an
              arg — stage-swap) has no GC $val cap rep in v1: refused LOUDLY. Full bignum (i64 wrap,
              inherited rung 4) and non-empty-start Θ (only atomically) stay named refusals. S5 proof-
              grade (wexec≡Source.eval with the $env-slot↔store bijection) = the tested→verified lift.
```
