# 0037 — Abstract model fights for correctness; implementation fights for performance under contract (+ the shared-nothing concurrency invariant)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Abstract model fights for correctness; implementation for performance under contract; the concurrency runtime is shared-nothing.
- **Depends-on**: 0016, 0035, 0030, 0026, 0028

- **Layer:** C (architecture / methodology; constrains the semantics-preservation contract)
- **Status:** Accepted (forward-looking invariant, pre-committed before ◊5/concurrency code exists)
- **Depends on:** 0016 (two-hop), 0035 (LR=correctness / sim=compilation), 0030 (STM concurrency deferred), 0026/0028 (the verified-core/tested-superset seam), invariant #7

## Context

The actors / multikernel direction (`docs/notes/design-space-map.md` → concurrency section) needs a
runtime concurrency model. The ◊5 recon established that *shared-nothing* keeps the forward-simulation
proof method (ADR-0035) valid, whereas shared mutable state across instances forces Iris concurrent
separation logic. In approving the concrete invariant, the operator named the **governing principle**
this ADR records.

## The principle

> **The abstract model fights for correctness. The implementation model fights for performance,
> upholding the contract with the language semantics. Constraints prove performance by reducing the
> invariants the implementation must uphold at runtime.**

Unpacked:

1. **Two layers, two objectives, one contract.** The abstract/spec layer (graded-CBPV reference, the
   LR, the equational theory) maximises *correctness* — strong invariants, provability, clarity;
   speed is not its concern. The implementation/backend layer (CalcVM → WasmFX) maximises
   *performance* — but is **bound by a contract**: observable behaviour must equal the abstract
   semantics (contextual equivalence). `compile_forward_sim` is the contract instrument (ADR-0035);
   the LR is the equivalence the contract preserves.
2. **Constraints are generative** (SOUL; No Free Lunch). A static invariant *upheld by the abstract
   model* **removes a runtime obligation** from the implementation — and that removal is what *licenses*
   the fast path. Constraints don't make code fast by themselves; they make a fast implementation
   **sound** (they delete the obligation that would otherwise force the slow path). More
   guaranteed-by-construction ⟹ less to check / synchronise at runtime.

**bang already runs on this principle** — it is being *named*, not invented:

```
constraint (abstract model)        obligation it REMOVES (implementation)        instrument
──────────────────────────────────────────────────────────────────────────────────────────
QTT grade 0                        emits NO code for the binder                  zero_grade_no_code
QTT grade 1 (linear, no aliasing)  in-place update / no GC for that value sound  (grade calculus)
effect row (static handler set)    no dynamic handler dispatch — specialise      no_accidental_handling
LR / contextual equivalence        the backend may rewrite freely below it       compile_forward_sim
shared-nothing (this ADR)          no cache-coherence traffic, no locking,        forward-sim composes
                                   AND no Iris                                    (ADR-0035)
```

## Decision

**The concurrency runtime model is shared-nothing.** Actors/cores are separate wasm instances
(separate linear memories by construction); coordination is **by-copy message-passing**; a "central
manager" is itself a message-passing / replicated actor, **never a shared-memory coordinator**
(Barrelfish's lesson). The load-bearing invariant:

> **messages by-copy; NO cross-instance shared TVars; NO shared global heap baked into the runtime
> (`Wasmfx.run` / the `⊨` modelling relation).**

Pre-committed **now**, before ◊5 runtime code exists, so the forward-sim method stays valid all the way
to multicore. The entire concurrency rework risk then collapses to one *deliberate* decision (Q21):
introducing cross-instance shared mutable state ⟺ opting into Iris.

## Why (the principle applied)

The shared-nothing constraint is **doubly generative** — the correctness enabler and the performance
enabler are the *same* constraint:
- **Verifiability:** each instance is a sequential program ⟹ per-instance forward-sim composes ⟹ no
  concurrent separation logic.
- **Performance:** no shared mutable state ⟹ no cache-coherence traffic, no lock contention, no SPOF.

A textbook instance of the principle: the invariant the abstract model upholds (no sharing) is exactly
the obligation the implementation no longer has to pay (synchronisation).

## Rejected alternatives

1. **Shared-memory / shared-TVar actors.** Why not: reintroduces concurrent mutable state → Iris
   (heavy proof) + cache-coherence/locking cost + bottleneck/SPOF. Violates the principle — the
   implementation would carry a runtime obligation the abstract model could have removed.
2. **Defer the invariant until concurrency is built.** Why not: a missing invariant is
   reversible-by-accident — ◊5+ runtime code could bake in a shared heap and silently invalidate the
   forward-sim method. Pre-committing makes the bad state unrepresentable (the generate > test >
   convention ladder, SOUL), at zero present cost.

## Revisit if

- A workload genuinely requires cross-instance shared mutable state → opt into Iris / iris-wasmfx
  **deliberately**, with its own ADR (don't let it leak in).
- **ELEVATED (2026-06-23):** the principle is now a stated invariant in `ROADMAP.md` → "The vertical
  principle — correctness above, performance below". This ADR remains the full treatment + the
  shared-nothing concurrency instance; the ROADMAP states the principle for orientation.
