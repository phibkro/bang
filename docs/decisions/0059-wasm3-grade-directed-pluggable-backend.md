# 0059 — Compile to Wasm 3.0 with a grade-directed pluggable backend (refines ADR-0016's WasmFX-primary target)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: **Stack switching did NOT land in Wasm 3.0** (Sept 2025 standardized WasmGC, exception
  handling, tail calls, memory64, SIMD; typed continuations / WasmFX remain a separate in-flight proposal,
  shipping only on the `wasmfxtime` fork — not in stock V8/SpiderMonkey/Wasmtime). So ADR-0016's commitment
  to **WasmFX as the primary target** would mean leaving stock engines and putting an **opaque
  stack-switching primitive inside the TCB**. This ADR **refines** that target (the two-hop *architecture*
  is unchanged): compile to **Wasm 3.0** with a **grade-directed, pluggable backend**. The effect row gives
  a free 2-coloring — **pure** (empty row) → native Wasm; **effectful** → routed by resumption disposition:
  **abort** → Wasm exceptions (`throw`/`try_table`, zero runtime), **tail** → direct in-place call,
  **general/multishot** → a **GC-frame-chain runtime** (managed `struct` frames + a tail-call trampoline —
  the only hand-built part). Only `general` is the swappable slot: GC-frame-chain now, WasmFX `switch` as a
  fast-path once standardized + shipped. The decisive reason for *us* is verification: a GC-frame-chain
  runtime is **our** abstract machine, verified end-to-end with **no opaque primitive in the TCB**
  (invariant #1), and its simulation relation is the easy, append-only, arithmetic-free kind — **machine-
  checked per-step** (the `CtxRel`/`SegRel` relation, Lean 4.31, axiom-clean; the *cross-step* partition is
  unbuilt — see the open sub-clause), the same identity-keyed shape that ADR-0058 adopts to dissolve the
  `CrelK` Canonical wall. **SCOPE (the load-bearing sharpening):** v1's three handler forms (`state`,
  `throws`, `transaction` — machine-confirmed exhaustive, Core.lean:120) are ALL abort or tail-resumptive
  (ADR-0025, one-shot-in-place, no reification), so **v1's backend is just `throws`→exception +
  `state`/`transaction`→tail-call — no GC-machine, no reified resumption; closed-focus IS the v1 answer.**
  The GC-frame general leg + grade-derived dispatch is the **post-v1 ADR-0015 multishot frontier**: the
  GC-machine proofs are the *frontier's* reference proof, NOT v1's backend, and v1 ships without any of it.
  Grading the resumption (which `HasCTy` doesn't do) is what *post-v1* needs to derive its annotation,
  composing with closed-focus at the v1/post-v1 boundary (a partition, not a conflict). Detail + the open
  cross-step sub-clause: §"The v1/post-v1 boundary".
- **Refines**: 0016
- **Depends-on**: 0016, 0058, 0001, 0052
- **See-also**: 0044, 0015, 0025, 0030

## Status

Accepted (2026-06-26), during the Lexa / Wasm-3.0 design session. The two-hop architecture (ADR-0016:
source → graded-CBPV `eval` → CalcVM → target) stands; this ADR revises only the **target** of the second
hop and how dispatch lowers. Implementation is **inc-6** (CalcVM route-B + Compile re-key).

## Context

- **Wasm 3.0 reality (Sept 2025):** landed = WasmGC (struct/array, typed refs), exception handling (tags,
  `throw`/`try_table`), tail calls (`return_call`), memory64, SIMD. **NOT landed** = typed continuations /
  stack switching (WasmFX) — a separate proposal, stock-engine-absent, fork-only. Safari also still lacks
  JSPI (the narrow stack-switching path that partially shipped elsewhere). So "lean on WasmFX" today means
  abandoning stock engines.
- **What 3.0 hands us for handlers:** GC ⇒ frames/continuations as managed structs (no Boehm GC, which Lexa
  links); tail calls ⇒ a constant-native-stack trampoline; exceptions ⇒ abort for free. The *only* missing
  capability is reifying a live native stack for a *resumable* handler — which is the one thing we build.
- **The grade is the partition.** CBPV separates values from computations; the effect row (`Finset Label`,
  ADR-0001/0018) certifies which computations are pure. A generic CPS backend can't 2-color because it
  doesn't *know* what's pure; ours does. Most code is the green (native) path; only genuine
  general/multishot handlers reach the hand-built runtime.
- **The verification fact that decides it for us.** Targeting WasmFX puts the engine's `switch` semantics in
  the trusted base — and the Iris-WasmFX mechanization found a real bug in the proposal's suspend
  translation, so "trust the engine's stack-switch" is not free. A GC-frame-chain runtime is *our* abstract
  machine; the source→(GC-machine) simulation is specified and verified with no opaque primitive in the TCB.
  That is invariant #1 ("proof rides the reference; never ship an execution path with no oracle behind it")
  applied to the backend.
- **The relation is machine-checked easy.** The GC-machine simulation (`CtxRel`/`SegRel`, Lean 4.31,
  standalone, axiom-clean — zero `sorry`, no `sorryAx`) keys a handler instance by a **bare reference**, so
  HANDLE preserves the relation by **append-only `Ξ`** (`ctxRel_mono`, axiom-free) and RESUME by
  **read-disjointness** (`h ∉ rs`, not arithmetic; `resume_preserves`, `propext`-only). Lexa's
  runtime-dependent `Ξ` fragment for tail/abort handlers — the part its pencil proof called "largely
  mechanical" — has **no site to live** here: GC references are stable, never relocated, so there are no
  interior offsets and no `next^m`. This is the same identity-keyed shape ADR-0058 adopts for `CrelK`.

## Decision

Compile to **Wasm 3.0**, lowering the IR control core (`handle`/`raise`/`resume`) **grade-directed**:

```
  pure (empty row)        → native Wasm (direct calls, native stack, engine codegen)
  effectful, abort (0×)   → Wasm exception (throw / try_table)            [engine-independent]
  effectful, tail (1× tl) → direct call in place                          [engine-independent]
  effectful, general (1×) → GC-frame-chain runtime + tail-call trampoline [pluggable]
```

Abort and tail are backend-independent (any 3.0 engine, forever). **Only `general` is the swappable slot** —
GC-frame-chain runtime now; WasmFX `switch`/`resume` as a fast-path once standardized and shipped. The
`compile_forward_sim` hop (ADR-0016's LR) targets the **GC-frame abstract machine** (managed `struct` frames
linked by `.parent`, handler identity = the struct reference, raise/resume = re-point a `.parent` field) —
for which the simulation relation is machine-checked easy (above).

## Consequences

- **ADR-0016's "WasmFX is the primary compilation target" is REVISED** → Wasm 3.0 is primary; WasmFX is a
  post-standardization fast-path for the `general` case only. The two-hop architecture and the calculation /
  LR split are unchanged.
- **inc-6 re-targets the GC-machine** (CalcVM route-B + Compile, task #15). The machine-checked
  `CtxRel`/`SegRel` is the reference for both the codegen *and* (via ADR-0058) the `CrelK` re-key — one
  identity-keyed relation serves both.
- **Smaller TCB.** Trusted = an idealized GC heap (reference stability + reachability), not an opaque
  `switch`. A precise GC model adds reachability obligations — strictly smaller than `next`-arithmetic
  survival across `sfree`.
- **Multishot is easier than Lexa**, and connects to **ADR-0015** (the paused multi-shot/non-tail frontier):
  immutable GC frame-chains share freely (Effekt-style, segment-copy, no pointer-rewrite hunt). Lexa's
  single-shot-by-default came *from* its mutable stacks; GC references dissolve it.
- **The honest cost.** General resumable handlers lose native-stack speed (frame alloc + trampoline bounce
  per effectful call) — the Effekt cost, now *contained* by the grade rather than whole-program. The engine
  can't optimize across reified frames the way Lexa got LLVM to optimize across C calls.

## The v1/post-v1 boundary — where the open extension actually lives

The routing *shape* (abort/tail/general) is banked, and its scope is sharper than "grade-derivation flagged":
it falls on a line the project already drew (ADR-0025 + ADR-0015). **`Handler` is exactly `state | throws |
transaction`** (machine-confirmed exhaustive, Core.lean:120; a fourth is a 6th-primitive ADR, invariant #5),
and **all three are abort or tail-resumptive** (ADR-0025: `throws` discards the continuation = abort;
`state`/`transaction` resume *one-shot in-place* — **no continuation value, no reification**). So:

- **v1's backend is the easy, engine-independent half:** `throws → exception`, `state`/`transaction →
  tail-call. **Nothing in v1 reifies a resumption**, so v1 needs no GC-frame-chain runtime, no `Resump`, no
  capture trampoline. **closed-focus (ADR-0025) *is* the v1 answer** — and the better one (grade `[]`, copy
  free, nothing to discharge), not a detour. v1 ships on stock 3.0 without the hand-built runtime.
- **The GC-frame general leg is the post-v1 ADR-0015 multishot frontier.** The machine-checked relation
  (`CtxRel`/`SegRel`/`resume_preserves`/`raise_establishes`) verifies *that* leg — it reifies a `Resump`,
  which no v1 handler does. So those proofs are **the frontier's reference proof, NOT v1's backend
  correctness** (v1's is the easy half, which needs no machine to verify because nothing reifies). Their
  value is "de-risks the frontier," not "unblocks the ship."
- **Grade-derived dispatch (task #35) is scoped to post-v1 (ADR-0015), not "the grade system."** It is what
  the post-v1 multishot leg would need to *derive* its annotation, and it **composes with closed-focus at the
  v1/post-v1 boundary** — a partition, **not a conflict**. (Our `HasCTy` grades track value/computation/
  capability/`let`-continuation multiplicity but not the resumption; closed-focus covers the v1 cases, so
  the resumption-grade is only needed where a resumption is reified, i.e. post-v1.) Where "ahead of Lexa"
  gets *earned*.

The convergence worth trusting (**nobody steered it**): three independent things land on this same line —
ADR-0025 drew it (closed-focus, 2026-06-22); the GC-machine proof lives entirely on the post-v1 side
(everything verified reifies a resumption); and the `Handler`-inductive enumeration confirms v1 has nothing
that crosses it. Design, proof, code — three arrivals at one boundary.

**Open sub-clause — the post-v1 general leg's verification status (NOT yet "verified", full stop).** The
GC-machine relation is machine-checked axiom-clean for HANDLE (append-only `Ξ`) and RESUME (read-disjointness)
**at each step**, but `resume_preserves` *assumes* its disjointness and `raise_establishes` discharges it
**only at the raise instant**. The **cross-step partition** (the resumption store modelled, the single-shot
core stated, `h ∉ active` preserved across HANDLE/LEAVE/RESUME) is **unbuilt — explicitly not predicted
membership-clean**. So the post-v1 general leg is **verified-as-designed (per-step, axiom-clean), modulo the
cross-step invariant**, to be resolved (clean-or-cracks) by the store-preservation lemma. This is a *post-v1
cleanliness* status, not a v1 gate.

> **This sub-clause is OPEN — tracked by task #36 (the cross-step partition / store-preservation).** It
> resolves to PROVEN only when that lemma lands membership-clean (or to an honest crack — a post-v1 multishot
> finding, v1 unaffected). **Do not cite the general leg as "verified" full stop until then** — "machine-
> checked easy" is *per-step* (HANDLE append-only, RESUME read-disjointness); the cross-step partition is the
> unbuilt half, and this hedge is on the survey/prose rung until task #36 puts a build behind it (the durable
> form: `gc_sim.lean` ported into the build with the cross-step lemma as a tracked sorry, then closed).

## Alternatives considered (rejected)

- **WasmFX as primary now (keep ADR-0016 as written).** Leaves stock engines (fork-only); puts an opaque
  `switch` in the TCB (Iris-WasmFX found a real suspend-translation bug); the proof inherits Lexa's
  segmentation / interior-offset difficulty. Rejected for a verification-first project.
- **Whole-program CPS (Effekt's slow path).** CPS everything, pay everywhere — the O(n²) "costly tick". Does
  not exploit the grades' 2-coloring. Rejected.
- **Contiguous array stacklets (boxed `{stack, offset}`) for the general case.** Re-imports the `next^m`
  offset problem *inside* a struct field (stable ref, runtime-offset content). The linked-frame
  representation avoids it; since the speed-sensitive handlers already left via the grade, take the clean
  representation. (Defer boxed offsets to a handler whose grade statically bounds its frame count.)
