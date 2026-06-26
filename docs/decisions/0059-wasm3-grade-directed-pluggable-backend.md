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
  checked** (the `CtxRel`/`SegRel` relation, Lean 4.31, axiom-clean), the same identity-keyed shape that
  ADR-0058 adopts to dissolve the `CrelK` Canonical wall. **CAVEAT (load-bearing):** the grade-*directed*
  routing is banked as the backend SHAPE, but **deriving** abort/tail/general *from the grades* requires
  grading the **resumption** multiplicity, which our type system does NOT currently do (the resumption is
  operational, not source-graded; ADR-0025's closed-focus dissolves the state-grade the *opposite* way). So
  the grade-derivation is an **open extension (its own follow-up ADR), NOT load-bearing**; until it lands the
  routing falls back to annotation/analysis (Lexa's own mechanism).
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

## The open extension (flagged, NOT load-bearing) — grade-derived dispatch

The routing *shape* (abort/tail/general) is banked. **Deriving** the disposition *from the grades* is NOT a
current result: our `HasCTy` grades track value/computation/capability/`let`-continuation multiplicity, but
**not the resumption** (the captured continuation is operational, not a source-graded binding), and ADR-0025
deliberately uses the **closed focus** to dissolve the state-grade tension rather than track it — the
*opposite* move from Lexa's multiplicity annotation. So:

- The backend does **not** depend on grade-derivation — only the "strictly ahead of Lexa" framing does.
- Making it real is a **separate follow-up ADR**: extend graded-CBPV to grade the resumption (0× / 1×-tail /
  1×-arbitrary), deriving abort/tail/general statically, and reconcile with ADR-0025's closed-focus (they
  pull opposite ways). This is a genuine, unbuilt research contribution — and it is where the "ahead of
  Lexa" claim would be *earned* rather than asserted.
- Until it lands, the routing uses annotation/analysis (Lexa's own mechanism); the backend is unaffected.

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
