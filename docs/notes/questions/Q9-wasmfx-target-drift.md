---
type: design-question
title: "WasmFX target drift: frozen OOPSLA'23 syntax vs Phase-3 standard"
description: "the verified compiler TARGET drifted (OOPSLA'23 → Phase-3); pin-to-engine at ◊5, not the paper"
status: open
area: tooling
ties: ["ADR-0016", "ADR-0035"]
see-also: ["references/README.md"]
---
**Question**: ADR-0016 freezes the WasmFX *abstract syntax* (from the OOPSLA'23
paper) as the verified compiler-output target. The WebAssembly stack-switching
proposal has since advanced to **Phase 3**, and its instruction set has diverged.
Is the frozen target still the right thing to compile to and verify against?

**Why it matters**: invariant #8 — "the WasmFX backend is the verified compiler
target." If `compile_forward_sim` proves correctness against an abstract syntax
the real engine no longer implements, the proof is green against a fiction. A
frozen, drifted target is the worst case: it *looks* verified.

**Detail** (confirmed by the 2026-06-21 SOTA sweep — see `references/README.md`
→ Integration findings; sources in `refs.bib`):

```
Frozen (OOPSLA'23)            Phase-3 standard (live)        Status
──────────────────            ──────────────────────        ──────
cont.new / resume / suspend   + switch                      NEW primitive — symmetric
  + cont.bind                                                peer-to-peer switching,
                                                             not sugar over suspend/resume
resume_throw                  + resume_throw_ref             NEW
cont (top type)               + nocont (bottom heap type)    NEW
handlers: (tag $e $h) pairs   handlers: (on $tag $label)     RENAMED — old codegen is wrong
                                clauses on `resume`
```

The frozen target is now a **strict subset** of the standard. Per the SpecTec
experience report (WAW 2025), *semantics* (not just surface syntax) were adjusted
during standardization.

**Options**:
1. **Pin-to-engine, defer reconciliation to ◊5** *(recommended)*. The target
   doesn't bind until ◊5 (Compiler v0); we're at ◊2. Do NOT chase a Phase-3
   (still-mutable) proposal now. When ◊5 begins: pin a specific commit of
   `WebAssembly/stack-switching` + a Wasmtime version, and gate
   `compile_forward_sim` on differential testing against that engine
   (`wasm_stack_switching`, x86-64 Linux) rather than against the paper.
2. Re-freeze the target now against the current Explainer.md. Premature: the
   proposal will move again before Phase 4; we'd just re-drift.
3. Adopt a mechanized oracle. WasmFXCert + Iris-WasmFX (PLDI'26, Rocq) is a
   mechanized type-soundness model of WasmFX — aligns with invariant #1
   ("proof rides the reference"). Caveat: Rocq, not Lean; and verify whether it
   models the new `switch`/`nocont` or only the `suspend`/`resume` core.

**Recommended**: (1) now + (3) as the reference to ride at ◊5. Record here; do
NOT rewrite ADR-0016 (the two-hop *architecture* is unchanged — only the target's
concrete syntax drifted, which is a ◊5 reconciliation, not an architecture
reversal).

**Blocked on**: nothing now. This is a ◊5 obligation, surfaced early.

> **Note (2026-06-23):** the ◊5 *proof method* is now settled — **ADR-0035**: `compile_forward_sim`
> uses AsmFX-style one-directional annotated simulation (not the biorthogonal LR, which stays ◊4-only).
> Q9 remains open on the *target* alone: AsmFX is its own abstract ISA, not WasmFX, so "pin the engine,
> not the paper" (options 1+3) is unchanged.
>
> **Cross-prover clarification (2026-06-23 recon):** option (3) "ride the mechanized oracle" CANNOT mean
> *import* — WasmFXCert / Iris-WasmFX are **Rocq** (`logsem/iris-wasmfx`, builds on WasmCert; confirmed
> models `switch` via `switch.addr` in `theories/`), and **no Lean-4 WasmFX semantics exists** (checked:
> T-Brick/lean-wasm, cajal/talos, Utrecht LeanWasm all model plain Wasm). So (3) = **transcribe** the Rocq
> operational semantics into a Lean `Wasmfx.run` (a few hundred lines for the trivial fragment, comparable
> to `Source.eval`), with the Rocq artifact as the faithful line-by-line reference (invariant #1 satisfied
> by transcription, not import). NEW SEAM this introduces — the Lean↔Rocq transcription — earns confidence
> from BOTH a line-by-line Rocq cross-check AND the real-engine differential test (a Lean-only-green
> `compile_forward_sim` would be "green against a fiction", relocated from syntax-drift to run-level).
> Engine status: stack-switching is Phase 3 (mutable); **Wasm 3.0 (Sept 2025) did NOT include it**;
> Wasmtime #10248 has core support behind the flag but x64-only, no `resume_throw`, "all test cases fail"
> — confirm a usable version by hands-on build at ◊5 start.
>
> **ENGINE PROBE RESOLVED (◊5, 2026-06-24):** stack-switching now RUNS on a RELEASED Wasmtime — no
> dev-commit pin needed. `wasmtime 44.0.1` (nixpkgs) executes a suspend/resume generator `.wat` on
> **x86_64 Linux**, deterministically returning the expected value. Required flag combination (the
> "conflated features" the brief flagged):
> `-W stack-switching=y,function-references=y,gc=y,exceptions=y`
> plus `(elem declare func $gen)` for the `ref.func`. The working shape (matches the ◊5
> markH/opH/unmarkH lowering): `(type $ct (cont $ft))` · `(tag $yield (param i32))` · `(cont.new $ct
> (ref.func …))` · `(resume $ct (on $yield $label) …)` · `(suspend $yield)` — the CURRENT Explainer
> form, NOT the OOPSLA'23 `(tag $e $h)`. The tracer/generator path (suspend/resume) needs NEITHER
> `resume_throw` NOR exceptions-as-control (exceptions is enabled only because the tag machinery shares
> it). ⟹ leg #2 (the differential-test oracle) is VIABLE: `compile_forward_sim` can gate on BOTH the
> Rocq cross-check (leg #1) AND a real wasmtime diff-test, not Lean-only-green. Probe `.wat` +
> invocation reproducible; not committed to the repo (a scratch artifact).

**Revisit signal**: starting ◊5 compiler/backend work; OR the stack-switching
proposal reaching Phase 4 (becomes stable — re-freeze then); OR a decision to
adopt WasmFXCert as the backend oracle.
