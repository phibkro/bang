# ADR-0110 · Preserve the Wasm proof-model to concrete-emitter boundary

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Route B preserves an explicit boundary between the project-defined Wasm-oriented abstract machine proved by `compile_forward_sim` and the separately implemented concrete WasmGC/WAT emitter. The product target remains Wasm 3.0, while emitted modules earn differential evidence from real-engine execution rather than inheriting the abstract model's theorem evidence.
- **Amends**: 0016 (narrows the original verified-target claim), 0059 (clarifies the evidence boundary without changing the Wasm 3.0 product target)
- **Depends-on**: 0016 (two-hop architecture), 0035 (forward-simulation proof method), 0059 (Wasm 3.0 product target)
- **See-also**: issue #133 (concrete first-class capability representation), issue #116 (component instantiation and value-transfer measurements), issue #166

- **Date**: 2026-07-16
- **Deciders**: operator
- **Layer**: compiler / verification evidence boundary

## Context

The repository has two different target-facing implementations:

- `Bang/Backend/Wasm.lean` defines a project Wasm-oriented abstract instruction language and executor. Its values and instructions include project source and calculated-machine structures, and some abstract instructions compile residual computations while executing. `Bang.compile_forward_sim` is a checked one-way simulation into this model.
- `Bang/Backend/WasmEmit.lean` independently lowers `Comp` to concrete WasmGC-flavoured WAT. Wasmtime differential batteries compare that output with the source oracle.

There is no theorem or mechanically checked serialization relation from the abstract instruction language to the emitted WAT, and neither the abstract executor nor `compile_forward_sim` is an account of official WebAssembly semantics. Calling the proof-bearing layer a "Formal Wasm 3.0 machine" therefore collapses two representations and transfers theorem evidence across an unproved edge.

ADR-0059 correctly selects Wasm 3.0 as the product target. This amendment narrows only how its verification evidence is interpreted.

## Decision

Choose **Route B: preserve the honest boundary**.

1. Name the proof-bearing layer the **Project Wasm-oriented abstract machine** and its runs **Abstract target execution**.
2. Keep concrete output as a separate **WasmGC / WAT** representation with an independent `Comp`-to-emission edge.
3. Attach theorem evidence only to the source-to-abstract-target simulation. Attach implementation and real-engine differential evidence to the concrete emitter path.
4. State in generated architecture facts and public architecture copy that no proof currently connects the two target layers or connects the abstract model to official WebAssembly semantics.
5. Keep **Wasm 3.0** as the product target name. Product-target language is not evidence that the abstract machine is Wasm 3.0 semantics.

The historical `Wasmfx` namespace may remain as a compatibility name. It does not determine the semantic status of the model.

## Why Route A remains separate

Route A would require a structured concrete target IR shared by the proof model and renderer, or an explicit relation between them, followed by a checked lowering/serialization correspondence. That is a distinct compiler-verification project, not a terminology patch.

Its scope also moves with unfinished concrete-target work. Issue #133 extends the emitter's value representation for first-class capabilities. Issue #116 measures component instantiation and cross-boundary value-transfer costs that may shape later component/ABI choices. A correspondence design made before those seams settle could prove the wrong concrete interface. Those issues do not themselves supply the missing proof; they remain inputs to any separately planned Route A.

Real-engine differential tests remain valuable even if Route A is later completed because they independently exercise the renderer, engine feature configuration, and runtime behaviour.

## Rejected alternatives

- **Treat similarly named instructions as a correspondence** — structural resemblance is not a semantic or serialization relation.
- **Describe the abstract executor as formal Wasm 3.0** — its project values, residual source computations, and executor are not official Wasm semantics.
- **Let the concrete emitter inherit `compile_forward_sim` evidence** — the theorem's conclusion mentions `Wasmfx.run (compileC c)`, not emitted WAT or Wasmtime.
- **Start Route A inside this closure** — it is a substantially larger design and proof project whose concrete interface is still affected by #133 and #116.
- **Remove Wasm 3.0 product language** — that would reverse ADR-0059's target decision rather than correct the evidence boundary.

## Consequences

- Architecture facts expose two differently named target layers and two evidence paths.
- Proof dashboards and public documentation can continue to report `compile_forward_sim` as strong within its stated abstract-model scope.
- Concrete Wasm claims remain implementation- and differential-evidence claims until an explicit correspondence is built.
- Future Route A work must add a new relation and evidence edge; it cannot silently strengthen the existing abstract-target edge.

## Revisit if

- a shared structured target IR is adopted by both the proof model and renderer;
- a checked lowering/serialization correspondence reaches the concrete emitted module;
- an official Wasm semantics is connected to the concrete target; or
- the concrete emitter is replaced by a renderer whose input is already the proved target language.
