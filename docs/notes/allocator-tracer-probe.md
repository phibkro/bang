<!-- note-status: archival -->
<!-- describes: Bang/Frontend/TypeCheck.lean Bang/Frontend/Surface.lean Bang/Core/Typing.lean Bang/Core/Semantics/Dispatch.lean Bang/Core/Semantics/Eval.lean @ 09de1b001f9f85beb7778205722a593e218aa5b0 -->
# Allocator tracer S0 — banked at the computed-update boundary

> Systems-wedge reconnaissance on 2026-07-19. This is a machine-backed stop result, not an
> allocator implementation. Run it with `just test-allocator-tracer-probe`; the completed work unit
> is `paths/archive/PATH-allocator-tracer-probe.md`.

## Verdict

The handler parameter can carry the intended modeled arena `(nextHandle, liveHandles)`, and an
effect-operation result can be bound by `use [1]`. The first honest allocator transition cannot be
expressed under the accepted ADR-0114 update envelope: direct pairs of values pass, but a literal
outer pair whose components are pure computations over `param` fails, as does a let-wrapped
computed pair. This is not a spelling accident.

The probe is therefore banked before an `Alloc` product journey. It does not fake private state by
putting it in client arguments, assign stable allocator misuse codes that cannot yet execute, or
change checker/kernel semantics. The retained generic refusal is part of the finding.

Two independent consumers now name one shared future door: **effect-free computed updating-clause
bodies that evaluate to one atomic `(resumeValue, nextParam)` pair**. The allocator tracer and the
CALM max-join program are the required future acceptance witnesses. That increment is ruled as a
follow-on, not implemented here.

## Computed-update bisect

| updating body | check result | execution evidence |
|---|---|---|
| direct value pair `(bytes, param)` | PASS | `value-pair-update.bang` returns `700` on `env`, `oracle`, `compiled`, and concrete Wasmtime |
| literal pair; both components are pure `let` projections/computations over `param` | FAIL, generic `code:"type"`, `explainCode:null` | exact JSON in `computed-components-refused.check.json`; no execution route |
| literal pair; both components are pure typed `match` expressions over `param` | FAIL, same generic diagnostic | exact JSON in `match-components-refused.check.json`; no execution route |
| `let` destructure followed by computed pair formation | FAIL, same generic diagnostic | exact JSON in `computed-update-refused.check.json`; no execution route |

The matrix falsifies the “literal outer pair is enough” hypothesis. `let` and `match` are pure here,
but they are computations rather than `Val` constructors.

## Rejecting layer and ADR-0114 attribution

The immediate rejection is the surface checker:

- `Bang/Frontend/TypeCheck.lean:1094-1100` defines `isValueSurf`; a pair is a value only when both
  components are values, while `let` and `match` are not.
- `Bang/Frontend/TypeCheck.lean:1710-1721` requires an updating body to be a literal pair with two
  `isValueSurf` components; line 1716 emits the retained generic diagnostic.
- `Bang/Frontend/Surface.lean:821-824` would otherwise lower an updating body through general
  `lowerC`; lowering is not the authority that rejects these fixtures.

That surface check is not narrower than the accepted kernel ruling. ADR-0114 fixes the first slice
to `ret (pair resumeValue nextParam)` at
`docs/decisions/0114-stateful-custom-clauses-use-explicit-update-keys.md:57-60` and explicitly leaves
computed/effectful update bodies separate at lines 84-85 and 110-114. The kernel mirrors it:

- `Bang/Core/Typing.lean:378-383` admits only
  `Comp.ret (.pair resume next)` with both components kernel values.
- `Bang/Core/Semantics/Dispatch.lean:179-189` installs a next parameter only after matching that
  exact ret-pair shape; any other untyped shape fails loud.

So widening only `isValueSurf` or lowering would create a checker/kernel disagreement. The ruled
future door needs an explicit computation/interception design across the typed kernel and every
machine, while preserving atomic install-before-resume.

## Static-versus-dynamic gap table

| question | static fact | dynamic fact | machine-backed evidence |
|---|---|---|---|
| Can the parameter encode bump plus live set? | `(Int * Live)` with recursive `Live` checks. | Explicit audit of `(4, Cell(3, Empty))` renders `403` everywhere it runs. | `structured-param.bang`; exact check JSON; `env`/`oracle`/`compiled`/Wasmtime gate |
| Is the effect contract and law queryable? | `Arena` declares `audit` and `audit_stable`. | `bang query contract` reports `subjectValid:true`, `typeChecked:true`, the operation, and law. | exact `structured-param.contract.json` compared by the gate |
| Is a direct ADR-0114 update envelope accepted? | Both pair components are values. | Result is `700` on all three engines and Wasmtime. | `value-pair-update.bang`; exact check JSON and differential gate |
| Can pure component computations derive the next private state? | No; surface and kernel both require values. | All three spellings stop before execution with the same generic refusal. | three refusal fixtures and exact check JSON matrix above |
| Can `use [1]` bind an operation result? | One use checks; duplicate and forgotten uses are B018. | Accepted pole returns `7` on all three engines and Wasmtime. | `use-one-result.bang`, duplicate/forgotten refusal fixtures, exact JSON |
| Is there an at-pop audit/finalizer clause? | No: `HClauses` has only `nil`, `cons`, and `consUpdating` at `Bang/Frontend/Surface.lean:353-356`. | Handler return discards the frame and parameter unchanged at `Bang/Core/Semantics/Eval.lean:104`. | source-shape assertions in the gate |
| Can double-free, unknown-free, or leak/audit be honest product poles now? | No private membership/update transition can be computed. | No such fixture is claimed runnable. | computed-update refusal plus finalizer exclusion; gate prevents authority-file diffs |

All runtime wording above is tested-stratum only. No performance or external-validation claim is
made.

## Separately priced follow-on doors

1. **Shared effect-free computed update envelope — ruled next increment.** It must evaluate a pure
   clause computation to one atomic resume/next-param pair, then install before resumption. Its
   acceptance needs surface/checker/lowering, typed Core, semantics/proofs, all execution engines,
   and concrete-Wasm agreement. The allocator happy/double-free/unknown-free/audit poles and CALM
   max-join are the two required consumers. It does not include effectful clauses, finalizers, a full
   D5 continuation port, grade polymorphism, type-class machinery, or consumer special cases.
2. **Stable diagnostic for the current refusal — frontend-sized but sequenced after semantics.** The
   committed generic diagnostic is intentionally unchanged here. A future code must be fixture
   first and must describe the finally ruled boundary, rather than fossilize this temporary wall.
3. **At-pop finalizer — independent semantic expansion, excluded.** It would change the identity
   return behavior and fan out through every machine/proof/backend. The allocator follow-on uses an
   explicit `audit` operation; it receives no automatic leak-at-pop claim.
4. **General/effectful clause bodies — excluded larger door.** Full D5, first-class continuation,
   answer-grade polymorphism, and clause effects remain separate work and are not justified by
   either north-star witness.

## Scope and residual risk

There are no bytes, sizes, alignment, layout, reclamation, performance, ownership, regions,
lifetimes, concurrency, real memory, new kernel primitive, Wasm emitter edit, or external-validation
credit here. The principal residual risk is that the shared pure-computation design may still expose
an answer-grade or atomicity obligation not visible in surface probes. Until that door lands, a real
allocator tracer with stable double-free, unknown-free, and explicit leak/audit codes remains
blocked; `use [1]` alone is not handle lifetime enforcement.
