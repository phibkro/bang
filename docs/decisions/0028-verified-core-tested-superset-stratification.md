# ADR-0028 — Verified core + tested superset: the stratification principle (tooling · language · the meta-circular evaluator)

- **Status**: Accepted
- **Layer**: K+C (tooling division + the language's total/partial stratification)
- **Depends on**: 0026 (the correctness ladder), 0027 (System F is the total typed core), 0002 (Lean), Q16
- **Date**: 2026-06-23

## Context

Two questions converged on one answer:

1. **Tooling**: given where bang is headed (a verified multi-paradigm *systems* language → the xv6 golden
   test), is the tech stack right? Do the kernel, abstract machine, and compiler share tooling?
2. **The meta-circular wall**: a strongly-normalizing total language (System F, STLC, Gallina) cannot host
   a *total* self-interpreter for a Turing-complete object language — interpreting a diverging program would
   force the interpreter to diverge, contradicting totality. (Brown & Palsberg, POPL 2016, built a
   type-preserving *self-recognizer* for F-ω, surprising the folklore — but that is recognition, not
   Turing-complete interpretation of diverging programs; the practical wall stands.) So how does bang —
   whose verifiable ambition is System F (ADR-0027) — host an interpreter, a scheduler, an OS loop?

Both are the same question: **what is verified, what is merely tested, and where is the seam?**

## Decision

**bang stratifies into a VERIFIED CORE and a TESTED SUPERSET, separated by an explicit, type-visible seam.**
This is the ADR-0026 correctness ladder seen structurally, and it manifests at three levels:

```
level         verified core               tested superset             the seam
──────────────────────────────────────────────────────────────────────────────────────
correctness   verified rung (proof)       tested / unsafe rungs       ADR-0026 ladder
tooling       Lean (kernel·CalcVM·        surface · runtime,          typed AST
              compiler·LR)                checked by differential test
language      total fragment              Div fragment                the EFFECT ROW
              (⊥-row, terminating,        (fuel-bounded, partial,     (Div ∈ row = descent)
               System-F-typed)            Turing-complete)
```

**Tooling.** The verified spine is **necessarily one proof system** — the `compile_forward_sim` / LR proof
*relates* the abstract machine (CalcVM) to the compiler output, and a cross-tool relation is unprovable. So
kernel + CalcVM + compiler + LR are all **Lean 4 + Mathlib** (ADR-0002; correct for metatheory). The
**surface** is the only divisible layer: **now all-Lean** (the surface→`Comp` lowering is *provable*,
single-AST, no serialization seam; Lean's heaviness doesn't bite at toy scale and LSP/CLI polish is a v1
non-goal); **post-v1, extract it to a fast language** (Rust/OCaml) behind the typed-AST seam, **differential-
tested against the Lean oracle** (the descent verified→tested, explicit). The **runtime** is external (a
WasmFX engine — Wasmtime/wasm3), checked by differential testing; a verified-wasm reference (WasmFXCert /
Iris-WasmFX, Rocq) is a candidate backend *oracle* at ◊5 (Q9), a cross-prover seam bridged by diff-testing.

**Language (the meta-circular reconciliation).** The verified core is the **total fragment** (⊥-row,
terminating, System-F-typed — where proofs and the moat live). The tested superset is the **`Div` fragment**
(fuel-bounded, partial, Turing-complete — where interpreters, schedulers, and the OS loop live; *tested* +
fuel, not proven total). A meta-circular `eval` for bang is written **either** (a) **fuel-bounded in the
total fragment** — `eval : Nat → Prog → Result` — total (terminates by fuel), hence verifiable; **or** (b)
**`Div`-effected in the superset** — `eval : Prog → A ! Div` — partial, tested. **The kernel already
demonstrates (a)**: `Source.eval : Nat → Comp → Result Val` is a *total* (Lean is total) interpreter for the
*partial, Turing-complete* `Comp` via fuel + `oom` (Amin–Rompf, "Type Soundness via Definitional
Interpreters", POPL 2017; Capretta's `Delay`). bang-in-bang does the identical thing. The Gödel/Tarski
"no system contains its own evaluator" is resolved the standard way: **stratify, and verify *safety
properties*, not *totality*** — exactly how seL4/CertiKOS verify an OS whose scheduler loops forever.

**Adopt `plausible`** (Lean's QuickCheck, already a lake dep) as the engine for the ADR-0026 *tested* rung,
starting at **rung 2** (the verified stack's push/pop laws). SMT backends (`lean-smt`/`lean-auto`/Duper) are
the *verify-climb* rung when a law needs it; `aesop`/`grind` accelerate ◊3/◊4 proofs; `iris-lean` is the ◊4
LR foundation.

## Why

1. **The cross-tool LR proof forces one prover** for the verified spine — not a preference, a necessity.
2. **All-Lean surface now** buys a *provable* lowering for free; divergence is a post-v1 optimization with a
   clean seam, not a v1 cost.
3. **The stratification dissolves the totality wall** instead of fighting it: bang need not be wholly total;
   the total fragment is the verifiable *sub*-language, the `Div` fragment the testable *super*-language, and
   the effect row is the firewall. Turing-completeness (required for an OS) lives in the superset.
4. **The biggest correctness accelerant is not a tool** — it is that ADR-0026 lets us *not prove everything*:
   the surface and the `Div` superset ride differential-testing + fuel, so the expensive Lean proof budget is
   spent only on the verified core.

## Rejected alternatives

1. **Make the whole language total (no `Div`).** *Why not*: cannot express interpreters, schedulers, or the
   xv6 loop — Turing-completeness is required for the golden test.
2. **Make the whole language partial/untyped (no verified core).** *Why not*: abandons the moat
   (proofs-as-programs) and the sound floor.
3. **Single tooling for everything, surface included, forever.** *Why not*: Lean's build/LSP/distribution
   cost; the surface is the *tested* rung (ADR-0026) and may diverge behind the diff-test seam.
4. **Prove the meta-circular `eval` total directly.** *Why not*: impossible for a Turing-complete object
   language (the totality wall). Use fuel (total, verifiable) or `Div` (partial, tested) instead.

## Consequences

- The verified spine stays Lean; the surface stays Lean *for now* with a documented divergence trigger.
- `Div` (Q16) + coinduction are the kernel additions the OS rungs (scheduler, drivers) will need —
  scheduled, not now.
- rung 2's PATH adopts `plausible` for its laws (the first ADR-0026 *tested*-rung use).
- The three-level table above is the project's load-bearing mental model: **verified core + tested superset +
  explicit seam**, at the correctness, tooling, and language levels.

## Revisit if

- Lean's surface tooling/distribution cost exceeds the prove-the-lowering benefit → extract the surface
  (trigger for the tooling divergence).
- A verified-wasm backend oracle (WasmFXCert) is adopted at ◊5 → the cross-prover seam becomes real.
- The `Div`/total seam proves too coarse (a program needs *partial verification*, not just testing) → revisit
  via refinement on the ladder (ADR-0026 climb).
