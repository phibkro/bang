# 0049 — Capability-safety diagnostics via the lexical-well-capped (LW) pass, not typing-rule fusion

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Capability errors (a `perform cap ℓ op`'s cap resolves to a handler of the wrong label/kind) are reported by a **label+kind-aware checking pass over the EXISTING LW machinery** (`CapResolvesKind`/`handlesOp`/`staticSplit`), which already computes the exact mismatch decidably and carries the `(cap, ℓ, op)` triple a sharp message needs. We do **NOT** fuse cap-resolution into the core typing rule `HasCTy.perform` (approach "A"): it is HARD (~200–300 LOC, **breaks the cap-irrelevance principle**, risks the axiom-clean STD block), buys **no** diagnostic power the LW lacks ("A forces B anyway"), and contradicts the field's universal practice of keeping handler RESOLUTION a separate lexical pass (Zhang-Myers, Effekt, Koka). `HasCTy.perform` stays **cap-irrelevant**; the diagnostic richness lives in the separate LW pass — the kernel-minimal / shell-rich stratification (ADR-0026, kernel-shell-library).
- **Depends-on**: 0045, 0026, 0044, 0046

## Context

Static dispatch routes `perform cap ℓ op v` to the cap-th enclosing handler (ADR-0045). An **ill-capped** program — cap resolves to a handler whose label/kind doesn't match `(ℓ, op)` — is a real error class, and catching it with a good message is load-bearing for the "safe to generate into" moat (PRD): a precise capability error beats a runtime stuck.

The open question: should the type system be made **label/capability-aware** (fold cap-resolution into `HasCTy.perform` — "approach A") *because* it might buy better error analysis, justifying the cost? Two surveys answered it (2026-06-25): an internal cost+current-state survey, and an external precedent survey of effect-handler type systems.

The key current-state fact (`Bang/Core/Soundness.lean:523`): **`HasCTy.perform` is CAP-IRRELEVANT** — the rule constrains the row/grade/op, never the cap. A *separate* label+kind-aware predicate already carries resolution: `LWT`/`LWConfig` over `CapResolvesKind S cap ℓ op` (`Bang/Core/Semantics.lean:344,572,626`), folded into typing only at the `HasConfig` seam. **The project is already running approach B.** "A vs B" is really: push `CapResolvesKind` up into `HasCTy.perform`, or keep it a sibling predicate.

## Decision

1. **Capability diagnostics ride a label+kind-aware pass over the EXISTING LW.** `CapResolvesKind` already carries the `(cap, ℓ, op)` triple; `handlesOp` distinguishes **label mismatch** (`h.label ≠ ℓ`) from **op-not-in-interface** (`h.label = ℓ`, `op` unsupported); `staticSplit K cap` yields the resolved handler. An error pass is ~100–150 LOC of querying + formatting, **no new proofs** — all the computation is already proven sound (`staticSplit_isSome_of_resolvesKind`, the cap-insertion lemmas).

2. **`HasCTy.perform` stays cap-irrelevant — do NOT do approach A.**

3. **Diagnostic quality lives in the STRUCTURE of the separate pass.** Keep `CapResolvesKind` label/kind-structured; do **not** let it degrade to a bare `Finset`-membership test — set-flattening loses the per-perform precision the message needs (and, Yoshioka §7, soundness under lift-coercions). The targeted message: *"perform of `op` at label `ℓ` resolves to cap `n`, which names a handler of kind `K` ≠ `op`'s kind."*

## Grounds (both surveys converge)

**Internal cost (Lean source).** Approach A is **HARD**: ~200–300 LOC across the `shiftCap`/`subst`/`weaken` perform-arms, because adding the premise **breaks cap-irrelevance** (`Metatheory:520-526`, the principle the whole cap-shift machinery rests on) and forces a new `CapResolvesKind.shiftCapFrom` commutation lemma — the inverse of the B3a wall that forced lexical caps. It risks the axiom-clean STD block. And it buys nothing: the LW **already** computes the exact label+kind mismatch decidably (`CapResolvesKind` + `handlesOp`). Decisive: **"approach A forces approach B to happen anyway"** (you still compute `CapResolvesKind`), so A is strictly dominated for diagnostics.

**External precedent (the literature).** The field splits the question on two axes: **coverage/safety** ("no op unhandled") is fused into the type-effect judgment universally (Koka, Eff, Frank, Yoshioka λ_EA, Tang); but **resolution** ("which handler catches `op`, nearest-enclosing") is kept a **separate lexical pass** wherever non-trivial — **Zhang-Myers POPL'19** (a separate desugaring pass + a fused *escape* side-condition — and the origin of this project's `no_accidental_handling`), Effekt's capability-passing elaboration, Koka's evidence-passing. `HasCTy` (fused safety: row/grade/op) + `LWConfig` (separate resolution: cap/label/kind) **is exactly that canonical Zhang-Myers two-tier shape, independently re-derived.** Fusing does **not** improve messages — the sharp "no handler for op X at label Y" comes from the label being explicit *type-visible structure* (Koka rows; here `CapResolvesKind`'s triple), which a cap-irrelevant `HasCTy` discards. OCaml 5 (the only system deferring entirely to runtime) has the *worst* diagnostics and lost static safety. The one "fuse" precedent — Koka named-handlers (OOPSLA'22) — fused for *expressiveness/framework-integration* via rank-2 polymorphism (which ADR-0045 deliberately avoids), explicitly **not** for diagnostics.

## Rejected alternatives

- **Approach A — fuse `CapResolvesKind` into `HasCTy.perform`.** HARD + breaks cap-irrelevance + STD-block risk; dominated for diagnostics ("A forces B anyway"; B gives *better* messages by keeping the label structure); contradicts the field's separate-resolution norm; re-imports the cap-in-row complexity the `setrow-tension-spike` was built to avoid. Reopen only if the *kernel itself* must gatekeep untrusted hand-written core with no LW pass in the loop — not v1's threat model.
- **Runtime-only detection (OCaml-5 style).** A `perform`-site exception with a backtrace: no compile-time signal, points at the call site not the missing handler — fails the "safe to generate into" moat.

## Consequences

- The error-analysis pass is a **post-LR ~150-LOC shell unit** riding the existing LW — no kernel typing change, no new proofs. It is the concrete "capability error, not runtime stuck" moat feature.
- **Convergence with the soundness work:** the LR's static-dispatch soundness fix (the `KrelS` `handleF` cap-threading, ADR-0045's Inc 2 / R1 bridge) is *also* not approach A — it threads cap+label inside the LR relation, kernel typing untouched. Both the diagnostics and the soundness work keep `HasCTy` cap-irrelevant.
- The stratification holds: rich label/kind analysis is a **shell-facing checker over a minimal kernel judgment** (kernel-shell-library), not a kernel typing change. Frozen statements unaffected (`preservation`/`progress` byte-identical; `type_safety`'s `LWConfig` premise is the existing ADR-0045 R1).
- **Standing constraint:** keep `CapResolvesKind` label/kind-structured (heed Yoshioka §7 / Tang §2.4) — the diagnostic precision and soundness both live in that structure.
