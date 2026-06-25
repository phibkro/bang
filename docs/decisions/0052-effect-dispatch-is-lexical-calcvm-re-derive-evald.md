# 0052 — bang's effect dispatch is LEXICAL; the CalcVM reference re-derives cap-keyed (route B)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The kernel (ADR-0045 static/cap dispatch) and the CalcVM reference `evalD` (ADR-0023 dynamic/nearest-label) **build-provenly DISAGREE** on a *well-typed* same-label-shadowing program: `handle (state 1 10) (handle (state 1 20) (perform cap=1 1 "get"))` gives kernel `10` (cap=1 names the OUTER handler, lexical) but `evalD` `20` (nearest-label, dynamic) — both `rfl`. The witness is well-TYPED (not just well-capped): `handleState`'s subsumption premise `e ≤ labelEff ℓ ⊔ φ` admits a handler over a body that doesn't use ℓ, so same-label nesting types. **DECISION: bang's effect dispatch is LEXICAL** — the kernel (ADR-0045's cap dispatch) is canonical; `evalD` is the stale dynamic half left over from before the typed-static pivot. **Route B: re-derive `evalD` (+ `unwindFind`/compile/exec) cap-keyed to match the kernel** — full generality, no seam, return-only/vacuous handlers retained. **Sequence B AFTER the absolute-caps migration** (ADR-0053): cap-keying `evalD` against de-Bruijn caps then re-doing it for absolute caps is wasted work. Rejected: **(A) CalcVM-seam** — ships a KNOWN machine≠kernel divergence (the diff-test `Agree` asserts one `v` from both, UNSATISFIABLE on shadow programs → not diff-testable → strictly weaker than the LR seam-5, which has `exec` as oracle); **(C-new=relevance typing)** — a `labelEff ℓ ≤ e` premise forbids the divergence by construction but also kills return-only handlers (`handle (throws 0) (ret 7)`, a deliberate + tested feature; the effect row cannot distinguish "ℓ handled below" from "ℓ unused" — both `⊥`); **(C-new=scope-tracking)** — a true narrow rule needs an in-scope-label set threaded through 12 rules + ~134 Metatheory + the FROZEN Spec (large, re-freeze).
- **Amends**: 0044, 0050
- **Depends-on**: 0023, 0044, 0045, 0050

## Status
Accepted (2026-06-25, operator ruling "CalcVM B"). Decision recorded now; **execution deferred** to a deliberate multi-session unit after the absolute-caps migration. This ADR fixes the *semantic* question (dispatch is lexical) and the *route* (B); the implementation is future work.

## Context

ADR-0045 pivoted the kernel to typed **static (cap) dispatch**: `Source.step (K, perform cap ℓ op v) = staticDispatch K cap op v` — the cap *names which handler*, resolved lexically at the use-site. The CalcVM reference `evalD` (ADR-0023/0024) predates this and resolves operations by **nearest matching label** (dynamic). While cap was inert (ADR-0045 step 1a) the two agreed; step 1b made the cap live, and the CalcVM was never re-run. The ◊5 "CalcVM re-run" investigation (2026-06-25) found this is not a mechanical re-thread but the **dynamic-vs-lexical fork ADR-0044 anticipated** ("changing dispatch re-runs the calculation"), and produced the build-proven divergence witness above.

The divergence is **orthogonal to the cap representation** (de-Bruijn vs absolute, ADR-0053): an absolute cap still names the OUTER handler by position; the gap is purely resolution-discipline (lexical vs dynamic). So absolute caps cleans the LR shift-wall but does NOT close this — confirmed from both the CalcVM side and the cap-representation spike.

## Decision

**bang's effect dispatch is lexical** (the cap is a real, semantically-load-bearing selector, per ADR-0045). The CalcVM reference must faithfully calculate the kernel; the kernel is lexical; therefore **`evalD` is re-derived cap-keyed (route B)**. This keeps the full language (return-only/vacuous handlers, same-label nesting with cap-selection) and makes the executable spec sound against the kernel everywhere — no seam, no feature loss.

The cost (accepted): a multi-session Bahr–Hutton re-derivation touching the reference + calculated machine, and it makes the VM **cap-dependent** (forfeiting the "VM is cap-agnostic / absolute-caps cost = zero" property the absolute-caps spike measured) — which is exactly why B is sequenced **after** the absolute-caps migration.

## Rejected alternatives

- **(A) CalcVM-seam** (restrict `evalD_agrees_source` to a no-shadow fragment). Rejected: the shadow region is a **known machine≠kernel divergence**, not a tested-but-unproven gap — the diff-test `Agree fuel M v := exec (compile M) = some [ret v] ∧ Source.eval fuel M = .done v` (CalcVM.lean:2365) needs the *same* `v` from both and is unsatisfiable on shadow programs, so that region cannot be diff-tested. Shipping it would mean the compiler's shadow behavior is unverified AND inconsistent with the kernel. Strictly weaker than the LR seam-5 (ADR-0050), where `exec` is the oracle. Acceptable only as an honestly-documented out-of-scope hole if forced to ship immediately — not chosen.
- **(C-new = relevance typing)** (`labelEff ℓ ≤ e` on `handleState`/`handleThrows`). Rejected: makes the divergence unrepresentable cheaply (headline stays frozen) BUT also rejects return-only/vacuous handlers — a deliberate, tested feature (`handle (throws 0) (ret 7)`, `CapEscapeWitness.h_M`). Build-proven that the effect row cannot separate "ℓ handled below" (`⊥`) from "ℓ unused" (`⊥`), so any row-based rule that kills the witness also kills return-only handlers.
- **(C-new = scope-tracking typing)** (add an in-scope-label set to `HasCTy`). Rejected for v1: forbids *exactly* same-label nesting with no feature loss, but threads through 12 computation rules + ~134 Metatheory sites + 31 Syntax + **12 frozen Spec.lean statements** (changes the judgment arity → frozen-statement violation + a re-freeze ADR). Large kernel-level refactor.

## Sequencing

1. Absolute-caps migration (ADR-0053) — LR 5→2, kernel rep change. **First.**
2. **Route B: re-derive `evalD` cap-keyed** against the absolute-cap kernel — the ◊5 CalcVM re-run, full generality. Multi-session, kernel/proof-engineer-paired.

## Evidence
- The build-proven witness + the three rejected-route assessments (diff-testability, relevance cost, scope-tracking size) — investigation thread 2026-06-25, captured in this ADR. The bounded route-B bridge diagnosis (re-key `dispatch K ℓ op` → cap-keyed via the kernel `staticSplit_*` family) is the starting point for the B implementation.
