# Architecture Decision Records

Each ADR records a decision a future session could otherwise reverse or relitigate: the **rationale**, the **rejected alternatives**, and a **"Revisit if"** clause that distinguishes legitimate reconsideration from drift. Read the relevant ADR before changing anything it covers.

| # | decision | status | depends on |
|---|----------|--------|------------|
| [0001](0001-effect-rows-as-finset-semilattice.md) | Effect rows are idempotent sets (join-semilattice), modeled as `Finset` | Accepted | — |
| [0002](0002-lean-over-fstar-for-the-oracle.md) | Verify the reference in Lean 4 + Mathlib, not F\* | Accepted | 0001 |
| [0003](0003-own-the-runtime.md) | Own the runtime; don't transpile to a borrowed effect runtime | Accepted | — |
| [0004](0004-calculated-vm-as-canonical-target.md) | The canonical target is a calculated VM; Effect TS et al. are optional lowerings | Accepted | 0002, 0003 |
| [0005](0005-collapse-sig-into-mut.md) | Collapse `sig` into `mut` + the `:`/`=` operator distinction | Accepted | — |
| [0006](0006-explicit-tracked-capture.md) | Capture is explicit and tracked; no implicit lexical closure | Accepted | 0003 |
| [0007](0007-force-is-dollar-parens-group.md) | Force is `$`; parens group without forcing; fixed global precedence | Accepted | 0005 (supersedes its force note), 0006 |
| [0008](0008-eval-free-monad-handler-fold.md) | Definitional `eval` is a fuel-bounded free-monad interpreter; handlers are a deep fold | Accepted | 0004, 0001, 0006, 0007 |
| [0009](0009-calculated-vm-extrinsic-staged.md) | Calculated VM is extrinsic and grown one constructor at a time, from an arithmetic kernel | Accepted | 0004, 0008 |
| [0010](0010-higher-order-calculation-fuel-cbv.md) | Higher-order calculation: fuel-indexed CBV, shared source-closures (equivalence now proven) | Accepted | 0009, 0008 |
| [0011](0011-effects-calculated-as-specific-machines.md) | Effects calculated as specific machines (Throws→unwinding, State→register); tail-resumption only | Accepted | 0004, 0008, 0009, 0010 |
| [0012](0012-effects-composed-with-the-closure-core.md) | Effects composed with the closure/CBN core — Throws fused into `CalcCBNEff` (zero-shot, re-throw at the meta-call boundary) | Accepted | 0011, 0010, 0008, 0009 |
| [0013](0013-state-composed-with-the-closure-core.md) | State composed with the closure/CBN core — `CalcCBNSt` (the register threads cleanly through the nested meta-runs; no flatten needed) | Accepted | 0012, 0011, 0010 |
| [0014](0014-two-effects-together-over-the-closure-core.md) | Throws *and* State together in one machine — `CalcCBNEffSt` (effect-row model realized; State persists through a throw) | Accepted | 0012, 0013, 0011, 0003 |

Format: lightweight MADR. Status ∈ {Proposed, Accepted, Superseded by NNNN, Deprecated}.
