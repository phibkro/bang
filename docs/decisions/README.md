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

Format: lightweight MADR. Status ∈ {Proposed, Accepted, Superseded by NNNN, Deprecated}.
