---
type: design-question
title: "`orElse`: how does the alternative discard the first branch's writes?"
description: "orElse must run b as if a's transactional writes never happened — savepoint vs nested-tx"
status: open
area: effects
ties: ["Q21", "ADR-0030"]
see-also: []
---
**Question**: `orElse a b` runs `a`, and if `a` aborts runs `b` — but `b` must run as if `a`'s **writes
never happened** (Harris OR3). How does the kernel discard `a`'s transactional writes on fallthrough?

**Why it matters**: `orElse` is STM's *compositional alternative* (the reason "composable memory
transactions" is the paper title). ADR-0030 listed it as minimal-core "costs nothing" — **that was wrong**
(corrected in the ADR): the `throws` handler *discards the continuation and yields the payload*; it cannot
run an alternative, and it cannot roll back only `a`'s sub-writes. So `orElse` is a real (small) increment,
not free.

**Detail**: `a`'s writes live in the transaction heap `Θ`. On `a`-abort, `Θ` must be rolled back to its
state at `orElse`-entry before `b` runs; on `a`-commit, `a`'s writes persist. The current single-threaded
rollback (abort = `throws` escaping the *whole* transaction frame) is too coarse — it discards the *entire*
transaction, not just `a`'s sub-effects.

**Options**:
1. **Savepoint (★ recommended for v1)** — snapshot `Θ` at `orElse` entry (`Θ_sp`); run `a`; on `a`-abort
   restore `Θ ← Θ_sp` and run `b`; on `a`-commit keep. One heap + a saved copy. Smallest extension: the
   transaction handler (or an `orElse` Comp form) brackets `a` with save/restore-on-abort. *Allocation
   subtlety*: truncating `Θ` to `Θ_sp` also drops `a`'s allocations — observationally fine (`b` can't name
   `a`'s TVars) though it diverges slightly from Harris's "keep `∆`"; record the choice.
2. **Nested transaction** — `a` runs in a sub-transaction (heap = copy of parent's current); commit merges
   to parent, abort discards + runs `b`. More general (composable nesting), needs snapshot-at-install +
   merge-on-commit. The **concurrency-era** form (couples to [[Q21]]).
3. **Recovery handler** — a `Handler.orElse`/`recover` variant catching `a`'s abort, restoring the heap,
   running `b`. ≈ option 1 framed as a handler; needs the variant to reach the transaction's heap.

**Recommended**: **savepoint (1)** for single-threaded v1; **nested-tx (2)** is where it generalizes when
concurrent STM (Q21) lands. Either way the *correctness* obligation is `orElse a b ≈ b` when `a` aborts
(its writes invisible) — provable like `all_or_nothing_abort`.

**Blocked on**: nothing — a bounded rung-3 follow-on. Needs the transaction handler to expose heap
snapshot/restore (a small kernel extension; touches Core/Operational/Syntax/Metatheory + a surface form).

**Revisit signal**: a program wants composable transactional alternatives (the canonical `orElse`
use-case); or concurrent STM (Q21) lands and nested-tx becomes the natural form.
