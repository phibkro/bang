# ADR-0030 — STM enters as a transactional handler in v1; privilege is concurrency-only

- **Status**: Accepted
- **Layer**: K (kernel semantics — how STM enters the model)
- **Depends on**: 0025 (resumptive state handler — STM reuses it), 0023 (CK machine + throws handler — rollback-on-abort), 0001/0018 (effect rows — the `stm` label), 0026 (laws on the tested rung), 0016 (architecture in force)
- **Date**: 2026-06-23

## Context

Rung 3 (the "ledger" — *STM + recovery/rollback*) is the other half of the v1 MVP (PRD §3.1:
imperative/State **+ STM**). STM does **not** exist in the kernel — the `Core.lean` "STM" hits are all
`tvar` (rung 2's μ var); the only mention is a stale comment in the legacy `Eval.lean` citing the
**deleted** ADR-0003. So STM must be designed in, and the project's standing position (invariants #3, #5)
is that **STM is a *privileged* kernel primitive — "the only one" — NOT a handler.** That raises the
question this ADR answers: *what does privilege earn us, and must STM be privileged in v1?*

A literature sweep (Harris et al. PPoPP'05; Guerraoui–Kapalka PPoPP'08; Tomášek TU-Delft; Lesani–Chlipala
C4 OOPSLA'22; Levy CBPV) was run to ground the answer in the source, not instinct.

## Decision

**In v1, STM enters as an ordinary *transactional handler* over the existing kernel — `state ⊗ exception`
composed — with NO new kernel primitive.** Privilege (a runtime-owned shared heap) is deferred to the
concurrent runtime, where it is the only thing a handler cannot provide.

```
v1 STM = a handler, reusing existing machinery
──────────────────────────────────────────────────────────────────────────────
stm operations   newTVar / readTVar / writeTVar  =  up-operations on an `stm` label
atomically M     =  handle M with (transactional handler) — carries (heap Θ, alloc-set ∆)
                    as handler state, exactly as rung 1's state handler carries a cell
commit           normal exit ⟹ expose Θ′
abort/exception  ⟹ restore Θ (discard the write delta), KEEP allocations ∆   ← all-or-nothing
retry            ≈ abort      (single-threaded retry = deadlock in Harris; fold into all-or-nothing)
orElse a b       a aborts/retries ⟹ discard a's writes, run b   (OR2/OR3 ≈ exception-discard)
```

**Sub-calls** (research-sharpened): `retry ≈ abort` (cleanest single-threaded; no blocking machinery);
`orElse` is **in** the minimal core (it is exception-style discard — costs nothing, makes the demo
composable).

**Correctness theorem (the rung-3 moat law): all-or-nothing atomicity** —
`abort / retry / exception ⟹ store unchanged (modulo fresh allocations ∆)`. Property-tested via
`plausible` now (ADR-0026 tested rung), proved later. This is Harris's (ATHROW)/(OR3) discard rule, and
it is **opacity's single-threaded degenerate case** (Guerraoui–Kapalka) — the upgrade path to the
concurrency checkpoint is explicit.

## Why this model (what privilege earns us)

Privilege is load-bearing **only for concurrency**, and the canonical source says so directly:

1. **A handler is a fold over ONE computation's tree.** It can carry a heap + journal as handler state
   and discard-on-abort (rung 1 + the throws handler), which *is* single-threaded STM. What it
   structurally **cannot** do is observe **another transaction's commit** — optimistic read-set
   validation, conflict detection, `retry`-wakeup. Those need a heap that survives *across independent
   computations*, owned by the runtime. **That shared heap is what "privileged" names.**
2. **Harris et al. PPoPP'05 — the reference — agrees verbatim.** Their abstract semantics threads the
   store directly and models abort as "discard the heap delta, keep allocations." They state the
   high-level semantics has *"no notion of transaction logs or rollback — these are implementation,"*
   relegating journal/validation to §6.1, where it exists to make atomicity hold **under concurrent
   committers**. So journal/validation is a concurrency device, not part of the meaning of `atomically`.
3. **The reduction is a recognized result, not novel.** Single-threaded transaction = `ExceptT`-over-
   `State` (exception outside state ⟹ state mutations discarded = all-or-nothing); Tomášek models STM
   ops as algebraic effects interpreted by a handler. We cite, we don't defend.
4. **CBPV favours it.** Levy's home example for CBPV *is* a global store; the value/computation split
   threads the store through the computation judgement only, and TVars-as-values fall out free. Grading
   (McDermott FSCD'25) makes `stm` a row entry like any effect. Nothing forces a primitive in v1.
5. **One construct per problem (invariant #1).** Shipping STM as a handler *unifies* it with rung 1 and
   the throws handler instead of adding privileged Config-threading machinery we cannot yet exercise.
   v1's kernel stays at its minimal core with **zero** privileged primitives in use.

## Rejected alternatives

1. **STM as a privileged primitive with a store in the CK Config (the original strawman).** *Why not*:
   single-threaded, it buys nothing the handler doesn't (Harris puts the store in the *semantics* either
   way; the *journal* is the only addition, and it is a concurrency device). Adds Config-threading +
   un-exercised machinery now, violating invariant #1. Correct **when threads exist** — that is exactly
   where it returns.
2. **Serializability / opacity as the rung-3 theorem.** *Why not*: **vacuous single-threaded** — a lone
   transaction always sees a consistent heap; every history is trivially serial. Spends proof budget for
   no information. All-or-nothing is the minimal-meaningful theorem and is opacity's degenerate case.
3. **Full concurrent STM in v1** (retry-blocking, contention). *Why not*: needs concurrency = multi-shot
   handlers / threads, which is post-v1 (ROADMAP ◊5+). v1 ships the **rollback** half of "STM + recovery."
4. **Linear (use-once) TVars via QTT now.** *Why not*: references are ω-graded (freely shareable) in v1;
   linear references are the rung-5 "QTT surfaced" hinge. Defer.

## Consequences

- **Likely no kernel-primitive change** (invariant #5 intact — STM-the-privileged-primitive remains a
  *named* member of the five, simply unused in v1). The build adds: an `stm` effect label + its
  operation signatures (`EffSig`), a **transactional handler** (`Handler.transaction`, a multi-cell
  state handler with abort-discards-journal), `atomically`/`orElse` as `handle`-shaped forms, and the
  metatheory cases — paralleling rung 1's state handler, not rung 2's type-former extension.
- The **moat demo** is the ledger: a transfer that aborts leaves balances untouched; the all-or-nothing
  law is `plausible`-tested (the second ADR-0026 tested-rung use, after rung 2).
- The privileged-STM invariant (#3) is **reframed, not dropped**: it governs the concurrent runtime. The
  CLAUDE.md invariant text should note "privilege is concurrency-only; v1 STM is a transactional handler
  (ADR-0030)."
- References: a `transactions` group is added to `references/` (the library had zero STM material).

## TVar representation (amendment 2026-06-23 — surfaced by the K2 preservation gap)

Building K1 exposed that two representation choices were left implicit, and both break preservation if
unpinned. Resolved:

1. **`TVarRef = int`** (a heap index *is* an int). The handler's eliminators (`newTVar` returns the new
   index, `read`/`write` take one) type cleanly against the single `vint : int` rule. Leaving `TVarRef`
   existential made `vint i : int` un-typeable at the result type.
2. **The store is TOTAL / default-initialized, with monomorphic `int` cells in v1.** `readTVar` on an
   out-of-range index returns a **default of the cell type** rather than producing `oom`. (K1 used `oom`,
   the *fuel-exhaustion* sentinel, for a bad read — a category error: `oom` is untypable, so a well-typed
   `readTVar (vint 999)` stepping to `oom` falsifies preservation.) A total store is the standard
   finite-representation of a total `Loc → Val` map; it makes `readTVar` total, so preservation closes
   with **no change to the frozen `type_safety` statement** (◊2). `writeTVar` out-of-range is a type-safe
   no-op (source programs never hold an invalid ref — refs come only from `newTVar` — so the default/no-op
   paths are kernel-expressible but source-unreachable).

   **v1 fixes the cell type `S = int`** (default `= vint 0`; `readTVar` miss returns `Θ.getD i (vint 0)`).
   This closes preservation with **zero change to the `Handler.transaction` arity and zero edits to the
   committed K2 resume-typing helpers** — which are written against the 2-arg `transaction ℓ Θ`. The
   general-`S` alternative (a caller-supplied **default-cell witness** carried by the handler, `atomically
   default M`, config-explicit at the boundary) is *more* general — TVars of any type, incl. rung-2 ADTs
   — but it bumps the constructor arity and would churn ~38 committed helper sites for a capability v1
   (int-balance ledgers, counters) does not need. **Deferred as a refinement**, consistent with
   monomorphic-v1 (ADR-0027) and the project's stage-it discipline.

**Rejected for the OOB-read case:**
- *Bounds invariant `i < |Θ|` in `HasConfig`.* Needs a non-trivial reachability invariant (the index is a
  raw int flowing through the program) — heavy, the wrong tool monomorphically.
- *Typed trap / generalize `oom` to be typable-at-any-`F`-type (WASM-style).* Cleanest long-term and
  aligns with the WasmFX backend (which traps on OOB), but it touches the **frozen** `type_safety`
  statement ("well-typed ⇒ value **or trap**"). Deferred — a deliberate later change, not a rung-3 detour.
- *Abstract capability `TVarRef` (a distinct value type, only `newTVar` introduces it).* "More correct"
  (invalid refs unrepresentable) but still needs heap-size tracking to discharge OOB at the kernel level.
  v1 takes the raw-int + total-store pragma; abstract refs are a refinement.

These are **v1 simplifications**, recorded so they are not mistaken for the final story.

## Revisit if

- **Concurrency arrives** (threads / multi-shot handlers, ROADMAP ◊5+) → STM-the-privileged-primitive
  returns: a runtime-owned shared heap, read-set validation, `retry`-wakeup, and the correctness theorem
  climbs all-or-nothing → **opacity** (Guerraoui–Kapalka). This ADR's deferral ends here.
- **STM interleaves with effects that observe partial state mid-transaction.** The handler-scoped journal
  keeps the deferral sound *only* while no effect can see a half-committed heap. This is the exact
  invariant the concurrency checkpoint must re-examine — if an effect needs to observe mid-transaction
  state, the handler model breaks and privilege returns early.
- `retry ≈ abort` proves too weak (a program genuinely needs blocking-retry single-threaded — i.e. wants
  to wait on its own future write, which is a deadlock) → revisit, but that is a concurrency need wearing
  a single-threaded mask.
- **OOB-read should TRAP, not default** (aligning with the WasmFX backend, which traps) → generalize
  `oom`/add a typed `trap` terminal and amend `type_safety` to "value or trap". Deferred from v1 (touches
  the frozen safety statement); the total/default store (above) is the v1 stand-in.
