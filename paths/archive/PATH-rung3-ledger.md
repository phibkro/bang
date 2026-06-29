# PATH · Rung 3 — a verified ledger (STM as a transactional handler)

> The other half of the v1 MVP (PRD §3.1: imperative/State **+ STM**). Ladder rung 3. Status: **READY**
> (scoped 2026-06-23 after ADR-0030; not started). The **second paradigm-as-library** and the **second
> moat demo** — transactional rollback, checked on the ladder.

## Why this rung

rung 1 proved a paradigm (State) is a handler; rung 2 proved user types + laws. Rung 3 proves the
**transactional** paradigm is *also* just a handler — **STM = `state ⊗ exception`** (ADR-0030), no new
kernel primitive. Two paradigms (imperative + transactional) on one verified kernel **is** the
multi-paradigm thesis, shipped. The demo: a ledger transfer that aborts leaves balances untouched.

## GOAL (verifiable)

1. A ledger program runs through `Source.eval`: `atomically (transfer a→b)` commits on success; an
   aborting transfer (e.g. insufficient funds) yields the **unchanged** balances. Green via `#guard`.
2. The **all-or-nothing law** holds: `abort ⟹ store unchanged (mod fresh allocations)`.
   - **Discharge: prove if cheap, else `plausible`-test** (operator call 2026-06-23). The proof-engineer
     assesses the proof cost; if cheap, rung 3 ships a **VERIFIED** law (a step UP the ladder from rung
     2's tested law); fall back to the tested rung if it fights. Either way the moat is visible.

## SCOPE — handler-first (ADR-0030), reusing rung 1

**K — kernel transactional handler (the bulk; kernel-engineer + proof-engineer):**
- `stm` effect label (distinct from `exnLabel=0`, `stateLabel=1` — pick `stmLabel`); `EffSig` op
  signatures for `newTVar`/`readTVar`/`writeTVar` (opArg/opRes).
- `Handler.transaction : Label → Store → Handler` where `Store = List Val` — a **multi-cell**
  generalization of `Handler.state` (which threads ONE cell). TVar = a heap index (de-Bruijn-style, like
  the μ tvar and the value-level vvar).
- Dispatch (`Operational.lean`, `handlesOp` + the resume walk): `read`/`write`/`new` RESUME threading the
  updated heap — **the exact ADR-0025 state-resume pattern, generalized to a list**. `new` extends the
  heap (an allocation ∆); `write` updates a slot; `read` returns a slot.
- **Rollback is free**: abort = a zero-shot `throws` that escapes the `transaction` frame (ADR-0023
  discards the continuation, so the frame's heap never commits) — Harris's "discard the delta, keep
  allocations". Decide: abort via the existing `throws` op escaping `atomically`, and/or an explicit
  `abort`/`retry` op. `retry ≈ abort` (ADR-0030); `orElse a b` = a aborts ⟹ run b (exception-flavored).
- `atomically M` = `handle (transaction stmLabel ∅) M` (a `handle`-shaped form; may be pure surface
  sugar over `handle`, or a thin Comp form — kernel-engineer's call, prefer reusing `handle`).
- Typing (`Syntax.lean`): `HasCTy`/`HasStack` cases for the transaction handler + stm ops (mirror
  `handleState`/`stateF` + the `up` rule). Metatheory (`Metatheory.lean`): preservation/progress for the
  new dispatch cases — stub as `RUNG3-OBLIGATION` for K2. **`no_accidental_handling` MUST stay 0-axiom**
  (the stm label is just another label; the ◊2 gate must not move).

**L — surface + the moat (surface IC):** ledger in `Surface.lean` — `atomically`/`newTVar`/`readTVar`/
`writeTVar`/`abort` surface forms (hide the `up`/`handle` lowering, a Q20 pseudoinstruction, like rung 1's
`state`/`get`/`put`); a transfer demo runs from source/AST; the all-or-nothing law (`plausible`-tested,
OR cite the Lean theorem if K2 proved it).

## OUT OF SCOPE (ADR-0030)

Concurrency / contention / `retry`-as-blocking · serializability/opacity (vacuous single-threaded) ·
a global cross-transaction heap (TVars are transaction-scoped in v1) · linear/QTT TVars (ω-graded; rung 5)
· the privileged-primitive store-in-Config (deferred to the concurrency checkpoint) · multi-shot.

## DELIVERABLE

- Kernel: `Handler.transaction` + stm ops land; `just verify` green, axiom-clean,
  `no_accidental_handling` 0-axiom.
- Surface: ledger runs; abort leaves balances untouched (`#guard`).
- Law: all-or-nothing **proven (if cheap) or `plausible`-tested** — the 2nd ladder demo.
- Finding appended here: did STM-as-handler reuse rung 1 as cleanly as predicted? Was the all-or-nothing
  law cheap to PROVE (did we climb the ladder)? What did `state ⊗ exception` cost?

## OWNER

**kernel-engineer + proof-engineer** (the transaction handler + dispatch + metatheory is the bulk),
then **surface IC** (ledger + law). Same triad + flow as rung 2.

## POINTERS

- **ADR-0030** (the decision — STM-as-handler, all-or-nothing, privilege=concurrency-only) · ADR-0025
  (resumptive state handler — the pattern to generalize) · ADR-0023 (CK machine + throws-discards-
  continuation — rollback) · ADR-0001/0018 (effect rows — the stm label).
- Literature (`references/`, ADR-0030): Harris PPoPP'05 (the semantics — abort discards delta, keeps
  allocations), Guerraoui–Kapalka opacity (the upgrade target), Tomášek (STM-as-handler prior art).
- Kernel: `Bang/Core/IR.lean` (`Handler` — add `transaction`; `EffSig` — stm op sigs), `Bang/Core/Semantics.lean`
  (`handlesOp` + resume dispatch — generalize state to a heap), `Bang/Core/Typing.lean` (typing),
  `Bang/Core/Soundness.lean` (preservation/progress cases). Surface: `Bang/Frontend/Surface.lean`. Pattern: rung 1
  (state handler) is the template — read its commits + `dispatch_state_typed`.

## STATUS — ✓ GOAL MET (kernel + verified law), 2026-06-23

Commits: `4737a1b` (K1 handler + ledger) · `6a81b0f` (K2 helpers, partial) · `13d39b4` (ADR amendment) ·
`acde8a3` (K1.5 fix + K2 metatheory closed + the law). `just verify` green; ◊2 gate held every commit.
GOAL.1 (ledger runs) ✓ · GOAL.2 (all-or-nothing) ✓ **and PROVEN, not just plausible-tested** —
`all_or_nothing_abort` axiom-clean `[propext, Quot.sound]`, in `Audit.lean`.

**Scoped follow-ons**: ✓ **from-source `atomically`/`new`/`read`/`write` surface DONE** (`9892126` — STM
is now writable from source text, incl. abort-rollback). Remaining: `orElse` (needs *nested-transaction*
semantics — discard the alternative's writes, Harris OR3; bigger than "a recovery handler") · general-`S`
TVars (ADR-0030 amendment, default-witness).

## FINDING — what STM-as-handler cost

**The ADR-0030 bet paid off: STM reused rung 1 cleanly.** `Handler.transaction` is the state handler with
a list-heap; resume-dispatch reused `dispatch_state_typed`'s structure (the helpers went in fast).
Rollback is **by construction**, not by validation — abort is a `throws` escaping the frame, and the
existing throws-discard machinery (`dispatch_raise_eq`) drops `Kᵢ` (which holds the frame + heap). The
moat law is a **6-line corollary** of that — both ICs predicted "cheap" and were right. So rung 3's law is
**verified** (a ladder climb above rung 2's *tested* law) for almost no extra budget.

**Four things worth carrying forward:**
1. **`oom` is the FUEL sentinel — never reuse it for a runtime error.** K1 used `oom` for an out-of-range
   `readTVar`; `oom` is untypable, so a well-typed bad read stepped to a stuck-untypable state and
   falsified preservation. Fix: keep `readTVar` **total** via a default-initialized store (TVarRef=int,
   S=int, miss returns `Θ.getD i (vint 0)`) — closes preservation with **no change to the frozen
   `type_safety` statement**. The WASM-aligned alternative (a typed `trap`, amending the safety theorem)
   is the deferred upgrade (ADR-0030 Revisit-if).
2. **The int-ness must live in the typing RULE, not just the handler value.** Resume proofs read the ref
   type off the *stack frame* (after `handleTransaction` is consumed), so pinning only `handleTransaction`
   leaves `TVarRef` generic at resume. Pin `transactionF`.
3. **For an int-monomorphic kernel, pin the helper lemma signatures too.** A generic-over-`S` lemma return
   handed callers opaque metavars (`w✝`) instead of `int` — the actual red. Generic buys nothing while the
   constructor is pinned.
4. **`orElse` is NOT free** (corrects ADR-0030's "minimal core, costs nothing"). `throws` *discards* the
   continuation and yields the payload — it cannot run an alternative. `orElse a b` ("run `b` if `a`
   aborts") needs a **recovery/catch handler** (a new `Handler` variant or a sum-tagging mechanism). A
   real small increment, scoped as a follow-on.

## CONTROL-FLOW NOTE (multi-agent process)

This rung exercised the full triad twice (K1 → K1.5 → K2) with two STOP-and-escalate moments handled
well: the proof-engineer refused to fake a proof over a broken typing rule (surfaced the `TVarRef`/`oom`
gap → ADR amendment); the kernel-engineer refused to apply two incompatible orchestrator instructions
(default-witness-constructor vs untouchable-helpers → re-decided to S=int). One coordination miss: the
orchestrator overlapped K1.5 and K2 on the same file (shared working tree) — caught early, resynced, no
damage. **Lesson: sequence agents that touch the same file, or give them worktrees.**
