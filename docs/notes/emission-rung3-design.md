<!-- note-status: active -->
# Emission rung-3 design — transaction journal/rollback on Wasm (the ◊5.5 novelty rung)

> **Verdict (one sentence).** Rung 3 of ◊5.5 (ADR-0030's transaction journal/rollback) is
> **TRACTABLE and DEMONSTRATED for the empty-start (`atomically`) fragment**: the TVar heap
> lowers to linear **memory** (one i64 per cell), `newTVar`/`readTVar`/`writeTVar` to
> alloc/load/store, and rollback-on-abort to a **`catch_all_ref` + `throw_ref` snapshot-restore**
> wrapping the body — and **6 transaction programs, including the A11 abort/rollback witness, ran on
> `wasmtime` 45 with values MATCHING `Source.eval`** (corpus now 72/72). The load-bearing finding:
> **wasm gives the unwind for free but NOT the memory rollback** — mutation is destructive, so the
> discard-the-frame semantics (`Θ'` vanishes with the frame, Dispatch.lean:143) must be an *explicit*
> restore, and a hand-witness confirms that restore is load-bearing (fires on the abort path).

Spike additive to the rung-1/2b leaf (`Bang/Backend/WasmEmit.lean`, `EmitMain.lean`,
`tools/emit-rung1-diff.sh`); refute-first oracle probe `scratch/TxnOracleProbe.lean`. No
proof-bearing file touched; emitter axiom set unchanged (`[propext]`, self-tests `by simp`).

---

## 1 · The four design questions (deliverable 1)

### Q1 — journal representation: **linear memory + heap-length pointer + snapshot** (recommended)

The kernel heap `Θ : List Val` (Dispatch.lean:116) is threaded through the resume frame:
`newTVar v` **appends** (returns the old length as the TVar index), `readTVar (vint i)` reads cell
`i`, `writeTVar (pair (vint i) w)` sets cell `i`. Three options weighed by SEMANTIC FIDELITY first
(invariant #7 — perf second-class):

| option | fidelity to `Θ`-as-list | rollback | verdict |
|---|---|---|---|
| **A. linear memory + `$heaplen` + snapshot** | exact: cell `i` at byte `8·i`, `newTVar` bumps `$heaplen` (= `Θ.length`), read/write index directly | snapshot the affected region (empty-start: just the length pointer) at entry, restore on catch | **CHOSEN** — the `Θ`-as-indexed-sequence maps 1:1 to `memory`; `newTVar`'s "return old length" is literally `$heaplen` |
| B. GC-struct heap + journal list | a `(ref $cell)` array + a write-set list; needs Wasm-GC (in per ADR-0059) | drop the journal list on abort | more machinery (GC types + a growable array) for no fidelity gain at v1's i64 cells; defer to when TVars hold non-i64 |
| C. copy-on-entry whole-heap snapshot | same memory rep, but snapshot the WHOLE heap region at `handle` entry | restore the whole region on abort | **the semantically-exact general form** — chosen shape for a PRE-SEEDED `Θ` (§3.2); for empty-start it degenerates to A (nothing pre-existing to copy) |

**Why A over B**: `Θ` is an indexed sequence with append-allocation and total indexing — exactly
linear memory with a bump pointer. A TVar reference is an `int` (ADR-0030 amendment, Dispatch.lean:148),
so `readTVar`/`writeTVar` index by an i64 the emitter already knows how to produce. WasmGC (option B)
buys heap-of-boxed-cells generality bang's i64-cell v1 does not need; it becomes the right rep when a
TVar can hold a closure/ADT (rung-4). **A and C are the same rep** — C only adds a copy loop for the
pre-existing cells a non-empty `Θ` starts with; the empty-start `atomically` (all v1 STM surface,
ADR-0030) needs only A's length-pointer snapshot.

### Q2 — rollback control flow: **`catch_all_ref` + `throw_ref` around the body, INSIDE the throws `try_table`**

The kernel's rollback is structural, not a step: an abort is a zero-shot `throws` on a DIFFERENT
label that escapes the transaction frame; the frame (carrying `Θ'`) is discarded, so writes never
commit (Dispatch.lean:140-142). On wasm the throws-unwind (rung-2's `try_table`/`throw`) transfers
control but does **NOT** undo `memory.store`s. So the transaction body is wrapped in its OWN
catch-all that restores then re-raises:

```wat
(block $txcommit (result i64)
  (block $txab (result exnref)
    (try_table (result i64) (catch_all_ref $txab)   ;; catch ANY exn crossing the txn boundary
      <body leaves i64>)                            ;; normal exit: i64 on stack
    (br $txcommit))                                 ;; COMMIT path: carry value out (writes stand)
  ;; ── reached only via catch: $txab leaves the exnref ──
  (local.set $heaplen (local.get $saved))           ;; ROLLBACK: drop allocations
  (throw_ref))                                       ;; RE-RAISE to the lexically-enclosing throws handler
```

- **`handle (throws) { handle (transaction) { … raise … } }`** (A11, A12): the inner txn's
  `catch_all_ref` catches the `throw $exn0` FIRST, restores, then `throw_ref` re-raises the same
  exnref, which the OUTER `(catch $exn0 $h0)` then delivers. Confirmed: `txn4`/`txn5` return the
  raise payload (100 / 42), the write is discarded. This is the exact nesting for both corpus shapes.
- **`handle (transaction) { … }` with no abort**: fall-through path only — `br $txcommit` carries
  the body value out; the restore/`throw_ref` code is unreachable; writes commit (`txn1` = 70).
- **Why `catch_all_ref` (not per-tag)**: the txn must roll back on ANY foreign abort regardless of
  which outer handler's tag it carries — it re-raises the *same* exnref (`throw_ref`), preserving the
  identity so the correct lexical throws handler still catches. A per-tag catch would need to know
  every enclosing tag statically; `catch_all_ref` + `throw_ref` is the tag-agnostic transparent wrapper.

### Q3 — verification story: TESTED stratum now; the proof-grade obligation named

Same seam as rung 1/2 (CLAUDE.md stratification): the emitter is the tested superset, oracle =
`Source.eval` across the engine boundary. Rung 3 adds to the harness: the 6-program txn corpus
(commit, multi-cell, two abort/rollback witnesses) emitted → `wasmtime -W exceptions=y` → diffed vs
`Source.eval` (all OK). **Refute-first** (route-agnostic de-risk, per the working method): before
any emitter, `scratch/TxnOracleProbe.lean` (compiled — the fuel recursion is unreliable under
`#eval`) confirmed `Source.eval`'s value on all six witnesses, so the diff tests a KNOWN target.

The **proof-grade** obligation (the honest what-remains, ADR-0035 annotated-sim shape): a
`wexec (emit M) ≡ Source.eval M` forward simulation for the txn fragment. The one new invariant over
rung-2b: a **memory-region ↔ `Θ` bijection** — cell `i`'s i64 at byte `8·i` mirrors `Θ[i]` at every
program point, preserved by `newTVar` (append ↔ bump+store), `readTVar` (load ↔ index), `writeTVar`
(store ↔ `storeSet`); AND a **rollback lemma**: on the abort path the restored region equals the
pre-`handle` heap (the wasm analog of "the frame's `Θ'` is discarded"). For empty-start this is just
`$heaplen := saved`, so the rollback lemma degenerates to "the post-abort live length = the pre-txn
length" — the simplest form. These are per-former cases, not a re-architecture (the structural
one-arm-per-former shape is preserved).

### Q4 — the rung-4 boundary (what rung 3 deliberately does NOT need)

- **No closures / no ADT cells.** TVars hold i64 only. A TVar holding a thunk/sum/product needs the
  WasmGC boxed-cell heap (Q1 option B) — rung-4, gated on the value-rep-beyond-i64 work (rung-1.5's
  deferred general-ADT half).
- **No general (multi-shot) resumption.** v1 transaction is one-shot in-place resume (ADR-0025) —
  `readTVar`/`writeTVar` continue the SAME continuation, which is straight-line wasm. Reified
  resumptions on the WasmGC frame-chain stay post-v1 (ADR-0059 §v1/post-v1); nothing in v1's three
  handler forms reifies.
- **No non-empty initial heap `Θ`.** Only `atomically` (empty-start) is in-fragment; a pre-seeded
  `Θ` (never produced by the surface, but expressible in the kernel) is a NAMED refusal (§3.2) — it
  needs the copy-on-entry snapshot loop (Q1 option C), a small delta, not a wall.
- **No concurrency (journal/retry/validation).** ADR-0030: v1 STM is single-threaded; the privileged
  concurrent form (journal validation, retry, conflict detection) returns post-v1. The rung-3 image
  is the single-threaded semantics = journal-of-one + rollback.
- **No `custom` (user effects).** The other rung-3 leg (a clause body as a tail-resume, §9.6 of the
  rung-1 note) is orthogonal — it needs clause-`Comp` emission (the first arm to need a real `call`),
  gated separately.

---

## 2 · The side-by-side — transaction output on a real engine (deliverable 2, the SPIKE)

```
sample   program                                                    wasmtime   oracle   verdict
txn0     atomically { r = new 9; read r }                                  9        9   OK   (alloc + read-back)
txn1     atomically { r = new 100; write r 70; read r }                   70       70   OK   (COMMIT — write stands)
txn2     atomically { a=new 5; b=new 10; write a 7; read a }               7        7   OK   (two cells, write first)
txn3     atomically { a=new 5; b=new 10; read b }                         10       10   OK   (second cell, offset 8)
txn4     handle (atomically { r=new 100; write r 70; raise 100 })        100      100   OK   (A11 ABORT/ROLLBACK)
txn5     handle (atomically { a=new 5; write a 99; raise 42 })            42       42   OK   (abort, payload≠cell)
```

`wasmtime run -W exceptions=y --invoke main txnN.wat` (real engine, wasm 3.0 exceptions +
core linear memory). Reproduce inside `nix develop`: `bash tools/emit-rung1-diff.sh` (72/72 OK,
exit 0). The emitted `.wat` for `txn4` (A11 — the abort/rollback witness):

```wat
(module
  (tag $exn0 (param i64))
  (memory 1)
  (func $main (export "main") (result i64) (local i64) (local i64) (local i64)
    (block $h0 (result i64)                                  ;; OUTER throws handler
      (try_table (result i64) (catch $exn0 $h0)
        (local.set 0 (i64.const 0))                          ;; $heaplen := 0
        (local.set 1 (local.get 0))                          ;; $saved  := $heaplen
        (block $txcommit0 (result i64)
          (block $txab0 (result exnref)
            (try_table (result i64) (catch_all_ref $txab0)   ;; TXN catch-all
              (local.set 2 (local.get 0))                    ;; idx := $heaplen (=0)
              (i64.store (i32.wrap_i64 (i64.mul (local.get 2) (i64.const 8))) (i64.const 100))  ;; new 100
              (local.set 0 (i64.add (local.get 0) (i64.const 1)))                                ;; $heaplen++
              (i64.store (i32.wrap_i64 (i64.mul (i64.const 0) (i64.const 8))) (i64.const 70))    ;; write 70
              (throw $exn0 (i64.const 100)))                 ;; raise 100 (foreign to txn)
            (br $txcommit0))
          (local.set 0 (local.get 1))                        ;; ROLLBACK: $heaplen := $saved
          (throw_ref))))))                                   ;; re-raise to $h0 ⇒ delivers 100
```

The `throw $exn0 100` unwinds to the txn's `catch_all_ref $txab0` (nearest), which resets
`$heaplen` and `throw_ref`s the SAME exnref up to the outer `catch $exn0 $h0` — delivering 100,
with the write to cell 0 discarded. **The write's discard is not directly OBSERVED here** (control
leaves the txn on abort — the kernel has no read-after-abort within a txn either), but the restore
provably FIRES: a hand-witness (`scratch/rollback-observable.wat`) returns the post-abort `$heaplen`
and gets **0** (restored), not **1** (leaked) — the `catch_all_ref`/`throw_ref` path is load-bearing,
not dead code.

---

## 3 · Scope + honest gaps

### 3.1 · The four fused op-sites (former → wasm)

| kernel op (`dispatchOn` `.transaction` arm) | wasm emission | fused shape |
|---|---|---|
| `handle (transaction ℓ [])` | `$heaplen:=0; $saved:=$heaplen; (block…(try_table catch_all_ref…))` | — |
| `newTVar v` → `ret (vint Θ.length)`, `Θ++[v]` | `idx:=$heaplen; mem[8·idx]:=v; $heaplen++` (idx binds N@0 as a `.val`) | `letC (newTVar v) N` |
| `readTVar (vint i)` → `ret Θ[i]` | `(i64.load (8·i))` — an i64-leaver (flows the bare/letC path) | any i64 context |
| `writeTVar (pair (vint i) w)` → `ret unit`, `storeSet` | `mem[8·i]:=w` (STATEMENT; write-unit binds N@0 as `.dead`) | `letC (writeTVar …) N` |

`newTVar`/`writeTVar` return the index / unit and are FUSED with their `letC` continuation (like
`put`, rung-2b §10.3): the index binds a real value local, the write-unit binds a `.dead` slot.
`readTVar` returns a value (i64-leaver), so it flows the ordinary path. A BARE `newTVar`/`writeTVar`
(tail, not `letC`-fused), a kind-mismatched op (`get`/`raise` on a txn cap), and a free/value target
are all NAMED refusals (fail-loud, invariant #1) — the `Slot` gains a `.txn` variant, and every
routing arm has its mismatch case.

### 3.2 · STUBBED (honest gaps)

1. **Empty-start `Θ = []` only** (all v1 STM surface). A pre-seeded `Θ` is a loud refusal; it needs
   the copy-on-entry snapshot loop (Q1 option C): lay the initial cells into memory at entry, copy
   the whole live region to a shadow region, restore the shadow on abort. A small delta — a memory
   copy loop — not a wall. The empty-start restore is just the length pointer.
2. **Unbounded `Int` → i64.** Inherited from rung-1 (§4.1 of the rung-1 note): TVar cells are i64;
   large-magnitude values wrap where the kernel is exact. Orthogonal to the txn design.
3. **Static `vint` TVar indices in the corpus.** `readTVar`/`writeTVar` emit `(i64.load (8·<idx>))`
   where `<idx>` is any i64 expression, so a computed/variable index already works (the offset math is
   runtime `i64.mul`); the corpus just happens to use literal indices. No new work — noted for honesty.
4. **Generator stays pure.** The 42-seed generator was not extended into txn nesting; the 6 witnesses
   are HAND anchors (like the throws/state legs). A generated txn corpus needs the generator to track
   the txn-cap depth + the newTVar/write index bookkeeping to stay in-fragment.
5. **Proof-grade (§Q3).** No `wexec ≡ Source.eval`; the memory↔`Θ` bijection + the empty-start
   rollback lemma are the two new obligations, both per-former.

---

## 4 · The implementation-lane slice map (deliverable — for the full rung, not this probe)

```
S0  [DONE in this spike]  Slot.txn + the 4 op arms + emitModule (memory 1) + 6 hand witnesses
                          — all through wasmtime == Source.eval (72/72 corpus). LANDABLE as-is.
S1  Generated txn corpus  extend genComp with a txn-cap depth tracker + newTVar/write index model;
                          the 42-seed generator emits in-fragment txn programs (commit + abort nests).
S2  Pre-seeded Θ (opt C)  the copy-on-entry snapshot loop: lay Θ into memory at entry, snapshot the
                          live region, restore-region on abort. Unblocks non-empty-start transactions.
S3  custom (other leg)    a user-clause body as a tail-resume (needs clause-Comp emission — the first
                          `call`); orthogonal to txn, gated separately (§9.6 rung-1 note).
S4  proof-grade           wasm-fragment small-step semantics (extend rung-1's pure machine with
                          memory + try_table/throw_ref) + wexec≡Source.eval for the txn arms:
                          the memory↔Θ bijection + the empty-start rollback lemma.
```

`S0` is this deliverable and is LANDABLE (leaf-additive, gate-green, oracle-checked). `S1`–`S2`
complete the tested rung; `S4` is the eventual proof-grade lift (the pure-arithmetic wasm machine of
§5 of the rung-1 note, extended with memory + the exception opcodes).

---

## 5 · One-glance status

```
DEMONSTRATED  transaction → journal/rollback on wasm (memory heap + catch_all_ref/throw_ref restore)
              6 txn programs incl. A11 abort/rollback == Source.eval on wasmtime 45; corpus 72/72
KEY FINDING   wasm gives the UNWIND free (rung-2 try_table) but NOT memory rollback (mutation is
              destructive) — the kernel's discard-the-frame is an EXPLICIT snapshot-restore; the
              hand-witness proves the restore path fires (heaplen 0, not 1)
DESIGN        Slot.txn = the $heaplen local; heap = linear memory (8·i per cell); rollback = a
              catch_all_ref+throw_ref wrapper INSIDE the throws try_table (re-raises the same exnref)
SCOPE         empty-start `atomically` only (all v1 STM); pre-seeded Θ = a named refusal (copy-loop, S2)
STRATUM       tested (differential vs Source.eval); emitter axiom set [propext]; leaf-additive
STOP-GATE     wasmtime 45 accepts catch_all_ref/throw_ref + memory under `-W exceptions=y` (wasm-3.0)
NEXT          generated txn corpus (S1) → pre-seeded Θ (S2) → custom leg (S3) → proof-grade (S4)
```
