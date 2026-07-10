<!-- note-status: active -->
# Emission rung-1 probe — pure ⊥-row arithmetic → real `.wat`, run on wasmtime

> **Verdict (one sentence).** Rung 1 of ◊5.5 (ADR-0059's "pure → native Wasm") is
> **TRACTABLE and DEMONSTRATED**: a structural emitter over the typed `Comp` turns closed
> ⊥-row integer arithmetic into core-wasm `.wat`, and **four sample programs ran on
> `wasmtime` 45 with values MATCHING `Source.eval`** — the first time bang output has
> executed outside Lean. The load-bearing design finding is **emit from the typed `Comp`,
> NOT from `Code`**: `compile` constant-folds the pure fragment to a single `RET v`, so the
> `Code` path is degenerate (it would emit the interpreter's answer, not a compiled program).

Spike branch `spike-emission-rung1`. Artifacts (all additive/leaf — no proof-bearing file
touched): `Bang/Backend/WasmEmit.lean` (the emitter + `by decide`/`simp` self-tests, axiom
set `[propext]`), `EmitMain.lean` (leaf runner exe `emit-rung1`), `tools/emit-rung1-diff.sh`
(the wasmtime-vs-`Source.eval` differential harness), `scratch/EmitProbe.lean` (the
`compile`-folds-arithmetic finding, `by rfl`).

---

## 1 · The side-by-side — bang output on a real engine (deliverable 2)

```
sample   program                              wasmtime     oracle   verdict
prog0    1 + 2                                       3          3   OK
prog1    let x = 1 + 2 in x * 3                      9          9   OK
prog2    let x = 5 in x + 10                        15         15   OK
prog3    let x = 2*3 in let y = x+4 in y-1           9          9   OK
```

`wasmtime` = `wasmtime run --invoke main progN.wat` (real engine, core wasm 3.0, no GC / no
exceptions / no imports — runs on ANY engine). `oracle` = `Source.eval 1000 progN` (the
kernel reference). Reproduce inside `nix develop`: `bash tools/emit-rung1-diff.sh` (exit 0 =
every module ran with a matching value; a mismatch is a LOUD exit 1).

The emitted `.wat` for `prog1` (`let x = 1 + 2 in x * 3`):

```wasm
(module
  (func $main (export "main") (result i64) (local i64)
    (local.set 0 (i64.add (i64.const 1) (i64.const 2)))
    (i64.mul (local.get 0) (i64.const 3)))
)
```

The de-Bruijn binder `let x = …` becomes a wasm **local** (`local.set 0` / `local.get 0`);
`+`/`*` become native `i64.add`/`i64.mul`; the arithmetic is preserved AS wasm computation,
not precomputed. This is exactly ADR-0059 rung 1 ("pure → native Wasm, engine codegen").

---

## 2 · The hop question — emit from `Comp`, not from `Code` (deliverable 1's SAY-WHY)

The task asked which hop rung 1 wants (`compile → Code`, or directly from the typed `Comp`).
**Answer: the typed `Comp`.** The evidence (`scratch/EmitProbe.lean`, all `by rfl`):

```
compile (binop add (vint 1) (vint 2)) []  =  [RET (vint 3)]           -- FOLDED at compile time
compile (letC (binop add 1 2) (binop mul #0 3)) []
      =  [RET (vint 3), SUBST (binop mul #0 3)]                        -- the residual re-compiles at RUNTIME
```

Two facts kill the `Code` path for a *static* emitter:

1. **`compile` constant-folds closed arithmetic.** `binop op (vint a) (vint b)` collapses onto
   `RET (op.eval a b)` at compile time (AbstractMachine.lean:452, invariant #4 — the calculation
   forces it). So `compile prog0 [] = [RET (vint 3)]`: the *answer*, already computed. Emitting
   wasm from that would produce `(i64.const 3)` — a module that returns the interpreter's result
   and exercises no wasm arithmetic at all. It would "pass" the diff while proving nothing.
2. **`SUBST`/`APP`/`CASE` carry RESIDUAL `Comp`s that `exec` re-`compile`s AT RUNTIME under fuel**
   (AbstractMachine.lean:2095 — `exec … (compile (Comp.subst v N) c) …`). A static emitter cannot
   consume a `SUBST N` instruction without *running the interpreter* to know what `N[v]` compiles
   to. The `Code`/`exec` pair is a fuel-driven CK interpreter, not a static lowering IR.

So the honest rung-1 emitter is a **structural recursion over the typed `Comp`** (`WasmEmit.emitComp`)
that maps each pure former to native wasm, keeping arithmetic as a wasm computation. This matches
CBPV's value/computation split cleanly: `Val` → an i64-leaving expression, `Comp` → the function
body. The `Code`-hop is the RIGHT input for the *proof* (`compile_forward_sim` targets the GC-frame
machine that consumes `Code`); it is the WRONG input for *pure static codegen*, because the pure
grade is exactly where the calculation already collapsed the control structure away.

> **This is not a contradiction with the two-hop architecture.** The verified hop
> (`compile_forward_sim`) proves the *interpreter* `exec ∘ compile` simulates `evalD`. The
> emitter is a THIRD, tested-stratum artifact that lowers the pure grade directly — its oracle
> is `Source.eval` (invariant #1), reached across the engine boundary. See §5 for what a
> proof-grade emitter would instead require.

---

## 3 · The rung-1 instruction / former map (deliverable 3's enumeration)

Because we emit from `Comp` (not `Code`), the map is **former → wasm**, and the calculated-VM
`Instr` column records what the SAME former becomes in the interpreter (for cross-reference):

| `Comp`/`Val` former (pure) | calculated-VM `Instr` | wasm 3.0 emission | status in the spike |
|---|---|---|---|
| `Val.vint n` | (operand of `RET`/`binop`) | `(i64.const n)` | ✅ emitted |
| `Val.vvar i` (de Bruijn) | (operand) | `(local.get $lᵢ)` via a depth→local map | ✅ emitted |
| `Comp.ret v` | `RET v` | the value expression (leaves one i64) | ✅ emitted |
| `Comp.binop {add,sub,mul} v w` | folds → `RET` | `(i64.add/sub/mul …)` | ✅ emitted |
| `Comp.binop div v w` | folds → `RET` | `(i64.div_s …)` | ⚠️ emitted, /0 mismatch (§4) |
| `Comp.binop {lt,eq} v w` | folds → `RET` | sum-encoded bool → **rung-1.5** | ⛔ refused (loud) |
| `Comp.letC M N` | `SUBST N` (runtime recompile) | `(local.set $k …M…)` then `…N…` | ✅ emitted (wasm locals) |
| `Comp.force (vthunk M)` | erases → `compile M` | inline the body (no call) | ◻ stretch (mapped, not emitted) |
| `Comp.lam` / `Comp.app` | `LAMI` / `APP` | wasm `func` + `call` (non-recursive) | ◻ stretch (mapped, not emitted) |
| `Comp.case/split/unfold` | `CASE`/`SPLIT`/`RET` | struct/sum rep → **rung-1.5** | ⛔ refused (loud) |
| `perform`/`handle` | `OP`/`HANDLE`/`THROW`/`UNMARK` | **rung 2/3** (§6) | ⛔ refused (loud) |

**Refusals are fail-loud** (`Emit.unsup <reason>`, invariant #1): an out-of-fragment former is a
NAMED refusal, never a silent wrong emission. The self-tests assert both directions —
`emitModule progN |>.isOk = true` on every pure sample, and `= false` on an effectful/`vunit`
former.

The i64 choice: bang `Int` is unbounded; the spike models it as wasm `i64` (rung-1 samples fit).
A faithful bignum rep is a rung-1.5 item (a boxed/`memory` big-int runtime, or a checked i64 with
overflow→trap); the note flags it, the spike does not chase it.

---

## 4 · What rung 1 STUBBED (honest gaps in the demonstrated slice)

1. **Unbounded `Int` → i64.** Samples fit i64; large-magnitude arithmetic would silently wrap in
   wasm where the kernel is exact. A rung-1.5 fix (bignum runtime, or trap-on-overflow). NOT a
   soundness hole for the demonstrated corpus, but a named scope edge.
2. **`div_s` vs total kernel `div`.** wasm `i64.div_s` **traps** on `/0`; the kernel `BinOp.eval`
   `div` is TOTAL (`a / 0 = 0`, Lean `Int` division — IR.lean:184). So a program dividing by a
   *statically-zero* denominator diverges between emitter (trap) and oracle (0). The spike does not
   emit such a program; a proof-grade emitter must either match the kernel's total div (emit a
   `select` guard: `if d = 0 then 0 else a/d`) or the kernel must adopt a checked `throws`-div.
   Named in ADR-0065's own div comment as a post-v1 `throws` effect.
3. **Comparisons + ADTs are refused, not emitted.** `lt`/`eq` return `boolVal` (`inl unit`/`inr
   unit`, IR.lean:173) — a sum value needing a struct/tag rep; `case`/`split` consume those. That
   is rung-1.5 (still pure ⊥-row, but needs a value rep beyond i64). Deliberately out of the
   one-program scope.
4. **No functions.** `lam`/`app`/`force` are mapped (§3) but not emitted — the stretch. A
   non-recursive call lowers to a wasm `func` + `call`; recursion needs a fuel/stack story. One
   running arithmetic program was the scoped win; five half-mapped features were the anti-goal.
5. **wasmtime `--invoke` is experimental.** Returning an i64 from an exported `main` uses
   wasmtime's `--invoke` (flagged experimental for value-returning funcs). A hardened harness would
   emit a WASI `_start` that prints the result, or a host-driver (node + `WebAssembly.instantiate`).
   The value crosses the boundary correctly today; the invocation ergonomics are stub-grade.

---

## 5 · The verification story — TESTED-stratum spike, and what proof-grade would need

Per the stratification principle (CLAUDE.md): the emitter is the **tested superset**, separated
from the verified core by an explicit seam. Concretely:

- **What is verified today:** nothing about the emitter's *correctness* is proven. The `by
  decide`/`simp` self-tests in `WasmEmit.lean` are STRUCTURAL guards (emission succeeds/refuses on
  the right formers; axiom set `[propext]`) — they do NOT prove `emit(M)` computes `Source.eval M`.
- **What rides the reference:** `tools/emit-rung1-diff.sh` is the differential test — it runs the
  emitted wasm on a real engine and diffs against `Source.eval` (invariant #1, now crossing the
  engine boundary). This is the SAME discipline as the `Agree` battery, one hop further out.
- **What a PROOF-GRADE emitter would require** (the honest what-remains):
  1. A **formal semantics of the wasm fragment** in Lean (a small-step `i64`-stack machine over
     the emitted `Instr` subset — `const`/`add`/`sub`/`mul`/`local.get`/`local.set`), i.e. a
     third abstract machine. This is real work but BOUNDED (the pure fragment is tiny).
  2. A theorem `wexec (emit M) ≡ Source.eval M` for the pure fragment — a forward simulation
     structurally analogous to `compile_forward_sim`, but source-to-wasm-directly rather than
     source-to-GC-machine. The de-Bruijn→local map is the one non-trivial invariant (a binder
     depth ↔ local-index bijection preserved by `letC`).
  3. The differential corpus generalizes to a **fuzzed** `Comp` generator (the `Witness/Fuzz`
     machinery already exists) diffed engine-vs-oracle — the tested rung under the proof.
  The emitter's structural shape (one arm per former, fail-loud refusal) is deliberately chosen so
  that (2) would be a per-former case analysis, not a re-architecture.

---

## 6 · The rung-2 wall visible from here (abort → exceptions)

ADR-0059's rung 2 = `throws → Wasm exception` + `state`/`transaction → tail-call. From the rung-1
vantage the wall is concrete:

- **`throws` → `try_table`/`throw` (wasm 3.0 exception handling).** `compile` emits `HANDLE`/`THROW`/
  `UNMARK`; the kernel's zero-shot abort (discard the inner continuation, resume the handler's saved
  outer continuation with the payload — AbstractMachine.lean:2116) is EXACTLY wasm's exception
  semantics: `throw $tag payload` unwinds to the enclosing `try_table` catch. The identity-keyed
  dispatch (`unwindFind n`) maps to a per-handler-instance tag. This is the engine-independent half
  ADR-0059 calls "for free" — but it needs the SAME emit-from-`Comp` decision (the `HANDLE` `Instr`
  carries a RAW body that `exec` re-compiles at the mint, so a static emitter must recurse the
  `handle`'s `Comp` body under the minted cap, not read `Code`).
- **`state`/`transaction` → tail-call / in-place resume.** One-shot in-place resumption (ADR-0025):
  the handler services `get`/`put` and continues the SAME continuation — a direct call in wasm, no
  reification. The store threads as wasm locals/globals or a `memory` cell.
- **The wall proper:** the emit-from-`Comp` recursion must now track the handler-frame nesting to
  place `try_table` scopes and mint tags, where rung 1 only tracked a locals environment. That is a
  bigger environment (a handler stack, mirroring `HStack`) but still structural. The GENERAL
  (multishot) leg — reified resumptions on the GC-frame chain — stays post-v1 (ADR-0059 §v1/post-v1
  boundary; nothing in v1's three handler forms reifies).

**Rung-1.5 (the smaller next step, pure-only):** comparisons + ADTs — a value rep beyond i64
(`i32` tag + `memory`/`struct` for sums/products) so `lt`/`eq`/`case`/`split` emit. This unblocks
`if`-sugar and boolean-guarded arithmetic while staying ⊥-row (no exceptions yet).

---

## 7 · One-glance status

```
DEMONSTRATED   pure ⊥-row Int arithmetic + let-bindings → core .wat → wasmtime, 4/4 == Source.eval
HOP DECISION   emit from typed Comp (compile folds the pure fragment to RET — Code path degenerate)
STRATUM        tested (differential vs Source.eval); emitter axiom set [propext]; proof-grade = §5
NEXT (pure)    rung-1.5: comparisons + ADTs (i32 tag + memory rep)
NEXT (effect)  rung-2 wall: throws→try_table/throw, state/transaction→tail-call (§6)
LEAF/ADDITIVE  Bang/Backend/WasmEmit.lean · EmitMain.lean · tools/emit-rung1-diff.sh — gate green (755 jobs)
```
