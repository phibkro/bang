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

```wat
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

---

## 8 · Rung-1.5 LANDED (comparisons + guarded div + generated corpus)

> **What landed (2026-07-10).** The two pure-fragment gaps §4 named — the `div_s`/`/0` mismatch and
> comparisons+`case` — are CLOSED, and the 4-program hand corpus is now a **53-program
> differential battery** (4 hand anchors + 7 rung-1.5 witnesses + 42 seed-generated), all
> `wasmtime == Source.eval`. Still the TESTED stratum (emitter axiom set `[propext]`, no proof).

### 8.1 · Guarded div — the reviewer ruling: preserve the kernel's total `div`

The kernel `BinOp.eval div` is **total**, `a / 0 = 0` (Lean `Int` division, IR.lean:184). wasm
`i64.div_s` **traps** on a zero divisor. Proof rides the reference (invariant #1), so the emitter
matches the kernel, NOT the trap — `emitDiv` wraps the divide in a guard:

```wat
(if (result i64) (i64.eqz <divisor>)
  (then (i64.const 0))
  (else (i64.div_s <dividend> <divisor>)))
```

The extra instructions are free (invariant #7, performance second-class). Operands are pure `Val`
expressions (`i64.const`/`local.get` — no side effects, no traps), so the divisor is duplicated in
the `eqz` test and the divide without a scratch local. Corpus witnesses: `div1` (`7/0 ⇒ 0`, static
zero), `div2` (`let d=3-3 in 100/d ⇒ 0`, dynamic zero) — both agree with the oracle. **Residual gap
(unchanged, §4.1):** `i64.div_s` also traps on `INT64_MIN / -1` (signed overflow) — the pre-existing
unbounded-`Int`→i64 edge, orthogonal to `/0`; the corpus stays in the i64-representable range.

### 8.2 · Comparisons + case-on-bool = the wasm `if` (the if-then-else pattern)

The kernel has NO standalone bool — `boolVal false = inl unit`, `boolVal true = inr unit`
(IR.lean:173), and `binop lt/eq` reduces to `ret (boolVal c)`. The surface `if a<b then E₂ else E₁`
is exactly `letC (binop cmp a b) (case (vvar 0) N₁ N₂)`: the comparison binds a `boolVal`, and
`case (vvar 0)` eliminates it (`inl → N₁` else, `inr → N₂` then, Eval.lean:96). The emitter
recognises this **fused** shape and emits a native wasm `if` — the comparison leaves an i32 `0`/`1`,
consumed by the `if` condition:

```wat
(if (result i64) (i64.lt_s <a> <b>)   ;; TRUE(1)=inr → then=N₂ ;; FALSE(0)=inl → else=N₁
  (then <N₂>)
  (else <N₁>))
```

A **bare** comparison (not immediately `case`-eliminated) stays `Emit.unsup` — a `boolVal` has no
standalone i64 rep. The general sum-`case` (arbitrary ADTs) stays out of scope (rung-2).

**The de Bruijn two-binder subtlety (a real finding, caught BY the corpus).** Inside a branch the
kernel context has TWO extra binders over the pre-`letC` scope: index 0 = the `case` unit payload,
index 1 = the outer `letC`-bound `boolVal`. A first-pass emitter that pushed only ONE unusable slot
(`none :: env`) mis-indexed any branch referencing an outer variable — `if3`
(`let x=2+3 in if x<4 then x*2 else x`) diverged (`wasmtime 5` vs oracle `NON-INT-VALUE`) because
the emitter read `x` where the kernel read the `boolVal`. Fix: branch env = `none :: none :: env`
(both payload and boolVal unusable — no i64 rep), and the generator lifts branch bodies by
`Comp.shiftFrom 0` **twice**. `env` is now `List (Option Nat)` — `some l` = a real wasm local,
`none` = a bound-but-unusable slot that fails loud if read. This is the differential test earning
its keep: a value-agreement corpus refuted the first derivation for the price of one run.

### 8.3 · The generated corpus + false-green defenses

`EmitMain.genComp` is a deterministic LCG-seeded structured generator over the emittable fragment
(int atoms, in-scope-only vars ⇒ always closed, arithmetic + guarded div with a forced-zero-divisor
branch, `letC` nesting, the fused `if`). Total (structural fuel recursion — no `partial`, no
inhabited-type obligation). `tools/emit-rung1-diff.sh` runs all 53 emitted → `wasmtime` → diff vs
`Source.eval`, and the false-green defenses the repo's bash conventions demand are all present: the
emit exe prints `EMITTED_COUNT`/`REFUSED_COUNT` footers; the harness ASSERTS `emitted ≥ 50`,
`refused == 0` (a generator drifting out of the fragment fails LOUD, not silently), `.wat`-count ==
emitted, and checked == emitted (no silent skip); `wasmtime`'s exit is captured separately (never a
piped exit code); a mismatch prints the program + both values and exits 1.

### 8.4 · What rung-2 needs next (the wall from here, refining §6)

- **General ADTs (the OTHER half of rung-1.5, deferred).** `lt`/`eq` are handled ONLY in the fused
  `case` shape; arbitrary `inl`/`inr`/`pair`/`fold` + non-fused `case`/`split`/`unfold` still need a
  value rep beyond i64 (an `i32` tag + `memory`/`struct` for sums/products, §6). That unblocks
  bool-VALUED expressions (a bool bound, passed, returned — not just immediately eliminated).
- **`throws → try_table/throw`** (§6, unchanged): the fused-`if` decision generalises — the emitter
  now tracks a de Bruijn→local *and unusable-slot* environment; the handler-frame nesting for
  `try_table` scopes + minted tags is the next environment layer (mirroring `HStack`).
- **Proof-grade (§5, unchanged):** a formal wasm-fragment semantics + a `wexec (emit M) ≡
  Source.eval M` forward simulation. The `if`/`div`-guard arms are per-former case analyses under
  that theorem, not a re-architecture — the structural one-arm-per-former shape is preserved.

```
LANDED (rung-1.5)  guarded div (a/0=0) · comparison+case-on-bool → wasm `if` · 53-program corpus, 53/53 == Source.eval
FINDING            fused-if branches carry TWO kernel binders (payload+boolVal); env = List (Option Nat), branch = none::none::env
STRATUM            tested (differential); emitter defs axiom set [propext] (no sorryAx); leaf-additive (no proof-bearing file)
NEXT (pure)        general ADTs — i32 tag + memory rep (bool-VALUED, non-fused case/split/unfold)
NEXT (effect)      rung-2: throws→try_table/throw (§6), state/transaction→tail-call
```
