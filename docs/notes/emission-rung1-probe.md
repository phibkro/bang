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

---

## 9 · Rung-2 LANDED (throws → Wasm-3.0 exceptions: `try_table`/`throw`)

> **What landed (2026-07-10).** The rung-2 abort leg (ADR-0059's `throws → Wasm exception`) is
> **DEMONSTRATED**: `handle (throws ℓ) M` emits a Wasm-3.0 `try_table`/`throw`, and **7 throws
> programs — caught raise, continuation-discard, normal return, compute-then-return, nested
> inner-catch, nested outer-catch, computed payload — ran on `wasmtime` 45 with values MATCHING
> `Source.eval`.** The corpus is now **60 programs** (53 pure/rung-1.5 + 7 rung-2), all
> `wasmtime == Source.eval`. Still the TESTED stratum (emitter axiom set `[propext]`, no proof).
> The STOP-gate ("does the engine accept exception opcodes?") passed: wasmtime 45 supports
> `try_table`/`throw` behind the `-W exceptions=y` feature flag (structurally fine — see §9.3).

### 9.1 · The kernel→wasm mapping — abort IS `try_table`/`throw`

The kernel's zero-shot `throws` (Eval.lean `Source.step` + Dispatch.lean `dispatchOn`) is EXACTLY
wasm exception semantics, confirmed against `scratch/U5bSpine.lean`'s composition lemmas:

| kernel step (`Source.step` / `dispatchOn`) | wasm emission |
|---|---|
| `handle (throws ℓ) M`: mint fresh id `g`, push `handleF g`, run `subst (vcap g ℓ) M` | `(block $hₜ (try_table (result i64) (catch $exnₜ $hₜ) <emit M>))` |
| caught raise (`dispatchOn` throws arm): discard `Kᵢ`, deliver payload `w` to `Kₒ` (`ret w`) | `throw $exnₜ (emit v)` → catch branches to `$hₜ` with the payload as block result |
| normal return (`handleF _ _ :: K, ret v ↦ K, ret v`, handler-return = identity) | body value flows out of the `try_table` = the block result (no throw) |

The catch-target `$hₜ` is a `block` WRAPPING the `try_table`, whose result type is the body's i64.
On a caught `throw` the payload is delivered as that block's result; on normal fall-through the body's
value IS that result — one uniform result type, so both outcomes leave one i64 (verified on wasmtime,
§9.4). This is the "engine-independent half ADR-0059 calls 'for free'" made concrete.

### 9.2 · The frame-stack design — the de-Bruijn env IS the handler stack (the rung-2 wall, resolved)

§6 named the wall: "the emit-from-`Comp` recursion must now track the handler-frame nesting to place
`try_table` scopes and mint tags, where rung 1 only tracked a locals environment." The resolution
is the SAME move rung-1.5 made for the two-binder subtlety, generalized: **one unified de-Bruijn
environment** (`emitVal`/`emitComp` take `List Slot`), because BOTH binders bind index 0 —

```
inductive Slot | val (l : Nat)   -- letC binder ⇒ wasm LOCAL l
                | cap (t : Nat)   -- handle(throws) binder ⇒ wasm exception TAG t
                | dead            -- case-on-bool payload (rung-1.5 unusable slot)
```

`handle (throws ℓ) M` (ADR-0054: `handle` binds a capability at index 0 in `M`, like `lam`) pushes
`.cap t :: env` where `t = nextTag` is minted by descent; `letC` pushes `.val next :: env`. A raise
`perform (vvar i) "raise" v` reads `env[i]`: a `.cap t` slot emits `throw $exnₜ`; a `.val`/`.dead`
slot (or a non-`raise` op) is `unsup` — FAIL-LOUD, never a wrong `throw`. **The de-Bruijn env IS the
`HStack` mirror**: a cap-slot per open `handle`, threaded on the SAME recursion as the locals — so
tag-minting needed no separate stack, just a third slot variant + a `nextTag` counter (the emit
return became `Emit × maxLocal × maxTag`).

**Tag-minting choice: one distinct tag per `handle` frame** (not one global tag). Justification: a
`try_table (catch $exnₜ $hₜ)` catches ONLY tag `t`, so `throw $exnₜ` unwinds to exactly the
lexically-enclosing handle that minted `t` — **tag identity IS the wasm image of identity-keyed
`idDispatch`** (the cap names its lexically-enclosing handler, ADR-0052/0054). This is what makes the
nested cases correct WITHOUT any runtime identity counter: `thr4` (inner `vvar 0` → inner tag, inner
catch) vs `thr5` (inner body `vvar 1` skips the inner cap-slot → outer tag → `throw $exn0` propagates
PAST the inner `try_table (catch $exn1)` to the outer catch) both matched the oracle (5 and 8). A
single global tag would MIS-route `thr5` (the inner catch would swallow the outer-bound raise).

This is the **HANDLE-defer-recompile idiom's static shadow**: `compile` can't read a label from a
`vvar` cap statically, and mints the id at exec-time; the STATIC emitter likewise can't see a runtime
`vcap`, but it mints the wasm TAG structurally by descent — the tag plays the role of the identity `g`,
and the de-Bruijn binder position (not a minted value) is what `perform` routes on.

### 9.3 · The tag-minting + engine-flag choices (deliverable 3's SAY-WHY)

- **Tag rep: `(tag $exnₜ (param i64))` per minted frame.** Each abort carries one i64 payload (the
  raise value), matching bang's rung-2 i64 fragment. `emitModule` declares `numTags` such tags at the
  module head; a pure/rung-1.5 program mints ZERO tags, so its module is byte-identical to the rung-1
  form — the extension is purely ADDITIVE (no pure module changed a byte).
- **wasmtime flag: `-W exceptions=y`.** wasmtime 45 gates the exception-handling proposal behind this
  feature flag (it is Wasm-3.0 CORE but not on-by-default yet). The flag is INERT for pure modules, so
  ONE invocation covers the whole 60-program corpus. Added to `tools/emit-rung1-diff.sh` with a comment.
  This is the STOP-gate the brief named: exceptions are STRUCTURALLY supported (a hand-written
  `try_table`/`throw` returning its payload ran clean), just behind a flag — NOT a structural rejection.

### 9.4 · The side-by-side — throws output on a real engine

```
sample   program                                              wasmtime   oracle   verdict
thr0     handle throws { raise 7 }                                    7        7   OK   (caught, payload delivered)
thr1     handle throws { let _ = raise 7 in 99 }                      7        7   OK   (continuation discarded)
thr2     handle throws { 42 }                                        42       42   OK   (normal return)
thr3     handle throws { 3 + 4 }                                      7        7   OK   (compute then normal return)
thr4     handle throws { handle throws { raise@inner 5 } }            5        5   OK   (inner catches)
thr5     handle throws { handle throws { raise@outer 8 } }            8        8   OK   (throw skips inner try_table)
thr6     handle throws { let x = 6*7 in raise x }                    42       42   OK   (computed payload, cap@idx1)
```

The emitted `.wat` for `thr1` (raise discards the `let`-continuation):

```wasm
(module
  (tag $exn0 (param i64))
  (func $main (export "main") (result i64) (local i64)
    (block $h0 (result i64)
      (try_table (result i64) (catch $exn0 $h0)
        (local.set 0 (throw $exn0 (i64.const 7)))    ;; throw unwinds BEFORE the local.set/99 run
    (i64.const 99)))))
```

The `throw` sits where the `letC`-bound computation would leave its value; because `throw` is
stack-polymorphic (produces the empty/unreachable result), wasm type-checks it as the `local.set`
operand AND unwinds before the set fires — so the `local.set 0 … (i64.const 99)` continuation is
DISCARDED exactly as the kernel's `dispatchOn` throws-arm discards `Kᵢ` (result 7, not 99). The
differential test earns its keep again: this is subtle, and wasmtime confirmed it.

### 9.5 · Scope + what rung-2 STUBBED (honest gaps)

- **`throws`/`raise` ONLY.** `state`/`transaction`/`custom` handlers, and any non-`raise` op
  (`get`/`put`/`newTVar`/…), stay `unsup` (loud). The resumptive handlers are the OTHER rung-2 leg
  (state/transaction → tail-call / in-place resume, §6) — a different wasm shape (thread the store as
  locals/globals + a direct call, no `try_table`), deliberately out of this abort-only slice.
- **Generator stays pure.** The 42-program seed generator was NOT extended into effect nesting; the 7
  throws witnesses are HAND anchors. A generated throws corpus (random handle-nesting + in-scope cap
  targets) is a cheap next step but needs the generator to track the cap-frame depth (mirror of the
  emitter's `Slot` stack) to stay in-fragment.
- **Forwarding a raise to a MISMATCHED-kind or ESCAPED cap is out of fragment.** The minimal fragment
  emits only raises caught by a lexically-enclosing `throws` handle (the `handle_throws_caught`/
  `_forward` composition lemmas' caught case). A cap escaping its handler (`escapedCap`) has no static
  wasm image here — post-v1 scoped-cap types make it untypeable anyway.
- **Proof-grade (§5, unchanged).** No `wexec (emit M) ≡ Source.eval M` theorem; the throws arms would
  be per-former cases under it (the `try_table` frame ↔ `handleF` frame is the one new invariant — a
  tag-identity ↔ handler-identity bijection, the static analog of `WellCounted`/`StratFresh`).

### 9.6 · The rung-3 wall from here

- **state/transaction → tail-call (the OTHER rung-2 leg).** One-shot in-place resumption (ADR-0025):
  the handler services `get`/`put`/TVar ops and continues the SAME continuation — a direct call in
  wasm, store threaded as locals/globals/`memory`. NO `try_table` (no unwind); the emit env grows a
  RESUMPTIVE frame variant carrying the store cells. This is the tractable next slice.
- **custom (user effects) → tail-call over a clause table.** `dispatchOn`'s custom arm is `state`'s
  resume with USER clause logic; the wasm image is the same tail-resume shape with the clause body
  emitted as the continuation. Gated on the resumptive leg landing first.
- **general (multi-shot) → the GC-frame chain (post-v1).** Reified resumptions on the WasmGC
  frame-chain (ADR-0059 §v1/post-v1). Nothing in v1's three handler forms reifies, so this stays
  post-v1; the WasmFX `switch`/`resume` fast-path plugs in once standardized.

```
LANDED (rung-2)   throws → try_table/throw (abort → exceptions) · 60-program corpus (53 pure + 7 throws), 60/60 == Source.eval
DESIGN            de-Bruijn env IS the handler stack: Slot = val l | cap t | dead; one tag per handle frame = tag-identity = idDispatch
STOP-GATE PASSED  wasmtime 45 accepts try_table/throw behind `-W exceptions=y` (Wasm-3.0 core, feature-flagged, not structural)
STRATUM           tested (differential); emitter defs axiom set [propext] (no sorryAx); leaf-additive (WasmEmit.lean/EmitMain.lean/harness)
NEXT (effect)     state/transaction → tail-call (in-place resume, no unwind) — the tractable rung-2 leg; then custom; general = post-v1 GC-chain
```

---

## 10 · Rung-2b LANDED (state → in-place resume: the store cell is a mutable wasm LOCAL)

> **What landed (2026-07-10).** ADR-0059's OTHER rung-2 leg — `state → tail-call / in-place resume` —
> is **DEMONSTRATED**: `handle (state ℓ s₀) M` maps the store cell to a mutable wasm **local**, `get`
> reads it (`local.get`), `put` writes it (`local.set`), and execution continues STRAIGHT-LINE — no
> `try_table`, no unwind. **6 state programs — get-only, put-then-get, arithmetic-around-get, computed
> put-payload, read-modify-write, normal-return — ran on `wasmtime` 45 with values MATCHING
> `Source.eval`.** The corpus is now **66 programs** (53 pure/rung-1.5 + 7 throws + 6 state), all
> `wasmtime == Source.eval`. Still the TESTED stratum (emitter axiom set `[propext]`, no `sorryAx`).
> **The STOP-gate the brief named — "do state ops need dispatch context the static tree lacks?" —
> passed: they do NOT. One handler per label, and the cap slot's de-Bruijn POSITION identifies the
> cell. No id-vs-label context is needed at emit time (§10.2).** These are CORE wasm (locals only) —
> no engine feature flag, unlike the throws leg.

### 10.1 · The kernel→wasm mapping — state RESUMES (no abort), so the cell is a mutable local

The derivation is forced by `dispatchOn`'s `.state` arm (Dispatch.lean:133) + handler-return-identity
(Eval.lean:65). Unlike `throws` (which ABORTS — discards `Kᵢ`), `state` RESUMES `Kᵢ` on both ops:

| kernel step (`dispatchOn` `.state ℓ' s` arm) | wasm emission |
|---|---|
| `handle (state ℓ s₀) M`: mint id `g`, push `handleF g (state ℓ s₀)`, run `subst (vcap g ℓ) M` | mint local `l`; `(local.set l <emit s₀>)` then `<emit M under .state l :: env>` — body value flows out |
| `get`: `some (Kᵢ ++ handleF n (state ℓ' s) :: Kₒ, .ret s)` — RESUME `Kᵢ` with `s`, cell unchanged | `(local.get l)` — an i64-leaving expression; the surrounding wasm IS the resumed `Kᵢ` |
| `put v`: `some (Kᵢ ++ handleF n (state ℓ' v) :: Kₒ, .ret .vunit)` — RESUME `Kᵢ` with UNIT, cell now `v` | `(local.set l <emit v>)` — a STATEMENT; then the continuation runs (fused `letC put; N`, §10.3) |
| normal return (`handleF _ _ :: K, ret v ↦ K, ret v`) | body value flows straight out (no block, no catch) |

Because RESUME reinstalls the frame with the threaded store and continues the SAME continuation, there
is **nothing to unwind** — the "in-place resume" is literally: the store lives in a wasm local, and the
`Kᵢ` the kernel resumes is the code that textually follows in the emitted function body. This is exactly
ADR-0059's "one-shot in-place resumption (ADR-0025) … a direct call in wasm, no reification." Here the
`state` fragment needs not even a call — a `letC`-threaded local sequence suffices (a `custom` clause
body would be the first thing to need a real tail-call; §10.5).

The `Slot` type gains a fourth variant, mirroring the `.cap` move for throws:

```
inductive Slot | val l    -- letC binder ⇒ wasm LOCAL (rung 1)
                | cap t    -- handle(throws) binder ⇒ exception TAG (rung 2)
                | state l  -- handle(state) binder ⇒ wasm LOCAL holding the store cell (rung 2b) ← NEW
                | dead     -- case-payload / put's unit result (no i64 rep)
```

A `perform (vvar i) op _` routes on `env[i]`: `.state l` + `"get"` ⇒ `(local.get l)`; `.state l` +
`"put"` ⇒ `(local.set l …)` (fused, §10.3). A KIND MISMATCH (`"raise"` on a `.state`, `"get"` on a
`.cap`) is `unsup` — FAIL-LOUD, never a wrong read/throw, the static shadow of `idDispatch`'s fail-loud
`handlesOp` guard.

### 10.2 · The STOP-gate answered — labels ARE sufficient; no id-vs-label context at emit time

The brief flagged the risk: "if state ops in the typed `Comp` require dispatch context the static tree
lacks (the id-vs-label question at emit time)." **They do not, for the minimal fragment.** The reason is
the SAME as throws: the emitter routes a `perform` by its cap's **de-Bruijn binder position**, not by a
runtime identity or a label. `handle (state ℓ s₀) M` binds the cap at index 0 in `M` (ADR-0054, like
`lam`); a `get`/`put` names it by `vvar i`; `env[i] = .state l` gives the cell's local. One `handle` per
label in the fragment means the binder position uniquely picks the frame — exactly the "tag-identity =
`idDispatch`" argument (§9.2), now "local-identity = `idDispatch`." The emitter never reads a label to
dispatch — the cell local `l` plays the role of the runtime identity `g`, assigned by structural descent.

**The de-Bruijn-shift finding (caught BY the corpus, the differential test earning its keep again).**
A `put`'s continuation is subtle: `put` returns UNIT and resumes `Kᵢ`, and in the surface `let _ = put v
in N` the `letC` binds that unit at index 0 of `N`. So **the cap that was `vvar i` before the put is
`vvar (i+1)` inside `N`** — the whole env shifts by one across a `put`. The refute-first oracle probe
(now `EmitMain.rung2bSamples`, run against `Source.eval` compiled) confirmed this directly: the
put-then-get witness `stt1` is STUCK if the get names `vvar 0` (that binds the put-unit), and correct
only at `vvar 1`. The emitter's fused `letC (put) N` arm pushes `.dead :: env` for `N` (the put-unit is
unusable, no i64 rep) — identical to the case-payload treatment — so the shifted indices land correctly.
`stt4` (read-modify-write) exercised three threaded locals (cell, `x=get`, `y=x+1`, `put y`, `get ⇒ 6`).

### 10.3 · Why `put` is FUSED with its `letC` continuation (the one asymmetry with `get`)

`get` returns a VALUE (`ret s`), so it slots anywhere an i64 is expected — `let x = get in x + 5` flows
through the ORDINARY `letC m n` arm (emit `get` into a fresh local, run `n`). `put` returns UNIT (`ret
.vunit`) — which has **no i64 rep** — so it cannot be a bare i64-leaving expression. The emitter handles
`put` ONLY in the fused shape `letC (perform (vvar i) "put" v) N`: emit `(local.set l <emit v>)` as a
STATEMENT, then emit `N` under `.dead :: env`. A **bare** `put` (a `put` in tail position, returning
unit as the program's answer) is `unsup` — it would leave unit where the module's `result i64` demands
an int, out of the int fragment (and a unit-returning program is `NON-INT-VALUE` to the oracle anyway).
This mirrors rung-1.5's bare-comparison refusal: an op whose result has no standalone i64 rep is
emittable only in the FUSED elimination shape that consumes it.

### 10.4 · The side-by-side — state output on a real engine

```
sample   program                                                    wasmtime   oracle   verdict
stt0     handle state(5) { get }                                            5        5   OK   (read initial cell)
stt1     handle state(0) { let _ = put 7 in get }                           7        7   OK   (write then read; cap idx1 in cont)
stt2     handle state(10) { let x = get in x + 5 }                         15       15   OK   (arithmetic around get)
stt3     handle state(0) { let v = 3*4 in put v; get }                     12       12   OK   (computed put payload)
stt4     handle state(5) { let x=get; let y=x+1; put y; get }               6        6   OK   (read-modify-write)
stt5     handle state(99) { 20 + 22 }                                      42       42   OK   (normal return, cell unread)
```

The emitted `.wat` for `stt4` (read-modify-write — three threaded locals, all straight-line, no unwind):

```wasm
(module
  (func $main (export "main") (result i64) (local i64) (local i64) (local i64)
    (local.set 0 (i64.const 5))              ;; cell l=0 := s₀ (=5)
    (local.set 1 (local.get 0))              ;; x := get      (local 1)
    (local.set 2 (i64.add (local.get 1) (i64.const 1)))  ;; y := x+1  (local 2)
    (local.set 0 (local.get 2))              ;; put y  — write the CELL local 0
    (local.get 0)))                          ;; get    — read it back ⇒ 6
```

Local `0` is the state CELL (written by both the init and each `put`); locals `1`/`2` are ordinary
`letC` binders. `get`/`put` are plain `local.get`/`local.set` of the cell — the "in-place resume" made
concrete: **no `try_table`, no `block`, no `throw`; the store never unwinds because state never aborts.**
A pure/throws program mints ZERO state locals beyond its own, so this extension is purely ADDITIVE.

### 10.5 · Scope + what rung-2b STUBBED (honest gaps)

- **`state`/`get`/`put` ONLY, single cell.** `transaction` (multi-cell STM) and `custom` (user effects)
  stay `unsup` (loud). A `put` reached OUTSIDE the fused `letC` (bare unit tail) is refused (§10.3).
- **`put` param is READ on resume, never captured.** v1 state is one-shot in-place (ADR-0025), which is
  what the mutable-local model gives. A multi-shot resume (re-entering `Kᵢ` twice with different stores)
  would need the store REIFIED, not a single mutating local — post-v1 GC-chain (§9.6), out of v1's three
  handler forms (none reifies).
- **Generator stays pure.** The 42-seed generator was NOT extended into state nesting; the 6 state
  witnesses are HAND anchors (like the 7 throws). A generated state corpus needs the generator to track
  the cap-frame depth AND the put-shift (mirror of the emitter's `Slot` stack) to stay in-fragment.
- **Proof-grade (§5, unchanged).** No `wexec (emit M) ≡ Source.eval M`; the state arms would be
  per-former cases under it. The one new invariant: a `.state l` slot ↔ a store cell whose value at each
  program point mirrors the kernel's `handleF n (state ℓ' s)` payload — a local-value ↔ store-value
  bijection preserved by `get` (read, no change) and `put` (write). Straight-line (no reification) makes
  this the SIMPLEST arm to prove of the three effect legs.

### 10.6 · What the store-as-a-local design implies for TRANSACTION (note-only analysis)

`transaction ℓ Θ` (Dispatch.lean:143) is the MULTI-CELL generalization of `state`: `Θ : List Val` is the
transaction heap, `newTVar` APPENDS (allocation, returns the new index), `readTVar`/`writeTVar`
index/update a cell — and it RESUMES exactly like `state` (reinstalls a deep frame with the threaded
`Θ'`, ADR-0025 pattern). So the naive wasm image is the state design SCALED UP: **the heap is a block of
wasm `memory` (or an array of locals/globals), `readTVar i` = a load, `writeTVar i w` = a store,
`newTVar v` = bump a length pointer + store.** The resumptive (commit) path is straight-line, same as
state — no unwind.

**But the ROLLBACK question is the real wall, and the store-as-mutable-cell design does NOT solve it for
free.** The kernel's rollback is elegant (Dispatch.lean:139 comment): an abort is a zero-shot `throws`
that ESCAPES the transaction frame, so the threaded `Θ'` is discarded WITH the frame and never commits —
allocations survive (the heap's append-only growth) but writes vanish. In wasm, the transaction body is
inside a `try_table` (the abort leg, §9), and a `throw` unwinds control to the catch — **but a
`local.set`/`memory.store` already executed inside the body is NOT rolled back by the unwind.** wasm has
no transactional memory: mutation is destructive-in-place. So a faithful `transaction` emitter needs ONE
of:

  1. **A JOURNAL (write-set).** Buffer `writeTVar`s in a side structure (a wasm `memory` region keyed by
     TVar index), and only APPLY them to the base heap on the commit path (fall-through past the
     `try_table`); on the abort path (catch), DROP the journal. This is the classic STM implementation,
     and it maps cleanly: the journal is a second `memory` block, commit = a copy loop, abort = a
     pointer reset. It is MORE code than state but structurally the SAME idioms (memory + a length).
  2. **A COPY-ON-ENTRY snapshot.** Snapshot the heap into a scratch region at `handle` entry; on abort,
     restore from the snapshot. Simpler to state, costlier per-transaction (whole-heap copy); the write
     path stays destructive so `readTVar` needs no journal indirection. Invariant #7 (performance
     second-class) says this is an acceptable v1 baseline.
  3. **RE-USE the throws unwind + re-execute** — NOT viable: the kernel does not re-execute, it discards;
     and wasm mutation is not idempotent under re-entry.

The honest verdict: **transaction is NOT a small delta on state.** State rides on wasm's native mutable
local because state never rolls back (its only control move is resume-in-place). Transaction ADDS the
abort leg's unwind (which rung-2 already emits) OVER a mutable heap that MUST be made transactional by an
explicit journal/snapshot — the piece wasm gives for free is the unwind (the `try_table`/`throw` control
flow), NOT the memory rollback. That journal is rung-3 CODE (a real slice, tractable via memory + a
write-set), not a note. **The state leg proves the resume half; the transaction leg's novelty is entirely
in the rollback half, and it is the journal that the store-as-a-local design leaves unsolved.**

### 10.7 · The honest boundary to rung-3 (the wall from here)

- **transaction → journal/snapshot over `memory`** (§10.6): the resume half is state-scaled-to-`memory`;
  the abort half re-uses rung-2's `try_table`, but the memory ROLLBACK needs an explicit write-set. The
  tractable next slice, but genuinely more than state.
- **custom (user effects) → tail-call over a clause table** (§9.6, unchanged): the resume shape is
  state's, but the resumed value is a USER CLAUSE BODY (a `Comp`), not a hardcoded `get`/`put` result. So
  custom needs the clause `Comp` emitted as the continuation — the FIRST arm that needs a real wasm
  `call` (or an inlined body), because the clause computes before resuming. Gated on state landing (it
  did) + the clause-emission machinery.
- **general (multi-shot) → the GC-frame chain (post-v1)** (§9.6, unchanged): reified resumptions; nothing
  in v1's three handler forms reifies, so this stays post-v1 (WasmFX `switch`/`resume` fast-path).

```
LANDED (rung-2b)  state → in-place resume (store cell = mutable wasm LOCAL) · 66-program corpus (53 pure + 7 throws + 6 state), 66/66 == Source.eval
DESIGN            Slot gains `state l`; get = local.get, put = local.set (fused letC); NO try_table/unwind (state RESUMES, never aborts)
STOP-GATE PASSED  no id-vs-label context needed at emit time — cap de-Bruijn POSITION picks the cell (one handle/label); local-identity = idDispatch
FINDING           a `put`'s letC-continuation shifts the cap index by one (put-unit binds idx0) — env = .dead :: env in the cont; caught by the oracle probe
STRATUM           tested (differential); emitter defs axiom set [propext] (no sorryAx); leaf-additive (WasmEmit.lean/EmitMain.lean/harness)
TRANSACTION       NOT a small delta: the resume half scales to `memory`, but the ABORT half needs an explicit JOURNAL/snapshot — wasm mutation is destructive, the unwind does not roll back memory (§10.6)
NEXT (effect)     transaction (journal over memory) → custom (clause body as tail-call) → general = post-v1 GC-chain
```
