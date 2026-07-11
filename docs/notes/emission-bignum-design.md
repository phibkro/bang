<!-- note-status: active -->
# Emission bignum design — full ℤ on the WasmGC path (closing the rung-4/5 i64-wrap gap)

> **Verdict (one sentence).** Ship a **sign-magnitude limb array in base 10⁹** as a new `$bigval`
> subtype of `$val`, with schoolbook add/sub/mul emitted as WasmGC functions — this closes the
> i64-wrap gap the rung-4 note named (`emission-rung4-design.md §2/§5.2`) and ADR-0067 §5 ratified
> ("real-Wasm emission ships bignum first; i64 a later verified optimization"). The core add/mul and
> **decimal readback** are hand-witnessed on wasmtime 45 at a value past 2⁶³
> (`scratch/bignum-limb-add-mul.wat` — A·B = 10000000008999999999, all limbs and the rendered decimal
> string == the Lean oracle). **The load-bearing correctness finding is NOT about width at all:** the
> kernel's `div` is **Euclidean** (`Int.ediv`), and the current emitter emits truncated `i64.div_s` —
> a PRE-EXISTING latent differential bug (`scratch/BignumOracleProbe.lean`), independent of bignum,
> that this lane must fix in the same breath as it touches the arithmetic arms.

Additive to `Bang/Backend/WasmEmit.lean` (`emitModuleGC` + its embedded `$val`-printer runtime). No
kernel/frontend/Spec touch. The machine stays a calc-output (invariant #4): every arm images
`BinOp.eval` (`Bang/Core/IR.lean:188`) over Lean `Int`, not an invented numeric.

---

## 0 · The two findings that reframe the task (refute-first, both witnessed)

**Finding A — the kernel's `div` is EUCLIDEAN, not truncated, not floored.** `BinOp.eval .div a b =
vint (a / b)` and Lean core `Int./` = `Int.ediv` (the remainder is always ≥ 0). Verified for all four
sign cases as compiled `#guard`s (`scratch/BignumOracleProbe.lean`, all green):

| `a / b`      | kernel (ediv) | wasm `div_s` (trunc) | `Int.fdiv` (floor) |
|--------------|:-------------:|:--------------------:|:------------------:|
| `(-7) / 2`   | **−4**        | −3                   | −4                 |
| `7 / (-2)`   | **−3**        | −3                   | −4                 |
| `(-7)/(-2)`  | **4**         | 3                    | 3                  |
| `5 / 0`      | **0**         | traps                | 0                  |

The emitter today (`emitDivGCI`, `WasmEmit.lean:731` and inline `emitDiv:91`) emits `i64.div_s` =
truncated. **This disagrees with the oracle for every negative-operand division** — a live soundness
gap on the i64 fast path, not merely a bignum concern. It has never fired because **no corpus example
divides with a negative operand** (grep: zero `.bang` files use `/` at all). Still: the moment a
`bang run --compiled` program does `(-7)/2`, the compiled path returns −3 while `Source.eval` returns
−4. **This lane fixes div to Euclidean** (correction: after `div_s`, if the truncated remainder is
non-zero and its sign differs from the divisor, adjust the quotient by ∓1 — the standard t→e fixup),
because it is rewriting the div arm for bignum anyway.

**Finding B — sign-magnitude base-10⁹ limbs run correctly on a real engine.**
`scratch/bignum-limb-add-mul.wat` witnesses schoolbook `addMag`/`mulMag` over a WasmGC `(array (mut
i64))` plus decimal readback. For A = 9 999 999 999, B = 1 000 000 001 (A·B = 10000000008999999999,
> 2⁶³ where a plain i64 mul WRAPS): limbs `[999999999, 8, 10, 0]` and the rendered decimal string
`"10000000008999999999"` (20 bytes) both == the Lean oracle. **Base 10⁹ is the key choice** — see §2.

## 1 · The options, priced honestly

| option | rep | per-op cost | code size | div/mod | verdict |
|---|---|---|---|---|---|
| **(a) limb array, always** | `$bigval` = sign + `(array i64)` base 10⁹, EVERY int | mul/add allocate + O(n) loop even for small ints | ~1 struct type + 3–4 wasm fns (~120 lines .wat) | schoolbook long division (a later slice) | **RECOMMENDED** for v1 fidelity |
| **(b) i64 fast-path + spill (smi/V8/JSC)** | `$ival` i64 when it fits, `$bigval` on overflow | fast common case, BUT overflow detect is expensive (no `add.ov` in wasm — see below) | (a) + the overflow-check sequence on every op + a dispatch on `ref.test` per operand | same as (a) + a fits-in-i64 fold | the perf answer; DEFER (ADR-0067 §5, inv#7) |
| **(c) i31ref fast-path** | `$val` = `i31ref` for \|n\| < 2³⁰, boxed/limb otherwise | `i31` avoids the box alloc for tiny ints; `ref.test i31` dispatch | narrower fast band than (b); same spill machinery | same | a refinement of (b); DEFER |
| **(d) do nothing (status quo)** | i64 `$ival`, LOUD trap on overflow | zero | zero | wrong sign for negatives (Finding A) | the gap this lane closes |

**Overflow detection cost in wasm (the reason (b) is deferred, priced not guessed).** wasm has no
carry flag and no `add.overflow`. Signed 64-bit add overflow must be synthesized: `let s = a + b; if
((a ^ s) & (b ^ s)) < 0 then overflowed`. Mul overflow is worse — either a 128-bit widening (wasm has
none) reconstructed from two `i64.mul_high`-less halves, or a post-hoc `s / a == b` check. That is
3–5 extra ops on the hot path of EVERY arithmetic op, plus a per-operand `ref.test $ival` to even
know you're on the fast path. ADR-0067 §5 explicitly orders this AFTER bignum ("i64 as a later
verified optimization … priced when performance is actually observable"), consistent with invariant
#7 (performance second-class). **v1 ships (a).**

**What the WasmGC ecosystem does (reasoned; no in-repo primary source — labelled as such).**
`dart2wasm` and `Kotlin/Wasm` both lower their language `Int`/`BigInt` to a limb array in a GC
`array`, with a small-int fast path (Dart's `_BigIntImpl` uses a `Uint32List` of base-2³² digits;
Kotlin boxes `Long` and defers true bignum to a library). Scheme-to-wasm efforts (Guile-on-Wasm,
Hoot) use fixnum (i32/i61 tagged) + a bignum `array` heap object, the classic (b)/(c) shape. The
consensus rep is **a GC array of unsigned limbs + a sign, small-int fast path optional** — exactly
(a) with (b) as the named perf follow-up. bang's fidelity-first ordering (bignum first) is the
minority-but-principled choice, forced by invariant #1 (proof rides the reference).

## 2 · The representation (recommended)

```wat
(type $bigval (sub $val (struct
  (field $sign i32)               ;; 0 = non-negative, 1 = negative ; zero is ALWAYS (sign 0, empty/[0])
  (field $mag  (ref $limbs)))))   ;; magnitude, base 10^9, LEAST-significant limb first, NO leading zero limbs
(type $limbs (array (mut i64)))   ;; each limb ∈ [0, 10^9)
```

**Base 10⁹ (not 2³² or 2⁶⁴) — three reasons it is load-bearing, all witnessed:**

1. **Decimal readback is a zero-pad concat, not a long-division loop.** The harness compares
   *Lean-`Int` decimal bytes* (`bang run` prints `toString n`). With base 10⁹ each limb is exactly 9
   decimal digits: render the top limb bare, every lower limb `%09d`, concatenate. The witness'
   `$render` does exactly this and produces byte-identical output. Base 2ᵏ would need repeated
   division by 10 over the whole bignum to print — O(n²) and a second bignum-div routine JUST for
   output. **Decimal-out is why base 10⁹ wins for a fidelity-first, differential-tested backend.**
2. **Products fit in i64 with no 128-bit intermediate.** limb·limb < 10¹⁸ < 2⁶³, so `ai * bj + carry
   + acc` stays in unsigned i64 (u63 headroom). Schoolbook mul is plain `i64.mul`/`i64.div_u`/`rem_u`
   — witnessed correct. Base 2³² would also fit; base 2⁶⁴ would NOT (needs mul_high).
3. **Add/sub carry is `%10⁹` / `/10⁹`.** Simple, witnessed.

Cost of base 10⁹ vs 2³²: ~7% more limbs (10⁹ ≈ 2³⁰), i.e. marginally more memory and slightly longer
mul loops. For a fidelity-first v1 with no observed perf pressure that is the correct trade (inv #7).

**Normalization invariant (the differential-critical discipline):** every routine returns a
*normalized* `$bigval` — no leading (most-significant) zero limbs, and canonical zero = `(sign 0, [0])`
(or empty). The witness over-allocates `la+lb` and leaves a top zero limb; the real routines must
**trim** so that `eq` and readback are canonical. `eq` on two normalized magnitudes is a length check
then a limb-wise compare; sign of zero is always 0 (so `−0` is unrepresentable — matches ℤ).

## 3 · The arithmetic arms (each images `BinOp.eval`, invariant #4)

Sign-magnitude means the `$val`-level op dispatches on operand signs, then calls the unsigned
magnitude kernel:

| kernel arm (`BinOp.eval`) | `$bigval` image |
|---|---|
| `.add a b` | same sign → `addMag` + keep sign; opposite → `subMag` of larger − smaller, sign of larger |
| `.sub a b` | `add a (−b)` (negate b's sign) |
| `.mul a b` | `mulMag` magnitudes; sign = `a.sign xor b.sign`; zero result normalizes to sign 0 |
| `.div a b` | **Euclidean** (Finding A): `divMag` (schoolbook long division, unsigned) gives truncated q,r; then apply the sign rule AND the t→e fixup so `0 ≤ r < |b|`; `b = 0 ⇒ 0` |
| `.lt a b` | compare signs first, then magnitudes (reverse for negatives); returns `boolVal` |
| `.eq a b` | sign-equal ∧ magnitude-equal; `boolVal` |

`addMag`, `subMag`, `mulMag` are schoolbook and **witnessed** (subMag is add's mirror; only add/mul
are in the .wat but subMag is the same carry loop with borrow). `divMag` (schoolbook long division —
the hard one) is **NOT yet witnessed** and is scoped LAST (§5).

## 4 · The exact change sites in `WasmEmit.lean` (grounded, not sketched)

The rung-4/5 `$val`-printer runtime ALREADY exists (task #85 landed it): `$emitInt`
(`WasmEmit.lean:1187`) renders one i64 via `div_u`/`rem_u`; `$isIval`/boxing at `boxI`/`unboxI`
(`WasmEmit.lean:728`). The change is a rep swap at those seams:

1. **`$ival` → `$bigval`** everywhere a value is boxed/unboxed. `boxI (i64.const n)` at emit time
   becomes "emit a `$bigval` literal whose `$mag` array is the base-10⁹ limbs of `n`" (compile-time
   limb-splitting in Lean, since `n : Int` is known). `unboxI` disappears — ops take `$bigval` refs.
2. **arithmetic arms** (`WasmEmit.lean:814` binop, `:823` div) call the new `$addBig`/`$mulBig`/
   `$divBig` runtime fns instead of `i64.add`/`i64.div_s`.
3. **`emitDivGCI` (`:731`) → Euclidean** — the t→e fixup, whether or not bignum lands (Finding A).
4. **`$emitInt` (`:1187`) → `$emitBig`** — walk the `$mag` limbs (top bare, rest `%09d`), prepend
   `−` if `$sign`. The witness' `$render`/`$put9`/`$putBare` are the drop-in shape.
5. **the runtime prelude** gains `$addMag`/`$subMag`/`$mulMag`/`$divMag`/`$cmpMag`/`$normalize` — the
   witnessed .wat functions, emitted as a fixed string block alongside the existing `$emitInt` etc.

Nothing else in the pipeline changes: `$sum`/`$pair`/`$clos`/`$env`/effect slots are untouched (a
bignum is just another `$val` subtype the closures/ADTs carry uniformly).

## 5 · Slice map (implement AFTER team-lead ack)

```
B0  Euclidean div fix (STANDALONE, ships first — smallest, closes the live bug)
      emitDivGCI + inline emitDiv → t→e fixup. Add a corpus example that divides negatives
      (e.g. (-7)/2 == -4) to the rung-4/5 diff harness — RED before, GREEN after. Keeps i64 rep;
      no bignum yet. Axioms unchanged. This is a correctness fix independent of the rest.
B1  $bigval rep + literals + readback   swap $ival→$bigval; boxI emits base-10^9 limbs; $emitBig
      walks limbs. NO arithmetic yet — a program that just returns a big literal round-trips to
      decimal. Gate: a literal past 2^63 prints byte-identical to bang run.
B2  add / sub / compare / eq            $addMag/$subMag (witnessed) + sign dispatch + $cmpMag.
      Gate: factorial-style sums, big +/−, ordering with negatives == bang run.
B3  mul                                 $mulMag (witnessed). Gate: factorial past 2^63 — the
      canonical witness (factorial 21 = 51090942171709440000 > 2^63). nqueens stays green (regression floor).
B4  div (LAST, or DEFER loudly)         $divMag schoolbook long division — the un-witnessed, hardest
      routine. If deferred: keep the LOUD trap for div-overflow-into-bignum ONLY (small-int div uses
      the B0 Euclidean i64 path), documented as the one remaining refusal. Div is rare in the corpus
      (zero uses today), so B4-deferred is an honest v1 ship.
```

**Harness extension:** `tools/emit-rung5-print-diff.sh` (or a `-bignum` sibling) gains big-value
programs — factorial-past-2⁶³ is the canonical one. Both-direction, auto-discovering, byte-comparing
`bang run` (Lean-`Int` decimal) against `wasmtime` decimal readback. nqueens = 21004 stays as the
regression floor (it never touches bignum — small ints throughout).

## 6 · What this does NOT do (honest boundary)

1. **No i64 fast-path** — (b)/(c) deferred per ADR-0067 §5 + inv #7. Every int is a limb array in v1;
   small ints pay the box+O(1)-loop tax. Priced when perf is observable, not now.
2. **div (B4) may defer** — schoolbook long division is un-witnessed; if it slips, the LOUD trap
   stays for div-into-bignum only (small-int div is correct via B0). Named, not silent.
3. **Proof-grade** — TESTED stratum (differential vs `Source.eval`), same seam as rungs 1–5. A
   `wexec ≡ Source.eval` over the limb rep needs the post-v1 WasmGC machine (rung-5 S5 refutation:
   `emitModuleGC` is a text emitter with no Lean machine). The limb ROUTINES could be unit-verified
   in Lean against `Int` ops independently — a NAMED future rung, not v1.
4. **`$bigval` in effect slots / TVars / closures** — falls out for free (it's a `$val` subtype;
   `$ref`/`$txcell`/`$env` hold `(ref null $val)`), no extra work, but gate a big-value-through-state
   program to confirm.

## 7 · One-glance status

```
VERDICT       sign-magnitude limb array, base 10^9, as $bigval <: $val; schoolbook add/sub/mul as
              WasmGC fns. Fidelity-first (ADR-0067 §5); i64 fast-path (V8-smi) DEFERRED, priced (§1).
FINDING A     kernel div = EUCLIDEAN (Int.ediv); emitter emits truncated div_s = a PRE-EXISTING
              latent soundness bug (BignumOracleProbe.lean), never fired (no corpus / with negatives).
              Fix as slice B0, standalone, ships first.
FINDING B     base-10^9 limbs witnessed on wasmtime 45: A*B=10000000008999999999 (>2^63), limbs +
              decimal readback == Lean oracle (bignum-limb-add-mul.wat). Base 10^9 makes readback a
              zero-pad concat (the harness compares decimal bytes) — the load-bearing rep choice.
CHANGE SITES  WasmEmit.lean: $ival→$bigval (boxI/unboxI :728), arith arms (:814/:823), emitDivGCI
              →Euclidean (:731), $emitInt→$emitBig (:1187), + a witnessed $addMag/$mulMag/$divMag prelude.
SLICES        B0 Euclidean-div (standalone) · B1 rep+literal+readback · B2 add/sub/cmp/eq · B3 mul
              (factorial past 2^63 = canonical) · B4 div (LAST or defer loudly). nqueens = regression floor.
STRATUM       tested (differential vs Source.eval); emitter axiom set unchanged ([propext]). Leaf-additive.
DEFERRED      i64 fast-path, div long-division (maybe), proof-grade wexec≡eval, limb-routine unit proofs.
WITNESSES     scratch/BignumOracleProbe.lean (ediv oracle) · scratch/bignum-limb-add-mul.wat (add/mul/readback).
```
