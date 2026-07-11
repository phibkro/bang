<!-- note-status: active -->
# Emission rung-4 design — closures + ADTs + recursion on WasmGC (the "nqueens compiles" rung)

> **Verdict (one sentence).** Rung 4 of ◊5.5 is **DEMONSTRATED**: the pure λ + ADT + recursion
> fragment lowers to **WasmGC** (ADR-0059's `general` slot), and **10 whole example programs —
> including the roadmap-named milestone `nqueens = 21004` — emit to `.wat` and run on `wasmtime` 45
> with values MATCHING `Source.eval`**. This is the first bang program with closures, generic ADTs,
> and deep recursion executing OUTSIDE Lean — the static-distribution artifact the distribution
> survey named. The load-bearing finding: **recursion is not a new instruction — it FALLS OUT of the
> μ-knot** (`let rec` = `Rec = μX.Thunk(X→T)`, ADR-0073). Emitting `fold`/`unfold`/`force`/`app`
> faithfully IS emitting recursion; the machine stays an OUTPUT of the calculation (invariant #4).

Additive to the rung-1/2/3 leaf (`Bang/Backend/WasmEmit.lean` — a SEPARATE `emitModuleGC`, the inline
emitter + its 72-corpus stay byte-identical and green). Emitter axiom set unchanged: `emitModule` and
`emitModuleGC` both `[propext]` (the `partial` closure-converting recursion adds NO `sorryAx`/`Classical`).

---

## 1 · The wall rung 4 had to break

The rung-1/2/3 emitter is a STATIC inline structural recursion: every former flattens into `$main`'s
body with a compile-time de-Bruijn env of `Slot`s. That model **cannot express recursion** — the
μ-knot applies itself under `force`/`unfold` an unbounded number of RUNTIME times; an inline emitter
that unfolded it would not terminate at compile time (exactly the rung-1 note §4 wall: "SUBST/APP
carry residual Comps `exec` re-compiles at runtime — a static emitter can't consume them without
BEING the interpreter").

**The DERIVED answer** (invariant #4): the kernel reduces closures/ADTs by SUBSTITUTION into RESIDUAL
Comps (`evalD`, AbstractMachine.lean:263-357):

| kernel reduction | rung-4 wasm image |
|---|---|
| `force (vthunk M) ↦ M` | run the closure with a dummy arg (`call_ref`) |
| `app (lam N) v ↦ N[v]` | `call_ref` the closure, arg prepended to its env |
| `case (inl v) N₁ _ ↦ N₁[v]` | branch on the `$sum` tag; bind the payload |
| `split (pair v w) N ↦ N[v][w]` | project `$pair` fields; bind both |
| `unfold (fold v) ↦ ret v` | erase (identity) |

"Reduce a residual Comp at runtime" faithfully imaged = **a REAL CALL**. Each `lam`/`vthunk`
lambda-lifts to a top-level wasm function; `app`/`force` are `call_ref` through a closure GC-struct;
recursion runs on the WASM CALL STACK, exactly as `exec` re-`compile`s under fuel. This IS ADR-0059's
`general → WasmGC-frame-chain runtime` slot (memory-management survey: closures = the only heap
escapers, WasmGC IS the heap).

## 2 · The value representation (design question 1) — decisions

`$val` = a uniform GC reference supertype (open `(sub (struct))`), so lambdas are polymorphic (`List
a` is generic; closures pass values uniformly). Concrete subtypes:

| bang value | WasmGC rep | note |
|---|---|---|
| `vint n` | `(struct $ival (field i64))` — **BOXED i64** | see bignum decision below |
| `inl v`/`inr v` | `(struct $sum (field $tag i32) (field $payload (ref null $val)))` | tag 0 = inl, 1 = inr |
| `pair a b` | `(struct $pair (field (ref null $val)) (field (ref null $val)))` | |
| `fold v` | **ERASES** (IR.lean:106 — no runtime tag) | `unfold` = identity; the μ-knot adds no wrapper |
| `vthunk M`/`lam M` | `(struct $clos (field $code (ref $fn)) (field $env (ref null $env)))` | captures the enclosing env |
| `boolVal` | `$sum` (`true = inr unit` tag 1, `false = inl unit` tag 0) | a comparison emits it directly — **no fusion needed** (unlike the inline emitter's bare-bool wall) |

**Bignum decision (fidelity-first, both priced).** bang `Int` is unbounded ℤ; the reference is exact.
Rung 4 is **i64-RANGE with a documented LOUD deviation** — the SAME gate shape as guarded-div (rung
1.5): a value outside [−2⁶³, 2⁶³) wraps where the kernel is exact. Priced against **full bignum** (a
GC-array limb rep + add/mul/compare routines): the array rep is the fidelity-exact form and the right
rung-5 item, but it buys nothing for the rung-4 corpus (nqueens' answer 21004, boards of small ints,
list lengths — all decisively in i64 range) at the cost of a bignum runtime. **Verdict: i64 now, full
bignum a NAMED rung-5 refusal.** (Matches the rung-1 note §4.1 gap, now carried into the boxed rep.)

## 3 · Closures + the calling convention (design questions 2, 3)

**Environment = a cons-list of values** (`$env`, innermost binder first): `(struct $env (field $hd
(ref null $val)) (field $tl (ref null $env)))`. Every binder (letC, lam-param, case-payload,
split-fst/snd) PREPENDS its value into a FRESH wasm local; `vvar i` = walk `$tl` i times (`$lookup`).
This is a uniform de-Bruijn → env-list — **no per-lambda env struct, no free-var minimization**. A
lifted function receives its captured env as param 0 and prepends its argument; `$main` starts null.

**Thunk ≠ lam — the one subtlety that bites.** The kernel treats them differently: `force (vthunk M)
↦ M` introduces NO binder (M's `vvar 0` is the first CAPTURED var), whereas `app (lam N) v ↦ N[v]`
makes index 0 the argument. So a lam's lifted fn prepends its arg to the captured env; a thunk's runs
the body under the captured env DIRECTLY (its arg param is a `force`-supplied dummy, ignored). Getting
this wrong shifts every index by one inside every thunk — the μ-knot's `unfold`/`force`/`app` then
`ref.cast` a non-closure and trap. (This was the one real bug found in the spike; the fix is the
`isThunk` flag in `emitCloVal`.)

**Currying (design question 3): curried chains, NOT tupled dispatch.** The elaborator emits
`lam(lam(lam …))` and `app(app(app(force f) a) b) c` (the nqueens dump confirms it). The emitter
follows the calculation — each `lam` is one closure, each `app` one `call_ref` — rather than imposing
a tupled convention. This is the derive-don't-patch choice: the machine mirrors the residual-Comp
shape the kernel produces, not a hand-picked ABI.

**The `let rec` knot maps DIRECTLY.** `Rec = μX.Thunk(X→T)`, self-knot `letC (unfold (vvar 0)) (app
(force (vvar 0)) (fold (vvar 0)))` (buildLetRec, TypeCheck.lean:2400) — `fold`/`unfold` erase,
`force`/`app` are `call_ref`s, the `#95`-hardened `fold (vvar 0)` self-argument re-wraps the LOCAL
unfolded binding (no growing free `sv` copy). No recursive struct fixup, no funcref-table: WasmGC's
closure struct capturing the enclosing env, plus the μ-knot's own re-construction each level, is the
whole recursion story. Measured: nqueens (5906 recursive `solve`/`safeAt` calls for n=4,5,6) runs in
< 0.2s on wasmtime.

**LOCALS.** One monotone counter per function; each fresh local records its wasm TYPE (`env`-ref or
`val`-ref) so declaration is in index order with no offset arithmetic or collisions. Statement-prefixed
sequences (`local.set …` then a value) are wrapped in `(block (result (ref null $val)) …)` — a single
value expression, so nesting (an `app` whose callee is itself an `app`) composes without a void
`local.set` in operand position (the wasm folded-form rule).

## 4 · The spike — 10 programs on a real engine (the deliverable that matters)

`bash tools/emit-rung4-diff.sh` (inside `nix develop`), source → `checkAndLower` → `emitModuleGC` →
`wasmtime run -W gc=y,function-references=y,exceptions=y --invoke main`:

```
example                      wasmtime         oracle   verdict
nqueens                         21004          21004   OK   ← THE MILESTONE
list-basics                       302            302   OK   (take/drop/length over List)
mutual-parity                    1101           1101   OK   (mutual recursion via the tuple-knot)
parser-combinators                 35             35   OK   (higher-order closures)
wildcard-match                      2              2   OK   (sum/case)
tokenizer                           3              3   OK   (ADT + recursion)
string-stdlib                       1              1   OK
derive-eq-ord                       1              1   OK   (derived trait dispatch)
trait-recursive-eq                  1              1   OK
trait-recursive-ord                 1              1   OK
```

**Corpus count: 72 (rung 1-3, inline path) + 10 (rung 4, GC path) = 82 whole-artifact diffs.** The
rung-1/2/3 harness stays green untouched (72/72) — the GC path is purely additive.

## 5 · What the rung honestly does NOT cover (rung-5 boundary)

1. **Effects on the GC path** (`handle`/`perform`) — a NAMED refusal. `state`/`throws`/`transaction`
   lower on the INLINE path (rungs 2/3); a program mixing closures AND effects needs the two lowerings
   UNIFIED (the general-resumption story: reified continuations on the WasmGC frame-chain, ADR-0059's
   post-standardization `switch`/`resume` fast-path). The sweep confirms every effect example refuses
   loudly (handle/perform), never a wrong emission.
2. **Bignum** — i64-range with the documented LOUD wrap (§2). Full ℤ = a GC-array limb rep, rung 5.
3. **Non-Int results** — `emitModuleGC`'s `$main` `$unbox`es to i64 for the harness diff, so a
   String/List-returning program (e.g. `caesar`) emits but the extracted answer is meaningless. A
   real value-printer (walk the `$val` GC tree → text) is rung-5 host-IO adjacent.
4. **Proof-grade** — TESTED stratum (differential vs `Source.eval`), same seam as rungs 1-3. The
   `wexec (emitGC M) ≡ Source.eval M` forward simulation needs a WasmGC small-step machine (structs +
   `call_ref` + the env-list ↔ substitution bijection) — a whole new obligation, not a per-former delta.
5. **Frontend-blocked examples** — `calc` (`unbound variable Ast`), `json` (unresolved type var) fail
   at `checkAndLower`, BEFORE the emitter; pre-existing frontend limitations, orthogonal to rung 4.

## 6 · One-glance status

```
DEMONSTRATED  closures + ADTs + recursion → WasmGC; 10 programs incl. nqueens=21004 on wasmtime 45,
              all == Source.eval. First bang output with closures/generic-ADTs/deep-recursion outside Lean.
KEY FINDING   recursion is NOT a new former — it falls out of the μ-knot (fold/unfold/force/app).
              The machine stays an OUTPUT of the calculation (invariant #4); nothing hand-designed.
DESIGN        uniform $val GC supertype (boxed i64 / $sum / $pair / erased fold / $clos); env = a
              cons-list; app/force = call_ref; thunk≠lam (the one index-shift bug); curried chains.
BIGNUM        i64-range, documented LOUD wrap (guarded-div-shape gate); full ℤ = rung-5 GC-array.
SCOPE         pure λ+ADT+recursion; effects (handle/perform) = a NAMED rung-5 refusal (inline path lowers them).
STRATUM       tested (differential vs Source.eval); emitter axiom set [propext]; leaf-additive; 72+10 corpus.
STOP-GATE     wasmtime 45 accepts WasmGC (structs, rec types, call_ref) under -W gc=y,function-references=y.
NEXT (rung 5) unify effects onto the GC frame-chain · full bignum · a $val value-printer · proof-grade wexec≡eval.
```
