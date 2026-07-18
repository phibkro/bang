<!-- note-status: active -->
<!-- describes: Bang/Backend/WasmEmit.lean tools/emit-escape-diff.sh @ 569cca42fa09aeae47529aafc9cd2d7c68831d60 -->
# First-class-capability GC rep — design (#133)

> **Re-audit (2026-07-18, `569cca42`):** the current escape differential is hard-green: all four
> raw/surface witnesses fail loud in wasmtime with rc 134, with no known-red exceptions. The effects
> corpus also remains green at 46 emitted whole programs (23 effectful), and the module-aware
> readback corpus is green at 23. Older counts below are retained as dated implementation snapshots.

> **Multi-operation successor (2026-07-18):** the single-operation guard described in §8.3 has now
> been replaced by exact module-local operation interning and runtime clause records carrying
> `(operation id, update mode, closure)`. The mixed plain/updating first-class tracer returns 255 on
> source/env/compiled/Wasm; the effects differential is green at 47 emitted programs, 24 effectful.

> **Design-probe deliverable, no emitter change lands here** (probe phase = docs/notes + scratch
> only; implementation only after the operator's ack). Measured on a clean clone of `main @
> 412a7f88`, 2026-07-11T22:11Z, `nix develop`, `lake build` EXIT 0 (760 jobs), `wasmtime 45.0.0`
> (`-W gc=y,function-references=y,exceptions=y`). Every verdict below is a `wasmtime` RUN of a
> hand-written `.wat`, not a reading. Witnesses live in `scratch/cap-gc/`.

## 0 · TL;DR — the call

**RECOMMEND candidate (a): a `$cap` GC value — but the load-bearing content is the ESCAPE story,
not the rep.** The rep itself is nearly free (a `$cap` is the clause-closure `$env` list the lexical
custom path ALREADY builds, lifted to a `$val`); a stage-swap witness carrying it as an ordinary
argument runs `30005` == the kernel oracle. The genuine wall is **not** "how do you represent a
cap" — it is **"how does a cap value fail loud when its handler has popped"** (ADR-0063
`.escapedCap`). A naive `$cap` that carries the clause closures directly **silently succeeds on an
escaped cap** (witnessed: prints `42` where the kernel produces `.escapedCap`). The faithful fix is
a **generation-stamped `$cap`** — carry the kernel's identity `n` (ADR-0055) and gate every perform
on a runtime live-frame watermark (`n < $liveTop`), which is the RUNTIME IMAGE of `idDispatch`'s
`splitAtId K n = none`. Witnessed: the stamped cap **traps (fail-loud)** on escape, and still
resolves nested same-label caps by IDENTITY (`210`, not the nearest-label `30`) — no ADR-0052 back
door. Candidate (b) (handler-passing closure conversion) is **not an escape from this wall**: it
relocates the identical escape hazard and adds a whole-program pass, so it needs the SAME stamp for
strictly more machinery. Sized **L** (post-v1) — the stamp is a real freshness-counter thread
through the emitter + a `wexec`/differential re-gate, not a one-arm change.

## 1 · What the wall actually IS (measured, not the issue's framing)

The emitter dispatches a `perform` by a **compile-time `CapSlot`** threaded parallel to the runtime
`$env` (`WasmEmit.lean:707`, `caps : List CapSlot`). `caps[i]` statically says whether de-Bruijn
slot `i` is a `.custom clauseMap` / `.throwsTag t` / `.none` cap-binder, and the custom arm
(`WasmEmit.lean:978-991`) uses that map to pick the op's clause POSITION. When a cap arrives as a
**function argument**, its slot's `CapSlot` is `.none` (a value binder), so the emitter has no
compile-time map and refuses (`WasmEmit.lean:1040`).

But the RUNTIME rep is already almost there. Reading the emitted `nested.wat` (`examples/
handle-custom-nested` → `210`), the custom handler's clause-closure list is stored as a **`$txbox`
in the handler's `$env` slot** (`nested.wat:375,379`), and each perform looks it up by de-Bruijn
index — inner cap at `$lookup env 0`, outer at `$lookup env 2` (`nested.wat:383,387`). **Identity
dispatch is already realized structurally as variable resolution**: the two same-label handlers get
distinct de-Bruijn indices because the elaborator bound each `handle` and each perform references
the correct enclosing binder. This is exactly why nested gives `210` (identity), not `30`
(nearest-label). So:

```
already a runtime value : the clause-closure $env list ($txbox contents) — a $val in the env slot
still compile-time only  : (1) the op→position map (CapSlot.custom), (2) the DECISION to route a
                           .none slot's perform to a runtime cap instead of refusing
missing entirely         : the handler's LIVENESS — the one thing "handlers = control flow" discarded
```

The issue (#133) frames the wall as "no GC value rep for a `vcap`." That is the CHEAP half. The
expensive half — the reason this is L and not S — is **liveness / fail-loud on escape**, which
neither candidate escapes.

## 2 · Candidate table (witnessed verdicts)

| # | candidate | shape | witness | verdict |
|---|---|---|---|---|
| (a₀) | **naive `$cap`** | `$cap = (struct (clauses $env))` — carry the clause closures directly, pass as a `$val` arg, `perform` = `$clausecell` + `call_ref` | `stage-swap-capval.wat` ⇒ **30005** ✅; `nested-identity-capval.wat` ⇒ **210** ✅ (identity, not 30) | **CORRECT on the happy path**, but… |
| (a₀-escape) | naive `$cap`, escaped | a `{get}` thunk captures the cap, forced after the handler region exits | `escape-naive-cap.wat` ⇒ **42** ✗ | **BREAKS ADR-0063**: silently reads the dead handler's box where the kernel produces `.escapedCap`. The hazard, witnessed. |
| (a) | **stamped `$cap`** (RECOMMENDED) | `$cap = (struct (id i64) (clauses $env))` + a global `$liveTop` watermark a `handle` bumps on entry / restores on exit; every `perform` gates on `id < $liveTop` else traps | `escape-stamped-cap.wat` ⇒ **wasm trap** (fail-loud) ✅ | **FAITHFUL**: escape fail-louds (= `.escapedCap`), happy path unchanged. Identity dispatch preserved (the `$cap` value IS the identity — no nearest search). |
| (b) | handler-passing closure conversion | a compile pass defunctionalizes cap-taking fns so `perform` becomes a direct `call_ref` to the passed clause-closure; no runtime `$cap` value | — (reasoned, §4) | **REJECTED as an escape from the wall**: relocates the IDENTICAL escape hazard (a converted cap still holds a live closure after its handler pops), so it ALSO needs the §3 stamp — for strictly more machinery (a whole-program pass vs one env slot). |
| (c) | honest "stays post-v1" | ship the S4 named refusal as-is | (already shipped) | **the current resting state** — correct to keep until (a) lands; (a) is the successor, not a blocker. |

## 3 · The recommended design — a generation-stamped `$cap` (candidate a)

### 3.1 The rep

```wat
(type $cap (sub $val (struct
  (field $id      i64)               ;; the kernel's generative identity n (ADR-0055)
  (field $clauses (ref null $env))))) ;; the clause-closure list — position k = op k (= today's $txbox contents)
```

A `handle (custom p cls) M` that BINDS a cap M might pass first-class already builds the
clause-closure `$env` (`emitClauses`, `WasmEmit.lean:1121`); wrap it in a `$cap` carrying the
freshly-minted `$id` and store THAT in the env slot (instead of, or alongside, today's `$txbox`).
A `perform op v` on a `.none` slot whose runtime value is a `$cap` extracts `$clauses`,
`$clausecell` to the op position, gates on liveness (§3.2), and `call_ref`s — the same call the
lexical path emits, sourced from a runtime value instead of a compile-time `CapSlot`.

State/throws/txn caps generalize the same way (`$cap` carries the `$ref` box / tag / `$txbox`
respectively); the witnesses use custom (clauses) and state (box) — the two structural shapes.

### 3.2 The escape check — the runtime image of `splitAtId`

The kernel's `idDispatch K n ℓ op v` calls `splitAtId K n`: walk the LIVE handler chain `K`, find
the frame whose minted identity is `n`. An ESCAPED cap names a frame no longer on `K` ⇒ `splitAtId
= none` ⇒ `.escapedCap`. The invariant that makes this sound is `WellCounted (g, K, _)`: **every
live handler identity on `K` is `< g`** (`Invariants.lean:31`, ADR-0055); the mint arm pushes
`handleF g` with counter `g+1`.

The runtime image (witnessed, `escape-stamped-cap.wat`):

```
global $liveTop  ;; = the kernel's g watermark: the count of currently-open handlers
global $nextId   ;; the mint counter

handle:  myId := $nextId++ ;  $liveTop := $nextId   ;; ENTER — this frame + those below are live
         … run body …
         $liveTop := myId                            ;; EXIT — this frame pops (its id no longer < liveTop)

perform on cap c:  if c.$id >= $liveTop then TRAP    ;; = splitAtId none = .escapedCap (fail-loud)
                   else $clausecell/call_ref as usual
```

`c.$id >= $liveTop` is EXACTLY `¬(id < g among the live)` — `splitAtId` finding nothing. This is not
a new mechanism bolted on; it is the ADR-0055 freshness theory the kernel already proves, made
runtime. **Invariant #4 holds**: the check falls out of `WellCounted`/`idDispatch`, it is not a
hand-designed instruction justified after the fact.

> **Subtlety — a monotone watermark is a conservative approximation, and the design must not let it
> become wrong.** A single `$liveTop` high-water mark models a STACK of handlers (LIFO
> enter/exit), which is what the kernel's `K` is. It correctly rejects a cap whose handler has
> popped. It could in principle be too permissive if a NEW handler with a higher id reopens after an
> old one popped AND an old cap's id happens to fall below the new watermark — but ids are
> globally-fresh monotone (`$nextId` never reused, ADR-0055's exact anti-collision property), so a
> popped handler's id is strictly below every later mint and can never be "revived" by a later
> frame's watermark. The stamp is sound BECAUSE ADR-0055 already killed id-reuse. (This is the
> place a careless implementation would reintroduce the ADR-0054 impostor collision; the global
> counter is load-bearing, not incidental.) A per-cap check against a reified live-id SET would be
> exact but heavier; the watermark suffices given monotone fresh ids, and matches `WellCounted`'s
> own `< g` bound one-for-one. **This equivalence is the key proof obligation for S-proof (§6).**

### 3.3 Identity dispatch is preserved — no ADR-0052 back door

`nested-identity-capval.wat` holds TWO same-label caps as runtime `$cap` VALUES and performs on
each ⇒ `210`, not `30`. The identity is the `$cap` value itself (each carries a direct reference to
its own handler's clause closure), so there is **no nearest-label search anywhere** — the performer
holds the exact handler, resolved when the cap value was constructed at its `handle`. This is the
H1b note's core worry (`h1b-nearness-design.md` §3: "which of N same-label live frames wins") and
the answer here is structural: the `$cap` value carries its own answer, exactly as the de-Bruijn
index does on the lexical path today. First-class caps do not reintroduce nearness because a cap is
a VALUE naming its handler, never a label to be re-resolved.

## 4 · Why candidate (b) is not the cheaper door

Handler-passing closure conversion (defunctionalize the cap-taking fn so `perform` compiles to a
direct `call_ref` on the passed clause-closure) is attractive because it needs no runtime `$cap`
struct. But:

1. **It has the identical escape hazard.** A closure-converted cap is a clause-closure passed as an
   argument; after its handler region pops, that closure is STILL a live GC object, so a perform on
   it silently succeeds — the same `42`-not-`.escapedCap` failure as (a₀). (b) therefore ALSO needs
   the §3.2 generation stamp (the closure would have to carry an id and check `$liveTop`). It does
   not avoid the wall; it moves it into the converted closure.
2. **It adds a whole-program pass** (elaborate → **closure-convert** → emit) that the pipeline does
   not have today (`checkAndLower` → `Comp` → `emitModuleGC`, no intermediate transform). The
   nested/stage-swap correctness that (a) gets by REUSING the existing `$clausecell`/`call_ref`
   machinery would have to be re-established for the converted form, including the same identity
   discipline.
3. **It fights invariant #4 more.** (a)'s stamp is a direct image of `WellCounted`; (b)'s
   defunctionalization is a compile-time reshaping of dispatch that must be shown to PRESERVE the
   kernel's identity semantics through the transform — a heavier equivalence than "the $cap value
   carries the identity."

(b) is the right frame for a MULTI-SHOT / reified-continuation future (defunctionalized handlers are
the classic CPS-emit path), but for v1's one-shot effect set it is strictly more machinery for the
same escape obligation. Rejected for v1; noted as the post-v1 multi-shot lowering if reified
continuations arrive (ADR-0015 frontier).

## 5 · What it does to the differential harness

- `tools/emit-rung5-effects-diff.sh` currently lists `stage-swap` in `KNOWN_REFUSALS` ("first-class
  capability (vcap) threaded as a runtime value"). When (a) lands, **remove that entry** — the
  harness auto-discovers `examples/stage-swap` and will gate its wasmtime stdout (`30005`) against
  `expected.txt`. `cap-as-arg`/`cap-lexical` (`scratch/calcjson/`) join as a discriminator pair if
  promoted to `examples/`.
- **Add an ESCAPE gate** the corpus does not currently have on the GC path: an example whose kernel
  outcome is `.escapedCap` must EMIT and then **trap** on wasmtime (a non-zero exit / `wasm trap`),
  not print a value. This is the differential test for §3.2 — without it, a regression to the naive
  rep (dropping the stamp) would pass silently (the `42` failure). The gate asserts the emitted
  module traps where the kernel `#guard`s `.escapedCap` (`Bang/Examples.lean:262` `capEscape`). A
  surface program can't easily express escape in v1 (needs scoped-cap types, post-v1), so this gate
  is driven from a hand-authored `Comp` or a `scratch/` witness, not an `examples/*/main.bang`.
- The `wexec ≡ Source.eval` proof-grade obligation (rung-5 S5, `rung5-s5-proofgrade-refutation.md`)
  gains one clause: the `$liveTop`/`$id` watermark ≡ `WellCounted`'s `< g` bound (§3.2's key
  equivalence). This is stateable against the proof-carrying backend (unlike the `$env↔store`
  bijection, which stays the post-v1 GC-machine item) — it is the runtime realization of an
  invariant the kernel already proves, so it is a transfer, not a new theory.

## 6 · Slice map (post-v1, size L)

```
C0  $cap type + happy-path perform   add (type $cap …); route a .none-slot perform whose runtime
                                     value is a $cap to $clausecell/call_ref (reuse the S4 machinery,
                                     sourced from the value not the CapSlot). REFUTE-FIRST DONE:
                                     stage-swap-capval.wat ⇒ 30005, nested-identity-capval.wat ⇒ 210.
C1  cap CONSTRUCTION at handle        a `handle` that binds a cap M may pass first-class wraps its
                                     clause list / box / tag in a $cap carrying the minted $id, stores
                                     it in the env slot. Elaboration already knows the binder; the
                                     emitter mints the id (thread a fresh-counter through GCState,
                                     mirroring st.freshTag).
C2  the ESCAPE stamp (load-bearing)   add global $liveTop/$nextId; handle bumps/restores; perform gates
                                     id < $liveTop else a DEFINED trap ($escapedCap). REFUTE-FIRST DONE:
                                     escape-stamped-cap.wat traps; escape-naive-cap.wat (no stamp) = 42
                                     is the regression witness the C2 gate must catch.
C3  differential re-gate              remove stage-swap from KNOWN_REFUSALS; add the escape-traps gate
                                     (§5); confirm the full rung-5 effects corpus stays green + calc
                                     (examples/calc) now EMITS (its Eval.eval takes tr:Cap Trace as an
                                     arg — the #133 headline consumer) once the frontend module-resolve
                                     harness gap (W3, calcjson-compiled-diagnosis.md) is also closed.
C4  proof-grade clause                $liveTop watermark ≡ WellCounted < g (§3.2); state against the
                                     proof-carrying backend (rung5-s5). Tested-superset until then (inv#1).
```

`C0`–`C2` are the feature (a first-class cap that dispatches AND fails loud); `C3` lands the #133
headline (`calc`/`stage-swap` emit); `C4` is the tested→verified lift. No closure-conversion slice
(that is candidate (b), rejected §4). No frame-chain / multi-shot slice (post-v1, ADR-0015).

## 7 · Sharpened wall statement (for #133)

> #133 is **not** "a `vcap` has no GC value rep" (that half is nearly free — the clause-closure list
> is already a runtime `$val` in the env slot). It is: **a first-class cap value must reproduce
> ADR-0063 `.escapedCap` fail-loud** — the kernel does this by `idDispatch`/`splitAtId` walking the
> LIVE handler chain, and the GC path discarded that chain when handlers became structured control
> flow. The design is a `$cap` carrying the ADR-0055 identity `n` + a runtime live-frame watermark
> (`n < $liveTop`), the runtime image of `WellCounted`'s `< g` bound. Sized L because the stamp is a
> freshness-counter thread through the emitter plus an escape-differential gate the corpus lacks,
> not a one-arm change; and because v1 does NOT statically exclude escape (scoped-cap types are
> post-v1, ADR-0063), so the runtime fail-loud is mandatory, not optional.

## 8 · Implementation findings (feat-cap-gc-rep, 2026-07-12)

Measured facts from the implementation lane that refine §6's slice map:

- **The escape hole is LIVE in the shipping emitter, and spans ALL cap kinds.** Fed real escape
  `Comp`s through `emitModuleGCPrint` (`rung4-shape --escape`): a STATE-cap escape (`{get}` thunk
  forced past its handler) emits + prints `0`; a CUSTOM-cap escape (`{perform log}` thunk) emits +
  prints `99` — both where the kernel `#guard`s `.escapedCap`. So C2's stamp is a **cross-cutting
  liveness thread** through EVERY `handle`-mint and EVERY `perform` arm (state `get`/`put`, custom
  `call_ref`, txn), not a first-class-cap-only change. This is wider than the #133 headline. The
  escape-differential gate (`tools/emit-escape-diff.sh`, LANDED `cb512890`) makes it visible + pins
  the regression class; `capEscape-get` is `XFAIL_UNTIL_STAMP` (known-red, build stays green) until
  C2 removes the entry.
- **The happy-path C0 is more surgical than §6 assumed — the `$txbox` IS already the runtime cap
  value.** Reading the emitted lexical-custom dispatch (`logger-counting`): a `perform` does
  `$clausecell (struct.get $txbox 0 (ref.cast (ref $txbox) ($lookup env i))) pos` + `call_ref`. A
  FIRST-CLASS cap's env slot holds the SAME `$txbox` (passed in via `app`). So a `.none`-slot
  perform on a CUSTOM op can REUSE the identical dispatch — no new `$cap` type needed for the happy
  path; the only new thing is knowing the op's POSITION (no compile-time `CapSlot.custom` map).
- **Single-op covers the entire shippable corpus.** The ONLY two first-class-cap programs are
  `calc` (`Eval_Trace`, one op `log`) and `stage-swap` (`Net`, one op `fetch`) — both single-op ⇒
  position 0. A MULTI-op first-class cap can be a NAMED refusal (invariant #1: fail loud, never a
  wrong multi-op dispatch) without blocking anything currently shippable. The general multi-op
  position needs the effect-decl op ordering threaded to the perform (a `$cap` carrying the op→pos
  map, or the effect signature in `GCState`) — deferred behind the refusal.
- **Revised slice order (proposed):** C0 (first-class happy path, single-op, stage-swap unlocks) is
  INDEPENDENT of C2 (the escape stamp). Shipping C0 first banks the #133 headline (`stage-swap`/
  `calc` emit) with escape honestly `XFAIL`'d; C2 then flips the escape gate green as its own slice.
  This isolates the riskier cross-cutting stamp from the headline win. (Ordering is a
  correctness-adjacent call — see the lane's messages to the manager.)

### 8.1 · SEVERITY: escape IS surface-reachable — a LIVE miscompile of legal programs (#134)

**The earlier "escape is not surface-expressible in v1" claim was WRONG** (it was a syntax artifact
of `let x = $(…)` attempts, which the elaborator rejects with `not a value` at `TypeCheck.lean:1042`
— a syntax refusal, NOT a structural one). The correct form `let x = <comp> in <force>` typechecks
clean AND reaches `escapedCap` on the oracle AND silently miscompiles. Two independent witnesses,
every verdict machine-cited (`scratch/cap-gc/surface-escape/`):

```
(1) STATE cap escape — b3.bang:
      let leaked = state 0 in { get } in
      $leaked
    bang check          → ok           (typechecker ACCEPTS — no structural refusal)
    run --engine=oracle → escapedCap   (ADR-0063 fail-loud)
    run --compiled      → fail-loud     (the CalcVM agrees — "no value" terminal)
    EMIT → wasmtime     → 0, rc=0       ← SILENT MISCOMPILE

(2) CUSTOM cap escape — c1.bang:
      effect Log { emit : Int -> Int }
      let leaked = handle ({ logger.emit(7) }) with Log as logger { emit(x) => x } in
      $leaked
    bang check          → ok
    run --engine=oracle → escapedCap
    EMIT → wasmtime     → 7, rc=0       ← SILENT MISCOMPILE
```

So **#134 is a LIVE compiled≠oracle divergence on legal, well-typed programs**, not an
unreachable-from-surface kernel curiosity. The oracle AND the CalcVM both fail loud; only
`emitModuleGC` produces a module that silently returns a value. This is the exact defect class that
GATES a tag (a wasm binary computing a different answer than the verified oracle for a program a
user can write and the typechecker blesses). It is EMIT-path-only today (`bang run` default env +
`--compiled` both fail loud correctly), but "the compiled-wasm binary silently miscompiles legal
escape programs" is real and demonstrable.

**The full 5-attempt experiment (bounds the reachable escape surface).** Per the manager's brief,
the named candidate shapes, each verdict machine-cited (`scratch/cap-gc/surface-escape/`):

| # | shape | `bang check` | oracle | emit → wasmtime |
|---|---|---|---|---|
| b3 | `let leaked = state 0 in { get } in $leaked` (STATE) | **ok** | escapedCap | **0, rc=0** (miscompile) |
| c1 | `handle ({logger.emit(7)}) with Log …` forced outside (CUSTOM) | **ok** | escapedCap | **7, rc=0** (miscompile) |
| d2 | `handle ({sched.bit(1)}) with Sched …` forced outside (the dst-rounds idiom) | **ok** | escapedCap | **0, rc=0** (miscompile) |
| d1 | cap-in-state: `put({logger.emit(5)})` then read outside | **REFUSED** `type mismatch` | — | — (path closed) |
| d3 | return a bare `Cap` then perform: `$(leak.emit(3))` | **REFUSED** `not a value` (TC:1042) | — | — (path closed) |

**Bound:** the reachable escape shape is `let leaked = <handle/state returning a cap-capturing
thunk> in <force outside>` — three distinct effect kinds (state, custom Log, Sched) ALL reach
`escapedCap` and ALL silently miscompile. Two attempts to escape by a DIFFERENT route (storing the
cap in a state cell; returning a bare cap value) are structurally refused by the checker (the
refusing diagnostics recorded in `scratch/cap-gc/surface-escape/REFUSED-attempts.md`). So the miscompile is not a
one-off shape — it is the general "thunk captures a cap, forced past its handler" pattern, which the
type system permits (scoped-cap types are post-v1, ADR-0063).

**Consequence for the slice order:** C2 (the escape stamp) is NOT the "riskier second slice" — it is
the FIX for a tag-gating miscompile, and should go FIRST. The §8 bullet's C0-first proposal assumed
escape was latent; it is not. Revised recommendation: **C2 (escape stamp, close the miscompile,
flip the gate green) before C0 (the first-class headline).** The escape gate's `capEscape-get`
`XFAIL` is now understood as masking a surface-reachable defect, not a theoretical one — sharpening
the urgency of removing it.

### 8.2 · C2 LANDED — the `$liveTop` stamp closes #134

**C2 is implemented and the escape gate is GREEN.** The `$liveTop`/`$nextId` globals + `$capMint`/
`$capExit`/`$capGate` helpers (`gcHelpers`) are the runtime image of ADR-0055's global-fresh counter
+ `WellCounted`'s `< g` bound. Each cap-carrying type (`$ref` state cell, `$txbox` txn/custom cap)
gained an `$id` field (field 0; the payload moved to field 1, `$box`/`$list`). Every `handle` arm
(state/throws/custom/transaction) mints an id (`$capMint` bumps `$liveTop`), stamps its cap value,
runs the body, saves the value, and restores `$liveTop` (`$capExit`); every `perform` on a state/txn/
custom cap gates `$id < $liveTop` (`$capGate`) else traps. A throws handle bumps/restores too (so a
nested state/custom cap gets a correctly-ordered id); a `raise` on an escaped throws cap traps
naturally (its `try_table` has exited).

Measured (wasmtime 45, `-W gc=y,function-references=y,exceptions=y`):
- **All 4 escape witnesses now TRAP** (rc=134) where they previously silently returned a value —
  `capEscape-get`, `surface:b3` (0→trap), `surface:c1` (7→trap), `surface:d2` (0→trap). The
  `emit-escape-diff.sh` `XFAIL_UNTIL_STAMP` list is now EMPTY; the gate is hard-green.
- **Zero regression**: the rung-5 effects corpus (40 programs, 22 effectful — state/stm/throws/
  logger/custom/dst/ndet) all still == `bang run`. The stamp does not false-fire on legitimate
  in-region perform (witnessed `structured-noescape-witness.wat` ⇒ 5, and the whole corpus).

`lake build` EXIT 0 · `just fitness` EXIT 0 · axioms baseline unchanged (`emitModuleGC` is a
tested-stratum text emitter, no proof headline). The tag-gating #134 miscompile is CLOSED. C0 (the
first-class-cap headline — stage-swap/calc emit) rides this stamped infra next.

### 8.3 · C0 LANDED — first-class caps emit (the #133 headline)

**A capability threaded as a function argument now emits and runs.** The `.none`-slot perform arm's
refusal (`WasmEmit.lean`, the old "first-class-capability rep is a rung-5+ wall") is REPLACED: when
the op is a CUSTOM op (not a built-in state/txn op), the runtime env slot holds the handler's
`$txbox` cap (the SAME value the lexical path builds), so dispatch REUSES the lexical machinery
sourced from the runtime value — gate the `$id` (#134 stamp), then `$clausecell` + `call_ref`.

- **stage-swap emits + runs `30005` == the oracle** (`examples/stage-swap`, `logic : Cap Net -> Int`
  threaded as an argument, two handlers ×10/+1). Removed from `emit-rung5-effects-diff.sh`'s
  `KNOWN_REFUSALS`; the corpus grew **40 → 41**.
- **Identity dispatch intact**: `handle-custom-nested` still `210` (not the nearest-label `30`).
- **First-class escape is trap-safe**: a first-class cap forced past its handler TRAPS (the `$capGate`
  in the C0 route fires) — the #134 stamp covers the new dispatch path by construction.
- **POSITION**: the emitter has no compile-time op→position map for a first-class cap, so it emits
  position 0 GUARDED by a runtime `$clauselen == 1` single-op check (else trap). The entire shippable
  corpus is single-op (calc `Trace`.log, stage-swap `Net`.fetch). A multi-op first-class cap traps
  (invariant #1: never a wrong-clause dispatch) rather than guessing — the general multi-op case
  needs a runtime op→position map on the cap (deferred; §6 C-note). `calc` (the other headline
  consumer) needs the frontend module-resolve harness gap closed first (W3, a separate lane).

`lake build` EXIT 0 · `just fitness` EXIT 0 · both emission harnesses green. #133 headline DONE for
the single-op first-class case (the whole current corpus).

#### 8.3.1 · Multi-operation successor landed

The retained guard did its job: the first natural two-operation consumer trapped rather than silently
calling clause 0. The successor stores an exact interned operation id and the clause's own update bit
beside every closure. A runtime capability perform now searches that cap's records with `$clausefind`;
lexical dispatch keeps `$clauseat` by compile-time position. Hashing was rejected because even a remote
collision would turn effect dispatch into a silent wrong-clause bug. IDs remain internal to one emitted
whole-program module; separate compilation must design a linking identity rather than inherit them.

### 8.4 · C3 LANDED — calc emits (the capstone: a 5-module program with a first-class cap on wasm)

**`examples/calc` — a 5-module program (Ast/Lexer/Parser/Eval/Print) with a first-class `Cap Trace`
woven through a recursive evaluator — emits to WasmGC and runs `11021193` == the oracle.** This is
the #133 arc's capstone: first-class capabilities carry a real multi-module program to WebAssembly.
`bang run` = `bang run --compiled` = `bang emit → wasmtime` = `11021193`, all three agreeing.

Two findings getting here:
- **The W3 module-resolve gap was ALREADY closed** — `bang emit <file> [-o out.wat]` (Main.lean, CLI
  at the `emit` subcommand) shares the runner's `resolveEntryFile`, so an import-ing program emits.
  No new resolution code needed; the `rung4-shape` scratch exe's single-file limitation was the only
  reason the OLD diagnosis (calcjson W3) saw calc/json as "frontend refusals."
- **calc was a STALE example** (broken on ALL paths, incl. `bang run`): the Mod_Eff ergonomics change
  requires imported effects spelled `Eval_Trace`, but calc still used `use Eval (Trace)` + `with
  Trace`. Fixed (6 lines: `Cap Trace`→`Cap Eval_Trace`, `with Trace`→`with Eval_Trace`, drop the
  `use`); all three engines then agree.

**json** (the pure multi-module companion, no effects) already gated via `bang emit` → `163`. calc
ENROLLS in the SAME existing `MODULE_CORPUS` leg (`tools/emit-rung5-print-diff.sh`, `#136` — driving
`bang emit` → wasmtime, diffed vs `bang run`'s live stdout): `MODULE_CORPUS=( json calc )`. No new
gate — the module-resolving mechanism already existed; C3 was a one-line enrollment + the stale-example
fix. The rung-5 EFFECTS gate's `calc`/`json` `KNOWN_REFUSALS` entries are documented as a HARNESS-scope
split (the single-file `rung4-shape` exe), not emitter walls.

The #133/#134 arc is complete at the emit stratum: escape fixed (C2), first-class caps emit (C0),
both headline consumers (stage-swap 30005, calc 11021193) run on wasmtime == the kernel oracle.

### 8.5 · C4 (proof-grade) INPUTS — handed to the wgcexec calculated-machine probe

**C4 is NOT scoped here** — the `wgcexec` calculated-machine design probe owns the proof-grade story
(the `wexec ≡ Source.eval` obligation on a GC machine, calculated not verified-after per inv#4). This
section is the INPUT handoff for that lane; two concrete obligations the #134 stamp introduces:

1. **The watermark-equivalence clause** (§3.2 + §8.2): the runtime `$liveTop`/`$id` gate ≡ the
   kernel's `WellCounted (g,K,_)` `< g` bound (`Invariants.lean:31`) — `capId < $liveTop` is the
   image of `splitAtId K n ≠ none`. This is a TRANSFER (the kernel already proves `WellCounted`),
   not a new theory. It is stateable against the proof-carrying backend (§8.2), unlike the
   `$env↔store` bijection (which needs the post-v1 GC machine).
2. **The txn-abort restore RESIDUAL** (§8.2, the honesty note + the txn arm comment): the `throw_ref`
   unwind on a txn ABORT skips the txn's `$capExit`, leaving `$liveTop` transiently HIGH. This is the
   SAFE direction (more caps look live ⇒ never a wrong-trap on a legit cap; worst case = failing to
   trap an escaped cap AFTER an abort, an exotic shape in no witness). The airtight fix (restore
   `$liveTop` on the abort path too, e.g. inside the `catch_all_ref` block before `throw_ref`) is a
   C4-lane input — tighten it opportunistically if that arm is touched. The rung-3 explicit-restore
   finding (`emission-rung3-design.md`) is the precedent (wasm unwinds free; the heap/watermark
   restore is the load-bearing manual part).

## Artifacts (all under `scratch/cap-gc/`, run on wasmtime 45.0.0)

- `stage-swap-capval.wat` — candidate (a) happy path: a `$cap` value passed as an argument, two
  handlers apply the same `logic`. ⇒ **30005** == `examples/stage-swap/expected.txt`.
- `nested-identity-capval.wat` — the ADR-0052 back-door test: two same-label caps as values. ⇒
  **210** (identity), NOT `30` (nearest-label).
- `escape-naive-cap.wat` — the HAZARD: a naive `$cap` (closures direct, no stamp) on an escaped cap
  ⇒ **42** (silent success) where the kernel says `.escapedCap`.
- `escape-stamped-cap.wat` — the FIX: a generation-stamped `$cap` + `$liveTop` gate ⇒ **wasm trap**
  (fail-loud) on the same escape.

## Citations

- issue #133; `docs/notes/calcjson-compiled-diagnosis.md` (the `cap-as-arg`/`cap-lexical`
  discriminator, the W4 wall)
- `docs/notes/emission-rung5-design.md` §S4 (the S4 custom lowering + the NAMED first-class-cap
  refusal this note lifts); `rung5-s5-proofgrade-refutation.md` (the proof-grade split)
- `Bang/Backend/WasmEmit.lean:707` (`CapSlot`), `:978-1041` (the custom perform arm + the runtime-cap
  refusal), `:1093-1138` (`emitClauses` — the clause-closure list this rep reuses)
- `Bang/Core/Semantics/Invariants.lean:31,46-63` (`WellCounted`, the `< g` bound = the watermark's
  soundness); `Bang/Core/Semantics/Dispatch.lean:78,186` (`splitAtId`/`idDispatch` — what the
  watermark images)
- ADR-0055 (global-fresh identity — the anti-reuse property the watermark relies on), ADR-0054
  (identity representation), ADR-0052 (lexical/identity dispatch, nearest-label REFUTED — §3.3's
  back door), ADR-0063 (capability-escape = defined fail-loud, scoped-cap types deferred post-v1 —
  why the runtime check is mandatory)
- `docs/notes/h1b-nearness-design.md` §3 (the same-label "which frame wins" question the `$cap`
  value answers structurally)
- `Bang/Examples.lean:258-262` (`capEscape` `#guard` `.escapedCap` — the escape oracle the C2 gate
  checks against)
