module

-- `#guard`s run `Source.eval` (compiled Operational) at the META phase → `meta import`
-- Operational alongside the runtime import (the cross-module #guard codegen escape).
meta import Bang.Core.Semantics
public import Bang.Core.Semantics
public import Bang.Core.Grade

/-! # D5 param-handler design witnesses — the mechanism is a PROJECTION of `state` (probe, HOLD)

Companion to `docs/notes/d5-param-handlers-design.md`. Every `#guard` below is a runnable
`Source.eval` fact at the kernel — no kernel change, no new former. The design claim these witness:

  **D5 (parameterised handlers / handler memory) is the `state`-arm's `put` swap generalized to the
  `custom` arm — a SEMANTIC mechanism that ALREADY EXISTS in the kernel (`dispatchOn`'s `state` arm,
  Dispatch.lean:137: `put` reinstalls `handleF n (.state ℓ' v)` with the NEW value `v`). What is
  READ-ONLY in v1 is only the `custom` arm (Dispatch.lean:181: reinstalls `p` UNCHANGED). D5 lifts
  that one arm; the update SHAPE is proven live by the built-in `state` witnesses here.**

So the ergonomic before/after is exhibitable TODAY using the built-in `state` effect (which is a
parameterised handler ALREADY), even though the USER-effect (`custom`) form awaits the D5 lift.
-/

namespace Bang.D5ParamHandlerWitness
open Bang
open Bang.EffectRow (Label EffRow)

/-- `Source.eval` yields exactly `done (vint n)`. -/
private def yieldsInt (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  match Source.eval fuel c with | .done (.vint m) => m == n | _ => false

/-! ## §1 · The update mechanism ALREADY LIVES in the kernel (the `state` `put` swap)

D5's core move — "a resumptive handler reinstalls itself carrying an UPDATED carried value" — is
exactly what `state`'s `put` does (`dispatchOn`, Dispatch.lean:137). These `#guard`s make the
"handler owns evolving state, the driver does not thread it" ergonomic concrete with the BUILT-IN
`state` effect. The `custom` (user-effect) analogue is the D5 lift; the SHAPE is proven here. -/

/-- **(1a) put-then-get = evolving handler memory.** A `state 1` handler (initial 100). Perform
`put 7` (updates the cell to 7, resumes with unit), then `get` (reads back 7). The handler CARRIES
the new value across the two performs — the driver never touches it. Yields 7. This is the exact
reinstall-with-new-value shape D5 gives `custom`. -/
private def stateUpdate : Comp :=
  .handle (.state 1 (.vint 100))
    (.letC (.perform (.vvar 0) "put" (.vint 7))          -- cap = var0; put 7 ⤳ cell := 7, resume unit
      (.perform (.vvar 1) "get" .vunit))                  -- get ⤳ reads the UPDATED 7
#guard yieldsInt 200 stateUpdate 7

/-- **(1b) accumulate across TWO puts — the memory is monotone.** put 3, then get (=3), then
put (3+4)=7, then get (=7). The handler threads the running total with ZERO driver-side plumbing:
each `put` is the D5 `p := f(p, arg)` update, realized by `state`'s reinstall. Yields 7. -/
private def stateAccumulate : Comp :=
  .handle (.state 1 (.vint 0))
    (.letC (.perform (.vvar 0) "put" (.vint 3))            -- cell := 3            (unit ⤳ var0)
      (.letC (.perform (.vvar 1) "get" .vunit)             -- read 3              (3 ⤳ var0)
        (.letC (.binop .add (.vvar 0) (.vint 4))           -- sum = 3 + 4 = 7     (sum ⤳ var0; 3 ⤳ var1)
          (.letC (.perform (.vvar 3) "put" (.vvar 0))      -- cell := 7           (put payload = sum@0)
            (.perform (.vvar 4) "get" .vunit)))))          -- read 7
#guard yieldsInt 200 stateAccumulate 7

/-! ## §2 · The DST-lcg ergonomic before/after, at the kernel

`examples/dst-rounds-lcg/main.bang` threads the LCG seed through the DRIVER's own recursion (`go n s
acc`) BECAUSE the `Sched` custom handler's param is read-only (v1). Here is the SAME shape at the
kernel, in miniature (2 rounds, seed folded twice), shown BOTH ways:

  BEFORE (v1, status quo): the seed is a driver argument, folded by the driver — `stepSeedBefore`.
  AFTER  (D5): the seed lives in a `state` handler (a parameterised handler = D5 realized for the
               BUILT-IN effect); the driver stops carrying it — `seedInStateAfter`.

Both compute the same fold `s ↦ (s*25+17) mod 2^16` applied twice from 12345. The AFTER form is
what a USER `Sched` effect would look like ONCE D5 lifts the `custom` arm — the driver-threading of
`s`, `s1`, `s2` in the real example collapses into `put`/`get` on the handler. -/

/-- LCG step reified as a closed kernel `Comp` over the seed at index `sVar`:
`t = s*25+17; t - (t/65536)*65536`. `binop`'s operands are VALUES, so each intermediate is
`letC`-bound (the seed shifts under each binder — see the index bookkeeping inline). -/
private def lcgStep (sVar : Nat) : Comp :=
  -- m = s * 25                                  (var0 = m; s ⤳ sVar+1)
  .letC (.binop .mul (.vvar sVar) (.vint 25))
    -- t = m + 17                                (var0 = t; m ⤳ var1)
    (.letC (.binop .add (.vvar 0) (.vint 17))
      -- q = t / 65536                           (var0 = q; t ⤳ var1)
      (.letC (.binop .div (.vvar 0) (.vint 65536))
        -- qk = q * 65536                        (var0 = qk; q ⤳ var1; t ⤳ var2)
        (.letC (.binop .mul (.vvar 0) (.vint 65536))
          -- t - qk                              (t ⤳ var2, qk ⤳ var0)
          (.binop .sub (.vvar 2) (.vvar 0)))))

-- The step, applied to a literal seed, as a stand-alone value fold (used by both forms).
private def lcgOf (s : Int) : Int :=
  let t := s * 25 + 17
  t - (t / 65536) * 65536

/-- **(2-BEFORE) seed threaded through the driver.** No handler at all: the driver binds `s`, folds
to `s1`, folds to `s2`, returns `s2`. This is the v1 status quo — the seed is a DRIVER argument
(the `go n s acc`'s `s`), because the handler cannot own it. Yields `lcg(lcg(12345))`. -/
private def stepSeedBefore : Comp :=
  .letC (.ret (.vint 12345))                                        -- s  = 12345  (var0)
    (.letC (lcgStep 0)                                              -- s1 = lcg s   (var0, s ⤳ var1)
      (.letC (lcgStep 0)                                            -- s2 = lcg s1  (var0)
        (.ret (.vvar 0))))                                          -- return s2
#guard yieldsInt 500 stepSeedBefore (lcgOf (lcgOf 12345))

/-- **(2-AFTER) seed lives in a `state` handler — the D5 shape.** A `state 1` handler initialized to
12345 IS the scheduler's memory. The driver `get`s the current seed, computes `lcg`, `put`s it back —
TWICE — then `get`s the final seed. The seed is NEVER a driver argument; it lives in the handler,
exactly what D5 gives a USER `Sched` effect. Same answer as BEFORE — the ergonomics differ, the value
does not. Yields `lcg(lcg(12345))`. -/
private def seedInStateAfter : Comp :=
  .handle (.state 1 (.vint 12345))                                  -- scheduler memory (cap = var0)
    (.letC (.perform (.vvar 0) "get" .vunit)                        -- read current seed  (var0)
      (.letC (lcgStep 0)                                            -- lcg it              (var0)
        (.letC (.perform (.vvar 2) "put" (.vvar 0))                 -- store back          (put resumes unit)
          (.letC (.perform (.vvar 3) "get" .vunit)                  -- read seed again
            (.letC (lcgStep 0)                                      -- lcg it again
              (.letC (.perform (.vvar 5) "put" (.vvar 0))           -- store back
                (.perform (.vvar 6) "get" .vunit)))))))             -- read final seed
#guard yieldsInt 800 seedInStateAfter (lcgOf (lcgOf 12345))

/-! ## §3 · The counter-example discipline: what D5 makes expressible that v1 CANNOT

**Honest verdict (matches `effect-algebra-survey.md` EA2): the DIFFERENCE for the DST/Sched class is
ERGONOMIC — v1 CAN already compute the same values by threading state through the driver (§2-BEFORE ==
§2-AFTER, same answer). D5's non-ergonomic win is the SIM-MAP class: a handler that is (a) a USER
effect (`custom`, not a built-in), AND (b) whose memory must be ENCAPSULATED behind the effect
interface (the driver must NOT see the seed/queue/map).**

The built-in `state` already realizes (a-for-built-ins) + (b): `seedInStateAfter` hides the seed. What
v1 CANNOT do is realize (a) for a USER-DECLARED effect — a `Sched`/`Fs`-sim handler whose CLAUSE
BODIES update the carried param — because `HasClauses.cons` fixes each clause to `Comp.ret w` reading a
READ-ONLY `p` (Typing.lean:374) and `dispatchOn`'s custom arm reinstalls `p` unchanged
(Dispatch.lean:181). So:

  · The SIM-MAP class (Fs sim wanting a growing file→content map behind the `Fs` interface, the Sched
    demo wanting an evolving queue behind `Sched`) is BLOCKED at the user-effect layer — the map/queue
    must leak into the driver's args (the dst-rounds workaround) OR be a built-in `state` alongside the
    user effect (two handlers where one should suffice — the "one construct per problem" cost).

  · There is NO v1 program that a D5 param-update makes *semantically* reachable-in-value that the
    ret-shape threading cannot also reach: the fold is the same (§2). D5 changes WHO owns the state
    (handler vs. driver), not WHAT values are computable. This is the honest scope: an
    ENCAPSULATION/ergonomics lift for user effects, not a new expressive power.

This §3 is the deliverable's "be honest" answer: **ergonomics + the sim-map encapsulation class, NOT
new computational power.** -/

/-- **(3) the sim-map shape v1 must thread through the driver.** A growing map, encoded as an `int`
accumulator (a stand-in for the Fs file-count / Sched queue-length the sim handler wants to own):
the driver folds `+1` three times, carrying the count in its OWN let-chain because a USER effect
cannot. Yields 3. Contrast (1b): with a BUILT-IN `state` the SAME fold needs no driver carrying — D5
extends that to user effects. -/
private def simMapThreadedByDriver : Comp :=
  .letC (.ret (.vint 0))                                            -- count = 0
    (.letC (.binop .add (.vvar 0) (.vint 1))                        -- +1 -> 1
      (.letC (.binop .add (.vvar 0) (.vint 1))                      -- +1 -> 2
        (.binop .add (.vvar 0) (.vint 1))))                         -- +1 -> 3
#guard yieldsInt 200 simMapThreadedByDriver 3

/-! ## §4 · The REAL `customUpd` param-evolution — a USER effect owning its memory (ADR-0107 D5 LANDED)

Now that the kernel carries `Handler.customUpd` (the pin: IR + the `Source.eval` dispatch arm, subset-green),
the §3 "BLOCKED at the user-effect layer" claim is LIFTED for the kernel: these `#guard`s run an actual
`customUpd` USER handler on `Source.eval`, whose CLAUSE BODY updates the carried param — the sim-map
encapsulation §3 said v1 could not do. The clause binds `param@1, arg@0` and yields `ret (pair w p')`
(resume `w`, reinstall `p'`) — the DECLARED customUpd contract (`dispatchOn`'s customUpd arm). This is the
e2e customUpd witness (gate condition 4, the `Source.eval` leg — the CalcVM/evalE legs land when the
engine port greens). -/

/-- The "set" clause for a `customUpd` handler carrying an int cell: `set(arg)` resumes with the OLD param
`p` and reinstalls the NEW param `arg`. The customUpd dispatch matches the substituted clause body
SYNTACTICALLY as `ret (pair w p')` (not after evaluation), so `w`/`p'` must be VALUES — hence the update is
`p' := arg` (a value), not `p + arg` (a binop is a Comp, not a Val; the S0 contract confines the update to
value operations). Body binds `arg@0, p@1`: `ret (pair p arg)` = `ret (pair (vvar 1) (vvar 0))` — resume the
OLD param `w = p`, reinstall `p' = arg`. -/
private def setClause : Comp :=
  .ret (.pair (.vvar 1) (.vvar 0))                  -- ret (pair p arg) = ret (pair w p') — SYNTACTIC ret-of-pair

/-- **(4a) customUpd param evolves across two performs — USER-effect handler memory.** A `customUpd 1`
handler carrying 100, one op "set". Perform `set 7` (resumes with the OLD param 100, param → 7), then
`set 9` (resumes with the evolved param 7, param → 9). The SECOND perform's resume value is the observable
— 7. The param LIVES IN THE USER HANDLER, evolving across performs with ZERO driver plumbing: the D5 sim-map
win realized for a USER effect (the §3 "BLOCKED at user-effect layer" claim, LIFTED). Yields 7. -/
private def customUpdEvolve : Comp :=
  .handle (.customUpd 1 (.vint 100) [("set", setClause)])
    (.letC (.perform (.vvar 0) "set" (.vint 7))     -- resume w = 100 (old param); param → 7
      (.perform (.vvar 1) "set" (.vint 9)))         -- resume w = 7 (evolved param); param → 9
#guard yieldsInt 300 customUpdEvolve 7

/-- **(4b) the regression pin (ADR-0107 yield-sniffing rejection): a READ-ONLY `custom` clause returning a
PAIR gets the pair AS ITS VALUE, NOT reinterpreted as a param-update.** The SAME `setClause` under `custom`
(read-only), performing once — the clause yields `pair 100 7`, and because `custom`'s arm NEVER decodes the
pair, the resume value IS the whole pair `(100, 7)`. We observe its FIRST component via `split`. Yields 100
(the pair's fst) — proving the pair-decode fires ONLY under `customUpd`, never `custom` (the exact silent
reinterpretation ADR-0107 rejects). -/
private def customPairValueRegression : Comp :=
  .handle (.custom 1 (.vint 100) [("set", setClause)])
    (.letC (.perform (.vvar 0) "set" (.vint 7))     -- custom (read-only): resume = the WHOLE pair (100, 7)
      (.split (.vvar 0) (.ret (.vvar 1))))          -- split the pair: fst@1, snd@0 ⇒ ret fst = 100
#guard yieldsInt 300 customPairValueRegression 100

end Bang.D5ParamHandlerWitness
