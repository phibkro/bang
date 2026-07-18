<!-- note-status: historical -->
# D5 — parameterised handlers (handler memory): design probe with HOLD (#44 rung-2 face)

> **Historical design probe.** ADR-0114 has now landed the explicit `ClauseKey.plain` /
> `ClauseKey.updating` protocol across typing, source dispatch, CalcVM, EnvMachine, abstract Wasm,
> and concrete WasmGC. Statements below written in the present tense describe the pre-ADR baseline;
> the final design differs from the early value-shape proposal by recording update intent in the
> clause key, so ordinary product-valued results remain unambiguous.

> The task (2026-07-12, Wave C): design **D5 — parameterised handlers / handler memory**, the
> rung-1→2 boundary of the effect-algebra ladder (`effect-algebra-survey.md` §2, Plotkin–Pretnar
> [plotkin-esop09]) and the unlock three lanes independently worked around this week: the Sched
> demo's seed/queue threading through the driver, the DST examples' ret-shape contortions, the Fs
> sim-map wanting state. **ADR-input probe, not an ADR — DESIGN-FIRST with a HOLD before any
> implementation** (the proven spine is touched). Every kernel claim is `file:line` or ADR; the
> ergonomic claim is a runnable witness (`Bang/Witness/D5ParamHandlerWitness.lean`, 6 `#guard`s
> green). Terminology guard: the "**D5**" here is the effect-algebra ladder's rung-2 **param-update**
> (ADR-0092 §D5 open item / ADR-0087 §Open-questions) — NOT ADR-0095's decision-list "(D5)" (the
> `resume` surface spelling), a different D5.

---

## 0 · The four-line verdict

```
WHAT     D5 = the custom arm reinstalls an UPDATED carried param `p'` (from the clause), not `p`
         unchanged. It is the `state`-arm `put` swap (Dispatch.lean:137) generalized to the
         `custom` arm (Dispatch.lean:181, currently reinstalls `p` UNCHANGED — the ONE read-only arm).
KERNEL   ZERO rep change (`Handler.custom ℓ p cls` already carries `p`). ONE dispatch-arm delta +
         ONE clause-shape delta (the clause must yield BOTH resume-value AND `p'`). NO 6th primitive
         (invariant #5 holds — a refinement of the existing handler arm, the `state` PUT proves the shape).
COST     The blast radius is the PROVEN SPINE, not the rep. The state PUT arm is a FULLY-WORKED
         TEMPLATE for every proof obligation (LR reinstall, soundness resume-typing) — so D5 is a
         BOUNDED multi-session M/L, not open-ended: mirror `state`, don't invent. Cheapest entry =
         the SEMANTIC arm (kernel+engines+diff-test) BEFORE the typed re-grade.
HONESTY  For the DST/Sched class the win is ERGONOMIC (v1 threads the same values through the driver;
         §2 witness: before == after). The non-ergonomic win is the SIM-MAP ENCAPSULATION class:
         handler-owned state behind a USER-effect interface. NOT new computational power (§3).
```

---

## 1 · The mechanism — D5 is one arm of `dispatchOn`, and the rep does not move

### 1.1 What the kernel already carries

The custom handler rep is **already parameterised** (`IR.lean:176`):

```
| custom : Label → Val → List (OpId × Comp) → Handler       -- ℓ, the carried param p, clauses
```

`p : Val` is the carried param — the same slot as `state`'s `Val` cell (`IR.lean:148`) and
`transaction`'s `List Val` heap (`:157`). **D5 adds NO field**: `p` is already there. What is
read-only in v1 is only the *reinstall* in the dispatch arm. Compare the two resumptive arms in
`dispatchOn` (`Dispatch.lean`):

```
state  put  (:137):  some (Kᵢ ++ handleF n (.state ℓ' v)      :: Kₒ, .ret .vunit)   -- reinstall CHANGED value v
custom      (:181):  some (Kᵢ ++ handleF n (.custom ℓ' p cls) :: Kₒ,                 -- reinstall p UNCHANGED
                           Comp.subst p (Comp.subst (Val.shift v) clause.2))
```

The `state` arm ALREADY reinstalls a *changed* carried value (`v`, the put payload). The `custom`
arm reinstalls `p` verbatim. **D5 = make the custom arm reinstall a `p'` computed by the clause.**
That is the entire semantic delta. (`memory-management-survey.md` §1.2 reached this verbatim; this
note grounds it in the dispatch code and prices the proof ripple.)

### 1.2 The design fork — WHERE does `p'` come from? (the one real decision)

The v1 clause body is `Comp.ret w` — it yields ONE value, the resume value `w` fed to `Kᵢ`
(`Typing.lean:376`; `HasClauses.cons` fixes `body = Comp.ret w`). D5 needs the clause to yield TWO
things: the resume value `w` AND the updated param `p'`. Three candidate shapes, one recommended:

```
 shape                       clause body           dispatch decode             verdict
 ─────────────────────────   ───────────────────   ─────────────────────────   ─────────────────────────
 (A) PAIR-yielding clause    ret (pair w p')       split the returned pair;     RECOMMENDED — zero new
     (the state PUT shape,     (w = resume,          reinstall custom ℓ p' cls,   former; `pair` already in
      one arm generalized)      p' = new param)      resume Kᵢ with w             the kernel (IR ADT); the
                                                                                  clause STAYS `ret <closed>`
 (B) new Comp former          customYield w p'      a bespoke reduction rule    REJECTED — a kernel former
     `customYield`                                   in Source.step               (invariant #5 pressure); the
                                                                                  pair encoding subsumes it
 (C) param as a 2nd clause    (ret w, ret p') a      two sub-derivations per     REJECTED — doubles the
     component (product cls)   product clause body    clause; blows up HasClauses  clause typing, no gain
```

**Recommendation: (A) pair-yielding.** The clause body stays `Comp.ret w'` where `w' = pair w p'`
is a CLOSED value (the focus-closed discipline holds — no new former, invariant #5 untouched, the
`pair` is the existing ADT constructor `IR`). The dispatch arm decodes:

```
| .custom ℓ' p clauses =>
    match clauses.find? (·.1 == op) with
    | some clause =>
        -- clause.2 = ret (pair w p'); substitute [param@1 := p, arg@0 := v] then split the pair.
        match Comp.subst p (Comp.subst (Val.shift v) clause.2) with
        | .ret (.pair w p') =>
            some (Kᵢ ++ Frame.handleF n (.custom ℓ' p' clauses) :: Kₒ, .ret w)   -- REINSTALL p', RESUME w
        | other => some (Kᵢ ++ Frame.handleF n (.custom ℓ' p clauses) :: Kₒ, other)  -- back-compat: read-only
    | none => none
```

This is *exactly* `state`'s PUT (reinstall a changed carried value + resume) with the split of the
pair being the one extra step. The `other` fall-through preserves v1 read-only clauses byte-for-byte
(a `ret w` clause reinstalls `p` unchanged) — so D5 is **additive**, not a rewrite of the existing
arm. The RET path (handler return clause) already sees the FINAL `p` — it is `handleF n (custom ℓ'
p_final cls)` at the moment `M` returns, and the return clause is the identity (ADR-0023 Q6), so
"does the ret clause see the final param?" — YES, structurally, no change (the identity return
ignores it in v1; a param-consuming return clause is a further, orthogonal generalization).

### 1.3 Invariant #5 — D5 is a refinement, not a sixth primitive

The five primitives are thunk · force · effect rows · handlers · STM (`CLAUDE.md` invariant #5). D5
touches the **handlers** primitive only, and only its `custom` constructor's *dispatch behaviour* —
the same class of change ADR-0025 made when it turned `state` from zero-shot to resumptive, and
ADR-0030 made adding `transaction`. No new `Handler` constructor, no new `Comp` former (shape A),
no new kernel object. **The `state` PUT arm is the existence proof**: a parameterised handler that
reinstalls a changed carried value is ALREADY in the kernel and ALREADY typed (`handleState`,
`krelS_state_reinstall` PUT arm). D5 gives the *user-effect* (`custom`) arm the capability the
*built-in* (`state`) arm already has. This is "one construct per problem" (SOUL): rather than a
bespoke mutable-user-effect primitive, generalize the arm that already does it.

---

## 2 · The typing delta — the ret-shape wall, and how the pair shape clears it

### 2.1 What v1's typing pins (and why)

`HasClauses.cons` (`Typing.lean:371`) requires each clause `body = Comp.ret w` with the resumed
value `w : opRes ℓ op` typed under `[opArg@0, P@1]`. The load-bearing reason is the
**answer-grade freedom** (`ctr-design.md` §2.3, the D4 wall): the resume focus `ret (w[…])` must
plug into `Kᵢ` at the perform's returner type `F q_perf (opRes ℓ op)` where `q_perf` is FREE. Only a
`ret <closed value>` re-derives its grade for ANY `q_perf` (via `HasCTy.ret`'s grade-freedom); a
general effectful body carries a FIXED grade and cannot adapt. This is proven in
`custom_resume_focus_types` (`Soundness.lean:2177`): it types `subst p (subst (shift v) (ret w)) :
F q_perf opR` for arbitrary `q_perf`, by inverting the closed `ret` and re-`ret`-ing at `q_perf`.

### 2.2 The pair shape STAYS inside the ret-shape (the key tractability finding)

**D5 shape (A) does NOT breach the D4 ret-shape wall.** The clause body is still `Comp.ret w'` with
`w' = pair w p'` a CLOSED value — the resume focus is still a `ret` of a closed value, so
`custom_resume_focus_types`'s grade-freedom argument goes through UNCHANGED (invert the closed ret,
re-ret at `q_perf`). The typing delta is purely in `HasClauses`:

```
 HasClauses.cons  (v1):   HasVTy [qa,qp] [opA, P]  w          opR                -- resume value : opR
 HasClauses.cons  (D5):   HasVTy [qa,qp] [opA, P]  (pair w p') (prod opR P)      -- resume value + new param
```

The new param `p'` is typed at `P` (the SAME carried-param type — a parameterised handler keeps its
param type fixed across resumes, Plotkin–Pretnar) under the clause's binders `[opArg@0, P@1]`. So `p'`
may depend on the current param `p` (index 1) and the op arg `v` (index 0) — exactly `p' = f(p, v)`,
the state-update shape. **This is why D5 is a TYPING cost, not a semantic one** (survey EA2): the
reinstall already works (§1); what v1's typing forbids is the clause *returning* the update, and the
pair shape clears that without touching the answer-grade freedom.

### 2.3 One-shot is preserved — D5 does NOT smuggle in multi-shot

ADR-0025's one-shot-in-place resume is load-bearing (the K axis / Q22, `multishot-survey.md`). D5
does not touch it: the clause still resumes `Kᵢ` EXACTLY ONCE (tail-implicit, no first-class `k`),
and the reinstalled `handleF n (custom ℓ' p' cls)` is a deep-handler reinstall (one continuation,
one resume), identical to `state`'s PUT. The param-update threads a VALUE through the single resume;
it adds no continuation capture. So D5 is strictly rung-2 (parameterised), strictly below rung-3
(bidirectional) and orthogonal to the K/multishot axis — the survey's placement holds.

### 2.4 The B-occ anti-escape premise

`handleCustom` carries `¬ LabelOccurs ℓ A` (`Typing.lean:354`) — the handled label may not occur in
the answer type. D5 adds a param `p' : P` at each resume; the analogue of `StateEscapeWitness` applies:
a cap-typed param `P = cap ℓ'` is inhabited only by a closed `vcap`, which VcapFree forbids, so a
cap-holding param is uninstantiable — the closed-param premise `HasVTy [] [] p P` (which the *initial*
`p` must satisfy, `Typing.lean:349`) is the guard, and each reinstalled `p'` is likewise closed (the
focus is closed). **No new escape surface** — the `state`-escape verdict (task #50) transfers verbatim
to the param.

---

## 3 · The counter-example discipline — what D5 makes expressible (be honest)

**Verdict: ergonomics + the sim-map ENCAPSULATION class, NOT new computational power.** The witness
`Bang/Witness/D5ParamHandlerWitness.lean` makes this concrete and machine-checked:

```
 §  witness                    shows                                                   guard
 ── ─────────────────────────  ──────────────────────────────────────────────────────  ──────────────
 1a stateUpdate                the UPDATE mechanism ALREADY lives in the kernel          = 7
                                (state put reinstalls a changed value)
 1b stateAccumulate            evolving handler memory across two puts, ZERO driver      = 7
                                plumbing — the D5 shape, via the built-in state effect
 2  stepSeedBefore  (v1)       the DST-lcg seed threaded through the DRIVER's args        = 48355
    seedInStateAfter (D5)      the SAME fold with the seed in a state handler —          = 48355
                                driver stops carrying it. BEFORE == AFTER (same value).
 3  simMapThreadedByDriver     the sim-map shape v1 must thread through the driver        = 3
                                because a USER effect cannot own it
```

The decisive pair is §2: `stepSeedBefore` (v1 driver-threading) and `seedInStateAfter` (seed in a
handler) compute the **identical** value `lcg(lcg(12345)) = 48355`. **D5 changes WHO owns the state
(handler vs. driver), not WHAT is computable.** So:

- **The DST/Sched class is ERGONOMIC.** `examples/dst-rounds-lcg/main.bang` threads the seed through
  `go n s acc` (the driver's own args) because the `Sched` custom handler is read-only; D5 moves the
  seed into the handler. Same answers (the example's 9/16 convergence is unchanged), fewer moving
  parts in the driver. The README already flags this as "the before/after ergonomics benchmark the
  day the CTR gate lands" — D5 IS that day for the handler-memory half.

- **The genuinely-blocked class is SIM-MAP ENCAPSULATION for USER effects.** The built-in `state`
  already gives handler-owned, interface-hidden memory (§1b hides the seed). What v1 CANNOT do is
  give that to a USER-DECLARED effect: a `Fs` sim wanting a growing `file → content` map behind the
  `Fs` interface, or a `Sched` wanting an evolving queue behind `Sched`, must either (a) leak the
  map/queue into the driver's args (the dst workaround), or (b) run a built-in `state` ALONGSIDE the
  user effect — two handlers where one construct should suffice (the "one construct per problem"
  cost). D5 collapses (b) into one user-effect handler. This is real, but it is *encapsulation*, not
  new expressive power: the value set is unchanged (there is no D5 program whose VALUE a ret-shape
  threading cannot also reach — §2 proves the fold is identical).

**The honest one-liner (survey EA2 confirmed): D5 is an encapsulation/ergonomics lift for user
effects — the `state` parameterised handler generalized from built-in to user-declared — not a new
class of computable result.**

---

## 4 · The blast radius — MEASURED, and why the state PUT arm bounds it

Census of the custom-rep consumers (grep across `Bang/`, `Handler.custom | .custom | handleCustom |
HasClauses | dispatchOn`): **519 raw hits across 26 files.** The overwhelming majority are
NAME-mentions or proof arms that pass the rep THROUGH unchanged; the load-bearing set — where D5's
*param-update* actually ripples — is small and every member has a `state` twin already proven.

### 4.1 The rep-shape ripple is ZERO (shape A adds no field)

Because shape (A) adds no constructor field, the ~519 sites that pattern-match `custom ℓ p cls`
compile UNCHANGED. The engines' custom arms already thread `p`:

```
 engine                       custom-arm site                    D5 delta under shape (A)
 ──────────────────────────   ────────────────────────────────  ────────────────────────────────────
 Source.step / dispatchOn     Dispatch.lean:177-181              +1 pair-decode (§1.2) — the arm
 evalD (CalcVM)               AbstractMachine.lean:318-321        +1 pair-decode (κ.get? path); PUSH/POP
                              (CStore = id ↦ (param, clauses))     of κ is unchanged (param already threaded)
 EnvMachine (default engine)  7 custom sites                     +1 pair-decode (mirror dispatchOn)
 exec / wexec (calc + WasmGC) Wasm.lean:41 sites, U5bComplete:18  the S4 arm reinstalls p → reinstall p'
 emitter (S4)                 WasmEmit.lean:13 sites              runtime $box already carries the param
```

Each engine delta is "decode the pair, reinstall `p'`" — mechanically identical across engines
(invariant #1: they stay diff-tested against `Source.eval`). The differential-test harness
(`AgreeOutcome`, `Fuzz`) re-runs all engines against the oracle, so the engine ripple is
build-and-diff-gated, not proof-gated.

### 4.2 The PROVEN-SPINE ripple — the real cost, but TEMPLATED

The theorems whose STATEMENTS or PROOFS depend on the custom clause resuming with `p` UNCHANGED:

```
 theorem                            file:line              D5 delta                        state twin (the template)
 ────────────────────────────────   ────────────────────  ──────────────────────────────  ──────────────────────────
 HasClauses.cons                    Typing.lean:371       body ret w → ret (pair w p'),    (the rule itself; new)
   (the typing rule)                                       resume-val type opR → prod opR P
 custom_resume_focus_types          Soundness.lean:2177   grade-freedom on ret (pair …);   (ret-shape holds — §2.2)
   (resume typing at q_perf)                                the pair is still a closed ret
 handleCustom_inv / concat_custom_* Soundness.lean:1735,  thread p' through the inversion  concat_state_* (proven)
   (the handle inversion lemmas)      2093, 2117
 custom_program_safe_proof          Soundness.lean:3392   preservation with p := p'        state_program_safe (proven)
 no_accidental_handling_custom      Soundness.lean:3367   unchanged (label-dispatch)       (proven; no ripple)
 custom_clause_resume(_of)          BinaryLR.lean:1253,   yields (w, p') not just w        clause_resume (state get/put)
                                      1743
 krelS_custom_reinstall             BinaryLR.lean:1307    reinstall p'₁/p'₂ (CHANGED) —    krelS_state_reinstall PUT arm
   (the LR resumptive heart)                               the IH runs at the NEW param      (Soundness/BinaryLR:700-706)
                                                            pair, exactly state's PUT
 compatK_handleCustom               BinaryLR.lean:1363    thread the update through compat  compatK_handleState (proven)
```

**The load-bearing finding: `krelS_state_reinstall`'s PUT arm (`BinaryLR.lean:700-706`) is a
FULLY-WORKED template for `krelS_custom_reinstall` under param-update.** Its own comment
(`BinaryLR.lean:1301-1303`) says the custom reinstall is "STRICTLY SIMPLER" *because* v1 is
read-only (`p=p`) "unlike state's put, which reinstalls a *changed* value." D5 REMOVES that
simplification — the custom reinstall becomes the state PUT arm's twin: the guarded-recursion IH runs
at the NEW param pair `(p'₁, p'₂)` (state does `(w₁, w₂)` at line 702). So D5's hardest proof
obligation is **already discharged for `state`** and needs porting, not inventing. This is what bounds
D5 to a *bounded* M/L rather than an open-ended research proof: every obligation has a green twin.

The one genuinely-new sub-obligation: the clause now returns a PAIR, so `custom_clause_resume` must
project the pair into (resume-value, new-param) and relate each — a `pair`-splitting step with no
`state` analogue (state's payload is a single value). This rides the existing `VrelK` product
machinery (the ADT `pair` relation already exists), so it is a lemma-composition, not a new relation.

---

## 5 · Slice map + effort — the cheapest honest entry

```
 slice   stratum              content                                                      effort   gate
 ─────   ──────────────────   ──────────────────────────────────────────────────────────  ──────   ──────────────────────
 S0      kernel def           dispatchOn custom arm: pair-decode + reinstall p' (§1.2);     S        #guard witnesses
         (SEMANTIC — CHEAPEST  fall-through preserves v1 read-only. NO rep change.            (1-2d)   (a D5 pair-clause
          ENTRY)               Extend D5ParamHandlerWitness with a CUSTOM (not state)                 evolving-memory eval)
                               param-update #guard once the arm lands.
 S1      engines              evalD / EnvMachine / exec / wexec custom arms: mirror S0's     M        AgreeOutcome + Fuzz
         (diff-tested)         pair-decode. exec/wexec = the L-size hiders (#62 history).     (2-4d)   diff-test all engines
                               Emitter S4: reinstall p' in the runtime $box.                          == Source.eval
 S2      typing               HasClauses.cons: body → ret (pair w p'), resume type →         M        lake build (the rule
                               prod opR P (§2.2). handleCustom rule unchanged (§2.4).         (2-3d)   types real programs)
 S3      soundness            handleCustom_inv, concat_custom_*, custom_resume_focus_types,  L        #print axioms ⊆
         (PROVEN SPINE)        custom_program_safe: port from the state twins (§4.2). The     (1-2wk)  trusted-3; custom_
                               pair-projection is the one new step.                                    program_safe green
 S4      LR (binary)          krelS_custom_reinstall (port state PUT arm), custom_clause_    L        #print axioms ⊆
         (PROVEN SPINE)        resume (pair-project), compatK_handleCustom. The resumptive    (1-2wk)  trusted-3; lr_sound
                               heart — the state PUT arm is the skeleton.                               unaffected
```

**Cheapest honest entry = S0 (the semantic arm).** It lands the capability at the kernel, witnessed
by a runnable custom-param-update `#guard`, WITHOUT touching a single proof — the tested-superset
gains handler memory for user effects immediately (diff-tested via S1), and the proven-core
re-grade (S2–S4) follows as a separate, templated push. This mirrors the ADR-0085 stage ladder
(rep → dispatch → typing → calc → LR) that landed `custom` itself: semantics first, proof after,
each stage independently gated.

**The costed verdict for the HOLD:** D5 is a **BOUNDED multi-session L** (S0–S2 ship a tested-superset
capability in ~1 week; S3–S4 re-establish the proven core in ~2–4 weeks by porting the `state` PUT
twins). It touches the proven spine but invents no new proof technique — the `state` parameterised
handler is the existence proof and the template throughout. It is NOT a research risk; it IS a real
proof-porting investment. Recommendation: land S0–S1 (tested-superset handler memory for user
effects) when the DST/Sched/Fs-sim lanes want it, gate S2–S4 as a dedicated proven-core increment,
and file the ADR at S0 (the pair-shape decision §1.2 is the fork a future session could reverse).

---

## 6 · ADR-inputs (present, don't decide)

```
 # ADR-input                                                                when              rides
 ── ──────────────────────────────────────────────────────────────────     ───────────────   ──────────────────────────
 D5-1 The param-update SHAPE is (A) pair-yielding clause (ret (pair w p')), S0 (the fork)      Dispatch.lean:181;
      NOT a new Comp former — no 6th primitive, the pair is the existing ADT.                   IR pair; invariant #5
 D5-2 D5 is a TYPING cost, not a semantic one — the reinstall (state PUT)     framing (adopt)   memory-survey §1.2;
      already exists; the pair stays inside the D4 ret-shape wall (§2.2).                        survey EA2
 D5-3 The proof burden is TEMPLATED by krelS_state_reinstall's PUT arm —      S3/S4             BinaryLR.lean:700,1307
      bounded L, port don't invent. The pair-projection is the one new step.
 D5-4 D5 is ergonomics + sim-map encapsulation for USER effects, NOT new      framing (adopt)   §2/§3 witnesses;
      computational power (§2: before == after value).                                          survey EA2
 D5-5 One-shot is preserved (§2.3) — D5 is rung-2, orthogonal to K/Q22.       framing            multishot-survey Q22
```

---

## References

Internal: `effect-algebra-survey.md` §2 (the rung-1→2 ladder; EA2 = state-as-handler-memory ≡ D5) ·
`memory-management-survey.md` §1.2 (D5 = the state-arm swap generalized to custom; M1) ·
`ctr-design.md` §2.3 (the D4 answer-grade wall the pair shape clears) · `multishot-survey.md` (Q22 =
the K axis, orthogonal) · `stage5-lr-design.md` (the LR ret-shape tractability the pair inherits).
Code: `IR.lean:176` (custom rep already carries `p`) · `Dispatch.lean:137` (state PUT = the changed-
value reinstall template) `:177-181` (custom arm, read-only param — the ONE arm D5 lifts) ·
`Typing.lean:371` (HasClauses.cons ret-shape) `:339-355` (handleCustom rule) · `Soundness.lean:2177`
(custom_resume_focus_types — the grade-freedom the pair preserves) `:3392` (custom_program_safe) ·
`BinaryLR.lean:662,700` (krelS_state_reinstall + its PUT arm = D5's template) `:1307` (krelS_custom_
reinstall — read-only today, the heart to lift) · `AbstractMachine.lean:318` (evalD custom arm, CStore)
· `Bang/Witness/D5ParamHandlerWitness.lean` (6 green `#guard`s plus a typed updating-clause theorem:
the mechanism + the before/after).
ADRs: 0025 (resumptive state — the parameterised-handler precedent) · 0030 (transaction — multi-cell
state) · 0085 (custom coexist, one-shot v1) · 0087 (finite rep + §Open-questions where param-update
is named) · 0092 §D5 (the read-only-param deferral this note designs the lift of) · 0095 (surface;
its "(D5)" is a DIFFERENT D5 — resume spelling). Invariants: #1 (diff-test), #4 (calc), #5 (five
primitives). External: Plotkin & Pretnar, ESOP 2009 (`plotkin-esop09`) — parameterised handlers.
