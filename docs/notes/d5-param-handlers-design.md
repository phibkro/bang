<!-- note-status: active -->
# D5 — parameterised handlers (handler memory): design probe with HOLD (#44 rung-2 face)

> The task (2026-07-12, Wave C): design **D5 — parameterised handlers / handler memory**, the
> rung-1→2 boundary of the effect-algebra ladder (`effect-algebra-survey.md` §2, Plotkin–Pretnar
> [plotkin-esop09]) and the unlock three lanes independently worked around this week: the Sched
> demo's seed/queue threading through the driver, the DST examples' ret-shape contortions, the Fs
> sim-map wanting state. **ADR-input probe, not an ADR — DESIGN-FIRST with a HOLD before any
> implementation** (the proven spine is touched). Every kernel claim is `file:line` or ADR; the
> ergonomic claim is a runnable witness (`Bang/Witness/D5ParamHandlerWitness.lean`, 5 `#guard`s
> green). Terminology guard: the "**D5**" here is the effect-algebra ladder's rung-2 **param-update**
> (ADR-0092 §D5 open item / ADR-0087 §Open-questions) — NOT ADR-0095's decision-list "(D5)" (the
> `resume` surface spelling), a different D5.

---

## 0 · The four-line verdict

```
WHAT     D5 = a parameterised custom handler reinstalls an UPDATED carried param `p'` (from the
         clause), not `p` unchanged. The mechanism is the `state`-arm `put` swap (Dispatch.lean:137).
KERNEL   OPT-IN AT THE REP (amended §0.5): a NEW `Handler.customUpd` constructor, distinct from the
         read-only `custom`. Param-update is NEVER inferred from the clause's YIELD shape (that would
         silently reinterpret a legal v1 clause returning a pair AS ITS VALUE — the soundness gap the
         team-lead caught, §0.5). `customUpd`'s clause yields `ret (pair w p')`; UNMARKED `custom` is
         byte-identical to today. NO 6th primitive (a 5th `Handler` constructor, invariant #5 holds).
COST     Re-measured under the marker (§4): the UNMARKED-path ripple is ZERO by construction (every
         existing `custom` statement/proof unchanged). The new-path cost = additive `customUpd` arms
         (~50 match-sites gain a parallel arm) + the proven spine, TEMPLATED by the `state` PUT twin —
         a BOUNDED M/L, mirror `state`, don't invent.
HONESTY  For the DST/Sched class the win is ERGONOMIC (v1 threads the same values through the driver;
         §2 witness: before == after). The non-ergonomic win is the SIM-MAP ENCAPSULATION class:
         handler-owned state behind a USER-effect interface. NOT new computational power (§3).
```

---

## 0.5 · AMENDMENT (2026-07-12, team-lead review) — OPT-IN at the rep, yield-sniffing REJECTED

The originally-recommended shape (§1.2 shape A: dispatch decodes `ret (pair w p')` as
value-plus-param-update) has a **soundness gap**: it infers param-update from the clause's YIELD
SHAPE. An EXISTING legal v1 clause that legitimately returns a pair AS ITS VALUE — `read(x) => ret
(pair a b)` typed at `opRes ℓ read = prod A B` — would be SILENTLY reinterpreted as "resume with `a`,
update param to `b`". That is a semantics change to already-shipped programs: the silent-wrong class,
the exact failure `CLAUDE.md`'s "make illegal states unrepresentable" forbids. **Yield-sniffing is
rejected.** (Recorded as the rejected alternative in the ADR — it is what a future session WILL
re-propose.)

**The fix — D5 is OPT-IN at the REP level, not inferred:**

```
 IR.lean:  | custom    : Label → Val → List (OpId × Comp) → Handler    -- UNCHANGED (read-only param)
           | customUpd : Label → Val → List (OpId × Comp) → Handler    -- NEW: parameterised (updatable)
```

- **A NEW constructor `customUpd`, not a field on `custom`.** Chosen over a mode-FLAG (`custom : … →
  ParamMode → …`) precisely to satisfy the team-lead's condition (3): with a distinct constructor,
  every existing `custom` match-arm, theorem STATEMENT, and proof is **definitionally unchanged**
  (they match `custom`, which did not move). A flag would touch all 134 construct-sites AND
  re-state every theorem mentioning `Handler.custom ℓ p cl` (the ~50 match-sites' statements) — the
  unmarked path would NOT be definitionally unchanged, so it would be a "red spine," not a
  tested-superset (condition 3 fails). The new constructor is the only shape where the unmarked path
  is untouched by construction.
- **The surface marks it explicitly.** ADR-0095 already lowers a param-carrying `handle … with Name
  as h { … }` to `.custom ℓ v clauses` (read-only, `param` names the carried Val, `#87`). The D5
  spelling adds an explicit opt-in — recommendation: a clause that WRITES the param uses a distinct
  form (`op(x) => resume(w) with param := p'`, or a handler-level `mut param` marker), lowering to
  `customUpd`. A non-writing handler stays `custom`. The exact surface token is the Stage-7 lane's
  call (rides ADR-0095 D5's reserved `resume`); the KERNEL commitment is only that the two are
  distinct constructors.
- **`customUpd`'s clause still yields `ret (pair w p')`** — but now that shape is only DECODED under
  `customUpd`'s dispatch arm, where it is the DECLARED contract, never sniffed. A `custom` clause
  yielding a pair keeps getting the pair as its value (the regression witness §3-new pins this).

Everything below that says "shape A" / "ZERO rep change" / "one arm" is READ THROUGH THIS AMENDMENT:
the pair-decode is shape A, but it lives ONLY in the `customUpd` arm; the rep gains a constructor
(not zero-rep, but the unmarked-path ripple is zero); the proof analysis (§2, §4.2, the state-PUT
templating) transfers verbatim to the `customUpd` arm.

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

> ⚠ READ §0.5 FIRST. The shape-(A) pair-yield below is CORRECT as the clause contract, but it must NOT
> be SNIFFED from a `custom` clause's yield (that silently reinterprets a legal pair-returning v1
> clause — the soundness gap). The pair-decode lives ONLY in the NEW `customUpd` arm; the analysis
> below describes that arm. "the custom arm" throughout §1.2 means "the `customUpd` arm."

The v1 clause body is `Comp.ret w` — it yields ONE value, the resume value `w` fed to `Kᵢ`
(`Typing.lean:376`; `HasClauses.cons` fixes `body = Comp.ret w`). D5 needs the clause to yield TWO
things: the resume value `w` AND the updated param `p'`. Three candidate shapes, one recommended:

```
 shape                       clause body           dispatch decode             verdict
 ─────────────────────────   ───────────────────   ─────────────────────────   ─────────────────────────
 (A) PAIR-yielding clause    ret (pair w p')       split the returned pair      RECOMMENDED — zero new
     under `customUpd`         (w = resume,          in the customUpd arm;        Comp former (`pair` is the
     (the state PUT shape)      p' = new param)      reinstall customUpd ℓ p'     ADT); the clause STAYS
                                                     cls, resume Kᵢ with w        `ret <closed>` (§2.2)
 (B) new Comp former          customYield w p'      a bespoke reduction rule    REJECTED — a kernel former
     `customYield`                                   in Source.step               (invariant #5 pressure); the
                                                                                  pair encoding subsumes it
 (C) param as a 2nd clause    (ret w, ret p') a      two sub-derivations per     REJECTED — doubles the
     component (product cls)   product clause body    clause; blows up HasClauses  clause typing, no gain
 (X) YIELD-SNIFFING on        custom clause yields   the custom arm decodes a     REJECTED (§0.5) — SILENTLY
     `custom` (the naive       ret (pair w p')        pair-yield as an update      reinterprets a legal v1 pair-
      first draft)                                                                 returning clause: soundness gap
```

**Recommendation: (A) pair-yielding, under the NEW `customUpd` constructor.** The clause body is
`Comp.ret w'` with `w' = pair w p'` a CLOSED value (focus-closed discipline holds — no new Comp
former, invariant #5, the `pair` is the existing ADT). The decode lives in a NEW dispatch arm for
`customUpd`, leaving the `custom` arm BYTE-IDENTICAL:

```
-- the EXISTING custom arm — UNCHANGED (Dispatch.lean:177-181, read-only param):
| .custom ℓ' p clauses =>
    match clauses.find? (·.1 == op) with
    | some clause => some (Kᵢ ++ Frame.handleF n (.custom ℓ' p clauses) :: Kₒ,
                           Comp.subst p (Comp.subst (Val.shift v) clause.2))    -- reinstall p UNCHANGED
    | none => none

-- the NEW customUpd arm — the ONLY place a pair-yield is decoded as an update:
| .customUpd ℓ' p clauses =>
    match clauses.find? (·.1 == op) with
    | some clause =>
        -- customUpd's clause CONTRACT is ret (pair w p') (typed by HasClausesUpd, S2) — DECLARED, not sniffed.
        match Comp.subst p (Comp.subst (Val.shift v) clause.2) with
        | .ret (.pair w p') =>
            some (Kᵢ ++ Frame.handleF n (.customUpd ℓ' p' clauses) :: Kₒ, .ret w)   -- REINSTALL p', RESUME w
        | other => some (Kᵢ ++ Frame.handleF n (.customUpd ℓ' p clauses) :: Kₒ, other)  -- ill-typed guard
    | none => none
```

This is *exactly* `state`'s PUT (reinstall a changed carried value + resume) with the pair-split the
one extra step — but confined to `customUpd`, so a `custom` clause returning a pair keeps getting the
pair as its VALUE (the §3-new regression witness pins this; the pair-decode NEVER runs on `custom`).
The `other` fall-through is an ill-typed guard (S2's `HasClausesUpd` forces the pair shape, so it is
source-unreachable). The RET path (handler return clause) sees the FINAL `p'` — the frame at return is
`handleF n (customUpd ℓ' p_final cls)`, return clause = identity (ADR-0023 Q6), so "does the ret
clause see the final param?" — YES, structurally, no change.

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

## 4 · The blast radius — RE-MEASURED under the `customUpd` marker (§0.5 amendment)

Census of the custom-rep consumers (grep across `Bang/`): **519 raw hits across 26 files**, split into
**134 CONSTRUCT-sites** (`Handler.custom ℓ …` built) and **160 MATCH-sites** (`| .custom …`
destructured). This split is what decides the marker shape:

```
 marker shape                 UNMARKED-path ripple            new-path cost                verdict
 ──────────────────────────   ─────────────────────────────  ──────────────────────────   ─────────────────────────
 (M-flag) field on custom     ALL 294 sites (every construct  branch on the flag in the    REJECTED — the unmarked
   `custom : … → Mode → …`      + every match re-patterns;      dispatch arm                 path is NOT definitionally
                                every theorem mentioning                                     unchanged ⇒ RED SPINE
                                `custom ℓ p cl` re-states)                                    (condition 3 fails)
 (M-kind) new customUpd        ZERO (custom unmoved — every    ~50 additive customUpd       CHOSEN — unmarked path
   constructor                   match-arm/theorem/proof         match-arms (mechanical,      byte-identical BY
                                 byte-identical)                 mostly = the custom arm) +   CONSTRUCTION (condition 3
                                                                 the param-update proof spine  met definitionally)
```

**Chosen: M-kind (new `customUpd`).** The team-lead's condition (3) — "the unmarked path is
definitionally unchanged, or it's a red spine" — is satisfiable ONLY by a distinct constructor: the
160 match-sites and every theorem STATEMENT mentioning `Handler.custom ℓ p cl` (`custom_handlesWithin`,
`no_accidental_handling_custom_proof`, `custom_program_safe_proof`, …) stay byte-for-byte, because
they destructure `custom`, which did not move. The cost moves to ADDITIVE `customUpd` arms.

### 4.1 The new-path ripple — additive `customUpd` arms (~50 match-sites gain a parallel arm)

Every place that currently has a `custom` arm gains a `customUpd` sibling. Most are MECHANICALLY the
`custom` arm (a parameterised handler shares label/clauses/param structure) — the ONLY arms that
genuinely differ are the reinstall (dispatch) and the typing rule. Per-engine:

```
 engine                       custom match-arms   customUpd delta
 ──────────────────────────   ─────────────────   ─────────────────────────────────────────────────
 Source.step / dispatchOn     Dispatch.lean:3      +1 arm: pair-decode + reinstall p' (the ONE new
                              (handlesOp/dispatch)  semantics; §1.2 shape A, now under customUpd only)
 evalD (CalcVM)               AbstractMachine:8    +customUpd arms: κ.get? pair-decode + PUSH/POP
                              (CStore path)         (mirror the custom arm, reinstall p')
 EnvMachine (default engine)  4                    +customUpd arms (mirror dispatchOn)
 exec / wexec (calc + WasmGC) Wasm.lean:15         +customUpd arms: reinstall p' in the $box
 emitter (S4)                 WasmEmit:13-site set  +customUpd lowering (runtime $box carries param)
 Subst / Freshness / capsH    Subst:3, Fresh:6     +customUpd arms = the custom arm VERBATIM (subst
                              (rep-traversal)       the param + clauses; capsH traverses clauses) —
                                                    zero-semantics, pure structural duplication
```

The rep-traversal arms (subst, freshness, cap-enumeration) are the custom arm copied verbatim — a
`customUpd` handler substitutes/enumerates identically to a `custom` one (same fields). Only
dispatch + typing carry real logic. Each engine's `customUpd` dispatch is "decode the pair, reinstall
`p'`" — diff-tested against `Source.eval` (invariant #1); the `AgreeOutcome`/`Fuzz` harness re-runs
all engines against the oracle, so the engine ripple is build-and-diff-gated, not proof-gated. AND
the whole EXISTING corpus (all `custom`, no `customUpd`) runs byte-identical every slice — condition
(2), enforced by the differential harness on an unchanged `custom` path.

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

## 5 · Slice map + effort — the cheapest honest entry (under the `customUpd` marker)

```
 slice   stratum              content                                                      effort   gate
 ─────   ──────────────────   ──────────────────────────────────────────────────────────  ──────   ──────────────────────
 S0      kernel rep + arm     ADD `Handler.customUpd` (§0.5); its dispatchOn arm pair-      S/M      #guard: customUpd
         (SEMANTIC — CHEAPEST  decodes + reinstalls p'. `custom` arm UNCHANGED. Structural   (2-3d)   evolving-memory eval;
          ENTRY)               arms (subst/freshness/capsH) get customUpd = the custom arm            + REGRESSION #guard: a
                               verbatim. Regression witness: a `custom` clause returning a            `custom` pair-return
                               pair still gets the pair as VALUE (§3-new).                             gets pair as VALUE
 S1      engines              evalD / EnvMachine / exec / wexec: add customUpd arms         M        AgreeOutcome + Fuzz +
         (diff-tested)         (mirror S0). exec/wexec = the L-size hiders (#62). Emitter    (3-5d)   WHOLE-CORPUS diff run
                               S4: customUpd lowering. custom path byte-identical.                    (all custom, unchanged)
 S2      typing               ADD `HasClausesUpd` (customUpd's clause typing): body →       M        lake build (the rule
                               ret (pair w p'), resume type prod opR P (§2.2); handleCustomUpd (2-3d) types real programs;
                               rule. `HasClauses`/`handleCustom` UNCHANGED.                            handleCustom untouched
 S3      soundness            customUpd_resume_focus_types, handleCustomUpd_inv, concat_    L        #print axioms ⊆
         (PROVEN SPINE)        customUpd_*, customUpd_program_safe: port the custom/state    (1-2wk)  trusted-3; the custom_*
                               twins (§4.2). custom_* lemmas UNCHANGED (byte-identical).              proofs still green
 S4      LR (binary)          krelS_customUpd_reinstall (port state PUT arm), customUpd_    L        #print axioms ⊆
         (PROVEN SPINE)        clause_resume (pair-project), compatK_handleCustomUpd. The    (1-2wk)  trusted-3; lr_sound
                               state PUT arm is the skeleton. krelS_custom_reinstall UNCHANGED.        + custom LR unaffected
```

**The four HARD conditions (team-lead review) gate every slice:**

```
 (1) OPT-IN at the rep — customUpd is a NEW constructor, param-update NEVER sniffed from the yield.
     The ADR records yield-sniffing as the REJECTED alternative (§0.5).
 (2) The WHOLE existing corpus byte-identical under a differential run EVERY slice — non-customUpd
     handlers are untouchable (enforced by the AgreeOutcome/Fuzz harness on the unchanged custom path).
 (3) Headline axioms green EVERY push — S0's arm is a NEW customUpd arm; the custom arm's equation is
     definitionally unchanged, so NO proof arm referencing the old equation breaks (that is WHY M-kind,
     not M-flag). If a custom proof arm broke, the slice would be a red spine, not tested-superset.
 (4) A pair-valued-clause REGRESSION witness pins that a NON-marked `custom` handler returning
     pair(w,x) still gets the pair as its VALUE — the exact regression yield-sniffing would have caused,
     pinned BEFORE it can ever happen (lands in S0).
```

**Cheapest honest entry = S0 (the semantic arm + the regression witness).** It adds `customUpd` at the
kernel with its dispatch arm and the regression pin, WITHOUT touching a single `custom` proof — the
tested-superset gains handler memory for user effects (diff-tested via S1), the `custom` path stays
byte-identical, and the proven-core re-grade (S2–S4) follows as a separate, templated push over
`customUpd`-specific lemmas. This mirrors the ADR-0085 stage ladder (rep → dispatch → typing → calc →
LR) that landed `custom` itself.

**The costed verdict:** D5 is a **BOUNDED multi-session L** (S0–S2 ship a tested-superset capability
in ~1 week; S3–S4 re-establish the proven core in ~2–4 weeks by porting the `state` PUT / `custom`
twins). It touches no `custom` proof (M-kind keeps them definitionally unchanged) and invents no new
proof technique — the `state` parameterised handler is the template throughout. Recommendation
(team-lead APPROVED, conditions above): land S0–S1 (tested-superset), gate S2–S4 as a dedicated
proven-core increment, file the ADR at S0 (the `customUpd` constructor + the yield-sniffing rejection
are the forks a future session could reverse).

---

## 5.5 · IMPLEMENTATION HANDOFF (branch `impl-d5-param-handlers`, WIP — SUBSET-GREEN, ENGINES PENDING)

**Status as banked (the #62-slice-3 bank-and-hand-off precedent):** the kernel `Handler.customUpd`
constructor + the `Source.eval` param-update dispatch arm + the ENTIRE route-A/LR proof-spine build
clean **as a subset** (`lake build Bang.Core.Soundness Bang.Meta.BinaryLR Bang.Core.CapCoh
Bang.Core.Freshness` → 717 jobs). What remains is the CalcVM calc-correctness + engine port — the L
that pulls `compile_correct` into scope. A fresh compiler-engineer successor takes it with full budget
(a lane deep in its session is the wrong vehicle for ~450 must-not-be-hollow proof arms). **The
successor lands ONLY whole-tree-green** (main never holds an IR constructor lacking engine arms) with
the whole-corpus differential + custom-byte-identical + REAL calc-correctness customUpd cases.

### The uninhabited-vs-real split (rider b — pre-empt the vacuous-forever trap)

Every customUpd proof case landed so far is ONE of two kinds. **A future auditor + the S2-typing
successor MUST know which**, because a case that is *vacuous today* (because `customUpd` is not yet
typeable) and *silently stays vacuous after S2 typing lands* is the trap:

```
 kind        where                                    why it's discharged that way        S2 obligation
 ─────────   ──────────────────────────────────────   ─────────────────────────────────   ────────────────────────
 VACUOUS     Soundness.lean: the 2 preservation-       customUpd is UNTYPED in S0 — no      When S2 adds
 (today)     dispatch sites + the 2 handle-MINT sites   `handleCustomUpd`/`customUpdF`       `handleCustomUpd` +
                                                         rule, so `HasStack`/`HasCTy` over    `customUpdF`, these
             `handle_customUpd_uninhabited`             a customUpd frame is uninhabited     become REAL cases —
             `concat_customUpd_absurd`                  (`cases h`/`cases hK` = 0 goals).    the `.elim` calls MUST
                                                                                              be REPLACED, not left.
 REAL        Freshness.lean (freshCfg_step customUpd),  these are RUNTIME invariants over    STAY real — S2 typing
 (now)       CapCoh.lean (weakCoh customUpd),           ANY config (not typing-gated), so    only ADDS the typed
             Dispatch dispatchOn arm, dispatchOn_isSome, customUpd IS reachable NOW; the      layer; these already
             return-pop, BinaryLR append_outer          proofs carry content (pair-decode    carry content.
                                                         split + clause-cap bound).
```

**The trap to pre-empt:** after S2 lands `handleCustomUpd`, the 4 VACUOUS Soundness sites are NO LONGER
vacuous (a well-typed program CAN now contain a customUpd frame). If a successor leaves the `.elim`
calls, the build BREAKS (the uninhabitedness lemmas become false) — which is the *good* failure (loud).
The trap is the inverse: a successor who "fixes" the break by re-proving uninhabitedness some other
vacuous way, hiding that the typed customUpd preservation was never actually proven. The S2 obligation
is to prove the REAL typed-preservation customUpd case (mirroring the `custom` case at
`Soundness.lean:2487`), NOT to keep it vacuous.

### The evalD param-update design (rider a — the engine approach, verified-then-reverted)

The evalD (CalcVM) customUpd arm was implemented and COMPILED, then reverted to keep the tree clean for
the bank. The design the successor re-applies:

```
 CStore payload  (Val × List(OpId×Comp))  →  (Val × List(OpId×Comp) × Bool)   -- +isUpd flag
 CStore.push     unchanged (isUpd = false — custom BYTE-IDENTICAL)
 CStore.pushUpd  new: (n, (p, cls, true)) :: κ                                  -- customUpd install
 CStore.setParam UPDATE-FIRST-MATCH (recursive, NOT map): stop at the first e.1=n              -- the param update
 handle arm      | .customUpd _ p cls => … κ.pushUpd id p cls … κ'.tail (POP like custom)
 perform service destructure (p, cls, isUpd); if isUpd: run clause → decode `.term (.ret (.pair w p'))`
                 → `κ'.setParam n p'` → resume `.term (.ret w)`; else custom-identical (read-only)
```

The `isUpd` flag reuses the SAME κ store (both custom + customUpd are keyed by the disjoint generative
identity) — chosen over a 4th store `κu` (which would ripple the CStore through all 71 evalD call sites
+ the ADR-0016 pipeline). The flag localizes to the 3 CStore defs + the 2 push sites + the service arm.

**`CStore.setParam` is UPDATE-FIRST-MATCH, not `map` (impl finding, S1).** The first-draft `κ.map (if
e.1=n …)` rewrites EVERY entry keyed `n`; the impl uses a recursive `setParam` that updates the FIRST
(innermost) match and stops. Why it matters: `customParamUpdate_setParam` (the machine↔store correspondence
— `customParamUpdate n p' hs` projects to `(hsCustoms hs).setParam n p'`) then commutes WITHOUT a
uniqueness premise. With `map`, the head case's residual is `(hsCustoms hs).setParam n p'` on the TAIL,
which differs from the machine's `hsCustoms (tail unchanged)` unless the tail has no key-`n` entry — a
freshness/uniqueness fact not locally available. Update-first-match matches `get?`'s innermost-wins and the
machine's `customParamUpdate` (which rewrites the first `id = n` frame), so the projection commutes
structurally. (The same reasoning is why a mid-body self-perform on a customUpd frame is a REAL net-effect
stack mutation — see the FrameMut(customUpd)=param-free finding: `netEffect` must apply `updateCustoms` to
reconstruct it, S1 route A1.)

### The engine census (the ~450-site shape — mechanical-verbatim vs genuinely-new)

```
 file                         customUpd-forced   MECHANICAL (= custom verbatim)     GENUINELY-NEW (real content)
 ──────────────────────────   ────────────────   ────────────────────────────────  ──────────────────────────────
 AbstractMachine.lean         303 + CStore ripple hsCustoms tuple, most exec arms,   the param-update service arm
   (evalD/compile/exec/         (101 downstream    subst/label traversal              (done, reverted); the
    compile_correct)            errors observed)                                      compile_correct customUpd case
 EnvMachine.lean              76                 the default-engine custom arms      the param-update env-machine arm
 U5bComplete.lean             48                 mostly rep-traversal                 the converse κ-thread case
 Wasm.lean (exec/wexec)       28                 GC/linear-mem custom arms            the $box param-update lowering
 WasmEmit.lean                2                  emit dispatch                        —
```

### The per-engine diff-gate plan (condition 2 — whole-corpus byte-identical every slice)

Each engine's customUpd arm is gated by the differential harness (`AgreeOutcome`/`Fuzz`, comparing the
engine against `Source.eval`). The whole EXISTING corpus (all `custom`, no `customUpd`) must run
byte-identical every slice — enforced by the harness on the unchanged `custom` path. A NEW witness
(rider from condition 4, NOT yet written) pins: (i) a `custom` handler returning `pair(w,x)` still gets
the pair as its VALUE (the yield-sniffing regression); (ii) a `customUpd` handler evolving its param
across performs (the D5 win) — both via `#guard` on `Source.eval`, then re-run against each engine.

---

## 6 · ADR-inputs (present, don't decide)

```
 # ADR-input                                                                when              rides
 ── ──────────────────────────────────────────────────────────────────     ───────────────   ──────────────────────────
 D5-0 D5 is OPT-IN at the REP: a NEW `customUpd` constructor (§0.5), NOT a  S0 (the DECISION) IR.lean custom rep;
      mode-flag and NOT inferred from the clause yield. YIELD-SNIFFING is                      invariant #5 (5th ctor)
      REJECTED (silently reinterprets a legal pair-returning v1 clause) —
      the ADR records it as the rejected alternative. M-kind chosen over
      M-flag so the unmarked `custom` path is DEFINITIONALLY unchanged.
 D5-1 customUpd's clause yields ret (pair w p') (shape A), decoded ONLY in   S0                Dispatch customUpd arm;
      its own dispatch arm — no new Comp former, the pair is the ADT.                          IR pair; invariant #5
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
· `Bang/Witness/D5ParamHandlerWitness.lean` (5 green `#guard`s: the mechanism + the before/after).
ADRs: 0025 (resumptive state — the parameterised-handler precedent) · 0030 (transaction — multi-cell
state) · 0085 (custom coexist, one-shot v1) · 0087 (finite rep + §Open-questions where param-update
is named) · 0092 §D5 (the read-only-param deferral this note designs the lift of) · 0095 (surface;
its "(D5)" is a DIFFERENT D5 — resume spelling). Invariants: #1 (diff-test), #4 (calc), #5 (five
primitives). External: Plotkin & Pretnar, ESOP 2009 (`plotkin-esop09`) — parameterised handlers.
