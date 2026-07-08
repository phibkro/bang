# ADR-0085 · User-defined effects: a general `custom` handler ALONGSIDE the built-in triple (coexist, one-shot v1)

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: #44 (user-defined effects — the moat: "paradigm and runtime are values") is blocked at the KERNEL, not the surface — the `Handler` type is a CLOSED triple (`state`/`throws`/`transaction`, `Bang/Core/IR.lean`) with operations hardcoded in `handlesOp`/`dispatchOn`. The **performer side is ALREADY general** (`perform`/`up` routes through `EffSig.opArg/opRes` — any label, any op; `EffSig` already IS the user-effect interface), so #44 is a HANDLER-side generalization. **Decision: COEXIST — add a fourth `Handler.custom : Label → Val → (OpId → Option Comp)` constructor ALONGSIDE the three built-ins, NOT collapse them into instances of it; scope v1 to ONE-SHOT tail-resumptive clauses (multi-shot deferred to Q22/Q27).** Coexist QUARANTINES the soundness risk behind the constructor seam (the project's own stratification principle): the trusted-three (`preservation`/`progress`/`type_safety`) can stay axiom-clean because their frozen statements are CONSTRUCTOR-AGNOSTIC (no Spec.lean statement changes — the ripple is ~424 ADDITIVE proof cases, not a re-freeze), and any gap that won't close lives in the NEW `custom` cases WITHOUT regressing the built-ins' clean census. **Rejected: INSTANCES (Option A — one `custom` ctor, the three derived from it)** — truer to minimality but routes the currently-CLEAN trusted-three THROUGH unproven general-handler soundness, risking a census regression; kept as a LATER census-preserving refactor once the general soundness + multi-shot grade (Q27) are settled. The single riskiest obligation is **invariant #4 — the calculated-machine re-derivation** (generalize `SStore`/`THeap` → a param store, DERIVE the custom `evalD`/`compile`/`exec` arm), entangled with the still-pending route-B (ADR-0052).
- **Depends-on**: 0022, 0023, 0025, 0052, 0054, 0055, 0063, 0070
- **Relates-to**: 0084 (networking = a small INSTANCE of #44 — this is its kernel gate), 0030 (STM = the transaction built-in this generalizes), Q39 (effects-as-typed-interfaces thesis), Q22 (labelling-vs-closure cap-rep — the multi-shot fork this DEFERS), Q27 (resumption grades — the type cost that later admits multi-shot), #44 (the issue)

- **Status:** Proposed — design-first pass (2026-07-07); staged implementation begun.
  - **Stage 1 DONE (`d84aeae`)** — `Handler.custom` rep + the ADDITIVE ripple; census 25→26, trusted-three axiom-clean, frozen statements untouched (the additive-ripple bet CONFIRMED while custom is inert+untyped).
  - **Stage 2 — SEMANTICS + typed-soundness proven-IN-ISOLATION, but the full census gate is BLOCKED (a real finding, gh44s2; WIP on branch `origin/gh44s2`).** The dispatch+one-shot-resume semantics work (kernel `#guard`s: custom `read 5`⤳clause `5+100`⤳continuation `+1` = **106**; zero-shot abort via a coexisting `throws` = **42**), and the TYPED trusted-three stay VACUOUS-CLEAN (new lemma `HasStack.concat_custom_absurd` — a custom frame can't sit on a typed stack). **BUT making dispatch real regresses the UNTYPED route-A CalcVM metatheory** that the CLEAN headlines `run_evalD`/`sim`/`compile_correct` carry: `CapLabelCoh`/`FreshCfg` are stated over ANY config and must BOUND a config's caps via `capsH : Handler → List (Nat × Label)` — but the coexist rep's clause map is an **opaque `OpId → Option Comp`**, whose caps CANNOT be collected into a finite `List` (the domain isn't enumerable). So `capsH` can't bound clause caps → a `sorry` there would taint the currently-clean CalcVM headlines. **The fix = a `custom-clauses-are-VcapFree` well-formedness invariant threaded through `CapLabelCoh`+`FreshCfg`+the route-A/B AbstractMachine proofs** (it IS preserved — `substFrom` identity on custom + a VcapFree seed ⟹ `capsC clause = []` closes the residuals — plus `.map` traversal for `renameH`/`substFrom`/`shiftFrom` + a no-custom-in-machine lemma). **This is multi-file, gated, and ENTANGLED WITH THE PENDING route-B (ADR-0052)** — i.e. the "riskiest single obligation" this ADR named for Stage 4 surfaces ALREADY at Stage 2. **CONSEQUENCE: the running-user-effect milestone (Stages 1–3) is GATED on the route-A/route-B metatheory (≈ Stage 4), not a quick 1→2→3.** `read`-side (read-only param) works; `put`-like mutation needs the Stage-4 denotational machine / first-class `k`.
- **Date:** 2026-07-07
- **Layer:** K (kernel — the `Handler` primitive + its metatheory). **Tag: K-ADR** (semantic; frozen-statement-adjacent but NON-changing — see §Soundness).
- **Builds on:** ADR-0022 (the `up`/`perform` rule + EffSig op-interface — already general), ADR-0023 (the CK machine + deep dispatch), ADR-0025 (resumptive state: keep Kᵢ, reinstall the frame, the closed-focus grade discipline — the mechanism the one-shot custom clause GENERALIZES), ADR-0030/0031 (STM as a transactional handler + its calc-machine store — the second resumptive instance), ADR-0052 (route-B: the calc-machine identity-keyed re-derivation this entangles with), ADR-0054/0055 (identity dispatch + global-fresh — preserved unchanged), ADR-0063 (`escapedCap` — the custom escape terminal, unchanged), ADR-0070/0072 (named-cap surface — the `handle … with` lowering starting point).
- **Reference:** Plotkin–Pretnar / Bauer–Pretnar (algebraic effects + handlers — op-clause maps + reified continuation); Hillerström–Lindley (deep handlers). Both in `references/papers/effects-handlers/`.

## Context

The northstar — "a language whose paradigm and runtime are VALUES, not language features"
(`CLAUDE.md`) — LITERALLY means user-defined effects: a user declaring their own effect and
writing a handler for it. #44 names this "the moat." ADR-0084 (networking) gated its genuine
`{Net}` effect on #44 and verified from code that #44 is a hard KERNEL prerequisite.

**The gating fact (verified from `Bang/Core/IR.lean` + `Bang/Core/Semantics/Dispatch.lean`):**
the kernel `Handler` is a CLOSED set of three (`state ℓ v` / `throws ℓ` / `transaction ℓ Θ`);
their operations are HARDCODED strings in `handlesOp`/`dispatchOn` (`get`/`put`, `raise`,
`newTVar`/`readTVar`/`writeTVar`). Named capabilities (ADR-0070/0072) let a user NAME an
*instance* of the three built-ins; they do NOT let a user declare a fourth effect kind.

**What is ALREADY general (the half-done insight):** the *performer* side. `Comp.perform c op v`
carries no hardcoded op or label (`IR.lean:123`); `HasCTy.perform` (`Typing.lean:207`) types any
op via the `EffSig.opArg/opRes` typeclass — which is *precisely* "the interface a program's
`effect` declarations present to the type system" (`IR.lean:327`). So a user can already NAME
and TYPE operations of a new label; what is missing is a HANDLER that can SERVICE them. #44 is
the handler-side generalization, not a from-scratch effect system.

## The three built-ins, by resumption shape

```
throws ℓ         ZERO-SHOT.  discard the captured continuation Kᵢ, abort to Kₒ with the payload.
state ℓ s        ONE-SHOT.   keep Kᵢ, reinstall handleF (state ℓ s'), resume Kᵢ with a value;
                             threads one closed Val s.
transaction ℓ Θ  ONE-SHOT.   as state, threading a list-heap; abort discards the write-delta.
```

A general algebraic-effect handler is a **label + a per-op clause map**, each clause a
computation over the operation's argument + a carried parameter, deciding resumption. The three
built-ins are semantic instances (throws = an abort clause; state/txn = one-shot resume clauses
carrying a Val/Store parameter).

## Decision

### D1 — COEXIST: add `Handler.custom` as a FOURTH constructor (not collapse to instances)

```
| custom : Label → Val → (OpId → Option Comp) → Handler
--          label   carried-param    per-op clause (a Comp binding param@1, arg@0)
```

The three built-ins stay as OPTIMIZED constructors, their dispatch/typing/soundness/calc-machine
arms BYTE-IDENTICAL. `custom` gets NEW dispatch (a clause-map arm in `handlesOp`/`dispatchOn`),
a NEW typing rule (`handleCustom` + a `customF` `HasStack` frame), a NEW calc-machine arm
(DERIVED — D3), and NEW soundness cases. This is the project's stratification principle
(ADR-0026/0028): the verified core (the three, axiom-clean) + a being-verified superset
(`custom`) separated by an explicit, type-visible seam (the constructor).

### D2 — v1 is ONE-SHOT (the load-bearing scope pin)

A genuinely general handler with an explicit, multiply-invocable `resume` requires FIRST-CLASS
continuation reification — the labelling→closure cap-rep change (Q22) the kernel has deliberately
AVOIDED (it is pure labelling: `vcap` + `splitAtId` + gensym, no closure value). So v1 restricts
custom clauses to **one-shot tail-resumptive** (a clause returns a value that resumes Kᵢ — the
ADR-0025 state mechanism, with USER logic where get/put's hardcode was) OR **zero-shot abort**
(the throws mechanism). This covers `{Net}` read/write, logging, reader, writer — most effects.
**Multi-shot / 0-or-many / first-class `k`** (nondeterminism, backtracking, schedulers) needs
closure cap-rep + resumption grades — DEFERRED to Q22/Q27. The resumption grade (#17/Q27) is the
type cost that later ADMITS multi-shot; v1 fixes it at one.

### D3 — invariant #4: the calc-machine arm is DERIVED, not hand-patched

The machine (`Bang/Backend/AbstractMachine.lean`) threads two specialized resumption stores
(`SStore` for state, `THeap` for transaction). For `custom`, generalize these to a SINGLE param
store (`identity → carried Val`) — generality HELPS here: one store subsumes two, and state/txn
become param-carrying instances (the natural place for the eventual D5 collapse). The custom
`evalD` clause RUNS the op's clause recursively and threads the updated param; the machine
instruction must FALL OUT of the `evalD` RHS (the `compile_correct` exemplar discipline,
`AbstractMachine.lean:296` "the machine — derived, not designed"). `compile_correct`
(`exec∘compile ≡ evalD`) + `evalD_agrees_source` are re-proven for the custom arm. **This is
sequenced WITH / AFTER route-B (ADR-0052), which is itself still pending** — the machine already
disagrees with the kernel on shadow programs; #44's arm must be derived against the identity-keyed
route-B machine, generally.

### D4 — the surface (frontend leaf)

`effect Net { read : Int -> Str; write : Str -> Unit }` → generates an `EffSig` instance (fresh
`Label`, `opArg/opRes` per op) + reserves the op names (elaboration-only, zero runtime fuel).
`handle e with Net { read(x) => …, write(x) => resume(…) }` → lowers to
`handle (Handler.custom netLabel initParam clauses) body`, building on the ADR-0070/0072 named-cap
machinery (`as h` binder + `h.op` perform + identity dispatch already exist). Census byte-identical.

### D5 — Option-A (instances) is a LATER refactor, not v1

Once (a) the general-handler soundness is proven axiom-clean AND (b) the multi-shot grade
discipline (Q27) is settled, the three built-ins MAY be collapsed into `custom` instances — a
census-preserving simplification toward the minimal end-state (one handler form). Coexist-first is
the correctness-preserving path there; the collapse is not taken on taste while the general
soundness is unproven.

## Soundness — the frozen statements do NOT change; the census risk is quarantined

**No frozen `Spec.lean` statement changes.** `preservation`/`progress`/`type_safety`/
`no_accidental_handling`/`subst_value` are all CONSTRUCTOR-AGNOSTIC — `Handler` is
existentially/universally quantified inside them, never destructured in the STATEMENT. So #44
needs NO frozen-statement change and NO re-freeze clause. The entire ripple (~424 sites, dominated
by `AbstractMachine` 218 / `Soundness` 91 / `BinaryLR` 80) is ADDITIVE proof cases — every
`cases h` gains one `custom` arm; the three existing arms are byte-identical (the coexist payoff).

**Does #44 threaten the trusted-three's clean census? — quarantinable; one-shot v1 stays clean.**
The one-shot custom soundness cases MIRROR the proven-clean state/transaction cases (the user
clause substitutes into the slot the hardcoded get/put logic occupied; the carried-param grade
discipline is the ADR-0025 D2 closed-focus argument reused). Residual risks, honestly named:
(a) MED — the custom clause can ITSELF perform effects (deep-handler recursion at the residual row
φ), which the effect-free hardcoded built-in clauses never did; preservation must track that
residual-effect threading; likely resolved by a clause-effect-row premise (a rule REFINEMENT, not
a frozen-statement change). (b) GAP — multi-shot resumption is a genuine gap needing a grade
restriction or a sorryAx; **scoped OUT of v1** (D2). The **coexist payoff is decisive**: if a
custom case cannot close cleanly it carries a DOCUMENTED sorryAx in the `custom` arm WITHOUT
regressing the three built-ins' clean census — Option A could not offer that isolation. The
LR/calc-machine custom cases ride the EXISTING (already-sorried) state/txn LR frontier
(`Spec.lean:212/243`) and are gated no stricter than the built-ins already achieve.

**Refute-first discipline (per team practice):** if the one-shot custom soundness resists during
implementation, produce a machine-checked `False`-from-`handleCustom` witness before reshaping the
rule — do not weaken it on a say-so; distinguish genuinely-FALSE (needs a premise) from merely-HARD.

## Considered options

- **B — COEXIST (CHOSEN).** Fourth `custom` ctor alongside the three; one-shot v1. Additive ripple,
  quarantined census risk, built-ins stay clean.
- **A — INSTANCES (REJECTED for v1, kept as D5).** One `custom` ctor; state/throws/transaction
  derived from it. Truer to minimality (invariant "minimality over generality") BUT routes the
  currently-axiom-clean trusted-three THROUGH the unproven general-handler soundness — risks
  regressing the working verified core for elegance. Correctness steers: isolate the risk first
  (B), collapse later (D5) once the general soundness is proven.
- **C — a bespoke per-effect kernel constructor (e.g. `| net`).** Already REJECTED by ADR-0084 —
  spends #44's full ~424-site ripple to buy ONE hardcoded effect, violating invariant #5's
  "generalize the handler, don't special-case one more effect." #44 IS the general form C was
  rejected in favor of.

## Invariant compliance

- **#2 (rows-as-sets):** a user effect = a new `Finset` atom label; union/join unchanged.
- **#4 (machine = output of calculation):** HONORED BY OBLIGATION — D3 DERIVES the custom arm; the
  risk is doing it right (entangled with route-B), not a violation.
- **#5 (five primitives):** generalizes the EXISTING handler primitive — a fourth CONSTRUCTOR of
  one of the five, NOT a sixth primitive. (ADR-0084 rejected a bespoke `| net` ctor on exactly this
  ground; `custom` is the general form.)
- **#1 (proof rides the reference):** stages gate against the oracle at each step — a `#guard`
  user-effect run (stage 2), the `Agree` diff-test + `compile_correct` (stage 4), `just axioms`
  (stage 6). No execution path ships without an oracle behind it.

## Staged plan (each a gated unit; full detail in SCOPE.md §7)

```
1 REP           +Handler.custom + total-fn arms            LOW    build + census unchanged
2 DISPATCH/EVAL one-shot custom dispatch                   MED    #guard: a Net demo RUNS on Source.eval
3 TYPING        handleCustom + customF + clause typing     MED    build + a typed user-effect example
4 CALC-MACHINE  generalize stores; DERIVE custom arm ★     HIGH   compile_correct + Agree; WITH route-B
5 LR            custom compat / Krel case                  HIGH   no worse than built-ins' sorry frontier
6 SOUNDNESS     preservation/progress/type_safety +        MED-   just axioms — trusted-three census
                no_accidental_handling custom cases        HIGH
7 SURFACE       effect decl + handle-with + EffSig-gen     LOW    end-to-end `bang eval`
```

Stages 1-3 unblock a RUNNING (if unproven) user-effect demo — the moat made visible — as an early
tracer bullet before the proof grind. Stage 4 sequences with route-B (ADR-0052). Stages 5-6 pair
with `proof-engineer`.

**Overall size:** L / weeks, spine-touching (confirms ADR-0084) — the largest post-MVP direction.
The no-frozen-statement-change + additive-ripple findings make it more tractable than feared (not a
re-freeze), but stage 4 (+route-B entanglement) and the LR frontier keep it multi-session.

**Riskiest single obligation:** stage 4 — the invariant-#4 calc-machine re-derivation (genuine
Bahr–Hutton calculation over garby §6's open handler-compiler frontier, entangled with pending
route-B). Runner-up: multi-shot soundness IF v1 scope creeps past one-shot (mitigation: the D2 pin).

## Revisit if

- Route-B (ADR-0052) lands → stage 4 becomes concretely schedulable against the identity-keyed
  machine; finalize the custom arm's derivation then.
- Q22 (closure cap-rep) / Q27 (resumption grades) resolve → v1's one-shot pin (D2) can lift to
  multi-shot, and D5 (the Option-A collapse) becomes a safe refactor.
- The general-handler soundness is proven axiom-clean AND multi-shot settles → collapse the three
  built-ins into `custom` instances (D5), moving to the minimal end-state.

## Evidence

Verified read of `Bang/Core/IR.lean` (closed `Handler` triple; already-general `EffSig`/`perform`),
`Bang/Core/Typing.lean` (constructor-agnostic frozen theorems; `handleThrows`/`State`/`Transaction`
+ 3 `HasStack` frames; the already-general `perform` rule), `Bang/Core/Semantics/{Eval,Dispatch}.lean`
(hardcoded op dispatch; identity-keyed `idDispatch`/`splitAtId`; the state/throws/txn resume shapes),
`Bang/Backend/AbstractMachine.lean` (SStore/THeap specialized stores; the `evalD`-derives-the-machine
discipline), `Bang/Spec.lean` (the frozen statements — none destructure `Handler`), and the ripple
grep (~424 constructor-match sites). ADR-0052's route-B pending status (inc-6 amendment).
Design thread + full staging: `SCOPE.md` (same scratchpad dir).
