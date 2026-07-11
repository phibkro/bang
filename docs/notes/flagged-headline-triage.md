<!-- note-status: active -->
# Flagged-headline triage (proof-debt lane, 2026-07-11)

Baseline: main @ `ccec47e9`. Axiom trace from `lake env lean Bang/Audit.lean` on
the clean seeded tree. Four NON-parked flagged headlines (the three `lr_*` are
operator-PARKED, do-not-reopen — not covered here).

| headline | axioms (baseline) | classification | blocker |
|---|---|---|---|
| `seq_unit` | `[propext, sorryAx]` | **(i) tractable-now** | focus-uniform `reshape_focus` lemma; proven machinery only, NO LR spine |
| `zero_usage_erasable` | `[propext, sorryAx]` | **(ii) blocked** | needs `lr_fundamental` (PARKED); grade-0 erasure is a LR corollary |
| `handler_compiles` | `[sorryAx]` | **(iii) do-not-close** | predicates are `True`-stubs; closing = vacuous laundering |
| `effect_sound` | `[sorryAx, Trace, traceWithin, Source.evalTrace]` | **(ii/iii) re-foundation** | `Trace`/`evalTrace`/`traceWithin` are bare `axiom`s, not defs |

## `seq_unit` — RECOMMENDED TARGET (tractable-now)

Statement (`Bang/Spec.lean:294`, frozen): `ctxEquiv (seqComp (ret v) c) c` — the
left-unit law. Proof stub at `Bang/Meta/LR.lean:969` (`seq_unit_proof`).

Purely OPERATIONAL (LR.lean:214 comment) — no LR machinery. Two bridges already
PROVEN axiom-clean and in-tree:
- `converges_plug_iff` (LR.lean:937): `Converges (plug C x)` iff config-convergence of
  the canonical reshaped config `(handlerCount C, canonStack C x, capSubstInto C x)`.
- `seqComp_ret_run` (LR.lean:956): `(g, C, seqComp (ret v) c)` runs to `(g, C, c)`
  in 2 steps (head reduction).

**The residual (the sole gap):** `capSubstInto C x = (reshape 0 [] C x).2.2`. By
`reshape_focus` this is `applyCaps L x` for SOME `L` — but the current lemma gives
`L` *per focus*, so `capSubstInto C (seqComp (ret v) c)` and `capSubstInto C c` get
different `L`s and don't visibly connect. The enabling fact (verified by reading
`reshape`/`reshape_counter`/`reshape_focus`): the accumulated `L` is
**focus-independent** — it is determined by `C`'s frames, the minted ids (counter =
`g + handlerCount C'`, focus-independent per `reshape_counter`), and the labels; the
focus threads only positionally through `fr.wrapStep`. So a strengthened
**focus-uniform** `reshape_focus` — `∃ L, ∀ c, (reshape g K C (frames-of c)).2.2 =
applyCaps L c` — lets `capSubstInto C (seqComp (ret v) c) = seqComp (ret (applyCapsV L v))
(applyCaps (bumpL L) c)` distribute (`applyCaps_letC` already proven), then
`seqComp_ret_run` fires on the substituted focus, and `converges_plug_iff` closes both
`⊑` directions.

Effort: moderate — one new focus-uniform induction lemma (~30-50 lines, mirrors the
existing `reshape_focus`/`reshape_counter` inductions), then the two-direction
`ctxApprox` close. All deps proven; no parked `sorry` touched. Axiom target:
`seq_unit` -> `[propext]` (drop `sorryAx`).

## `zero_usage_erasable` — BLOCKED on parked LR

Statement (`Spec.lean:165`): `HasCTy (0::γ) (A::Γ) c e B → NotEvaluated 0 c`.
`NotEvaluated 0 c` (LR.lean:208) = grade-0 filler substitution-irrelevance up to `≈`.
The body comment (Spec.lean:181) names the blocker explicitly: needs
`lr_fundamental` (PROOF_ORDER #1, PARKED) to instantiate `Crel`/`Vrel` at the grade-0
slot. Both syntactic shortcuts (non-occurrence, subst-independence) are REFUTED by
`ret (vvar 0)` at `q=0`. No path that avoids the parked LR. **Do not target.**

## `handler_compiles` — DO-NOT-CLOSE (vacuous laundering)

Statement (`Spec.lean:333`): `HandlerLawful h → HandlerEquiv (compileHandler h) h`.
`HandlerLawful _ := True` (Wasm.lean:2154), `HandlerEquiv _ _ := True` (Wasm.lean:2159),
`compileHandler _ := {body:=[], result:=.unit}` (Wasm.lean:243) — all honest Milestone-B
`True`-placeholders (comment: "a tracked Milestone B `sorry`, not an axiom"). The
statement is definitionally `True → True`; `fun _ => trivial` would close it and drop
`sorryAx`. **This is vacuous** — it proves nothing about handler compilation because the
predicates carry no content and the emitter emits an empty module. Closing it trades an
honest tracked `sorry` for a green-that-lies (discipline rule 31, no laundering). It
should stay `sorry` until the Milestone-B generator backend defines the real predicates.
NOTE: `compileHandler`/predicates live in `Bang/Backend/Wasm.lean` (not the
lane-forbidden `WasmEmit.lean`), but the correct move is to NOT touch it regardless.

## `effect_sound` — RE-FOUNDATION, not a discharge

Statement (`Spec.lean:191`): `HasCTy [] [] c e (F q A) → evalTrace fuel c = done (v,t)
→ traceWithin t e`. The three symbols `Trace`, `Source.evalTrace`, `traceWithin` are
bare `axiom` declarations (`Bang/Core/Semantics/Eval.lean:403-407`), gated on "need a
concrete `Eff` to express label-in-row" (Q1, OPEN_QUESTIONS). So the axiom set carries
`Trace, traceWithin, Source.evalTrace` in ADDITION to `sorryAx`. Discharging this is
NOT a proof gap — it requires first turning three axioms into real definitions (a
concrete `Trace` type over the fixed `Eff`, an `evalTrace` fuel interpreter that
accumulates performed labels, and `traceWithin` as `t subseteq e`), i.e. a Phase-A
re-foundation blocked on the Q1 concrete-`Eff` decision. Out of a pure-discharge lane's
scope; escalate as its own increment. **Do not target as a discharge.**

## Recommendation

Target **`seq_unit`** (the one (i)-tractable headline). Slice plan:
1. Prove the focus-uniform reshape-focus lemma (`∃ L` shared across foci) — the sole
   new machinery. Build + local axiom-check on the lemma.
2. Wire `seq_unit_proof`: unfold `ctxEquiv`, both `ctxApprox` directions, apply
   `converges_plug_iff` + the distribution + `seqComp_ret_run`. `#print axioms seq_unit`
   ==> `[propext]` (sorryAx dropped), diff `just axioms` vs baseline (20 clean stay clean).

The other three: `zero_usage_erasable` waits on the parked LR; `handler_compiles` must
stay `sorry` (vacuous otherwise); `effect_sound` is a Q1 re-foundation increment.
