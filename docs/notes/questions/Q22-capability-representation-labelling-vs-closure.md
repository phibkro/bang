---
type: design-question
title: "Capability representation: labelling vs closure (multi-shot fork)"
description: "labelling (name + stack-search) vs closure/evidence-passing cap rep, at multi-shot resumption"
status: open
area: effects
ties: ["Q6", "ADR-0052", "ADR-0054", "ADR-0055"]
see-also: ["Bang/Reify/CalcReify.lean", "#72"]
---
**Question**: When bang extends to **multi-shot / non-tail resumption** (`Bang/Reify/CalcReify.lean`, post-v1),
should a capability stay a generative NAME resolved by stack-search (`vcap n ℓ` + `splitAtId K n` + a
global-fresh gensym — ADR-0054/0055, **labelling**), or switch to a **closure / capability-passing**
representation (the cap captures the handler + delimited context directly, invoked without any search)?

**Why it matters**: The VM-calc spike (2026-06-27, on the `vm-calc-spike` branch) build-proved this is a
REPRESENTATION CHOICE *upstream* of the Bahr–Hutton calculation, not forced by the language: a labelling
`eval` calculates a machine WITH `gensym` + `splitAtId`; a closure `eval` calculates one with NEITHER
(O(1) `perform`, no fresh names). So that machinery is **introduced, not calculated** — invariant #4
degrades locally and precisely here (the spike's recommended honest framing: "calculated except for two
seams" — the cap representation, and the gensym discipline).

**★ CONCRETE MANIFESTATION (2026-06-29, inc-5 route-1) — `lr_sound` (task #72).** The labelling rep surfaces
this seam EARLIER than multi-shot: `lr_sound`'s adequacy needs to bridge `CrelK`'s observation of the RAW
focus `(g, K, c)` to `converges_plug_iff`'s RESHAPED focus `capSubstInto C c` (the labelling rep pushes
`C`'s frame caps INTO the focus; the raw RHS is provably FALSE — a raw `vvar`-cap focus is stuck). No
`CrelK` instantiation bridges them (build-witness `scratch/AdequacySpike.lean` @ `7574a5b`; `crelK_adequacy_nil`
for `C=[]` is CLEAN → it's specifically the arbitrary-context reshape). Two design options, both touching
FROZEN LR defs: (a) re-shape `CrelK` to the reshaped config; (b) plug-congruence (= `crelK_fund_up`'s
deferred direction). Under a **closure** rep this bridge would be a direct re-invoke (no reshape) — so the
seam is rep-specific, exactly as this Q frames it. Tracked: task #72 + `CONTEXT.md` lead.

**Detail** — the tradeoff:
```
                    labelling (name + search)        closure (capture + invoke)
  perform cost      O(stack depth) — a walk          O(1) — direct call
  minting           needs a gensym (fresh names)     none
  cap as a value    tiny, storable, first-class      heavier — captures context
  escape detection  FAIL-LOUD: escaped name → stuck  can be MASKED — closure still runs
                    (= the v1 NonEscape theorem)
  what you verify   NonEscape + freshness            closure-validity on re-invoke
```
v1 picked labelling because escape becomes fail-loud (exactly the `NonEscape` soundness theorem) and caps
stay small/storable — clean for SCOPED/affine caps. But **multi-shot re-invokes a captured continuation
AFTER its handler returned**, natural for a closure (it kept its context) and awkward for "the handler must
still be on the stack." That's where closure gets attractive. This is the literature's **search vs
evidence-passing** split: Xie–Leijen evidence passing (ICFP'21, motivated to eliminate the linear search)
and Brachthäuser–Schuster–Ostermann **Effekt** capability-passing (OOPSLA'20). bang's labelling is the
IDENTITY-keyed refinement of classic op-based search.

**Options**: (1) **keep labelling**, extend to multi-shot by reifying continuations as values while keeping
name-dispatch (the current `CalcReify` direction; cf. Q6 option 3); (2) **switch to closure /
evidence-passing** for the multi-shot fragment — kills gensym + `splitAtId`, O(1) `perform`, natural
multi-shot; cost: heavier caps, escape needs separate machinery, a representation migration; (3) **hybrid**
— labelling for v1 scoped/affine caps, closure for the multi-shot fragment (two reps, an explicit seam).

**Recommended**: none yet — decide WHEN multi-shot is scoped. If going closure, keep the machine
CALCULATED via an effectful identity-`evalD` (Garby–Hutton, *Calculating Compilers Effectively*, Haskell
2024). Keep the spike's `splitAtId_rename` lemma (cap names unobservable → any injective allocator is
correct) as the proof that the gensym discipline is a *provably-free* choice if labelling is kept.

**Blocked on**: nothing now (v1 ships labelling, scoped + fail-loud).

**Revisit signal**: scoping the multi-shot / non-tail resumption extension (`CalcReify` goes live); OR a
perf requirement where O(depth) `perform`-search becomes a bottleneck (evidence-passing's original motivation).
