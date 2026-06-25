# PATH — cap-assignment spike (ADR-0045, de-risk the typed-capability discipline)

> Operator decision 2026-06-25: SPIKE the cap-assignment problem before more impl. The naive uniform
> cap-shift is UNSOUND (ADR-0045 "Correction" section): it fixes case A (migration) but regresses case B
> (open caps — `progB` terminates under dynamic, STUCK under cap-shift). The real fix is a LEXICAL typing
> discipline; this spike de-risks whether it's tractable.

## State (reliable, compiled `lake build` A/B — NOT `lake env lean`, which is garbage for Source.eval)

- `progB = let c = {get} in handle (state 1) ($c)` is well-typed (axiom-clean `CapEscapeWitness.lean` on
  branch `typed-static-b3a`), `done` under DYNAMIC, `STUCK` under CAP-SHIFT → progress/type_safety are
  FALSE for the naive-cap-shift kernel. No dynamic type_safety hole.
- `capMigrate1/2` (case A) are fixed by the shift (`done 5`/`done 9`).
- Branch tip: `typed-static-b3a @ 62e97a7`. The cap-shift impl + WC infra (`39d7c46`/`b6558ee`) stand.

## The crux (root incoherence)
Effect-ROW typing is DYNAMIC (label-based, admits late binding = case B); static cap dispatch is LEXICAL.
A `perform 0` conflates "bind to my enclosing handler" (case A, cap shifts) and "bind to a handler placed
under me" (case B, cap must not shift). Fix: make TYPING lexical (Effekt second-class capabilities):
- **(a)** a `perform` needs an enclosing handler for its effect at its AUTHOR site (a handler-context Σ in
  `HasCTy`; `handle` pushes onto Σ). Reuse the IC's WC infra (`WCComp`/Σ) — but as a TYPING PREMISE.
- **(b)** capability NON-ESCAPE: a handler body can't RETURN a value carrying a capability bound by that
  handler (the escape `handle(state)(ret {get})` = `progB`'s M must be ILL-TYPED).

## The decisive, bounded spike question
**Is there a clean typing premise that makes `progB`'s escape `M = handle(state)(ret {get})` ILL-TYPED
(non-escape) WITHOUT making `capMigrate` (case A) ill-typed — and under which progress holds?**

Minimal fragment (perform/handle/letC/force/ret). Build-gated deliverables (COMPILED `lake build` #guards):
1. The lexical typing predicate (premise (a)+(b)).
2. `capMigrate` (case A): well-typed under it + `done` under cap-shift (compiled #guard).
3. `progB` (case B / the escape M): ILL-TYPED under it (a proof the premise can't be met) — the decisive split.
4. The heart of progress: `lexical-well-typed ⟹ every perform's cap resolves under cap-shift, preserved by
   step` (the property that was FALSE for progB), axiom-clean (no sorryAx).

Outcome is either: TRACTABLE (a clean premise splits A/B + progress holds → proceed to the full typed
re-index, fused B3a+B3b) or RABBIT-HOLE (no clean split / progress needs heavy region typing → feed back to
the operator's "reassess the pivot" option). Both are useful.

## Gating protocol (hard — both the IC and I made measurement errors this session)
- EVERY behavioural claim = a compiled `lake build Bang.<SpikeModule>` #guard. NEVER `lake env lean` #eval
  (it can't reduce Source.eval → garbage; see memory `lean-eval-reliable-only-compiled`).
- The progress/resolve lemma = a real elaborating lemma; `#print axioms` ⊆ trusted-three, no sorryAx.
- Manager gates by `lake build` + `#print axioms` on a clean tree.

## VERDICT (2026-06-25) — TRACTABLE (gated, manager-verified on a clean compiled build)

The spike is on branch **`cap-spike @ 216f136`** (`Bang/CapAssignSpike.lean`, builds isolated-green —
710 jobs). Manager-gated: `lake build` green ⇒ compiled `#guard`s pass (case A `done 5/9`, case B `stuck`);
`#print axioms` `perform_progress` / `progB_ill_typed` / `capMigrate1_LWT` all `[propext, Quot.sound]`,
**no sorryAx**.

**The de-risked mechanism — a two-context lexical judgement `LWT S R`:**
- `S` = AUTHOR context (handlers enclosing M at its def site); `handle h` PUSHES `handleF h` onto S for body.
- `R` = RETURN/escape context; `handle h`'s body gets `R := old S` (a returned value crosses OUT past h).
- `letC M N`: M typed with `R_M := S` (consumed here, not escaped).
- `perform cap ℓ op v` : `CapResolvesKind S cap ℓ op` (author-site resolution).
- `ret v` : `LWVal R v` (NON-ESCAPE — the returned value's caps must resolve where it LANDS).

The S/R split IS the capability-non-escape discipline (Effekt second-class, minimal form). It makes the
escape (`progB`'s `ret {get}` out of `handle(state)`) ill-typed (its `perform 0` must resolve against `[]`
= False), keeps case-A migration well-typed, and `cap>0` resume-into-outer stays accepted (ADR-0045 KEEP) —
the spike's deleted discrimination probe confirmed all three; make these PERMANENT #guards in the re-index.

## NEXT (the full typed re-index — the multi-session bulk, now de-risked)
1. Promote `LWT` to the real typed judgement: thread S/R through `HasCTy` (or fold into `HasConfig` exactly
   as `WellCapped` was), `handle` as the binder.
2. Prove `LWT` PRESERVATION across `Source.step` (incl. `Comp.subst` + the cap-shift) — the bulk the spike
   did NOT do (it proved only the decisive perform case + the A/B split).
3. Re-green the STD block (progress/type_safety) over the cap-shift kernel under `LWT` — now SOUND because
   case B is ill-typed. Then the LR re-index (Vτ/Cτ/Tτ).
4. CONFIRM no v1 rung needs late-bound effects (case B) — the expressivity LWT forbids.
