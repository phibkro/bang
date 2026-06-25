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
