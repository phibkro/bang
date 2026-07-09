# ADR-0087 · #44 Stage 2′: finite clause representation — enumerability by construction dissolves the `capsH` wall

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: The #44 arc is blocked at ADR-0085's Stage-2 finding: making `Handler.custom` dispatch real regresses the clean CalcVM coherence headlines because `capsH : Handler → List (Nat × Label)` must BOUND a config's capabilities, and the coexist rep's clause map is an opaque `OpId → Option Comp` whose caps cannot be collected (the domain is not enumerable; `capsH (.custom …) = []` is currently sound ONLY by Stage-1 inertness). ADR-0085 sketched the fix as a THREADED well-formedness invariant ("custom clauses are VcapFree") through `CapLabelCoh`/`FreshCfg`/the machine proofs. **This ADR proposes the stronger move: change the representation — `Handler.custom : Label → Val → List (OpId × Comp) → Handler` (a finite association list) — making cap-enumeration STRUCTURAL.** `capsH`'s custom arm becomes `clauses.flatMap (capsC ∘ ·.2)` — total, honest, compositional — so `CapLabelCoh`/`FreshCfg` **statements do not change and gain no premise**: clause caps are bounded by the SAME machinery as every other cap, and the clean headlines stay clean by construction rather than by a side condition. The finite rep also matches the surface (an `effect` declaration and a `handle … with { … }` block are syntactically finite clause lists), makes `handlesOp` a decidable lookup, gives `renameH`/`substFrom`/`shiftFrom` an ordinary `.map` traversal, and eases Stage-3 typing (pointwise over the list). Cost: rebase the banked Stage-2 semantics (`origin/gh44s2`, one ~180-line WIP commit) from function-application dispatch to list lookup, and give up infinite op families — which `EffSig`-declared effects never produce (an `effect` decl is finite by construction). **Rejected**: (a) the threaded VcapFree-clause invariant (detection where construction is available: every machine theorem gains a premise + a preservation-lemma surface, violating the make-illegal-states-unrepresentable principle); (b) a subtype/bundled rep `{cl // ∀ op c, cl op = some c → VcapFree c}` (carries dependent proof obligations through every construction site for less than the list buys). Probe-first before the arc commits (falsifiable rungs below).
- **Depends-on**: 0085, 0086, 0055, 0063
- **Relates-to**: 0084 (the Net instance this unblocks), Q22/Q27 (multi-shot — unaffected by the rep choice), #44

## Status

Proposed (2026-07-09) — the **entry gate for the #44 resume arc**; operator review before the arc opens. Supersedes ADR-0085's Stage-2 invariant SKETCH (its staged plan otherwise stands; see §Staging).

- **Layer:** K (kernel — the `Handler.custom` constructor's argument type). Stage-1's rep is landed but INERT and UNTYPED (no well-typed program contains it; `capsH`/dispatch arms are vacuous or `[]`), so this is a **pre-activation rep change, not a re-freeze**: no frozen statement mentions the clause map's type, and the ~424-site coexist ripple re-touches only the custom arms (byte-identical built-ins stay byte-identical).

## Context

**The wall (ADR-0085 Stage-2 finding, build-confirmed on `origin/gh44s2`):** the Stage-2 semantics
work — dispatch + one-shot resume, kernel `#guard`s green (custom `read 5` ⤳ clause `5+100` ⤳
continuation = 106; zero-shot abort = 42), typed trusted-three vacuous-clean via
`HasStack.concat_custom_absurd` — cannot LAND because the route-A/B coherence layer that the clean
headlines `run_evalD`/`sim`/`compile_correct` ride requires `capsH` to bound every capability a
config can reach. With clauses as `OpId → Option Comp`:

- `capsH (.custom ℓ p cl)` cannot enumerate `cl`'s caps (infinite domain, opaque codomain);
- the current `[]` arm (`Bang/Core/Freshness.lean:73`) is sound ONLY because Stage-1 custom is
  inert — real dispatch makes a clause's body reachable, so a `vcap` smuggled in a clause would be
  a capability the coherence invariant never saw: `CapLabelCoh` preservation breaks at exactly the
  dispatch step, and a `sorry` there taints the clean census.

**What changed since ADR-0085 was written:** ADR-0086 landed the `CustomFree` family
(`CFComp`/`CFVal`/`CFHandler` + store/heap variants) and the completeness spine — machinery Stage 4
inherits — and settled the premise-lifecycle pattern (scaffolding premises with named expiry). The
kernel's handle/pop arms were confirmed handler-agnostic; the machine treats custom as an inert
catch-all everywhere. The question this ADR answers is *how the coherence layer generalizes* when
custom stops being inert.

## Decision

### D1 — finite clause representation

```
| custom : Label → Val → List (OpId × Comp) → Handler
```

First-match-wins lookup (or require distinct `OpId`s at construction — the elaborator emits
distinct ops from an `effect` decl by construction; duplicate = LOUD error per ADR-0046). The
clause `Comp` keeps the Stage-1 binder discipline (param@1, arg@0; one-shot v1 per ADR-0085 D2).

### D2 — the coherence layer generalizes with NO new premise

- `capsH (.custom ℓ p cls) = capsV p ++ cls.flatMap (fun c => capsC c.2)` — total and honest.
- `CapLabelCoh`/`FreshCfg`/`WeakCoh` statements are **unchanged**: a clause cap is bounded, shifted,
  renamed, and coherence-tracked by the SAME per-step machinery as state's carried value or
  transaction's heap (the `state`/`transaction` arms of `capsH` are the exemplars — this makes
  custom's arm their sibling instead of a special case).
- `renameH`/`substFrom`/`shiftFrom` gain ordinary `.map` traversals over the list — the
  preservation lemmas are the mechanical siblings of the transaction (`List Val`) arms.

### D3 — rebase the banked Stage 2 (`origin/gh44s2`) onto the rep

Dispatch becomes `cls.lookup op` (or `find?`); the one-shot resume mechanism, the `#guard`
witnesses (106/42), and `HasStack.concat_custom_absurd` carry over shape-unchanged. The rebased
Stage 2 lands ON MAIN (the census gate that blocked `gh44s2` is dissolved by D2).

### D4 — falsifiable probe before the arc commits (survey-wide-then-commit)

1. **Rung 1 (scratch, ~hours):** re-rep in a scratch probe; re-run the Stage-2 `#guards`; prove the
   `capsH`-extension preservation slice (`capLabelCoh_step` custom arms) in isolation.
2. **Rung 2:** rebase `gh44s2` fully; gate the census (26→26 ctors, every clean headline still
   ⊆ trusted-three) — the Stage-2 landing this time MUST pass the gate that stopped it before.
3. **Fallback (named, not hidden):** if the finite rep hits an unforeseen wall, ADR-0085's threaded
   VcapFree-clause invariant remains available — it is strictly weaker (adds premises) but known-
   shaped. State the wall precisely before falling back.

## Considered options

- **Finite association list — CHOSEN.** Enumerability by construction; no premise creep; matches
  the surface's syntactic shape and `EffSig`'s finite op sets; decidable `handlesOp`; mechanical
  traversals. Loses infinite op families, which no `effect` declaration can express anyway.
- **Threaded VcapFree-clause invariant (ADR-0085's sketch) — REJECTED as primary.** Detection where
  construction is available: every machine/coherence theorem gains a `WfHandler` premise, plus a
  preservation-lemma surface (subst/rename/step keep clauses VcapFree), plus the invariant must be
  seeded and re-established at every handler construction site. Kept as the named fallback (D4).
- **Subtype rep `{cl : OpId → Option Comp // ∀ op c, cl op = some c → VcapFree c}` — REJECTED.**
  Carries dependent proof obligations through every construction and match site; still doesn't give
  enumerability (capsH still can't LIST the caps — it only knows there are none), so it buys less
  than the list while costing more. Also over-restricts: clauses may legitimately carry caps under
  the finite rep (the coherence machinery handles them); VcapFree-ness of clauses is a property of
  ELABORATED programs, not a kernel requirement.

## Open questions the arc must settle (flagged, not decided here)

- **Param update protocol (the `put`-like gap):** Stage 2's clause returns a resumption value; a
  `put`-like op must also UPDATE the carried param. Candidate: the clause returns a pair
  (resumption value × new param), mirroring how `state`'s hardcoded `put` threads `s'` — decide in
  the arc's Stage-2′ design step against the Net/write instance (ADR-0084). The rep choice here is
  orthogonal and forecloses nothing.
- **Stage-4 param store:** ADR-0085 D3's single generalized store stands; the ADR-0086
  `CFStore`/`CFHeap` machinery is the inherited scaffolding, retired when the derived custom arm
  lands and the `CustomFree` premise is dropped (ADR-0086's named expiry).

## Invariant compliance

- **#5 (five primitives):** unchanged — same fourth constructor, different argument type.
- **#4 (machine = output of calculation):** strengthened — Stage 4 derives the custom arm against a
  rep whose caps the calculation can SEE; no hand-waved side condition enters the derivation.
- **#2 (rows as sets):** untouched.
- **Make illegal states unrepresentable (house root principle):** this IS the decision — the
  cap-smuggling clause the threaded invariant would DETECT becomes a state the coherence machinery
  simply HANDLES, because it can finally enumerate it.

## Revisit if

- Rung-1 probe fails (a preservation slice that won't close) → execute the named fallback with the
  wall documented.
- Multi-shot (Q22/Q27) arrives → the clause list rep is orthogonal to resumption arity; no rework
  expected, verify then.
- A genuine need for op-family handlers (infinite ops) materializes → would force back toward a
  function rep + the threaded invariant; no current or planned surface feature produces one.

## Evidence

`Bang/Core/IR.lean:150-160` (Stage-1 rep + inertness comments), `Bang/Core/Freshness.lean:67-73`
(`capsH` with the inertness-justified `[]` custom arm), `origin/gh44s2` @ `946c342` (the banked
Stage-2 semantics + the blocked-landing finding), ADR-0085 §Status Stage-2 (the wall's original
statement), ADR-0086 (the `CustomFree` machinery + premise-lifecycle pattern this arc inherits).
Surface shape: `docs/decisions/0085` D4 (`handle e with Net { read(x) => …, … }` — a finite clause
list in the syntax).
