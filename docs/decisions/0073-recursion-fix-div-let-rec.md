# ADR-0073 · Recursion: `let rec` surface + `Div`-row typing; μ-encoding preferred (no new primitive), fix-primitive fallback; TCO deferred

<!-- adr-frontmatter -->

- **Status**: Accepted — MECHANISM CONFIRMED (μ-encoding, no new primitive; re-spike POSITIVE 2026-07-05 after #45)
- **Summary**: Recursion enters as a surface `let rec` construct that the checker recognizes and types with `Div` in the effect row (the stratification seam made real — general recursion is the descent into the fuel-bounded fragment). MECHANISM: prefer a μ-types LIBRARY ENCODING of the fixpoint (no new kernel primitive — invariant #5 holds; the recursion spike #42 confirmed the kernel has the pieces: iso-recursive μ + thunks + arrows), gated on checker completeness (#45) which currently blocks the higher-order payload the encoding needs; a minimal `fix` kernel primitive is the FALLBACK if the encoding proves too fiddly to type/lower. v1 recursion runs under `Source.eval`'s existing fuel (deep recursion → `oom`); TCO is a DEFERRED verified machine optimization (invariant #7), unified with resumption grades (Q27/#17). Resolves Q28.
- **Resolves**: Q28 (the recursion marker)
- **Depends-on**: 0029, 0028, 0065

- **Status:** Accepted for the DIRECTION + the decided sub-parts; the μ-vs-primitive mechanism is
  build-arbitrated (a re-spike after #45 confirms whether the encoding types end-to-end).
- **Date:** 2026-07-05
- **Layer:** C+K (surface construct + the Div-row typing; kernel only if the fix-primitive fallback fires)
- **Builds on:** ADR-0029 (iso-recursive μ — the fixpoint's engine), ADR-0028 (the total/`Div`
  stratification seam — recursion is the descent), ADR-0065 (arithmetic — the δ-rules a recursive
  numeric function uses). Reference: the #42 recursion spike (2026-07-05) + Landin's knot
  (recursion from recursive types).

## Context

BANG is a total, first-order expression language today — no recursion (#42), the single biggest
capability gap (blocks folds, evaluators, tokenizers). The 2026-07-05 spike found: recursive DATA
types work; a μ-encoded FIXPOINT is reachable *in the kernel* (μ + `U` + arrows all exist) but is
blocked at the SURFACE by a checker check-mode gap (#45 — a `Thunk (Rec -> Int)` payload won't type).
So the mechanism is NOT a kernel gap; the design turns on ergonomics + the Div-row + whether to expose
the raw μ-knot or a construct.

## Decision

1. **Surface: `let rec f = <fun> in <body>`** (a recursion MARKER, per Q28). The marker brings `f`
   into scope in its own body (which a plain `let` doesn't). Functions NEED a marker; `data` does
   NOT (ADR-0069 auto-detects self-reference) — so **`rec` is NOT shared with data** (Q28 resolved:
   keep them separate; the unification is at the *row* level, below, not a shared keyword).
2. **Type: a recursive function carries `Div` in its effect row.** The checker recognizes `let rec`
   and adds `Div` (may-not-terminate — the type-visible partiality, the ADR-0028 seam). This is Q28's
   "unify at the effect row": recursion's marker is the *effect* `Div`, not a cosmetic keyword.
   Structural recursion (provably terminating on a `data` argument) staying ⊥-row/total is a LATER
   refinement — v1 marks all `let rec` as `Div`.
3. **Mechanism: μ-encoding PREFERRED (no new primitive), fix-primitive FALLBACK.** `let rec` lowers
   to the kernel fixpoint built from iso-recursive μ + thunks (Landin's knot) — users write `let rec`,
   never the raw μ-knot. This preserves invariant #5 (no 6th primitive; recursion is library-over-
   kernel). PENDING: the encoding needs the higher-order payload #45 unblocks; a re-spike after #45
   must confirm `let rec` types + runs end-to-end. If the encoding proves untypable/too fiddly to
   lower, the fallback is a minimal `fix` computation form in the kernel (a spec change — ADR + ripples
   to the calculated machine + soundness; strictly more than the encoding, hence the fallback).
4. **Runtime: recursion runs under `Source.eval`'s existing fuel.** Deep/non-terminating recursion →
   `oom` (the reference is fuel-bounded; it has no stack-space model). This is the total prover
   interpreting the `Div` fragment — already how the stratification works.
5. **TCO deferred.** Tail-call optimization is a MACHINE concern (the calculated `exec`'s explicit
   stack), not a reference-semantics one (`Source.eval` is step-fuel-bounded — TCO is invisible to
   it). Per invariant #7 (performance second-class): slow-correct recursion first. TCO is a later
   VERIFIED machine optimization (recognize tail position at compile → reuse the frame at exec →
   proven against the reference), and it UNIFIES with resumption grades — tail-CALL (function) and
   tail-RESUMPTION (handler, Q27/#17) are the same "tail position → no frame growth" phenomenon, so
   they should be designed together, not as two features.

## Rejected / not-now

- **`fix` as a kernel primitive by DEFAULT** — a 6th-primitive-ish spec change (ripples to machine +
  LR + soundness) when the spike says the μ-encoding likely suffices. Fallback only.
- **Shared `rec` keyword for data + functions** — conflates the total/`Div` seam (Q28); data needs no
  marker, functions signal generality via the `Div` row.
- **TCO / structural-totality in v1** — perf + totality-refinement are second-class (invariant #7);
  ship recursion-that-ooms first.

## RESOLVED (build-arbitrated) — the re-spike gate: POSITIVE (2026-07-05, after #45, `b42014a`)

The re-spike is **positive**: μ-encoded recursion (Landin's knot — `data Rec = Rec(Thunk (Rec -> Int
-> Int))` + self-application) TYPES and RUNS end-to-end on the kernel's existing μ + `U` + arrows, with
**NO new primitive** — bounded countdown-sum `5+4+3+2+1+0` → 15, unbounded → `oom` (build-gated
`#guard`s in `TypeCheck.lean`). So the mechanism is **FINAL: μ-encoding, invariant #5 preserved**; the
fix-primitive fallback does NOT fire. Prerequisite #45 (checker check-mode completeness — push expected
types into thunks) landed to unblock the higher-order payload.

## IMPLEMENTATION STATUS (2026-07-05)

- **§1 `let rec` surface — LANDED (`0f771c6`).** `let rec f : T = fun x => <body> in <cont>` desugars
  (in `elabS`) to Landin's knot generalized per-function: `Rec = μX. Thunk(X -> T)` via raw
  `tMu`/`tVar` (NOT a `data` decl — `let rec` is expression-level), `f : Thunk T` in scope in its own
  body, called `($f) arg`. Emits only ordinary `Surf` — existing checker + kernel run it (invariant #5
  preserved). Recursion is USER-FACING + natural: factorial 5 → 120, countdown-sum → 15, nested rec fns
  → 16, unbounded → `oom` (CLI + `⑨e` guards). Enabled by extending #41's value-position A-norm to APP
  ARGUMENTS (so `($sum)(n-1)` reads naturally). v1 choices: monomorphic + annotation-required
  (`let rec f : T = …`), bare-`fun` RHS, `f : Thunk T`.
- **§2 `Div`-row typing — LANDED (`0397adc`, #46, Option A).** `let rec`'s call-site result carries
  `Div`: `($sum) 5 : Int ! {Div}` — the type-visible partiality. PLACEMENT: `U {Div}` (canonical —
  effects ride the `U`/judgment, ADR-0019/0020), NOT the codomain (`A -> B ! {Div}`): the codomain call
  was REFUTED against the source (effect annotations are upper bounds not forcing — guard 512; `tyBoth`
  strips `tEff`; would break ④b). `divLabel := 3` is a never-performed/handled pure typing marker,
  ERASED at lowering (`divMark`'s `lowerC` passes through) → runtime BYTE-UNCHANGED. **Option A**
  (Div-marked on the OUTER knot only; inner self-calls typed pure ⊥) — a documented v1 UNDER-
  APPROXIMATION (operationally sound: `Div` has no runtime semantics). Full inner+outer threading
  (**Option B** — needs a row-carrying thunk TYPE) DEFERRED to the `⊥-row ⟹ terminates` soundness work,
  where the representation should be driven by the proof. The `letRecRow` seam (v1 `{divLabel}`,
  computed) is the single point **#47** (termination checker) flips to ⊥ for provably-terminating
  recursion → the total fragment.

Earlier note (the #41 gap, now CLOSED by `8e2e132`): μ-recursion needed the `if` condition
A-normalized by hand; #41 fixed value-position A-normalization so it reads naturally.

## Revisit if

- The re-spike refutes the μ-encoding → the fix-primitive fallback becomes the mechanism (new ADR).
- TCO is taken up → design it WITH resumption grades (Q27/#17), and revisit the `Div` fragment's
  space semantics.
- Structural-recursion totality checking is added → some `let rec` stays ⊥-row (the total refinement).
