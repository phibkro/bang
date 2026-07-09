# ADR-0092 · #44 Stage 3: typing user-defined effects — program-derived EffSig + the typed custom-handle rule

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: Stage 2 landed custom dispatch census-clean (`6413281`), but custom is still UNTYPED: no `HasCTy` rule mentions it, and the typed trusted-three stay clean only via vacuity (`HasStack.concat_custom_absurd` — a custom frame cannot sit on a typed stack). Stage 3 makes user effects TYPEABLE. The grounding fact that shapes everything: **the kernel metatheory is already parametric in `[EffSig Eff Mult]` and the performer side (`perform`/`up` via `EffSig.opArg/opRes`) is already fully general** (ADR-0085's own finding) — so op typing needs NO new kernel mechanism. **Decision: (D1) user `effect` declarations allocate labels deterministically in the elaborator (`ℓ ≥ 4`, decl order — the four built-ins keep 0–3; the kernel is label-agnostic, `Label = Nat`, zero kernel change); (D2) the elaborator CONSTRUCTS the concrete `EffSig` instance from the program's `effect` decls (finite-map `opArg`/`opRes` over the declared ops) — the typed judgment runs at the program-derived instance, so the parametric soundness theorems apply to user effects BY INSTANTIATION, not by new proof; (D3) one new typed rule, `handle`-custom, mirroring the three built-in handle rules: clauses typed pointwise over the finite list (`body : opRes ! φ` under `param` + `arg` bindings, one-shot tail-resumptive), the B-occ anti-escape premise (`¬ LabelOccurs ℓ A`) carried verbatim; v1 types the READ-ONLY-param form only; (D4) the vacuous custom arms in `preservation`/`progress` become REAL additive arms (the ADR-0085 additive-ripple pattern; frozen statements untouched), probe-first per the ADR-0087 rung discipline — the preservation-of-dispatch slice is the bet.** **Deferred, named: (D5) the param-UPDATE protocol** (`put`-like ops mutating the carried param — ADR-0087 §Open-questions; semantics not yet landed either, deferred with ADR-0085's Stage-4/first-class-`k` note; read-like user effects (Net/read, ADR-0084's motivating case) do not need it). **Rejected**: a universal open `EffSig` instance keyed by runtime maps (loses by-construction totality of op signatures; the program-derived instance is total over declared ops by construction), and typing custom via a NEW judgment separate from `HasCTy` (two judgments for one problem — the coexist seam already quarantines risk at the constructor, not the judgment).
- **Depends-on**: 0085, 0087, 0022 (the general `up`/EffSig performer rule), 0046 (deterministic elaboration), 0054/0055 (identity dispatch — unchanged)
- **Relates-to**: #44 (Stage 3 of the arc), Q39 (effects-as-typed-interfaces — this ADR is its typing half), #56 (single-ρ row-poly — user labels ride the same set machinery and INHERIT the mixing limit; noted, not solved here), Q22/Q27 (multi-shot — out of scope, one-shot v1), ADR-0084 (Net instance — the first consumer)

## Status

Proposed (2026-07-09, the desk-design pattern: drafted while the s4/diag59/ml90 lanes run) —
awaiting operator ruling. Implementation sequencing: D1/D2 are elaborator work
(`TypeCheck.lean` — queue behind the #50 lane); D3/D4 are kernel typing + soundness work
(`Bang/Core/Typing.lean` + `Soundness.lean` — a proof-engineer unit, probe-first). Stage 4
(the s4 lane, in flight) is INDEPENDENT — the machine correspondence is untyped; neither unit
blocks the other.

- **Layer:** K (typing judgment + soundness arms) + F (label allocation, EffSig construction).
  Frozen `Spec.lean` statements untouched — D4 is additive arms under constructor-agnostic
  statements, the same shape Stage 1 proved landable.

## Context

What exists: `perform`/`up` types at ANY label/op through `EffSig.opArg/opRes` (ADR-0022 —
"EffSig already IS the user-effect interface"); rows are label sets over `Label = Nat` (user
labels compose by the same join, no row-machinery change); the three built-in handle rules
carry the B-occ premise (`¬ LabelOccurs ℓ A`, `Typing.lean:50-55`) — the anti-escape device
that keeps a capability from outliving its handler inside the answer type; custom frames are
UNTYPEABLE today (`concat_custom_absurd`, `Soundness.lean:1958`), which is exactly what D3
retires and D4 pays for.

What Stage 3 buys: a user writes (Stage-7 surface, sketched in ADR-0085 D4)
`effect Net { read : Int -> Int }` / `handle e with Net { read(x) => … }` and the program
TYPE-CHECKS with `Net`'s label in the row, the handler discharging it, and the whole thing
riding `preservation`/`progress` — the moat's "paradigm is which effects are in your row"
made real for effects the language authors never named.

## Decision detail

- **D1 — label allocation.** `effect` decls get `ℓ := 4 + declIndex` (deterministic, ADR-0046;
  duplicate effect names = LOUD error). Built-ins keep exn=0/state=1/stm=2/Div=3. Kernel never
  learns names; the elaborator owns the name↔label map (same pattern as `data` ctor tags).
- **D2 — program-derived EffSig.** The elaborator builds `opArg/opRes` as total functions:
  finite lookup over declared `(ℓ, op)` pairs, defaulting to the existing built-in signatures
  below 4. Totality by construction (every declared op has a declared signature; undeclared
  ops at a user label are an ELABORATION error, never a kernel stuck). The metatheory's
  `[EffSig]` parametricity means `preservation`/`progress`/`type_safety` hold at this instance
  with NO new op-side proof.
- **D3 — the typed custom-handle rule.** Shape (mirroring `handleThrows`/`handleState`):
  given `M : A ! φ` under the bound cap, param `p : P`, and for each clause `(op, body)`:
  `body : opRes ℓ op ! φ'` under `param@1 : P, arg@0 : opArg ℓ op` (the landed binder
  discipline), with `φ' ⊆` the handle's residual row; conclusion `handle … : A ! (φ \ ℓ) ⊔ φ'`
  matching the built-ins' row algebra; premise `¬ LabelOccurs ℓ A` verbatim. One-shot
  tail-resumptive only (the landed semantics); read-only param (D5 defers update).
- **D4 — soundness arms.** `concat_custom_absurd`'s two call sites become real cases: typed
  custom frames CAN now sit on stacks, so preservation-of-dispatch (the resume step: clause
  body's type meets the continuation's expectation) and progress (a typed custom handle never
  sticks — `dispatchOn_isSome` from rung-2 is the semantic half) get additive arms. Probe
  rung: the preservation-of-dispatch slice in isolation FIRST; census-gate before the full
  transplant (the exact ADR-0087 D4 discipline).

## Revisit if

- D4's probe finds the one-shot clause typing needs answer-type polymorphism the mono
  elaborator can't express → surface the obligation; candidate fallback is restricting v1
  clause bodies to `φ' = ⊥` (pure clauses), named here so it's a shrink not a scramble.
- Param-update (D5) lands semantically → extend D3 with the pair-return protocol
  (ADR-0087 §Open-questions' candidate) as its own slice.
- #56 gets subeffecting → the D3 row algebra inherits it mechanically (same `⊆` site).

## Evidence

`Bang/Core/IR.lean:360-394` (EffSig parametricity + built-in labels), `Typing.lean:50-55,204+`
(B-occ + the built-in handle rules), `Soundness.lean:1958,2252,2596` (the vacuity this
retires), ADR-0085 §Summary (performer-side-already-general finding + D4 surface sketch),
ADR-0087 §Status (rung-2 verdict + the open param-update question), `6413281` (the landed
Stage-2 semantics D3 types).
