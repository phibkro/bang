# PATH-stable-interface-effect-rendering — semantic checked names without runtime relabeling

> Remove declaration-order numerals and missing nested rows from the checked interface view while
> preserving the honest boundary between presentation stability and a separately compiled artifact.

## Seam

- **From checkpoint**: `PATH-module-interface-boundary-probe` exposed a useful public firewall and
  retained `Cap 4 → Cap 5` under an unrelated earlier effect as its first architectural falsifier.
- **To checkpoint**: checked value/interface rendering uses the elaborator's semantic effect names at
  every type depth; lowered code continues to use dense labels and remains whole-program.
- **Contract preserved**: `DeclFact` remains the single checked fact source for query, hover,
  annotation, and module interfaces; no interface-only type renderer or runtime identity scheme is added.

## Layer

- [ ] Kernel  [x] Compiler query  [x] Surface diagnostics  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author compares a dependency's public contract after an unrelated
  module/effect is inserted earlier in the resolver walk.
- **Public starting point**: `bang query dump <file.bang>`.
- **Terminal observation**: the unchanged dependency retains its interface digest and renders
  `Cap Trace` plus `Thunk!{Trace}` rather than a dense numeral or an omitted nested row.
- **Adverse / recovery route**: a genuine `{Trace}` add/drop moves the interface; two modules' local
  `Net` effects render as distinct qualified names across reversed import order; an unexplained checked
  label refuses rendering instead of emitting a plausible partial type.
- **Downstream journey released**: the next artifact tracer can study lowered module body/link identity
  without confusing a checked presentation defect with a runtime representation requirement.

## Feeds the constraint

- **Binding constraint now**: `PATH-module-interface-boundary-probe` demonstrated that an unrelated
  earlier effect moved an unchanged dependency interface, blocking trustworthy module-edge invalidation.
- **How this path feeds it**: remove that checked presentation coupling and retain runtime/global-body
  coupling as the narrower cited constraint for the next artifact tracer.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| dense runtime label leaks into public contract | already realized as `Cap 4 → Cap 5` | high / high / medium | **render through the existing environment now** | a checked type still exposes an ordinal |
| nested effect row silently disappears | existing `.U` renderer omitted `effects` | high / critical / low | **thread one shared renderer and gate sensitivity** | nested row edits preserve an interface |
| same local effect names collapse | ordinary multi-module naming | medium / high / high | **gate qualified separation now** | two owners render one identity |
| multi-effect row order leaks resolver order | rows are sets but effect table is ordered | high / high / low | **sort semantic user names and gate reversed imports** | equal rows render differently |
| presentation fix is mistaken for artifact stability | runtime labels/body remain global | high / critical / high | **retain `separateCompilationReady:false`** | an independently lowerable body and link contract land |
| type-hole numerals still shift | checked generic/hole rendering uses global markers | medium / high / medium | **defer explicitly; do not overclaim all type identities** | a public generic export changes only because hole allocation moved |
| second renderer diverges from query/hover | interface facts already share `DeclFact` | high / high / high | **repair decl-aware SSoT, never post-process interface strings** | any consumer re-renders independently |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: inserting `Noise` before `Lib.Trace` preserved source semantics but
  changed the interface type from `Cap 4` to `Cap 5`; `.U` used `showRow φ` without the effect table,
  so the nested `{Trace}` was absent from both variants.
- **Smallest tracer bullet**: thread `effects` through the shared decl-aware type fold, reverse `.cap`
  labels through `EffectInfo`, and validate all outer/nested labels before public checked rendering.
- **Positive evidence**: compiled CLI comparison preserves the unchanged digest across label shifts;
  import-order swaps preserve both `LibA`/`LibB` digests while rendering `LibA_Net` and `LibB_Net`;
  a cross-module two-effect row is sorted canonically and also preserves its digest.
- **Sensitivity control**: changing `Thunk (Cap Trace -> Int -> Int ! {Trace})` to the pure nested
  function changes the rendered type and module-interface digest.
- **Recovery evidence**: checked rendering returns an error if any outer row, nested row, or capability
  label is absent from the environment's built-in/declared set; interface projection already turns a
  checked fact failure into `moduleInterfaces:null`.
- **Broader convergence gate**: full Lean build, 31 batteries, live proof audit, generated reference,
  documentation facts, provenance falsifiers, and repository fitness.
- **Assumptions / exclusions**: environment names are stable for the gated resolver journeys, not a new
  persistent symbol format. Equivalent import-vs-`use` spellings, global type-hole marker normalization,
  future declaration-level quantity/grade contracts, runtime relabeling/link-time relocation, independent
  bodies, cryptographic digests, stores, schedulers, compile-time wins, and cache hits are not claimed.

## Plan

1. [x] Audit runtime allocation versus checked rendering and obtain strategic scope review.
2. [x] Thread semantic effect names through the shared checked type renderer and fail unexplained labels.
3. [x] Gate reorder invariance, same-name module separation, and nested-row sensitivity end to end.
4. [x] Regenerate governed facts, run full convergence, report evidence to the advisor, and publish.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **165 passed, 0 failed** with Python + jq available.
- Convergence evidence: authoritative Lean builds completed (**1550** verification jobs and **1452**
  battery jobs), all **31/31** batteries passed, live proof facts matched the elaborated audit, and
  repository fitness passed with the stacked branch's immediate predecessor as its explicit virtual
  landing base/stable reference. The strategic advisor's blocking multi-effect row-order objection was
  accepted, fixed, adversarially gated, and closed before publication.
- Retained failed gates / successors: dense lowered labels, global type-hole markers, and the flat
  whole-program `Comp` remain explicit inputs to the lowered module-body/link tracer. If `VT` gains a
  new label-bearing position, replace the validator-plus-renderer parallel walk with one `Except` renderer
  before extending it; no numeral fallback may become publicly reachable.
- Reopen / observe: any declaration-order numeral or omitted nested label in a public checked type;
  keep artifact readiness false until independently lowered code can be validated and linked.

## Owner

- Agent / human: Codex, with persistent read-only Fable 5 strategic advisor in Herdr
