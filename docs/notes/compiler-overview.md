# bang-lang compiler overview — how it works (for the Lexa comparison)

> A comprehensive, citation-grounded map of how bang-lang compiles effect handlers, written to
> be put side-by-side with a lexical-effect-handler paper (Lexa). Tagged **[PROVEN]** /
> **[IN-FLIGHT]** / **[DEFERRED]** / **[PLANNED]** throughout, because the comparison hinges on
> what is *established* vs *designed*. Code is the source of truth; this links to ADRs/files, never
> restates them. Companion: `docs/architecture/core-overview.md` (the module/coupling map).

## 0. The one-paragraph version

bang-lang is a **lexical effect-handler language** whose compiler is **calculated, not hand-written**,
and **verified against a reference** rather than tested. A program is graded-CBPV source; its meaning is
a denotational `Source.eval`; a CalcVM is *derived* from `eval` by Bahr–Hutton equational calculation; and
a WasmFX backend is the optimized output, proven correct by an **annotated forward simulation**
(`compile_forward_sim`, ADR-0035). (A separate biorthogonal/Benton–Hur logical relation proves ◊4
*contextual equivalence* — not the compilation hop.) Handler dispatch is **lexical** — a `perform` carries a first-class **capability value**
that names *one specific* handler by generative identity, not "the nearest dynamically-enclosing one."
Right now the **source semantics + type safety** are the front being established (inc-1–5); the actual
CalcVM→WasmFX compilation is largely **the next phase** (inc-6). So: same *dispatch model* as Lexa, a
*different verification method* than Lexa, and a compiler that's mid-construction.

## 1. The pipeline — two-hop verified compilation  [ADR-0016, PROVEN architecture]

```
  Source AST
     │  graded-CBPV reference semantics
     ▼
  Source.eval            ← THE SPECIFICATION (denotational, fuel-bounded)        [PROVEN]
     │  Bahr–Hutton calculation:  exec ∘ compile ≡ eval
     ▼
  CalcVM                 ← THE EXECUTABLE INTERPRETER (canonical operational meaning)  [IN-FLIGHT, red]
     │  annotated forward simulation (ADR-0035):  compile_forward_sim
     ▼
  WasmFX module          ← THE OPTIMIZED COMPILER OUTPUT                          [PLANNED]
     │  wasm3 / wasmfx-runtime
     ▼
  Observed values
```

This is the **CakeML-style verified-compilation model**, with the front half replaced by
**Bahr–Hutton calculation** rather than a hand-designed IR (ADR-0016). Two distinct proof methodologies
ride the two hops — *calculation* for source→CalcVM, *annotated simulation* for CalcVM→WasmFX (ADR-0035) —
so neither is overloaded. Both are checked against `exec` (invariant #1: "proof rides the reference").

**The deliberate stance:** the machine is an **output of the calculation**, never hand-designed then
justified after the fact (CLAUDE.md invariant #4). The CalcVM is *runnable today* — users run the spec,
not an approximation (ADR-0016 §"Why this model").

## 2. Source language + the kernel  [PROVEN]

- **Substrate:** graded CBPV (call-by-push-value, Torczon et al. OOPSLA'24). Values vs computations are
  syntactically separated; `thunk`/`force` mediate. "Graded" = multiplicities track resource use
  (ADR-0025); the store discipline rides the grades.
- **Five primitives, and only five** (CLAUDE.md invariant #5): `thunk · force · effect-rows · handlers ·
  STM`. Everything else (mutability, IO, async, actors, signals) is *library code over the kernel*. A
  sixth primitive is a spec change requiring an ADR.
- **Effect rows are SETS** — `Finset Label`, a semilattice; union = join, idempotent, unordered
  (ADR-0001/0018). A function's *paradigm* is which effects are in its row.
- **Handlers** are values; three kernel forms: `handleThrows` (abort), `handleState` (a `state` cell of
  general type `S`), `handleTransaction` (STM, the cells int-pinned in v1, ADR-0030). `handle` binds a
  **capability** `Cap ℓ` at de Bruijn 0 — this is the lexical capability-passing (see §3).
- **Typing:** `HasVTy` (values) / `HasCTy` (computations), in `Bang/Syntax.lean`. A `handle` rule's
  subsumption premise `e ≤ labelEff ℓ ⊔ φ` admits a handler over a body that *doesn't* use ℓ (return-only
  handlers are a deliberate, tested feature — ADR-0052 §C-new).
- **STM is the one privileged primitive** — but in v1 it ships *as a transactional handler*, not a
  privileged shared heap (ADR-0030); the privileged concurrent form returns post-v1.

## 3. Handler dispatch — the LEXICAL choice (the heart of the Lexa comparison)

### 3a. bang's dispatch is LEXICAL  [ADR-0052, PROVEN by a build-checked divergence]

The single most Lexa-relevant fact. On a **well-typed same-label-shadowing** program:

```
  handle (state 1 → 10) ( handle (state 1 → 20) ( perform cap=1 "get" ) )
        outer handler         inner handler          which one answers?

  kernel (cap dispatch):  10   ← cap=1 names the OUTER handler it was bound at   (LEXICAL)
  evalD  (dynamic):       20   ← nearest enclosing label-1 handler               (DYNAMIC)
        both `rfl` — a genuine, build-proven semantic divergence
```

The witness is well-*typed*, not merely well-formed (same-label nesting types because the subsumption
premise admits it). **DECISION (ADR-0052): bang's dispatch is LEXICAL** — the kernel's capability dispatch
is canonical; the dynamic `evalD` is the stale half left over from before the typed-static pivot. The
capability names *one specific* handler, the one it was lexically bound at, regardless of what's
dynamically nearest when the `perform` fires.

### 3b. How a capability resolves: identity, not search  [ADR-0054/0055, PROVEN]

- A capability is an **ordinary value** `vcap n ℓ` — a generative **identity** `n` (minted fresh) plus its
  label `ℓ`. No 6th primitive (a capability is just data; `handler` is already primitive).
- `perform (vcap n ℓ) op v` dispatches by **identity match**: `splitAtId K n` walks the stack for the
  handler frame whose minted id is exactly `n` (`Bang/Operational.lean`). Found → resolve; **not found →
  stuck** (fail-loud). Not a label search — an identity match.
- Identity is **global-fresh** (a monotonic Config counter, ADR-0055): no two handler instances ever share
  an id, so an escaped capability resolves to *its* handler or to *nothing* — collisions are
  unrepresentable by construction.

### 3c. The dispatch evolution — bang walked *toward* the lexical model

| ADR | move | dispatch |
|---|---|---|
| 0023/0024 | CK machine, deep handlers | **dynamic** — outward nearest-label `splitAt` search |
| 0044 | dynamic-vs-lexical weighed | v1 *stays* dynamic; lexical/named (Koka/**Lexa tunneling**) recorded as future |
| 0045 | typed-static pivot | **static/capability** dispatch — dissolves the resume-through-a-wrap edge |
| 0046/0050 | de-Bruijn caps | shift wall: crossing `handle` shifts the cap → LR cancellation refuted |
| 0053 | absolute caps | dissolve the shift wall — then **build-refuted UNSOUND** (mis-dispatch on escape) |
| 0054 | **generative identity** | the cap is a *value* travelling with the thunk; **grounded in Lexa/Effekt/Koka** |
| 0052 | dispatch IS lexical | re-derive `evalD` cap-keyed (route B) to match the lexical kernel |
| 0055 | global-fresh id | monotonic counter — escape resolves to its handler or to nothing |
| 0056/0057 | the escape gap + **B-occ** | answer-type label-freedom: a handled label can't ride out in the result type |

The trajectory — dynamic → static → identity → global-fresh — is the *same convergence* the lexical-handler
literature made, but bang arrived at it from the **verification** side (each step was forced by what made
the logical relation tractable / sound), where Lexa arrived from the **efficiency** side.

## 4. Dynamic semantics — the CK machine  [PROVEN]

`Source.step` / `Source.eval` (`Bang/Operational.lean`): a CK machine over `Config = Nat × EvalCtx × Comp`
(the `Nat` is the global-fresh id counter, ADR-0055). Frames: `letF`/`appF` (eval contexts), `handleF n h`
(an installed handler, carrying its minted id `n`). Key steps: `handle` install (mint id, push `handleF`,
increment counter, substitute the bound `vcap` into the body); handler **pop** (`⟨handleF h::K, ret v⟩ ↦
⟨K, ret v⟩` — frame *and stored state discarded*, only the return value crosses outward — this is why the
*answer type* is the sole escape channel, ADR-0057); **dispatch** (`perform (vcap n ℓ)` → `splitAtId K n`).
`eval` is **fuel-bounded** — a total prover interpreting a Turing-complete object language (the Div
fragment of the stratification; CLAUDE.md "stratification principle").

## 5. The compilation hops — CalcVM → WasmFX

### 5a. CalcVM — the calculated machine  [IN-FLIGHT, currently red]

The `(compile, Code, exec)` triple is **derived from `eval`** by Bahr–Hutton equational reasoning (so
`exec ∘ compile ≡ eval` holds by construction, not by a separate proof). It exists as real code
(`Bang/CalcVM.lean` ~4320 LOC, `Bang/Compile.lean` ~3310 LOC) but is **deferred RED**: **route-B**
(ADR-0052) re-derives `evalD`/`unwindFind`/`compile`/`exec` **cap-keyed** to match the lexical kernel —
because the inherited `evalD` was the *dynamic* half that ADR-0052 build-proved disagrees with the kernel.
Route-B is **inc-6**. (`docs/architecture/core-overview.md` §2 has the module graph; the green subset today
is Core·Syntax·Operational·Metatheory·LR·Compat.)

### 5b. WasmFX — the verified compiler output  [PLANNED]

WasmFX (WebAssembly stack-switching: typed continuations, `cont.new`/`resume`/`suspend`) is the primary
target; `wasm3` is the test/bootstrap runtime. CalcReify's resume-frames are *structurally adjacent* to
WasmFX typed continuations (ADR-0016 §"Why this model" #3) — the compiler is closer to syntactic than
semantic. The proof obligation is `compile_forward_sim` (the CalcVM↔WasmFX hop). NOTE: the WasmFX proposal
has drifted to Phase-3 syntax (`switch`/`resume_throw_ref`; `(on $tag $label)`) — a *concrete-syntax*
reconciliation (OPEN_QUESTIONS Q9), not an architecture change.

## 6. Verification structure  [the core of the project]

```
  level         verified core                tested superset            seam
  ─────────────────────────────────────────────────────────────────────────────────────
  correctness   verified (proof)             tested · unsafe            the ADR-0026 ladder
  language      total fragment (⊥-row)       Div fragment (fuel-bounded) THE EFFECT ROW
  tooling       Lean kernel·CalcVM·LR        surface · runtime          typed AST + diff-test
```

- **The oracle** (invariant #1): every execution path is `exec` itself or differential-tested against it.
- **Step-indexed logical relation** (Biernacki et al. POPL'18) — `Bang/LR.lean` + `Bang/Compat.lean`:
  `Crel`/`CrelK`/`KrelS`/`VrelK`. `lr_sound`/`lr_fundamental` = **contextual equivalence**, what
  `compile_forward_sim` consumes. **[IN-FLIGHT]** This is the inc-5 re-key; its decomposition + KrelS layer
  are GREEN (`splitAtId` decomp banked), but the binary-LR `crelK_fund` ret case **walls** on a density
  obligation (`Canonical` for arbitrary KrelS stacks) that is neither derivable nor removable —
  **route 1 (a frozen `Crel` change) or route 2 (a hard reachability lemma), DEFERRED to inc-6** (task #33).
- **The diagonal** — the `Model` module (on the inc-5 branch): `HasConfigTy ⊥ ∧ VcapFree → NonEscape → type_safety`. This is the
  **soundness payoff** ("well-typed source can't get stuck"), and it is *separate* from the binary LR.
  **[IN-FLIGHT, one sorry from done]**: `handlesOp_of_hasConfigTy` is closed axiom-clean; the last sorry is
  `wsCfg_step` (the WellScoped invariant reshape — see §7).
- **B-occ** (ADR-0056/0057) — the **non-escape discipline**: a handled label `ℓ` must not occur in the
  handler's *answer type* (`¬LabelOccurs ℓ A`). This makes the cap-escape bug (`progB`, ADR-0056) untypeable
  by construction. **[PROVEN, phase 1 axiom-clean]**: the kernel premise + `LabelOccurs` + regression lemmas
  landed; it's the typing-side answer to capability escape.

## 7. Current state — honest

| area | status |
|---|---|
| inc-1–4 metatheory (`preservation`/`progress`/`type_safety` over identity dispatch) | **[PROVEN]** axiom-clean |
| B-occ phase 1 (the non-escape kernel premise, ADR-0057) | **[PROVEN]** axiom-clean |
| inc-5 LR Units 1+2 (the `splitAtId` decomp + KrelS layer) | **[PROVEN]** green |
| the diagonal / `type_safety` sorryAx-clean | **[IN-FLIGHT]** ONE sorry left: `wsCfg_step` |
| binary LR (`lr_sound`, contextual equivalence) | **[DEFERRED]** Canonical wall, task #33, inc-6 |
| CalcVM/Compile route-B (cap-key the backend) | **[DEFERRED]** inc-6 |
| WasmFX backend + `compile_forward_sim` | **[PLANNED]** |
| surface elaborator (NamedCore) | **[PLANNED]** inc-7 |

**`wsCfg_step`, the last soundness sorry, IS a lexical-handler question** (this is where §8 bites): the
current `WellScoped` invariant collects capabilities *syntactically through thunks*, so it is **not preserved
when a handler pops** — a capability captured in a thunk that escapes its handler is syntactically present
yet no longer resolvable on the current stack (the "carry-drop"). The fix is to reshape `WellScoped` to a
**performability** notion: a *dormant* captured capability is inert (B-occ proves it can't be *performed*),
and **re-resolves dynamically in the then-current stack when the thunk is forced.** A captured handler
reference resolving where it's *forced*, not where it was *captured* — that is the lexical escape semantics.

## 8. The Lexa comparison axes (where to put the paper side-by-side)

| axis | bang | Lexa (per our ADRs — confirm against the paper) |
|---|---|---|
| **dispatch model** | LEXICAL — capability names one specific handler by identity (ADR-0052/0054) | lexical handlers / tunneling (ADR-0044 cites it) — **likely CONVERGENT** |
| **capability rep** | a first-class value `vcap n ℓ`, global-fresh identity (ADR-0055) | lexical handler reference — confirm: first-class? evidence-passed? |
| **compiler-correctness METHOD** | step-indexed **logical relation** (Biernacki) — `lr_sound` | **Leroy forward-simulation, NO LR** (ADR-0054 records this as the alternative) |
| **escape / capture semantics** | the `wsCfg_step` reshape: dormant caps re-resolve on force; B-occ forbids *performable* escape in the answer type | tunneling (ADR-0044) — Lexa's worked answer to handler escape |
| **stance** | verification-first; the VM is *calculated*, optimization must preserve contextual equivalence | efficiency-first; an optimized lexical-handler compiler |

**The sharp question the comparison should chase:** our binary-LR **Canonical wall** (task #33) is a
difficulty *of the step-indexed-LR method* — closing `lr_sound` needs a density invariant over arbitrary
related stacks that forces either a frozen-statement change or a hard reachability lemma. **ADR-0054 already
recorded Lexa's Leroy forward-simulation (no LR) as the alternative method.** So the most actionable insight
the paper could yield is *not* "are we lexical?" (we are) but: **does Lexa's forward-simulation proof
technique dissolve the Canonical wall that our LR hit?** If so, inc-6's compiler-correctness hop might adopt
Lexa's method rather than push the LR through route 1/2.

Secondary: Lexa is an *efficient* compiler; our CalcVM→WasmFX lowering (inc-6) is unbuilt. Lexa's
*compilation* technique (how it lowers lexical dispatch to efficient code — direct jumps? segmented stacks?
evidence vectors?) is exactly the design input the route-B re-derivation and the WasmFX backend will need.

## See also
- ADR-0016 (the two-hop) · ADR-0052 (dispatch is lexical) · ADR-0054/0055 (cap-by-identity) ·
  ADR-0056/0057 (B-occ) · ADR-0044 (dynamic-vs-lexical, cites Lexa) · ADR-0050 (the de-Bruijn shift wall)
- `docs/architecture/core-overview.md` (module/coupling map) · `CONTEXT.md` (live position) ·
  `paths/PATH-inc5-lr-reindex.md` (the LR re-key + the Canonical wall detail)
