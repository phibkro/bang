<!-- note-status: active -->
# The calculated `wgcexec` machine — calculation plan + tractability spike (Wave D, 2026-07-12)

> **Verdict (one sentence).** The 3-step unlock the S5 refutation priced (calculate a
> WasmGC machine from the kernel · prove it ≡ `Source.eval` · show `emitModuleGC` is its
> text image) is **STATEABLE and — for the load-bearing state fragment — TRACTABLE**: a
> refute-first spike (`scratch/WgcexecSpike.lean`) hand-derives `wgcexec` for pure-arith +
> closures + state over an explicit `$env` + box heap and shows it VALUE-AGREES with the
> closed-term (`evalD`-shaped) oracle after reification on 3 witnesses (incl. state
> mutated through a captured-env closure), with the reification's heap and leaf legs
> PROVEN axiom-clean and the only residual `sorry` being the STANDARD env-machine
> substitution-coherence debt — **not** a structural mismatch in the machine's shape. The
> machine is NOT mispriced. It remains **post-v1** (gated on ADR-0059 per prior ruling);
> the price is now REAL, and the **pure+state fragment is cheap enough to bank early as a
> standing adequacy gate** if the operator wants a verified floor under the GC emitter.

Spike: `scratch/WgcexecSpike.lean` (builds green, EXIT 0; 8 `#guard`s pass; `reifyHeap_get`
+ `closeEnv_nil/cons` + `ret_leaf_reifies` proved; one honest `sorry` at the top-level
simulation marking the subst-coherence debt). This note refines:
`rung5-s5-proofgrade-refutation.md` (the priced unlock), `cap-gc-rep-design.md` §8.2-8.3
(the C4 stamp clause folds in here), `emission-rung4/5-design.md` (the rep).

---

## 1 · The calculation plan

### 1.1 · Starting semantics — `evalD`, NOT `Source.eval`'s CK directly

The manager flagged the choice. **Start from `evalD`** (`AbstractMachine.lean:269`), the
same Bahr–Hutton starting point that produced the inline CalcVM. Reasons:

- `evalD` is ALREADY the "kernel semantics with effects realized as explicit STATE"
  (`SStore`/`THeap`/`CStore`) — the state-reification the GC path also needs. Deriving the
  GC machine from `evalD` reuses that store structure; deriving from `Source.eval`'s CK
  would re-do the effect-to-store lowering the CalcVM already paid for.
- `evalD` is the reference the inline `exec` was calculated from, and it is tied back to
  the kernel by `evalD_agrees_source` (an existing theorem). A `wgcexec` derived from
  `evalD` inherits that tie-back for free: `wgcexec ≡ evalD ≡ Source.eval`.
- Invariant #4 (the machine is the calculation's OUTPUT) is satisfied identically: each
  `evalD` clause forces a `wgcexec` arm, exactly as it forced a `compile`/`exec` arm.

The ONE genuinely new thing the GC rep adds over `evalD`/`exec`/`wexec` is that it reifies
**meta-level substitution** (`Comp.subst v N`) into an **explicit `$env` cons-list with
de-Bruijn `$lookup`**, and closures into `$clos (field $code) (field $env)`. `evalD`,
`exec`, and `wexec` all keep values CLOSED and substitute at the meta level; `emitModuleGC`
does not (it cannot — a static text emitter can't run the interpreter, rung-1 note §4). So
the derivation from `evalD` to `wgcexec` is a **known program transformation**: closure
conversion / environment introduction (the "closures = delayed substitutions" step,
Danvy; the same move that turns a substitution-based interpreter into an environment
machine, e.g. Krivine / the CEK-vs-substitution equivalence).

### 1.2 · The derivation steps

```
evalD  (meta-subst, closed values, SStore/THeap/CStore)
  │  STEP A — environment introduction (closure conversion)
  │     · defunctionalize `Comp.subst v N` into "run N under (v :: ρ)" with an explicit
  │       env ρ; `vvar i` becomes `ρ[i]?` ($lookup). This is where the $env cons-list
  │       FALLS OUT — it is the reification of the substitution the kernel does at the
  │       meta level. A binder (letC/lam/case-payload/split) PREPENDS; force runs the
  │       thunk body under its CAPTURED env; app runs the lam body under arg :: captured.
  │     · a `vthunk`/`lam` VALUE becomes a `$clos` = (code, captured-env) snapshot.
  ▼
wgcexec-substrate  (explicit env, closed by capture, SStore/THeap/CStore still meta-store)
  │  STEP B — heap-of-boxes for the resumptive stores
  │     · the state SStore cell → a $ref MUTABLE BOX at a heap address (struct.set = put);
  │       the txn THeap → a $txbox pointing at a GC list of $ref cells; the custom CStore
  │       clause list → a $txbox of lam-style $clos (the emission-rung5 S3/S4 rep).
  │     · get/put/newTVar/readTVar/writeTVar become struct.get/set on the box (NO store
  │       threaded through the return type — the mutation is in the heap, the box addr is
  │       in the env). This is the rung-5 "one $ref box, visible through any capturing
  │       closure" merge (emission-rung5 §(b) Candidate 1).
  ▼
wgcexec  (explicit env + box heap — the ADR-0059 GC abstract machine)
  │  STEP C — control-flow formers as CALCULATED wasm artifacts
  │     · handle(throws) → try_table; raise → throw_ref (the escape from the box-heap
  │       machine is the wasm unwind — CALCULATED, the rung-5 S2 port). handle(state/txn/
  │       custom) → mint $id (the $capMint watermark), push the box/cap into the env slot,
  │       run the body, pop (restore $liveTop). perform → $capGate then struct.get/set /
  │       call_ref (id-keyed dispatch, the OP arm's image).
  ▼
Code image  (a compile : Comp → WgcCode, structural fold; see §1.3)
```

**Where try_table/throw_ref sit: CALCULATED artifacts, not axiomatized wasm behaviors.**
The step function's `handle(throws)`/`raise` arms are the machine's own control-flow (an
`Option`-monad short-circuit / a saved-continuation abort, exactly `exec`'s `UNMARK`/
`THROW`/`unwindFind`). The wasm `try_table`/`throw_ref` are the TEXT IMAGE of those arms
(STEP: §1.3's lowering), the same way `exec`'s `OP` arm images to `struct.get`. So the
machine axiomatizes NO wasm semantics; it is a Lean `def` whose lowering to `.wat` is a
syntactic image. (This mirrors `wexec`: a Lean machine, `run` on wasmtime is the harness.)

### 1.3 · The adequacy seam — the formal statement connecting `wgcexec` to `emitModuleGC`'s TEXT

This is the crux the manager asked to nail. The connection is a **two-stage image**,
structurally the SAME shape the inline path already has (`compile` → `Code`; `lowerCode`/
`emit` → `.wat` text):

```
  Comp ──compileGC──▶ WgcCode ──emitGC──▶ String (.wat)
        (structural           (per-instr
         fold, the             text template)
         calculated
         machine's
         program)
   │                     │
   │  wgcexec over       │  wasmtime runs the text
   │  WgcCode = the      │
   │  machine semantics  │
```

- **`compileGC : Comp → WgcCode`** — a structural fold, DERIVED from `wgcexec` by the same
  Bahr–Hutton reasoning that gave `compile : Comp → Code`. The key finding from reading the
  emitter: **`emitCompGC (envL, caps) c` (`WasmEmit.lean:864`) is ALREADY this fold** — it
  walks `Comp` with `(envL : runtime env local, caps : compile-time cap metadata)` exactly
  as `compile` walks with a continuation, but it emits TEXT directly rather than an
  intermediate `WgcCode`. So `compileGC` is `emitCompGC` with the codomain changed from
  `String` to a `WgcCode` inductive; `emitGC` is the residual per-instruction text
  template. The refactor is MECHANICAL (extract the `WgcCode` intermediate), and it makes
  the emitter's structure a theorem-visible object.

- **The adequacy statement** (the `$env`-slot↔store bijection made STATEABLE):
  ```
     wgcexec f ρ h (compileGC c) ≡ evalD f (σ,τ,κ of h) c        (under reifyEnv/reifyHeap)
     emitGC (compileGC c) = the .wat emitModuleGC emits                (syntactic image)
  ```
  The FIRST line is the machine ≡ oracle (proven by a fuel forward-simulation, ADR-0035
  shape). The SECOND is the text image (a syntactic equality at instruction granularity —
  each `WgcCode` instr renders to a fixed `.wat` fragment, an `exec_wexec`-style lowering
  lemma). Composed: `emitModuleGC c`'s text is the faithful image of a machine that ≡ the
  kernel — the miscompile class #134 exposed becomes UNREPRESENTABLE (a should-fail path
  can't emit a value-returning module, because the machine it images fails loud).

- **Syntactic image at which granularity?** Per-instruction (the `WgcCode` inductive's
  constructors), NOT per-whole-module-string. `emitModuleGC` = a module wrapper (type
  decls, `$main` export, the `gcHelpers` prelude) around `emitCompGC`'s body text. The
  bijection lives on the BODY (`emitCompGC`); the wrapper is fixed boilerplate. So the
  image lemma is `emitGC instr = <the fixed template for instr>`, folded over the code —
  exactly the granularity `lowerInstr`/`lowerCode` (`Wasm.lean:211`) use for the inline
  path.

### 1.4 · The reification IS the `$env`-slot↔store bijection the refutation named

The S5 refutation named "the `$env`-slot↔store bijection" as the unstateable half. In the
spike it becomes two CONCRETE, proved functions (`WgcexecSpike.lean` §5):

- `reifyV : RVal → WVal` — unloads a runtime `clo M ρ` closure into a closed thunk by
  substituting its captured env into the body (`$val`-tree → kernel-value read-back).
- `closeEnv ρ c` / `reifyHeap h` — flatten the runtime env into the term by multi-subst,
  and map the box heap to the kernel's value store.

`envSlotStore : GCEnv ≃ (SStore × THeap × CStore)` the refutation gestured at is exactly
`reifyHeap` split per kind ($ref → SStore cell, $txbox-list → THeap, $txbox-clauses →
CStore). It is stateable BECAUSE `wgcexec` exists as a Lean `def` to relate to — the whole
point of the unlock.

---

## 2 · The spike — the tractability oracle (refute-first)

`scratch/WgcexecSpike.lean` (self-contained, imports only `Bang.Core.IR`; builds EXIT 0).

**Fragment**: pure arith (`add`) + closures (`letC`/`force`/`lam`/`app` with env capture)
+ ONE effect (state, as `getB`/`putB`/`newB` on a `$ref`-image box heap). This is the
smallest fragment that exercises the load-bearing merge: **a closure that captures a state
cell and sees a `put` through the shared env** (emission-rung5's key witness, now in Lean).

**What it builds**:
- `wgcexec : Nat → REnv → RHeap → WComp → Option (RVal × RHeap)` — the env-machine, with
  `RVal.clo` carrying a captured env ($clos), a box heap (the $ref cells), de-Bruijn
  `$lookup` (`resolveV`). Hand-derived to the §1.2 shape.
- `evalC` — the closed-term (meta-subst) oracle, the `evalD`-image for the fragment.
- `reifyV`/`closeEnv`/`reifyHeap` — the reification (§1.4).

**What it proves / measures**:

| obligation | status | evidence |
|---|---|---|
| env-machine value-agrees with the oracle (pure-through-closure, `w1`) | ✅ `#guard` | reifyV ∘ wgcexec = evalC |
| state MUTATED through a captured-env closure (`w2`, put-then-force ⇒ 20) | ✅ `#guard` | the LOAD-BEARING case |
| nested closures + re-put (closure over another closure's env, `w3` ⇒ 6) | ✅ `#guard` | the deep case |
| heap reifies in-step (`reifyHeap_get`) | ✅ **proved** | pure `List.map` — the EASY leg |
| `closeEnv` fold/unfold (`closeEnv_nil`/`_cons`) | ✅ **proved** | definitional |
| the leaf reifies with NO coherence debt (`ret_leaf_reifies`) | ✅ **proved** | induction on ρ |
| the full simulation `wgcexec_reifies` | ⚠️ `sorry` | the binder subst-coherence debt (below) |

**The wall, located precisely.** The only `sorry` is `wgcexec_reifies`'s binder cases
(letC/app/force), which need `closeEnv` to commute with the structural formers under a
shifted index — the STANDARD "closures = delayed substitutions" coherence (a
`substC`-commutes-with-shift lemma). This is:
- NOT a structural mismatch in `wgcexec`'s shape (the closed-value/heap cases discharge
  outright — proven, no debt),
- a KNOWN-tractable obligation (every env-machine correctness proof — Krivine, CEK,
  Danvy's "closures = defunctionalized continuations" — pays exactly this),
- the same shape as the inline CalcVM's `compile`/`exec` residual-recompile lemmas,
  already discharged for the substitution path in `AbstractMachine.lean`.

**Verdict**: the state fragment's calculation does NOT fight the rep. The machine is
correctly priced. A cheap refutation (a witness where wgcexec ≠ oracle) did NOT appear —
value-agreement holds including the escape-adjacent state-through-closure case.

---

## 3 · Sizing the whole machine

Per-fragment effort, the transferable infrastructure, and the honest estimate.

### 3.1 · Per-fragment effort

```
fragment            derivation (STEP A/B/C)          proof effort         notes
──────────────────────────────────────────────────────────────────────────────────────
pure (ret/binop/    A only (env intro); no heap      SMALL — the leaf     spike PROVES the
 ADT elim/unfold)                                     cases (proved in     leaf; ADT elim = same
                                                      spike)               fold as case/split
closures (letC/     A (the $clos capture); the        MEDIUM — the subst-  the spike's one sorry;
 force/lam/app/rec)  thunk≠lam split (rung-4 bug)      coherence lemmas     rec falls out of the
                                                      (KNOWN tractable)     μ-knot (rung-4 §3)
state (get/put/     B ($ref box heap) + the           MEDIUM — heap-op     spike PROVES the heap
 newB)               $capMint/$capGate stamp          reify (proved) +      leg; the stamp = §3.3
                                                      the box-addr fresh
throws (handle/      C (try_table/throw_ref); the      MEDIUM — the abort   pure control flow, rep-
 raise)              saved-continuation abort          = unwindFind image   agnostic (rung-5 §S2)
transaction         B (the $txbox list) + rollback     MEDIUM-LARGE — the   journal/rollback = the
                     (catch_all_ref/throw_ref)         Θ↔list bijection +    rung-3 S3 rep; abort
                                                      the rollback replay   restore is explicit
custom (user eff)   B ($txbox clause $clos) + the      MEDIUM — the clause  the inline-service sub-
                     call_ref clause-resume            call_ref = customUp-  eval (rung-5 S4); one-
                                                      date image            shot, no reification
caps-stamp (escape) the $liveTop watermark ≡           SMALL-MEDIUM — this  cap-gc-rep §8.2 C4:
 = the C4 clause     WellCounted < g                   IS the C4 clause,     "$liveTop ≡ WellCounted
                                                      folds into THIS       < g", stateable against
                                                      proof                 wgcexec (§3.3)
```

### 3.2 · Transferable infrastructure

- **`injStack`/`injHStack`/`compileV`/`recoverV`** (`Wasm.lean:179,517`) — the inline
  path's value-injection. PARTIALLY transfers: the SHAPE (a value-rep map + a stack-lift)
  is reused, but the GC rep's map is `reifyV`/`closeEnv` (env-aware), not the inline
  identity injection. So the scaffolding transfers, the specific map is new.
- **`exec_wexec_sim` machinery** (`Wasm.lean:1092`) — the fuel-induction + per-instr
  `cases` skeleton. The PROOF STRUCTURE transfers verbatim (induction on fuel, cases on
  head instr, IH to the residual-recompiled body). The per-arm content differs (env vs
  closed). This is the single biggest transfer: the ADR-0035 forward-simulation template
  is proven to work for handler compilation on the inline path, and `wgcexec_reifies` is
  the SAME template with the env-reification relation swapped in.
- **`CodePure`/`StackPure`/`HStackPure`** — the purity side-conditions. Reused as-is
  (`VcapFree ∧` the fragment predicates).
- **`evalD_agrees_source`** — the tie-back to the kernel. Reused verbatim: `wgcexec ≡
  evalD ≡ Source.eval` composes through it.
- **The `#134` escape stamp** (`gcHelpers` $capMint/$capExit/$capGate, cap-gc-rep §8.2) —
  ALREADY implements the runtime watermark; the C4 proof clause ("$liveTop ≡ WellCounted
  < g") is a lemma ABOUT `wgcexec`'s stamp arms, folds into `wgcexec_reifies`.

### 3.3 · The caps-stamp clause belongs in THIS proof (per the brief)

cap-gc-rep §8.2-8.3's C4 ("$liveTop watermark ≡ WellCounted < g") and the txn-abort
`$capExit` residual are NOT a lane-local C4 — they are the escape-soundness CLAUSE of
`wgcexec_reifies`. Concretely: `wgcexec`'s `handle` arm mints `id := g` and pushes it
(the $capMint watermark bump), its `perform` arm gates `id < liveTop` (the $capGate); the
simulation must show this gate FIRES exactly when `evalD`'s `splitAtId`/`idDispatch`
returns `.escapedCap` (i.e. when `n` is in no live store). That is `WellCounted (g, K, _)`
transported to the box-heap machine — the "runtime realization of an invariant the kernel
already proves" (cap-gc-rep §5), a transfer, not a new theory. The txn-abort `$capExit`
residual (restore $liveTop on rollback) is the frame-pop image, discharged by the same
push/pop bookkeeping the state arm uses. So the escape-fail-loud that #134 exposed as a
LIVE miscompile becomes a PROVEN conjunct of the GC machine's correctness — the strongest
argument for banking at least the state fragment (§4).

### 3.4 · The honest multi-session estimate

Comparable to the ORIGINAL CalcVM derivation (the refutation's own pricing: "a rung-5-scale
calculation"). Concretely, banking on the transfers above:

- **`compileGC`/`emitGC`/`WgcCode` extraction** (the refactor making `emitCompGC` a
  theorem-visible fold): ~1 session. Mechanical but touches the live emitter (needs the
  WasmEmit owner's coordination — the text output must stay byte-identical, gated by the
  existing diff harness).
- **pure + state `wgcexec_reifies`** (the spike's fragment, subst-coherence discharged):
  ~2-3 sessions. This is the CHEAP, bankable slice (§4).
- **closures + recursion**: ~2 sessions (the μ-knot + the thunk≠lam coherence).
- **throws + transaction + custom**: ~3-4 sessions (the abort/rollback/clause-resume
  arms, each a MEDIUM per §3.1).
- **the caps-stamp escape clause**: ~1 session (folded into the state/custom arms).
- **the `emitGC` text-image lemma** (per-instr syntactic image): ~1-2 sessions.

Total: **~10-13 sessions**, i.e. a full increment, gated on ADR-0059 landing (the machine
is the ADR-0059 GC abstract machine; building it before ADR-0059 formalizes the target
would be premature). This matches the refutation's "rung-5-scale, post-v1" pricing — the
spike CONFIRMS the price rather than discovering a hidden multiplier.

---

## 4 · The decision the operator faces (and the early-bank option)

**The standing ruling** (S5 refutation, rung-5 §(c)): the full proof-grade GC path is
**post-v1**, gated on ADR-0059. This probe does NOT reverse that — it makes the price REAL
and confirms it is not mispriced. The `emitModuleGC` text backend stays differential-tested
(inv #1) as the sanctioned tested-stratum oracle in the interim.

**The early-bank option (recommended for consideration).** The **pure + state fragment is
cheap enough to bank NOW as a standing adequacy gate**, independently of the full machine:

- It is ~2-3 sessions on top of the `compileGC` extraction (~1 session).
- It closes the HIGHEST-VALUE slice: #134 proved the GC emit path can SILENTLY miscompile a
  should-fail (escape) path on state caps, and the differential harness only catches value
  disagreements someone thought to test. A calculated pure+state `wgcexec` + the escape
  clause (§3.3) makes the state-cap miscompile class UNREPRESENTABLE — a verified floor
  under exactly the defect #134 exposed as LIVE.
- It is a genuine adequacy GATE (a Lean theorem `wgcexec_reifies` over the state fragment,
  axiom-gated), not another differential test — the stratification's verified core
  extended one fragment up the GC path.

**Against banking early**: it needs the `emitCompGC`→`compileGC` refactor, which touches the
live emitter (owner coordination); and the fragment gate only covers state/pure programs,
so the harness stays load-bearing for the rest — a partial floor, honestly labelled.

**The whole-machine decision** stays where the ruling put it: post-v1, an increment, opened
when ADR-0059 lands and the operator wants the GC path on the verified stratum. This probe's
contribution: the price is REAL (~10-13 sessions, §3.4), the shape is PROVEN tractable (the
spike), and the caps-stamp escape soundness is IN the story (§3.3), not a separate debt.

---

## 5 · One-glance status

```
UNLOCK STATEABLE?   YES. wgcexec exists as a Lean def (the spike hand-derives it); the
                    $env-slot↔store bijection = reifyV/closeEnv/reifyHeap (concrete, proved
                    on the leaf+heap legs). The refutation's "unstateable in v1" was about
                    the TEXT emitter having no machine — this builds the machine.
START FROM          evalD (not Source.eval CK) — reuses its store reification + the
                    evalD_agrees_source tie-back; inv #4 satisfied per-clause.
NEW CONTENT         env introduction (the $env cons-list = reified meta-subst) + box heap
                    ($ref/$txbox = reified SStore/THeap/CStore). try_table/throw_ref are
                    CALCULATED control-flow artifacts (the machine's own abort, lowered),
                    not axiomatized wasm.
ADEQUACY SEAM       two-stage: compileGC : Comp→WgcCode (= emitCompGC with codomain swapped
                    to a WgcCode inductive — a MECHANICAL extract) then emitGC : per-instr
                    text image (exec_wexec-style, per-instruction granularity).
SPIKE VERDICT       pure+closures+state TRACTABLE: 3 witnesses value-agree (incl. state-
                    through-captured-closure), heap+leaf legs PROVED axiom-clean, the one
                    sorry = STANDARD subst-coherence (known-tractable), NOT a machine wall.
                    No refutation appeared.
CAPS-STAMP          the $liveTop ≡ WellCounted<g clause (cap-gc-rep §8.2 C4) is a CONJUNCT
                    of wgcexec_reifies (the escape-fail-loud #134 exposed → PROVEN), not a
                    lane-local C4.
PRICE               ~10-13 sessions (full machine), rung-5-scale, post-v1, gated ADR-0059.
                    Confirms the refutation's pricing; no hidden multiplier.
EARLY-BANK          pure+state fragment ~2-3 sessions (+ ~1 for compileGC extract) = a
                    standing adequacy GATE that makes the #134 state-cap miscompile class
                    UNREPRESENTABLE. Recommended for operator consideration; the rest stays
                    differential-tested (inv #1). Whole-machine stays post-v1 per ruling.
```
