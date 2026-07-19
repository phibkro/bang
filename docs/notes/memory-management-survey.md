<!-- note-status: active -->
# Memory-management — design survey: param-passing handlers, the CBPV stack/heap split, and the heap ladder

> The operator's question (2026-07-10): *how does bang manage memory?* — mutable state, the
> stack/heap boundary, and the garbage-collection story. This note mines the design space and the
> code already in the tree, then prices each pillar against what bang has **already pinned**
> (ADR-0025 state handler, ADR-0030 STM-as-handler, ADR-0063 escapedCap, ADR-0092 D5 param-update,
> ADR-0094 env machine). It is an **ADR-input note, not an ADR**: it presents the design, names the
> prior art and the honest cost, and — for section 4 — reports a build-checkable verdict on the
> load-bearing analogy the operator asked to test the hardest. Every claim is graded
> shown / suggests / can't-verify and, where it is a claim about bang's own code, cited to
> `file:line`. Web citations live in §References; `refs.bib` additions are listed there too.

## 0 · The one-paragraph thesis

bang does not have a memory-management *subsystem* — it has the **CBPV value/computation split**, and
memory management falls out of it. The load-bearing observation: **the only object that outlives the
stack frame that created it is a thunk** (a `U`-typed value — a suspended computation closed over its
environment). Everything else — values, `let`-results, handler frames, the effect stores — is
stack-disciplined, LIFO, and dies when its frame pops. So the heap is exactly "the set of live
thunks/closures", and every richer memory story bang could adopt is a *policy over that one seam*:
mutable state is a handler that threads a carried value (no heap at all — §1); the usage grade `Mult`
in the type is the dial that says whether a binder is erased (0), used-in-place (1), or heap-shared
(ω) (§2); and the heap-reclamation ladder (host-GC now → Perceus reference-counting-with-reuse at
v1.x → regions-as-handler-scopes post-v1, §3) climbs *without touching the kernel*, because a handler
scope already **is** a stack-disciplined region (Tofte–Talpin's arena, for free). The one place the
seam is not yet airtight is a capability captured into a thunk that outlives its handler — and that is
exactly the escape ADR-0063 already detects and fail-louds. §4 asks how far that machinery
generalizes to region-escape detection; the answer (a partial refinement, not a clean isomorphism) is
the note's sharpest finding.

```
   memory concept                bang's construct                            landed / pinned
   ─────────────────────────     ──────────────────────────────────────     ───────────────────────
   mutable cell / heap slot      a `state`/`custom` handler's carried value   Dispatch.lean:133-181
   shared mutable state          a TVar under a `transaction` handler         ADR-0030, Dispatch.lean:143
   the stack                     CBPV frames: let/app/handleF + the MEnv      EnvMachine.lean:89-93
   the heap (escaping objects)   thunks = closures `mvclos M ρ`               EnvMachine.lean:81-82
   the erasure/in-place/share    the usage grade `Mult` in VTy/CTy            IR.lean:221-241, Spec.lean:164
     policy dial
   reclamation (now)             host RC (Lean); Wasm 3.0 WasmGC at backend    ADR-0059 (grade-directed)
   reclamation (v1.x)            Perceus RC + reuse (soundness rides U)        §3, this note
   reclamation (post-v1)         regions = handler scopes (arena free at pop)  os-inspiration §7, ADR-INPUT
   "closure outlived its scope"  escapedCap defined fail-loud                  ADR-0063, Dispatch.lean:182
   ─────────────────────────     ──────────────────────────────────────     ───────────────────────
```

---

## 1 · Handler mutability = parameter-passing handlers over EXISTING machine capability

### 1.1 The claim, and the code that proves it

The canonical account of stateful effects (Plotkin–Pretnar algebraic effects + handlers; Bauer–Pretnar)
models `get`/`put` as **operations of a `state` handler that threads a stored value** — no heap cell,
just a value carried in the handler and *replaced* at each `put`. bang's kernel implements exactly this,
and the replacement is visible in one line:

```
-- Bang/Core/Semantics/Dispatch.lean:133-137  (dispatchOn, the state arm)
| .state ℓ' s =>
    if op == "get" then
      some (Kᵢ ++ Frame.handleF n (.state ℓ' s) :: Kₒ, .ret s)          -- resume, state KEPT (s' = s)
    else
      some (Kᵢ ++ Frame.handleF n (.state ℓ' v) :: Kₒ, .ret .vunit)     -- resume, state REPLACED s ↦ v
```

**Shown** (source, `Dispatch.lean:133-137`): a `put v` reinstalls the handler frame carrying `v` in
place of the old `s`. The mutation is real — the carried value changes — but there is **no mutable
memory**: the "cell" is a value threaded through a one-shot resumptive continuation (ADR-0025). The
transaction handler (`Dispatch.lean:143-164`) is the same mechanism generalized from one cell to a
list-heap `Θ`: `writeTVar` reinstalls `transaction ℓ' (storeSet Θ i w)` (`:162`) — replace-in-a-list,
same threading. This is why ADR-0030 could ship STM with **zero new kernel primitives** (invariant #5
intact): STM *is* `state` over a list, and rollback is free (an abort discards the frame, so the
threaded `Θ'` never commits — `Dispatch.lean:138-142`).

### 1.2 Custom (user-effect) handlers: v1 is READ-ONLY param; D5 is the mutability surface slice

The user-effect arm (ADR-0085 Stage 2, ADR-0092 typing) uses the identical resume-and-reinstall shape,
but the carried value — the handler *parameter* `p` — is reinstalled **unchanged**:

```
-- Bang/Core/Semantics/Dispatch.lean:177-181  (the custom arm)
| .custom ℓ' p clauses =>
    match clauses.find? (·.1 == op) with
    | some clause =>
        some (Kᵢ ++ Frame.handleF n (.custom ℓ' p clauses) :: Kₒ,          -- param p REINSTALLED UNCHANGED
              Comp.subst p (Comp.subst (Val.shift v) clause.2))
```

The comment at `Dispatch.lean:173` states the restriction outright: *"The reinstalled param is `p`
UNCHANGED: v1 is a READ-ONLY param (reader/config/Net — `get`-like); put-like param MUTATION is a
stage-4 concern."* So the finding for section 1 is precise and **build-grounded**:

> **User-handler mutability is not new semantics — it is the D5 surface slice** (ADR-0092 §Decision,
> "D5 — the param-UPDATE protocol … `put`-like ops mutating the carried param"). The machine already
> knows how to reinstall a *replaced* carried value: the built-in `state`/`transaction` arms do it at
> every `put`/`write` (`Dispatch.lean:137,162`). D5 is the move that lets a *user* clause return a new
> `p'` and have the reinstall thread it — literally the `state` arm's `s ↦ v` swap, generalized to the
> `custom` arm. **Suggests** (the two arms are structurally identical bar the reinstalled value):
> the D5 cost is a clause-return-shape + a soundness arm, not a kernel-mechanism addition. ADR-0092
> D5's own "pair-return protocol" candidate is exactly this.

Why v1 defers it (ADR-0092 §Revisit-if, ADR-0087 §Open-questions): the answer-grade wall. The captured
continuation expects the perform's returner type, whose grade is *free*; a general clause body's grade
is structure-pinned, and no re-grading lemma exists — so v1 pins clause bodies to the return shape
`ret w` (recovering `ret`'s grade-freedom), which is incompatible with also threading an updated `p`
in the same clause. Mutable user-handlers wait on that grade machinery (Q27). **This is a typing cost,
not a semantic one** — the semantics (the reinstall) is already there.

### 1.3 The escalation to shared/concurrent state: TVar-in-param (ADR-0030)

Parameter-passing handlers give **transaction-local** mutable state — one computation's tree, folded
(ADR-0030 §"what privilege earns us": *"A handler is a fold over ONE computation's tree"*). What they
structurally **cannot** give is state shared *across independent computations* — that needs a heap that
survives across the fold, owned by the runtime. bang's ladder for this is explicit and does not add a
memory primitive:

```
  need                          bang's construct                          cost
  ───────────────────────────   ──────────────────────────────────────   ──────────────────────────
  transaction-local mutation    param-passing handler (§1.1)              LANDED (Dispatch.lean)
  shared mutable cell (1 thread) TVar under `transaction` handler          LANDED (ADR-0030, v1)
  shared across THREADS          the privileged STM shared heap             post-v1 (ADR-0030 §Revisit)
```

TVars are the v1 shared-state story: they live in the transaction handler's list-heap `Θ`, addressed
by `int` index (ADR-0030 amendment), and are `ω`-graded (freely shareable — ADR-0030 rejected
alternative 4 defers linear TVars to the rung-5 "QTT surfaced" hinge). The genuinely-privileged
shared heap (read-set validation, `retry`-wakeup, opacity) returns only with concurrency (ROADMAP ◊5+),
which is the *one* thing invariant #3 still reserves as privileged. **Shown** (ADR-0030 §Consequences):
"STM-the-privileged-primitive remains a *named* member of the five, simply unused in v1."

---

## 2 · Stack vs heap = the CBPV split, made type-visible

### 2.1 The split, and where the code draws it

Call-by-push-value's discipline: **values are stack-shaped, computations are frame-shaped, and the only
value that carries a suspended computation is a thunk** (`U`-type — `IR.lean:224`, `| U : Eff → CTy →
VTy`). The env machine (ADR-0094) makes this operational and draws the stack/heap line as sharply as
the survey needs:

```
-- Bang/Backend/EnvMachine.lean:77-93
inductive MVal where
  | mvunit | mvint (n) | mvcap (n ℓ) | mvpair …          -- ground values: STACK-shaped, no env
  | mvclos : Comp → MEnv → MVal                          -- the CLOSURE: a Comp + the env it captured
inductive MEnv where                                     -- the variable environment = the STACK
  | nil | cons : MVal → MEnv → MEnv
```

**Shown** (`EnvMachine.lean:81-82` + the module doc `:71-75`): *"computation `vthunk M` becomes a
**closure** `mvclos M ρ` … `vvar` VANISHES from `MVal`: environment values are ground."* And the
embedding `evalV` (`:116-121`) confirms the closure is the *sole* env-capturing constructor: *"The ONLY
constructor that captures the env is `vthunk M ↦ mvclos M ρ` — every other [is ground]"* (`:113`,
`:121`). So:

```
   CBPV object            machine representation          lifetime          memory class
   ────────────────────   ────────────────────────────    ───────────────   ──────────────
   value (unit/int/cap)   MVal ground                     frame-local       STACK
   let-result             bound into the MEnv (ρ)         frame-local       STACK
   handler frame          handleF in the EvalCtx          LIFO (install/pop) STACK
   thunk (U-type)         mvclos M ρ (closure)            can escape frame   HEAP ← the only one
   effect store (Θ/state) carried in the handler frame    frame-local       STACK (not var-heap)
```

The effect stores (`SStore`/`THeap`) are **effect-state, not the variable heap** — ADR-0094 is explicit
(`:35`): *"the effect stores are additively untouched … `SStore`/`THeap` are effect-state, not var-env."*
This matters for the survey: the *only* heap-shaped thing in bang's value domain is the closure. Get
closure lifetime right and you have the whole memory story.

### 2.2 The usage grade as the policy dial

CBPV says *which* objects can escape; QTT's multiplicity grade says *how* each is used, and that is the
refinement dial for memory. The grade `Mult` is a type parameter of every type (`IR.lean:221`
`VTy Eff Mult`, `:237` `F : Mult → VTy → CTy`, `:241` `arr : Mult → …`), instantiated to the three-valued QTT semiring `{zero, one, omega}`
(`Bang/Core/Grade.lean:25-26` — the concrete `QTT` instance of the `Mult` parameter; the kernel
stays parametric in `[Semiring Mult]`). The reading for memory:

```
   grade   QTT meaning         memory policy it licenses          bang status
   ─────   ─────────────────   ────────────────────────────────   ───────────────────────────────
   0       used zero times      ERASED — never allocated/run       zero_usage_erasable (Spec:164) †
   1       used exactly once     in-place / linear — reuse-safe     the Perceus reuse rung (§3.2)
   ω       used freely           heap + shared (must be GC'd/RC'd)  the default today
```

† **Honest calibration.** `zero_usage_erasable` (`Spec.lean:164`) is a **stated theorem whose body is
currently `sorry`** (`Spec.lean:187`), blocked on `lr_fundamental` (PROOF_ORDER #1, still partial —
state/txn arms). So the 0-rung is *formalized intent with a mechanized template* (Torczon's grade-0
coeffect erasure, `semtyping.v`, cited in the proof comment `:174-184`), **not** a closed proof today.
The claim "grade 0 ⟹ erasable" is therefore **suggests (design-level, with a mechanized precedent)**,
not **shown (proven in-tree)**. This is the one place section 2's clean story has a live proof
obligation, and it is worth stating plainly: the erasure dial is real in the *type*, pending in the
*proof*.

The 1-rung (linear/in-place) is the interesting one for memory: a grade-1 binder is used exactly once,
so its storage can be **reused in place** rather than copied-then-freed. That is precisely Perceus's
reuse analysis (§3.2), and it is why the U axis is the soundness carrier for the RC-with-reuse ladder:
reuse is safe *because* the grade proves single-use. The ω-rung is the fallback — freely-shared values
that a tracing/counting collector must manage. **Suggests** (kernel-substrate-survey §2a lists U as a
live grade axis, `zero_usage_erasable` as the 0-rung): the memory policy is not a separate analysis but
a *reading of a grade the type system already carries*.

---

## 3 · The heap-reclamation ladder: host-GC → Perceus → regions

Invariant #7 (performance second-class) frames the sequencing: a slow correct path beats a fast
unverified one, so bang delegates reclamation to a trusted host **now** and climbs the ladder only as
the language earns the grades that make each rung sound. Three rungs, each a strict superset of trust:

```
  rung                 mechanism                              trust source                    when
  ──────────────────   ────────────────────────────────────  ──────────────────────────────  ──────────
  R0  host-delegated   Lean RC (host); Wasm 3.0 WasmGC at      the host runtime is trusted      NOW
                       the backend (ADR-0059)                 (idealized GC heap, not a switch)
  R1  RC + reuse        Perceus (Koka/Lean4 runtime)           soundness rides the U grades     v1.x
  R2  regions           handler scope = arena, free-at-pop     handler LIFO = Tofte region      post-v1
```

### 3.1 R0 — delegate to the host (now); at the backend, the heap IS the control representation

Today bang's evaluators run *inside Lean*, so reclamation is **Lean 4's own reference counting** — the
values are Lean objects, collected by Lean's RC. The verified compiler backend targets **Wasm 3.0**
(ADR-0059, refining ADR-0016), and here the memory story and the *control* story stop being separable —
which is the correction that makes this rung richer than a plain "delegate to the host GC."

**There is no compatibility question to answer.** GC (managed `struct`/`array`, typed refs), tail calls
(`return_call`), and exception handling (tags, `throw`/`try_table`) are all **standardized core features
of Wasm 3.0** (Sept 2025) — not separate proposals to be composed or checked for interoperability. So
bang's grade-directed lowering maps each grade to a *core 3.0 instruction*, and nothing needs verifying
about whether those features coexist; the standard already guarantees it. (The one thing that did **not**
land in 3.0 is stack switching / WasmFX — which is exactly why ADR-0059 does not depend on it: WasmFX is
a post-standardization fast-path for the `general` slot only, never a v1 requirement.)

**The lowering is grade-directed** — the effect row 2-colors the program for free (ADR-0059 §Decision):

```
  pure (empty row)        → native Wasm (direct calls, native stack)         core 3.0
  effectful, abort (0×)   → Wasm exception (throw / try_table)               core 3.0
  effectful, tail (1× tl) → direct call in place (return_call trampoline)    core 3.0
  effectful, general (1×) → GC-frame-chain (managed structs) + trampoline    core 3.0 (GC + tail calls)
```

The finding for this survey: **WasmGC is not merely "the host GC to delegate reclamation to" — the
managed GC `struct` frames ARE the general-resumption runtime.** ADR-0059 §Decision: continuations are
"managed `struct` frames linked by `.parent`, handler identity = the struct reference, raise/resume =
re-point a `.parent` field." So at the backend, "the heap" (WasmGC-managed frames) and "the control
representation" (the resumption chain) are **the same design** — the frames a GC collects are exactly
the frames a resumable handler walks. And because the whole lowering lands on core 3.0 features, the
runtime is **bang's own abstract machine with no opaque primitive in the TCB** (invariant #1; the
machine-checked `CtxRel`/`SegRel` relation, ADR-0059 §Context, Lean 4.31 axiom-clean per-step).

**The load-bearing v1 sharpening (shown, ADR-0059 §"The v1/post-v1 boundary"):** v1 does not need the
GC-frame runtime *at all*. bang's three handler forms (`state`, `throws`, `transaction` —
machine-confirmed exhaustive, `Core.lean:120`) are all abort- or tail-resumptive (ADR-0025 closed-focus,
one-shot in-place, no reification). So **v1's backend is just `throws`→exception + `state`/`transaction`
→tail-call** — the engine-independent half, on stock Wasm 3.0, with no hand-built GC-machine. The
GC-frame general leg is the **post-v1 ADR-0015 multishot frontier**; its per-step relation is
axiom-clean but the cross-step store-preservation lemma is **unbuilt** (ADR-0059 open sub-clause, task
#36 — do not cite the general leg as "verified" full stop until it lands). For the *memory* story this
matters: v1's heap discipline is the closed-focus stack (§2) plus host RC; the GC-managed resumption
heap is a post-v1 concern that arrives *with* multishot, not before.

### 3.2 R1 — Perceus reference-counting-with-reuse (v1.x)

The v1.x rung is **Perceus** (Reinking, Xie, de Moura, Leijen — "Perceus: Garbage-Free Reference
Counting with Reuse"): precise RC that emits reference-count instructions such that cycle-free programs
are *garbage-free*, plus **reuse analysis** that turns a freed-then-allocated pair into a guaranteed
in-place update ("functional but in-place", FBIP). **The existence proof is in bang's own toolchain:
Lean 4's runtime *is* a Perceus implementation** (de Moura is a co-author; Koka is the reference
implementation). So R1 is not research — it is a shipped, formalized technique (Reinking et al. give a
linear-resource-calculus formalization and prove soundness + garbage-freedom).

The bang-specific angle: **Perceus's reuse is exactly what the U grade licenses** (§2.2). Perceus infers
single-use to fire in-place reuse; bang's grade-1 binders *carry that single-use as a type*. So bang's
RC+reuse rung has a soundness carrier the general Perceus setting infers dynamically — the reuse is
sound *by the grade*, not by a separate borrow/uniqueness inference. **Suggests** (the U axis is the
linearity grade; Perceus reuse = single-use in-place): bang could drive Perceus-style reuse from the
grade rather than re-deriving uniqueness, folding two mechanisms into one (invariant #1). This is an
ADR-input, not a decision — the grade→reuse lowering is unspecified and would need its own ADR.

### 3.3 R2 — regions as handler scopes (post-v1)

The post-v1 rung is **regions**, and bang gets the region *stack* for free: a handler already delimits a
LIFO dynamic extent (install…pop), which is exactly Tofte–Talpin's region stack (r1-before-r2 ⟹
r2-freed-before-r1). So **a handler scope is an arena; values allocated under it die when it pops; the
pop is the region free.** This is os-inspiration-survey §7's ADR-INPUT verbatim (`:398-432`):

> *"a handler already delimits a stack-disciplined dynamic extent (install…pop, LIFO, exactly a region
> stack). So handler-scoped arenas are the natural home for region memory … But this is **not a kernel
> primitive** … lifetime/region is a candidate GRADE AXIS."* (os-inspiration `:406-411`.)

Region memory is thus the **R axis of the grade family** (kernel-substrate-survey §2a `:240`:
*"regions / space (R) … Tofte–Talpin … regions ARE effects"*) — a coeffect the type system tracks,
licensing arena allocation, on the *same* GradeVec machinery as rows, multiplicity, and IFC (different
lattice, same fold-on-composition). **Shown** (both surveys carry this as a pinned ADR-INPUT; Tofte–Talpin
is already in `refs.bib` as `tofte-ic97-region-memory`): regions are post-v1, a grade axis, **not** a
sixth primitive — invariant #5 holds. The sequencing (R0 now, R1 at v1.x, R2 post-v1) is invariant #7's
"don't optimize speculatively" applied to reclamation: each rung ships when the language needs it and
can prove it sound.

---

## 4 · The load-bearing claim, tested hardest: cap-escape ≈ region-escape

The task asks the hardest question: bang's `escapedCap` machinery (ADR-0063) already detects "a closure
outlived its scope" — **how far does it generalize to region-escape detection?** I verified the escape
machinery against the code and the ADR, and the honest verdict is a **partial refinement, not a clean
isomorphism**. What carries over is real and load-bearing; what does not is precise and matters.

### 4.1 What cap-escape actually is (the code)

A capability `vcap n ℓ` names a specific handler instance by identity `n` (glossary: typing-by-label,
dispatch-by-identity). Capabilities are first-class values, so they can be captured into thunks and
forced *after* their handler has popped. When that happens, dispatch finds no matching handler:

```
-- Dispatch.lean:182 (custom arm) / the idDispatch = none path (ADR-0063 §Decision step 1)
| none => none   -- no handler of identity n on the stack ⟹ idDispatch = none ⟹ Result.escapedCap
```

ADR-0063's move: reclassify this from `.stuck` to a **defined terminal `.escapedCap`** (like OCaml 5's
`Effect.Unhandled`, Koka's `final`). The witness `progComp` (`ReturnEscapeReach.lean`) is a typeable,
axiom-clean program that launders a `state` handler's cap into a returned thunk via an inner re-handle
of the same label, then forces it past the handler ⟹ `.escapedCap`. **Shown** (ADR-0063 §Context, the
committed regression witnesses `68c44e0`/`bce2093`): the escape is real, operational, and *detected* —
the kernel fails loud, never corrupts.

### 4.2 What carries over to region-escape (the real analogy)

Three things transfer, and they are the *hard* parts of region safety:

```
  region-escape problem              cap-escape machinery that addresses it        transfer
  ────────────────────────────────   ────────────────────────────────────────────  ────────
  "a value outlived the scope         escapedCap: dispatch-by-identity to a popped   STRONG — same
   (region/handler) that owns it"      handler = use-after-region-free               shape of bug
  detecting it as a DEFINED outcome    .escapedCap terminal (≠ stuck), fail-loud     STRONG — the
   rather than UB                      (ADR-0063 §Decision)                          fail-loud model
  the STRUCTURAL fix is scoped types   ADR-0063 §post-v1: scoped/region capability   STRONG — bang
   that make escape UNTYPEABLE          types making progComp untypeable             already names it
```

**Shown** (ADR-0063 §Consequences + §Alternatives): the *post-v1 goal* for cap-escape is literally
"scoped/region capability types (rank-2 / region polymorphism, the `runST` move) that make the escape
untypeable." That is **the same type-system technology as region typing** — the `runST` rank-2 trick is
Launchbury–Peyton-Jones's original region-escape prevention, and Tofte–Talpin region inference is its
inferred cousin. So the analogy is not loose: bang's cap-escape *structural fix* and region-escape
*prevention* are **the same construct** (scoped existential/rank-2 types), which is a genuine
"one construct per problem" (invariant #1) win — bang would build region-escape prevention and
cap-escape prevention with one type-system extension.

### 4.3 What does NOT carry over (the refinement — the finding)

The analogy breaks in two places, and both are load-bearing enough that calling it an isomorphism would
be a lie:

1. **A capability is a handler *selector*; a region holds *arbitrary data*.** `escapedCap` detects
   escape *at the dispatch site* — the moment a captured cap is `perform`ed to a dead handler
   (`idDispatch = none`, `Dispatch.lean:182`). That detection is **operation-triggered**: it fires
   because the cap is *used* to select a handler that is gone. A region-escaped *value* (an escaped
   `int`, pair, or closure) has no dispatch — it is just read. There is no `idDispatch = none` moment
   for a plain escaped datum, so the *runtime* detection mechanism does **not** generalize: escapedCap
   catches escape only for values that trigger a handler lookup. **Shown** (the escape path is
   specifically the `perform`-with-no-handler case, ADR-0063 §Decision step 1; a returned escaped
   `int` would simply be a value, never routed through `idDispatch`). Region safety needs the escape
   caught for *all* data, which is why the real region story is **static** (the type system), not a
   runtime terminal.

2. **Caps are per-handler-*instance* (identity `n`); regions scope *sets* of allocations.** The
   escapedCap machinery keys on a single fresh identity (`Dispatch.lean` `splitAtId … n`) — "does
   *this* handler instance still live?" Region-escape is about *lifetime containment* — "is every
   allocation in this value's transitive reach owned by a region still live?" That is a reachability
   property over a heap, not a single-identity lookup. The B-occ anti-escape premise (ADR-0092 `:43`,
   `¬ LabelOccurs ℓ A`) guards a *label* out of an answer type; it is precisely the guard that
   ADR-0063 showed is **incomplete** — it catches direct-perform escape but not laundered-via-re-handle
   escape (`liveCapsResolveC_returnEscape` is build-FALSE, `ReturnEscapeRefute.lean`). Region typing
   needs the *complete* containment property, which is exactly the harder theorem B-occ does not
   deliver.

### 4.4 The theorem-SHAPE mismatch — why the runtime detector cannot be promoted to the static guarantee

There is a deeper reason the runtime half of the analogy fails, beyond "caps select, data is read"
(§4.3): **the two mechanisms prove different *shapes* of theorem, and one shape cannot be lifted to the
other.** Region typing (Tofte–Talpin, `runST`) is a **static soundness** property — *ahead of any run*,
the type system guarantees "no allocation is ever read after its region is freed," a `∀`-over-executions
statement discharged once at type-check time. `escapedCap` is a **per-execution liveness/fail-loud**
property — *during a particular run*, if a specific captured cap is performed after its handler pops, the
kernel routes to a defined terminal instead of corrupting. Concretely, in bang's own statements:

```
  mechanism        theorem shape                             where discharged        quantifier
  ──────────────   ───────────────────────────────────────   ─────────────────────   ──────────────
  region typing    "no escaped value is EVER read"            type-check (once)       ∀ programs · ∀ runs
   (runST/T-T)      = STATIC SOUNDNESS
  escapedCap       "IF a cap escapes, THIS run fails loud     runtime (per fuel/run)  ∃ run · at a
   (ADR-0063)       (≠ stuck)" = type_safety's `≠ .stuck`      (Source.eval fuel c)     dispatch site
                    (Spec.lean:155) — a DEFINED-outcome claim
```

**Shown** (`Spec.lean:155`, `type_safety`): bang's escape guarantee is `∀ fuel, Source.eval fuel c ≠
Result.stuck` — a claim that *every run terminates in a defined outcome*, where an escape lands in the
defined `.escapedCap` rather than genuine `.stuck`. That is not the region-soundness statement ("the
escape never happens"); it is the *weaker, honest* statement bang ships for v1 ("if it happens it is
defined, not UB"). You cannot promote the second to the first by improving the runtime: the runtime only
ever sees one execution, at dispatch sites, after the fact. Making the escape *impossible* (the region
guarantee) is intrinsically a type-system job — which is exactly why ADR-0063 files the structural fix as
**post-v1 scoped-cap types**, not "a better `escapedCap`." So the runtime half of the analogy is not
merely narrow (§4.3) — it is the *wrong theorem shape*, and no amount of runtime engineering closes it.

### 4.5 The constructive half: what a region type system would have to prove (the B-occ strengthening)

The refutation is not the whole story — §4.2's type-level transfer is *constructive*, and bang's own
build-refuted lemma tells the region type system precisely what obligation it must discharge. The escape
witness `progComp` (`ReturnEscapeReach.lean`) launders a cap out of a `state` handler via an **inner
re-handle of the same label**: the re-handle discharges `ℓ` from the thunk's external type *by label*
(identity-blind), satisfying the answer-type B-occ premise (`¬ LabelOccurs ℓ A`, ADR-0092 `:43`), while a
live `cap ℓ` of a *different identity* rides inside the thunk (ADR-0063 §Context). So B-occ — a *label*
non-occurrence check — is provably **incomplete** (`liveCapsResolveC_returnEscape` is build-FALSE,
`ReturnEscapeRefute.lean`).

The lesson for region typing, stated as an obligation: **a sound scoped-cap / region type system must
track identity-containment, not just label non-occurrence.** The property B-occ approximates —
"no live cap in the answer references a popped handler" — is exactly Tofte–Talpin's region-containment
("every region in a value's type outlives the value's use"), and the witness shows the *label*
approximation is the leaky version. So the region-typing work inherits a **sharpened spec for free**: not
"strengthen B-occ" (still label-keyed, still leaky) but "re-index the escape guard by *identity/region*,"
which is the dispatch-by-identity principle (glossary) lifted from the runtime into the type system. This
is the genuine, code-grounded payoff of the type-level analogy: bang already has the counterexample that
pins down what region typing must prove, and it points at the same identity-keyed structure the kernel
already dispatches on. **Suggests** (the witness is build-sealed; the region-typing theorem is unbuilt):
the post-v1 scoped-cap system and a region system would share not just the *construct* (rank-2/scoped
types) but the *exact containment obligation* — one theorem, discharged once.

### 4.6 Verdict

> **cap-escape ≈ region-escape is TRUE for the type-system fix, FALSE for the runtime detector.** The
> *structural* endpoint is genuinely shared: bang's post-v1 "scoped/region capability types that make
> the escape untypeable" (ADR-0063) **is** region typing (the `runST` rank-2 move; Tofte–Talpin's
> inferred version) — one construct discharges both, a real invariant-#1 unification and a strong
> reason to build the scoped-cap type system with regions in view. But the *runtime* machinery
> (`.escapedCap`) is a **narrow special case**, not a general region-escape detector: it fires only at
> a dispatch site (`idDispatch = none`), so it catches escaped *capabilities* (which are used to select
> handlers) and **not** escaped *data* (which is merely read). And identity-keyed single-handler
> liveness is weaker than region reachability-containment — the very incompleteness ADR-0063 documented
> (B-occ guards a label, not the laundered escape) is the gap region typing must close completely.
> **So: adopt the analogy at the type level (build scoped-cap types AS region types — the payoff is
> real), reject it at the runtime level (escapedCap does not scale to a region-free detector — regions
> need static containment, per Tofte–Talpin).** This is a partial refutation, and it is the note's
> sharpest finding: the machinery that *looks* like it already solves region-escape solves only its
> capability-shaped corner, and the honest post-v1 path is the shared *type-system* fix, not a
> generalized runtime terminal.
>
> Two sharpenings the deepened analysis adds. **(a) The runtime half fails for a theorem-shape reason,
> not just a coverage reason (§4.4):** region typing is *static soundness* (`∀ runs`, escape never
> happens), `escapedCap` is *per-run fail-loud* (`∀ fuel, Source.eval ≠ .stuck`, `Spec.lean:155`) — a
> defined-outcome claim caught after the fact at a dispatch site. No runtime improvement lifts the second
> to the first; making the escape *impossible* is intrinsically a type-check-time job (which is why
> ADR-0063 files the fix as post-v1 *types*, not a better terminal). **(b) The type-level transfer is
> constructive, and bang already owns the counterexample that specs it (§4.5):** the build-refuted
> `liveCapsResolveC_returnEscape` proves B-occ's *label* non-occurrence is the leaky approximation of
> region-containment; the region type system's obligation is therefore to re-index the escape guard by
> **identity/region** (dispatch-by-identity lifted into the type system), not to strengthen a still-leaky
> label check. So the type-level analogy delivers more than a shared construct — it hands the region work
> a **pre-refuted spec** and points at the exact identity-keyed containment the kernel already dispatches
> on. Net: reject the runtime analogy (wrong theorem shape), adopt the type-level analogy (shared
> construct *and* shared, already-pinned containment obligation).

---

## 5 · Summary — the ADR-inputs, cost-tiered

Per invariant #7's sequencing and the ADR-input posture (present, don't decide):

| # | ADR-input | rung / when | rides | ADR touchpoint |
|---|---|---|---|---|
| **M1** | **Mutable user-handlers = D5 param-update** — the `state`-arm swap (`Dispatch.lean:137`) generalized to the `custom` arm; not new semantics | **v1.x** (gated on Q27 answer-grade) | existing reinstall mechanism | ADR-0092 D5 (extend D3 with pair-return) |
| **M2** | **Shared state = TVar-in-transaction** (v1); privileged shared heap post-v1 | **v1 landed / post-v1** | ADR-0030 handler-STM | ADR-0030 §Revisit-if (concurrency) |
| **M3** | **The U grade is the memory policy dial** (0=erase, 1=in-place, ω=share); close `zero_usage_erasable` to make the 0-rung a theorem | **v1** (proof pending `lr_fundamental`) | GradeVec, laws-taxonomy §5 | Spec.lean:164 (the open sorry) |
| **M4** | **Backend = Wasm 3.0, grade-directed** (ADR-0059) — at the `general` slot the WasmGC frame-chain IS the resumption runtime (heap = control representation); no opaque WasmFX `switch` in the TCB; v1 needs only abort→exn + tail→call (closed-focus), no GC-machine | **now (R0)** | ADR-0059 two-hop refinement | ADR-0059 (WasmFX = post-standardization fast-path for `general` only) |
| **M5** | **RC+reuse = Perceus, driven by the U grade** — Lean4's runtime is the existence proof; reuse rides single-use grades | **v1.x (R1)** | U axis (§2.2) | future ADR (grade→reuse lowering) |
| **M6** | **Regions = handler scopes = the R grade axis** — handler pop is the region free; NOT a sixth primitive | **post-v1 (R2)** | os-inspiration §7, laws-taxonomy §5 | future ADR when grade axes ship |
| **M7** | **Scoped-cap types = region types** (§4 verdict) — build the post-v1 cap-escape fix AS region typing (`runST` rank-2); one construct, both problems | **post-v1 (research)** | ADR-0063 §post-v1 goal | reopened #50 + a region-typing ADR |

The through-line: **bang has no memory subsystem because CBPV + the grade family already is one.** The
stack/heap seam is the value/computation split (closures are the only escapers, `EnvMachine.lean:81`);
the policy dial is the usage grade (`IR.lean:221`); reclamation climbs host-GC → Perceus → regions
without a kernel change (each rung is a grade the type system already knows how to carry); and the one
seam-crossing hazard — a capability outliving its handler — is already a defined fail-loud, whose
*structural* fix (§4) is the same scoped-type technology as region-escape prevention. The single honest
caveat is the open `zero_usage_erasable` proof (M3): the erasure dial is real in the type and pending in
the proof.

---

## References

External sources (added to `references/refs.bib` where new):

- **Plotkin & Pretnar**, "Handlers of Algebraic Effects", ESOP 2009 — the `get`/`put`-as-handler-
  operations model that §1 grounds parameter-passing state on. Already cited via ADR-0025's reference
  line (Plotkin–Pretnar / Bauer–Pretnar).
- **Tofte & Talpin**, "Region-Based Memory Management", Information and Computation 132(2), 1997
  (<https://doi.org/10.1006/inco.1996.2613>). Already in `refs.bib` as `tofte-ic97-region-memory` — the
  R grade axis; regions ARE effects; the handler-scope-as-region-stack (§3.3) and the region-typing
  half of the §4 verdict.
- **Reinking, Xie, de Moura, Leijen**, "Perceus: Garbage-Free Reference Counting with Reuse", PLDI 2021
  (MSR-TR-2020-42; <https://xnning.github.io/papers/perceus.pdf>). NEW → `refs.bib` as
  `reinking-pldi21-perceus`. The R1 rung (§3.2): precise RC + reuse analysis (FBIP), formalized in a
  linear resource calculus, sound + garbage-free; Koka reference impl, Lean 4 runtime as bang's
  in-tree existence proof.
- **Phipps-Costin, Rossberg, Guha, Leijen, Hillerström, Sivaramakrishnan, Pretnar, Lindley**,
  "Continuing WebAssembly with Effect Handlers", OOPSLA'23 (<https://doi.org/10.1145/3622814>;
  <https://kcsrk.info/papers/wasmfx_oopsla23.pdf>; wasmfx.dev). NEW → `refs.bib` as
  `wasmfx-oopsla23`. WasmFX = the typed-continuations proposal; per ADR-0059 it is **not** bang's
  primary target (stock-engine-absent, and a `switch` primitive in the TCB — Iris-WasmFX found a real
  suspend-translation bug), only the post-standardization **fast-path for the `general` slot** (§3.1).
- **WebAssembly 3.0** — the actual backend target (ADR-0059). The Sept 2025 standard folds GC (managed
  `struct`/`array`, typed refs), exception handling, tail calls, memory64, and SIMD into **core Wasm**
  — so they are not separate proposals and there is no coexistence/compatibility question (§3.1). NEW →
  `refs.bib` as `wasm3-standard`. §3.1: bang's grade-directed lowering maps each grade to a core 3.0
  feature (exceptions=abort, tail calls=trampoline, GC structs=frame chain); the design ruling lives in
  ADR-0059, verified against it, not the web.
- **Launchbury & Peyton Jones**, "Lazy Functional State Threads", PLDI 1994 — the `runST` rank-2
  region-escape trick that ADR-0063's post-v1 scoped-cap fix is an instance of (§4.2). NEW →
  `refs.bib` as `launchbury-pldi94-runst`.

Internal anchors:

- **ADR-0025** (resumptive state handler — the `get`/`put` threading §1.1 cites), **ADR-0030**
  (STM-as-transactional-handler — TVars, the §1.3 shared-state escalation), **ADR-0063**
  (escapedCap defined fail-loud — the §4 machinery), **ADR-0092** (D5 param-update deferral — the §1.2
  mutability surface slice), **ADR-0094** (env machine — the §2.1 stack/heap split), **ADR-0059**
  (grade-directed Wasm 3.0 backend — the §3.1 target: WasmGC frame-chain = heap = general-resumption
  runtime; WasmFX is the post-standardization fast-path for `general` only; refines ADR-0016's
  WasmFX-primary target).
- **Code**: `Bang/Core/Semantics/Dispatch.lean:133-182` (the state/transaction/custom dispatch arms —
  the carried-value replace + the read-only-param reinstall + the escapedCap none-path);
  `Bang/Backend/EnvMachine.lean:77-121` (MVal/MEnv/evalV — closures = the only escapers);
  `Bang/Core/IR.lean:221-241` (the `Mult` grade in VTy/CTy); `Bang/Spec.lean:164-187`
  (`zero_usage_erasable` — the 0-rung theorem, body currently `sorry`).
- **Sibling surveys**: `docs/notes/os-inspiration-survey.md` §7 (regions-as-handler-scopes, the R-axis
  ADR-INPUT), `docs/notes/kernel-substrate-survey.md` §2a (the grade family, U as the linearity axis,
  R as the region axis), `docs/notes/laws-taxonomy.md` §5 (grade-axis admissibility — how a region
  lattice becomes a legal grade).
- **Banked S0 evidence**: `docs/notes/allocator-tracer-probe.md` (structured arena state fits;
  effect-free computed update envelope is the shared allocator/CALM follow-on door).
- **Invariants**: #3 (STM privilege is concurrency-only), #5 (five primitives — regions are a grade,
  not a sixth), #7 (performance second-class — the R0→R1→R2 sequencing), #1 (one construct per problem
  — scoped-cap types = region types, §4).
