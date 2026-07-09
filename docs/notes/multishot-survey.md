<!-- note-status: active -->
# Multi-shot resumption — empirical design inputs for the Q22 cap-rep fork

> Research lane (rq22), 2026-07-09. Empirical survey of what SHIPPED effect-handler systems chose for
> **resumption multiplicity** (one-shot vs multi-shot) and the **capability representation** (labelling
> vs closure) that choice forces — the design inputs for [Q22](questions/Q22-capability-representation-labelling-vs-closure.md)
> BEFORE the `Bang/Reify/CalcReify.lean` probe, so the probe tests the right hypotheses. Docs-only
> research; no production code. SoT for "what the field did about multi-shot and what it cost."
>
> Reads on top of, does not duplicate: Q22 (the fork), [Q27](questions/Q27-surfacing-the-grade-axis.md)
> (the grade axis / the operator's 0-1-ω channel), [ADR-0085](../decisions/0085-general-handler-coexist-one-shot-v1.md)
> (one-shot v1, multi-shot deferred).

## TL;DR (the one-sentence verdict)

**The evidence supports staying ONE-SHOT-plus-explicit-copy for the foreseeable future — this is not a
stopgap, it is where the field's best-engineered systems (OCaml 5, WasmFX) deliberately sit, and bang's
own ◊6 backend (WasmFX) makes multi-shot *impossible to do cheaply* regardless of the kernel choice.**
When multi-shot is eventually scoped, the probe's first job is not "labelling vs closure" but "can the
WasmFX backend clone a continuation at all" — the backend is the binding constraint, upstream of the
kernel rep fork. If multi-shot lands, the evidence points to a **hybrid** (Q22 option 3): keep labelling
for the one-shot majority, add a closure/reified-continuation rep *only* for a statically-marked
ω-channel (Q27) — the same stratification seam bang already runs everywhere else.

The three sharpest findings, and why each moves the decision, are in the last section.

---

## 1. The one-shot precedent — OCaml 5's deliberate choice (reconstructed)

OCaml 5 (2022) shipped effect handlers with **one-shot continuations** as a hard, deliberate restriction,
not a temporary limitation. The reasoning, reconstructed from the manual + the retrofitting paper +
the multicore design notes:

```
OCaml 5's four reasons for one-shot          what it buys                           what it gives up
────────────────────────────────────────────────────────────────────────────────────────────────────
1. no stack copying                          fiber context-switch is ~O(1)          re-entering a
   (a resumption is used ≤ once, so the       (just a stack-pointer swap), no        continuation
   captured fiber is never duplicated)        heap copy of the captured stack        (amb, generators-
                                                                                      via-effects)
2. linear-resource safety                    sockets/fds/locks obey their           patterns that WANT
   (double-resume would let a file-descr.     linear discipline "for free" — the     to fork a resource-
   or lock be used past its handler)          type system needn't track it           holding continuation
3. sound compiler optimizations              standard reasoning about mutable       nondeterminism
   (multi-shot + mutable refs breaks the      refs stays valid; the optimizer        exploiting refs
   equational rules the optimizer relies on)  is not blocked                         under multi-shot
4. sufficiency for the driving use-case      concurrency/async — the whole point    nothing the target
   (concurrency needs only one-shot)          of multicore OCaml — needs no more     use-case needed
```

**Deep vs Shallow (`Effect.Deep` / `Effect.Shallow`) is an ORTHOGONAL axis** — it is about whether the
handler re-installs itself on resume (deep) or must be re-established explicitly (shallow), NOT about
multiplicity. Both are one-shot in OCaml 5. bang's `dispatchOn` reinstalls `handleF n h` on every resume
(`Dispatch.lean:135–137`), so bang is a **deep, one-shot** handler system — the same corner OCaml chose.

**The recovery path OCaml documents for the lost patterns is EXPLICIT COPY**: if you genuinely need to
resume twice, you reify the needed state yourself (e.g. a snapshot / an explicit `clone`), paying the copy
only where you asked for it. This is exactly bang's "one-shot v1 + explicit-copy-later" road (ADR-0085 D2).

**Is one-shot + explicit-copy a real expressiveness LOSS, or free?** — the formal answer (Kobayashi–Kameyama,
APLAS 2025, `kobayashi-kameyama-aplas25-oneshot-expressiveness`): using Felleisen macro-expressiveness,
one-shot effect handlers and one-shot delimited control **can be macro-expressed by asymmetric coroutines,
but NOT vice versa** — there is a genuine expressiveness gap that one-shot control alone cannot cross
*locally* (without a global CPS/state transform). So "one-shot + copy" is not free syntactic sugar: the
copy is a real, non-macro cost you pay to buy back the ω patterns. This matters for bang because it means
the ω-channel, if it ships, is a genuinely different capability — which is precisely why Q27 wants it typed
(so the machine knows when it is empty and can pick the cheap rep).

---

## 2. Multi-shot implementations — what shipped, its rep, and what the copy cost

The systems that DO support multi-shot, and how:

```
system              rep of the continuation        multi-shot mechanism            copying cost / what broke
──────────────────────────────────────────────────────────────────────────────────────────────────────────
OCaml 5             one-shot fiber (linear)        NONE — one-shot only            n/a (excluded by design)
WasmFX (bang's      single-shot linear cont;       NONE currently; a future        n/a today; a `cont clone`
  ◊6 backend)         resume/cont.bind DESTROY it    `cont clone` instr. is the      would be a full stack copy
                      (trap on 2nd use)              only envisaged path             (defeats the refcount/no-GC win)
Koka / libmprompt   in-place growable gstack       mp_resume_multi + mp_resume_dup  a multi-shot resume must
  (Leijen)            (virtual-memory, address-      (ref-count a multi-shot          COPY the gstack fragment;
                      stable, never moved)           resumption; "use with care      README: "use with care in
                                                     with linear resources")         combination with linear
                                                                                      resources" — the OCaml risk
Racket              full first-class delimited      call/comp + composable           heap-allocated continuation;
                    control (call/cc, prompts)      prompts — unrestricted           general but the expensive
                                                     multi-shot                       default (no zero-copy path)
Eff / Effekt       closure / capability-passing    resumption is a first-class      Effekt's caps are 2nd-class
                    (the cap CAPTURES its handler   value; multi-shot = invoke it     (cannot be returned/stored),
                    + delimited context)            more than once                    so escape is prevented by
                                                                                      TYPING, not by fail-loud
GHC prim delim.     PrimOp continuation tokens      control0#/prompt# — the RTS      RTS-level; multi-shot needs
  control (I/O)      over the RTS stack              can capture a stack segment      an explicit stack copy
```

Two reps, two failure modes (this is the Q22 fork, seen across the field):

- **Labelling / search** (bang v1, classic op-based dispatch): the cap is a NAME resolved against the
  stack (`vcap n ℓ` + `splitAtId`). Escape is **fail-loud** (an escaped name → stuck, = bang's `NonEscape`
  theorem). Multi-shot is awkward: "the handler must still be on the stack" is false once you've returned
  past it. To multi-shot you must reify + copy the stack fragment (Koka's gstack copy, or a WasmFX
  `cont clone`).
- **Closure / capability-passing** (Eff, Effekt, evidence-passing): the cap CAPTURES its handler + delimited
  context, so re-invoking is a direct call with no search and multi-shot is natural (the closure kept its
  context). Escape is NOT fail-loud — a captured closure still runs after its handler returned, so escape
  must be prevented by TYPING (Effekt's second-class caps) or a separate validity check.

**The evidence-passing subtlety (Xie–Leijen ICFP'21, `xie-icfp21-generalized-evidence-passing`)**: evidence
passing was invented to kill the O(depth) *search* cost of labelling — it pushes an evidence vector down the
context so `perform` is an O(1) lookup. Crucially, this is a *performer-side* optimization and is
**orthogonal to multiplicity**: it makes the innermost handler cheap to FIND; it does not by itself make the
continuation cheap to COPY. Koka combines evidence passing (cheap find) with libmprompt's gstacks
(multi-shot copy when needed) — the two concerns are separable. This is the datum that lets bang keep
labelling *and* later add multi-shot: the search cost and the copy cost are independent axes.

---

## 3. The WasmFX constraint — the backend reality check (the binding constraint)

**This section is load-bearing: bang's ◊6 backend is WasmFX, and WasmFX forecloses cheap multi-shot at the
machine level, upstream of any kernel rep choice.**

From the WasmFX explainer (`wasmfx.dev/specs/explainer`) and the Wasmtime implementation
(`emrich-hillerstrom-continuing-stack-switching-wasmtime`), verbatim:

> "Continuations in this proposal are *single-shot* (aka *linear*), meaning that they must be invoked
> exactly once."

> "In order to ensure that continuations are one-shot, `resume`, `resume_throw`, and `cont.bind`
> **destructively modify** the continuation object such that any subsequent use of the same continuation
> object will result in a **trap**."

> "Some applications such as backtracking, probabilistic programming, and process duplication exploit
> *multi-shot* continuations, but none of the critical use cases require multi-shot continuations."

> "Nevertheless, it is natural to envisage a future iteration of this proposal that includes support for
> multi-shot continuations by way of a **continuation clone instruction**."

The consequences for bang, in order of decision-weight:

1. **The backend natively runs bang's one-shot v1 at ZERO copy cost.** WasmFX single-shot linear
   continuations + reference counting (no GC) is the *exact* shape of bang's deep one-shot handlers. The
   one-shot road is not just cheap in the kernel — it is what the target hardware/VM was designed for.
2. **The backend offers NO cheap multi-shot primitive.** Multi-shot requires a `cont clone` that does not
   exist in the current proposal, and whose whole point (a stack copy) *defeats* the refcount/no-GC win
   WasmFX was built around. So even a closure-rep kernel that wanted multi-shot would compile to an
   expensive backend path.
3. **The CalcReify probe's FIRST question is a backend question, not a kernel question.** "Labelling vs
   closure" is the kernel-side fork Q22 frames — but if the backend cannot clone a continuation cheaply,
   the machine design is constrained regardless. The probe should test the WasmFX `cont clone` story
   (does it exist yet; what does it cost) *before* committing to a kernel rep, because the backend is the
   binding constraint.

**The nearest published twin of bang's own CalcVM→WasmFX hop** is Lindley et al's ASFX→AsmFX
(`lindley-draft25-asmfx-handlers-all-the-way-down`): a handler calculus compiled to a register machine,
correctness by annotated simulation, bridging a **scope-based source dispatch and an address-based machine
dispatch** via a well-scoping invariant threaded through the simulation. That is bang's identity-vs-label
dispatch gap exactly. It is a one-shot story; extending it to multi-shot is not addressed — a second data
point that the verified-compilation frontier for multi-shot handlers is genuinely open.

---

## 4. The verification tax — what multi-shot costs the proof

The proof cost of multi-shot is measurable in the LR / separation-logic literature, and it is real:

```
proof artifact                    one-shot                          multi-shot
──────────────────────────────────────────────────────────────────────────────────────────────
bang's dispatch (Dispatch.lean)   reinstall handleF, resume Kᵢ      REIFY Kᵢ as a copyable value,
                                   IN PLACE (frame reinstall)        re-invoke it N times
binary LR (Biernacki POPL'18,     continuation-value relation       SAME relation, but must be
  handle-with-care)                closed under re-invoke ≤ 1×        closed under re-invoke ANY ×
                                                                      — the resumption is a first-class
                                                                      related VALUE surviving re-entry
Iris/Hazel sep-logic              deep-handler resumption rule       multi-shot is FUTURE WORK
  (devilhena-pottier POPL'21        (§4.2.3) guarded by a ⊲ later      (§8) — the Löb induction that
  §4.2.3)                            modality, discharged by Löb        closes the one-shot rule ONLY
                                     induction — and it closes ONLY     works because the deep handler
                                     BECAUSE the deep handler            reinstalls INSIDE the resumption;
                                     reinstalls inside the resumption   drop that and the guard is gone
```

The pattern is consistent across the field: **the one-shot proof closes precisely because the handler
reinstalls itself inside the resumption** (bang does exactly this — `dispatchOn` reinstalls `handleF n h`).
Multi-shot removes that structural crutch — the continuation becomes an independently-related value that must
survive re-entry with the store/heap framed correctly on each re-invoke. Even Hazel, the state-of-the-art
Iris separation logic under Affect / Iris-WasmFX, treats multi-shot as future work. So bang's proof-tax
prediction: multi-shot is not a "few more cases" additive ripple (the way ADR-0085's *one-shot* custom arm
was) — it re-opens the resumption relation in the binary LR (◊4), the single hardest theorem in the stack.

The linearity line (Tang et al POPL'24, `tang-popl24-soundly-handling-linearity`; POPL'26 modal effects,
`tang-popl26-rows-capabilities-modal-effects`) is the constructive counter-move: if you TYPE resumption
multiplicity, you can *soundly* mix linear and multi-shot resumptions — which is the bridge to Q27.

---

## 5. Grades — typing resumption multiplicity (the compiler seam)

The operator's Q27 thesis — declare the resumption grade (0/1/ω) and let the machine pick the cheap rep
when the ω-channel is empty — has direct precedent:

```
system      surface annotation        grade → compilation
─────────────────────────────────────────────────────────────────────────────────
Koka        fun / ctl / brk           tail-resumptive (fun) → in-place, no yield/resume cycle;
                                       general (ctl) → full multi-prompt capture (expensive)
Effekt      2nd-class handlers        caps can't escape → stack discipline, no heap closure
OCaml 5     (implicit) one-shot        one-shot fiber → O(1) switch, no copy
Ma et al    lexical handlers          zero residual overhead when continuation not captured;
  (OOPSLA'25)                          the tail/one-shot path emits plain call+return
```

**Koka's `fun`/`ctl` split is the operator's thesis already shipping**: a `fun` (tail-resumptive) clause
compiles to an in-place call with no continuation reification; only `ctl` (general) pays the multi-prompt
capture. Ma et al (`ma-oopsla25-zero-overhead-handlers`) measure this as literally zero overhead on the
non-captured path — for LEXICALLY-scoped handlers, which is bang's identity-dispatch semantics exactly
(cap names its lexically-enclosing handler). So the "empty ω-channel licenses the cheap rep" optimization
(Q27's compiler seam) is not a hypothesis — it is a measured, published technique.

**The Q27 unification the operator proposed holds up against the literature**: resumption grade = the QTT
grade of the continuation binder `k` (abort = `k` at 0, tail = `k` at 1, multi-shot = `k` at ω), checked by
the SAME rig that grades every other binding. Tang's linearity work is the proof that this is sound —
multiplicity-typed resumption is exactly what lets linear and multi-shot resumptions coexist without the
OCaml double-resume hazard. And the trichotomy stays inside invariant #2 (rows-as-sets): the grade lives
BESIDE the row (per-handler), never as a per-label row weight — the operator's own guard, and it matches
how Granule (the one graded+row neighbour) keeps coeffect and effect axes orthogonal.

---

## 6. ADR-INPUTS — what the CalcReify probe should test first, and the likely verdict-shape

**What the probe should test, in order (backend-first, because the backend is the binding constraint):**

1. **The WasmFX `cont clone` reality** (§3). Does the backend proposal have a clone instruction yet; if
   not, what is the cost model of the envisaged one? This gates everything — a kernel closure-rep that
   compiles to an expensive/absent backend clone is a false economy. Test this BEFORE the kernel fork.
2. **The one-shot machine at zero copy** (the safe rung). Confirm bang's deep one-shot dispatch compiles to
   WasmFX single-shot resume with no copy — the ADR-0085 v1 path — and that the ASFX/AsmFX-style
   scope-vs-address simulation (`lindley-draft25`) is the proof method (annotated simulation, not
   machine-mirrors-source). This is the near-certain-to-work baseline; bank it.
3. **The hybrid seam** (if/when ω is scoped). Test whether a statically-marked ω-channel (Q27) can select a
   reified-continuation rep for JUST that fragment while the one-shot majority stays labelling — the
   Koka `fun`/`ctl` split, ported. The spike's `splitAtId_rename` lemma (cap names unobservable → any
   injective allocator is correct) already proves the gensym discipline is provably-free if labelling is
   kept, so the hybrid keeps labelling's proof intact for the 0/1 channels.

**The fork's likely verdict-shape** (empirics-driven, not yet decided — that is CalcReify's job):

```
                          evidence pull                                          likely verdict
────────────────────────────────────────────────────────────────────────────────────────────────
stay one-shot + copy      OCaml 5 + WasmFX both deliberately here; the           STRONG default —
  (Q22 non-action)         backend makes multi-shot expensive regardless;         indefinitely viable,
                           one-shot proof closes (reinstall-inside-resume)         NOT a stopgap
full switch to closure     kills gensym+splitAtId, O(1) perform, natural          REJECT for v1 — loses
  (Q22 option 2)            multi-shot BUT: loses fail-loud escape (needs          the NonEscape theorem +
                           typing to replace NonEscape), heavier caps,             fails the WasmFX backend
                           and STILL hits the expensive WasmFX clone               (closure ≠ cheap clone)
hybrid: labelling for      the field's actual pattern (Koka fun/ctl, Effekt      LIKELY endgame IF ω is
  0/1, closure/reify for    2nd-class + libmprompt); keeps labelling's proof       scoped — the stratification
  a typed ω-channel         for the majority; ω-channel typed (Q27) so the         seam bang already runs;
  (Q22 option 3 + Q27)      machine picks the rep; empty ω = cheap path            gated on Q27 landing first
```

**The counterweight (name the fallback, per the pin discipline)**: the hybrid is a *hypothesis*, not a
foregone conclusion. Its risk is TWO reps + an explicit seam = more surface to verify, and the WasmFX clone
cost may make even the ω-channel too expensive to be worth exposing (in which case the verdict collapses back
to "one-shot + explicit user-level copy, forever" — a legitimate terminal answer, and the one the raw
evidence most supports today). The probe should bank the one-shot-at-zero-copy baseline (rung 2) as a
labelled fallback BEFORE attempting the hybrid, so a failed hybrid does not strand the machine design.

---

## The three sharpest findings

1. **The backend, not the kernel, is the binding constraint — and it says one-shot.** WasmFX (bang's own ◊6
   target) makes continuations single-shot by construction: `resume`/`cont.bind` destructively trap on reuse,
   multi-shot needs a not-yet-existing `cont clone` whose stack copy defeats the refcount/no-GC design.
   Q22 frames the fork as a *kernel* rep choice (labelling vs closure), but the CalcReify probe's first
   question is a *backend* question — a closure-rep kernel still compiles to an expensive/absent backend
   clone. The fork is downstream of a constraint the kernel doesn't control.

2. **One-shot + explicit-copy is where the best-engineered systems deliberately sit, and it is not free.**
   OCaml 5 chose one-shot for four independent reasons (no stack copy, linear-resource safety, sound
   ref-optimizations, sufficiency for concurrency); WasmFX chose it for the same. But Kobayashi–Kameyama
   (APLAS'25) prove a genuine expressiveness gap (one-shot control is macro-expressible by coroutines, not
   vice versa) — so the "explicit copy" is a real, non-macro cost buying back the ω patterns, which is
   exactly *why* Q27 wants the ω-channel typed: so the machine knows when it is empty.

3. **The operator's Q27 compiler-seam is already shipping elsewhere, and the verification tax confirms its
   value.** Koka's `fun`/`ctl` split and Ma et al's zero-overhead lexical handlers (OOPSLA'25) are the
   "empty-ω-channel → cheap rep" optimization measured in the wild, on lexically-scoped handlers = bang's
   identity dispatch. And the proof side agrees it is worth typing: the one-shot LR/sep-logic proof
   (Biernacki, Devilhena–Pottier) closes ONLY because the handler reinstalls inside the resumption — the
   exact structural crutch multi-shot removes — so a typed ω-channel lets bang confine that proof-tax to the
   fragment that actually needs it, instead of paying it globally.

**Verdict on the mission's headline question — does the evidence support staying one-shot-plus-explicit-copy
indefinitely?** Yes, for now, strongly. It is the deliberate choice of OCaml 5 and the forced choice of the
WasmFX backend, the one-shot proof closes cleanly, and multi-shot re-opens the hardest theorem in the stack.
Multi-shot becomes worth revisiting only when (a) a concrete ω use-case is scoped (generators, amb,
backtracking as a library goal) AND (b) WasmFX ships a `cont clone` with a tolerable cost — and even then the
evidence points to a typed hybrid (Q27), not a wholesale switch to closure caps.
