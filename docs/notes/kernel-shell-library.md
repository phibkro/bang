# Kernel / Shell / Library — the layering of bang-lang

> A framing to think *with*, not yet an ADR. Captures the three-tier model worked out 2026-06-25.
> Boundary #1 (dispatch) is OPEN pending the static-link spike (task #13). The "pivot to typed"
> direction is the operator's stated lean (2026-06-25), recorded here, not yet a committed decision.

## Two axes place everything

```
                    MACHINE-facing                       USER-facing
                    (executes · proven · VM-realizable   (composes · elaborates DOWN
                     · translatable to hardware)          to the machine)
  ───────────────────────────────────────────────────────────────────────────────────────
  blessed /         KERNEL                               SHELL
  definitional      the abstract machine                 the surface: syntax, paradigms,
                    (minimal instruction set)             dispatch policy, runtimes, the
                                                          rich type experience (analysis, errors)

  ordinary          —  (FFI / native, someday)           LIBRARY
                                                          ordinary code in the surface
```

- **Axis 1 — derivability:** irreducible → derived-but-blessed → ordinary.
- **Axis 2 — orientation:** machine-facing ↔ user-facing. The kernel **is** the abstract machine
  (the spec a VM realizes + translates to hardware); the shell is the human surface that elaborates
  *down onto* the machine. The kernel is the only machine-facing tier.

Three of the four cells are bang-lang today; the empty one is the future FFI/native slot.

## Two boundary tests sort everything

- **kernel ↓ shell = the derivability test.** "Can this be expressed over a smaller substrate?" If yes,
  it isn't kernel. (Exactly what the dispatch spike answers: is the *search* derivable over a static *link*?)
- **shell ↓ library = the definitional test.** "Is this part of what bang-lang *is* — shipped and blessed —
  or just code someone could write?" Shell is the blessed surface; library is ordinary code.

## This IS the two-hop architecture, named from the layering side

```
  source           ─►   graded-CBPV semantics   ─►   CalcVM        ─►   WasmFX / hardware
  (SHELL surface)        (KERNEL = abstract machine)   (the VM that       (translation to
                                                        REALIZES it)       hardware instructions)
  ╰─ user-facing ─────────╯╰──────────────────── machine-facing ────────────────────────────╯
```

"A VM runs this spec with a translation to hardware" *is* the `CalcVM → WasmFX` hop (ADR-0016). The kernel is
the abstract-machine layer; the shell elaborates onto it.

## First-cut map

```
KERNEL  (irreducible · proven · frozen · machine-facing)
  thunk · force ($)                        the deferral + the sole observation (ADR-0007)
  effect rows                              the set-semilattice effect algebra (ADR-0001)
  handlers as the STATIC perform→handler   ⟵ OPEN (spike): is the LINK the kernel, with the
    LINK                                      SEARCH demoted to a shell macro?
  STM (concurrent)                         the one privileged shared-heap primitive (#3, ADR-0030)
  graded-CBPV typing + Source.eval         the reference operational semantics (minimal kernel typing)
  the calculated VM (CalcVM)               executable spec
  → proven: type_safety · compile_correct · lr_sound · no_accidental (or structural under static)

SHELL  (derived · blessed · TESTED · user-facing · where composition + the type experience live)
  DYNAMIC dispatch                         ⟵ if spike GO = macro + reader-effect over static-link
  surface syntax + parser + ELABORATION    surface → kernel lowering (the tested artifact)
  the paradigm runtimes                    state · exceptions · async · reactive · actors
  the dispatch-policy knob                 dynamic-by-default ⟷ named/lexical (ADR-0044)
  the RICH type experience                 effect/capability types for ANALYSIS + ERROR MESSAGES
  the WasmFX compiler/backend              the verified bridge to the engine

LIBRARY  (ordinary · replaceable · typed-only · user-facing)
  data structures · collections · prelude · IO drivers · domain code · user-written handlers
```

## Typing has TWO faces (the "pivot to typed" insight)

Typing is not monolithic across the tiers — it serves different masters:

- **Kernel typing = minimal.** Just enough for soundness + the Bahr–Hutton calculation + (the pivot) to make
  the dispatch edge dissolve. The runtime VM stays untyped *at execution* (types erase); what gets typed is the
  *relation/analysis*, not the running machine.
- **Shell typing = rich.** Effect/capability types exist to serve the **user** — static program analysis,
  precise error messages, safe composition of paradigms. This is the user-facing payoff, and it's where most of
  a "typed pivot" actually lives.

**Direction (operator's lean, 2026-06-25, not yet an ADR):** pivot toward **typed**, coupled with **static**
dispatch — because the deep-research landscape (`dispatch-verification-landscape.md`) shows the *proven*
edge-dissolving approaches (Lexa, tunneling, Effekt) are exactly *typed + static*, and a typed relation simply
*has* the intermediate answer type the untyped LR cannot recover (dissolving ADR-0043's edge), while rich shell
types buy the analysis + error-message wins. The trade is relaxing invariant (3)'s "untyped oracle" *for the
relation/analysis* (the running VM stays untyped); watch the invariant-(2) set-vs-multiset tension the
canonical typed LR wants.

## Verification contract per tier

```
KERNEL    PROVEN     trusted-three; the abstract machine is correct + hardware-realizable
SHELL     TESTED     the elaboration surface→kernel preserves meaning (differential vs the kernel oracle)
LIBRARY   TYPED      the language's own type system; no extra proof
```

The minimal-kernel goal becomes operational: **push everything that passes the derivability test down into the
shell.** Dispatch is the first, highest-value test case.

## Open boundaries

1. **Dispatch: kernel or shell? — ANSWERED, GO (spike, task #13, 2026-06-25).** Build-gated verdict
   (spike `static-dispatch-spike` @ `b1330db` — in git history; landed as `Bang/Core/Semantics.lean`'s
   `staticSplit`/`perform cap`, lemmas `[propext, Quot.sound]`, 725 jobs
   green): a static-link kernel dispatch (`perform cap`, `staticSplit` — counts a de-Bruijn capability, **never
   calls `handlesOp` to decide skipping**) **dissolves the ADR-0043 edge structurally AND UNTYPED for cap=0**
   (the perform resolves to its NEAREST enclosing handler — the common, well-scoped case): the captured `Kᵢ` is
   `NoHandleF` (pure letF/appF plumbing), so there is no nested non-catching handler and no answer type to
   recover. For **cap>0** (resume-into-an-outer / shadowing) the strip RELOCATES but to a tractable place — it
   becomes **cap-indexed**, and the static count IS the answer-type witness (so it does NOT reintroduce the
   untyped-LR's missing recovery). Consequences confirmed: `no_accidental_handling` becomes **structural** at
   cap=0; the **calculated VM impact is LOW** (static dispatch is a *simpler* `splitAt` — Bahr–Hutton re-runs a
   strictly smaller obligation); **no 6th primitive** (`perform cap` REPLACES `up`+`splitAt`-search; the search
   moves to shell elaboration); frozen statements untouched (`dispatchOn` consumers unchanged). The
   dynamic-dispatch-as-shell-macro (Effekt-style capability threading, `perform name` → reader-effect lookup →
   `perform cap`) is the kernel↓shell derivability test passing. **Honest residue:** cap>0 needs either
   nearest-only caps (an expressivity cut — no resume-into-outer) or the typed cap-witness (the pivot's intent).
2. **How far does the typed pivot reach into the kernel?** — minimal kernel typing vs a fully typed relation;
   the set-vs-multiset (#2) question.
3. **Paradigm runtimes: shell or library?** — the definitional test; lean = a small blessed set in the shell.
4. **The compiler/WasmFX:** shell, or a distinct backend face of the machine-facing pole?

*Related: ADR-0016 (two-hop), ADR-0023/0024 (dispatch + no-accidental-handling), ADR-0043 (the edge),
ADR-0044 (dynamic vs lexical), `dispatch-verification-landscape.md` (the research).*
