<!-- note-status: active -->
# Explainer series — the multi-sensory outline

> The multi-sensory-explainer deliverable (operator-posed 2026-07-11): for each of bang's 5 core
> mental models, ONE explainer with a visual metaphor · an interactive element · a 30-second
> short-form beat sheet · the R-note/example it mines. Ordered for a newcomer. Sibling:
> `copy-kit.md`. Docs-only.
>
> Grounding for FORM (prior art, §Form-costs): Bartosz Ciechanowski's interactive essays ·
> Rust ownership visualizations · Julia Evans (JVNS) zines · distill.pub. Grounding for CONTENT:
> the examples/ that already run each idea (cited per explainer) + the R-series surveys.

## The 5 mental models (the series spine)

```
 #  mental model                       one-line                                         drawn as
 ── ────────────────────────────────   ────────────────────────────────────────────    ──────────────────────
 E1 descriptions-until-forced ($)       a program is a recipe until you cook it          a sealed thunk you crack
 E2 paradigm = the effect row           a function's "kind" is the set of effects        a row of colored tags
                                          in its type                                      on the type signature
 E3 runtime = a handler you install     swap the machine under a fixed program           one program, machines
                                                                                           slotted underneath
 E4 verified-core / tested-superset      an explicit, marked seam: proof vs test          two-tone landscape,
    (the stratification)                                                                   a bright line between
 E5 deterministic-replay / handler-swap  same seed ⇒ byte-identical run; opt out of       a dice-roll you can
                                          determinism by swapping the scheduler            rewind and replay
```

## Newcomer order — and why

**E1 → E3 → E2 → E4 → E5.** (Note: NOT numeric order.)

1. **E1 (`$` / descriptions-until-forced)** first — it's the one idea every other rests on. Nothing
   else parses until "programs are descriptions" lands.
2. **E3 (runtime = handler)** second, not E2 — because the *payoff* (swap the machine) is more
   visceral than the *classifier* (the row). Show the magic trick before the theory behind it.
   `logger-silent` vs `logger-counting` is the same program with one clause changed — the perfect
   second beat.
3. **E2 (paradigm = the effect row)** third — now the reader has *seen* handlers swap, so "the row
   is the type-level record of which handlers a function needs" has something to attach to.
4. **E4 (stratification)** fourth — the trust story. Once they believe the mechanics, show them the
   verified/tested seam that makes it *safe*. This is also the copy-kit's headline wedge; the
   explainer is where "docs can't lie" gets *shown*.
5. **E5 (deterministic replay)** last — it's the most advanced *and* post-v1 (ADR-0101). Ends the
   series on the forward-looking hook (candidate-C tagline), honestly flagged as the roadmap.

Rationale: load-bearing primitive → payoff-before-theory → trust → frontier. Same shape Rust's
book uses (ownership *mechanics* before the borrow-checker *theory*).

---

## E1 · Descriptions until forced (`$`)

- **Visual metaphor:** a **sealed capsule** labeled with a recipe. A bare `name` is the sealed
  capsule — inert, passable, storable. `$name` **cracks it open** and the computation *happens*
  (evaluate-to-WHNF). Animate: dragging a sealed capsule around does nothing; the `$` is a crack
  that releases a puff of "the value". Contrast panel: a normal language *cooks as it reads*; bang
  *hands you the recipe* and cooks only at `$`.
- **Interactive element:** a two-pane toy. Left: an expression with several `$` sites the reader can
  toggle on/off. Right: an **evaluation-order trace** that lights up *only* the forced sub-terms, in
  order. Tweak which `$` fires → watch the trace change → see "un-forced = never ran". **Rung-1
  honest constraint:** back it with real rung-1 pure arithmetic on wasmtime (`emission-rung1-probe`)
  so the trace is *true*, not simulated; effects/handlers stay diagram-only until the playground
  climbs (`traction-survey.md` §5).
- **30-sec short-form beat sheet:**
  1. "Every value in this language is a *recipe*, not a dish." (capsule on screen)
  2. "Passing it around cooks nothing." (drag it — inert)
  3. "One symbol cooks it: `$`." (crack — puff)
  4. "So *when* things run is something you write down — not a mystery the runtime decides."
  5. hook: "That's the whole trick everything else is built on."
- **Mines:** `examples/state` (`state 0 in let c = {get}; z = put 5 in $c` — `{get}` is a sealed
  description, `$c` forces it); `PRD.md` §5 (the when/where axis); ADR-0007 (`$` = force, `!` =
  actor-send); glossary (thunk/force).

## E3 · Runtime = a handler you install

- **Visual metaphor:** **one program on a pedestal, interchangeable machines slotting underneath.**
  The program text never changes; the reader drags a *handler cartridge* into the slot and the
  **output changes**. The killer demo is real: `logger-silent` and `logger-counting` are the
  *identical* program `(logger.log(10)) + (logger.log(20)) + (logger.log(30))`, differing only in
  the handler clause (`log(msg) => 0` vs `=> 1`) → outputs `0` vs `3`. Draw the two cartridges,
  same socket, different number lights up.
- **Interactive element:** the **cartridge swapper**. Fixed program up top; a rack of handler
  cartridges (silent / counting; then the `stage-swap` test-vs-prod pair: `fetch(n) => n*10` vs
  `=> n+1`). Reader slots one → the answer recomputes. The "aha": *the runtime is a value you're
  holding in your hand.* (Rung-1 honest: these particular examples are ⊥-row arithmetic bodies, so
  they can genuinely run in the browser — verify before shipping, but this is the swap that's
  *demonstrable today*.)
- **30-sec short-form beat sheet:**
  1. "Same program. Watch the output." (program on pedestal, result `0`)
  2. "I didn't touch the code. I swapped the *runtime*." (slot the counting cartridge → `3`)
  3. "Logging, state-with-history vs fast-in-place, test-vs-prod — all just cartridges." (rack pans)
  4. hook: "The runtime isn't a property of the language. It's a value you install."
- **Mines:** `examples/logger-silent` + `examples/logger-counting` (the identical-program pair —
  *the* asset); `examples/stage-swap` (one logic thunk through test vs prod handlers);
  `examples/state` (event-store vs in-place is the PRD §6 headline handler-swap); `PRD.md` §2.

## E2 · Paradigm = the effect row

- **Visual metaphor:** **colored tags clipped onto a type signature.** A function's type ends in a
  `! { … }` row; each effect is a colored tag (State = blue, Throws = red, Div = grey). "What
  paradigm is this function?" = "read its tags." Compose two functions → the tag sets **union**
  (draw two tag-clusters merging, duplicates collapsing — because rows are *sets*, invariant #2).
  A pure function has *no tags* — the ⊥ row.
- **Interactive element:** a **row-composition sandbox**. Reader picks two functions from a palette
  (each with its tag-row shown); the tool draws the composite's row as the set-union, live. Toggle a
  handler *around* a call and watch its tag **discharge** (disappear from the row) — the visual proof
  that "installing a handler removes that effect from what's left to handle."
- **30-sec short-form beat sheet:**
  1. "In most languages, 'is this function pure? does it do IO?' is invisible." (plain signature)
  2. "Here it's written on the type." (tags clip on: `! {State, Throws}`)
  3. "Compose two functions — the tags just union." (two clusters merge)
  4. "Handle an effect — its tag falls off." (discharge animation → `! {State}`)
  5. hook: "'Paradigm' isn't a language mode. It's the set of tags in the row."
- **Mines:** `docs/reference/language.md` (the `T ! {throws, …}` row form — generated, real);
  `effect-algebra-survey.md` §1/§4 (effects = theories; the row = the λ2-analog, row-polymorphism);
  invariant #2 (rows are sets, union = join); `examples/dst-rounds-lcg` (`! {Div, Sched}` on the
  driver — a real multi-effect row).

## E4 · The verified-core / tested-superset seam (the stratification)

- **Visual metaphor:** a **two-tone landscape with a bright, labeled line across it.** Left half
  (solid ground, "PROVEN") = the kernel: thunks, effects, handlers, STM, the CalcVM. Right half
  (scaffolding, "TESTED") = the surface parser, runtime, the `Div` fragment. **The line is the
  effect row / the marked descent** — never blurred. Overlay the *docs* story: pull a doc example
  off the page, drop it onto the build → it turns into a green ✓ (or, if you edit it wrong, red ✗).
  *That's* "docs can't lie" made visible — the example is load-bearing, not decorative.
- **Interactive element:** a **"break the docs" challenge**. The reader edits a reference example in
  a box; a mock build gate re-runs the `#guard` and flips green→red the instant the claimed output
  no longer matches. The felt lesson: *the documentation is wired to the compiler; you cannot make
  it lie without turning the build red.* (Backable at rung-1 with the real gate on pure examples.)
- **30-sec short-form beat sheet:**
  1. "Two claims: 'verified' and 'well-tested.' Most languages blur them." (fog over the line)
  2. "Here the line is drawn *in the types*." (bright line snaps in: PROVEN | TESTED)
  3. "The proven core is small and machine-checked. The rest is tested against it." (pan both sides)
  4. "And the docs? Generated from the proven source. Every example is build-gated." (example → ✓)
  5. hook: "Try to make the docs lie. The build turns red. That's the whole pitch."
- **Mines:** CLAUDE.md (the stratification principle — the three-level table); `docs/reference/
  language.md` header (generated, `#guard`-gated); `stranger-test-1.md` ("the docs' superpower is
  build-gated examples"); `stranger-test-3.md` (~90 gated examples pass). This explainer *is* the
  copy-kit §1 wedge, shown.

## E5 · Deterministic replay / handler-swap (post-v1 — flagged)

- **Visual metaphor:** a **dice roll you can rewind.** A concurrent program's interleaving is a
  sequence of dice (the scheduler's `pick`s). Under the *seeded* scheduler, the dice are fixed by
  the seed → run it 10× → **byte-identical every time** (draw 10 identical tapes stacking exactly).
  Then **swap the scheduler cartridge** (callback to E3!) to the production one → the dice go random
  → the tapes diverge. Determinism is the *default*; nondeterminism is a cartridge you *choose*.
- **Interactive element:** a **seed dial + replay button**. Reader sets a seed, runs a toy
  two-replica delivery-order round (the `dst-rounds` shape), sees the interleaving; hits *replay* →
  identical. Change the seed → different-but-still-deterministic. Flip to "production scheduler" →
  each run differs. **Honesty flag on-screen:** "concurrency is post-v1 (ADR-0101); this is a
  simulation of the ratified design" — never present it as runnable-today (`copy-kit.md` §5).
- **30-sec short-form beat sheet:**
  1. "Concurrency bugs are hard because you can't reproduce them." (tapes diverging)
  2. "Here, the scheduler is seeded. Same seed, same run — byte for byte." (tapes stack, identical)
  3. "Replay a heisenbug as many times as you want." (replay → identical)
  4. "Want real nondeterminism? Swap the scheduler. It's just another handler." (cartridge swap)
  5. hook: "Deterministic by default. Nondeterministic on purpose."
- **Mines:** ADR-0101 G6 (deterministic replay is the default; the open replay-contract edge);
  `examples/dst-rounds-lcg` + `dst-rounds-const` (the swappable-scheduler shape, running today in
  Lean); `ndet-dst-design.md` (seeded stateless-seed-splitting); `wasm-concurrency-survey.md` §1.2
  (WASI-0.3 converged on scheduler-as-handler). **Post-v1 — the roadmap beat, not a shipped claim.**

---

## Form costs — prior art, and what each form costs to produce

| form | exemplar | strength | production cost | fits which explainer |
|---|---|---|---|---|
| **deep interactive essay** | Bartosz Ciechanowski (gears, GPS) | canonical scroll-driven WebGL/canvas sims; unmatched depth-per-scroll | **very high** (weeks each; bespoke canvas + physics/sim per piece) | E1, E3 (the flagship "runtime cartridge" essay — worth it once) |
| **focused concept viz** | Rust ownership / lifetime visualizations | one idea, one interaction, embedded in prose | **medium** (days; a small stateful widget) | E2 (row-union sandbox), E4 (break-the-docs) |
| **hand-drawn zine / comic** | Julia Evans (JVNS) zines | warmth, approachability, shareable single-image explainers | **low** (hours; the *clarity* is the work, not the tech) | the 30-sec shorts for ALL five; E1's capsule metaphor |
| **rigorous explorable** | distill.pub articles | publication-grade, cited, math-forward | **high** (needs real figures + review; academic register) | E4, E5 (the verification/replay story — matches the proof audience) |

**Production sequencing recommendation:** start with the **JVNS-zine-cost 30-sec shorts** for all
five (cheap, shareable, seed the series), plus the **one Ciechanowski-class flagship** on E3 (the
cartridge swapper — the most visceral, and its assets are *real today* via `logger-silent/counting`
+ `stage-swap`). The medium-cost concept vizzes (E2, E4) follow. E5's deep explorable waits for the
sim-scheduler to be runnable (don't build the distill-grade piece on a post-v1 feature yet).

Prior-art sources: [Bartosz Ciechanowski](https://ciechanow.ski/) · [Rust ownership
visualization / RustViz](https://rustviz.github.io/rustviz/) · [Julia Evans / Wizard
Zines](https://wizardzines.com/) · [distill.pub](https://distill.pub/).
