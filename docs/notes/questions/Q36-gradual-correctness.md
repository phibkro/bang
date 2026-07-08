---
type: design-question
title: "Gradual correctness / prototyping mode: typed holes, run-with-warnings, the coarse-vs-fine escape-hatch gap"
description: "surface + tooling; the vague-spec / exploratory end of the gradient"
status: open
area: type-system
ties: ["Q31", "Q35", "ADR-0026", "ADR-0073", "ADR-0067"]
see-also: ["#51", "#54"]
---
**Question**: how does bang support PROTOTYPING — a vague or absent spec, exploratory code — beyond
today's COARSE escape hatches? bang is a correctness-BY-CONSTRUCTION toolchain, which looks hostile to
prototyping; but the stratification principle (ADR-0026: verified core / tested superset / MARKED descent)
already makes correctness a GRADIENT, not a gate — prototyping is living in the tested-superset with the
verified core deferred. The question is the FINE-GRAINED hatches that make that mode ergonomic.

**Why it matters**: the irony is only apparent — a tool that FORCED a spec up front commits premature
rigor (the anti-pattern). The escape hatches COMPLETE the thesis ("correctness by construction WHERE IT
EARNS ITS PLACE, marked descent elsewhere"), they don't betray it. A vague spec is the LEFT END of the
gradient, and the point is that the gradient is walkable — you harden where the spec sharpens.

**The escape hatches that EXIST (gate → hatch, all MARKED = visible descent):**
- type-check-then-run (#51) → `--no-typecheck` (erase-and-run, the raw `Source.eval` oracle path).
- termination (#47) → **`Div`** — "couldn't prove it terminates" ⇒ run with FUEL, NOT rejected. THE
  standout: incompleteness-not-rejection, where bang beats Lean/Agda (which REJECT non-total) for
  exploration. A permissive default with an OPT-IN total fragment — the whole philosophy in miniature.
- effect declaration → rows are INFERRED; `! {ρ}` is opt-in ENFORCEMENT (no signature = no obligation).
- type annotations → OPTIONAL (HM infers; annotate only for higher-order / decidability, ADR-0075).
- the spec itself (`#guard`) → OPTIONAL (no guard = no checked behaviour; never FORCED to specify to run).

**The GAP (today's hatches are COARSE)**: `--no-typecheck` is ALL-OR-NOTHING — a prototyper wants to run
the GOOD parts while one corner is broken. Missing fine-grained hatches:
1. **Typed HOLES (`?`)** — a `?` that type-checks (accepts anything) and, if reached at runtime, is a
   DEFINED Outcome (NOT UB) — the prototyping-native "fill this in later." **Ties the Outcome-ADT
   assertion work directly** (a reached hole = a defined terminal, like `escapedCap`/`stuck`). bang has
   INTERNAL holes (HM unification vars) but no USER-FACING `?`. Lineage: Hazel (holes first-class).
2. **Run-with-errors-as-warnings** — run the well-typed parts, warn on the broken ones (gradual, not
   binary). Lineage: TypeScript (run-despite-errors).
3. **A `dynamic`/`Any` region** — opt a subtree into runtime-checked dynamism, harden it later. Lineage:
   gradual typing (Siek/Taha).

**Recommended**: **typed holes (`?`) FIRST** — smallest, highest-value, and it PAIRS with the Outcome-ADT
assertion layer already spiked (a hole is just another defined terminal). Run-with-warnings + a dynamic
region are further design space. Keep the DEFAULT strict (type-check-then-run, fail-loud — the correctness
posture per SOUL "surprising default = latent bug"); the hatches are EXPLICIT, so descent stays visible.

**Blocked on**: nothing hard for typed holes — a surface `?` + a `hole` Outcome terminal (the Outcome ADT
work is the natural pairing; both are surface/checker/CLI leaves, kernel untouched). The gradual/dynamic
region is a bigger type-system question (post-polymorphism).

**Revisit signal**: real prototyping friction (all-or-nothing `--no-typecheck` bites); OR the `?`-hole
terminal is added to the (now-built) `Outcome` layer; OR a gradual-typing direction is taken
up. Ties [[Q31 refinement types]] (the other end — MORE precision), ADR-0026 (stratification = the
gradient), ADR-0073/ADR-0067 (`Div` = the termination hatch), #51 (`--no-typecheck`), the Outcome-ADT
assertion work (the live `Outcome` layer, issue #54), [[Q35 force ergonomics]] (sibling surface-ergonomics fork).
