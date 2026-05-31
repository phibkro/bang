# bang-effectrow-oracle

A verified **specification + oracle** for bang-lang's effect-row algebra, plus a
**differential test harness** that drives your Effect TS transpiler's row
unifier against it. Prove the small, slow-changing core; ship the language in
Effect TS; keep them honest by differential testing.

There are **two interchangeable oracles** behind the same JSON-over-a-pipe
protocol. The harness doesn't care which one it talks to.

- **`oracle-lean/`  (Lean 4 + Mathlib) — recommended.** Best agent-fluency in
  the proof-language family, more stable proofs than SMT, compiles to a native
  binary directly, and Mathlib hands you the algebra.
- **`oracle/`  (F* → OCaml) — alternate.** SMT auto-discharges the arithmetic
  lemmas with less manual proof; first-class OCaml extraction.

## The model

Effect rows are **idempotent sets of labels with an optional polymorphic tail**.
Union is the semilattice join (idempotent, commutative, associative, empty
identity) — the monoid tier of the Trinity framing, and the algebra Effect TS's
`R`/`E` channels actually obey.

## Why the Lean version is shorter than the F* one

Modeling the label set as Mathlib's `Finset` collapses two things that were real
work in F*:

- **`canon_unique` is free.** It was the keystone lemma in F* (extensional
  equality ⇒ syntactic equality on the canonical form). For `Finset` that IS the
  definition of equality — `Finset.ext`. One line.
- **The semilattice laws are inherited, not proved.** `Finset Label` already has
  the `Lattice` and `OrderBot` instances (`· ∪ ·` is `⊔`, `∅` is `⊥`), so
  commutativity / associativity / idempotence / identity come straight off
  Mathlib. `EffectRow.lean` shows `example : Lattice RowC := inferInstance`.

What you give up vs F*: you write the soundness proof more by hand (Lean's
tactics, not fire-and-forget SMT). `unify_sound` is **proven** — the proof needed
a freshness precondition (`fresh` not already a row's tail var; without it the
open/open case binds a cyclic `some fresh`), a real strengthening of the spec.

## Layout

```
oracle-lean/
  Bang/EffectRow.lean   # SPEC: Finset rows, unify, inherited laws, unify_sound
  Bang/Eval.lean        # SPEC: the definitional `eval` (ADR-0008) — K2 reference
  Bang/EvalJson.lean    # JSON codec for the eval op (harness glue)
  Main.lean             # native binary; ops: unify/union/canon/apply + eval
  lakefile.toml         # requires mathlib (rev must match lean-toolchain)
  lean-toolchain        # pinned Lean version
oracle/                 # the F* alternate (see oracle/src/Bang.EffectRow.fst)
harness/
  src/wire.ts           # Effect Schema wire types (parse-don't-validate edge)
  src/oracle-client.ts  # one long-lived oracle process, line in/out (unify + eval)
  src/transpiler.ts     # CODE UNDER TEST (unify) — swap in bang-lang's unifier
  src/rowalg.ts         # TS reference algebra + denotation comparison
  src/ast.ts            # BANG core AST builders (shared by goldens + candidate)
  src/eval-candidate.ts # CODE UNDER TEST (eval) — independent tree-walker
  test/effectrow.test.ts
  test/eval.test.ts     # eval goldens (candidate≡oracle≡expected) + pure-core fuzz
  test/eval-programs.ts # the golden core programs
tools/selfcheck.mjs     # zero-dep third implementation; the shared de-risk
flake.nix               # devShells.default = Lean; devShells.fstar = F*
```

## The `eval` oracle (the bigger oracle)

The same harness now also hosts a second, larger oracle: the **definitional
interpreter** `Bang/Eval.lean` (rep 2, toward keyframe **K2** — the VM the
Bahr–Hutton calculation derives *from*). A fuel-bounded, total free-monad
interpreter for the pinned core — thunk + `$` force, λ/application, `let`, ADTs +
match, one-shot `State`/`Throws` handlers — whose effect labels reuse the same
`Finset` row model. Driven over the same NDJSON pipe (`{"op":"eval",…}`) against
an **independent** TS candidate (`src/eval-candidate.ts`) on 10 golden programs
plus a pure-core fuzz. Shape & rationale: **ADR-0008**. The deferred edges
(multi-shot handlers, STM, `:`/`=` reactivity, divergence-beyond-fuel) are
documented `TODO`s in `Eval.lean`, never faked.

## Run it

No toolchain needed (validates the shared algorithm):

```bash
make selfcheck
```

Lean oracle, full pipeline:

```bash
nix develop                 # default = Lean shell (elan, node)
make check-lean             # selfcheck -> lake cache+build -> harness vs Lean
```

F* oracle instead:

```bash
nix develop .#fstar
make check
```

## Pinning note (the one Lean gotcha)

`oracle-lean/lean-toolchain` and the Mathlib `rev` in `lakefile.toml` **must
match**. Pinned here to `v4.29.0`. To re-pin to a Mathlib release tag, set the
toolchain from that tag's own file:

```bash
curl -sL https://raw.githubusercontent.com/leanprover-community/mathlib4/<tag>/lean-toolchain \
  -o oracle-lean/lean-toolchain
```

then set the same `<tag>` as `rev` in `lakefile.toml` and commit
`lake-manifest.json` so a fresh session resolves identical deps. `lake exe cache
get` downloads prebuilt Mathlib — without it the first build compiles Mathlib
from scratch (very slow).

## Two things worth internalizing

**The trust boundary is the adapters, not the core.** Compilation/extraction
erases the proofs: the verified core's guarantees are conditional on
preconditions the pragmatic shell must establish at runtime, which is why
`wire.ts` re-validates everything crossing the process edge.

**Sound, not principal.** The oracle proves `unify_sound` (if it says yes, the
rows really unify) — exactly what a judge needs. Most-generality (MGU) is
deferred to the differential test; ACI unification is finitary but not unitary.
`selfcheck.mjs` confirms soundness on 20k cases and confirms the harness catches
a planted open/open bug.

## Bonus differential check

You now have THREE implementations of the same algebra (Lean, F*/OCaml, the
zero-dep JS in `selfcheck.mjs`) plus the TS reference. Pointing the harness at
each oracle in turn, or diffing their JSON output on the same inputs, is free
extra cross-validation.

## Next rep

The definitional `eval` (rep 2) is now in place. **Next is the actual K2
keyframe: calculate the VM from it** — Bahr–Hutton-derive `(compile, Code, exec)`
so that `exec ∘ compile ≡ eval`, starting with the pure core (thunk/force/app)
and then swapping in the effect monad. The harness drives candidate machines
against `eval` the same way it drives the candidate evaluator now. (Effect-row
*inference* over an expression core — the other growth direction — folds in at
K4, on top of the verified unifier.)
