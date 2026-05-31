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
tactics, not fire-and-forget SMT). `unify_sound` ships as `sorry` with a proof
plan in the comment.

## Layout

```
oracle-lean/
  Bang/EffectRow.lean   # SPEC: Finset rows, unify, inherited laws, unify_sound
  Main.lean             # native binary, same NDJSON protocol as the F* oracle
  lakefile.toml         # requires mathlib (rev must match lean-toolchain)
  lean-toolchain        # pinned Lean version
oracle/                 # the F* alternate (see oracle/src/Bang.EffectRow.fst)
harness/
  src/wire.ts           # Effect Schema wire types (parse-don't-validate edge)
  src/oracle-client.ts  # one long-lived oracle process, line in/out
  src/transpiler.ts     # CODE UNDER TEST — swap in bang-lang's unifier
  src/rowalg.ts         # TS reference algebra + denotation comparison
  test/effectrow.test.ts
tools/selfcheck.mjs     # zero-dep third implementation; the shared de-risk
flake.nix               # devShells.default = Lean; devShells.fstar = F*
```

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

Grow the oracle from "row algebra" to "row algebra + effect inference for a tiny
expression core," so the differential test compares the transpiler's whole
inference pass against verified inference. Inference is constraint generation
plus this unifier, so the unifier is the thing to nail first.
