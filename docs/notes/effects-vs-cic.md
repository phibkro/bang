<!-- note-status: active -->
# Effects vs the Calculus of (Inductive) Constructions — additive or derivative?

> The one-page answer to "are algebraic effects an extension of CIC or expressible inside
> it?", recorded because it names WHY bang's architecture has the shape it has, and it is
> the theoretical frame for the R6 lambda-cube-ascent rung (ROADMAP §Pre-v1 research ladder).
> Companion to `kernel-substrate-survey.md` (the profile ladder: cube axis × effect-row axis).

## The split

Both answers are true at different levels, and the level split is precise:

| | effects as DATA (free monad, ITrees) | effects as BEHAVIOR (real state/IO/divergence) |
|---|---|---|
| CIC status | **DERIVABLE** — an ordinary inductive type + folds | **ADDITIVE** — and if added carelessly (call/cc + strong Σ), **INCONSISTENT** |
| where in bang | the Lean kernel: `Comp`, effect rows, `Handler.custom`, `Source.eval` | the compiled Wasm artifact; **fuel** marks the seam inside the kernel |

**Derivative (as representation).** Inside CIC an effectful computation is an inductive
datatype: the free monad on a signature — `Comp A` as an operation tree, handlers as folds
(Plotkin–Power: the State monad = the free model of the state equations; modern CIC
incarnations: freer monads, interaction trees). **This repo is the existence proof**: the
kernel carries out exactly this derivation in Lean. "Programs are descriptions until forced"
(ADR-0007) is the encoding elevated to a language design — the description IS the free-monad
tree, and even forcing stays inside CIC as a pure fuel-bounded interpreter.

**Additive (as capability) — aggressively so.** CIC's judgmental computation is total and
pure. Two facts make behavioral effects foreign rather than merely missing:

1. **Divergence**: strong normalization is load-bearing for consistency. The Div fragment's
   fuel is the tax CIC charges; true divergence exists only past the compilation boundary.
   The stratification seam (total verified core / fuel-bounded superset) is the
   CIC-compatibility line drawn as a feature.
2. **Control effects poison the logic**: unrestricted effects as PRIMITIVES don't extend a
   dependent theory, they destroy it — Herbelin's paradox derives `False` from call/cc plus
   strong Σ-types. The quarantine (monadic encoding, or an effect ladder with a total base
   as in F*'s `Tot`/`Div`/`ST`) is mandatory, not stylistic.

## The synthesis is CBPV (why the kernel is graded CBPV, not an accident)

Levy's value/computation split is the discipline that lets the two axes compose: dependency
and substitution live in the VALUE fragment (where CIC-style reasoning is sound), effects
live in the COMPUTATION fragment (graded by the row), and `F`/`U` are the only doors between
them. Consequences:

- The cube axis and the effect-row axis are independent **at the base** — the polymorphism
  arc climbed to F-and-HKT over a ∀-free kernel without the rows caring (ADR-0075).
- They do **NOT freely commute at the top**: "a type depending on `net.fetch(1)`" is
  meaningless before the effect runs. CBPV's answer — dependency over values only, thunk
  what you must — is the stratified compromise **R6** probes; F*'s total-base effect ladder
  is the nearest existing system.
- Because the kernel side is pure CIC data, Lean can PROVE things about effectful programs
  without being able to RUN their effects. The separation is not a limitation — it is the
  mechanism that makes the verification possible.

## References

Plotkin & Power, *Notions of computation determine monads* (algebraic effects / free
models) · Plotkin & Pretnar, *Handlers of algebraic effects* (handlers as an ADDITION to
the calculus) · Levy, *Call-by-push-value* (the value/computation split) · Xia et al.,
*Interaction trees* (coinductive effect encodings in CIC) · Herbelin, *On the degeneracy of
Σ-types in presence of computational classical logic* (the inconsistency) · Swamy et al.,
F* (the `Tot`-base effect ladder). Local: `references/README.md` for held copies.
