# ADR-0103 · ∀-generalization for bound-free self-recursive generics: a call-site-monomorphization pre-pass (the List-family door)

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: A bound-free self-recursive generic (`length : List a -> Int`, the whole List family:
  `append`/`take`/`drop`/`zip`/`range`/`replicate`) is realized by the SAME elaborate-to-mono move as
  every other generic (ADR-0075/0079/0080/0082): a pre-`elabS` pass discovers the FINITE set of
  concrete instantiations from the program's call sites, and emits ONE monomorphic `let rec` residue
  per instantiation — exactly the two-residues-by-hand program of witness w3, auto-generated. The
  kernel / `Source.eval` / `HasCTy` / soundness NEVER see a `∀`, a tyvar, or a bound (invariant #4/#5
  hold, census byte-identical). The fork's TWO surface doors — (a) "real top-level ∀ for `let rec`
  ascriptions" and (b) "a bound-FREE bounded-fn" — collapse to the **same mechanism** (one construct
  per problem): both need call-site-driven monomorphization of an ARGUMENT-position tyvar; door (b)'s
  reuse-the-bounded-fn-seam framing is REFUTED (witness w2 — ADR-0080's `bfnWrapper` requires the
  carrier in RESULT position, the fold shape `… -> a`; the List family's carrier is in ARGUMENT
  position, `List a -> Int`). The honest MINIMAL door (c) — monomorphic prelude entries per base type
  (`lengthI`/`lengthB`/…) — is priced and rejected (combinatorial blowup, no genericity). Verdict:
  adopt the monomorphization-pre-pass framing (door a ≡ door b); defer implementation to its own
  spike; the surface spelling is a bound-free `let rec` ascription (`let rec length : List a -> Int`),
  no new `where` syntax.
- **Depends-on**: 0075, 0080, 0079, 0073, 0069
- **Relates-to**: #120 (the machine-traced wall this resolves), #105 (the 9-10/10 List-family residue
  it gates), Q26 (the generic lawful stdlib), R6 / `docs/notes/lambda-cube-ascent-survey.md` (the
  finiteness gate this lives inside), #55 (annotation-driven generic CONSTRUCTION — the append/zip
  half's residual dependency)

- **Status:** Proposed (kernel-engineer consult 2026-07-11; the OPERATOR ratifies — a type-power
  extension, invariant #4/#5 discipline)
- **Date:** 2026-07-11
- **Layer:** C + checker/elaborator (tested superset). Frontend LEAF (`Frontend/TypeCheck`, the
  elaborate-away seam); census byte-identical, kernel untouched. NO Spec.lean / Kernel change (a
  kernel change would be a REFUTATION finding — it is not needed; witnesses w0/w3 prove the residues
  already run).

## Context — the #120 wall (machine-traced, refute-first)

Every List-family prelude entry is a self-recursive function generic over the element type with NO
trait bound (`length : List a -> Int`, `append : List a -> List a -> List a`, …). The corpus has NO
such entry today — only monomorphic `List Int` recursion (nqueens, Prelude's `Str`-typed folds) and
NON-recursive generics (`mapOption`/`bimap`, which ride let-generalization). #120 traced two failure
modes; both are reproduced against the real binary in `witness-0103/`:

```
witness   program                                    observed (bang run / check, 2026-07-11)
───────   ────────────────────────────────────────   ──────────────────────────────────────────────
w0        let rec length : List Int -> Int  (mono)    2          — the RESIDUE; certifies TOTAL
w1        let rec length : List a  -> Int  (free a)   error: unknown type name 'a'   — THE WALL
w2        fn length(xs):List a->Int where Monoid a    error: … result type must be 'a' (fold shape)
w3        two mono residues (Int + Unit+Unit) in one  3          — the monomorphization TARGET
w4        non-rec `id` at two types (generalizes)     5          — why let-general can't be reused
```

**The wall is ONE line.** `w1` fails at `resolveTy env.gen env.aliases t env.effects` in the
`.letRecS` elaboration arm (`TypeCheck.lean:3033`): `resolveTyG`'s `.tName "a"` arm finds no σ-entry
(no type params bind at top level) and no `self?` match, so `resolveName` fails loud "unknown type
name 'a'". No construct introduces a free top-level `∀a`. Everything downstream — `structOK`/Div
certification, the `buildLetRec` μ-knot, the bidirectional checker — is INERT to the tyvar once it is
closed to a concrete type: witnessed by w0 (`length : List Int -> Int` type-checks, certifies total,
runs).

**Why `let rec` can't ride the let-generalization that non-recursive generics already use (w4, the
#120 "say precisely why" ask).** ADR-0075 bite-0b generalizes a let-bound THUNK's value type (the
`⑦b id` example — w4 runs `id` at two types). The obstacle for `let rec` is NOT the ascription
resolution alone; it is the SELF-KNOT. In the `.letRecS` arm the recursive name is bound in its own
body at a SINGLE fixed monomorphic thunk type `uT := .U botR (embC (ctyOf t'))` (`TypeCheck.lean:3034`),
and `buildLetRec` closes the μ-knot `Rec = μX. Thunk(X → T)` over a CONCRETE `t'`. Generalizing the
ascription would require the recursive CALL to instantiate the scheme at a fresh type — i.e.
**polymorphic recursion**, which is undecidable (the R6 §4 mono-instantiation wall: no finite
instantiation set by construction). But the List family is UNIFORM: `$length t` calls `length` at the
SAME `a` as the caller — **monomorphic recursion**, which monomorphization handles by construction.
So the barrier is "the self-knot is monomorphic", and the fix is to close the tyvar BEFORE building
the knot (once per call-site instantiation), never to generalize the knot itself.

## The fork, refuted both ways

**Door (a) — real top-level ∀ for `let rec` ascriptions.** Generalize the ascription's free tyvars
(close over the decl, HM-style). Falsifier outcomes:
- The checker's self-recursion seeding: a SCHEMATIC seed breaks the fixpoint (polymorphic recursion,
  above). REFUTED as stated — a genuine `∀`-scheme in the self-knot is undecidable.
- BUT: if "generalize" means "instantiate the scheme per call site and monomorphize each" (the
  elaborate-to-mono reading, NOT a residual `∀` in the knot), it is decidable and sound — this is the
  same monomorphization ADR-0075/0080 already run, applied to an argument-position tyvar. This
  reading SURVIVES.

**Door (b) — a bound-free bounded-fn** (`fn length(xs) : List a -> Int where a = …`, or `for a` /
bare `where a`). Falsifier outcomes:
- **The fold-shape wall (w2, DECISIVE).** ADR-0080's carrier-fixing is annotation-driven off the
  RESULT type: `bfnWrapper` (`TypeCheck.lean:2642`) requires the declared result to BE the bound var
  (`… -> a`). The List family's tyvar is in ARGUMENT position (`List a -> Int`, result `Int`). Even
  with a vacuous bound, the bounded-fn path rejects it (w2, observed on the real binary). So "reuse
  the bounded-fn seam, minus the dictionary" does NOT work — the seam's whole carrier-discovery
  assumes result-position, and the ops-splicing step (`env.rawImpls.find?`) has nothing to splice for
  a bound-free fn anyway. The dictionary is not the only thing to drop; the entire carrier-from-result
  mechanism is wrong for this family. REFUTED as a bounded-fn variant.
- The empty-dictionary question ("does the splice step become a no-op?"): moot — the splice step is
  reached only AFTER the fold-shape check passes, which it never does for `List a -> Int`.

**Same mechanism (one construct per problem).** Once door (b) is stripped of the bounded-fn framing,
what BOTH doors need is identical: **discover the finite instantiation set of an argument-position
tyvar from call sites, monomorphize the `let rec` per element.** Door (a) reaches it by
"generalize-then-instantiate-per-use"; door (b) by "bound-free fn monomorphized per use". These are
the same elaborate-to-mono pass with two surface spellings. Adopting BOTH surfaces would be two
constructs for one problem. **We adopt ONE:** the existing `let rec … : T = …` ascription form, with
`resolveTy` extended to admit free tyvars (closed by the monomorphization pre-pass), and NO new
`where`/`for`/`fn` syntax. Rationale: `let rec` is already the generic-recursion surface (ADR-0073);
the wall is purely that its ascription can't NAME a free tyvar. Fixing that one gap is minimal; adding
a parallel bound-free `fn` form is a second door onto the same room.

## Decision

1. **A call-site-monomorphization pre-pass** (structurally the `expandBFns` twin, ADR-0080): a pure
   fuel-bounded `Surf → Surf` rewrite running BEFORE `elabS`. For each bound-free generic `let rec`,
   collect the concrete types at which it is applied (the instantiation set), emit one specialized
   `let rec` residue per instantiation (`resolveTy`'s tyvar closed to that concrete type, then the
   existing `buildLetRec` μ-knot), and rewrite each call site to its residue. The kernel sees only the
   concrete residues (w0/w3 prove they run).
2. **Surface: the bound-free `let rec` ascription.** `let rec length : List a -> Int = …` — a free
   tyvar in the declared type is admitted; NO new syntax. `resolveTy`/`resolveTyG` gain a "collect
   free tyvars as generalizable" reading at the `.letRecS`/top-level-decl entry (the ONLY sites that
   may introduce a top-level scheme — every other `resolveTy` caller stays fail-loud on an unknown
   name, preserving the typo-catch).
3. **Instantiation discovery is annotation-anchored, finiteness-gated (R6).** v1 discovers the carrier
   from each call site's argument/annotation (the ADR-0079/0080 annotation discipline), computing a
   FINITE closed instantiation set. A call whose carrier is itself unresolved (a generic used inside
   another un-instantiated generic — polymorphic recursion / an unbounded set) is a LOUD error
   ("annotate the use" / "cannot monomorphize"), never a guess — the R6 finiteness gate as a fitness
   function, the type-system analog of `Div`.
4. **structOK/Div is inert (verified).** Certification runs AFTER monomorphization on ground residues
   (w0: `length : List Int -> Int` certifies TOTAL with no Div marker). No change to structOK.
5. **Kernel/Spec.lean UNTOUCHED.** No `∀` reaches the kernel; residues are ordinary monomorphic
   `let rec`s. This is the fifth elaborate-away win (after ADR-0075/0079/0080/0082); the census
   (18→20 headline theorems) does not move.

## Rejected / staged

- **Door (b) as a bounded-fn variant** (`where a` / `for a`). REFUTED by the fold-shape wall (w2):
  ADR-0080's carrier lives in result position; the List family's is in argument position. Not a
  syntax tweak — a different discovery mechanism. Rejected in favor of extending `let rec`.
- **A residual `∀`-scheme in the self-knot (naive door a).** Polymorphic recursion, undecidable
  (R6 §4). The monomorphize-per-call-site reading is adopted instead.
- **(c) Monomorphic prelude entries per base type** (`lengthI : List Int -> Int`,
  `lengthB : List (Unit+Unit) -> Int`, …). The "ugly-but-tomorrow" floor: it WORKS today (w0/w3 are
  literally this, by hand) but requires one hand-written entry per (function × base type) — a
  combinatorial blowup with no genericity, and it does not scale past `Int` to user data types. It is
  the fallback if the pre-pass slips, and the ground truth the pre-pass must reproduce — but not the
  ship target. Priced and rejected as the primary door.
- **A System F kernel** (carry the `∀` in `HasCTy`/the LR/soundness/CalcVM). Spine work, unnecessary —
  elaborate-to-mono is the standing architecture (ADR-0075). Rejected (invariant #4/#8).

## The sites-to-change map (for the implementing spike)

```
site                                            change
──────────────────────────────────────────     ─────────────────────────────────────────────────
TypeCheck.lean:3033 (.letRecS `resolveTy`)      the CHOKEPOINT: admit a free tyvar in the ascription
                                                (collect-as-generalizable), not fail-loud
resolveTyG/.tName arm (:1821-1828)              a new "free tyvar → generalizable marker" reading,
                                                gated to the top-level/`.letRecS` entry only
                                                (other callers unchanged — typo-catch preserved)
a new `monomorphizeLetRec` pre-pass             the `expandBFns` twin (:2698): discover the finite
                                                instantiation set from call sites, emit one
                                                `buildLetRec` residue per element, rewrite calls
elabProg wiring                                 run the pre-pass before `elabS` (as `expandBFns` runs)
genericPrelude / Prelude.bang (:3531)           the List family becomes expressible as bound-free
                                                `let rec` entries (the #105 payoff)
buildLetRec (:2347)                             UNCHANGED (each residue is a concrete `let rec`)
structOK / letRecRow (:2295)                    UNCHANGED (runs on ground residues, w0)
Kernel / Spec.lean / Core                       UNTOUCHED (no `∀`, invariant #4/#5)
```

## R6-consistency argument (the finiteness gate)

This lives entirely inside the elaborate-to-mono rung the R6 survey already priced. `length :
List a -> Int` is the F (∀) rung, which the survey records as SHIPPED via monomorphization
(`lambda-cube-ascent-survey.md` §1, the "won five times" line). A bound-free generic is STRICTLY
LESS demanding than a bounded one: no dictionary, no trait resolution, no impl lookup — just close a
tyvar. The instantiation set is discovered from call sites exactly as bounded-fn carriers are
(ADR-0080), and for the uniform (monomorphic-recursion) List family it is FINITE and CLOSED at
elaboration time — the §4 gate holds. The one place it could fail the gate is polymorphic recursion
(a self-call at a DIFFERENT type, growing the set unboundedly); that is caught loud by the finiteness
check (decision item 3), never monomorphized silently. Kernel untouched, census stable — the survey's
licence extends here conditional on the finiteness gate, exactly as it does for the bounded rung.

## What the List family costs once the door opens

The 9-10/10-universal List family (#105's final residue) becomes expressible as bound-free `let rec`
prelude entries. CONSUMING members (`length`/`take`/`drop`/`sum`) are unblocked immediately (w0/w3
prove the residues run + certify). CONSTRUCTING members that BUILD generic data in synth position
(`append`/`zip`/`range`/`replicate` returning `List a`) carry a RESIDUAL dependency on #55's
annotation-driven generic INTRODUCTION (ADR-0079/0081) — the same construction-side wall bounded fns
hit (ADR-0080's own deferral). w0's `List Int` construction runs because the annotation pins it; the
generic case needs #55's inference. So the door opens the CONSUMING List family in full and the
CONSTRUCTING half up to the #55 annotation boundary.

## Revisit if

Polymorphic recursion is genuinely needed (a self-call at a different type) — that pressures the
finiteness gate and is the R6 λ2/dependent frontier, its own K-ADR; OR annotation-free carrier
inference (#55) is taken up, unblocking the constructing half; OR a bound-free `fn` surface is
demanded independently of `let rec` (would reopen the one-construct-per-problem choice).
