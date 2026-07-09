<!-- note-status: active -->
> **RULED (operator, 2026-07-09): §6's coverage fork = TOTAL-ONLY.** `#prove` on a Div-rowed
> law is a TYPE error — proof-eligibility is typed; Div laws stay on the fuzzed rung, visibly.
> The arm-C north-star (fuel-free via `Source.eval ↔ StepStar` adequacy) remains the later
> coverage extension. Ruled alongside: Q43-R1 (export-goal-with-sorry) is CARVED OUT of the
> post-v1 distribution axis — it may slot into v1.x as verification-ladder work.

# Proof export (Q43) — design survey: a bang `law` becomes a Lean proof goal, proved once, cached

> Successor to the Q43 sketch in `verification-ladder.md` ("The genuinely novel rung: proof
> export"). That note names the *idea*; this note designs the *pipeline* so the eventual ADR is a
> ruling, not a research cycle. Grounds: `Bang/Frontend/TypeCheck.lean`'s `lawInstancesOf`
> (the landed discovery seam), `Bang/Witness/LawTest.lean` (the landed runner), ADR-0076
> (content-addressing), `distributed-story.md` §2 rung 1 (certified CRDTs — the flagship consumer).
> Web citations live in §References at the bottom (NOT `refs.bib` — the manager wires the library at
> landing).

## 0 · The one-paragraph thesis

bang programs already elaborate into a Lean kernel (`Comp`) carrying a *verified* semantics
(`Source.eval`) — **no mainstream language has this seam.** So "types as propositions" does not
require making bang a proof assistant. A `law` is *fuzzed by default* (the landed `bang test` rung,
#60) and *provable on demand*: a `#prove` pragma exports the law's obligation as a **Lean goal about
the elaborated `Comp` term**, discharged in the host by an agent or human, cached content-addressed
on the term's hash (ADR-0076's Merkle machinery). One construct, two rigor levels, an explicit,
type-visible seam — the stratification principle (verified core / tested superset) surfaced *into
user programs*: **"your paradigm is your row; your rigor is your rung."** This survey confirms the
shape has strong prior art (QuickChick's `Dec` typeclass is the near-exact analog), fixes the
goal-shape fork, designs the cache, and names the smallest shippable rung.

---

## 1 · Prior art — the test-to-proof bridge landscape

The table maps each system onto the two axes that matter for Q43: **(i) is the checked object the
SAME artifact as the proved object** (the "one construct, two rigor levels" property), and **(ii)
what carries the proof** (a solver, a kernel, extraction).

| system | test→proof relation | proof carrier | what it teaches Q43 |
|---|---|---|---|
| **QuickChick** (Coq) | `Dec P` typeclass: a decidable prop is BOTH `Checkable` (fuzz) AND provable by reflection — *the same term* | Coq kernel (reflection) | **the near-exact analog** — one construct, two rigor levels, no TCB growth |
| **Plausible/SlimCheck** (Lean 4) | given a `theorem` statement, generates inputs to *refute* it; a survivor is not proved, just un-refuted | — (finds counterexamples only) | the *fuzz half* bang already has (#60); Q43 adds the proof half |
| **hs-to-coq / coq-of-ocaml** | shallow embedding: source becomes a Coq term; you prove *about the embedding* | Coq kernel | **shallow embedding ⇒ no TCB extension** — the trust keystone (§4) |
| **Creusot** (Rust) | deductive: annotate, translate to Why3, discharge with SMT | Why3 + SMT (Z3/…) | contracts as the spec unit; SMT enters the TCB |
| **Kani** (Rust) | bounded model checking of MIR via CBMC; *bounded*, not a proof | CBMC/SAT | bounded ≠ proved — a rung *below* Q43's proof rung, above fuzz |
| **F\*** | VCs discharged by Z3; dependent types + SMT | Z3 (large TCB) | the "SMT is fast but in the TCB" cost bang REFUSES (invariant: proof rides the reference) |
| **Unison** | (not test→proof) content-addressed defs; typecheck once, cache forever | — | **the cache design** (§3) — hash the term, never recompute |
| **"A Failed Proof Can Yield a Useful Test"** | the *inverse* arrow: proof-goal → test | — | contrast: Q43 goes test-artifact → proof-goal, not the reverse |

**The load-bearing finding.** QuickChick's `Dec (P : Prop)` is a thin wrapper over a decision
procedure; because a decidable prop is *both* `Checkable` and reflectable, the same `P` is fuzzed by
QuickChick and proved by `reflexivity`/reflection — no separate statement, no TCB growth beyond the
Coq kernel. **This is precisely the bang `law` → `#prove` relationship**: the law body already
elaborates to a runnable `Comp` that `bang test` fuzzes; `#prove` lifts that *same* `Comp` to a Lean
`Prop` the kernel checks. Q43 is not inventing a bridge — it is instantiating the QuickChick pattern
with bang's *own verified kernel* as the reflection target. That is the design's biggest de-risking
fact: the shape is known-good, and bang's seam (an elaborated term with a verified oracle) is
*stronger* than QuickChick's (which reflects into Coq's `bool`, not a verified language semantics).

**The anti-pattern to avoid** is the F\*/SMT posture: fast, automatic, but the solver (Z3, ~500
KLOC, documented soundness bugs) enters the TCB. bang invariant #1 ("proof rides the reference") and
the axiom-gate discipline (`#print axioms` ⊆ {`propext`, `Classical.choice`, `Quot.sound`}) forbid
this by construction — a `#prove` obligation must close in the Lean *kernel*, not be delegated to an
oracle outside it. Automation (`decide`, `omega`, `simp`, an SMT-backed *tactic* whose output the
kernel re-checks) is fine; a solver whose *say-so* is trusted is not.

---

## 2 · The elaboration anchor — what is the GOAL SHAPE?

This is the section only the codebase can settle. The landed seam fixes every input:

### 2.1 · What a law elaborates to (the landed facts)

- `lawInstancesOf (src) : Except String (List (String × String × List String × String))` returns,
  per (trait-law × matching-impl) pair, `(traitName, lawName, params, body-as-source-text)`
  (`TypeCheck.lean:3570`). The body is **source text**, deliberately `Surf`/`Ty`-free.
- The landed *test* runner (`checkLawOn`, `TypeCheck.lean:3509`; and `LawTest.evalLawOn`,
  `LawTest.lean:334`) discharges one sample by the **truth-readback idiom**: bind each param to a
  value, wrap the Bool body as `let #r = body in if #r then 1 else 0`, elaborate → check → lower →
  `Source.eval 400`, and accept iff the result is `.done (.vint 1)`.
- `Source.eval (fuel : Nat) (c : Comp) : Result Val` (`Eval.lean:231`), where
  `Result` = `.done α | .oom | .escapedCap | .stuck` (`Eval.lean:38`). It is **fuel-bounded**:
  `Div`-fragment laws (`let rec`) can `.oom`; total-fragment laws always reach `.done`.

So a law of `k` params is, semantically, a **`k`-ary predicate reified as a `Comp`** that evaluates
to `vint 1` (true) or `vint 0` (false) under `Source.eval`, with `.oom`/`.stuck`/`.escapedCap` as
the "didn't even evaluate to a Bool" failure modes the runner's `LawOutcome` already distinguishes
(`LawTest.lean:361`).

### 2.2 · The goal-shape fork

The proof obligation must say "for ALL inputs, the readback is `true`". The elaborated body is a
*function of the param substitution*; write `bodyComp args` for the `Comp` obtained by substituting
generated arg values for the params (exactly `wrapLawBody`'s splice, `LawTest.lean:320`, but with
`Val`s not source strings). The fork is over how "eval terminates true for all args" is stated:

| arm | goal statement | price | verdict |
|---|---|---|---|
| **A · fuel-existential** | `∀ args, ∃ n, Source.eval n (bodyComp args) = .done (.vint 1)` | matches the runner exactly; but `∃ n` is awkward to discharge and lets a law "pass" that needs unbounded fuel (a `Div` law that happens to converge) | **rejected** — the existential hides non-termination; a law that needs growing fuel is not a *law* |
| **B · fuel-polymorphic (total laws)** | `∀ args, ∀ n ≥ N₀, Source.eval n (bodyComp args) = .done (.vint 1)` for a computed `N₀`, OR simply `∀ args, Source.eval N₀ (bodyComp args) = .done (.vint 1)` with `N₀` the total-fragment bound | for the **total fragment** (⊥-row, the CRDT laws' home) `N₀` is *structural* — a term with no `let rec` reaches WHNF in steps bounded by its size, so a fixed `N₀` suffices | **recommended for v1** — CRDT `merge` laws (comm/assoc/idem over finite ADTs) are total; a fixed-fuel equality is a decidable, kernel-checkable `Prop` |
| **C · eval-relation (fuel-free)** | `∀ args, Source.BigStep (bodyComp args) (.vint 1)` over the `StepStar`/big-step relation, no fuel at all | the *cleanest* statement — proves the law about the SEMANTICS, not an implementation detail (the fuel) | **the north star** — but needs a big-step/`StepStar`-termination bridge (`Eval.lean:111` `StepStar` exists; a `Source.eval n = .done v ↔ StepStar … (ret v)` adequacy lemma is the missing hop) |
| **D · equational** (for equational laws) | `∀ args, Source.eval N₀ (lhsComp args) = Source.eval N₀ (rhsComp args)` — equality of two `Comp` evaluations, not a Bool readback | needed for laws phrased as `lhs == rhs` where `==` is a *user* `eq` (e.g. `VecOps.eq`), whose result is `(Unit + Unit)`, not a decidable host equality | **subsumed by B** in v1 — the readback idiom already reifies `user-eq` to `vint 1`; a *separate* host-equality arm is a post-v1 refinement for laws over host-decidable types |

**Recommendation: v1 ships arm B (fixed-fuel readback = `.done (.vint 1)`), scoped to the total
fragment, with arm C named as the north star.** Rationale, three-fold:

1. **It rides the existing corpus verbatim.** The readback idiom (`let #r = body in if #r then 1 else
   0`) is *already* how `checkLawOn`/`evalLawOn` phrase truth; the proof goal is the *universally
   quantified* version of the exact proposition the fuzzer samples. Test and proof are then the same
   statement at two rigor levels — the QuickChick `Dec` property, realized. A law that `bang test`
   fuzzes green and `#prove` closes are provably about *one* `Comp`.
2. **The total-fragment scoping is the stratification seam, not a limitation.** The language-level
   seam (CLAUDE.md) is the effect row: total fragment (⊥-row) vs `Div` fragment. Q43's proof rung is
   *defined only on the total fragment* — a `Div`-rowed law (one whose body diverges for some input)
   is **structurally ineligible** for `#prove` and stays test-only. This makes "which laws can be
   proved" a *typed* property (read off the row), not a runtime discovery. Fail-loud by construction:
   `#prove` on a `Div`-rowed law is a *type* error, not a stuck proof.
3. **Arm C is a strictly-later, additive upgrade.** Once the `Source.eval ↔ StepStar` adequacy lemma
   lands (it is a natural kernel-lane deliverable, independent of Q43), the fixed-fuel goal B
   *implies* the fuel-free goal C for total terms — so shipping B first does not paint into a corner;
   C re-states the same theorem more abstractly.

**STOP-and-SHOW candidate flagged, not blocking:** whether v1 `#prove` should *also* cover the
`Div`-fragment via a **fuel-parametric** statement ("for all args and all fuel ≥ the fuel that made
`bang test` pass, …") is a genuine fork the operator may want to rule — it trades the clean
total/`Div` seam for broader coverage. My recommendation is to **keep the seam sharp** (total-only in
v1) because it makes eligibility *typed*; but this is a preference call (coverage vs seam-sharpness),
so it is named here rather than silently decided. See §6 ADR-INPUTS.

---

## 3 · Cache design — content-address on the elaborated term, not source text

ADR-0076 already pins the machinery ("IMMUTABILITY ⟹ content hash canonical + stable ⟹ Merkle-DAG
staleness ⟹ a silently-stale cache is UNREPRESENTABLE") and names the *open* question this section
closes (ADR-0076 "Revisit if": *"A content-addressed store is built → decide the hashing boundary:
hash the surface AST? the elaborated core? both?"*). Q43 answers it for proofs specifically.

### 3.1 · The hashing boundary — hash the elaborated `Comp`, not the source

```
  source text  ──parse──▶  Surf AST  ──elaborate──▶  Comp (the proof's subject)  ──▶  hash
       ✗ formatting-sensitive        ✗ still names-sensitive         ✓ THE cache key
```

**Hash the elaborated `Comp` term (the goal's actual subject), NOT the source text.** Reasons:

- **Formatting must not bust the cache.** `a<b` vs `a < b` vs a reformatted body (canonical `fmt`,
  the landed rung) are the *same* law; a source-text hash would spuriously invalidate on a whitespace
  or comment change. The `Comp` is post-`fmt`, post-parse — invariant under all of it.
- **The `Comp` IS what the proof is about.** The goal is `∀ args, Source.eval N₀ (bodyComp args) =
  …`; its truth depends on `bodyComp`, i.e. the elaborated term, and *nothing else*. Content-address
  on exactly the thing the proof's validity depends on ⟹ "cache hit ⟹ proof still valid" is true **by
  construction** (the ADR-0076 move: the hash IS the dependency check).
- **This is the Unison lesson applied to proofs.** Unison hashes the definition's AST (SHA3-512) and
  never recompiles a hash-stable definition; Q43 hashes the elaborated law-`Comp` and never re-proves
  a hash-stable law. The proof is a *cached typecheck of the law's obligation*.

Note the hash must be over the `Comp` **up to α-equivalence / de Bruijn** (bang's kernel is already
de-Bruijn — `Comp.subst`, `Val.shift` — so this is free: renaming params can't bust the cache
either).

### 3.2 · What the cache stores, and where

```
proofs/
  <blake3-of-law-Comp>.lean     -- the proof term (or `sorry` at the lower rung)
  <blake3-of-law-Comp>.axioms   -- the #print axioms census captured at proof time (the gate record)
```

- **Key**: `blake3` (or any collision-resistant hash — the *choice* of function is a one-liner, not a
  design fork) of the canonicalized elaborated `Comp` of the law obligation. Same hash discipline as
  ADR-0076's module Merkle-DAG — **one construct per problem**: the proof cache is a *view* over the
  same content-addressed store the incremental compiler uses, not a parallel cache.
- **Staleness = hash inequality.** Re-elaborate the law → recompute the hash → if it differs from any
  cached key, the cached proof is *not* consulted (it is about a different term). No timestamps, no
  manual invalidation, no "remember to re-run" convention — the top rung of the SSoT derivation
  ladder (generate, not test-or-convention).
- **Where proofs live**: a `proofs/` directory addressed by hash, checked into the repo (they *are*
  source — a certificate is a first-class artifact), built by a dedicated `lake` target (`lake build
  Bang.Proofs` or a `just prove` recipe) so CI re-checks them against the *current* kernel. A proof
  that references a `Comp` no longer produced by any law is dead and GC-able (Merkle-reachability, ADR-0076).

### 3.3 · Why not hash the source, or the goal `Prop`

- **Source text**: formatting-sensitive (§3.1) — rejected.
- **The rendered goal `Prop` string**: better than source but still Lean-pretty-printer-sensitive
  (universe metavars, notation) — the `Comp` term is the stable root; the `Prop` is *derived* from it
  by a fixed goal-shape function (§2), so hashing the `Comp` and hashing the `Prop` are the same
  staleness signal, and the `Comp` is cheaper and more stable. Hash the root, derive the rest.

---

## 4 · The trust story — what enters the TCB, and the seam

### 4.1 · TCB accounting (the keystone: no growth)

```
  ALREADY in the bang TCB          Q43 adds
  ─────────────────────────        ─────────────────────────
  Lean kernel                      NOTHING to the kernel
  Source.eval (the oracle)         a goal-shape FUNCTION (law-Comp → Prop) — itself a
  the axiom gate {propext,          Lean definition, kernel-checked, not trusted
    Classical.choice, Quot.sound}  the hash function (integrity, not soundness: a
                                     hash collision yields a WRONG-CACHE-HIT, caught by
                                     the CI re-check on a clean kernel — §4.3)
```

**Q43 adds nothing to the soundness TCB.** This is the shallow-embedding lesson (hs-to-coq /
coq-of-ocaml): because the law is *embedded* as a `Comp` and the goal is a `Prop` *about* that
`Comp`, the proof is ordinary Lean checked by the ordinary kernel under the ordinary axiom gate. No
SMT solver (contrast F\*), no bounded checker (contrast Kani), no external oracle whose say-so is
trusted. The proof either closes in the kernel with an axiom set ⊆ the gate, or it does not exist.

### 4.2 · Seam placement — the descent marker made visible

The stratification principle demands descent (verified → tested) be **explicit and marked**. Q43
surfaces this *into user programs*:

```
  law rigor       marker in the program            what it means
  ─────────       ─────────────────────            ─────────────
  TESTED          (default — a bare `law`)          fuzzed by `bang test`; DESCENT [test] rung
                                                    (the ADR-0068 `↓ Trait.law … (tested)` line
                                                     checkLaws already emits, TypeCheck.lean:3557)
  PROVED          `#prove`d, cache HIT              a kernel proof exists, axiom-gated; the
                                                    certificate hash is in proofs/
  PROVED-STALE    `#prove`d, cache MISS             the law's Comp changed; the old proof is about
                                                    a different term — re-prove (fail-loud, not
                                                    silently trusted)
```

The `↓ … (tested)` discharge line `checkLaws` *already prints* is the descent marker for the tested
rung; Q43 adds a `⇑ … (proved @ <hash>)` line for the proved rung. **Same construct, two rungs, the
seam is a line in the report** — the operator's "your paradigm is your row; your rigor is your rung"
made literal.

### 4.3 · The cache-integrity argument (why a hash collision is not a soundness hole)

A hash collision (two different law-`Comp`s, same key) would serve a proof about term X as if it
proved term Y — a *soundness* risk if trusted blindly. It is not, because the **CI `lake` target
re-checks every cached proof against the current kernel**: the cached `.lean` states its goal in
terms of the *actual* elaborated `Comp` (re-derived at build time), so a mis-served proof fails to
typecheck (its stated goal won't match the re-derived one) — fail-loud, caught by the gate, never
silently accepted. The hash is a *performance* index (skip re-proving), not a *soundness* authority.
This mirrors ADR-0076's "cache hit is provably right" — but Q43 gets it even cheaper because the
proof re-check is the backstop.

---

## 5 · The rung ladder with costs — smallest shippable rung named

| rung | ships | mechanism | cost | status |
|---|---|---|---|---|
| **R0 · test-only** | `bang test` fuzzes every discovered law, shrinks counterexamples | `lawInstancesOf` + `LawTest.runLaws` | — | ✅ **LANDED** (#60) |
| **R1 · export-goal-with-`sorry`** | `#prove L` emits `proofs/<hash>.lean` = the goal-shape `Prop` for law `L`, body `sorry`; `bang` reports the law as `⇑ PROVE-PENDING @ <hash>` | goal-shape function (§2 arm B) + hash (§3) + a `#prove` frontend pragma + a `proofs/` writer | **SMALL** — no proof automation, just the goal-emitter + cache plumbing; the `Comp`→`Prop` function is ~a day, the pragma rides the existing decl-walk | ✗ **the smallest shippable rung** |
| **R2 · proved-and-cached** | an agent/human fills the `sorry`; cache HIT on re-elaboration skips re-proof; axiom census captured | R1 + the `.axioms` sidecar + staleness check | **MID** — per-law proof effort (the CRDT laws are `decide`/`omega`/`simp`-shaped for finite ADTs; harder laws are agent-fillable) | ✗ next |
| **R3 · CI-gated** | `just prove` (or `lake build Bang.Proofs`) fails CI on any `sorry`-bodied or axiom-gate-violating cached proof; a `#prove`d law with a stale/absent proof is a RED build | R2 + a CI leg wired into `just verify`, gated via `#print axioms` (never grep-for-sorry, per the gate discipline) | **SMALL given R2** — one CI leg + the audit-sync move (`Bang/Audit.lean`'s existing pattern) | ✗ then |

**R1 is the smallest shippable rung and the right first cut**: it makes the seam *visible* and the
pipeline *real* (a law → a concrete Lean goal file, content-addressed) without committing anyone to
discharging proofs. It is the "exported-goal-with-sorry" rung the task names. Crucially R1 is
*useful on its own* — an agent handed `proofs/<hash>.lean` with a stated goal and a `sorry` has
exactly the well-posed obligation it needs; the goal-shape function having *derived* that `Prop`
from the elaborated term (not a human transcription) is itself the correctness-by-construction win.

The flagship consumer (`distributed-story.md` §2 rung 1, **certified CRDTs**) needs **R2** for its
headline ("user `merge` *proved* a join-semilattice"): comm/assoc/idem over a finite CRDT state ADT
are total-fragment laws (arm B applies directly) and are `decide`/`omega`/`simp`-shaped, so R2 for
CRDTs is *cheap* once R1's goal-emitter exists. That is the concrete pull that justifies building the
ladder in this order.

---

## 6 · ADR-INPUTS (decision-shaped)

### Recommended pipeline

1. **Goal shape**: arm **B** — `∀ args, Source.eval N₀ (bodyComp args) = .done (.vint 1)`, the
   universally-quantified form of the *exact* readback proposition `bang test` already fuzzes,
   **scoped to the total (⊥-row) fragment**; `#prove` on a `Div`-rowed law is a *type* error. Arm C
   (fuel-free, over `StepStar`) is the named north star, additively reachable once the
   `Source.eval ↔ StepStar` adequacy lemma lands. Arm D (host-equational) is post-v1.
2. **Cache**: content-address on the **canonicalized elaborated `Comp`** of the law obligation
   (de-Bruijn, so α/param-rename-invariant; post-`fmt`, so formatting-invariant), NOT source text.
   Staleness = hash inequality (ADR-0076's Merkle move). Proofs live in `proofs/<hash>.lean` +
   `<hash>.axioms`, built by a dedicated `lake`/`just` target, GC'd by Merkle-reachability. The proof
   cache is a **view over ADR-0076's existing content-addressed store**, not a parallel cache.
3. **Trust**: **nothing enters the soundness TCB** — the goal-shape function is a kernel-checked Lean
   definition; the proof closes in the Lean kernel under the existing axiom gate (⊆ {`propext`,
   `Classical.choice`, `Quot.sound`}). No SMT/oracle (rejects the F\* posture). Hash collisions are a
   *performance* concern only: the CI re-check re-derives each goal from the current kernel, so a
   mis-served proof fails to typecheck (fail-loud), never silently accepted.
4. **Descent marker**: extend `checkLaws`'s existing `↓ … (tested)` discharge line with a
   `⇑ … (proved @ <hash>)` / `⇑ PROVE-PENDING @ <hash>` line — the seam is a line in the report.
5. **Build order**: **R1 (export-goal-with-`sorry`) first** — smallest shippable, makes the pipeline
   real and the seam visible without committing to proof effort; **R2 (proved+cached)** delivers the
   certified-CRDT headline (total, `decide`-shaped laws); **R3 (CI-gated)** closes the loop, gated via
   `#print axioms`, never grep-for-sorry.

### Named costs

- **R1**: ~a day of goal-emitter + cache plumbing + a `#prove` pragma on the decl-walk. No proof
  automation. Adds a `proofs/` dir and a `lake` target.
- **R2**: per-law human/agent proof effort; cheap for the total `decide`-shaped corpus (CRDT laws),
  open-ended for arbitrary laws (but that is the *point* — hard laws get real proofs).
- **R3**: one CI leg + audit-sync (the `Bang/Audit.lean` pattern).
- **The `Source.eval ↔ StepStar` adequacy lemma** (to reach arm C) is a kernel-lane deliverable
  *independent* of Q43; naming it as a dependency, not a blocker (arm B ships without it).

### Rejected alternatives (with reasons)

- **Arm A (fuel-existential goal)** — the `∃ n` hides non-termination; a law that "passes" only with
  growing fuel is not a law. Rejected in favor of the total-fragment fixed-fuel arm B.
- **Hash the source text** — formatting-sensitive; a whitespace/comment change would bust an
  otherwise-valid proof. Rejected for hashing the elaborated `Comp` (the proof's actual subject).
- **SMT/oracle discharge (F\* posture)** — fast and automatic but grows the TCB with a ~500-KLOC
  solver (documented soundness bugs). Rejected by invariant #1 (proof rides the reference) and the
  axiom gate. Automation whose output the *kernel re-checks* (`decide`, `omega`, SMT-backed tactics)
  is fine; a *trusted* oracle is not.
- **A parallel proof cache** — would be a second content-addressed store that can disagree with
  ADR-0076's module Merkle-DAG (an SSoT violation). Rejected for a *view* over the one store.
- **Bounded model checking (Kani posture) as the "proof" rung** — bounded ≠ proved; it belongs
  *between* fuzz and proof on the ladder, not as the top rung. bang's fuzz rung (#60) already
  occupies the "cheap, incomplete" slot; a bounded checker would be a redundant middle rung with no
  new guarantee the proof rung doesn't dominate.

### One fork flagged for the operator (STOP-and-SHOW)

**Should v1 `#prove` cover only the total fragment (sharp typed seam, my recommendation) or also the
`Div` fragment via a fuel-parametric statement (broader coverage, softer seam)?** This is a
*preference* call — coverage vs seam-sharpness — not a correctness one; both arms are sound. I
recommend total-only because it makes proof-eligibility a *typed, read-off-the-row* property and
keeps the language-level stratification seam (the effect row) load-bearing. Named here rather than
silently decided.

---

## References

- QuickChick — Property-Based Testing in Coq (Software Foundations vol. QC);
  `Dec (P : Prop)` typeclass making a decidable prop both `Checkable` and reflectable:
  <https://softwarefoundations.cis.upenn.edu/qc-current/index.html>,
  <https://softwarefoundations.cis.upenn.edu/qc-current/QuickChickInterface.html>. Foundational
  verified-testing framework: Paraskevopoulou et al., "Foundational Property-Based Testing"
  (<https://lemonidas.github.io/pdf/Foundational.pdf>).
- Plausible (Lean 4 property testing, refutation-only):
  <https://github.com/leanprover-community/plausible>.
- hs-to-coq / coq-of-ocaml — shallow embedding, no-TCB-extension:
  <https://formal.land/docs/tools/coq-of-ocaml/introduction>.
- Creusot (deductive, Why3+SMT): <https://creusot.rs/>. Kani (bounded model checking, CBMC):
  <https://arxiv.org/abs/2607.01504>. Rust verification landscape survey:
  <https://arxiv.org/pdf/2410.01981>.
- F\* / Z3 SMT pipeline + TCB accounting (context on solver-in-the-TCB cost):
  Agora, "Trust Less and Open More in Verification" (<https://arxiv.org/html/2407.15062v3>).
- Unison — content-addressed code, typecheck-once-cache-forever (the cache-design prior art):
  <https://www.unison-lang.org/docs/the-big-idea/>.
- "A Failed Proof Can Yield a Useful Test" (the *inverse* arrow, proof→test):
  <https://arxiv.org/pdf/2208.09873>.
- Internal anchors: `Bang/Frontend/TypeCheck.lean` (`lawInstancesOf:3570`, `checkLawOn:3509`,
  `checkLaws:3529`), `Bang/Witness/LawTest.lean` (`runLaws`, `LawOutcome`, `evalLawOn`),
  `Bang/Core/Semantics/Eval.lean` (`Source.eval:231`, `Result:38`, `StepStar:111`), ADR-0076
  (content-addressing), ADR-0068 (laws-as-tested-rung), `docs/notes/verification-ladder.md` (Q43
  sketch — this note's predecessor), `docs/notes/distributed-story.md` §2 (certified CRDTs — the
  consumer).
