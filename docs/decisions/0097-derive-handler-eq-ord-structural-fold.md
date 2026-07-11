# ADR-0097 · Deriving handlers: `Eq`/`Ord` as a structural fold over the ADR-0069 μ-sum-of-products

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: A `data Foo = … deriving (Eq, Ord)` clause runs an elaboration-level handler
  (mirroring Lean 4's own `DerivingHandler`) that reads the carrier's resolved constructor/payload
  shape and EMITS an ordinary `impl` — same-tag structural equality for `Eq`, decl-order
  lexicographic comparison for `Ord` — targeting **user `data` only** (a built-in-carrier target is
  refused, the dead-impl trap). The derived impl's trait laws auto-attach for free because
  `bang test`'s law discovery already walks the decl prelude generically (verified empirically,
  §Ground). **Load-bearing finding, machine-checked this session:** a derive for a RECURSIVE data
  type cannot be emitted as an ordinary `impl` today — `buildEnv`'s single-pass elaboration
  registers an impl's own instance into `env.insts` only AFTER elaborating its body
  (`TypeCheck.lean:2926-2927`), so a self-referential call (`tx == ty` where `tx : Self`) inside
  that same impl's body sees an `env.insts` that does not yet contain it, failing
  `no impl provides 'eq' for (mu. …)` — witnessed for BOTH `Eq` and `Ord`, hand-written or derived,
  independent of the derive mechanism. **This narrows tier-1's honest scope to non-self-recursive
  carriers** until the ordering gap is fixed (a named, separate, non-blocking follow-up, §Recursive
  wall); tier-1 SHIPS for the non-recursive case, which is the common law-bearing shape the
  `VecOps`/`IntOrd`/`Box`-style corpus already exercises. **UPDATE (2026-07-11, issue #112, §3a):
  the wall is FIXED** — knot-based `.binopS` dispatch (not the originally-named two-pass, which was
  built and refuted first) closes it; tier-1's scope narrowing above is LIFTED for the
  self-recursive case, see §3a for the full account.
- **Resolves**: issue #110 (this design consult), gates issue #109 (`deriving (Eq, Ord)` impl)
- **Depends-on**: 0068 (trait/impl wiring + `checkLaws`/`bang test` law discovery), 0069
  (`data`-decl μ-sum-of-products encoding), 0079 (generic data monomorphization — scopes tier-1 to
  monomorphic `data`, see §Decision 1)
- **Relates-to**: #78 (trait-op name-callability — Eq/Ord's `==`/`<` are binop-dispatched TODAY, so
  tier-1 has NO #78 dependency), #108 (ctor namespacing — RULED option (a) 2026-07-11, not yet
  implemented; this ADR states its ordering assumption explicitly, §Decision 5), #111 (tier-2
  derives, blocked on #78), `docs/notes/traits-prelude-survey.md` §2-4 (the derivability matrix and
  recommendation this ADR implements — not re-surveyed here)

## Status

Proposed (2026-07-11). Design consult for #110; the recursive-carrier finding is a genuine surprise
this design session surfaced and reshapes tier-1's scope — flagged for operator ruling before #109
implementation starts (§Recursive wall names the fallback options).

- **Layer:** F (frontend — parser + elaborator). Kernel untouched by construction (invariant #5):
  a derive handler emits an ordinary `Decl.implD`, indistinguishable at the kernel boundary from a
  hand-written one — the same "elaborate-away" move `ADR-0069`/`0075`/`0088`/`0091`/`0093` all use.

## Context

`docs/notes/traits-prelude-survey.md` (§2, the derivability matrix) established that `Eq`/`Ord` are
**structural folds** over `data`'s ADR-0069 encoding (`data T = C₀(…) | C₁(…)` lowers to
`μX. p₀ + (p₁ + …)`, decl order = sum order) — the SAME shape Lean 4's own `deriving` handlers fold
over (`DerivingHandler = Array Name → CommandElabM Bool`, inspecting an inductive's
constructors/fields and emitting an instance). Tier 1 targets exactly `Eq`/`Ord` because their ops
(`==`/`<`) are binop-dispatched TODAY (`docs/reference/language.md` §Traits & Laws; `.binopS`
consults `env.insts`) — a derived impl is usable the moment it exists, no #78 (name-callability)
dependency, unlike `Show`/`Hash`/`Default`/`Enum` (tier 2, #111).

This ADR pins the mechanism #109 implements: surface spelling, codegen shape, the carrier-refusal
diagnostic, law auto-attachment, and #108's sequencing — each verified against the REAL `bang`
binary (built this session from a clean `lake build bang`, `Build completed successfully
(1448 jobs)`), not speculated.

## Decision

### 1 — Surface: a `deriving (…)` clause on the `data` decl, not a standalone `derive` decl

```
data Box = BLeft(Int) | BRight(Int) deriving (Eq, Ord)
```

**Rejected: standalone `derive Eq for Box`.** Two reasons, both concrete costs, not taste:

- **Parser cost.** `pDecl`'s `"data"` arm (`Bang/Frontend/Surface.lean:1967-1972`) already parses
  `data N ā = C₀ | C₁ | …` to a fixed token (`=`) currently ending the decl; a `deriving (…)` suffix
  is one more optional trailing clause on an EXISTING arm (mirrors `pDataParams`'s own
  loop-until-`=` shape — a loop-until-EOD after the ctor list). A standalone `derive` decl is a
  BRAND NEW `pDecl` arm (`isDeclStart`, `Bang/Frontend/Surface.lean:2029-2031`, needs `"derive"`
  added) plus its own name-resolution-of-an-existing-type step, plus interacts awkwardly with
  ADR-0079's generic `data T a` (bite-1 monomorphize-per-use template) — a trailing clause reads
  naturally as "this template ALSO derives", a standalone decl has to re-name the (possibly
  type-parametrized) target.
- **Locality — the Rust/Haskell/Swift/Scala precedent (4/6 deriving-clause languages in the
  survey's census) vs Lean 4's own `deriving` keyword-suffix syntax on `structure`/`inductive`.**
  bang's elaborator IS Lean; `data … deriving (…)` is syntactically the closest transplant of
  exactly the mechanism being adopted. A standalone decl (closer to nothing surveyed — no language
  in the census separates the derive site from the type decl) buys nothing and reads as an
  unexplained divergence.

`bang fmt` **consequence** (verified): `Bang/Frontend/Format.lean:545` (`.dataD` arm) has no
`deriving`-clause rendering today — adding the clause to `Decl.dataD`'s constructor needs a
matching `Format.lean` print arm or `bang fmt` silently DROPS it on round-trip (a real, concrete
implementation item this ADR flags for #109, not a design fork).

### 2 — Codegen shape: same-tag structural fold, emitted as an ordinary `impl`

**`Eq`** — per constructor: same tag ⇒ AND over payload-slot equality (recursing via `==` at a
non-`Self` payload type, i.e. `Int`); different tag ⇒ `false`. Worked example, the derive for
`data Box = BLeft(Int) | BRight(Int) deriving (Eq)` — hand-written and RUN against the real binary
this session (`w1-eq-nonrec.bang`):

```
trait Eq { fn eq(a, b) -> (Unit + Unit) law refl(a): a == a }
impl Eq for Box {
  fn eq(p, q) = match p {
    BLeft(x)  -> match q { BLeft(y) -> x == y, BRight(y) -> 0 == 1 },
    BRight(x) -> match q { BLeft(y) -> 0 == 1, BRight(y) -> x == y }
  }
}
```
`(BLeft(3) == BLeft(3), BLeft(3) == BRight(3))` ⟹ `(true, false)` — **RAN, exit 0, output `1`**
(the witness threads both booleans through one `if`-nest to a single Int so a run needs no tuple
sugar; see §Ground for the exact program). This is the ELABORATOR's fold target: a
`match`-of-`match` diagonal over the ctor sum, `==` at each `Int` payload slot.

**`Ord`** — ctor-index order = decl order (the tag IS the ordinal, ADR-0069 "sum by decl order");
ties broken left-to-right lexicographic over payload slots (`hx < hy`, else if `hy < hx` then
false, else recurse/compare next slot). Same `match`-of-`match` shape with a 3-way ladder instead
of a 2-way equality. **RAN** (`w3-ord-nonrec.bang`, `BLeft(3) < BLeft(5)` ⟹ `inr ()` = true).

**A trait declaration must exist for the derive to target.** `Eq`/`Ord` are ordinary bang traits
(no built-in "the language knows Eq" hook) — the derive handler either (a) assumes a PRELUDE
`Eq`/`Ord` trait declaration always in scope (the #106 `Prelude.bang` migration's natural home), or
(b) synthesizes the trait declaration too if absent. **Recommendation: (a)** — a hand-authored
`trait Eq { fn eq(a,b) -> (Unit+Unit); law refl(a): a == a; law symm(a,b): a==b => b==a; law
trans(a,b,c): a==b => b==c => a==c }` (and the analogous `Ord` with the total-order laws) ships
ONCE in the prelude; the derive handler emits ONLY the `impl`, never redeclares the `trait`. This
keeps the derive handler's own scope minimal (fold-over-ctors → impl-ops only) and makes the laws
single-sourced on the trait declaration (no risk of a derived program's laws drifting from the
prelude's).

### 3 — The recursive-carrier wall (the load-bearing finding — machine-checked)

**Both Eq and Ord fail identically on a self-recursive carrier**, derived OR hand-written:

```
data IntList = Nil | Cons(Int, IntList)
impl Eq for IntList {
  fn eq(p, q) = match p {
    Nil -> match q { Nil -> 0 == 0, Cons(hy, ty) -> 0 == 1 },
    Cons(hx, tx) -> match q {
      Nil -> 0 == 1,
      Cons(hy, ty) -> let headEq = hx == hy in let tailEq = tx == ty in
                       if headEq then tailEq else 0 == 1
    }
  }
}
```
**RUN RESULT:** `error: no impl provides 'eq' for (mu. (Unit + (Int * #0)))` — reproduced
identically for `Ord`/`<` on the same type (`w2c` witness). **Root cause, machine-located:**
`Bang/Frontend/TypeCheck.lean:2911-2929` (`buildEnv`'s `.implD` arm) elaborates an impl's op body
(`elabS ⟨insts, …⟩ bodyΓ od.body`, line 2926) using `insts` as it stood BEFORE this impl's own
`insts := insts ++ […]` registration (line 2927, the NEXT statement) — a strict single-pass
ordering, not a fixpoint. A self-referential call inside the body being elaborated (`tx == ty`
where `tx, ty : Self`) needs the very instance not yet in scope. **Confirmed NOT derive-specific**:
a hand-written, non-derived hand-authored hollowed-out `impl Eq for IntList` with an inert
non-recursing body type-checks and RUNS fine (`w2b.bang`, returns `inr ()`) — the wall triggers
purely on **self-reference within the impl's own body**, exactly what any Eq/Ord derive for a
RECURSIVE type structurally needs to emit.

**Consequence for tier-1's scope:** a derive handler emitting the naive fold above for a recursive
`data` type would generate an impl that PARSES and TYPE-CHECKS the signature but FAILS AT RUNTIME
on any recursive-payload comparison — silently worse than refusing. **This ADR narrows tier-1 to
non-self-recursive carriers** (any `data` decl whose payload slots never mention the type's own
name) until the `insts`-registration ordering is fixed. The derive handler must **detect
self-recursion in the ctor shape and refuse** (a named diagnostic, same shape as §4's carrier
refusal) rather than emit a body that will runtime-fail — refusing at DERIVE time is strictly
better than a `bang test`/`bang run` failure downstream, and is consistent with this ADR's own
carrier-refusal precedent (§4).

**Fix options for the wall itself (named, NOT decided here — a separate, escalable follow-up, not
a #109 blocker):** (i) two-pass `buildEnv` — pre-register every impl's SIGNATURE (name/target/ret
type) before elaborating any body, so self- and mutually-recursive impls both resolve (mirrors how
`gen`/`ctors`/`traits` are ALREADY forward-visible across the whole decl list, just `insts` is not);
(ii) a fixpoint/knot-tying `insts` construction. Option (i) is the smaller, more surgical change
(pre-scan for signatures only, a metadata pass, not a semantic one) and is the natural next step —
but it touches `buildEnv`'s core elaboration order, a shared surface path every trait/impl program
rides, not a derive-only concern, so it is **kernel-adjacent enough to escalate** rather than fold
into #109's scope silently. Filed as a follow-up issue (recommendation: title
`fix(traits): impl bodies can't self-reference their own instance — buildEnv single-pass insts
registration`), independent of and NOT blocking tier-1's non-recursive slice.

### 3a — ADDENDUM (2026-07-11, issue #112): the wall is FIXED — knot-based dispatch, not option (i)

**Option (i) alone (signature pre-registration) was BUILT and REFUTED before landing anything.**
Two-pass `buildEnv` — pre-register every impl op's signature into `env.insts` with a placeholder
body, elaborate real bodies in a second pass against the complete table — compiles and still FAILS
on `w2`/`w2c`: `unbound variable #pending-impl-body`. Root cause, machine-confirmed this session:
`.binopS` dispatch (`elabS`'s `.binopS` arm) resolves an operator by **textually splicing
`inst.body`** — an already-elaborated `Surf` VALUE — into the call site
(`.app (.app (.annotS (.lam p (.lam q inst.body)) fnTy) a') b'`), never re-descended into. A
self-referential call bakes in whatever `insts[idx]` holds AT THE MOMENT its OWN body is
elaborated (still the pass-1 placeholder) — no ordering of a signature-then-body two-pass closes
that gap, because splicing is substitution, and a genuinely self-recursive body has no fixed
inlining depth (iterating pass 2 to a fixpoint can't converge either, for the same reason). The
same probe also showed a FORWARD reference between two DIFFERENT impls (impl A's op calling impl
B's, B declared textually AFTER A) fails identically and for the identical reason — this is not a
self-recursion-only gap, it is a property of the SPLICE mechanism itself.

**The actual fix: uniform knot-based dispatch, not a two-pass registration order.** Every 2-param
impl op (the only arity `.binopS` ever dispatches — its own match requires exactly `[p, q]`) is
now bound as a genuine `let rec` fixpoint via the SAME Landin's-knot machinery (`letRecS`/
`buildLetRec`, ADR-0073, hardened by #95's knot-sharing fix) ordinary recursive `let`s already use
— NOT a new recursion mechanism. `buildEnv`'s `.implD` arm defers a 2-param op to a
`PendingOpKnot` (fresh binder name, target/ret types, RAW params/body) instead of elaborating it
inline; `elabProg` wraps the whole program body in one `let rec` per pending knot (decl order,
TUPLED single-argument encoding — `let rec eq : (Self * Self) -> RetTy = fun pq => let (p, q) = pq
in body`, called as `($eq) (a, b)`) BEFORE the single `elabS` pass, so `letRecS`'s own elaboration
arm — which resolves a self-reference through the μ-encoded fixpoint, not substitution — is what
actually type-checks and lowers the recursive body. `.binopS` dispatch changed from splicing
`inst.body` to `.app (.force (.var knotName)) (.pairS a' b')`. Non-2-param ops (0/1/3+) are
UNCHANGED (still pre-elaborated + spliced) — safe because `.binopS` never dispatches that arity, so
a splice-caused self-reference wall there is structurally unreachable through the operator surface.

**Why TUPLED, not curried, args:** `letRecS`'s elaboration arm only threads the `let rec`'s
DECLARED type onto its OUTERMOST `.lam` binder; a curried second parameter (`fun p => fun q =>
…`) falls through the GENERIC `.lam` arm instead, which mints it a FRESH HOLE rather than the
arrow's second domain — a separate, pre-existing gap in `letRecS` for curried multi-arg functions,
confirmed this session and NOT touched by this fix (consuming `letRecS` as-is, not restructuring
it — the tupled encoding sidesteps the gap entirely, since `peelTupleSplit`'s single-param-
immediately-destructured shape is already fully supported).

**Scope actually landed vs. still blocked:**
- Self-recursion (w2/w2c's exact shape — `Eq`/`Ord` on `IntList`) — **FIXED.** Both witnesses now
  RUN correctly (`w2` → `1`, `w2c` → `inr ()`), promoted to `examples/trait-recursive-eq` and
  `examples/trait-recursive-ord` (gated by `check-examples.sh`/`check-examples-env.sh` forever, both
  engines).
- A BACKWARD reference (a later-declared impl's op calling an earlier-declared impl's op) — **now
  works, strictly MORE than pre-#112** (the old single-pass splice already resolved "earlier ops",
  this fix adds self-reference on top without regressing it — confirmed via a hand-written
  cross-impl repro, backward direction).
- A FORWARD or MUTUAL reference (an earlier-declared impl calling a later one, or two impls calling
  each other) — **still fails** (`unbound variable <laterKnotName>`). Plain `letRecS` only ever
  sees itself + prior bindings in scope; TRUE forward/mutual dispatch needs the N-way
  tuple-of-thunks generalization of `buildLetRec` a separate, concurrently in-flight lane
  (`feat-mutual-rec`, `buildLetRecMulti`) is building — deliberately NOT built or touched here (a
  cross-lane collision this fix's own scope explicitly stopped short of).

**Consequence for tier-1's scope (supersedes §3's narrowing above):** the `insts`-registration
wall this section names is CLOSED for the self-recursive case — tier-1's derive scope widens back
to self-recursive carriers (`IntList`/`List`-shaped `data`, the FIRST recursive-type derive ask
§3 flagged as blocked) the moment #109 targets it; the derive handler's own carrier-detection logic
(§3's "detect self-recursion and refuse") is no longer needed for that case. Tier-1 remains
narrowed only for a MUTUAL-recursion derive shape (two `data` types whose `Eq`/`Ord` impls would
need to call each other) — a shape no SINGLE-type derive (§2's fold, always over ONE `data` decl's
own ctors) can produce in the first place, so this residual limit is VACUOUS for #109's actual
codegen target, not a live constraint.

Landed: branch `fix-112-buildenv-twopass`, `Bang/Frontend/TypeCheck.lean` (`Inst`/`PendingOpKnot`/
`ElabEnv.pendingKnots`, `buildEnv`'s `.implD` arm, `wrapPendingKnots`, `elabProg`, `checkLawOn`'s
matching wrap), two new `examples/` projects. Gates: `lake build bang` clean, `just verify` green
(examples both engines, `tools/test-law.sh` 20/20, fitness/audit), `just axioms` unchanged (7
pre-existing `sorryAx`, none in `TypeCheck.lean`).

### 4 — Carrier refusal: built-in carriers refused outright; function-typed fields refused

**Built-in carrier (dead-impl trap, #78 fact 3, RE-CONFIRMED this session):**
`impl Eq for Int { fn eq(a,b) = a==b }` type-checks and even reports its law `PASS` under
`bang test` (`w5-int-carrier.bang`: `✓ Eq.refl — PASS (30 samples)`) while ALSO reporting
`✗ Eq.(unreachable impl) — ERROR` — the impl's own `eq` NEVER RUNS (the kernel's `Int` δ-rule wins
`==` before `env.insts` is consulted), so the law's PASS is checked against the KERNEL's `==`, not
the derived impl — silently misleading if a user trusted the PASS as validating their (nonexistent,
from the runtime's view) impl. **The derive handler must refuse a built-in-carrier target
OUTRIGHT at derive time** (`deriving (Eq)` on `data`-only is naturally enforced by the surface
form itself — `deriving` is a `data`-decl clause, so a built-in type can never be the SYNTACTIC
target; this closes the class of bug ADR-0068/#74's `unreachableIntImplDiagnostics` catches only
post-hoc for HAND-WRITTEN impls). No new runtime check needed beyond "derive only fires from a
`data` decl clause" — a happy case of the surface FORM making the bad state unrepresentable, not
merely detected.

**Function-typed payload fields (Eq is undecidable on functions):** REFUSE with a named
diagnostic, not silently skip the field. A `data` decl in v1 has no function-typed payload slot
(ctor payloads are `Int`/a named-type recursion per ADR-0069's `resolveTy`/`CtorInfo` shape) — so
this is currently VACUOUS (no v1 program can construct the refused case) but the ADR states the
policy now so a future payload-kind extension (e.g. a thunk-typed field) does not silently
mis-derive `false`-always or a bogus comparison.

### 5 — Law auto-attachment: free by construction, verified empirically

**No new wiring needed.** `bang test`'s law discovery (`TypeCheck.lawInstancesOf`,
`Bang/Witness/LawTest.lean` §6 `runLawsFromSource`) walks a program's WHOLE decl prelude generically
— it has no notion of "hand-written vs derived impl," it just pattern-matches `Decl.implD` nodes
against `Decl.traitD` law clauses. **Verified this session**: a derive-shaped `impl Eq for Box`
(§2's exact worked example) placed in a decls-only file and run through `bang test` reports
`✓ Eq.refl — PASS (30 samples)` with ZERO extra plumbing (`w4-eq-lawcheck-decls.bang`) — confirming
the survey's differentiator claim ("derived-AND-law-checked, no surveyed language ships this") is
not merely designed but **empirically holds today**, PROVIDED the trait's laws live on the trait
declaration (§2's decision (a)) — which they already do, structurally, per ADR-0068.

### 6 — Sequencing against #108 (ctor namespacing)

#108 is **RULED** (operator, 2026-07-11): option (a), type-namespaced constructors with bare-name
sugar when unambiguous — but **NOT YET IMPLEMENTED** (the resolution-rules probe is queued behind
the mutual-rec probe per #108's own comment). The derive handler's fold (§2) NAMES ctors explicitly
in the emitted `match` arms (`BLeft`/`BRight`/`Nil`/`Cons` — the exact bare names as declared) —
today this is safe because ctor names are (pre-#108) globally unique by construction (a duplicate
ctor name across two `data` decls is already a `buildEnv` error, `TypeCheck.lean:2877`
`"duplicate constructor"`). **The derive handler reads whichever ctor-name resolution is CURRENT at
its call site** — it needs no special #108-awareness because it emits ctor names exactly as the
target `data` decl declared them, and #108's post-implementation semantics is bare-name-when-
unambiguous, WITHIN the type being derived over, which is always unambiguous (the derive handler
only ever names the ctors of the ONE type it targets). **Consequence: tier-1 does NOT depend on
#108's implementation landing first** — it degrades gracefully whether #108 has landed or not, since
the derive handler's ctor references are always self-type-scoped by construction. (This REVISES
the traits-prelude-survey's framing, which stated derive "runs POST-#108-namespacing" — that
caution was about the BROADER prelude-injection collision problem #108 solves for hand-written
multi-type programs; a single-type derive fold was never exposed to the cross-type collision #108
targets.)

### 7 — Generated-code visibility: no provenance marker exists today (a gap, flagged)

`bang query symbols` (verified, `w4-eq-lawcheck-decls.bang`) renders a derived-shaped `impl Eq for
Box` identically to a hand-written one — `DeclFact` (`Bang/Frontend/Query.lean:128-175`) carries no
"derived" marker. **This ADR does not propose adding one now** (out of scope — `#109`'s minimal
slice is codegen + refusal + the `deriving` clause; provenance is a query-surface enhancement, not
a correctness requirement) but FLAGS it: a future `DeclFact.provenance : Option String` field
(`some "derived(Eq)"` vs `none`) would let `bang query dump`/`symbols` distinguish them for an
agent inspecting a program — filed as a follow-up, non-blocking.

## Rejected alternatives

- **Standalone `derive Eq for T` decl** — §1, parser-cost + no-precedent-for-separation reasons.
- **Macro-expansion at parse time** (textual substitution before elaboration) — loses the
  elaborator's access to the RESOLVED ctor/payload shape (ADR-0069's `CtorInfo`, built during
  `buildEnv`, not available at parse time); would need its own duplicate shape-resolution logic,
  violating "one construct per problem" against the elaborator's existing `buildEnv` walk.
- **No-derive (keep all impls hand-written)** — the survey's baseline; rejected because Eq/Ord are
  ≥8/10-language deriving-culture invariants and bang's own law-auto-attach differentiator (§5) is
  free the moment ANY derive mechanism exists — leaving it on the table costs the ecosystem's
  single strongest "no surveyed language ships this" story for zero savings (the fold logic is the
  same work whether hand-authored per-program or built once as a handler).
- **Silently emitting the recursive-carrier fold anyway** (accept the runtime failure) —
  rejected: `Eq`/`Ord` are meant to be trustworthy structural equality; a `deriving` clause that
  compiles clean and fails at first recursive use is a worse user experience than a named refusal
  naming the exact wall (consistent with the `CLAUDE.md` invariant "fail loud").

## Ground (witnesses run against the real binary, this session)

Built from a clean checkout (`design-derive-handler` @ `43676ce2`, `lake build bang` →
`Build completed successfully (1448 jobs)`, `.lake/build/bin/bang`). All four are hand-written
stand-ins for what the derive handler WOULD generate (§2's worked examples), run via
`bang run`/`bang test` directly — no Lean-side witness needed, no claim here needs kernel
arbitration.

| witness | shape | result |
|---|---|---|
| `w1-eq-nonrec.bang` | `Eq` fold, 2-ctor non-recursive `Box` | RAN, output `1` (both comparisons correct: equal-payload same-ctor ⟹ true, same-payload different-ctor ⟹ false) |
| `w2-eq-recursive.bang` / `w2c` (Ord) | `Eq`/`Ord` fold, self-recursive `IntList` | **FAILED**: `error: no impl provides 'eq'/'lt' for (mu. (Unit + (Int * #0)))` — the load-bearing wall, §3 |
| `w2b.bang` | hand-written non-recursing impl on the SAME recursive type | RAN fine (`inr ()`) — isolates the wall to self-REFERENCE, not the recursive TYPE itself |
| `w3-ord-nonrec.bang` | `Ord` fold, 2-ctor non-recursive `Box` | RAN, output `inr ()` = true (`BLeft(3) < BLeft(5)`) |
| `w4-eq-lawcheck-decls.bang` | §2's `Eq` impl, decls-only, run through `bang test` | `✓ Eq.refl — PASS (30 samples)` — law auto-attach confirmed free, §5 |
| `w5-int-carrier.bang` | `impl Eq for Int`, decls-only, `bang test` | `✗ Eq.(unreachable impl) — ERROR` co-reported alongside a MISLEADING `✓ Eq.refl — PASS` — the dead-impl trap re-confirmed, §4 |
| `bang query symbols` on `w4` | provenance check | `impl` fact for `Eq for Box` carries no derived-vs-hand-written marker — §7 |
| `bang fmt` on `w4` | round-trip check | clean round-trip; NO `deriving`-clause rendering exists yet in `Format.lean:545` — §1 implementation note |

Also consulted: `docs/reference/language.md` §Traits & Laws (the binop-dispatch-only constraint,
build-gated); Lean 4 core `Deriving/` (`DerivingHandler = Array Name → CommandElabM Bool`,
BEq/DecidableEq/Repr/Inhabited/Hashable/Ord — the mechanism transplanted, §1/§2); issue #108's
ruling comment (operator, 2026-07-11, option (a)); `Bang/Frontend/TypeCheck.lean:2854-2929`
(`buildEnv`, the exact ordering the recursive-carrier wall is located in).

**§3a addendum, 2026-07-11 (issue #112):** the `w2`/`w2c` FAILED row above is HISTORICAL — both now
RUN correctly (`w2` → `1`, `w2c` → `inr ()`) against the knot-based dispatch fix; promoted to
`examples/trait-recursive-eq`/`examples/trait-recursive-ord`, gated forever. See §3a for the full
before/after and what remains blocked (forward/mutual reference).

## Consequences

- #109 implements: the `deriving (Eq, Ord)` parser clause (`pDecl`'s `"data"` arm), the fold
  codegen — **now for self-recursive `data` targets too** (§3a), not just non-recursive ones — the
  built-in-carrier refusal (free by construction — §4), and a `bang fmt` print arm for the new
  clause (§1's flagged gap).
- #109 does NOT implement (named, separate work): a `DeclFact` provenance marker (§7's follow-up),
  a prelude `Eq`/`Ord` trait declaration if #106's `Prelude.bang` migration has not landed one yet
  (§2's dependency — if absent, #109 ships its own minimal `trait Eq`/`trait Ord` declaration
  inline as a stopgap, superseded once #106 lands the canonical one). Recursive-carrier derive is
  NO LONGER on this list (§3a closed it) — a MUTUAL mid-derive shape remains structurally
  unreachable from a single-type fold (§3a's last paragraph), so it needs no explicit exclusion.
- The traits-prelude-survey's tier-1 recommendation SURVIVES with its §3 narrowing now LIFTED
  (§3a): "tier 1 ships today" covers self-recursive carriers (`IntList`/`List`-shaped `data`) as
  well as the non-recursive `VecOps`/`Box`-style corpus — the FIRST recursive-type derive ask is
  unblocked.

## Revisit if

- ~~The `buildEnv` `insts`-ordering fix (§3) lands~~ — **DONE, §3a (2026-07-11, issue #112).** Landed
  as knot-based dispatch (a dispatch-MECHANISM change: splice → `let rec`-bound call), not the
  originally-named two-pass registration order (§3a explains why option (i) alone was refuted).
  Tier-1 scope extended to self-recursive carriers; the codegen SHAPE in §2 needed no change.
- #106's `Prelude.bang` migration lands a canonical `trait Eq`/`trait Ord` → #109's stopgap inline
  declaration (§2) is deleted in favor of importing the prelude one.
- Tier-2 derives (#111) unblock on #78 → this ADR's carrier-refusal and law-auto-attach findings
  (§4/§5) are directly reusable (both are trait-shape-generic, not Eq/Ord-specific); only the
  codegen fold (§2) is per-trait and needs its own worked example at that time.
- `feat-mutual-rec`'s `buildLetRecMulti` (N-way tuple-of-thunks knot) lands → the forward/mutual
  impl-reference gap §3a leaves open (structurally unreachable from #109's own single-type fold,
  but a real gap for HAND-WRITTEN cross-impl programs) could close too, by swapping
  `wrapPendingKnots`'s chained `letRecS` for the mutual generalization — not required for #109,
  named here as the natural next step if a hand-written mutual-impl program is ever blocked on it.
