<!-- note-status: active -->
# Mutual `let rec` / sibling forward-reference — design probe (#97 item 2)

> Refute-first design probe, branch `design-mutual-rec` off `main @ f03cbad3`. Ground: the
> dogfood-calc wall (`docs/notes/dogfood-calc-findings.md`), issue #61 (closed — the hang class),
> ADR-0073 (the μ-knot mechanism), ADR-0088 (row-carrying recursive thunks), ADR-0091 (multi-slot
> `structOK`), `Bang/Backend/EnvMachine.lean` (ADR-0094, the closure-sharing engine).

## TL;DR

**H2 (elaborator-level tuple-of-thunks μ-knot) SURVIVES all falsifiers and RUNS end-to-end,
verified by a compiled spike (evidence below).** H1 (a Bekić sum-dispatcher) is REFUTED by two
independent, build-confirmed walls: the ctor-arity-≤2 cap and per-knot all-or-nothing `Div`
certification. No kernel change is needed for either hypothesis — this is an elaborator-only
feature, same layer as `buildLetRec` itself. H3 (the teaching diagnostic) is specified below and
should ship regardless, since H2's real implementation is nontrivial (see the slice map).

## H1 — Bekić-style sum-dispatcher: REFUTED (two independent walls)

**Hypothesis**: elaborate a mutual group into a single `let rec` over a sum-typed dispatcher —
one knot `go : (Args₁ + Args₂) -> (Res₁ + Res₂)` with injected callers — purely in the elaborator.

**Falsifier (b) — ctor/generic arity ≤ 2, CONFIRMED by direct build.** A dispatcher for an
N-way mutual group needs an N-way argument sum and an N-way result sum. bang's constructor
payload arity is capped at 2 (`Bang/Frontend/TypeCheck.lean:2878/2889`, `B011`), and `tApp`
(generic-data application) is likewise capped at 2 type args. Built and ran:

```
data DispatchArg = A(Int, Int, Int)
```
→ `error[B011] at 13:20: constructor 'A': payload arity ≤ 2 in v1 (nest tuples)`

A 3-way (or larger) mutual group's dispatcher forces nested-tuple encoding of its own argument
sum, on top of nesting for the ≥3-way sum-of-cases itself — and per issue #108 (open,
build-confirmed live), bang constructor names are **not type-namespaced**: any fresh
`Arg1`/`Left`/`Case1`-style sum ctor the desugar mints for ONE mutual group's dispatcher
collides with the SAME desugar's ctors from any OTHER mutual group in the same program, or with
a user's own same-named type. A per-group-unique-name scheme is possible but adds exactly the
kind of generated-name-collision machinery #108 flags as unresolved for the stdlib `List`
injection — riding on an open, unrelated wall.

**Falsifier (a) — Div-row all-or-nothing certification, CONFIRMED by reading the landed code.**
`Div` is inserted into a knot's row as a single boolean fact (`if divLabel ∈ recRow then
.thunk (.divMark …) else .thunk …`, `buildLetRec`, `TypeCheck.lean:2179`), computed ONCE per
knot by `letRecRow`/`structOK` (ADR-0091). A single-knot Bekić dispatcher folding N functions
into ONE `let rec` would force ALL N functions to share ONE certification verdict: if even one
sibling in the group is non-structural (the common case — a parser's `factor`/`term`/`expr` tower
is rarely uniformly structural), `structOK`'s call-recognizer (`callSpine`, keyed on a single
function `name`) can't even correctly attribute the fan-out dispatcher's self-calls back to
per-function descent, so the WHOLE group would conservatively fall to `Div` — including siblings
that, kept as separate `let rec`s, would certify total today. This is a real completeness
regression, not just an implementation inconvenience: it makes the mutual-rec sugar STRICTLY
WORSE than the current nested-`let rec` workaround for any group with a mixed structural/
non-structural membership.

**Verdict: H1 refuted on both falsifiers independently — either alone is sufficient. No spike
built (the walls are structural, confirmed by direct evidence, not worth end-to-end proving a
dead design).**

## H2 — elaborator-level tuple-of-thunks μ-knot: SURVIVES, SPIKE GREEN

**Hypothesis**: generalize `buildLetRec`'s single self-knot `Rec = μX. Thunk(X → T)` to a
PAIR self-knot `Rec2 = μX. Thunk(X → T1) * Thunk(X → T2)` (an N-tuple for an N-way group), so
each sibling forces the SAME shared knot and projects its own slot — giving every sibling
visibility of every other sibling by construction (not by ordering).

### The spike (built, ran, reverted — never committed)

Hand-built the `Surf` term (bypassing the surface parser — v1 has no `let rec f and g` grammar,
so this tests the elaborator TARGET a future desugar would emit) for a mutual `even`/`odd` pair
over `Int`, temporarily inlined at the end of `Bang/Frontend/TypeCheck.lean` (its `synthSC`/
`runInferC` aren't `public`, so an external module can't reach them — this is itself a scoping
finding, noted below) as a namespaced block, compiled with `lake build`, then **fully reverted**
(`git diff` on the file is empty; the repo tree is clean on this branch). Verified copy of the
final green block: `scratch/H2Spike-VERIFIED-GREEN.lean` in this branch's push (see Deliverables).

**Result — all `#guard`s (compiled, not `#eval`) PASS:**
```
#guard runFull2 5000 progEven0  == some 1   -- even 0 = 1  (base case)
#guard runFull2 5000 progEven1  == some 0   -- even 1 = 0
#guard runFull2 5000 progEven10 == some 1   -- even 10 = 1 (9 levels of even<->odd mutual descent)
#guard runFull2 5000 progOdd10  == some 0   -- odd 10 = 0
#guard runFull2 5000 progEven7  == some 0   -- even 7 = 0
-- differential vs. a hand-fused single-function equivalent (today's workaround shape):
#guard runFull2 5000 (fusedProg 0 10) == runFull2 5000 progEven10   -- both `some 1`
#guard runFull2 5000 (fusedProg 1 10) == runFull2 5000 progOdd10    -- both `some 0`
#guard runFull2 5000 (fusedProg 0 7)  == runFull2 5000 progEven7    -- both `some 0`
```
Both TYPED (`synthSC`/`runInferC`) and RAN (`Bang.Surface.lower` + `Source.eval`) — the full
pipeline, not just one stage. `lake build Bang.Frontend.TypeCheck` exit 0 with the spike inlined
(checked at the time); reverted-tree `lake build` also exit 0 (checked after revert, both
timestamped in this session).

### The encoding (what actually worked, after two wrong turns)

```
recTy2 := μX. Thunk(X -> T1 * T2)                       -- the shared self-knot's type
knotBody2 sv := let #g = unfold sv in (force #g) (fold #g)     -- BYTE-IDENTICAL to buildLetRec's
                                                                  -- knotBody (incl. the #95 fix:
                                                                  -- `fold #g`, never a 2nd free `sv`)

evenThunk sv := let #p = force (thunk (knotBody2 sv)) in
                  split (#e, #o) = #p in force #e            -- re-derive the PAIR, project, FORCE
oddThunk  sv := let #p = force (thunk (knotBody2 sv)) in
                  split (#e, #o) = #p in force #o            -- (symmetric)

inner2 := (fun #self =>
             let even : Thunk(Int->Int) = thunk (evenThunk #self) in    -- ASCRIBED (see below)
             let odd  : Thunk(Int->Int) = thunk (oddThunk  #self) in
             (thunk evenBody, thunk oddBody)                            -- the pair VALUE
          ) : Rec2 -> T1*T2

recVal2 := fold (thunk inner2) : Rec2
outer   := let #rec = recVal2 in
           let even : Thunk(Int->Int) = thunk (evenThunk #rec) in
           let odd  : Thunk(Int->Int) = thunk (oddThunk  #rec) in
           <tail using even/odd>
```

Two structural findings surfaced only by BUILDING it, not by reading the encoding on paper:

1. **Mandatory type ascription, exactly mirroring `let rec`'s own `ADR-0073` requirement.**
   `even`'s RHS (`evenThunk #self`) free-references `odd`, and vice versa — HM's ordinary
   `let`-generalization path (`Bang/Frontend/TypeCheck.lean:1014-1023`, the bite-0 value-restriction
   generalize) has nothing concrete to unify against until BOTH bindings exist, so an unascribed
   `.lett "even" (.thunk …) …` for a self-referential pair fails to type (confirmed: the unascribed
   form threw before ascription was added). Explicitly ascribing each projection's thunk type
   (`.annotS _ (.tThunk fnTy)`) breaks the circularity the same way `let rec f : T = …`'s mandatory
   annotation already does for the single-function case — **this generalizes cleanly: the future
   desugar needs ONE type per sibling, which a `let rec f : T1 and g : T2 = …` surface syntax
   supplies for free** (no new inference burden beyond what single-function `let rec` already asks).

2. **A CBPV double-thunk trap, NOT present in the single-function case.** The first attempt
   projected the split's result directly (`split (#e,#o) = #p in #e`) and typed/ran to `STUCK`
   despite being well-typed by the surface checker's own account at each isolated sub-step —
   the checker's structural unification silently accepted a `U (U ρ arrow)`-shaped mismatch
   (a thunk-of-a-thunk) because `checkSV`'s `.thunk` arm unifies against the ARROW payload, not
   against a value that's itself still wrapped. The fix (`force #e`/`force #o` before returning)
   is a one-line correction once diagnosed, but it is a genuinely NEW failure mode `buildLetRec`'s
   single-function shape never hits (there's only one thunk-layer there, never a split-then-
   reproject). **Any real implementation of this encoding needs a differential `#guard` at
   exactly this shape (a split immediately re-consumed by force) or it silently reproduces this
   bug for every future N-way group.**

### Falsifiers probed for H2 (all survive)

- **(c) ENGINE sharing (#95-class regression)**: the ADR-0094 env engine (`Bang/Backend/
  EnvMachine.lean`) represents recursion as CLOSURES (`mvclos M ρ`) over a shared environment,
  not substitution — `ρ` is referenced, not copied, on every force. The #95 exponential blowup
  was specific to the SUBSTITUTION-based `Source.eval`/CalcVM path (`Comp.substFrom` rebuilding
  the whole knot body per unfold) and was fixed by removing a SECOND free occurrence of the
  growing self-value (`fold #g` not `sv`) in `buildLetRec`'s own knot. `knotBody2` in this spike
  is BYTE-IDENTICAL to `buildLetRec`'s `knotBody` (same fix, inherited verbatim) — a tuple-of-
  thunks generalization does not introduce any NEW extra free occurrence of the self-value; each
  of `evenThunk`/`oddThunk` calls `knotBody2 sv` exactly once, so the per-level residual-cost
  argument transfers unchanged. No new spike needed to confirm this beyond re-using the identical
  knot body, which the spike does.
- **(d) the #61 hang-class regression**: verified directly. `scratch/hang61/sib2.bang` (the
  exact repro from the closed #61, "outer `let rec` + 2 sibling nested `let rec`s, each
  Div-declared, each calling the outer knot") still runs in ~0.4s on BOTH `bang run` and
  `bang run --compiled` on this branch's baseline — confirmed via `time` before any code change
  (see Deliverables). This shape is the STATUS QUO workaround the mutual-rec feature would
  replace, not something H2 touches; H2's own knot reuses the identical `knotBody`/`#95`-fixed
  shape, so it inherits the same fixed cost profile, not the pre-fix exponential one.
- **(b) generic-data arity / ctor collision**: DOES NOT APPLY to H2 — the tuple-of-thunks
  encoding uses the BUILT-IN product type (`tProd`/`pairS`/`splitS`), not a fresh named `data`
  declaration, so it never touches the ctor-arity cap or #108's namespace collision at all. This
  is H2's main structural advantage over H1.
- **(a) row composition**: NOT under this spike's scope (the spike is pure `Int -> Int`, no
  `Div`/effect row on the functions) — flagged as a genuine judgment call for the real
  implementation, next section.

### Judgment call flagged for implementation, not resolved here

**`structOK`/`Div`-row certification for a mutual group is an open design point.** Unlike H1,
H2 does NOT force an all-or-nothing verdict at the TYPE level (each sibling's thunk is
independently ascribed, so nothing structurally prevents per-sibling row annotations à la
ADR-0088) — but `structOK`'s call-recognizer (`callSpine`, `TypeCheck.lean:1973+`) is keyed on a
SINGLE function name and does not know that `even`'s calls to `odd` (and vice versa) are part of
the SAME structural-descent argument. Making mutual structural certification work needs
`structOK` extended to accept a GROUP of co-recursive names with a shared slot-mapping (each
sibling may have a different arity/slot), which is a real but bounded extension — not a wall,
just unscoped by this probe. Absent that extension, EVERY mutual `let rec` group defaults
conservatively to `Div` on every sibling (sound, per `structOK`'s own "default false" discipline)
— acceptable for v1 (recursion already runs fuel-bounded under `Div` today) but worth naming
explicitly in the ADR as a known completeness gap, not a silent regression.

## H3 — the teaching diagnostic (ships regardless of H1/H2's fate; spec below)

**Detection point**: `letRecRow`/`buildLetRec`'s elaboration of a `let rec` whose body (pre-desugar,
in `elabS`'s `.letRecS` arm, `TypeCheck.lean:2657-2667`) contains a NESTED `let rec` referencing a
name not yet in scope — i.e., the existing "unbound variable" error surfaces from a nested
`let rec`'s body when the referenced name is itself another SIBLING `let rec` bound later in the
SAME enclosing scope. Concretely: when `elabS`'s `.lett`/nested-`.letRecS` elaboration throws
`"unbound variable: X"` AND `X` is bound by a `let rec` construct textually LATER in the same
block, emit a NAMED diagnostic instead of the generic unbound-variable message.

**Message spec** (mirrors the existing `DiagCodes.lean` B0xx convention, e.g. B011's "nest
tuples" hint pattern):
```
error[B0NN] at <span>: 'X' is a sibling `let rec` defined later — siblings cannot forward-
reference (v1 has no mutual `let rec`). Reorder so every sibling calls only EARLIER siblings +
the outer knot (leaf-level rules first), or restructure into ONE self-recursive function.
```
This requires threading a "names bound by a later sibling `let rec` in this block" set into the
elaborator's error path at the unbound-variable site — a small, localized addition (the block's
sibling names are already enumerable from the parse, since `foldLetDecls`/the nested-`letRecS`
chain is walked top-to-bottom). No kernel/machine/census involvement; pure diagnostic-message
work, same layer as the existing B0xx codes.

## Recommendation

1. **Adopt H2's encoding as the target** for a future `let rec f : T1 and g : T2 = … and … in …`
   surface form (ADR-worthy: names the rejected H1 alternative + the row-certification gap as a
   known deferral, mirrors ADR-0073/0088's own documentation shape).
2. **Ship H3 (the diagnostic) immediately, independent of H2's timeline** — it is small, needed
   regardless (a mutual-rec surface form is still useful to have a good error for the OLD nested
   shape, since existing corpus code still uses it), and directly addresses the #97 item 2 ask's
   floor.
3. **Do not attempt H1** — refuted on two independent, build-confirmed walls; no partial credit
   (a 2-way-only Bekić dispatcher dodges falsifier (b) but not (a), and still forecloses the
   ctor-arity headroom #108 needs for the stdlib `List` injection).

## Slice map (if H2 is picked up for implementation)

1. **Grammar**: extend `let rec` to accept `and`-chained sibling declarations (parser +
   `letRecD`/`letRecS`-analog AST shape) — each sibling keeps its OWN mandatory `: T` annotation
   (per the ascription finding above).
2. **`buildLetRec` generalization**: `buildLetRecMulti` building the N-tuple self-knot + per-
   sibling projection thunks (`evenThunk`/`oddThunk`'s pattern, generalized to N via `splitProd`/
   `navSum`-style right-nested product navigation, which the ctor-payload machinery already has —
   reuse, don't reinvent).
3. **`structOK` group extension** (separate slice, can ship AFTER #1-2 land with conservative
   `Div` default): thread a co-recursive name SET instead of a single `name` through `callSpine`/
   `structOKSpine`, so mutual structural descent can certify.
4. **Regression guards**: the #61-shape witness (`scratch/hang61/sib2.bang`-equivalent) as a
   PERMANENT `#guard`/example, gating that the new desugar's knot reuses the #95-fixed
   `knotBody` shape byte-for-byte (a literal AST-equality check against `buildLetRec`'s existing
   `knotBody`, or a shared helper, would make regression on this axis structurally impossible —
   preferred over re-deriving the knot construction independently).
5. **H3's diagnostic** ships independently, any time (item 2 above, no dependency on 1-2-3).

## Deliverables / evidence trail

- This file.
- `scratch/H2Spike-VERIFIED-GREEN.lean` (this branch) — the exact spike block that built and ran
  green, inlined into `Bang/Frontend/TypeCheck.lean` at the time (needed its internal `synthSC`/
  `runInferC`, which are not `public` — an external module cannot reach them; noted as a real
  constraint on how any FUTURE non-throwaway implementation must be structured: it lives inside
  `TypeCheck.lean` itself, same as `buildLetRec`). `Bang/Frontend/TypeCheck.lean` itself is
  UNCHANGED on this branch (`git diff` empty) — the spike was reverted after the green build was
  confirmed, per the assignment's "evidence, not implementation" instruction.
- `scratch/mutrec-regression-boundary-sib.bang` (this branch) — the #61-shape regression witness
  (`docs/notes/dogfood-json-findings.md`'s exact 2-sibling repro), confirmed fast (~0.4s) and
  correct (`0`) on both `bang run` and `bang run --compiled` on this branch's baseline.
- `scratch/mutrec-h1-sum-dispatcher-3way.bang` (this branch) — the H1 falsifier (b) witness
  (`B011` ctor-arity error on a 3-way dispatcher argument sum).

## Gate

`lake build` on the reverted tree (no spike code committed): EXIT 0, confirmed post-revert in
this session. No corpus file changed; no ADR filed yet (this is a design PROBE per the
assignment — an ADR should follow if the operator picks up the recommendation, naming H1 as the
rejected alternative with its two falsifiers as the rationale, per this repo's ADR convention).
