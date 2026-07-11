<!-- note-status: active -->
# Carrier-inference design — closing #55's result-position instantiation-discovery gap

> Design probe for issue #55 (annotation-free generic-data introduction) and ADR-0103's "Revisit
> if" line 3 ("annotation-free carrier inference is taken up, unblocking the constructing half").
> DESIGN-FIRST with a HOLD: this note is the deliverable, not an implementation — every claim below
> is witnessed live against the built binary (`.lake/build/bin/bang`, `feat-lang-fill` branch), not
> reasoned-only. No code changes ride with it.

## 0. The wall, precisely — narrower than #55's original framing

Issue #55 (2026-07, closed after the parser-combinator milestone) frames the gap as "a generic
combinator cannot construct generic data" and blames it entirely on ADR-0079's annotation-driven
introduction. **That framing is partially STALE** — live-probed here, not assumed:

```
probe                                    result (live, this branch)
──────────────────────────────────────────────────────────────────────────────────────────
Some(3)  (bare synth position, NO         3  — WORKS. `Some(x)`'s field type IS Int directly
enclosing annotation at all)                 (embVInst's fresh hole unifies against 3 : Int
                                              during checkSV's structural descent — ADR-0079's
                                              OWN mechanism already closes this case).
mapOpt : (Int -> Int) -> Option Int ->    type mismatch — unrelated to #55 (a monomorphic
  Option Int, calling Some(($f) x)        ascription can't be applied polymorphically; expected).
mapOpt : (a -> b) -> Option a -> Option   "'mapOpt': a use leaves a type variable unresolved
  b, calling Some(($f) x), BOTH the        — annotate the argument" — THE WALL, even WITH
  arg (Some(3) : Option Int) AND the       annotations present on both the argument and the
  whole call's result annotated            whole call's result.
```

So the SIMPLE case #55's title names ("a generic combinator cannot construct generic data") is
**already fixed** — `ADR-0079`'s check-mode/synth-mode split already lets a bare `Some(x)` infer
its element type from `x`'s own type when `x`'s type is directly evident. The REMAINING wall is
narrower and different in kind: **a bound-free `let rec`'s tyvar that appears ONLY in the
declared RESULT type (never in any argument's own type) cannot be discovered at all**, no matter
how the call site is annotated — because the discovery mechanism (ADR-0103's `monoCallSpine`/
`discoverAtCall`) only ever inspects argument positions, and the ONE place a result-position
tyvar's concrete instantiation could be recovered — an enclosing annotation ON THE CALL — is
structurally discarded before discovery ever runs.

## 1. The mechanism, traced to the exact line

`Bang/Frontend/TypeCheck.lean`'s `callSitesOf` (ADR-0103's discovery walk, called from
`monomorphizeOne`) has this arm:

```lean
| .annotS e t => callSitesOf name domains e
```

`t` — the annotation's own declared type — is **thrown away**; only the inner unannotated `e` is
walked. So `(($mapOpt f) o : Option Int)`'s outer `: Option Int` annotation is invisible to
`discoverAtCall` by construction, even though it is EXACTLY the information needed to close `b`
(`mapOpt : (a -> b) -> Option a -> Option b`'s result-position tyvar).

`discoverAtCall` itself only walks CURRIED ARGUMENT positions against `curriedDomains`:

```lean
def discoverAtCall (domains : List Ty) (args : List Surf) : List (String × Ty) :=
  (domains.zip args).flatMap (fun (dom, arg) => match arg with
    | .annotS _ concreteTy => matchTyVars dom concreteTy
    | _                    => [])
```

There is no RESULT-position twin — no `resultDomain`/`resultAnnotation` argument at all. The
underlying unifier (`matchTyVars : Ty → Ty → List (String × Ty)`) is already FULLY GENERAL
(recurses through `tArr`/`tProd`/`tSum`/`tApp`/`tThunk` uniformly) — it would happily unify
`Option b` against a caller-supplied `Option Int` if it were ever handed the pair. **The gap is
purely "nothing ever calls it on the result," not a unification-power limitation.**

`completeInstantiation tvs binding` (the caller) requires EVERY tyvar in the ascription's `tvs`
list to be covered before it accepts a call site — `b`, appearing only in the result, is
structurally unreachable from any argument-only discovery, so `completeInstantiation` can never
succeed for `mapOpt`-shaped signatures today, regardless of how many arguments are annotated.

## 2. Candidate mechanisms, priced

```
mechanism                          what it needs                              cost / risk
─────────────────────────────────────────────────────────────────────────────────────────────────
(A) Result-position discovery      `callSitesOf`'s `.annotS e t` arm STOPS     LOW mechanical
    at the CALL site               discarding `t` when `e`'s SPINE HEAD is    cost — `matchTyVars`
                                    exactly `name`'s own call (mirroring       already does the
                                    `monoCallSpine`'s own spine-recognition):  unification; only
                                    `discoverAtCall` gains a THIRD input       the plumbing (thread
                                    (the declared result type + the caller's  `t` down to
                                    annotation), unified via the SAME          `discoverAtCall`,
                                    `matchTyVars`. Requires `monoCallSpine`    add a result-domain
                                    to also report WHETHER `e` (the           param) is new.
                                    annotated expr) IS itself the call spine
                                    (not just descend past the annotation).
(B) Field-type inference at        Extend ADR-0079's ALREADY-WORKING          MEDIUM — the
    the ctor-intro site (the       check-mode/synth-mode split so a bound     mechanism this
    literal #55 reading)           polymorphic tyvar `b` used inside a        note's §0 shows is
                                    let-rec's OWN body construction can       ALREADY MOSTLY
                                    still resolve via unification against     SOLVED for the
                                    the CALLER's eventual instantiation —     monomorphic-body
                                    but this requires propagating a          case; the residual
                                    "pending hole" through the                need is specifically
                                    monomorphization pre-pass itself, since  bound-free `let rec`
                                    residues are built BEFORE `elabS`/       CONSTRUCTION, which
                                    `checkSV`'s hole-unification ever runs.  is (A)'s exact target.
(C) HM-style let-generalization    Generalize the LET RESULT to a real ∀,    REJECTED by
    (a genuine top-level scheme)   deferring monomorphization to EVERY       ADR-0103 itself
                                    downstream USE (not just the direct      (door (a), "a
                                    call spine).                             residual ∀-scheme
                                                                              in the self-knot" —
                                                                              polymorphic
                                                                              recursion,
                                                                              undecidable, R6 §4).
(D) Require the user to always     Status quo (the current error message's  ZERO cost, ZERO
    annotate at a DIFFERENT,       own suggestion) — no mechanism change.    genericity gain —
    argument-anchored call site                                             works ONLY when the
    (rewrite `mapOpt` to take an                                            tyvar ALSO appears
    extra witness argument, or                                              in SOME argument
    restructure so `b` also                                                 (not `mapOpt`'s own
    appears in an argument)                                                 shape) — the
                                                                             FALLBACK today, not
                                                                             a fix.
```

**(A) is the recommended door.** It is the SAME "one construct per problem" move ADR-0103 itself
made for argument-position discovery — extending `discoverAtCall`'s existing, already-general
`matchTyVars` machinery to a SECOND input (the call's own result annotation) rather than inventing
a parallel inference mechanism. (B) is a real alternative reading of #55's ORIGINAL title but is
strictly HARDER (needs the pre-pass to defer hole-resolution across the `elabS` boundary it
currently runs entirely before) and solves a problem (A) already solves as a side effect: once
`b`'s instantiation is discovered from the call's result annotation, `monomorphizeOne`'s EXISTING
`substTyVar`-closing machinery closes `b` everywhere in the residue's body — including inside
`Some(($f) x)`'s construction — with ZERO change to the ctor-elaboration path itself (ADR-0079's
own mechanism, confirmed already working for a closed tyvar, §0's `Some(3)` witness).

## 3. What (A) must NOT do (the hard constraints this design respects)

- **No kernel `∀`.** (A) stays entirely within the existing tested-superset Frontend pre-pass
  (`Bang/Frontend/TypeCheck.lean`'s `monomorphizeLetRec`/`callSitesOf`/`discoverAtCall` mutual
  group) — the kernel / `Source.eval` / `HasCTy` never see a type variable, unchanged from
  ADR-0075/0079/0103's own invariant. `matchTyVars`'s output is consumed exactly like an
  argument-discovered binding is today: `substTyVar`-closed into a concrete residue BEFORE `elabS`
  ever runs.
- **No full HM at the mono pre-pass.** (A) does NOT generalize-then-instantiate (door (a)/(c),
  REJECTED by ADR-0103 for the self-knot's polymorphic-recursion undecidability). It stays a
  FINITE, per-call-site DISCOVERY step — the same R6 finiteness discipline every other
  monomorphization in this codebase already rides (a call site with NO annotation anywhere
  reachable — neither an argument nor the result — still fails LOUD with the existing "annotate"
  message, never a guess; (A) only widens WHERE an annotation may legally live, not whether one is
  required).
- **No silent multi-candidate resolution.** If a call site's argument annotations AND its result
  annotation DISAGREE on a shared tyvar's instantiation (a malformed/contradictory program), (A)
  must fail loud naming BOTH sources, not silently prefer one — `completeInstantiation`'s existing
  "every discovered binding for the same tyvar across the call's own bindings must agree" check
  (implicit today in how `discoverAtCall`'s flatMap accumulates — untested for a genuine conflict
  case, a gap this note flags for whoever implements (A) to close with a `#guard`, not something
  this note claims is already handled).
- **Does not touch `Bang/Core`.** Purely a Frontend-leaf change (`callSitesOf`'s `.annotS` arm +
  `discoverAtCall`'s signature), matching this session's #144 items' own leaf discipline.

## 4. Witnesses this note's claims rest on (reproducible)

```bang
-- W1 — the ALREADY-FIXED simple case (§0 row 1): bare Some(3) in synth position.
match (Some(3)) { None -> 0, Some(v) -> v }
-- -> 3

-- W2 — a MONOMORPHIC map (unrelated to #55; confirms the wall is genericity-specific, not
-- generic-construction-specific in general).
let rec mapOpt : (Int -> Int) -> Option Int -> Option Int =
  fun f => fun o => match o { None -> None, Some(x) -> Some(($f) x) }
in
match (($mapOpt (fun n => n + 1)) (Some(3) : Option Int)) { None -> 0, Some(v) -> v }
-- -> "error: type mismatch" (expected — a monomorphic ascription can't apply polymorphically)

-- W3 — the WALL: a genuinely polymorphic map, BOTH argument and result annotated.
let rec mapOpt : (a -> b) -> Option a -> Option b =
  fun f => fun o => match (o : Option a) { None -> None, Some(x) -> Some(($f) x) }
in
match (($mapOpt (fun n => n + 1)) (Some(3) : Option Int) : Option Int) { None -> 0, Some(v) -> v }
-- -> "error: 'mapOpt': a use leaves a type variable unresolved — annotate the argument
--     (e.g. `(mapOpt arg : List Int)`) so ADR-0103's monomorphization pass can close it"
```

W3's error message is itself evidence of the gap's exact shape: it suggests annotating "the
argument" — but `b` is NOT AN ARGUMENT tyvar; no argument annotation could ever close it. The
message is honest about failing loud (never a guess) but currently cannot suggest the CORRECT fix
(annotate the call's own result) because that door doesn't exist yet.

## 5. Verdict

STOP-and-SHOW per the assignment's hold point — this note is the deliverable. (A) — result-
position discovery, threading the call site's own `.annotS` annotation into `discoverAtCall` as a
second, RESULT-domain-matched input — is the recommended door: mechanically small (a few lines in
`callSitesOf`'s `.annotS` arm + `discoverAtCall`'s signature), reuses the fully-general
`matchTyVars` unifier that already exists, requires no kernel change, and closes #55's remaining
scope (ADR-0103's own named "Revisit if" condition) without reopening the "one construct per
problem" question ADR-0103 already settled for argument-position discovery. Implementation is
NOT started; awaiting ack or redirect before proceeding.
