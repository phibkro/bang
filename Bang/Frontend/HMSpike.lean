/-
  Bang/Frontend/HMSpike.lean — bite-0 de-risk SPIKE for the polymorphism initiative.
  ─────────────────────────────────────────────────────────────────────────────────
  ADR-0075 asks: does HM inference (unification + let-generalization) land on the
  bidirectional surface checker with the kernel UNTOUCHED? This module answers it on
  the PURE FUNCTION fragment (`id`/`const`, no effects, no generic data) — a
  self-contained Algorithm-W core over `Surf`, exactly the shape a full integration
  would fold into `synthSC`/`synthSV`.

  The elaborate-to-mono claim (ADR-0075 decision 1) is trivial here: `Source.eval` is
  UNTYPED, so a polymorphic term ERASES to its ordinary kernel term and runs directly.
  HM is therefore a pure TYPE-CHECKING phenomenon — the run reuses the existing untyped
  `Surface.parse ∘ lower ∘ Source.eval` pipeline unchanged. So the #guards below are two
  claims per program: (a) it TYPES under HM, (b) the erased term RUNS to the right value.

  A LEAF (nothing in `Bang/` imports it; census untouched), like `TypeCheck.lean`.

  WHY a separate module and not an in-place edit of `synthSC`: the existing checker is
  pure `Except String` over the KERNEL `VTy`/`CTy` with STRUCTURAL equality (`A = expected`)
  — it has no metavariable notion and no unification state. HM needs both. This spike
  proves the mechanism in isolation (à la the recursion spike) so the integration cost
  is a measured finding, not a guess. See the FINDING block at the bottom.
-/
module

-- #guards run the compiled inference (this module) + `runYieldsInt` (Source.eval) at the
-- META phase → meta imports, mirroring TypeCheck.lean's cross-module #guard wall.
meta import Bang.Frontend.Surface
meta import Bang.Core.Semantics
public import Bang.Frontend.Surface

namespace Bang.HMSpike
open Bang
open Bang.Surface

/-! ## 1. Inference types — the KERNEL `VTy`/`CTy` collapsed to one tree, plus HOLES.

`HTy` mirrors the pure CBPV fragment (value: int·unit·prod·sum·`u`=U; computation: `f`=F·`arr`)
in ONE inductive so unification/zonk/occurs are single recursions. The two additions HM needs and
the kernel forbids are `meta` (a unification hole, ADR-0075's "unification-variable notion") and
`rigid` (a ∀-bound scheme variable — DISTINCT from `Surface.Ty.tVar`, the μ-internal de Bruijn var
the task warned against reusing). Both live ONLY in the checker; neither reaches the kernel. -/
inductive HTy where
  | int  : HTy
  | unit : HTy
  | prod : HTy → HTy → HTy
  | sum  : HTy → HTy → HTy
  | u    : HTy → HTy            -- U C : a thunk (suspended computation) value
  | f    : HTy → HTy            -- F A : a returner computation
  | arr  : HTy → HTy → HTy      -- A → C : a function computation
  | hole : Nat → HTy            -- a unification hole (?n) — checker-only
  | rigid : Nat → HTy           -- a ∀-bound scheme variable — checker-only (≠ Surface.Ty.tVar)
  deriving Repr, Inhabited, DecidableEq

/-- A type scheme `∀ (arity vars). body`, where the bound variables are `rigid 0 … arity-1`
(de-Bruijn-ish; instantiation maps each `rigid i` to a fresh `meta`). A MONOMORPHIC binding
(a lambda parameter) is `⟨0, τ⟩` — no quantification, so instantiation returns `τ` unchanged.
This is the ONLY place let-polymorphism lives: `let` generalizes, `fun` does not. -/
structure Scheme where
  arity : Nat
  body  : HTy
  deriving Repr, Inhabited

/-- A monomorphic scheme (a lambda parameter / a not-yet-generalized binding). -/
@[inline] def mono (t : HTy) : Scheme := ⟨0, t⟩

/-- The named typing environment: like the checker's `NCtx`, but binds SCHEMES (so `let`-bound
names can be polymorphic). -/
abbrev Env := List (String × Scheme)


/-! ## 2. The inference monad — fresh-variable supply + substitution.

The existing checker is pure `Except String`; HM needs THREADED STATE (a fresh counter + the
metavariable substitution). `StateT St (Except String)` is that thread. This is the one structural
change an in-place integration forces: every `synth*/check*` arm gains this monad. -/
structure St where
  next  : Nat                    -- fresh-metavariable counter
  subst : List (Nat × HTy)       -- metavariable ⇒ type bindings (association list; fine at spike scale)

abbrev Infer := StateT St (Except String)

/-- All recursions below are FUEL-driven total (the repo idiom — see the parser/tokenizer): a
substitution has no cycles once occurs-check holds, but Lean can't see that, so fuel bounds every
walk. Generous — it never bites a well-formed program (the `next` counter tops out in the dozens). -/
def bigFuel : Nat := 1000000

/-- Mint a fresh unification hole. -/
def freshHole : Infer HTy := modifyGet (fun st => (.hole st.next, { st with next := st.next + 1 }))

/-- Bind metavariable `n` to `t` (the unification "assign"). -/
def bindHole (n : Nat) (t : HTy) : Infer Unit :=
  modify (fun st => { st with subst := (n, t) :: st.subst })

/-- Look through the substitution ONE hop at the top (find the current binding of a hole). -/
def lookupHole (n : Nat) : Infer (Option HTy) := do return (← get).subst.lookup n

/-- Resolve the TOP of a type: follow the metavariable chain until a non-bound head. -/
def resolve (fuel : Nat) (t : HTy) : Infer HTy := do
  match fuel, t with
  | 0,      t        => return t
  | fu + 1, .hole n  => match (← lookupHole n) with
                        | some t' => resolve fu t'
                        | none    => return (.hole n)
  | _,      t        => return t

/-- FULLY apply the substitution (deep): resolve at every node. Used before occurs-check,
generalization, and display. -/
def zonk (fuel : Nat) (t : HTy) : Infer HTy := do
  match fuel with
  | 0      => return t
  | fu + 1 =>
    let t ← resolve (fu + 1) t
    match t with
    | .prod a b => return .prod (← zonk fu a) (← zonk fu b)
    | .sum  a b => return .sum  (← zonk fu a) (← zonk fu b)
    | .u a      => return .u    (← zonk fu a)
    | .f a      => return .f    (← zonk fu a)
    | .arr a b  => return .arr  (← zonk fu a) (← zonk fu b)
    | other     => return other

/-- Does hole `n` occur in `t`? (Run on a ZONKED `t`, so bound holes are already expanded.)
Structural + total — the occurs-check that makes an infinite type a fail-loud ERROR, not a hang. -/
def occursIn (n : Nat) : HTy → Bool
  | .hole m   => n == m
  | .prod a b => occursIn n a || occursIn n b
  | .sum  a b => occursIn n a || occursIn n b
  | .u a      => occursIn n a
  | .f a      => occursIn n a
  | .arr a b  => occursIn n a || occursIn n b
  | .int | .unit | .rigid _ => false

/-- Unify two types, extending the substitution (the MGU contract is DIFFERENTIAL-tested per
CLAUDE.md, not proven — soundness = the elaborated term still runs). Occurs-check fails LOUD. -/
def unify (fuel : Nat) (a b : HTy) : Infer Unit := do
  match fuel with
  | 0      => throw "unify: out of fuel"
  | fu + 1 =>
    let a ← resolve (fu + 1) a
    let b ← resolve (fu + 1) b
    match a, b with
    | .hole n, .hole m => if n == m then return () else bindHole n (.hole m)
    | .hole n, t       => if occursIn n (← zonk (fu + 1) t) then
                            throw "occurs check: cannot construct an infinite type"
                          else bindHole n t
    | t, .hole n       => if occursIn n (← zonk (fu + 1) t) then
                            throw "occurs check: cannot construct an infinite type"
                          else bindHole n t
    | .int, .int   => return ()
    | .unit, .unit => return ()
    | .prod a1 a2, .prod b1 b2 => do unify fu a1 b1; unify fu a2 b2
    | .sum  a1 a2, .sum  b1 b2 => do unify fu a1 b1; unify fu a2 b2
    | .u a1, .u b1   => unify fu a1 b1
    | .f a1, .f b1   => unify fu a1 b1
    | .arr a1 a2, .arr b1 b2 => do unify fu a1 b1; unify fu a2 b2
    | _, _ => throw "type mismatch"


/-! ## 3. Generalization + instantiation — the HEART of HM (the two moves the `let` arm makes). -/

/-- The free metavariables of a (zonked) type, left-to-right, no dedup. -/
def freeHoles : HTy → List Nat
  | .hole n   => [n]
  | .prod a b => freeHoles a ++ freeHoles b
  | .sum  a b => freeHoles a ++ freeHoles b
  | .u a      => freeHoles a
  | .f a      => freeHoles a
  | .arr a b  => freeHoles a ++ freeHoles b
  | .int | .unit | .rigid _ => []

/-- Replace each `meta m` (for `m` in `ms`) with `rigid (its index in ms)`; other holes stay. -/
def abstractHoles (ms : List Nat) : HTy → HTy
  | .hole m   => match ms.idxOf? m with | some i => .rigid i | none => .hole m
  | .prod a b => .prod (abstractHoles ms a) (abstractHoles ms b)
  | .sum  a b => .sum  (abstractHoles ms a) (abstractHoles ms b)
  | .u a      => .u    (abstractHoles ms a)
  | .f a      => .f    (abstractHoles ms a)
  | .arr a b  => .arr  (abstractHoles ms a) (abstractHoles ms b)
  | t         => t

/-- Replace each `rigid i` with `insts[i]` (instantiation's fresh holes); out-of-range stays rigid. -/
def instRigids (insts : List HTy) : HTy → HTy
  | .rigid i  => insts.getD i (.rigid i)
  | .prod a b => .prod (instRigids insts a) (instRigids insts b)
  | .sum  a b => .sum  (instRigids insts a) (instRigids insts b)
  | .u a      => .u    (instRigids insts a)
  | .f a      => .f    (instRigids insts a)
  | .arr a b  => .arr  (instRigids insts a) (instRigids insts b)
  | t         => t

/-- GENERALIZE `t` against `env`: quantify over the holes free in `t` but NOT free in `env` (those
are still "in flight" elsewhere and must stay monomorphic). This is the whole reason `let id = …`
becomes `∀a. …` while a lambda parameter does not. -/
def generalize (env : Env) (t : HTy) : Infer Scheme := do
  let tz ← zonk bigFuel t
  let mut envHoles : List Nat := []
  for (_, s) in env do
    let bz ← zonk bigFuel s.body
    envHoles := envHoles ++ freeHoles bz
  let genHoles := (freeHoles tz).filter (fun m => !envHoles.contains m) |>.eraseDups
  return ⟨genHoles.length, abstractHoles genHoles tz⟩

/-- INSTANTIATE a scheme: a fresh hole for every quantified variable, at EACH use site (so two uses
of `id` get INDEPENDENT holes — the polymorphism). -/
def instantiate (s : Scheme) : Infer HTy := do
  let mut insts : List HTy := []
  for _ in List.range s.arity do
    insts := insts ++ [← freshHole]
  return instRigids insts s.body


/-! ## 4. Algorithm W over `Surf` (the pure fragment).

`inferV` reads a `Surf` as a VALUE (returns its value `HTy`), `inferC` as a COMPUTATION — the same
value/computation split as the real `synthSV`/`synthSC`. A lambda invents a FRESH domain hole (the
move the current checker can't make → its "annotate the fun" error); `let` GENERALIZES its RHS.
Only the constructs the pure `id`/`const` fragment needs are handled; anything else fail-louds
(out of the bite-0 scope, NOT a silent pass). -/
mutual
def inferV : Nat → Env → Surf → Infer HTy
  | 0,      _,   _ => throw "infer: out of fuel"
  | fu + 1, env, e => match e with
    | .lit _     => return .int
    | .unitS     => return .unit
    | .var x     => match env.lookup x with
                    | some s => instantiate s
                    | none   => throw s!"unbound variable {x}"
    | .thunk b   => do return .u (← inferC fu env b)
    | .pairS a b => do return .prod (← inferV fu env a) (← inferV fu env b)
    | _          => throw "not a value (pure-fragment spike)"

def inferC : Nat → Env → Surf → Infer HTy
  | 0,      _,   _ => throw "infer: out of fuel"
  | fu + 1, env, e => match e with
    | .lit _   => return .f .int
    | .unitS   => return .f .unit
    | .var x   => match env.lookup x with
                  | some s => do return .f (← instantiate s)   -- a variable in comp position = `ret`
                  | none   => throw s!"unbound variable {x}"
    | .thunk b   => do return .f (.u (← inferC fu env b))       -- a thunk value in comp position = `ret`
    | .pairS a b => do return .f (.prod (← inferV fu env a) (← inferV fu env b))
    | .force b => do
        let t ← inferV fu env b
        let c ← freshHole
        unify bigFuel t (.u c)                                  -- b : U c
        return c
    | .lam x b => do
        let a ← freshHole                                       -- the FRESH domain — HM's key move
        let c ← inferC fu ((x, mono a) :: env) b                -- param is MONO (not generalized)
        return .arr a c
    | .app fn arg => do
        let tf ← inferC fu env fn
        let a ← freshHole; let c ← freshHole
        unify bigFuel tf (.arr a c)                             -- callee : a → c
        let ta ← inferV fu env arg
        unify bigFuel ta a                                      -- argument : a
        return c
    | .lett x rhs body => do
        let tr ← inferC fu env rhs
        let a ← freshHole
        unify bigFuel tr (.f a)                                 -- RHS is a returner `F a`
        let sch ← generalize env a                             -- ← GENERALIZE (the heart of HM)
        inferC fu ((x, sch) :: env) body
    | .splitS x y p body => do
        let tp ← inferV fu env p
        let a ← freshHole; let b ← freshHole
        unify bigFuel tp (.prod a b)
        inferC fu ((y, mono b) :: (x, mono a) :: env) body
    | .binopS op a b => do
        let ta ← inferV fu env a; unify bigFuel ta .int
        let tb ← inferV fu env b; unify bigFuel tb .int
        match op with
        | .lt | .eq => return .f (.sum .unit .unit)            -- comparisons → Bool = 1+1
        | _         => return .f .int
    | _ => throw "computation out of the pure-fragment spike (effects/data are later bites)"
end

/-! ## 5. Entry points + display. -/

/-- Render an `HTy` for the finding (rigids as `'a`, `'b`, …; holes as `?n`). -/
def showHTy : HTy → String
  | .int      => "Int"
  | .unit     => "Unit"
  | .prod a b => s!"({showHTy a} * {showHTy b})"
  | .sum  a b => s!"({showHTy a} + {showHTy b})"
  | .u a      => s!"Thunk {showHTy a}"
  | .f a      => s!"F {showHTy a}"
  | .arr a b  => s!"({showHTy a} -> {showHTy b})"
  | .hole n   => s!"?{n}"
  | .rigid i  => s!"'{Char.ofNat (97 + i)}"

/-- Parse + HM-infer a source string (as a computation), returning the ZONKED type or an error. -/
def hmType (src : String) : Except String HTy := do
  let e ← Bang.Surface.parse src
  match (do let t ← inferC bigFuel [] e; zonk bigFuel t) ⟨0, []⟩ with
  | .ok (t, _) => .ok t
  | .error m   => .error m

/-- Did it type? -/
def hmOk (src : String) : Bool := match hmType src with | .ok _ => true | .error _ => false

/-- Parse + HM-infer (the GATE) + erase-and-run: only runs if it typechecks, then reuses the
existing UNTYPED pipeline (`parse ∘ lower ∘ Source.eval`) — the elaborate-to-mono claim in action. -/
def hmRunYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  hmOk src && Bang.Surface.runYieldsInt fuel src n


/-! ## 6. Validation — the KILLER guards (ADR-0075 bite-0).

The one-program discriminator: `let id` used at TWO types both TYPES and RUNS; a `fun`-bound `id`
(monomorphic — generalization withheld) at two types FAILS. Same body, different binder — so
generalization is provably load-bearing. Plus `const` at two types, occurs-check fail-loud, and a
monomorphic no-regression case. -/

-- ── the polymorphic `id` used at Int AND (Int * Int) in ONE program ──
private def killerId : String :=
  "let id = {fun x => x} in " ++
  "(let a = ($id) 5 in (let p = ($id) (1, 2) in (let (x, y) = p in a + x)))"

-- (a) it TYPES under HM (let-generalization gives `id : ∀a. Thunk (a -> F a)`, instantiated twice)
#guard hmOk killerId
-- (b) the ERASED term RUNS: id 5 = 5, id (1,2) = (1,2), 5 + 1 = 6
#guard hmRunYieldsInt 200 killerId 6

-- ── THE DISCRIMINATOR: the SAME body, but `id` is a LAMBDA parameter (monomorphic — no
-- generalization). The Int use fixes its hole; the (Int * Int) use then FAILS to unify. This is
-- exactly the guard that FAILS without generalization and PASSES with it. ──
#guard !hmOk
  ("fun id => (let a = ($id) 5 in (let p = ($id) (1, 2) in (let (x, y) = p in a + x)))")

-- ── `const = fun x => fun y => x` used at TWO types (Int×Int result-agnostic in the 2nd arg) ──
private def killerConst : String :=
  "let const = {fun x => fun y => x} in " ++
  "(let a = (($const) 5) 9 in (let b = (($const) 7) (1, 2) in a + b))"
#guard hmOk killerConst
-- const 5 9 = 5, const 7 (1,2) = 7, 5 + 7 = 12
#guard hmRunYieldsInt 200 killerConst 12

-- ── occurs-check FAILS LOUD (an infinite type → error, not a hang): `fun x => ($x) x`
--    forces `x : U ?c` then applies it to `x : U ?c`, needing `?c = U ?c -> …`. ──
#guard !hmOk "fun x => ($x) x"

-- ── MONOMORPHIC no-regression: an ordinary program still types AND runs (HM is a strict superset). ──
#guard hmOk "let z = 3 in z + 4"
#guard hmRunYieldsInt 50 "let z = 3 in z + 4" 7
-- a bare identity still infers its principal (polymorphic) type.
#guard (match hmType "fun x => x" with | .ok (.arr (.hole a) (.f (.hole b))) => a == b | _ => false)
-- application of an inferred identity, no annotation anywhere (the current checker NEEDS one here).
#guard hmRunYieldsInt 50 "let id = {fun x => x} in ($id) 41" 41

/-! ## FINDING (the spike deliverable — see the module header for the question).

  Q: Does HM (unification + let-generalization) land cleanly on the bidirectional checker with the
     kernel UNTOUCHED?
  A: **YES, the mechanism lands cleanly** — proven above (killer id + const type AND run; occurs-check
     fail-loud; mono no-regression; kernel census untouched, this is a leaf). BUT landing it IN PLACE
     (folding into `synthSC`/`synthSV`) is a real, mechanical RESTRUCTURE, not a drop-in, because:

  1. TYPE REP: the checker types in the KERNEL `VTy`/`CTy` with STRUCTURAL equality (`A = expected`).
     HM needs a representation with HOLES. `VTy.tvar` is taken (μ-internal + the 998/999 poison), so
     you CANNOT reuse it — you introduce a checker-only inference type (`HTy` here: kernel fragment +
     `meta` + `rigid`) and zonk back to `VTy` at the boundary. The kernel stays untouched (good), but
     the checker's whole type vocabulary changes.
  2. MONAD: the checker is pure `Except String`; HM needs a fresh-var + substitution STATE
     (`StateT St (Except String)`). Every `synth*/check*` arm re-threads this — mechanical but total.
  3. WHERE GENERALIZATION GOES: the `let` arm, and ONLY there — `inferC .lett` above is a faithful
     preview of `synthSC .lett`. It did NOT resist; the arm already binds the RHS's value type `A`
     (`(.F _ A, φ) => … (x, A) :: Γ`), so generalizing `A` before extending the context is a
     one-line-shaped insertion (+ instantiation at `.var`). This is the clean part.
  4. ANNOTATION / CHECK-MODE COMPOSES: the bidirectional check mode does NOT conflict. An annotation
     becomes "infer, then UNIFY with the annotation" (subsumption), replacing the current `A = expected`
     structural test with `unify A expected`. Check-mode-only intros (`lam`/`inl`) stop being errors:
     an un-annotated `fun` gets a fresh domain hole (this spike), so the two "annotate the fun" errors
     the current pipeline raises — `synthSC`'s `.lam` arm (TypeCheck.lean:369) AND `elabS`'s `.lett`
     arm (TypeCheck.lean:904-909, which pre-synths the RHS) — both DISSOLVE.
  5. ELABORATE-TO-MONO IS FREE: `Source.eval` is untyped, so erasure = identity and the run reuses the
     existing untyped pipeline verbatim (every `hmRunYieldsInt` above). No per-use specialization was
     needed — monomorphization/dict-passing (the bite-2 fork) is a code-GENERATION choice, irrelevant
     to bite 0's "can it type + run".

  OBSTACLES / caveats for the manager:
  • Not a drop-in: items 1-2 touch every checker arm. Budget bite-0b's real work as "port synthSC to
    the HTy + StateT substrate", not "add a case". The recursion spike was a leaf ADD; this is a
    checker REWRITE (still a leaf w.r.t. the kernel).
  • The subsumption switch `check t → synth t` + the current `(sizeOf, rank)` termination measure must
    survive the monad port (fuel-driven here sidesteps it; the real arms recurse on subterms + rank).
  • Row-polymorphism (bite 0b) is NOT here by design: rows are SETS (invariant #2), so a row variable
    unifies differently from a type hole (Rémy/Leijen open rows) — the genuinely bang-specific add.
  • CBPV texture: generalization lands on the VALUE type under `U`/`F` (`let id = {fun…}` generalizes
    the thunk's `U (arr …)`), which is exactly where the `.lett` arm already binds — no friction, but
    worth stating so 0b doesn't expect a textbook `∀a. a -> a` shape.

  VERDICT: proceed with bites 0b→2 as scoped in PATH-polymorphism.md. Bite 0b = port `synthSC`/`synthSV`
  onto this substrate (the mechanical rewrite) + add row variables (the bang-specific part). No spine
  work; no ADR-0075 revision needed.
-/

end Bang.HMSpike
