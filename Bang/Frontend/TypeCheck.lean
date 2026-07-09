/-
  Bang/Frontend/TypeCheck.lean — ADR-0066 stage ③: the bidirectional-checker SPIKE.
  ───────────────────────────────────────────────────────────────────────────────
  De-risks the surface type layer: does a bidirectional checker (`synth ⇒` / `check ⇐`)
  cleanly produce types that match the kernel's `HasCTy`? This handles the PURE fragment
  (int·unit·var·let·lam·app·thunk/force·pair/split·sum/case) over the LOWERED `Comp` (de
  Bruijn, so the context is a positional `List VTy` — no name lookup yet; surface names +
  annotations are stage ②). Grades default to `ω` (= unrestricted, so any type-correct term
  is `HasCTy`-derivable; grade-CHECKING is deferred). Effects: the pure fragment is `⊥`.

  Two validations below:
    · `#guard`s — the checker infers the expected `CTy`/`VTy` for terms parsed from SOURCE.
    · a `HasCTy` example — the kernel AGREES with the checker's type (the spec connection).
  A LEAF module (nothing imports it; outside the soundness closure), like `Examples.lean`.
-/
module

-- `#guard`s run the COMPILED checker over parsed source at the META phase → meta import
-- (the cross-module `#guard` codegen wall; mirrors `Examples.lean`).
meta import Bang.Frontend.Surface
meta import Bang.Core.Semantics     -- runTypedYieldsInt's #guards execute Source.eval (Trait.lean precedent)
meta import Bang.Core.Grade         -- QTT.omega must be META-accessible for the #guards
public import Bang.Frontend.Surface
public import Bang.Core.Typing
public import Bang.Core.Grade      -- QTT (the concrete grade rig)

namespace Bang.TypeCheck
open Bang
open Bang.EffectRow (EffRow Label Row)

/-- The concrete instantiation the surface uses: effect rows are `Finset Label`, grades are QTT.
`VT` is PUBLIC (#60 seam): forced by `sampleVT`/`checkLawOn`'s signatures — additive visibility
only, no behavior change. -/
public abbrev VT := VTy EffRow QTT
abbrev CT := CTy EffRow QTT
abbrev Ctx := List VT      -- positional type context (de Bruijn, innermost first)

-- structural decidable equality for the subsumption check (`synth then compare`). Derived
-- after-the-fact so the kernel `IR.lean` stays untouched (EffRow/QTT already have DecidableEq).
-- VTy/CTy are MUTUAL — DecidableEq must be derived for both in one command.
deriving instance DecidableEq for VTy, CTy

/-! ## The bidirectional checker (pure fragment).

`synth` infers; `check` verifies against an expected type. Introductions that can't infer their
type (`inl`/`inr` — which sum? `lam` — which domain?) are CHECK-mode only; everything else synths.
This is the standard bidirectional discipline (Dunfield–Krishnaswami): the gaps are exactly where
annotations (stage ②) will plug in. -/
-- Termination: synth/check recurse on PROPER subterms — except the subsumption switch
-- `check t → synth t` (same term). A rank (synth=0, check=1) breaks that tie: the
-- lexicographic measure `(sizeOf term, rank)` strictly decreases on every call.
mutual
/-- Synthesize a value's `VTy`. -/
def synthV (Γ : Ctx) (v : Val) : Except String VT :=
  match v with
  | .vunit    => .ok .unit
  | .vint _   => .ok .int
  | .vvar i   => match Γ[i]? with
                 | some A => .ok A
                 | none   => .error s!"unbound de-Bruijn var {i}"
  | .pair a b => do return .prod (← synthV Γ a) (← synthV Γ b)
  | .vthunk M => do let (B, φ) ← synthC Γ M; return .U φ B
  | .inl _    => .error "inl is check-mode only (which sum type?) — annotate"
  | .inr _    => .error "inr is check-mode only (which sum type?) — annotate"
  | _         => .error "value out of the pure fragment (cap/fold)"
  termination_by (sizeOf v, 0)

/-- Check a value AGAINST an expected `VTy`. -/
def checkV (Γ : Ctx) (v : Val) (expected : VT) : Except String Unit :=
  match v, expected with
  | .inl w, .sum A _ => do let _ ← checkV Γ w A; pure ()
  | .inr w, .sum _ B => do let _ ← checkV Γ w B; pure ()
  | v, expected      => do
      let A ← synthV Γ v
      if A = expected then pure () else .error "value type mismatch"
  termination_by (sizeOf v, 1)

/-- Synthesize a computation's `CTy` AND its effect row. -/
def synthC (Γ : Ctx) (c : Comp) : Except String (CT × EffRow) :=
  match c with
  | .ret v   => do return (.F .omega (← synthV Γ v), ⊥)   -- grade defaults to ω
  | .force v => do match (← synthV Γ v) with
                   | .U φ B => return (B, φ)
                   | _      => .error "force: not a thunk"
  | .app M w => do match (← synthC Γ M) with
                   | (.arr _ A B, φ) => do let _ ← checkV Γ w A; return (B, φ)
                   | _               => .error "app: callee is not a function"
  | .letC M N => do match (← synthC Γ M) with
                    | (.F _ A, φ₁) => do let (B, φ₂) ← synthC (A :: Γ) N; return (B, φ₁ ⊔ φ₂)
                    | _            => .error "let: head is not a returner (F)"
  | .case v N₁ N₂ => do match (← synthV Γ v) with
                        | .sum A B => do
                            let (C₁, φ₁) ← synthC (A :: Γ) N₁
                            let (C₂, φ₂) ← synthC (B :: Γ) N₂
                            if C₁ = C₂ then return (C₁, φ₁ ⊔ φ₂) else .error "case: branches disagree"
                        | _ => .error "case: scrutinee is not a sum"
  | .split v N => do match (← synthV Γ v) with
                     | .prod A B => synthC (B :: A :: Γ) N   -- N binds fst@idx1, snd@idx0
                     | _         => .error "split: scrutinee is not a product"
  | .lam _   => .error "lam is check-mode only (which domain?) — annotate"
  | _        => .error "computation out of the pure fragment"
  termination_by (sizeOf c, 0)

/-- Check a computation AGAINST an expected `CTy`, returning its effect row. -/
def checkC (Γ : Ctx) (c : Comp) (expected : CT) : Except String EffRow :=
  match c, expected with
  | .lam M, .arr _ A B => checkC (A :: Γ) M B
  | c, expected        => do
      let (B, φ) ← synthC Γ c
      if B = expected then pure φ else .error "computation type mismatch"
  termination_by (sizeOf c, 1)
end

/-- End-to-end: parse + lower a SOURCE string, then synthesize its type. -/
def infer (src : String) : Except String (CT × EffRow) := do
  let c ← Bang.Surface.parse src >>= Bang.Surface.lower
  synthC [] c

/-! ## Validation ① — the checker infers the expected type, from source text. -/

-- a literal returns `int`; the effect is empty (pure). (Bare `3` doesn't parse at top level — a
-- parser quirk, filed separately; `(3)` does. The checker is what's under test here.)
#guard infer "(3)" == .ok (.F .omega .int, ⊥)
-- `let` sequences; the body's type is the whole type.
#guard infer "let x = 3 in x" == .ok (.F .omega .int, ⊥)
-- a product value: `(3, 4) : Int × Int`.
#guard infer "(3, 4)" == .ok (.F .omega (.prod .int .int), ⊥)
-- destructure a product (the `split` scrutinee is a var of known product type) → fst : int.
#guard infer "let p = (3, 4) in (let (a, b) = p in a)" == .ok (.F .omega .int, ⊥)

-- REJECTIONS (the checker is sound — it refuses ill-typed terms):
-- forcing a non-thunk (`$x` where `x : Int`) is rejected.
#guard (match infer "let x = 3 in $x" with | .error _ => true | _ => false)
-- positive control: forcing an ACTUAL thunk (`$f` where `f = {x}`) succeeds.
#guard (match infer "let x = 3 in (let f = {x} in $f)" with | .ok _ => true | _ => false)
-- forcing a product component that is an `Int` is rejected (same force-not-a-thunk rule).
#guard (match infer "let p = (3, 4) in (let (a, b) = p in $a)" with | .error _ => true | _ => false)

/-! ## Stage ② foundation — type ascription `(e : T)` parses into `annotS` (ADR-0066 ②).

The type-expression grammar + the ascription node are in place; the `Surf`-level checker that
CONSUMES them (driving check-mode for lambdas) is the next unit. -/

-- a function-typed ascription parses to `annotS` carrying the arrow type.
#guard (match Bang.Surface.parse "( fun x => x : Int -> Int )" with
        | .ok (.annotS (.lam "x" (.var "x")) (.tArr .tInt .tInt)) => true | _ => false)
-- `->` is right-associative: `Int -> Int -> Int` = `Int -> (Int -> Int)`.
#guard (match Bang.Surface.parse "( g : Int -> Int -> Int )" with
        | .ok (.annotS (.var "g") (.tArr .tInt (.tArr .tInt .tInt))) => true | _ => false)
-- `*` binds tighter than `+`; `Thunk` is an atom former.
#guard (match Bang.Surface.parse "( p : Int * Int )" with
        | .ok (.annotS (.var "p") (.tProd .tInt .tInt)) => true | _ => false)
#guard (match Bang.Surface.parse "( k : Thunk Int + Unit )" with
        | .ok (.annotS (.var "k") (.tSum (.tThunk .tInt) .tUnit)) => true | _ => false)
-- ascription erases at lowering: the annotated identity still runs as the bare identity.
#guard Bang.Surface.runYieldsInt 20 "( fun x => x : Int -> Int ) 5" 5

/-! ## Validation ② — the kernel `HasCTy` AGREES with the checker's inferred type (the spec link).

The checker says `infer "3" = F ω int`. The kernel confirms a real derivation exists at that type
— so for this term the checker's output is `HasCTy`-witnessed, the soundness the full build will
differential-test. (`ret (vint 3)`: `vint` has grade `zeros`, and `q •Q zeros = zeros` for any `q`,
so the `ret` rule admits `q = ω`.) -/
-- (No effects are used, so any `EffSig` instance does — take it as a hypothesis, as the witnesses do.)
example [EffSig EffRow QTT] : HasCTy (Eff := EffRow) (Mult := QTT)
    (GradeVec.zeros 0) [] (.ret (.vint 3)) ⊥ (CTy.F .omega VTy.int) :=
  -- `ret`: HasVTy γ' [] (vint 3) int  (vint ⇒ γ' = zeros 0), and γ = ω • γ' (empty vectors).
  HasCTy.ret (q := QTT.omega) (HasVTy.vint (Γ := [])) (by decide)

/-! ## Stage ②b — the `Surf`-LEVEL checker (consumes annotations, lifts the limitation).

Bidirectional over the SURFACE (named contexts, BEFORE lowering — where annotations live). `annotS`
drives check-mode: a `lam`/`Left`/`Right` checked against an expected type gets the info synthesis
lacked, so ANNOTATED functions and injections now typecheck — exactly the limitation the spike (over
the annotation-free lowered `Comp`) could not lift. Mirrors `lowerC`/`lowerV`: `synthSC`/`checkSC`
read a `Surf` as a computation, `synthSV`/`checkSV` as a value. Effect ops (④) infer rows now:
each `perform` adds its label, each handler discharges it; `synthSC` ENUMERATES every constructor. -/
open Bang.Surface

/-! ## Inference types `IVTy`/`ICTy` (ADR-0075 bite-0b) — the checker's type vocabulary.

The re-rep that unlocks HM-inferred HIGHER-ORDER polymorphism (bare `compose`). The bite-0
substrate rode holes on `VTy.tvar` reserved ranges — pragmatic, but a computation hole CANNOT ride
`CTy` (it has no `tvar`; forcing a value-hole into an unknown COMPUTATION had to fail loud). Here the
checker works over PARALLEL SUPERSET types that ERASE to the closed kernel types (ADR-0075
elaborate-to-mono): `IVTy` = `VTy` + a value hole `vhole`, `ICTy` = `CTy` + a computation hole
`chole`. A value hole may now be bound to `U ρ (chole)` (a thunk of an unknown computation) — the
exact shape `force`-of-an-unknown-thunk needs. The KERNEL never sees a hole: `embV`/`embC` inject a
closed kernel type; `extractV`/`extractC` zonk-extract back to a closed `VTy`/`CTy` at every boundary
(trait/data resolution · `display` · the `lower`/`HasCTy` handoff). A residual VALUE hole extracts to
a reserved-range `tvar` (display continuity with bite-0); a residual COMPUTATION hole is
unrepresentable in `CTy` → the DEFINED fail-loud "annotate" (a genuinely un-inferable higher-order
force), never a wrong accept. -/
def holeBase  : Nat := 1000000
def rigidBase : Nat := 2000000
def bigFuel   : Nat := 1000000
/-- Base for a GENERIC-ctor template's type-PARAM markers (`data Option a`'s `a` ⟹ `.tVar (paramBase+0)`,
ADR-0079 annotation-FREE intro, #55). A distinct range ABOVE `rigidBase`/`holeBase` so a param marker
is unambiguously NOT a μ-recursion var (0-2), a ∀-scheme rigid, or a hole. Markers exist ONLY inside the
template `Ty` an annotation-free generic ctor carries; `embVInst`/`embCInst` turn EVERY marker into a
FRESH unification hole at the annotation site (so no marker `tvar` ever survives into the checker's
substitution / unrolling). -/
def paramBase : Nat := 3000000

/-! The inference layer's OPEN effect row IS the proven-sound kernel `Bang.EffectRow.Row` (ADR-0075
bite-0b item 3, row polymorphism; SSoT per #57). A closed kernel `EffRow = Finset Label` (invariant #2)
`emb`s to `⟨φ, none⟩` and zonk-EXTRACTS back to `.labels` (exactly as `IVTy` zonks to `VTy`) — the KERNEL
row algebra is UNTOUCHED; this `Row` is the same one `unify`/`applyR` (`unify_sound`) operate on. `tail =
some v`: `v < rigidBase` is a UNIFICATION row var (bound in `USt.rsubst`), `v ≥ rigidBase` is a ∀-scheme
RIGID row var (a quantified `∀ρ`); `tail = none` is a closed row. `unifyRow`/`resolveRow` below are thin
monadic wrappers that DELEGATE to the proven `EffectRow.unify`/`applyR` (dormant in the kernel +
differential-tested by `tools/selfcheck.mjs`) — no mirror. -/

/-- The pure/empty inference row (`⊥`). -/
def botR : Row := ⟨∅, none⟩
/-- A single-label closed inference row (`{ℓ}`). -/
def singR (ℓ : Label) : Row := ⟨{ℓ}, none⟩
/-- Inject a closed kernel `EffRow` into `Row`. -/
def embRow (φ : EffRow) : Row := ⟨φ, none⟩

/-- Map effect NAMES to the kernel label row (the inverse of `effName`). Moved ahead of `tyBoth`
(below) so `tyBoth`'s `tThunk`/`tArr` arms can read a declared row via `effOf` (ADR-0088 D1). -/
def effNames (ns : List String) : EffRow :=
  ns.foldl (fun acc n =>
    if n = "throws" then insert exnLabel acc
    else if n = "state" then insert stateLabel acc
    else if n = "stm" then insert stmLabel acc
    else if n = "Div" then insert divLabel acc else acc) ∅

/-- The DECLARED effect bound of an ascribed type, if any (`none` = unconstrained, stay inferred —
the optional-annotation philosophy). A function's bound is its codomain's. -/
def effOf : Ty → Option EffRow
  | .tEff ns _ => some (effNames ns)
  | .tArr _ b  => effOf b
  | _          => none

/-- A user `effect` decl's ALLOCATED label + resolved op signatures (ADR-0092 D1/D2). `label` is
`4 + declIndex` among the program's `effect` decls (deterministic by decl order, ADR-0046 — see
`buildEnv`). `ops` maps each declared op name to its resolved `(argTy?, resTy)` — `argTy? = none`
for a 0-ary op (a bare result-type signature, `op : ResTy`), `some A` for the v1 single-arg arrow
(`op : ArgTy -> ResTy`). This IS the surface-side analogue of the kernel's `[EffSig]` typeclass
(`Bang/Core/IR.lean`) — a per-program, program-DERIVED, total finite instance the elaborator
constructs and consults; the kernel itself never sees effect NAMES (label-agnostic, `Label = Nat`,
D1's "kernel never learns names"). PUBLIC (#60 seam): forced by `ElabEnv`'s field type —
additive visibility only, no behavior change. -/
public structure EffectInfo where
  label : Label
  ops   : List (String × Option VT × VT)   -- (opName, argTy?, resTy)

/-- Map an effect label back to its surface name (the inverse of the lowering's `exnLabel`/… choice).
Moved ahead of `checkSV` (below) so the thunk-row mismatch error (ADR-0088) can name the offending
effect instead of a bare "exceeds the bound". -/
def effName (ℓ : Label) : String :=
  if ℓ = exnLabel then "throws" else if ℓ = stateLabel then "state"
  else if ℓ = stmLabel then "stm" else if ℓ = divLabel then "Div" else s!"e{ℓ}"

/-- Render an effect row as `throws, state` by decidable membership of the known labels (computable —
`Finset.toList` is noncomputable; the four BUILT-IN labels throws·state·stm·Div are always checked).
`effects` (ADR-0092 D2, default `[]`) additionally names any DECLARED user-effect label present in
`φ` by its SOURCE name (e.g. `Net`, not the kernel's bare `e4`) — the same finite-known-set pattern
as the built-ins, extended over the program's OWN declared labels instead of a fixed four; a caller
with no `ElabEnv` in scope (`display`, the decl-free path) passes nothing and gets the pre-ADR-0092
behavior byte-identical. -/
def showRow (φ : EffRow) (effects : List (String × EffectInfo) := []) : String :=
  String.intercalate ", " <|
    (if exnLabel ∈ φ then [effName exnLabel] else []) ++
    (if stateLabel ∈ φ then [effName stateLabel] else []) ++
    (if stmLabel ∈ φ then [effName stmLabel] else []) ++
    (if divLabel ∈ φ then [effName divLabel] else []) ++
    (effects.filterMap (fun (n, ei) => if ei.label ∈ φ then some n else none))

mutual
/-- A value inference type: a kernel `VTy` shape plus unification `vhole`s. `tvar` still carries BOTH
the μ-recursion vars (0-2) and the ∀-scheme RIGIDs (`rigidBase + i`); only unification holes moved to
the proper `vhole` constructor. -/
inductive IVTy where
  | int   : IVTy
  | unit  : IVTy
  | sum   : IVTy → IVTy → IVTy
  | prod  : IVTy → IVTy → IVTy
  | U     : Row → ICTy → IVTy
  | mu    : IVTy → IVTy
  | tvar  : Nat → IVTy
  | cap   : Label → IVTy
  | vhole : Nat → IVTy
/-- A computation inference type: a kernel `CTy` shape plus unification `chole`s. -/
inductive ICTy where
  | F     : QTT → IVTy → ICTy
  | arr   : QTT → IVTy → ICTy → ICTy
  | chole : Nat → ICTy
end

/-! Inject a closed kernel value type into `IVTy`/`ICTy` (structural, hole-free). -/
mutual
def embV : VT → IVTy
  | .int      => .int
  | .unit     => .unit
  | .sum a b  => .sum  (embV a) (embV b)
  | .prod a b => .prod (embV a) (embV b)
  | .U φ b    => .U (embRow φ) (embC b)
  | .mu a     => .mu (embV a)
  | .tvar n   => .tvar n
  | .cap ℓ    => .cap ℓ
def embC : CT → ICTy
  | .F q a     => .F q (embV a)
  | .arr q a b => .arr q (embV a) (embC b)
end

/-! Zonk-EXTRACT an `IVTy` to a closed kernel `VTy`. A residual `vhole` becomes a reserved-range
`tvar` (bite-0 display continuity — legitimate leftover polymorphism, e.g. a bare `Left(3)`'s phantom
variant); a `chole` reachable through a `U` is unrepresentable in `CTy` → fail loud ("annotate"). -/
mutual
def extractV : IVTy → Except String VT
  | .int      => .ok .int
  | .unit     => .ok .unit
  | .sum a b  => do return .sum  (← extractV a) (← extractV b)
  | .prod a b => do return .prod (← extractV a) (← extractV b)
  -- an UNCONSTRAINED polymorphic tail zonk-EXTRACTS to its known labels (⊥-default): a residual row var
  -- means "no effects forced" for a monomorphic run, exactly as a residual value hole → reserved tvar.
  | .U r b    => do return .U r.labels (← extractC b)
  | .mu a     => do return .mu (← extractV a)
  | .tvar n   => .ok (.tvar n)
  | .cap ℓ    => .ok (.cap ℓ)
  | .vhole n  => .ok (.tvar (holeBase + n))
def extractC : ICTy → Except String CT
  | .F q a     => do return .F q (← extractV a)
  | .arr q a b => do return .arr q (← extractV a) (← extractC b)
  | .chole _   => .error "force: cannot infer this thunk's type — annotate (higher-order is bite-0b)"
end

/-- A ∀-scheme RIGID (still on `tvar`, `rigidBase`-offset). -/
@[inline] def mkRigid (i : Nat) : IVTy := .tvar (rigidBase + i)
/-- A BARE-lambda parameter's placeholder hole (the HM higher-order path; ELABORATION-only — the final
check re-mints fresh domain holes). Offset high so it can't collide with a `freshHole` minted from `0`
by a per-site inference; `Γ.length` keeps nested params distinct. -/
@[inline] def paramHole (depth : Nat) : IVTy := .vhole (rigidBase + depth)
/-- Is this EXTRACTED value type a residual hole/rigid `tvar` (⟹ unresolved, defer to the checker)? -/
@[inline] def asHole : VT → Option Nat
  | .tvar n => if holeBase ≤ n then some (n - holeBase) else none
  | _       => none

/-- A HINDLEY-MILNER type scheme `∀ (arity vars). body` (ADR-0075 bite-0). The quantified variables
are the RIGID markers `rigidBase + 0 … rigidBase + arity-1` inside `body`; instantiation replaces
each with a fresh unification HOLE. A MONOMORPHIC binding (a lambda / match / split parameter) is
`⟨0, τ⟩` — no quantification, so `Coe IVTy Scheme` below lets every ordinary `(x, A) :: Γ` binding site
stay UNCHANGED; only `let` (which generalizes) and the lookup consumers (which instantiate) differ. -/
structure Scheme where
  arity    : Nat := 0    -- quantified VALUE vars (rigid `tvar`s `rigidBase + i`)
  rowArity : Nat := 0    -- quantified ROW vars (rigid tails `rigidBase + j`), bite-0b item 3
  body     : IVTy

instance : Coe IVTy Scheme := ⟨fun v => { body := v }⟩

abbrev NCtx := List (String × Scheme)   -- named typing context, innermost first (= `List.lookup` keys)

/-- Interpret a surface `Ty` into BOTH its value reading (`.1`) and computation reading (`.2`) in one
structural pass — `tArr`/`tThunk` are computations (`arr`/the wrapped `F`); a non-arrow as a value is
itself, as a computation a returner `F` of that value type. One recursion (no mutual block, no
termination obligation).

`tThunk`'s wrapping `.U` row (ADR-0088 D1, #48): the row a THUNK carries is whatever `! {ρ}` the
wrapped type itself declares (`effOf`, e.g. `Thunk (Int -> Int ! {throws})`'s row is `{throws}`,
read off the arrow's codomain) — ⊥ when none is declared (D2: absent annotation ⟹ ∅, backward
compatible with every non-effectful `Thunk`/function value already in the corpus). This is what lets
`checkSV`'s generic `.thunk b, .U φ B` arm (the #45 fold-payload check, unchanged) accept a
`let rec`'s self-knot once its `recTy` declares a row — the row-carrying recursive thunk type IS
this general mechanism, not a recursion-specific special case. -/
def tyBoth : Ty → VT × CT
  | .tInt      => let V : VT := .int;              (V, .F .omega V)
  | .tUnit     => let V : VT := .unit;             (V, .F .omega V)
  | .tSum  a b => let V : VT := .sum  (tyBoth a).1 (tyBoth b).1; (V, .F .omega V)
  | .tProd a b => let V : VT := .prod (tyBoth a).1 (tyBoth b).1; (V, .F .omega V)
  | .tThunk t  => let V : VT := .U ((effOf t).getD ∅) (tyBoth t).2; (V, .F .omega V)
  | .tArr  a b => let f : CT := .arr .omega (tyBoth a).1 (tyBoth b).2
                  (.U ((effOf b).getD ∅) f, f)                        -- fn VALUE = thunked arrow, ITS OWN row
  | .tEff  _ t => tyBoth t        -- effect annotation is checker-level (effOf); dropped from the kernel type
  | .tSelf     => let V : VT := .tvar 999; (V, .F .omega V)  -- POISON: `buildEnv` substitutes Self before
                                  -- any tyBoth; a leaked Self surfaces as `#999`, never unifies
  | .tName _   => let V : VT := .tvar 998; (V, .F .omega V)  -- POISON: `resolveTy` closes names before
                                  -- any tyBoth; a leaked name surfaces as `#998` (ADR-0069)
  | .tApp _ _  => let V : VT := .tvar 996; (V, .F .omega V)  -- POISON: `resolveTy` monomorphizes tApp first (bite-1)
  | .tMu b     => let V : VT := .mu (tyBoth b).1;  (V, .F .omega V)
  | .tVar n    => let V : VT := .tvar n;           (V, .F .omega V)
@[inline] def vtyOf (t : Ty) : VT := (tyBoth t).1
@[inline] def ctyOf (t : Ty) : CT := (tyBoth t).2

/-- Bool is `1 + 1` (ADR-0065); comparisons return it, arithmetic returns `Int`. (An `IVTy` — it
feeds the inference layer directly.) -/
def boolTy : IVTy := .sum .unit .unit
def binopResTy : BinOp → IVTy
  | .lt | .eq => boolTy
  | _         => .int

/-- The label a `with <kind>` handler installs (its cap has type `Cap ℓ`). ADR-0070. -/
def capKindLabel : String → Option Label
  | "state"      => some stateLabel
  | "throws"     => some exnLabel
  | "atomically" => some stmLabel
  | _            => none

/-- A named cap op's signature: the label its receiver must carry · its argument value-types ·
its result value-type (payloads fixed to `Int`, ADR-0030). `h.op` is well-typed iff the receiver
is `Cap ℓ` with `ℓ` = the label here and the args check. -/
def capOpSig : String → Option (Label × List VT × VT)
  | "get"   => some (stateLabel, [],          .int)
  | "put"   => some (stateLabel, [.int],      .unit)
  | "raise" => some (exnLabel,   [.int],      .int)   -- result = the payload (v1, matches ambient)
  | "new"   => some (stmLabel,   [.int],      .int)   -- TVar ref
  | "read"  => some (stmLabel,   [.int],      .int)
  | "write" => some (stmLabel,   [.int, .int], .unit)
  | _       => none


/-! ## HM inference substrate (ADR-0075 bite-0/0b) — unification + let-generalization over `IVTy`/`ICTy`.

Holes are proper constructors: a VALUE hole is `IVTy.vhole n`, a COMPUTATION hole is `ICTy.chole n`.
The substitution binds BOTH (`subst : vhole → IVTy`, `csubst : chole → ICTy`). A value hole bound to
`U ρ (chole)` is what makes `force`-of-an-unknown-thunk representable (higher-order). Rigids (∀-scheme
vars) still ride `tvar` (`rigidBase`-offset), so generalize/instantiate touch only `tvar`.
`bigFuel`-driven total recursion (the repo's parser idiom) — no cycles once occurs-check holds, but
Lean can't see that, so fuel bounds every walk (never bites: the fresh counter tops out in the dozens). -/

/-- The unification state: a fresh-variable counter + the value-hole and comp-hole substitutions
+ the program's user-EFFECT table (ADR-0092 D2 — READ-ONLY here: `buildEnv` populates it once
before inference starts; nothing during a run ever mutates `effects`, it just rides the state
monad because `Infer`'s mutual family has no separate reader-style environment parameter — the
established `synthSC`/`checkSC`/… signatures take only `Γ : NCtx`, and re-threading `ElabEnv`
through every one of them would be a far larger diff than piggybacking on the state already
passed implicitly everywhere). -/
structure USt where
  fresh   : Nat := 0
  subst   : List (Nat × IVTy) := []
  csubst  : List (Nat × ICTy) := []
  rsubst  : List (Nat × Row) := []   -- row-variable substitution (bite-0b item 3); = EffectRow.Subst
  effects : List (String × EffectInfo) := []   -- ADR-0092 D2: name ↦ label + op sigs, seeded once

abbrev Infer := StateT USt (Except String)

/-- Mint a fresh VALUE unification hole. -/
def freshHole : Infer IVTy := modifyGet (fun s => (.vhole s.fresh, { s with fresh := s.fresh + 1 }))
/-- Mint a fresh COMPUTATION unification hole. -/
def freshCHole : Infer ICTy := modifyGet (fun s => (.chole s.fresh, { s with fresh := s.fresh + 1 }))
/-- Assign value hole `n := t`. -/
def assign (n : Nat) (t : IVTy) : Infer Unit := modify (fun s => { s with subst := (n, t) :: s.subst })
/-- Assign comp hole `n := t`. -/
def assignC (n : Nat) (t : ICTy) : Infer Unit := modify (fun s => { s with csubst := (n, t) :: s.csubst })
/-- One-hop lookup of a value hole's binding. -/
def hget (n : Nat) : Infer (Option IVTy) := do return (← get).subst.lookup n
/-- One-hop lookup of a comp hole's binding. -/
def hgetC (n : Nat) : Infer (Option ICTy) := do return (← get).csubst.lookup n

/-! ### Row-variable inference (bite-0b item 3) — open-row unification threaded through `USt.rsubst`.
`resolveRow`/`unifyRow` DELEGATE to the proven-sound `Bang.EffectRow.applyR`/`unify` (`unify_sound`) — a
thin monadic shell that carries `rsubst` as the pure `Subst` and installs `unify`'s result bindings
(SSoT per #57; the algorithm is the kernel's, differential-tested by `tools/selfcheck.mjs`). The KERNEL
`EffRow = Finset Label` is untouched; row vars live ONLY here. -/

/-- Mint a fresh row-variable id (shares the `fresh` counter; row ids live in `rsubst`, disjoint from
value/comp holes). -/
def freshRVar : Infer Nat := modifyGet (fun s => (s.fresh, { s with fresh := s.fresh + 1 }))
/-- A fresh, empty-known OPEN row `∅ ∪ ρ`. -/
def freshRow : Infer Row := do return ⟨∅, some (← freshRVar)⟩
/-- Bind row var `v := r`. -/
def rassign (v : Nat) (r : Row) : Infer Unit := modify (fun s => { s with rsubst := (v, r) :: s.rsubst })

/-- Resolve a row against `rsubst` — delegates to the proven `EffectRow.applyR` (`rsubst` IS its `Subst`). -/
def resolveRow (fuel : Nat) (r : Row) : Infer Row := do
  return EffectRow.applyR fuel (← get).rsubst r

/-- Open-row unification: resolve both sides, then delegate to the proven-sound `EffectRow.unify` and
install its result substitution. `unify` needs a fresh tail var only in the open/open-DISTINCT case, so
that is the sole case that mints one (preserving the fresh-counter trajectory of the former mirror). MGU
is the differential-tested contract (CLAUDE.md); soundness is `EffectRow.unify_sound`. -/
def unifyRow (fuel : Nat) (a b : Row) : Infer Unit := do
  let a ← resolveRow fuel a
  let b ← resolveRow fuel b
  let fresh ← match a.tail, b.tail with
    | some v1, some v2 => if v1 == v2 then pure 0 else freshRVar
    | _,       _       => pure 0
  match EffectRow.unify fresh a b with
  | some s => for (v, r) in s do rassign v r
  | none   => throw "effect row mismatch"

/-- Join two rows (the effect-`⊔`). Two DISTINCT open tails are COLLAPSED to one (the single-ρ first cut,
ADR-0075 item 3): `compose`'s body `($f)(($g) x)` joins `ρf ⊔ ρg` — collapsing forces one shared row var,
yielding `∀ρ. …!ρ…`. FINDING (documented): this rejects composing functions at DIFFERENT effect rows (that
needs independent tails + a real join, i.e. full Rémy lacks-constraints). Sound (over-approximates), incomplete. -/
def joinRow (fuel : Nat) (a b : Row) : Infer Row := do
  let a ← resolveRow fuel a
  let b ← resolveRow fuel b
  match a.tail, b.tail with
  | none,    none    => return ⟨a.labels ∪ b.labels, none⟩
  | some v,  none    => return ⟨a.labels ∪ b.labels, some v⟩
  | none,    some v  => return ⟨a.labels ∪ b.labels, some v⟩
  | some v1, some v2 =>
      if v1 == v2 then return ⟨a.labels ∪ b.labels, some v1⟩
      else do rassign v2 ⟨∅, some v1⟩; return ⟨a.labels ∪ b.labels, some v1⟩

/-- Remove a CONCRETE (handler) label from a row's known part (the `.erase ℓ` mirror). First cut: the tail
carries an implicit ℓ-LACKS constraint (Rémy) that is NOT enforced — full lacks-constraints are the
deferred refinement. -/
def eraseRow (fuel : Nat) (ℓ : Label) (r : Row) : Infer Row := do
  let r ← resolveRow fuel r; return ⟨r.labels.erase ℓ, r.tail⟩
/-- Insert a concrete label into a row's known part (the `insert ℓ` mirror; e.g. `divMark`). -/
def insertRow (fuel : Nat) (ℓ : Label) (r : Row) : Infer Row := do
  let r ← resolveRow fuel r; return ⟨insert ℓ r.labels, r.tail⟩
/-- Is the (resolved) row `a` within the DECLARED bound `b` (concrete, from an annotation)? An
UNCONSTRAINED open tail on `a` defaults to ⊥ (contributes no labels) — the same "higher-order row = ⊥"
assumption the pre-row-poly checker baked in by hardcoding ⊥ on forced-thunk rows, so this is behaviour-
preserving on the existing corpus; full lacks-constraints on the tail are the deferred refinement. -/
def subRow (fuel : Nat) (a b : Row) : Infer Bool := do
  let a ← resolveRow fuel a
  let b ← resolveRow fuel b
  return a.labels ⊆ b.labels

/-- Follow the value-hole chain at the TOP of a value type. -/
def resolve (fuel : Nat) (t : IVTy) : Infer IVTy := do
  match fuel with
  | 0      => return t
  | fu + 1 => match t with
              | .vhole n => match (← hget n) with | some t' => resolve fu t' | none => return t
              | _        => return t
/-- Follow the comp-hole chain at the TOP of a computation type. -/
def resolveC (fuel : Nat) (c : ICTy) : Infer ICTy := do
  match fuel with
  | 0      => return c
  | fu + 1 => match c with
              | .chole n => match (← hgetC n) with | some c' => resolveC fu c' | none => return c
              | _        => return c

mutual
/-- Deeply apply the substitution to a value type. -/
def zonkV (fuel : Nat) (t : IVTy) : Infer IVTy := do
  match fuel with
  | 0      => return t
  | fu + 1 =>
    let t ← resolve (fu + 1) t
    match t with
    | .sum a b  => return .sum  (← zonkV fu a) (← zonkV fu b)
    | .prod a b => return .prod (← zonkV fu a) (← zonkV fu b)
    | .U φ b    => return .U (← resolveRow (fu + 1) φ) (← zonkC fu b)
    | .mu a     => return .mu (← zonkV fu a)
    | other     => return other
/-- Deeply apply the substitution to a computation type. -/
def zonkC (fuel : Nat) (c : ICTy) : Infer ICTy := do
  match fuel with
  | 0      => return c
  | fu + 1 =>
    let c ← resolveC (fu + 1) c
    match c with
    | .F q a     => return .F q (← zonkV fu a)
    | .arr q a b => return .arr q (← zonkV fu a) (← zonkC fu b)
    | other      => return other
end

mutual
/-- Does VALUE hole `n` occur in a (ZONKED) value type? The occurs-check that makes an infinite type a
LOUD error, not a hang. -/
def occVinV (n : Nat) : IVTy → Bool
  | .vhole m  => m == n
  | .sum a b  => occVinV n a || occVinV n b
  | .prod a b => occVinV n a || occVinV n b
  | .U _ b    => occVinC n b
  | .mu a     => occVinV n a
  | _         => false
def occVinC (n : Nat) : ICTy → Bool
  | .F _ a     => occVinV n a
  | .arr _ a b => occVinV n a || occVinC n b
  | .chole _   => false
end

mutual
/-- Does COMPUTATION hole `n` occur in a (ZONKED) computation type? -/
def occCinV (n : Nat) : IVTy → Bool
  | .sum a b  => occCinV n a || occCinV n b
  | .prod a b => occCinV n a || occCinV n b
  | .U _ b    => occCinC n b
  | .mu a     => occCinV n a
  | _         => false
def occCinC (n : Nat) : ICTy → Bool
  | .chole m   => m == n
  | .F _ a     => occCinV n a
  | .arr _ a b => occCinV n a || occCinC n b
end

mutual
/-- Unify two value types, extending the substitution. Rows/grades unify by EQUALITY (concrete in
bite-0 — row variables are item 3). Occurs-check fails loud. MGU is the differential-tested contract
(CLAUDE.md), not proven here. -/
def unifyV (fuel : Nat) (a b : IVTy) : Infer Unit := do
  match fuel with
  | 0      => throw "unify: out of fuel"
  | fu + 1 =>
    let a ← resolve (fu + 1) a
    let b ← resolve (fu + 1) b
    match a, b with
    | .vhole n, .vhole m => if n == m then return () else assign n b
    | .vhole n, _        => do if occVinV n (← zonkV (fu + 1) b) then
                                 throw "occurs check: cannot construct an infinite type" else assign n b
    | _, .vhole m        => do if occVinV m (← zonkV (fu + 1) a) then
                                 throw "occurs check: cannot construct an infinite type" else assign m a
    | .int, .int   => return ()
    | .unit, .unit => return ()
    | .cap ℓ, .cap ℓ' => if ℓ == ℓ' then return () else throw "cap label mismatch"
    | .tvar n, .tvar m => if n == m then return () else throw "rigid/rec type-var mismatch"
    | .sum a1 a2, .sum b1 b2   => do unifyV fu a1 b1; unifyV fu a2 b2
    | .prod a1 a2, .prod b1 b2 => do unifyV fu a1 b1; unifyV fu a2 b2
    | .mu a1, .mu b1           => unifyV fu a1 b1
    | .U φ B, .U φ' B'         => do unifyRow fu φ φ'; unifyC fu B B'   -- OPEN-row unify (bite-0b item 3)
    | _, _ => throw "type mismatch"
def unifyC (fuel : Nat) (a b : ICTy) : Infer Unit := do
  match fuel with
  | 0      => throw "unify: out of fuel"
  | fu + 1 =>
    let a ← resolveC (fu + 1) a
    let b ← resolveC (fu + 1) b
    match a, b with
    | .chole n, .chole m => if n == m then return () else assignC n b
    | .chole n, _        => do if occCinC n (← zonkC (fu + 1) b) then
                                 throw "occurs check: cannot construct an infinite computation type" else assignC n b
    | _, .chole m        => do if occCinC m (← zonkC (fu + 1) a) then
                                 throw "occurs check: cannot construct an infinite computation type" else assignC m a
    | .F q A, .F q' A'         => if q == q' then unifyV fu A A' else throw "returner grade mismatch"
    | .arr q A B, .arr q' A' B' => if q == q' then do unifyV fu A A'; unifyC fu B B'
                                   else throw "arrow grade mismatch"
    | _, _ => throw "computation type mismatch"
end

mutual
/-- Free VALUE holes of a (zonked) value type, left-to-right. -/
def freeHolesV : IVTy → List Nat
  | .vhole m  => [m]
  | .sum a b  => freeHolesV a ++ freeHolesV b
  | .prod a b => freeHolesV a ++ freeHolesV b
  | .U _ b    => freeHolesC b
  | .mu a     => freeHolesV a
  | _         => []
def freeHolesC : ICTy → List Nat
  | .F _ a     => freeHolesV a
  | .arr _ a b => freeHolesV a ++ freeHolesC b
  | .chole _   => []
end

mutual
/-- Free COMPUTATION holes of a (zonked) type — the choles generalization defaults to `F ω ?`. -/
def freeCholesV : IVTy → List Nat
  | .sum a b  => freeCholesV a ++ freeCholesV b
  | .prod a b => freeCholesV a ++ freeCholesV b
  | .U _ b    => freeCholesC b
  | .mu a     => freeCholesV a
  | _         => []
def freeCholesC : ICTy → List Nat
  | .chole m   => [m]
  | .F _ a     => freeCholesV a
  | .arr _ a b => freeCholesV a ++ freeCholesC b
end

/-! Free ROW VARIABLES of a (zonked) type — unification tails (`< rigidBase`), left-to-right; the row
analog of `freeHolesV`. Generalization quantifies these; instantiation mints fresh ones. -/
mutual
def freeRowsV : IVTy → List Nat
  | .U r b    => (match r.tail with | some v => if v < rigidBase then [v] else [] | none => []) ++ freeRowsC b
  | .sum a b  => freeRowsV a ++ freeRowsV b
  | .prod a b => freeRowsV a ++ freeRowsV b
  | .mu a     => freeRowsV a
  | _         => []
def freeRowsC : ICTy → List Nat
  | .F _ a     => freeRowsV a
  | .arr _ a b => freeRowsV a ++ freeRowsC b
  | .chole _   => []
end

/-! Abstract free row vars in `rs` to RIGID row tails (`rigidBase + i`) — the generalization step; and
instantiate rigid row tails from a fresh-row list — the instantiation step. Row rigids ride `rigidBase`
in the TAIL field, disjoint from value rigids (which ride it in `tvar`). -/
mutual
def abstractRowsV (rs : List Nat) : IVTy → IVTy
  | .U r b    => .U (match r.tail with
                     | some v => (match rs.idxOf? v with | some i => ⟨r.labels, some (rigidBase + i)⟩ | none => r)
                     | none   => r) (abstractRowsC rs b)
  | .sum a b  => .sum  (abstractRowsV rs a) (abstractRowsV rs b)
  | .prod a b => .prod (abstractRowsV rs a) (abstractRowsV rs b)
  | .mu a     => .mu (abstractRowsV rs a)
  | t         => t
def abstractRowsC (rs : List Nat) : ICTy → ICTy
  | .F q a     => .F q (abstractRowsV rs a)
  | .arr q a b => .arr q (abstractRowsV rs a) (abstractRowsC rs b)
  | c          => c
end
mutual
def instRowsV (insts : List Row) : IVTy → IVTy
  | .U r b    => .U (match r.tail with
                     | some v => if v ≥ rigidBase then
                                   (match insts[v - rigidBase]? with
                                    | some ri => ⟨r.labels ∪ ri.labels, ri.tail⟩ | none => r)
                                 else r
                     | none   => r) (instRowsC insts b)
  | .sum a b  => .sum  (instRowsV insts a) (instRowsV insts b)
  | .prod a b => .prod (instRowsV insts a) (instRowsV insts b)
  | .mu a     => .mu (instRowsV insts a)
  | t         => t
def instRowsC (insts : List Row) : ICTy → ICTy
  | .F q a     => .F q (instRowsV insts a)
  | .arr q a b => .arr q (instRowsV insts a) (instRowsC insts b)
  | c          => c
end

mutual
/-- Replace each VALUE hole in `ms` with `rigid (its index)` — the generalization abstraction step. -/
def abstractV (ms : List Nat) : IVTy → IVTy
  | .vhole m  => (match ms.idxOf? m with | some i => mkRigid i | none => .vhole m)
  | .sum a b  => .sum  (abstractV ms a) (abstractV ms b)
  | .prod a b => .prod (abstractV ms a) (abstractV ms b)
  | .U φ b    => .U φ (abstractC ms b)
  | .mu a     => .mu (abstractV ms a)
  | t         => t
def abstractC (ms : List Nat) : ICTy → ICTy
  | .F q a     => .F q (abstractV ms a)
  | .arr q a b => .arr q (abstractV ms a) (abstractC ms b)
  | c          => c
end

mutual
/-- Replace each `rigid i` with `insts[i]` — the instantiation step. -/
def instV (insts : List IVTy) : IVTy → IVTy
  | .tvar m   => if m ≥ rigidBase then insts.getD (m - rigidBase) (.tvar m) else .tvar m
  | .sum a b  => .sum  (instV insts a) (instV insts b)
  | .prod a b => .prod (instV insts a) (instV insts b)
  | .U φ b    => .U φ (instC insts b)
  | .mu a     => .mu (instV insts a)
  | t         => t
def instC (insts : List IVTy) : ICTy → ICTy
  | .F q a     => .F q (instV insts a)
  | .arr q a b => .arr q (instV insts a) (instC insts b)
  | c          => c
end

/-- GENERALIZE `A` against `Γ`: quantify over the VALUE holes free in `A` but NOT free in the
environment (the heart of let-polymorphism). First DEFAULT any dangling COMPUTATION hole to `F ω ?`
(a fresh value hole) so a higher-order result whose computation shape was never pinned (`compose`'s
tail) generalizes as an ordinary value var — enabling use at multiple types. Documented bite-0b
limitation: the default assumes a RETURNER (the common case); a genuinely arrow-shaped dangling
result would be pinned by its use site or need an annotation. -/
def generalize (Γ : NCtx) (A : IVTy) : Infer Scheme := do
  let Az0 ← zonkV bigFuel A
  for c in (freeCholesV Az0).eraseDups do
    let h ← freshHole
    assignC c (.F .omega h)
  let Az ← zonkV bigFuel A
  let mut envHoles : List Nat := []
  let mut envRows  : List Nat := []
  for (_, s) in Γ do
    let sz ← zonkV bigFuel s.body
    envHoles := envHoles ++ freeHolesV sz
    envRows  := envRows  ++ freeRowsV sz
  let genHoles := ((freeHolesV Az).filter (fun m => !envHoles.contains m)).eraseDups
  -- bite-0b item 3: ALSO quantify free ROW vars (not env-constrained) — `∀ρ. …!ρ…` (effect-row poly).
  let genRows  := ((freeRowsV Az).filter (fun m => !envRows.contains m)).eraseDups
  return ⟨genHoles.length, genRows.length, abstractRowsV genRows (abstractV genHoles Az)⟩

/-- INSTANTIATE a scheme with a fresh hole per quantified VALUE var + a fresh row var per quantified ROW
var (independent per use-site). -/
def instantiate (s : Scheme) : Infer IVTy := do
  let mut insts : List IVTy := []
  for _ in List.range s.arity do insts := insts ++ [← freshHole]
  let mut rinsts : List Row := []
  for _ in List.range s.rowArity do rinsts := rinsts ++ [← freshRow]
  return instRowsV rinsts (instV insts s.body)

/-- Look a name up and instantiate its scheme (the `var` rule). -/
def lookupInst (Γ : NCtx) (x : String) : Infer IVTy := do
  match Γ.lookup x with
  | some s => instantiate s
  | none   => throw s!"unbound variable {x}"

/-! IVTy-native μ-substitution — a faithful mirror of the kernel's `VTy.tyShiftFrom`/`tySubstFrom`
(`Bang/Core/IR.lean`) that PRESERVES `vhole`/`chole` (which the extract-to-kernel round-trip would
freeze into reserved-range `tvar`s). On a hole-free `IVTy` it agrees byte-for-byte with the kernel
(same shift/subst/renumber), so it is a safe drop-in; the hole-preserving behaviour is what lets an
annotation-FREE generic ctor (`Some(x)`, #55) unroll a μ whose element type is still an unsolved hole. -/
mutual
def ivShiftV (k : Nat) : IVTy → IVTy
  | .int      => .int
  | .unit     => .unit
  | .cap ℓ    => .cap ℓ
  | .vhole n  => .vhole n
  | .tvar i   => if i ≥ k then .tvar (i + 1) else .tvar i
  | .sum a b  => .sum  (ivShiftV k a) (ivShiftV k b)
  | .prod a b => .prod (ivShiftV k a) (ivShiftV k b)
  | .U φ b    => .U φ (ivShiftC k b)
  | .mu a     => .mu (ivShiftV (k + 1) a)
def ivShiftC (k : Nat) : ICTy → ICTy
  | .F q a     => .F q (ivShiftV k a)
  | .arr q a b => .arr q (ivShiftV k a) (ivShiftC k b)
  | .chole n   => .chole n
end
mutual
def ivSubstV (k : Nat) (T : IVTy) : IVTy → IVTy
  | .int      => .int
  | .unit     => .unit
  | .cap ℓ    => .cap ℓ
  | .vhole n  => .vhole n
  | .tvar i   => if i = k then T else if i > k then .tvar (i - 1) else .tvar i
  | .sum a b  => .sum  (ivSubstV k T a) (ivSubstV k T b)
  | .prod a b => .prod (ivSubstV k T a) (ivSubstV k T b)
  | .U φ b    => .U φ (ivSubstC k T b)
  | .mu a     => .mu (ivSubstV (k + 1) (ivShiftV 0 T) a)
def ivSubstC (k : Nat) (T : IVTy) : ICTy → ICTy
  | .F q a     => .F q (ivSubstV k T a)
  | .arr q a b => .arr q (ivSubstV k T a) (ivSubstC k T b)
  | .chole n   => .chole n
end

/-- μ-unroll an `IVTy` μ-BODY: `A[μX.A / X]`, filling the nearest recursion var (index 0) with the whole
`μX.A` — the IVTy mirror of the kernel's `VTy.unrollMu`, hole-preserving (see `ivSubstV`). -/
def unrollI (A : IVTy) : Infer IVTy := return ivSubstV 0 (.mu A) A

/-! ## Annotation-FREE generic-ctor instantiation (ADR-0079 follow-on, #55).

A generic ctor elaborates to `annotS (foldS (inj v)) template`, where `template : Ty` is the ctor's
closed μ with each type PARAM left as a marker `.tVar (paramBase + i)`. When the annotation is EMBEDDED
into the checker (`embVInst`/`embCInst`), every marker becomes a FRESH unification hole — so the ctor's
concrete instantiation is INFERRED by unifying the field expressions against the (hole-carrying) μ,
rather than requiring a concrete `: Option Int` annotation. A concrete-use fills the holes; a use inside
a polymorphic function leaves them, and `let`-generalization abstracts them (real HM over generic data). -/
mutual
def collectMarkersV : IVTy → List Nat
  | .tvar n   => if n ≥ paramBase then [n] else []
  | .sum a b  => collectMarkersV a ++ collectMarkersV b
  | .prod a b => collectMarkersV a ++ collectMarkersV b
  | .U _ b    => collectMarkersC b
  | .mu a     => collectMarkersV a
  | _         => []
def collectMarkersC : ICTy → List Nat
  | .F _ a     => collectMarkersV a
  | .arr _ a b => collectMarkersV a ++ collectMarkersC b
  | _          => []
end
mutual
def substMarkersV (m : List (Nat × IVTy)) : IVTy → IVTy
  | .tvar n   => match m.lookup n with | some t => t | none => .tvar n
  | .sum a b  => .sum  (substMarkersV m a) (substMarkersV m b)
  | .prod a b => .prod (substMarkersV m a) (substMarkersV m b)
  | .U φ b    => .U φ (substMarkersC m b)
  | .mu a     => .mu (substMarkersV m a)
  | t         => t
def substMarkersC (m : List (Nat × IVTy)) : ICTy → ICTy
  | .F q a     => .F q (substMarkersV m a)
  | .arr q a b => .arr q (substMarkersV m a) (substMarkersC m b)
  | c          => c
end

/-- Embed a value annotation, replacing each generic-ctor param MARKER with a fresh unification hole
(consistent per marker index). A marker-free annotation (every ordinary user/`let rec`/trait type) is
byte-identically `embV (vtyOf t)` — the substitution map is empty, so behaviour is unchanged. -/
def embVInst (t : Ty) : Infer IVTy := do
  let A := embV (vtyOf t)
  let marks := (collectMarkersV A).eraseDups
  let m ← marks.mapM (fun n => do return (n, ← freshHole))
  return substMarkersV m A
/-- As `embVInst`, for a computation annotation (`ctyOf t = F ω (μ…)` for a generic-ctor value type). -/
def embCInst (t : Ty) : Infer ICTy := do
  let C := embC (ctyOf t)
  let marks := (collectMarkersC C).eraseDups
  let m ← marks.mapM (fun n => do return (n, ← freshHole))
  return substMarkersC m C

/-- Expect a RETURNER: resolve `c` to `.F q A`; a bare `chole` is unified with `F ω ?` (a returner of a
fresh value hole) — the returner-context rule that lets `let x = ($g) y in …` bind `x` when `($g) y`'s
type is still an unknown computation (higher-order). -/
def expectF (c : ICTy) : Infer (QTT × IVTy) := do
  match (← resolveC bigFuel c) with
  | .F q A   => return (q, A)
  | .chole n => do let A ← freshHole; assignC n (.F .omega A); return (.omega, A)
  | _        => throw "let: head is not a returner"

/-- Run an inference action from an empty state, zonk, and zonk-EXTRACT to a kernel `VTy` (the concrete
answer the elaborator's resolution sites + the boundary need). A residual value hole extracts to a
reserved-range `tvar`; a residual comp hole fails loud. -/
def runInferV (act : Infer IVTy) : Except String VT := do
  let iv ← (do zonkV bigFuel (← act)).run' {}
  extractV iv
/-- As `runInferC`, but keep the ZONKED `ICTy` (no extraction) — for the elaborator's chole-tolerant
returner probes (`anfSplit`, `let`-RHS), which must inspect a higher-order result WITHOUT failing on a
still-open computation hole. -/
def zonkInferC (act : Infer (ICTy × Row)) : Except String (ICTy × EffRow) :=
  (do let (B, φ) ← act; return (← zonkC bigFuel B, (← resolveRow bigFuel φ).labels)).run' {}
/-- Run an inference action, zonk, and zonk-EXTRACT to a kernel `CTy` + effect row. `effects` seeds
`USt`'s user-effect table (ADR-0092 D2, default `[]` — every PRE-existing call site is decl-free or
doesn't need `.dotPerform` against a user effect, so it stays behaviour-identical); callers that DO
have a built `ElabEnv` (`checkProg`/`checkAndLower`/`runTypedYieldsInt`) pass `env.effects` so the
type-checker's `.dotPerform` arm can resolve a user op by `(label, op)`. -/
def runInferC (act : Infer (ICTy × Row)) (effects : List (String × EffectInfo) := []) :
    Except String (CT × EffRow) := do
  let (Bz, φ) ←
    (do let (B, φ) ← act; return (← zonkC bigFuel B, (← resolveRow bigFuel φ).labels)).run'
      { effects := effects }
  return (← extractC Bz, φ)


/-- Syntactic value check — mirrors `Surface.lowerV`'s value-shaped constructors. A `thunk` is
ALWAYS a value (its body is a separate computation), even a thunk of a check-mode-only `fun`; this
is why the check is syntactic, not `synthSV`-based (a thunk-of-bare-`fun` neither `synthSV`s nor
`synthSC`s, yet is a perfectly good value — the #45 `Box({fun x => x})` payload). Also the
VALUE-RESTRICTION predicate (bite-0b): only a syntactic value's `let`-type is generalized. -/
def isValueSurf : Surf → Bool
  | .lit _ | .var _ | .unitS | .thunk _ => true
  | .inlS e | .inrS e | .foldS e        => isValueSurf e
  | .pairS a b                          => isValueSurf a && isValueSurf b
  | .annotS e _                         => isValueSurf e
  | _                                   => false

/-- Post-hoc error location, cheap tier (issue #52 Stage B, option-2 sweep): when the offending
Surf sub-term is a BARE variable, name it in the message so `Surface.locateInMsg` resolves a real
source span (`locateToken` finds the token by name). A compound sub-term (`$($f) x`, a nested
`match`, …) has no single source token to point at without the deferred `Spanned`-`Surf` tier, so it
stays silent — a message with no nameable token is the documented, tested un-located case
(`locateInMsg … == none`), not a bug. This only ADDS a quoted name to messages that had none; no
existing message text changes for a non-`.var` sub-term. -/
def nameHint : Surf → String
  | .var x => s!" ('{x}')"
  | _      => ""

-- Termination: the rank (synth = 0, check = 1) breaks the `check t → synth t` subsumption tie, as
-- in the spike; every other call is on a structural subterm of the `Surf`.
mutual
/-- Synthesize the value type of a `Surf` read as a VALUE. -/
def synthSV (Γ : NCtx) (e : Surf) : Infer IVTy :=
  match e with
  | .lit _     => return .int
  | .var x     => lookupInst Γ x                       -- HM: instantiate the scheme with fresh holes
  | .thunk b   => do let (B, φ) ← synthSC Γ b; return .U φ B   -- φ : Row — the body's (possibly poly) row
  | .pairS a b => do return .prod (← synthSV Γ a) (← synthSV Γ b)
  | .unitS     => return .unit
  | .annotS b t => do let A ← embVInst t; let _ ← checkSV Γ b A; return A
  -- HM (#53): a bare anonymous injection SYNTHESIZES with a fresh hole for the UNFILLED variant.
  -- `Left(e) : A + ?b` (`e : A`), `Right(e) : ?a + B` (`e : B`); unification resolves the hole from
  -- context (match arms / annotation / use site). Check mode (with an expected sum) is still preferred.
  | .inlS e    => do let A ← synthSV Γ e; return .sum A (← freshHole)
  | .inrS e    => do let B ← synthSV Γ e; return .sum (← freshHole) B
  | .foldS _   => throw "fold needs an expected μ type — annotate (ctor elaboration provides it)"
  | _          => throw "not a value (wrap a computation in braces)"
  termination_by (sizeOf e, 0)

/-- Check a `Surf` read as a VALUE against an expected value type. -/
def checkSV (Γ : NCtx) (e : Surf) (expected : IVTy) : Infer Unit :=
  match e, expected with
  | .inlS b,    .sum A _  => checkSV Γ b A
  | .inrS b,    .sum _ B  => checkSV Γ b B
  | .pairS a b, .prod A B => do let _ ← checkSV Γ a A; checkSV Γ b B
  -- T_Fold mirrored (ADR-0069): `fold v : μ.A` ⇐ `v : A[μ.A/0]` — the kernel's own unrollMu.
  | .foldS b,   .mu A     => do let U ← unrollI A; checkSV Γ b U
  -- T_Thunk mirrored (#45): push the expected computation type INTO the thunk body so check-mode-only
  -- forms (a bare `fun`, `Left`, …) drive off it instead of synth failing. The declared `φ` is an
  -- upper bound (over-approximating a thunk's latent effects is the safe direction), as in `annotS`.
  -- ADR-0088 (#48): name the OFFENDING effect(s) + the declared bound (agent-first: explicit, concise
  -- over a bare "exceeds the bound") — this is the site a `let rec` body with an undeclared effect
  -- (or any thunk-shaped mismatch) hits, so the message earns its keep across both call sites.
  | .thunk b,   .U φ B    => do
      let φ' ← checkSC Γ b B
      if (← subRow bigFuel φ' φ) then return ()
      else do
        let φ'r ← resolveRow bigFuel φ'
        let φr  ← resolveRow bigFuel φ
        let excess := φ'r.labels \ φr.labels
        throw s!"thunk body performs \{{showRow excess}}, exceeding its declared bound \{{showRow φr.labels}}"
  | .annotS b t, expected => do
      let A ← embVInst t
      let _ ← checkSV Γ b A
      unifyV bigFuel A expected                         -- HM subsumption (was structural `A = expected`)
  | e, expected => do
      let A ← synthSV Γ e
      unifyV bigFuel A expected                         -- HM subsumption (was structural `A = expected`)
  termination_by (sizeOf e, 2)

/-- Synthesize the computation type + effect row of a `Surf` read as a COMPUTATION. The row is an
`Row` (bite-0b item 3): an OPEN row when the computation is effect-polymorphic (`compose`'s body). -/
def synthSC (Γ : NCtx) (e : Surf) : Infer (ICTy × Row) :=
  match e with
  | .lit _   => return (.F .omega .int, botR)
  | .var x   => do return (.F .omega (← lookupInst Γ x), botR)   -- `ret` of the instantiated scheme
  | .thunk b => do let (B, φ) ← synthSC Γ b; return (.F .omega (.U φ B), botR)
  | .pairS a b => do return (.F .omega (.prod (← synthSV Γ a) (← synthSV Γ b)), botR)  -- value ⇒ ret
  -- force: the thunk's type must be `U φ B`. HM (bite-0b): a value HOLE here is an unknown thunk — the
  -- higher-order case (`$g` where `g` is a bare param). Unify it with `U ρ (chole)` (a FRESH ROW VAR ρ +
  -- a fresh computation hole) and return `(chole, ρ)`: the forced thunk's row is now POLYMORPHIC (item 3).
  -- `compose`'s `($f)`/`($g)` each mint a fresh ρ; the body's join collapses them to one `∀ρ` — so
  -- `compose : ∀ρ. (b→c!ρ)→(a→b!ρ)→(a→c!ρ)` instantiates at ⊥ (pure) AND a non-⊥ row.
  | .force b => do
      match (← resolve bigFuel (← synthSV Γ b)) with
      | .U φ B    => return (B, φ)
      | .vhole n  => do let C ← freshCHole; let ρ ← freshRow; assign n (.U ρ C); return (C, ρ)
      | _         => throw s!"force: not a thunk{nameHint b}"
  -- HM let-generalization: the RHS's value type `A` is generalized against `Γ` before binding, so a
  -- `let`-bound name is polymorphic (instantiated fresh per use) — the heart of bite-0.
  | .lett x e b => do
      let (Ce, φ₁) ← synthSC Γ e
      let (_, A) ← expectF Ce                            -- a higher-order RHS (`chole`) unifies to `F ω ?`
      -- VALUE RESTRICTION (bite-0b soundness gate): generalize ONLY a syntactic-value RHS
      -- (`{…}`/lit/var/pair — `isValueSurf`). A computation/effectful RHS stays MONOMORPHIC, so a
      -- latent effect can never escape a `let` disguised as a polymorphic type variable (the classic
      -- ML unsoundness). Must precede effect-typed poly (row vars) — an effectful returner with a
      -- would-be type var is exactly the trap. Pure/value RHS (the id/const case) still generalizes.
      let sch ← if isValueSurf e then generalize Γ A else pure ({ body := A } : Scheme)
      let (B, φ₂) ← synthSC ((x, sch) :: Γ) b
      return (B, ← joinRow bigFuel φ₁ φ₂)
  -- HM: a bare unannotated `fun` invents a FRESH domain hole (the move the old checker couldn't make —
  -- its "annotate the fun" error DISSOLVES). The lam's row is its body's, mirroring the checkSC lam arm.
  | .lam x b => do
      let a ← freshHole
      let (B, φ) ← synthSC ((x, a) :: Γ) b
      return (.arr .omega a B, φ)
  | .app f a => do
      let (cf, φ) ← synthSC Γ f
      match (← resolveC bigFuel cf) with
      | .arr _ A B => do let _ ← checkSV Γ a A; return (B, φ)
      -- bite-0b: the callee's type is still an unknown computation (`$g` forced to a `chole`). Unify it
      -- with `arr ω ? ?` (fresh value + comp holes) so a higher-order application (`($g) x`) types; the
      -- arg checks against the fresh domain, the result is the fresh codomain.
      | .chole n   => do
          let A ← freshHole; let B ← freshCHole
          assignC n (.arr .omega A B)
          let _ ← checkSV Γ a A
          return (B, φ)
      | _          => throw s!"app: callee is not a function{nameHint f}"
  | .binopS op a b => do
      let _ ← checkSV Γ a .int; let _ ← checkSV Γ b .int
      return (.F .omega (binopResTy op), botR)
  | .ifS c t e => do
      let _ ← checkSV Γ c boolTy
      let (C, φ₁) ← synthSC Γ t
      let φ₂ ← checkSC Γ e C
      return (C, ← joinRow bigFuel φ₁ φ₂)
  | .matchS s xl el xr er => do match (← resolve bigFuel (← synthSV Γ s)) with
      | .sum A B => do
          let (C, φ₁) ← synthSC ((xl, A) :: Γ) el
          let φ₂ ← checkSC ((xr, B) :: Γ) er C
          return (C, ← joinRow bigFuel φ₁ φ₂)
      -- an unresolved hole scrutinee: a Left/Right match REQUIRES a sum, so invent `?A + ?B` and unify
      -- (the principal type — mirrors `.splitS`'s `.vhole ⟹ prod` #55 move). Lets a bare-sum eliminator
      -- over an unannotated param (`bimap`/`eitherToResult`/`eitherToOption` in the generic prelude) type.
      | .vhole n  => do let A ← freshHole; let B ← freshHole
                        assign n (.sum A B)
                        let (C, φ₁) ← synthSC ((xl, A) :: Γ) el
                        let φ₂ ← checkSC ((xr, B) :: Γ) er C
                        return (C, ← joinRow bigFuel φ₁ φ₂)
      | _ => throw s!"match: scrutinee is not a sum{nameHint s}"
  | .splitS a b p body => do match (← resolve bigFuel (← synthSV Γ p)) with
      | .prod A B => synthSC ((b, B) :: (a, A) :: Γ) body
      -- #55: the scrutinee is an unresolved hole (a generic Option's element `a := (v * rest)` not yet
      -- solved). A split REQUIRES a product, so invent `?A × ?B` and unify — the principal type (mirrors
      -- the `.vhole ⟹ U`/`.chole ⟹ arr` moves for force/app). The fields' types flow from the body.
      | .vhole n  => do let A ← freshHole; let B ← freshHole
                        assign n (.prod A B); synthSC ((b, B) :: (a, A) :: Γ) body
      | _ => throw s!"split: scrutinee is not a product{nameHint p}"
  | .annotS b t => do
      let C ← embCInst t
      let φ ← checkSC Γ b C
      match effOf t with                              -- declared row (if any) is an upper bound — ④b
      | some ρ => if (← subRow bigFuel φ (embRow ρ)) then return (C, φ) else throw "inferred effect exceeds the declared row"
      | none   => return (C, φ)
  -- ── effects (ADR-0066 ④): each op ADDS its label to the row; handlers DISCHARGE it (`Finset.erase`).
  -- v1 simplification (marked): operation payload/result types are fixed to the surface convention
  -- (state cell + TVar contents + exn payload are `Int`, ADR-0030) — no payload-type threading yet.
  | .raise e     => do let _ ← checkSV Γ e .int; return (.F .omega .int, singR exnLabel)    -- result = payload (v1)
  | .handle e    => do let (B, φ) ← synthSC Γ e; return (B, ← eraseRow bigFuel exnLabel φ)   -- discharge throws
  | .getS        => return (.F .omega .int, singR stateLabel)
  | .putS e      => do let _ ← checkSV Γ e .int; return (.F .omega .unit, singR stateLabel)
  | .stateS e0 e => do let _ ← checkSV Γ e0 .int; let (B, φ) ← synthSC Γ e; return (B, ← eraseRow bigFuel stateLabel φ)
  | .atomS e     => do let (B, φ) ← synthSC Γ e; return (B, ← eraseRow bigFuel stmLabel φ)   -- discharge stm
  | .newS e      => do let _ ← checkSV Γ e .int; return (.F .omega .int, singR stmLabel)     -- TVar ref = Int (ADR-0030)
  | .readS e     => do let _ ← checkSV Γ e .int; return (.F .omega .int, singR stmLabel)
  | .writeS r w  => do let _ ← checkSV Γ r .int; let _ ← checkSV Γ w .int; return (.F .omega .unit, singR stmLabel)
  -- ── ADR-0069 (data) ──
  | .unitS     => return (.F .omega .unit, botR)
  | .unfoldS b => do match (← resolve bigFuel (← synthSV Γ b)) with   -- T_Unfold mirrored: F 1 (A[μ.A/0]), pure
                     | .mu A => do let U ← unrollI A; return (.F 1 U, botR)
                     | _     => throw s!"unfold: not a μ value{nameHint b}"
  | .matchD .. => throw "named match is elaborated away on the typed path — reaching the checker means the data env lacked its constructors (ADR-0069)"
  | .letRecS .. => throw "let rec is desugared away by the elaborator — reaching the checker means elabProg didn't run (ADR-0073)"
  | .divMark e => do let (B, φ) ← synthSC Γ e; return (B, ← insertRow bigFuel divLabel φ)  -- #46: mark the row divergent
  -- ── ADR-0070 (named capabilities) ──
  | .withCapS kind init name body => do
      match capKindLabel kind with
      | none => throw s!"with: unknown handler kind '{kind}'"
      | some ℓ => do
          if kind = "state" then let _ ← checkSV Γ init .int   -- the initial cell value is Int
          let capTy : IVTy := .cap ℓ
          let (B, φ) ← synthSC ((name, capTy) :: Γ) body   -- name : Cap ℓ in scope
          return (B, ← eraseRow bigFuel ℓ φ)                    -- the handler DISCHARGES ℓ
  | .dotPerform recv op args => do
      match (← resolve bigFuel (← synthSV Γ recv)) with
      | .cap ℓ =>
          -- ADR-0092 D1/D2: dispatch on the RECEIVER'S label first (`ℓ < 4` ⟹ built-in, `ℓ ≥ 4` ⟹ a
          -- user effect) — NOT on the op name. `capOpSig` is keyed globally by name only (sound for
          -- the four fixed built-ins, which never collide with EACH OTHER), but a user `effect` may
          -- freely reuse a built-in op NAME (`read`/`get`/…) on its own distinct label — checking
          -- `capOpSig op` before the label would let a same-named user op be wrongly shadowed by an
          -- unrelated built-in's signature (found live: `effect Net { read : … }` collided with the
          -- STM `read` op before this fix). Label-first makes the two tables genuinely disjoint.
          -- (A same-named user effect is now ALSO rejected one step earlier, at `effect` decl
          -- elaboration — `buildEnv`'s `.effectD` case — since built-in names are RESERVED v1-wide,
          -- closing a separate elaborator/MACHINE consistency gap; this dispatch fix stays correct
          -- and load-bearing regardless, it's what makes that reservation actually sound to rely on.)
          if ℓ < 4 then
            match capOpSig op with
            | none => throw s!"unknown capability op '{op}'"
            | some (ℓ', argTys, resTy) =>
                if ℓ != ℓ' then throw s!"cap op '{op}' expects a different capability (label mismatch)"
                else
                  -- match SurfArgs to the op's arity: each arg is a syntactic subterm (termination).
                  match args, argTys with
                  | .none,    []       => return (.F .omega (embV resTy), singR ℓ)
                  | .one a,   [t]      => do let _ ← checkSV Γ a (embV t); return (.F .omega (embV resTy), singR ℓ)
                  | .two a b, [t1, t2] => do let _ ← checkSV Γ a (embV t1); let _ ← checkSV Γ b (embV t2)
                                            return (.F .omega (embV resTy), singR ℓ)
                  | _, _ => throw s!"cap op '{op}' expects {argTys.length} argument(s)"
          else
              -- D2: total lookup over declared (ℓ, op) pairs; an undeclared op at a DECLARED user
              -- label is an ELABORATION error (never a kernel stuck — the program-derived instance
              -- is total BY CONSTRUCTION over what it declares, so "no entry" here is a genuine
              -- source error, not a gap to guess through).
              let effs ← (do return (← get).effects)
              match effs.find? (fun (_, ei) => ei.label == ℓ) with
              | none => throw s!"cap op '{op}': receiver's capability label is not a declared effect"
              | some (effName, ei) =>
                  match ei.ops.find? (fun (n, _, _) => n == op) with
                  | none => throw s!"unknown operation '{op}' for effect '{effName}'"
                  | some (_, argTy?, resTy) =>
                      match args, argTy? with
                      | .none,  none   => return (.F .omega (embV resTy), singR ℓ)
                      | .one a, some t => do let _ ← checkSV Γ a (embV t); return (.F .omega (embV resTy), singR ℓ)
                      | .none,  some _ => throw s!"effect '{effName}' op '{op}' expects 1 argument(s), got 0"
                      | .one _, none   => throw s!"effect '{effName}' op '{op}' expects 0 argument(s), got 1"
                      | .two .., _     => throw s!"effect '{effName}' op '{op}': v1 supports at most 1 argument"
      | _ => throw s!"cap op '{op}': receiver is not a capability value (Cap ℓ)"
  -- HM (#53): a bare anonymous injection in COMPUTATION position lowers to `ret (inj v)` — a value ⇒
  -- ret, with a fresh hole for the unfilled variant (mirrors the `synthSV` arm and `pairS` here).
  -- `fold` still needs an expected μ type (its unrolling is not a hole the unifier can invent).
  | .inlS p => do return (.F .omega (.sum (← synthSV Γ p) (← freshHole)), botR)
  | .inrS p => do return (.F .omega (.sum (← freshHole) (← synthSV Γ p)), botR)
  | .foldS _ => throw "fold needs an expected μ type — annotate (ctor elaboration provides it)"
  -- NO catch-all: synthSC now ENUMERATES every Surf constructor, so a NEW feature fails to compile
  -- here until it is typed — pipeline-completeness by construction (the operator's enforcement ask).
  termination_by (sizeOf e, 1)

/-- Check a `Surf` read as a COMPUTATION against an expected computation type. -/
def checkSC (Γ : NCtx) (e : Surf) (expected : ICTy) : Infer Row :=
  match e, expected with
  | .lam x b,   .arr _ A B => checkSC ((x, A) :: Γ) b B
  -- value-constructors in computation position lower to `ret v` — check the value against `A` of `F A`.
  | .inlS b,    .F _ (.sum A B)  => do let _ ← checkSV Γ (.inlS b) (.sum A B); return botR
  | .inrS b,    .F _ (.sum A B)  => do let _ ← checkSV Γ (.inrS b) (.sum A B); return botR
  | .pairS a b, .F _ (.prod A B) => do let _ ← checkSV Γ (.pairS a b) (.prod A B); return botR
  | .foldS b,   .F _ (.mu A)     => do let _ ← checkSV Γ (.foldS b) (.mu A); return botR
  | .thunk t,   .F _ (.U φ B)    => do let _ ← checkSV Γ (.thunk t) (.U φ B); return botR
  | .annotS b t, expected => do
      let C ← embCInst t
      let φ ← checkSC Γ b C
      let _ ← unifyC bigFuel C expected                 -- HM subsumption (was structural `C ≠ expected`)
      match effOf t with
        | some ρ => if (← subRow bigFuel φ (embRow ρ)) then return φ else throw "inferred effect exceeds the declared row"
        | none   => return φ
  | e, expected => do
      let (B, φ) ← synthSC Γ e
      let _ ← unifyC bigFuel B expected                 -- HM subsumption (was structural `B = expected`)
      return φ
  termination_by (sizeOf e, 3)
end

/-- End-to-end at the SURFACE: parse a source string, then type-check it as a computation (running the
inference monad + zonking so the reported type is hole-free for concrete programs). -/
def check (src : String) : Except String (CT × EffRow) := do
  let e ← Bang.Surface.parse src
  runInferC (synthSC [] e)

/-! ## Validation ③ — the Surf checker types ANNOTATED programs the spike could not.

The limitation lift: an annotated lambda/injection now type-checks, because the ascription feeds
check-mode the type synthesis lacked. -/

-- the annotated identity now CHECKS at `Int -> Int` (= arr ω int (F ω int)). (spike: couldn't synth `fun`.)
#guard check "( fun x => x : Int -> Int )" == .ok (.arr .omega .int (.F .omega .int), ⊥)
-- annotated injection now CHECKS at a sum type. (spike: couldn't synth bare `Left`.)
#guard check "( Left(3) : Int + Int )" == .ok (.F .omega (.sum .int .int), ⊥)
-- inference still flows where it can: application of an annotated function.
#guard check "( fun x => x : Int -> Int ) 5" == .ok (.F .omega .int, ⊥)
-- arithmetic + let, fully inferred (no annotation needed).
#guard check "let x = 2 in x + 3" == .ok (.F .omega .int, ⊥)
-- a comparison returns Bool = 1 + 1.
#guard check "1 < 2" == .ok (.F .omega (.sum .unit .unit), ⊥)
-- product destructure, inferred.
#guard check "let p = (3, 4) in (let (a, b) = p in a)" == .ok (.F .omega .int, ⊥)

-- #53 — a BARE anonymous injection now SYNTHESIZES (fresh hole for the unfilled variant), so idiomatic
-- raw-sum code type-checks WITHOUT an annotation on the typed-default path (surfaced by #51's check-first).
-- match over a bare `Right(7)`: the scrutinee's Left-variant hole is discarded ⇒ the RESULT is hole-free.
#guard check "match Right(7) { Left(a) -> 0, Right(x) -> x }" == .ok (.F .omega .int, ⊥)
-- let-bound bare injection: the value RHS generalizes over the phantom variant; the match resolves it.
#guard (match check "let x = Right(7) in match x { Left(a) -> 0, Right(x) -> x }" with
        | .ok (.F .omega .int, _) => true | _ => false)
-- the phantom variant RESOLVES from the OTHER match arm's use (Left(3); the Right arm forces it to Int).
#guard check "match Left(3) { Left(a) -> a, Right(x) -> x }" == .ok (.F .omega .int, ⊥)
-- the ANNOTATED form is UNCHANGED — check mode (with an expected sum) is still preferred over synth.
#guard check "( Left(3) : Int + Int )" == .ok (.F .omega (.sum .int .int), ⊥)
-- a bare TOP-LEVEL injection with no resolving context types as a POLYMORPHIC sum: the filled variant
-- is concrete, the unfilled stays a hole (a `tvar` in the reserved hole range) — legitimate HM
-- polymorphism (`Int + ∀b. b`), NOT a wrong accept (it erases-and-runs as a well-formed `Left` value).
#guard (match check "Left(3)"  with | .ok (.F _ (.sum .int (.tvar _)), _) => true | _ => false)
#guard (match check "Right(3)" with | .ok (.F _ (.sum (.tvar _) .int), _) => true | _ => false)

-- REJECTIONS — the surface checker is sound (the synth hole never rescues an ILL-typed program:
-- an injection forced into a concrete NON-sum type still fails via `unifyV`):
#guard (match check "1 + Left(0)" with | .error _ => true | _ => false)         -- non-Int operand
#guard (match check "( fun x => x : Int -> Int ) Left(0)" with | .error _ => true | _ => false)  -- arg type
#guard (match check "( 3 : Int + Int )" with | .error _ => true | _ => false)    -- 3 is not a sum
-- mismatched match arms are STILL caught: Left arm returns Int, Right arm a product ⇒ unify fails.
#guard (match check "match Right(7) { Left(a) -> 0, Right(x) -> (x, x) }" with | .error _ => true | _ => false)

/-! ## Validation ⑦ — HM inference + let-polymorphism (ADR-0075 bite-0, in-place).

The spike's substrate, now folded into the PRODUCTION checker: a bare unannotated `fun` INFERS its
domain (the old "annotate the fun" error DISSOLVED); a `let`-bound value is GENERALIZED and
instantiated fresh per use, so ONE definition types at MULTIPLE types AND runs end-to-end through
`bang eval` (`runTypedYieldsInt` = the real parse→elab→check→lower→`Source.eval` pipeline). -/

-- a bare unannotated identity now SYNTHESIZES `∀a. a -> F a` (the dissolved error): domain hole = codomain hole.
#guard (match check "fun x => x" with | .ok (.arr _ (.tvar a) (.F _ (.tvar b)), _) => a == b | _ => false)

-- THE KILLER: one `let`-bound `id` used at Int AND at (Int * Int) in one program — TYPES (needs
-- let-generalization; without it the second use clashes). The RUN guards (`runTypedYieldsInt`) live
-- at the file's end, after that helper is defined — Validation ⑦b.
def killerId : String :=
  "let id = {fun x => x} in (let a = ($id) 5 in (let p = ($id) (1, 2) in (let (x, y) = p in a + x)))"
#guard (match check killerId with | .ok _ => true | _ => false)

-- `const = fun x => fun y => x` used at TWO types (Int×Int-agnostic 2nd arg) — TYPES.
def killerConst : String :=
  "let const = {fun x => fun y => x} in (let a = (($const) 5) 9 in (let b = (($const) 7) (1, 2) in a + b))"
#guard (match check killerConst with | .ok _ => true | _ => false)

-- FAIL-LOUD boundary: occurs / self-application `fun x => ($x) x` — forcing a param hole hits the
-- bite-0 higher-order boundary (a value hole can't become a computation; `CTy` has no `tvar`) → a
-- DEFINED error, never a hang or a wrong accept.
#guard (match check "fun x => ($x) x" with | .error _ => true | _ => false)

-- VALUE RESTRICTION (bite-0b soundness gate): a NON-value `let`-RHS (here an `if` returning a
-- function — a computation, not a syntactic value) stays MONOMORPHIC, so using it at TWO types
-- FAILS. Contrast the `let id = {fun…}` value case above, which DOES generalize. This is the guard
-- that must hold before effect-typed poly can generalize an effectful returner (the ML value restriction).
#guard (match check "let f = (if 1 < 2 then {fun x => x} else {fun x => x}) in (let a = ($f) 5 in (let p = ($f) (1, 2) in (let (x, y) = p in a + x)))" with | .error _ => true | _ => false)

/-! ## Validation ④ — the Surf checker AGREES with the spike's `Comp` checker on the lowering.

For terms in the INTERSECTION of what both handle (the Comp spike is pure-fragment: no `binop`, no
annotations), `synthSC e` on the surface and `synthC (lower e)` on its lowering agree — the
through-lowering soundness chain, differential-tested. -/
#guard (check "let x = 3 in x") == (infer "let x = 3 in x")
#guard (check "let p = (3, 4) in (let (a, b) = p in a)") == (infer "let p = (3, 4) in (let (a, b) = p in a)")

/-! ## Validation ⑤ — effect-row inference + handler discharge (ADR-0066 ④ = #5).

Each `perform` ADDS its label to the inferred row; each handler DISCHARGES it. An UNHANDLED effect
surfaces in the row (the static "this computation can throw/touch state/stm" signal #5 is about). -/
-- raise contributes {throws}; unhandled, it shows in the row.
#guard check "raise 7" == .ok (.F .omega .int, {exnLabel})
-- handle DISCHARGES throws → empty row.
#guard check "handle (raise 7)" == .ok (.F .omega .int, ⊥)
-- get contributes {state}; the state handler discharges it. (`(get)` — bare `get` hits the #31 quirk.)
#guard check "(get)" == .ok (.F .omega .int, {stateLabel})
#guard check "state 0 in get" == .ok (.F .omega .int, ⊥)
-- a put;get sequence under `state`: the whole row is discharged.
#guard check "state 0 in (let z = put 7 in get)" == .ok (.F .omega .int, ⊥)
-- stm: `new` contributes {stm}; `atomically` discharges it.
#guard check "atomically (new 0)" == .ok (.F .omega .int, ⊥)
-- a type error INSIDE an effect op is still caught (raise of a non-Int payload).
#guard (match check "handle (raise Left(0))" with | .error _ => true | _ => false)

/-! ## Stage ④b — type DISPLAY (#5's "type display": effect rows made visible).

Render the inferred `(CTy, EffRow)` back to surface notation, with the row shown as `! {throws, …}`.
This is what makes effect-typed signatures legible: you run the checker and SEE `Int -> Int ! {throws}`.
(`effName`/`showRow` moved ahead of `checkSV`, above — same definitions.) -/

mutual
def showVTy : VT → String
  | .int      => "Int"
  | .unit     => "Unit"
  | .sum a b  => s!"({showVTy a} + {showVTy b})"
  | .prod a b => s!"({showVTy a} * {showVTy b})"
  | .U φ b    => let r := showRow φ; s!"Thunk{if r.isEmpty then "" else s!"!\{{r}}"} {showCTy b}"
  | .cap ℓ    => s!"Cap {ℓ}"
  | .mu a     => s!"(mu. {showVTy a})"
  | .tvar n   => s!"#{n}"
def showCTy : CT → String
  | .F _ a     => showVTy a                                   -- a returner displays as the value it yields
  | .arr _ a b => s!"{showVTy a} -> {showCTy b}"
end

/-- Render a computation's full type: the value/arrow shape plus its effect row as a `! {…}` suffix.
`effects` (ADR-0092 D2, default `[]`) names any declared user-effect label present in the row —
see `showRow`. -/
def showType (B : CT) (φ : EffRow) (effects : List (String × EffectInfo) := []) : String :=
  let r := showRow φ effects
  if r.isEmpty then showCTy B else s!"{showCTy B} ! \{{r}}"

/-- End-to-end: parse + check a source string, then DISPLAY its type (or the error). -/
def display (src : String) : String :=
  match check src with
  | .ok (B, φ) => showType B φ
  | .error e   => s!"error: {e}"

-- pure types show with no effect suffix; effectful ones surface their row.
#guard display "( fun x => x : Int -> Int )"       == "Int -> Int"
#guard display "( fun x => raise x : Int -> Int )" == "Int -> Int ! {throws}"
#guard display "raise 7"                            == "Int ! {throws}"
#guard display "handle (raise 7)"                   == "Int"
#guard display "state 0 in get"                     == "Int"
#guard display "(get)"                              == "Int ! {state}"
#guard display "let x = 2 in x + 3"                 == "Int"

/-! ## Stage ④b (writing) — effect SIGNATURES: declare `! {ρ}`, the checker enforces it (#5).

A declared row is an UPPER BOUND (the inferred effect must be ⊆ it). No annotation = unconstrained
(stay inferred) — the optional-annotation philosophy. So a signature is something you can RELY on. -/
-- a declared row that COVERS the inferred effect passes (and the inferred effect is what displays).
#guard display "( fun x => raise x : Int -> Int ! {throws} )" == "Int -> Int ! {throws}"
-- a PURE function satisfies a may-throw signature (⊥ ⊆ {throws}).
#guard display "( fun x => x : Int -> Int ! {throws} )" == "Int -> Int"
-- declaring PURITY (`! {}`) for a throwing function is REJECTED — the signature is enforced.
#guard (match check "( fun x => raise x : Int -> Int ! {} )" with | .error _ => true | _ => false)
-- declaring the WRONG effect ({state} for a throwing fn) is REJECTED.
#guard (match check "( fun x => raise x : Int -> Int ! {state} )" with | .error _ => true | _ => false)
-- un-annotated arrow stays unconstrained: a throwing fn is fine, effect inferred + shown.
#guard display "( fun x => raise x : Int -> Int )" == "Int -> Int ! {throws}"

/-! ## Stage ⑤b — type-directed operator RESOLUTION (#24 piece 2; ADR-0068 decision 3).

`a + b` on a non-Int operand type resolves to the matching `impl`'s op: `elabS` rewrites the
`binopS` into an application of the impl's ANNOTATED lambda, so the existing checker machinery
types the call site — zero new typing rules. The typed path is a NEW entry (`checkProg` /
`displayProg` / `runTypedYieldsInt`); the untyped `parse → lower → eval` path is untouched.

v1 conventions (monomorphic, ADR-0040/0027): an operator resolves through its trait-op NAME
(`+` ↦ `add`, Rust-style); trait-op params are implicitly `Self`-typed; `Self` in the declared
ret type is substituted by the impl target at env build; impl bodies are spliced RAW (kernel ops
only — a nested trait-op inside one is reported by the checker at the unresolved binop). -/

/-- The trait-op name an operator resolves through (`a + b` ⇒ the instance's `add`). -/
def binopName : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .lt  => "lt"  | .eq  => "eq"

/-- Substitute the impl TARGET for `Self` in a trait signature type (env-build time; `tyBoth`
never sees a raw `tSelf`). Enumerated — a new `Ty` former fails here until handled. -/
def substSelf (target : Ty) : Ty → Ty
  | .tSelf     => target
  | .tInt      => .tInt
  | .tUnit     => .tUnit
  | .tName n   => .tName n
  | .tApp n (.one a)   => .tApp n (.one (substSelf target a))              -- inlined (termination sees the subterms)
  | .tApp n (.two a b) => .tApp n (.two (substSelf target a) (substSelf target b))
  | .tVar n    => .tVar n
  | .tMu b     => .tMu   (substSelf target b)
  | .tArr a b  => .tArr  (substSelf target a) (substSelf target b)
  | .tSum a b  => .tSum  (substSelf target a) (substSelf target b)
  | .tProd a b => .tProd (substSelf target a) (substSelf target b)
  | .tThunk t  => .tThunk (substSelf target t)
  | .tEff ns t => .tEff ns (substSelf target t)

/-- Substitute the concrete carrier `T` for a bound type VARIABLE `tv` in a bounded-fn's declared
type (`List a -> a` at `a := Int` ⟹ `List Int -> Int`). A `.tName tv` is the bound var; any other
`.tName` is a real data name, left for `resolveTy`. Enumerated (a new `Ty` former fails here). -/
def substTyVar (tv : String) (target : Ty) : Ty → Ty
  | .tName n   => if n == tv then target else .tName n
  | .tApp n (.one a)   => .tApp n (.one (substTyVar tv target a))
  | .tApp n (.two a b) => .tApp n (.two (substTyVar tv target a) (substTyVar tv target b))
  | .tSelf     => .tSelf
  | .tInt      => .tInt
  | .tUnit     => .tUnit
  | .tVar n    => .tVar n
  | .tMu b     => .tMu   (substTyVar tv target b)
  | .tArr a b  => .tArr  (substTyVar tv target a) (substTyVar tv target b)
  | .tSum a b  => .tSum  (substTyVar tv target a) (substTyVar tv target b)
  | .tProd a b => .tProd (substTyVar tv target a) (substTyVar tv target b)
  | .tThunk t  => .tThunk (substTyVar tv target t)
  | .tEff ns t => .tEff ns (substTyVar tv target t)

/-- Right-nested arrow type from a param count + result (`mkArrs 2 T r = T -> T -> r`). -/
def mkArrs : Nat → Ty → Ty → Ty
  | 0,     _, r => r
  | n + 1, d, r => .tArr d (mkArrs n d r)

/-- Peel `n` domain arrows off a type, returning the tail result type (`stripArrows 1 (List a -> a) = a`). -/
def stripArrows : Nat → Ty → Ty
  | 0,     t          => t
  | n + 1, .tArr _ b  => stripArrows n b
  | _ + 1, t          => t   -- fewer arrows than params: return what's left (a shape error the checker catches)

/-- Curried lambda from a param-name list over a body (`[x, y] ↦ fun x => fun y => body`). -/
def funFromParams : List String → Surf → Surf
  | [],      body => body
  | p :: ps, body => .lam p (funFromParams ps body)

/-! ## HKT helpers (ADR-0082): kind-check · carrier-head extraction · application spine. -/

/-- KIND-CHECK a trait method's type against the trait's constructor-kinded parameters (Stage A). v1 kinds
are ARITY: a trait param `f` is `Type→Type` (arity 1), so an applied `f a` is well-formed but `f a b`
(arity 2) is a kind error. Structural over `Ty` (`TyArgs` inlined for termination, like `substSelf`);
non-application formers just recurse. A method var (`a`, `b`) or data name applied wrongly is NOT checked
here (needs the decl env) — the injectivity unifier (Stage B) catches the rest. -/
def kindCheckTy (params : List String) : Ty → Except String Unit
  | .tApp n (.one a)   => do
      if params.contains n then pure () else pure ()          -- arity-1 use of a trait param: well-kinded
      kindCheckTy params a
  | .tApp n (.two a b) => do
      if params.contains n then
        throw s!"kind error: trait parameter '{n}' is applied to 2 arguments (v1 kind ceiling is arity 1, `{n} a`)"
      kindCheckTy params a; kindCheckTy params b
  | .tArr a b  => do kindCheckTy params a; kindCheckTy params b
  | .tSum a b  => do kindCheckTy params a; kindCheckTy params b
  | .tProd a b => do kindCheckTy params a; kindCheckTy params b
  | .tThunk t  => kindCheckTy params t
  | .tMu t     => kindCheckTy params t
  | .tEff _ t  => kindCheckTy params t
  | _          => pure ()

/-- The carrier CONSTRUCTOR name at the head of an impl target / result annotation (`Option Int` ↦ `Option`,
`Option` ↦ `Option`). The key an HK impl resolves on (ADR-0082 §4). -/
def hktCtorHead : Ty → Option String
  | .tName n  => some n
  | .tApp n _ => some n
  | .tEff _ t => hktCtorHead t
  | _         => none

/-- Substitute the carrier CONSTRUCTOR name for a higher-kinded bound var at every `tApp` HEAD (ADR-0082
Case B): `f a ↦ Option a` when the bound var `v = "f"` and the resolved carrier `ctor = "Option"`. The
carrier var appears only as an application head (arity 1, `f a`), never as a bare `tName` — that's an
ordinary tyvar, substituted by `substTyVar`. This is the *surface-level* realization of injectivity's
`f := Option`: monomorphize the abstract carrier once it's pinned at a concrete use. -/
def substCarrierHead (v ctor : String) : Ty → Ty
  | .tApp n (.one a)   => .tApp (if n == v then ctor else n) (.one (substCarrierHead v ctor a))
  | .tApp n (.two a b) => .tApp (if n == v then ctor else n) (.two (substCarrierHead v ctor a) (substCarrierHead v ctor b))
  | .tArr a b  => .tArr  (substCarrierHead v ctor a) (substCarrierHead v ctor b)
  | .tSum a b  => .tSum  (substCarrierHead v ctor a) (substCarrierHead v ctor b)
  | .tProd a b => .tProd (substCarrierHead v ctor a) (substCarrierHead v ctor b)
  | .tThunk t  => .tThunk (substCarrierHead v ctor t)
  | .tMu t     => .tMu    (substCarrierHead v ctor t)
  | .tEff ns t => .tEff ns (substCarrierHead v ctor t)
  | t          => t

/-- Match a bounded-fn RESULT-type pattern (`f a`) against the concrete result annotation (`Option Int`),
collecting the ORDINARY tyvar bindings (`a ↦ Int`) — the injectivity-decomposition of ADR-0082 Stage B,
realized structurally at the Surf pre-pass (the carrier head `f := Option` is read off separately by
`hktCtorHead`; here we peel the arg positions). A `tName` in the pattern is a tyvar bound to the concrete
arg; every other former recurses in parallel. Non-aligning shapes contribute nothing (a later resolve/
kind-check catches a genuinely ill-typed use). -/
def hktMatch : Ty → Ty → List (String × Ty)
  | .tName v,           c                 => [(v, c)]
  | .tApp _ (.one p),   .tApp _ (.one c)  => hktMatch p c
  | .tApp _ (.two p q), .tApp _ (.two c d) => hktMatch p c ++ hktMatch q d
  | .tArr p q,          .tArr c d         => hktMatch p c ++ hktMatch q d
  | .tProd p q,         .tProd c d        => hktMatch p c ++ hktMatch q d
  | .tSum p q,          .tSum c d         => hktMatch p c ++ hktMatch q d
  | .tThunk p,          .tThunk c         => hktMatch p c
  | .tEff _ p,          c                 => hktMatch p c
  | p,                  .tEff _ c         => hktMatch p c
  | _,                  _                 => []

/-- Does a trait's op-sig list contain an op of this name? -/
def sigsHasOp : Option (List OpSig) → String → Bool
  | some sigs, nm => sigs.any (fun s => s.name == nm)
  | none,      _  => false

/-- The head variable + argument list of a left-nested application spine (`f a b` ↦ `some ("f", [a, b])`),
`none` if the head is not a bare variable. Used to recognize an HK method call `fmap inc x`. -/
def appSpine : Surf → Option (String × List Surf)
  | .var x   => some (x, [])
  | .app f a => (appSpine f).map (fun (h, as) => (h, as ++ [a]))
  | _        => none

/-- One resolvable instance op: the resolution key (`opName` × structural `target`) plus what
the elaborated call site needs. `body` is PRE-ELABORATED at env build (ADR-0069 upgraded
piece-2's raw splice: nested ctors and earlier ops inside an impl body now resolve). PUBLIC
(#60 seam): forced by `ElabEnv`'s field type — additive visibility only, no behavior change. -/
public structure Inst where
  opName   : String
  target   : VT       -- the structural resolution key (ADR-0068 decision 2)
  targetTy : Ty       -- the impl's declared target, for the elaborated annotation
  retTy    : Ty       -- the trait sig's ret type, Self-substituted
  params   : List String
  body     : Surf

public abbrev InstEnv := List Inst

/-- One data constructor's elaboration record (ADR-0069). For a GENERIC data type (`params ≠ []`,
ADR-0069 bite-1) `payloadClosed`/`dataTy` are placeholders (a generic ctor has no ONE closed type —
it is monomorphized per use); the concrete μ is built from `params`/`payloadGen` at the use site by
`monoData`, gated on `params.isEmpty`. PUBLIC (#60 seam): forced by `ElabEnv`'s field type —
additive visibility only, no behavior change. -/
public structure CtorInfo where
  dataName      : String
  idx           : Nat        -- position in decl order (the sum injection)
  total         : Nat        -- constructor count (right-nested sum shape)
  arity         : Nat        -- payload arity (≤ 2 in v1)
  payloadClosed : List Ty    -- MONOMORPHIC: payload types, the data's own name resolved to the CLOSED μ
  dataTy        : Ty         -- MONOMORPHIC: the closed μ type (`tMu body`)
  params        : List String := []   -- GENERIC type params ([] = monomorphic; ADR-0069 bite-1)
  payloadGen    : List Ty    := []    -- GENERIC: this ctor's SURFACE payload template (params as `tName`, self as `tApp`)

/-- A GENERIC data declaration's template (ADR-0069 bite-1): its type params + each ctor's surface
payload types (params free as `tName`, self-reference as `tApp Name params`). Monomorphized to a
closed μ by `monoData` per concrete instantiation (`List Int` ↦ `μX. Unit + (Int × X)`). Only
generic (`params ≠ []`) decls live here; monomorphic decls stay in `aliases` (byte-identical path).
PUBLIC (#60 seam): forced by `ElabEnv`'s field type — additive visibility only, no behavior
change. -/
public structure GenData where
  params : List String
  ctors  : List (String × List Ty)

/-- A bounded generic function template (bite-2, ADR-0080): `fn fold(xs) : List a -> a where Monoid a
= …`. Stored RAW (its type mentions the bound var `tyVar`, its body references the trait's ops by
name + itself recursively); monomorphized per concrete use by substituting `tyVar := T` and splicing
the resolved `Trait T` instance's ops. PUBLIC (#60 seam): forced by `ElabEnv`'s field type —
additive visibility only, no behavior change. -/
public structure BoundedFn where
  name       : String
  params     : List String
  declaredTy : Ty
  traitName  : String
  tyVar      : String
  body       : Surf

/-- One impl op kept in RAW (un-elaborated) form, with the trait sig's `Self`-based ret type — so a
bounded-fn monomorphization can re-elaborate it at a concrete carrier `T` (its trait ops resolve at
`T`, exactly as `buildEnv`'s pre-elaboration does). PUBLIC (#60 seam): forced by `RawImpl`'s field
type — additive visibility only, no behavior change. -/
public structure RawOp where
  name   : String
  params : List String
  body   : Surf
  retTy  : Ty          -- the trait sig's ret type (`Self`-based; `Self ↦ T` at use)

/-- One impl kept RAW + keyed by its resolved carrier, for bounded-fn instance resolution. PUBLIC
(#60 seam): forced by `ElabEnv`'s field type — additive visibility only, no behavior change. -/
public structure RawImpl where
  traitName : String
  targetVT  : VT
  ops       : List RawOp

/-- One higher-kinded impl (ADR-0082), kept keyed on the carrier CONSTRUCTOR NAME (`Functor Option` ⟹
`ctorName = "Option"`) rather than a resolved carrier VT — an HK carrier (`Option`, arity 1) has no
closed VT until applied. `ops` are the impl's op defs, spliced monomorphically at each concrete use.
PUBLIC (#60 seam): forced by `ElabEnv`'s field type — additive visibility only, no behavior
change. -/
public structure HktImpl where
  traitName : String
  ctorName  : String
  ops       : List Bang.Surface.OpDef

/-- The full elaboration environment: instance ops + data constructors + type aliases + generic decls
+ bounded generic functions + raw impls (for bounded-fn monomorphization) + higher-kinded traits/impls
+ user EFFECT decls (ADR-0092 D1/D2 — name ↦ allocated label + op signatures). PUBLIC (#60 seam):
the law-runner harness needs a real, constructed `ElabEnv` to drive `checkLawOn` — additive
visibility only, no behavior change. -/
public structure ElabEnv where
  insts    : InstEnv
  ctors    : List (String × CtorInfo)
  aliases  : List (String × Ty)
  gen      : List (String × GenData) := []
  bfns     : List (String × BoundedFn) := []
  rawImpls : List RawImpl := []
  hktTraits   : List (String × List String) := []   -- HK trait NAME × its constructor-kinded params (`Functor` ↦ `["f"]`)
  hktMethodOf : List (String × String) := []         -- HK method opName × its trait name (`fmap` ↦ `Functor`)
  hktImpls    : List HktImpl := []                    -- HK impls, keyed by carrier ctor name
  effects     : List (String × EffectInfo) := []      -- ADR-0092 D1/D2: effect NAME ↦ its label + op sigs

/-- k-ary payload as a right-nested product (`[] ↦ Unit`, the 0-ary payload). -/
def prodOfTys : List Ty → Ty
  | []        => .tUnit
  | [t]       => t
  | t :: rest => .tProd t (prodOfTys rest)

/-- N constructors as a right-nested sum in decl order. -/
def sumOfTys : List Ty → Ty
  | []        => .tUnit   -- unreachable (≥ 1 ctor enforced at env build)
  | [t]       => t
  | t :: rest => .tSum t (sumOfTys rest)

/-- Are these already-parsed type-application args EXACTLY the decl's own params (in order)? — the
self-recursion test (`data List a` sees `List a` in a payload ⟹ the μ-bound var, not a re-instantiation;
ADR-0069 bite-1). A nested DIFFERENT instantiation (`List (List a)`, `Rose`) is NOT self — v1 monomorphizes
it via `monoData` instead (finite: it references an EARLIER decl). -/
def argsAreParams (params : List String) : List Ty → Bool
  | []      => params == []
  | ty :: rest => match params with
                  | p :: ps => (ty == .tName p) && argsAreParams ps rest
                  | []      => false

mutual
/-- Monomorphize `name argTys` to its CLOSED μ (ADR-0069 bite-1). `List Int` ↦ `μX. Unit + (Int × X)`:
substitute the args for the decl's params in every ctor payload (self-reference ↦ the μ-bound var 0),
right-nest into sum/product, μ-wrap. Fuel bounds decl-nesting depth (a cyclic generic instantiation
fail-louds). The kernel only ever sees this closed μ (elaborate-to-mono; kernel untouched). -/
def monoData (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → String → List Ty → Except String Ty
  | 0,        _,    _      => .error "type monomorphization out of fuel (cyclic generic instantiation?)"
  | fuel + 1, name, argTys => do
      match gen.lookup name with
      | none    => .error s!"unknown generic type '{name}'"
      | some gd =>
        if gd.params.length != argTys.length then
          .error s!"type '{name}' expects {gd.params.length} argument(s), got {argTys.length}"
        else do
          let σ := gd.params.zip argTys
          let openPays ← gd.ctors.mapM (fun c =>
            c.2.mapM (resolveTyG gen aliases fuel σ (some (name, gd.params))))
          return .tMu (sumOfTys (openPays.map prodOfTys))

/-- Resolve a type in a GENERIC template context: `σ` substitutes params for concrete args, `self?`
identifies the recursive self-application (↦ the μ-bound `tVar 0` — v1 has no nested self-binders so
depth is always 0, ADR-0069). A `tApp` of ANOTHER (or the same, different-args) generic name recurses
through `monoData`. `tName`s resolve param → σ, else the monomorphic alias env. -/
def resolveTyG (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → List (String × Ty) → Option (String × List String) → Ty → Except String Ty
  | 0,        _, _,     _  => .error "type resolution out of fuel"
  | fuel + 1, σ, self?, ty =>
    match ty with
    | .tName n   =>
        match σ.lookup n with
        | some t => .ok t                                    -- a type PARAM → its concrete arg
        | none   =>
          match self? with
          | some (sn, []) => if n == sn then .ok (.tVar 0)   -- NULLARY self (monomorphic self-ref)
                             else resolveName gen aliases n
          | _             => resolveName gen aliases n
    | .tApp n args =>
        match self? with
        | some (sn, sps) =>
            if n == sn && argsAreParams sps args.toList then .ok (.tVar 0)   -- self-recursion → μ-bound var
            else do let args' ← args.toList.mapM (resolveTyG gen aliases fuel σ self?)
                    monoData gen aliases fuel n args'
        | none => do let args' ← args.toList.mapM (resolveTyG gen aliases fuel σ self?)
                     monoData gen aliases fuel n args'
    | .tInt      => .ok .tInt
    | .tUnit     => .ok .tUnit
    | .tSelf     => .ok .tSelf
    | .tVar n    => .ok (.tVar n)
    | .tMu b     => do return .tMu   (← resolveTyG gen aliases fuel σ self? b)
    | .tArr a b  => do return .tArr  (← resolveTyG gen aliases fuel σ self? a) (← resolveTyG gen aliases fuel σ self? b)
    | .tSum a b  => do return .tSum  (← resolveTyG gen aliases fuel σ self? a) (← resolveTyG gen aliases fuel σ self? b)
    | .tProd a b => do return .tProd (← resolveTyG gen aliases fuel σ self? a) (← resolveTyG gen aliases fuel σ self? b)
    | .tThunk t  => do return .tThunk (← resolveTyG gen aliases fuel σ self? t)
    | .tEff ns t => do return .tEff ns (← resolveTyG gen aliases fuel σ self? t)

/-- A bare type NAME: a monomorphic alias, else fail-loud (a generic name used WITHOUT args, or a typo). -/
def resolveName (gen : List (String × GenData)) (aliases : List (String × Ty)) (n : String) : Except String Ty :=
  match aliases.lookup n with
  | some t => .ok t
  | none   => match gen.lookup n with
              | some _ => .error s!"generic type '{n}' needs type argument(s) (`{n} …`)"
              | none   => .error s!"unknown type name '{n}'"
end

/-- Close a type over the elaboration env: monomorphic names via `aliases`, generic applications
(`List Int`) monomorphized via `monoData` (ADR-0069 bite-1). The public entry (σ empty, no self). -/
def resolveTy (gen : List (String × GenData)) (aliases : List (String × Ty)) (t : Ty) : Except String Ty :=
  resolveTyG gen aliases 1000 [] none t

/-- Inject a payload at ctor position `i` of `n` (right-nested sum; `n = 1` ⇒ no sum wrapper). -/
def injSum : Nat → Nat → Surf → Surf
  | 0,     1, p => p
  | 0,     _, p => .inlS p
  | i + 1, n, p => .inrS (injSum i (n - 1) p)

/-- The elaborated ctor intro: the injected payload, μ-folded, ANNOTATED at the data type —
check-mode then drives T_Fold via `unrollMu`; no new typing rule. -/
def ctorIntro (ci : CtorInfo) (payload : Surf) : Surf :=
  .annotS (.foldS (injSum ci.idx ci.total payload)) ci.dataTy

/-- A GENERIC ctor intro (ADR-0079 annotation-FREE, #55): the same μ-folded injection, ANNOTATED at the
data type's TEMPLATE μ — its type params left as markers `.tVar (paramBase + i)`. `embVInst` turns each
marker into a fresh hole when the checker embeds the annotation, so the concrete element type is INFERRED
by unifying the fields (no user `: List Int` needed). Built by reusing `monoData` with the params fed
back as marker args (`data List a` at args `[â]` ⟹ `μX. Unit + (â × X)`). -/
def genTemplateTy (env : ElabEnv) (ci : CtorInfo) : Except String Ty :=
  let markers := (List.range ci.params.length).map (fun i => Ty.tVar (paramBase + i))
  monoData env.gen env.aliases 1000 ci.dataName markers

def genCtorIntro (env : ElabEnv) (ci : CtorInfo) (payload : Surf) : Except String Surf := do
  return .annotS (.foldS (injSum ci.idx ci.total payload)) (← genTemplateTy env ci)

/-- Shadow `bs` out of a subterm-tracking set, then (if `add`) re-introduce them AS subterms. Every
binder shadows — a re-bound name is no longer the tracked parameter/subterm, which is what keeps the
analysis SOUND under name-shadowing; only a match/split on a `matchable` scrutinee re-adds its pattern
binders (they are strict subterms of the parameter). -/
def shadowAdd (bs : List String) (add : Bool) (l : List String) : List String :=
  let l' := l.filter (fun n => !bs.contains n)
  if add then bs ++ l' else l'

/-- Is `s` a variable currently known to be the recursion parameter or a strict subterm of it (so
matching it yields strict subterms)? Only a bare variable qualifies — matching a COMPUTED value gives
no subterm-of-parameter guarantee. -/
def scrutMatch (matchable : List String) : Surf → Bool
  | .var v => matchable.contains v
  | _      => false

/-- One SLOT's tracking state (ADR-0091 #50): `matchable` = the parameter/subterms you may match to
descend, `subterms` = the strict subterms (the only legal recursive-call arguments FOR THIS SLOT).
`structOK` v1 (single-arg) is `Slot × Slot` inline; the multi-slot generalization below makes it a
`List Slot`, ONE per curried/tupled recursion parameter, indexed left-to-right. -/
abbrev Slot := List String × List String

/-- Shadow a binder out of EVERY slot uniformly (ADR-0091): a binder that re-binds some name `n`
shadows `n` out of whichever slot(s) currently track it — at most one slot ever contains a given
name (they partition the recursion's parameters), so this is exactly `shadowAdd` applied
slot-by-slot, safe to broadcast across the whole list. -/
def shadowAddAll (bs : List String) (add : Bool) (slots : List Slot) : List Slot :=
  slots.map (fun (m, s) => (shadowAdd bs add m, shadowAdd bs add s))

/-- The union of every slot's `matchable` set — `scrutMatch`'s "is this a tracked variable" query
does not need to know WHICH slot a variable belongs to (a match/split on it re-adds its binders to
THAT slot only, via `shadowAddAll`'s uniform broadcast — a name lives in at most one slot, so
broadcasting is safe: shadowing removes it from every slot, matchable-readd only applies where the
scrutinee's OWN name was actually tracked). -/
def matchableUnion (slots : List Slot) : List String := (slots.map Prod.fst).flatten

/-- Recognize a recursive-call SPINE rooted at `name`: unwind curried application
`($name) v1 v2 … vn` (peeling `.app`s outside-in, so the OUTERMOST `.app`'s argument is the LAST
element) or the single-tupled `($name) (v1, v2)` (ADR-0091: `pairS` is binary in the grammar, so an
n>2-ary tupled call is the user's own right-nested `(v1, (v2, v3))` — flattened here one level, deeper
nesting is out of scope: no corpus example needs more than a 2-tuple accumulator). Returns `none` if
`e` is not a call on `name` at all (so the generic `structOK` arms handle it structurally). -/
def callSpine (name : String) : Surf → Option (List Surf)
  | .app (.force (.var g)) a =>
      if g == name then
        match a with
        | .pairS a1 a2 => some [a1, a2]     -- the tupled single-slot-pair call shape
        | _            => some [a]          -- a plain single-arg call (v1 arm's shape, unchanged)
      else none
  | .app f a =>
      -- peel a curried spine: `(($name) v1 v2) v3` ⟹ recurse on `($name) v1 v2`, append `v3`.
      match callSpine name f with
      | some args => some (args ++ [a])
      | none      => none
  | _ => none

mutual
/-- **The #47/#50 structural-termination certifier — SOUND, deliberately incomplete.** `structOK
name slots targetIdx body` = `true` iff EVERY occurrence of the recursive function `name` in `body`
is a call whose FULL argument spine `v1 … vn` (curried `($name) v1 v2 … vn` OR the single tupled
`($name) (v1, v2, …, vn)`, ADR-0091 treats both identically) has `slots.length = n` and the argument
at `targetIdx` is a STRICT SUBTERM of the slot-`targetIdx` recursion parameter — a field
pattern-bound by `match`/`let (..)`-ing that parameter (or an already-established subterm of it).
Every OTHER slot's argument rides free (checked only for `name`-misuse, via the ordinary recursive
call below) — an accumulator may be any well-typed expression, not just a passthrough.

`targetIdx` is FIXED for the whole certification pass (ADR-0091 D: "the SAME slot at every call
site", not inferred per-call) — `letRecMultiOK` (below) tries each index in turn and accepts the
function iff SOME single fixed index certifies every call. Single-arg recursion is the `slots =
[one slot]`, `targetIdx = 0` special case — this generalizes #47's original checker, not replaces
it (the one-slot instantiation is definitionally identical to the pre-ADR-0091 `structOK`).

CONSERVATIVE BY CONSTRUCTION — the default is `false` (⟹ the caller keeps `Div`). Anything not
manifestly structural is rejected: a bare `name`, a `$name` not applied to subterms, a call whose
arity doesn't match `slots.length`, a call on a non-subterm at `targetIdx` (`($f) x`, `($f)(n-1)` on
`Int` — ℤ has no data-floor, ADR-0067), `name` passed as a value, or a match on a NON-parameter
value. Sound under shadowing (every binder shadows via `shadowAddAll`). Missing a terminating
function (→ `Div`) is fine; certifying a diverging one is a SOUNDNESS BUG, so we never guess.

DEFERRED (conservatively `Div`, each needs more than this syntactic check): full LEXICOGRAPHIC
descent (≥2 slots required to decrease, ranked — ADR-0091 names this (B), rejected for v1: no
corpus example needs it), well-founded numeric MEASURES (needs a `Nat`/floor type — ADR-0067's ℤ is
unbounded — ADR-0091's (C), tracked behind Q31), and subterm-aliasing through `let`. -/
-- EXPLICIT FUEL (the `expandBFns` idiom, TypeCheck.lean's established shape for a heterogeneous
-- mutual block spanning `Surf`/`List Surf`/`DArms`/`SurfArgs` — `sizeOf`-based structural inference
-- cannot find one measure across all four target types, so termination is fuel-visible instead,
-- exactly as every other cross-type mutual traversal in this file). Fuel-exhaustion returns `false`
-- (the SAME conservative default as every other unrecognized shape — under-certifies, never guesses;
-- fuel is set generously at the `letRecRow` call site so it never bites a well-formed program, only
-- caps runaway recursion for totality, per this file's own fuel convention).
def structOK (fuel : Nat) (name : String) (slots : List Slot) (targetIdx : Nat) (e : Surf) : Bool :=
  match fuel with
  | 0      => false
  | fu + 1 =>
  -- The recursive-call recognizer runs FIRST (ADR-0091): unwind a CURRIED spine `($name) v1 v2
  -- … vn` or the single-tupled `($name) (v1, …, vn)` via `callSpine`; a recognized call short-
  -- circuits the rest of the match (which handles every OTHER `Surf` shape, `.app` included — an
  -- `.app` that `callSpine` did NOT recognize as a call on `name`, e.g. `($g) x` with `g ≠ name`,
  -- falls through to the ordinary `.app` arm below unchanged from #47's original checker).
  match callSpine name e with
  | some args =>
      if args.length != slots.length then false     -- arity mismatch with the declared recursion → reject
      else structOKSpine fu name slots targetIdx 0 args
  | none => structOKRest fu name slots targetIdx e
/-- Check a recognized recursive-call SPINE's arguments against `slots`, ONE designated `targetIdx`
requiring a strict-subterm bare variable, every other position checked only for `name`-misuse
(an accumulator may be any well-typed expression). `i` is the current position (0-indexed,
threaded explicitly — no `List.enum`/`zipIdx` dependency needed). -/
def structOKSpine (fuel : Nat) (name : String) (slots : List Slot) (targetIdx : Nat) (i : Nat) :
    List Surf → Bool
  | []      => true
  | a :: as =>
      (if i == targetIdx then
        match a with | .var v => (slots.getD i ([], [])).2.contains v | _ => false
      else structOK fuel name slots targetIdx a)
      && structOKSpine fuel name slots targetIdx (i + 1) as
/-- Every `Surf` shape that is NOT a recognized recursive-call spine — #47's original per-constructor
match, unchanged except `matchable`/`subterms : List String` → `slots : List Slot` threaded
uniformly (`shadowAddAll` broadcasts a shadow across every slot; `matchableUnion` reads the union for
`scrutMatch`'s membership query, since a name lives in at most one slot). -/
def structOKRest (fuel : Nat) (name : String) (slots : List Slot) (targetIdx : Nat) : Surf → Bool
  | .lit _          => true
  | .unitS          => true
  | .getS           => true
  | .var g          => g != name                    -- a bare `name` (used as a value) is non-structural
  | .thunk e        => structOK fuel name slots targetIdx e
  | .force (.var g) => g != name                    -- `$name` NOT immediately applied to args → reject
  | .force e        => structOK fuel name slots targetIdx e
  | .app f a        => structOK fuel name slots targetIdx f && structOK fuel name slots targetIdx a
  -- Binders that RE-BIND the recursion name shadow it — `$name` there is NOT the recursion, so the
  -- structural argument tells us nothing about it. REFUSE to certify (soundness > completeness).
  | .lett v ev b    => v != name && structOK fuel name slots targetIdx ev &&
                       structOK fuel name (shadowAddAll [v] false slots) targetIdx b
  | .lam v b        => v != name &&
                       structOK fuel name (shadowAddAll [v] false slots) targetIdx b
  | .ifS c t el     => structOK fuel name slots targetIdx c && structOK fuel name slots targetIdx t
                       && structOK fuel name slots targetIdx el
  | .binopS _ a b   => structOK fuel name slots targetIdx a && structOK fuel name slots targetIdx b
  | .pairS a b      => structOK fuel name slots targetIdx a && structOK fuel name slots targetIdx b
  | .inlS e'        => structOK fuel name slots targetIdx e'
  | .inrS e'        => structOK fuel name slots targetIdx e'
  | .foldS e'       => structOK fuel name slots targetIdx e'
  | .unfoldS e'     => structOK fuel name slots targetIdx e'
  | .raise e'       => structOK fuel name slots targetIdx e'
  | .handle e'      => structOK fuel name slots targetIdx e'
  | .putS e'        => structOK fuel name slots targetIdx e'
  | .stateS a b     => structOK fuel name slots targetIdx a && structOK fuel name slots targetIdx b
  | .atomS e'       => structOK fuel name slots targetIdx e'
  | .newS e'        => structOK fuel name slots targetIdx e'
  | .readS e'       => structOK fuel name slots targetIdx e'
  | .writeS a b     => structOK fuel name slots targetIdx a && structOK fuel name slots targetIdx b
  | .annotS e' _    => structOK fuel name slots targetIdx e'
  | .divMark e'     => structOK fuel name slots targetIdx e'
  | .matchS s xl el xr er =>
      xl != name && xr != name &&
      let sm := scrutMatch (matchableUnion slots) s
      structOK fuel name slots targetIdx s &&
      structOK fuel name (shadowAddAll [xl] sm slots) targetIdx el &&
      structOK fuel name (shadowAddAll [xr] sm slots) targetIdx er
  | .splitS a b p body =>
      a != name && b != name &&
      let sm := scrutMatch (matchableUnion slots) p
      structOK fuel name slots targetIdx p &&
      structOK fuel name (shadowAddAll [a, b] sm slots) targetIdx body
  | .matchD s arms  =>
      structOK fuel name slots targetIdx s &&
      structOKArms fuel name slots targetIdx (scrutMatch (matchableUnion slots) s) arms
  | .withCapS _ init v body =>
      v != name && structOK fuel name slots targetIdx init &&
      structOK fuel name (shadowAddAll [v] false slots) targetIdx body
  | .dotPerform recv _ args =>
      structOK fuel name slots targetIdx recv && structOKArgs fuel name slots targetIdx args
  | .letRecS gname _ fb bd =>                     -- nested let rec: a re-bound `gname` shadows our name
      gname != name && structOK fuel name slots targetIdx fb && structOK fuel name slots targetIdx bd
/-- Per-arm structural check: a matchable scrutinee (`sm`) makes each arm's pattern binders strict
subterms of the parameter; a non-matchable one only shadows them. -/
def structOKArms (fuel : Nat) (name : String) (slots : List Slot) (targetIdx : Nat) (sm : Bool) :
    DArms → Bool
  | .nil => true
  | .cons _ bs b r =>
      !bs.contains name &&                            -- an arm binder shadowing the recursion name → reject
      structOK fuel name (shadowAddAll bs sm slots) targetIdx b &&
      structOKArms fuel name slots targetIdx sm r
def structOKArgs (fuel : Nat) (name : String) (slots : List Slot) (targetIdx : Nat) : SurfArgs → Bool
  | .none    => true
  | .one a   => structOK fuel name slots targetIdx a
  | .two a b => structOK fuel name slots targetIdx a && structOK fuel name slots targetIdx b
end

/-- Peel a CURRIED lambda chain (`fun x1 => fun x2 => … => fun xn => body`) into its parameter list
+ innermost body (ADR-0091 #50). `n = 1` is the pre-ADR-0091 single-arg shape, unchanged; `n > 1` is
the newly-certifiable curried-accumulator shape. Fuel-bounded (structural on `Surf`, matches every
other elaborator traversal's discipline) though `Surf` nesting from a SOURCE `let rec` is bounded by
the program text, so this always terminates in practice — the fuel is a totality formality. -/
def peelCurried : Nat → Surf → List String × Surf
  | 0,     body        => ([], body)
  | _+1,   .lam x body =>
      let (rest, inner) := peelCurried 1000000 body   -- fuel doesn't shrink meaningfully deeper than
      (x :: rest, inner)                              -- source nesting, so re-seed generously each hop
  | _+1,   body         => ([], body)

/-- Detect the TUPLE-accumulator shape (ADR-0091 #50, the design note's second corpus example):
`fun p => let (x1, x2) = p in rest`, a SINGLE parameter immediately destructured. If matched,
returns the two destructured binder names + the REST of the body past the split (so `structOK`
below runs on `rest`, never re-seeing the `splitS` node — its slots already reflect the split, and
re-processing it through the generic `.splitS` arm would harmlessly re-derive the same shadowing
but is redundant, so this consumes it once, at seed time). `none` if the single param is NOT
immediately split — that stays the pre-ADR-0091 one-slot shape (a plain single-arg `let rec`). -/
def peelTupleSplit : Surf → Option (String × String × Surf)
  | .splitS a b (.var _) rest => some (a, b, rest)
  | _                         => none

/-- Seed ONE slot per curried parameter (`[x1], [x2], …`, each starting with empty `subterms` — a
bare parameter is matchable but not yet a proven subterm of itself). -/
def seedSlots (params : List String) : List Slot := params.map (fun x => ([x], []))

/-- The effect row a `let rec` CALL-SITE carries (#46/#47/#50, ADR-0073 §2, ADR-0091). Recursion may
not terminate — the ADR-0028 total/`Div` seam, made type-visible — UNLESS the structural check
(`structOK`) proves every recursive call descends on a strict `data` subterm at ONE FIXED slot,
in which case the function is in the TOTAL fragment and carries `⊥` (no `Div`). SOUND, incomplete:
an uncertified function conservatively keeps `{divLabel}` (it still RUNS, fuel-bounded — the `Div`
escape hatch is what lets the check be aggressive without a rejection tax).

ADR-0091 lifts the v1 single-parameter-only restriction: a CURRIED `let rec f = fun x1 => … => fun
xn => body` seeds `n` slots (one per parameter, `peelCurried`) and tries EVERY `targetIdx` in
`[0, n)` in turn (`slots.length.fold`-style linear search below) — the function certifies iff SOME
single fixed index makes every recursive call's argument at that index a strict subterm, with every
OTHER call argument checked only for `name`-misuse (an accumulator, #50's motivating case). A
lexicographic requirement (≥2 slots decreasing together, ranked) is explicitly OUT of this search —
ADR-0091 (B), rejected — so trying each index independently, not jointly, is the intended search
space, not an approximation of a richer one. Measures / lexicographic remain deferred (see
`structOK`'s doc comment) — those stay `Div`.

Placement note (#46, unchanged): `Div` is seeded on the OUTER knot only (`buildLetRec`); the inner
self-calls are typed pure `⊥` (Option A) — operationally sound since `Div` has no runtime semantics. -/
def letRecRow (name : String) (funBody : Surf) : EffRow :=
  match funBody with
  | .lam _ _ =>
      let (params, curriedBody) := peelCurried 1000000 funBody
      -- The TUPLE shape only applies to a lone parameter (`fun p => let (a,b) = p in …`) — a
      -- curried multi-param `let rec` whose LAST param happens to be split is the curried shape
      -- with an ordinary internal `splitS`, handled generically by `structOK`'s existing arm; only
      -- `params.length == 1` is ambiguous between "a plain single struct-arg fn" and "a tupled
      -- pair-accumulator fn", so only there does `peelTupleSplit` get a look.
      let (slots, body) := match params, peelTupleSplit curriedBody with
        | [_], some (a, b, rest) => (seedSlots [a, b], rest)
        | _,   _                 => (seedSlots params, curriedBody)
      -- linear search over target slots (ADR-0091 D: fixed index per pass, tried independently —
      -- NOT jointly, that would be lexicographic descent, explicitly deferred). First hit wins; a
      -- multi-slot-certifiable function is certified via its LOWEST such index (any would do —
      -- soundness doesn't depend on which one, only that SOME fixed one works end to end). Fuel
      -- generous per this file's convention (a token-count-proportional bound would need threading
      -- the source size here; a flat large constant never bites a well-formed `let rec` body, only
      -- caps runaway recursion for totality — the SAME role `parseE`'s `toks.length * 6 + 1` plays,
      -- sized up since this walks a already-small elaborated AST, not raw tokens).
      if (List.range slots.length).any (fun i => structOK 1000000 name slots i body) then ∅ else {divLabel}
  | _ => {divLabel}                                              -- not a `fun` literal → Div (conservative)

/-- The μ-encoded fixpoint for `let rec f : T = <funBody'> in <bodyExpr'>` (ADR-0073; Landin's knot,
NO new kernel primitive). `funBody'`/`bodyExpr'` are ALREADY elaborated (with `f : Thunk T` in scope).
`Rec = μX. Thunk(X -> T)`; the self-knot `{ let #g = unfold sv in ($#g) sv } : Thunk T` reconstructs
`f` from a self-value (`unfold` returns a RETURNER of the thunk, so it is let-bound before forcing —
the #45 spike's shape). The OUTER knot (the user's call-site binding) is `divMark`-wrapped when
`recRow` is nonempty (see `letRecRow`) → `f : Thunk ! {Div} T`, so `($f) x : … ! {Div}` (Div rides the
`U`/judgment per ADR-0019/0020, NOT the arrow). The INNER knot stays pure so `recTy`'s `tThunk` (⊥)
annotation holds. Emits only ordinary `Surf` the existing checker + kernel handle. -/
def buildLetRec (name : String) (t' : Ty) (funBody' bodyExpr' : Surf) (recRow : EffRow) : Surf :=
  let recTy : Ty := .tMu (.tThunk (.tArr (.tVar 0) t'))     -- μX. Thunk(X -> T)
  let knotBody : String → Surf := fun sv =>
    .lett "#g" (.unfoldS (.var sv)) (.app (.force (.var "#g")) (.var sv))
  let inner : Surf := .annotS (.lam "#self" (.lett name (.thunk (knotBody "#self")) funBody')) (.tArr recTy t')
  let recVal : Surf := .annotS (.foldS (.thunk inner)) recTy
  let outerKnot : Surf :=                                     -- Div rides the outer (call-site) thunk
    if divLabel ∈ recRow then .thunk (.divMark (knotBody "#rec")) else .thunk (knotBody "#rec")
  .lett "#rec" recVal (.lett name outerKnot bodyExpr')

/-- Bind a match arm's payload binders over the payload variable (arity ≤ 2). -/
def bindPayload : List String → String → Surf → Surf
  | [],       _, body => body
  | [b],      v, body => .lett b (.var v) body
  | [b1, b2], v, body => .splitS b1 b2 (.var v) body
  | _,        _, body => body   -- arity ≤ 2 enforced at env build

/-- Assemble the ordered (already-elaborated) match arms into the `matchS` chain over the
unfolded scrutinee — the last ctor's payload is the bare right-nested-sum tail. -/
def buildMatch : List (List String × Surf) → String → Surf
  | [],              v => .var v   -- unreachable (≥ 1 ctor)
  | [(bs, body)],    v => bindPayload bs v body
  | (bs, body) :: r, v => .matchS (.var v) "#l" (bindPayload bs "#l" body) "#r" (buildMatch r "#r")

/-- `DArms` back to the parser's list shape (for the elaborator's arm bookkeeping). -/
def armsToList : DArms → List (String × List String × Surf)
  | .nil            => []
  | .cons c bs b r  => (c, bs, b) :: armsToList r

/-- Navigate to ctor position `i` of `n` in a right-nested-sum payload (`n = 1` ⇒ the whole thing is
the single ctor's payload) — the eliminator dual of `injSum` (ADR-0069 bite-1, generic match). -/
def navSum : Nat → Nat → VT → Option VT
  | _,     1, p            => some p
  | 0,     _, .sum p _     => some p
  | i + 1, n, .sum _ rest  => navSum i (n - 1) rest
  | _,     _, _            => none

/-- Split a k-ary right-nested product payload into its field types (`splitProd`'s dual of `prodOfTys`;
`arity 0` ⇒ `[]` for a `Unit` payload). -/
def splitProd : Nat → VT → List VT
  | 0,     _              => []
  | 1,     p              => [p]
  | k + 1, .prod a rest   => a :: splitProd k rest
  | _,     p              => [p]

/-- GENERIC-match binder types (ADR-0069 bite-1): from the CONCRETE scrutinee μ (`τ = μX. Unit +
(Int × X)`), unroll + navigate each ctor's payload to its field types — so `Cons(h, t)` on a `List Int`
binds `h : Int`, `t : List Int`. The kernel's own `VTy.unrollMu` does the substitution; the checker
would derive the same types at typing, but the ELABORATOR needs them so `anfSplit` inside an arm can
synthesize a computation (`($length) t`). Returns a per-ctor-NAME table. Empty if `τ` isn't a μ. -/
def genBinderTable (ctors : List (String × CtorInfo)) (dataName : String) (τ : VT) :
    List (String × List IVTy) :=
  match τ with
  | .mu body =>
      let unrolled := VTy.unrollMu body
      (ctors.filter (fun p => p.2.dataName == dataName)).filterMap (fun (cn, ci) =>
        match navSum ci.idx ci.total unrolled with
        | some pay => some (cn, (splitProd ci.arity pay).map embV)
        | none     => none)
  | _ => []


/-- A-normalize a VALUE-position subterm (#41), mirroring `lowerV`-or-`letC` in `Surface.lower` but
at the NAMED elaboration layer (no de-Bruijn shift — a fresh binder just extends `Γ`). Returns the
extended context, a `let`-prefix to wrap around the enclosing construct, and the value-`Surf` to use
in the value slot: a syntactic value passes through (`id` prefix); a computation is bound under a
fresh `#anf`-name (its returner payload type in `Γ`), lifting it ABOVE the construct (so e.g. a
ctor's fold still wraps a VALUE). A non-returner is left for the checker; an untypeable RHS surfaces
its REAL error, not a downstream "unbound variable" (the #41 diagnostic). Fresh names key on `Γ.length`
and shadow innermost-first (as `lower`'s own sentinels do), so nested/sibling binds stay correct. -/
def anfSplit (Γ : NCtx) (e' : Surf) : Except String (NCtx × (Surf → Surf) × Surf) :=
  if isValueSurf e' then .ok (Γ, id, e')
  else match zonkInferC (synthSC Γ e') with
    | .ok (.F _ A, _)   => let nm := s!"#anf{Γ.length}"; .ok ((nm, A) :: Γ, (Surf.lett nm e' ·), .var nm)
    -- bite-0b (arm c): a higher-order returner-to-be — `($g) x` whose type is still a bare `chole` — is
    -- LIFTED exactly like an `F`-returner (bind `#anf`, `let`-hoist it), so `($f)(($g) x)` can A-normalize
    -- its computation argument. `#anf`'s placeholder type is irrelevant here (never inspected downstream in
    -- elaboration); the FINAL check re-infers it via `expectF` (unifying the chole to `F ω ?`). This is why
    -- the chole-TOLERANT `zonkInferC` (not the extracting `runInferC`) probes the returner shape.
    | .ok (.chole _, _) => let nm := s!"#anf{Γ.length}"
                           .ok ((nm, (paramHole Γ.length : IVTy)) :: Γ, (Surf.lett nm e' ·), .var nm)
    | .ok _             => .ok (Γ, id, e')
    | .error m          => .error m

/-- Type a `let`-RHS for the ELABORATOR's binding decision, as a CLOSED scheme. Runs its own throwaway
inference (`.run' {}`), defaults any dangling `chole` to `F ω ?`, then abstracts ALL free value holes to
rigids. Closing is LOAD-BEARING: an elaboration binding that embedded a throwaway's raw hole ids would
COLLIDE with a later throwaway's fresh holes (whose counter restarts at 0) — spuriously unifying two
independent polymorphic uses (bare `compose` at two types). A closed scheme instantiates fresh holes per
use, exactly like the final check. `none` = the RHS is not a returner (and not a higher-order `chole`). -/
def elabBind (Γ : NCtx) (e' : Surf) : Except String (Option Scheme) :=
  (do
    let (Ce, _) ← synthSC Γ e'
    let payload? ← (match (← resolveC bigFuel Ce) with
      | .F _ A   => pure (some A)
      | .chole n => do let A ← freshHole; assignC n (.F .omega A); pure (some A)
      | _        => pure none)
    match payload? with
    | none   => return none
    | some A => do
        let A0 ← zonkV bigFuel A
        for c in (freeCholesV A0).eraseDups do let h ← freshHole; assignC c (.F .omega h)
        let Az ← zonkV bigFuel A
        let ms := (freeHolesV Az).eraseDups
        let rs := (freeRowsV Az).eraseDups   -- bite-0b item 3: close ROW vars too (else two uses of a
                                             -- row-poly binding share a tail var + spuriously clash)
        return some (⟨ms.length, rs.length, abstractRowsV rs (abstractV ms Az)⟩ : Scheme)
  ).run' {}

/-- Peel matching `fun`/`->` layers of an ASCRIBED curried lambda, binding EVERY parameter to its
annotated domain — not just the outermost. So a nested `fun g => …` inside `(fun f => fun g => … :
A -> B -> C)` also sees `g : B`; `elabS`'s `.lam` arm threads this extended `Γ` unchanged into the
nested bodies, so `anfSplit` inside a curried fun can synthesize a computation ARGUMENT's type
(`($g) x`) instead of failing on an unbound param. -/
def curryBind : NCtx → Surf → Ty → NCtx
  | Γ, e,        .tEff _ t   => curryBind Γ e t
  | Γ, .lam x b, .tArr aT bT => curryBind ((x, (embV (vtyOf aT) : IVTy)) :: Γ) b bT
  | Γ, _,        _           => Γ
  termination_by _ _ t => sizeOf t

/-- Build the RAW monomorphic wrapper for one bounded-fn use `(fold arg : T)` (bite-2, ADR-0080). The
result annotation `t` fixes the carrier (v1 requires the declared result type to BE the bound var — the
fold shape `… -> a`); we resolve the `Trait T` instance and emit: the instance's ops in a prologue
(0-ary `empty` ⟹ a value binding; n-ary `combine` ⟹ an annotated function thunk) around a concrete
`let rec name : declaredTy[tyVar := T] = fun … = body in (\$name) arg`. This is PURE `Surf` (no
elaboration) — `elabS` later resolves the spliced trait ops AT the concrete `T` (exactly as `buildEnv`'s
impl pre-elaboration) and desugars the `let rec` (ADR-0073), all on structural subterms so it stays
TOTAL. A MISSING `Trait T` instance ⟹ a loud error (the bound is unsatisfied). -/
def bfnWrapper (env : ElabEnv) (bfn : BoundedFn) (t : Ty) (arg : Surf) : Except String Surf := do
  let resTy := stripArrows bfn.params.length bfn.declaredTy
  if resTy != Ty.tName bfn.tyVar then
    throw s!"bounded fn '{bfn.traitName} {bfn.tyVar}': v1 fixes the carrier from the RESULT annotation, so the declared result type must be '{bfn.tyVar}' (the fold shape); got a different result type"
  let Tv := vtyOf (← resolveTy env.gen env.aliases t)         -- the annotation IS the carrier T
  let some rimpl := env.rawImpls.find? (fun r => r.traitName == bfn.traitName && r.targetVT == Tv)
    | throw s!"no impl of '{bfn.traitName}' for {showVTy Tv} — the bound '{bfn.traitName} {bfn.tyVar}' is unsatisfied"
  let recTy   := substTyVar bfn.tyVar t bfn.declaredTy        -- `List a -> a` ↦ `List T -> T`
  let recCore := Surf.letRecS bfn.name recTy (funFromParams bfn.params bfn.body)
                   (.app (.force (.var bfn.name)) arg)         -- `let rec fold : … = … in ($fold) arg`
  return rimpl.ops.foldr (fun op acc =>
      if op.params.isEmpty then                                -- 0-ary op (`empty`) ⟹ a value binding
        Surf.lett op.name (.annotS op.body t) acc
      else                                                     -- n-ary op (`combine`) ⟹ an annotated fn thunk
        let fnTy := mkArrs op.params.length t (substSelf t op.retTy)
        Surf.lett op.name (.thunk (.annotS (funFromParams op.params op.body) fnTy)) acc)
    recCore

/-- Build the monomorphic wrapper for one HIGHER-KINDED bounded-fn use (ADR-0082 Case B, abstract-over-f):
`(twice inc (Some 5) : Option Int)` where `twice(g, x) : (a -> a) -> f a -> f a where Functor f`. This is
`bfnWrapper` re-keyed on a carrier CONSTRUCTOR instead of a carrier VT — the difference the whole Case-B
seam turns on. The result annotation pins the abstract `f` to a concrete constructor (`f := Option`, by
`hktCtorHead` = the injectivity head-solution); the remaining ordinary tyvars are read off by matching the
result pattern (`f a`) against the annotation (`Option Int` ⟹ `a := Int`, `hktMatch`). We substitute BOTH
into the declared type — `substCarrierHead` (the HK head `f ↦ Option`) then `substTyVar` (each `a ↦ Int`)
— giving a fully concrete `recTy`, and SPLICE the resolved `Functor Option` impl's ops as unannotated
local thunks (their types inferred from the concrete `recTy` at each use, exactly as the Stage-C Case-A
method splice). The abstract carrier NEVER reaches the kernel as a residual HK application: it is
monomorphized to `mu` here, per concrete use, because bang is whole-program (ADR-0082 §5). Missing impl ⟹ loud (the bound is unmet). -/
def hktBfnWrapper (env : ElabEnv) (bfn : BoundedFn) (t : Ty) (args : List Surf) : Except String Surf := do
  let some ctor := hktCtorHead t
    | throw s!"bounded fn '{bfn.name}' ({bfn.traitName} {bfn.tyVar}): cannot determine the carrier constructor from the result annotation — annotate the use with `C …`"
  let some impl := env.hktImpls.find? (fun i => i.traitName == bfn.traitName && i.ctorName == ctor)
    | throw s!"no impl of '{bfn.traitName}' for '{ctor}' — the bound '{bfn.traitName} {bfn.tyVar}' is unsatisfied"
  let resPat := stripArrows bfn.params.length bfn.declaredTy
  let recTy  := (hktMatch resPat t).foldl (fun ty (v, cty) => substTyVar v cty ty)
                  (substCarrierHead bfn.tyVar ctor bfn.declaredTy)
  let recCore := Surf.letRecS bfn.name recTy (funFromParams bfn.params bfn.body)
                   (args.foldl (fun acc a => Surf.app acc a) (.force (.var bfn.name)))
  return impl.ops.foldr (fun od acc =>
      Surf.lett od.name (.thunk (funFromParams od.params od.body)) acc) recCore

mutual
/-- Bounded-fn EXPANSION pre-pass (bite-2, ADR-0080): a PURE `Surf → Surf` rewrite that replaces every
bounded-fn use `(fold arg : T)` with its monomorphic wrapper (`bfnWrapper`) BEFORE type-directed
elaboration. Running it first means `elabS` only ever elaborates structural subterms of its input (the
wrappers are part of that input) — so `elabS` stays TOTAL (no env-pull during elab, no `partial`).
Fuel-bounded (idiomatic here — `resolveTyG`/`monoData`/the parser all bound their descent this way);
`bigFuel` from `elabProg` dwarfs any real AST depth. Every node maps structurally (ENUMERATED — a new
`Surf` former fails here until handled), recursing into children; an expanded use's arg is expanded first.

`carrier?` is the ENCLOSING monadic carrier hint (ADR-0082 Stage D): inside `bind M { fun x => … }` at
`Monad Option`, the continuation is expanded with `carrier? = some "Option"`, so a BARE (un-annotated)
`pure e` / `bind …` in it fixes its carrier from the hint rather than a per-call `: Option _` annotation
(the ergonomics payoff). Propagated uniformly to children; only a bare HK-method spine CONSUMES it (a
data ctor / ordinary app ignores it). An explicit annotation still wins — the `annotS` arm sets the
carrier from the annotation. Un-fixable (`carrier? = none`, no annotation) ⟹ the use is left for the
checker, which fails loud (decidability descent, never a guess). -/
def expandBFns (env : ElabEnv) (carrier? : Option String) : Nat → Surf → Except String Surf
  | 0,     _ => .error "bounded-fn expansion out of fuel"
  | _ + 1, .lit n     => .ok (.lit n)
  | _ + 1, .var x     => .ok (.var x)
  | _ + 1, .unitS     => .ok .unitS
  | _ + 1, .getS      => .ok .getS
  | f + 1, .thunk e   => do return .thunk (← expandBFns env carrier? f e)
  | f + 1, .force e   => do return .force (← expandBFns env carrier? f e)
  | f + 1, .raise e   => do return .raise (← expandBFns env carrier? f e)
  | f + 1, .handle e  => do return .handle (← expandBFns env carrier? f e)
  | f + 1, .putS e    => do return .putS (← expandBFns env carrier? f e)
  | f + 1, .atomS e   => do return .atomS (← expandBFns env carrier? f e)
  | f + 1, .newS e    => do return .newS (← expandBFns env carrier? f e)
  | f + 1, .readS e   => do return .readS (← expandBFns env carrier? f e)
  | f + 1, .inlS e    => do return .inlS (← expandBFns env carrier? f e)
  | f + 1, .inrS e    => do return .inrS (← expandBFns env carrier? f e)
  | f + 1, .foldS e   => do return .foldS (← expandBFns env carrier? f e)
  | f + 1, .unfoldS e => do return .unfoldS (← expandBFns env carrier? f e)
  | f + 1, .divMark e => do return .divMark (← expandBFns env carrier? f e)
  | f + 1, .lam x b   => do return .lam x (← expandBFns env carrier? f b)
  | f + 1, .lett x e b   => do return .lett x (← expandBFns env carrier? f e) (← expandBFns env carrier? f b)
  | f + 1, .app g a      => do
      -- HKT Stage D (ADR-0082): a BARE HK-method spine `bind M K` / `pure e` under an enclosing carrier
      -- hint splices at that carrier WITHOUT a per-call annotation (the ergonomics payoff). Anything else
      -- (partial spine, non-HK head, no carrier) recurses structurally.
      match carrier?, appSpine (.app g a) with
      | some ctor, some (op, args) =>
          match env.hktMethodOf.lookup op with
          | some tn =>
              match env.hktImpls.find? (fun i => i.traitName == tn && i.ctorName == ctor) with
              | some impl =>
                  match impl.ops.find? (fun od => od.name == op) with
                  | some od =>
                      if args.length == od.params.length then hktMethodSplice env carrier? f op ctor od args none
                      else do return .app (← expandBFns env carrier? f g) (← expandBFns env carrier? f a)
                  | none => do return .app (← expandBFns env carrier? f g) (← expandBFns env carrier? f a)
              | none => throw s!"no impl of '{tn}' for '{ctor}' — the higher-kinded method '{op}' is unresolved"
          | none => do return .app (← expandBFns env carrier? f g) (← expandBFns env carrier? f a)
      | _, _ => do return .app (← expandBFns env carrier? f g) (← expandBFns env carrier? f a)
  | f + 1, .stateS a b   => do return .stateS (← expandBFns env carrier? f a) (← expandBFns env carrier? f b)
  | f + 1, .writeS a b   => do return .writeS (← expandBFns env carrier? f a) (← expandBFns env carrier? f b)
  | f + 1, .pairS a b    => do return .pairS (← expandBFns env carrier? f a) (← expandBFns env carrier? f b)
  | f + 1, .binopS op a b => do return .binopS op (← expandBFns env carrier? f a) (← expandBFns env carrier? f b)
  | f + 1, .ifS c t e    => do return .ifS (← expandBFns env carrier? f c) (← expandBFns env carrier? f t) (← expandBFns env carrier? f e)
  | f + 1, .splitS a b p body => do return .splitS a b (← expandBFns env carrier? f p) (← expandBFns env carrier? f body)
  | f + 1, .matchS s xl el xr er => do
      return .matchS (← expandBFns env carrier? f s) xl (← expandBFns env carrier? f el) xr (← expandBFns env carrier? f er)
  | f + 1, .withCapS k init n body => do return .withCapS k (← expandBFns env carrier? f init) n (← expandBFns env carrier? f body)
  | f + 1, .letRecS n t fn b => do return .letRecS n t (← expandBFns env carrier? f fn) (← expandBFns env carrier? f b)
  | f + 1, .dotPerform recv op args => do return .dotPerform (← expandBFns env carrier? f recv) op (← expandArgs env carrier? f args)
  | f + 1, .matchD s arms => do return .matchD (← expandBFns env carrier? f s) (← expandArms env carrier? f arms)
  | f + 1, .annotS e t => do
      -- HKT (ADR-0082): a higher-kinded METHOD call `(fmap inc x : Option Int)` — the result annotation
      -- fixes the carrier constructor (`f := Option`), so we resolve the `Functor Option` impl and SPLICE
      -- its `fmap` body as a monomorphic local (the bite-2 `bfnWrapper` move keyed on a ctor NAME). The
      -- spliced body then type-checks + runs with the ordinary generic-data machinery — kernel untouched.
      match appSpine e with
      | some (op, args) =>
          match env.hktMethodOf.lookup op with
          | some tn =>
              match hktCtorHead t with
              | none => throw s!"'{op}': cannot determine the carrier constructor from the result annotation — annotate the use with `C …`"
              | some ctor =>
                  match env.hktImpls.find? (fun i => i.traitName == tn && i.ctorName == ctor) with
                  | none => throw s!"no impl of '{tn}' for '{ctor}' — the higher-kinded method '{op}' is unresolved"
                  | some impl =>
                      match impl.ops.find? (fun od => od.name == op) with
                      | none => throw s!"impl of '{tn}' for '{ctor}' does not define '{op}'"
                      | some od =>
                          if args.length != od.params.length then
                            throw s!"'{op}' at '{ctor}': applied to {args.length} args, the impl takes {od.params.length}"
                          hktMethodSplice env carrier? f op ctor od args (some t)
          | none =>
              match env.bfns.lookup op with
              | some bfn =>                                       -- a bounded-fn use `(fold arg : T)` (bite-2/HKT)
                  let args' ← expandList env carrier? f args
                  match env.hktTraits.lookup bfn.traitName with
                  | some _ => hktBfnWrapper env bfn t args'       -- HK bound (`where Functor f`): Case B
                  | none   => match args' with                   -- ordinary bound (`where Monoid a`): bite-2 (single arg)
                              | [arg] => bfnWrapper env bfn t arg
                              | _     => do return .annotS (← expandBFns env carrier? f e) t
              | none => do return .annotS (← expandBFns env carrier? f e) t
      | none => do return .annotS (← expandBFns env carrier? f e) t

/-- Splice one resolved HK-method use to a monomorphic local (ADR-0082): `let op = { fun params => body }
in (call : t?)`. The impl's `body` is concrete (expanded carrier-free); the ARGS are expanded under
`some ctor` so nested un-annotated `pure`/`bind` in a continuation resolve at THIS carrier (Stage D
threading). `ann? = some t` keeps the result annotation (Case A / annotated use); `none` relies on the
annotation-free ctor intro (`Some x`) to infer the element type at the concrete carrier (bare use).
(`_carrier?` is inert — the resolved `ctor` IS the carrier here; the param stays only to align the
mutual block's argument positions for termination inference.) -/
def hktMethodSplice (env : ElabEnv) (_carrier? : Option String) (f : Nat)
    (op ctor : String) (od : Bang.Surface.OpDef) (args : List Surf) (ann? : Option Ty) :
    Except String Surf := do
  let body' ← expandBFns env none f od.body
  let args' ← expandList env (some ctor) f args
  let call := args'.foldl (fun acc a => Surf.app acc a) (Surf.force (Surf.var op))
  return Surf.lett op (.thunk (funFromParams od.params body'))
    (match ann? with | some t => .annotS call t | none => call)

/-- `SurfArgs` expansion (cap-op arguments). -/
def expandArgs (env : ElabEnv) (carrier? : Option String) : Nat → SurfArgs → Except String SurfArgs
  | 0,     _        => .error "bounded-fn expansion out of fuel"
  | _ + 1, .none    => .ok .none
  | f + 1, .one a   => do return .one (← expandBFns env carrier? f a)
  | f + 1, .two a b => do return .two (← expandBFns env carrier? f a) (← expandBFns env carrier? f b)

/-- Expand a list of `Surf` (HK method args), explicit recursion so termination stays fuel-visible. -/
def expandList (env : ElabEnv) (carrier? : Option String) : Nat → List Surf → Except String (List Surf)
  | 0,     _         => .error "bounded-fn expansion out of fuel"
  | _ + 1, []        => .ok []
  | f + 1, a :: rest => do return (← expandBFns env carrier? f a) :: (← expandList env carrier? f rest)

/-- `DArms` expansion (named-match arm bodies). -/
def expandArms (env : ElabEnv) (carrier? : Option String) : Nat → DArms → Except String DArms
  | 0,     _             => .error "bounded-fn expansion out of fuel"
  | _ + 1, .nil          => .ok .nil
  | f + 1, .cons c bs b r => do return .cons c bs (← expandBFns env carrier? f b) (← expandArms env carrier? f r)
end

/-! Type-directed elaboration over `Surf`: resolves `binopS` on non-Int operands through the
instance env, ctor intros + named matches through the data env (ADR-0069); every other
constructor maps structurally (ENUMERATED — a new `Surf` form fails here until elaborated, the
same completeness-by-construction as `synthSC`/`lowerC`). Binder arms extend `Γ` so operand
types inside them synthesize — `lett` via `synthSC` on the elaborated head, `match`/`split` via
the scrutinee's type; a BARE lam body is elaborated with its param unbound (resolution inside
one needs an ascription, exactly like checking). -/
mutual
/-- The elaborator (see the section comment). Mutual with `elabArms` (named-match arm bodies). -/
def elabS (env : ElabEnv) : NCtx → Surf → Except String Surf
  | _, .lit n => .ok (.lit n)
  | _, .var x =>
      match env.ctors.lookup x with           -- a 0-ary ctor use (`Nil`) IS an intro (ADR-0069)
      | some ci => if ci.arity == 0 then
                     -- GENERIC (bite-1/#55): the ctor's TEMPLATE μ (params as markers) — `embVInst` mints
                     -- fresh holes at the annotation, so the element type is INFERRED from context (an
                     -- enclosing concrete annotation OR the fields), no user `: Option Int` required.
                     -- Monomorphic: the concrete `ci.dataTy` annotation, exactly as ADR-0069.
                     if ci.params.isEmpty then .ok (ctorIntro ci .unitS)
                     else genCtorIntro env ci .unitS
                   else .error s!"constructor '{x}' expects {ci.arity} argument(s)"
      | none    => .ok (.var x)
  | _, .getS  => .ok .getS
  | _, .unitS => .ok .unitS
  | Γ, .thunk b  => do return .thunk (← elabS env Γ b)
  | Γ, .force b  => do return .force (← elabS env Γ b)
  -- A-normalize a computation ARGUMENT (#26 part-2), as `.pairS` does: an effect op's arg is
  -- VALUE-position (`checkSV … .int`), so `put (get + 1)` ⟹ `let #anf = get + 1 in put #anf`. A bare
  -- value arg passes through unchanged (`anfSplit`'s `id` prefix), matching `Surface.lower`.
  | Γ, .raise e  => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e'; return w (.raise v)
  | Γ, .handle e => do return .handle (← elabS env Γ e)
  | Γ, .putS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e'; return w (.putS v)
  | Γ, .atomS e  => do return .atomS (← elabS env Γ e)
  | Γ, .newS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e'; return w (.newS v)
  | Γ, .readS e  => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e'; return w (.readS v)
  -- A-normalize a computation payload (#41), as `.pairS` does: `Left(($g) e)` ⟹ `let #anf = ($g) e in
  -- Left(#anf)`, so the sum injection gets a VALUE payload (a bare `Left(value)` is unchanged).
  | Γ, .inlS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e'; return w (.inlS v)
  | Γ, .inrS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e'; return w (.inrS v)
  -- state's INITIAL value is value-position (`checkSV e0 .int`) too — A-normalize it like the ops.
  | Γ, .stateS e0 e => do
      let e0' ← elabS env Γ e0
      let (Γ1, w, v0) ← anfSplit Γ e0'
      return w (.stateS v0 (← elabS env Γ1 e))
  | Γ, .writeS r w  => do
      let r' ← elabS env Γ r
      let w' ← elabS env Γ w
      let (Γ1, wr, rv) ← anfSplit Γ r'
      let (_,  ww, wv) ← anfSplit Γ1 w'
      return wr (ww (.writeS rv wv))
  | Γ, .pairS a b   => do                     -- A-normalize computation components (bare pair in comp position), #41
      let a' ← elabS env Γ a
      let b' ← elabS env Γ b
      let (Γ1, wa, va) ← anfSplit Γ a'
      let (_,  wb, vb) ← anfSplit Γ1 b'
      return wa (wb (.pairS va vb))
  | Γ, .foldS b     => do return .foldS (← elabS env Γ b)
  | Γ, .unfoldS b   => do return .unfoldS (← elabS env Γ b)
  | Γ, .withCapS kind init name body => do   -- bind name : Cap ℓ so body operands synthesize (ADR-0070)
      let init' ← elabS env Γ init
      let Γ' := match capKindLabel kind with
        | some ℓ => (name, (.cap ℓ : IVTy)) :: Γ
        | none   => Γ
      return .withCapS kind init' name (← elabS env Γ' body)
  | Γ, .dotPerform recv op args => do
      let recv' ← elabS env Γ recv
      let args' ← (match args with
        | .none    => (pure .none : Except String SurfArgs)
        | .one a   => do return .one (← elabS env Γ a)
        | .two a b => do return .two (← elabS env Γ a) (← elabS env Γ b))
      return .dotPerform recv' op args'
  | Γ, .app (.var c) a => do                  -- ctor intro `Cons(e, …)` parses as application (ADR-0069)
      match env.ctors.lookup c with
      | some ci =>
          if ci.arity == 0 then .error s!"constructor '{c}' takes no arguments"
          else do
            -- A-normalize the payload so the fold wraps a VALUE (computations lifted above, #41). A
            -- multi-field payload is a `pairS` whose own arm already lifts its fields into a returner;
            -- this bind then lifts that returner above the fold. Inner/outer `#anf` names may coincide
            -- at equal depth but shadow innermost-first (as `lower`'s sentinels do), so it stays correct.
            let a' ← elabS env Γ a
            let (_, w, v) ← anfSplit Γ a'
            -- GENERIC (bite-1/#55): the TEMPLATE μ (params as markers) — `embVInst` mints fresh holes, so
            -- the element type is INFERRED from the fields (`Cons(1, Nil)` ⟹ `a := Int`, no annotation).
            if ci.params.isEmpty then return w (ctorIntro ci v)
            else return w (← genCtorIntro env ci v)
      | none    => do return .app (.var c) (← elabS env Γ a)
  | Γ, .app f a     => do                     -- A-normalize a computation ARGUMENT (`($f)(n-1)`), #41
      let f' ← elabS env Γ f
      let a' ← elabS env Γ a
      let (_, wrap, av) ← anfSplit Γ a'
      return wrap (.app f' av)
  | Γ, .ifS c t e   => do                     -- A-normalize a computation condition (`n == 0`), #41
      let c' ← elabS env Γ c
      let (Γ1, wrap, cv) ← anfSplit Γ c'
      return wrap (.ifS cv (← elabS env Γ1 t) (← elabS env Γ1 e))
  | Γ, .lam x b     => do
      -- BARE (un-annotated) `fun x => …`: bind the param to a fresh HOLE so `anfSplit` inside the body
      -- can synthesize a computation ARGUMENT's type (`($g) x`) instead of failing on an unbound param
      -- (the HM-inferred higher-order path). An ALREADY-bound `x` (the annotated `curryBind` path) keeps
      -- its concrete type — the hole is only for the bare case.
      let Γ' := if (Γ.lookup x).isSome then Γ else (x, ({ body := paramHole Γ.length } : Scheme)) :: Γ
      return .lam x (← elabS env Γ' b)
  -- `let rec f : T = <fun> in <body>` → the μ-encoded fixpoint (Landin's knot, ADR-0073; NO new
  -- kernel primitive — invariant #5). `Rec = μX. Thunk(X -> T)`; the self-knot `{ let #g = unfold sv
  -- in ($#g) sv } : Thunk T` reconstructs `f` from a self-value, so `f : Thunk T` is in scope in its
  -- OWN body (and the outer body) — call it as `($f) arg`. `unfold` is a RETURNER of the thunk, so it
  -- is let-bound before forcing (the #45 spike's shape, generalized per-function; monomorphic + the
  -- `: T` annotation drives check-mode on the recursive `fun`). The whole thing type-checks + lowers
  -- through the EXISTING checker/kernel — the desugar emits only ordinary `Surf`.
  | Γ, .letRecS name t (.lam pn pbody) bodyExpr => do
      let t' ← resolveTy env.gen env.aliases t
      let uT : IVTy := .U botR (embC (ctyOf t'))               -- f : Thunk T
      let dom : IVTy := match tyBoth t' with                   -- the fun's param type (domain of T)
        | (_, .arr _ A _) => embV A
        | _               => .tvar 997                          -- POISON: T not a function → fails loud below
      -- f in scope in its OWN body, param bound (the `: T` annotation drives the check); annotate the
      -- user `fun` with `T` (its param already elaborated under `dom`, so re-check-mode is a no-op).
      let pbody' ← elabS env ((pn, dom) :: (name, uT) :: Γ) pbody
      let bodyExpr' ← elabS env ((name, uT) :: Γ) bodyExpr
      return buildLetRec name t' (.annotS (.lam pn pbody') t') bodyExpr' (letRecRow name (.lam pn pbody))
  | _, .letRecS _ _ _ _ =>
      .error "let rec requires a function literal: `let rec f : T = fun x => … in …` (ADR-0073)"
  | _, .divMark _ =>
      .error "divMark is internal (#46 let rec Div-marker) — it is EMITTED by the elaborator, never received"
  | Γ, .lett x e b  => do
      let e' ← elabS env Γ e
      match elabBind Γ e' with                 -- report the RHS's REAL error, not a downstream unbound (#41)
      | .ok (some sch) => return .lett x e' (← elabS env ((x, sch) :: Γ) b)
      | .ok none       => throw s!"let-binding '{x}': value is not a returner — force it (${x}) or bind a value"
      | .error m       => throw s!"let-binding '{x}': {m}"
  | Γ, .matchS s xl el xr er => do
      let s' ← elabS env Γ s
      let (Γ1, wrap, sv) ← anfSplit Γ s'       -- A-normalize a computation scrutinee, #41
      let (Γl, Γr) := match runInferV (synthSV Γ1 sv) with
        | .ok (.sum A B) => ((xl, embV A) :: Γ1, (xr, embV B) :: Γ1)
        -- the scrutinee's sum structure isn't known yet (a bare-sum eliminator over an unannotated
        -- param — `bimap`/`eitherToResult` in the generic prelude). Bind each binder to a placeholder
        -- hole so the body elaborates; the CHECKER's `matchS` invents the sum (`.vhole ⟹ sum`) and
        -- unifies — the exact `.splitS` #55 move for products.
        | _              => ((xl, (paramHole Γ1.length : IVTy)) :: Γ1, (xr, (paramHole (Γ1.length + 1) : IVTy)) :: Γ1)
      return wrap (.matchS sv xl (← elabS env Γl el) xr (← elabS env Γr er))
  | Γ, .splitS a b p body => do
      let p0 ← elabS env Γ p
      let (Γ1, wrap, p') ← anfSplit Γ p0       -- A-normalize a computation scrutinee, #41
      let Γ' := match runInferV (synthSV Γ1 p') with
        | .ok (.prod A B) => (b, embV B) :: (a, embV A) :: Γ1
        -- #55: the scrutinee's product structure isn't known yet (a generic Option's element `a` bound to
        -- `(v * rest)`, still an opaque marker at elaboration). Bind the fields to placeholder holes so the
        -- body elaborates; the CHECKER's `splitS` invents the product (`.vhole ⟹ prod`) and unifies.
        | _               => (b, (paramHole (Γ1.length + 1) : IVTy)) :: (a, (paramHole Γ1.length : IVTy)) :: Γ1
      return wrap (.splitS a b p' (← elabS env Γ' body))
  | Γ, .annotS (.lam x b) t => do   -- an ascribed lam's body sees its param's type (as in checking)
      let t' ← resolveTy env.gen env.aliases t         -- data names in user ascriptions close here (ADR-0069)
      let Γ' := curryBind Γ (.lam x b) t'      -- bind EVERY curried param, not just the outermost
      return .annotS (← elabS env Γ' (.lam x b)) t'
  | Γ, .annotS e t => do return .annotS (← elabS env Γ e) (← resolveTy env.gen env.aliases t)
  | Γ, .matchD s arms => do                    -- named match → unfold + matchS chain (ADR-0069)
      let s0 ← elabS env Γ s
      let (Γ, wrap, s0') ← anfSplit Γ s0       -- A-normalize a computation scrutinee, #41
      -- GENERIC (bite-1): derive concrete arm-binder types from the CONCRETE scrutinee μ, so an arm's
      -- `anfSplit` can synthesize a computation (`($length) t`). Monomorphic ctors ⟹ empty table (elabArms
      -- falls back to `payloadClosed`, unchanged).
      -- #55 wall 2: when the scrutinee's type isn't YET a concrete μ (it is a bare higher-order param or
      -- result — `($p) s`, a bare `o`), ANNOTATE it with the arm ctor's TEMPLATE μ (params as markers).
      -- `embVInst` mints fresh param holes at the check, so the scrutinee's `Option`/`List` STRUCTURE is
      -- recovered (and unified back onto the higher-order param), letting a generic `map`/`orElse` match
      -- through a parser argument with NO concrete `: Option (Int * Str)` annotation.
      let (s', binderTys) ← (match armsToList arms with
        | (c0, _, _) :: _ =>
            match env.ctors.lookup c0 with
            | some ci0 =>
                if ci0.params.isEmpty then pure (s0', ([] : List (String × List IVTy)))
                else match runInferV (synthSV Γ s0') with
                     | .ok τ@(.mu _) => pure (s0', genBinderTable env.ctors ci0.dataName τ)   -- concrete: bite-1
                     | _ => do let tmpl ← genTemplateTy env ci0                                -- unknown: template-drive
                               pure (.annotS s0' tmpl, genBinderTable env.ctors ci0.dataName (vtyOf tmpl))
            | none => pure (s0', [])
        | [] => pure (s0', ([] : List (String × List IVTy))))
      let arms' ← elabArms env binderTys Γ arms   -- bodies elaborated under ctor-typed Γ
      match armsToList arms' with
      | [] => .error "match needs at least one arm"
      | armsL@((c0, _, _) :: _) =>
        match env.ctors.lookup c0 with
        | none => .error s!"unknown constructor '{c0}' in match"
        | some ci0 => do
            let dcs := (env.ctors.filter (fun p => p.2.dataName == ci0.dataName)).map Prod.snd
            let dcs := (dcs.toArray.qsort (fun a b => a.idx < b.idx)).toList
            if armsL.length != dcs.length then
              throw s!"match on {ci0.dataName}: {dcs.length} constructor(s), {armsL.length} arm(s)"
            -- GENERIC (bite-1): the scrutinee is a CONCRETE instantiation (`μX. Unit + (Int × X)`), which
            -- can't equal the placeholder `ci0.dataTy` — accept any μ of the right variant count; the arm
            -- binders are typed by the CHECKER from the concrete unrolled μ (`#u = unfold s'`). Monomorphic:
            -- the exact structural equality of ADR-0069, unchanged.
            match runInferV (synthSV Γ s') with
            | .ok τ =>
                if ci0.params.isEmpty then
                  if τ != vtyOf ci0.dataTy then throw s!"match scrutinee is {showVTy τ}, not {ci0.dataName}"
                else match τ with
                     | .mu _ => pure ()
                     | _     => throw s!"match scrutinee is {showVTy τ}, not a {ci0.dataName}"
            | .error e => throw s!"match scrutinee: {e}"
            -- order arms by ctor position (pure bookkeeping — no recursion below)
            let mut ordered : List (List String × Surf) := []
            for ci in dcs do
              match env.ctors.find? (fun p => p.2.dataName == ci.dataName && p.2.idx == ci.idx) with
              | none => throw "impossible: ctor without a name key"
              | some (cn, _) =>
                match armsL.find? (fun a => a.1 == cn) with
                | none => throw s!"match on {ci0.dataName}: missing arm for '{cn}'"
                | some (_, bs, body') => do
                    if bs.length != ci.arity then
                      throw s!"'{cn}' arm binds {bs.length} variable(s), the constructor has arity {ci.arity}"
                    ordered := ordered ++ [(bs, body')]
            return wrap (.lett "#u" (.unfoldS s') (buildMatch ordered "#u"))
  | Γ, .binopS op a b => do
      -- A-normalize computation operands (nested `a + c + 1`, `(V+V)+V`) to VALUES BEFORE dispatch —
      -- both the kernel δ-rule and the trait resolver need value operands (#41). Atoms pass through.
      let a0 ← elabS env Γ a
      let b0 ← elabS env Γ b
      let (Γ1, wa, a') ← anfSplit Γ a0
      let (Γ2, wb, b') ← anfSplit Γ1 b0
      match runInferV (synthSV Γ2 a') with
      | .ok .int  => return wa (wb (.binopS op a' b'))   -- the kernel δ-rule path (ADR-0065)
      | .error _  => return wa (wb (.binopS op a' b'))   -- non-value operand: leave it; the checker rules
      | .ok τ =>
        match asHole τ with
        | some _ => return wa (wb (.binopS op a' b'))     -- HOLE operand (bare-`fun` param): defer to the checker
        | none =>
          match env.insts.find? (fun i => i.opName == binopName op && i.target == τ) with
          | none => .error s!"no impl provides '{binopName op}' for {showVTy τ}"
          | some inst =>
              match inst.params with
              | [p, q] =>
                  let fnTy : Ty := .tArr inst.targetTy (.tArr inst.targetTy inst.retTy)
                  return wa (wb (.app (.app (.annotS (.lam p (.lam q inst.body)) fnTy) a') b'))
              | _ => .error s!"'{inst.opName}': operator resolution needs exactly 2 params (got {inst.params.length})"

/-- Elaborate named-match arm BODIES structurally over `DArms`, each under its ctor's
payload-typed Γ (unknown ctor / wrong arity ⇒ un-extended Γ here; the `matchD` arm's
validation fail-louds right after). -/
def elabArms (env : ElabEnv) (binderTys : List (String × List IVTy)) : NCtx → DArms → Except String DArms
  | _, .nil => .ok .nil
  | Γ, .cons c bs b r => do
      let Γa := match binderTys.lookup c with
        -- GENERIC (bite-1): concrete field types derived from the scrutinee's μ (`genBinderTable`).
        | some tys =>
            (match bs, tys with
             | [b1], [t1]         => (b1, (t1 : Scheme)) :: Γ
             | [b1, b2], [t1, t2] => (b2, (t2 : Scheme)) :: (b1, (t1 : Scheme)) :: Γ
             | _, _               => Γ)
        -- MONOMORPHIC: the ctor's own closed payload types (ADR-0069), unchanged.
        | none => match env.ctors.lookup c with
          | some ci =>
              (match bs, ci.payloadClosed with
               | [b1], [t1]         => (b1, embV (vtyOf t1)) :: Γ
               | [b1, b2], [t1, t2] => (b2, embV (vtyOf t2)) :: (b1, embV (vtyOf t1)) :: Γ
               | _, _               => Γ)
          | none => Γ
      let b' ← elabS env Γa b
      let r' ← elabArms env binderTys Γ r
      .ok (.cons c bs b' r')
end

/-- Build the elaboration environment from a program's decl prelude, IN ORDER (a data type may
reference itself + earlier decls; forward references fail loud). Data: encode the μ body
(self ↦ `tVar 0` — no surface μ syntax means self never sits under a nested binder, so depth 0
is always right) and the closed binder-typing payloads (self ↦ the closed μ). Impls: resolve
the target, validate against the trait (op name + param arity), and PRE-ELABORATE op bodies
against the env-so-far — nested ctors and EARLIER ops resolve; a self-recursive op fail-louds
as an unresolved operator (out of scope until `fix` lands, ADR-0069). PUBLIC (#60 seam): the
law-runner harness needs a real `ElabEnv` (trait/impl-derived) to drive `checkLawOn`, and this
is the only constructor of one from a parsed decl list — no behavior change, additive visibility
only. -/
public def buildEnv (ds : List Decl) : Except String ElabEnv := do
  let mut aliases : List (String × Ty) := []
  let mut ctors   : List (String × CtorInfo) := []
  let mut insts   : InstEnv := []
  let mut traits  : List (String × List OpSig) := []
  let mut gen     : List (String × GenData) := []
  let mut bfns    : List (String × BoundedFn) := []
  let mut rawImpls : List RawImpl := []
  let mut hktTraits   : List (String × List String) := []
  let mut hktMethodOf : List (String × String) := []
  let mut hktImpls    : List HktImpl := []
  let mut effects     : List (String × EffectInfo) := []
  for d in ds do
    match d with
    | .dataD n [] cs => do                       -- MONOMORPHIC: byte-identical to the ADR-0069 path
        if cs.isEmpty then throw s!"data {n}: needs at least one constructor"
        if (aliases.lookup n).isSome || (gen.lookup n).isSome then throw s!"duplicate type name '{n}'"
        let openPays ← cs.mapM (fun c => c.2.mapM (resolveTy gen ((n, Ty.tVar 0) :: aliases)))
        let closed := Ty.tMu (sumOfTys (openPays.map prodOfTys))
        let closedPays ← cs.mapM (fun c => c.2.mapM (resolveTy gen ((n, closed) :: aliases)))
        aliases := (n, closed) :: aliases
        let mut i := 0
        for (c, cp) in cs.zip closedPays do
          if (ctors.lookup c.1).isSome then throw s!"duplicate constructor '{c.1}'"
          if cp.length > 2 then throw s!"constructor '{c.1}': payload arity ≤ 2 in v1 (nest tuples)"
          ctors := (c.1, ⟨n, i, cs.length, cp.length, cp, closed, [], []⟩) :: ctors
          i := i + 1
    | .dataD n params cs => do                   -- GENERIC (ADR-0069 bite-1): register the TEMPLATE; ctors monomorphize per use
        if cs.isEmpty then throw s!"data {n}: needs at least one constructor"
        if (aliases.lookup n).isSome || (gen.lookup n).isSome then throw s!"duplicate type name '{n}'"
        if params.eraseDups.length != params.length then throw s!"data {n}: duplicate type parameter"
        gen := (n, ⟨params, cs⟩) :: gen
        let mut i := 0
        for c in cs do
          if (ctors.lookup c.1).isSome then throw s!"duplicate constructor '{c.1}'"
          if c.2.length > 2 then throw s!"constructor '{c.1}': payload arity ≤ 2 in v1 (nest tuples)"
          ctors := (c.1, ⟨n, i, cs.length, c.2.length, [], .tUnit, params, c.2⟩) :: ctors
          i := i + 1
    | .traitD n params sigs _ => do
        traits := (n, sigs) :: traits
        if !params.isEmpty then                       -- HKT (ADR-0082): a constructor-kinded trait
          if params.length != 1 then throw s!"trait {n}: v1 supports exactly one constructor-kinded parameter"
          -- kind-check every method sig: an applied trait-param `f a` must be arity-1, `Int Int` etc. rejected
          for sig in sigs do
            kindCheckTy params sig.methodTy
          hktTraits := (n, params) :: hktTraits
          for sig in sigs do hktMethodOf := (sig.name, n) :: hktMethodOf
    | .implD tn τTy ops =>
        match hktTraits.lookup tn with
        | some _ => do                                 -- HKT (ADR-0082): key the impl on the carrier CONSTRUCTOR name
            let ctor ← match hktCtorHead τTy with
              | some c => pure c
              | none   => throw s!"impl '{tn}': the carrier must be a constructor name (`impl {tn} for Option`)"
            for od in ops do
              if !(sigsHasOp (traits.lookup tn) od.name) then
                throw s!"impl '{tn}' defines '{od.name}', which is not an op of the trait"
            hktImpls := hktImpls ++ [⟨tn, ctor, ops⟩]
        | none =>
        match traits.lookup tn with
        | none => throw s!"impl of undeclared trait '{tn}'"
        | some sigs => do
            let τR ← resolveTy gen aliases τTy
            let mut rawOps : List RawOp := []
            for od in ops do
              match sigs.find? (fun s => s.name == od.name) with
              | none => throw s!"impl '{tn}' defines '{od.name}', which is not an op of the trait"
              | some sig => do
                  if od.params.length != sig.params.length then
                    throw s!"'{od.name}': impl has {od.params.length} params, the trait declares {sig.params.length}"
                  let retR ← resolveTy gen aliases (substSelf τR sig.retTy)
                  -- op params are all `Self`-typed (v1 convention); a 0-ary op (`empty`) has none.
                  let bodyΓ : NCtx := od.params.map (fun p => (p, embV (vtyOf τR)))
                  let ebody ← elabS ⟨insts, ctors, aliases, gen, [], [], [], [], [], []⟩ bodyΓ od.body
                  insts := insts ++ [⟨od.name, vtyOf τR, τR, retR, od.params, ebody⟩]
                  rawOps := rawOps ++ [⟨od.name, od.params, od.body, sig.retTy⟩]   -- RAW, for bounded-fn monomorphization
            rawImpls := rawImpls ++ [⟨tn, vtyOf τR, rawOps⟩]
    | .fnD n ps ty tr tv b =>                    -- bounded generic function (bite-2, ADR-0080)
        if (traits.lookup tr).isNone then throw s!"fn '{n}': bound trait '{tr}' is not declared"
        if (bfns.lookup n).isSome then throw s!"duplicate function '{n}'"
        bfns := (n, ⟨n, ps, ty, tr, tv, b⟩) :: bfns
    | .effectD n ops => do                       -- ADR-0092 D1/D2: `effect N { op : ArgTy -> ResTy, … }`
        -- D1: duplicate EFFECT names are a LOUD elaboration error (op-name duplicates within one
        -- block are already caught at PARSE time, `pEffectMembers`) — naming both conflicting sites
        -- isn't possible with only a name here (the parser doesn't carry spans this deep), so the
        -- message names the effect; ADR-0076's span-view still locates the token by name downstream.
        if (effects.lookup n).isSome then throw s!"duplicate effect '{n}'"
        if ops.isEmpty then throw s!"effect {n}: needs at least one operation"
        -- BUILT-IN op names are RESERVED in an `effect` decl, v1 (operator ruling, follow-up to
        -- D1/D2's initial landing). Root cause: the label-first `.dotPerform` dispatch fix (this
        -- file) makes elaboration correctly type a user op sharing a built-in's NAME (dispatch is
        -- by the receiver's LABEL, not the op name) — but the MACHINE side (`Bang/Core`, the s4
        -- lane's op-priority guard: a built-in op is never served by a custom clause) has an
        -- INDEPENDENT name-keyed check that does not know about user labels. A user effect named
        -- `get`/`put`/`raise`/`new`/`read`/`write` would therefore TYPE fine here but could
        -- diverge from the machine at runtime once D3/D4 land the typed custom-handle — a typed-
        -- program/machine gap, exactly the class the Agree differential battery exists to catch,
        -- currently UNWITNESSED for user effects. Closing it AT THE SURFACE, by construction, is
        -- cheaper than coordinating two independent name checks across lanes: reserving the names
        -- here makes the collision UNREPRESENTABLE in any elaborated program, so the machine's
        -- guard is vacuously safe for everything that type-checks. `capOpSig` (this file) is the
        -- SINGLE SOURCE OF TRUTH for "which names are built-in" — checked directly (`.isSome`),
        -- never a hand-copied name list, so a future built-in op addition can't silently desync
        -- this reservation from what `.dotPerform`'s built-in arm actually recognizes.
        -- DEFERRED: real per-effect NAMESPACING (so `Net.get` and the built-in `get` coexist) is
        -- the Q34/Q38 module-interface work's territory, not this ADR's — this reservation is the
        -- v1 stopgap, not the final design.
        for (opName, _) in ops do
          if (capOpSig opName).isSome then
            throw s!"effect {n}: op '{opName}' is reserved by a built-in effect (v1 restriction — see ADR-0092)"
        -- D1: label := 4 + declIndex, deterministic by EFFECT-decl order (the four built-ins keep
        -- 0-3; `effects.length` is exactly "how many effect decls processed so far", so this is
        -- stable under interleaving with data/trait/impl/fn decls — only relative EFFECT order
        -- matters, matching D1's "decl order" (the effect sub-sequence, not the whole decl list).
        let ℓ : Label := 4 + effects.length
        -- D2: resolve each op's declared Ty into (argTy?, resTy) — a bare type is 0-ary; a single
        -- arrow `A -> B` is v1's one-arg op (ADR-0085 D4's sketch); anything else (a multi-arrow,
        -- `A -> B -> C`) is OUT of v1 scope and fail-louds rather than silently truncating.
        let mut opSigs : List (String × Option VT × VT) := []
        for (opName, ty) in ops do
          let tyR ← resolveTy gen aliases ty
          match tyR with
          | .tArr a b =>
              match tyBoth b with
              | (_, .F _ resV) => opSigs := opSigs ++ [(opName, some (vtyOf a), resV)]
              | (_, .arr ..)   => throw s!"effect {n}: op '{opName}' is multi-argument — v1 supports only a single `ArgTy -> ResTy` arrow"
          | _ => opSigs := opSigs ++ [(opName, none, vtyOf tyR)]
        effects := (n, ⟨ℓ, opSigs⟩) :: effects
  return ⟨insts, ctors, aliases, gen, bfns, rawImpls, hktTraits, hktMethodOf, hktImpls, effects⟩

/-- The built-in string prelude (ADR-0074): `Char` = a code point (a newtype over `Int`, distinct so
you can't mix a char and a number), `Str` = a monomorphic char-list. Injected before every program so
string/char literals (`"hi"`, `'a'`) resolve, UNLESS the program declares `Char`/`Str` itself. Library
code over `data` + `Int` — NO kernel primitive (invariant #5). -/
def strPrelude : List Decl :=
  [ .dataD "Char" [] [("Char", [.tInt])],
    .dataD "Str"  [] [("SNil", []), ("SCons", [.tName "Char", .tName "Str"])] ]

/-- The built-in GENERIC prelude: the universal tagged-sum types, injected before every program so
`Some`/`None`/`Ok`/`Err` resolve with NO declaration (enabled by generic data — ADR-0079 — plus
annotation-free introduction — ADR-0081/#55). `Option a` is nullable/`Maybe`; `Result e a` is
Rust-style success/error (`Ok` = success), two type params (the v1 arity-≤2 ceiling, ADR-0079).
`Either e a` is NOT here: it IS the built-in binary sum `e + a` — `Left`/`Right`/`match` are already
reserved surface primitives for it (Surface.pIdent), so `Either` needs no data decl (one construct per
problem — the isos below convert between `Result`/`Option` and this built-in sum). Each type is
filtered out (like `Str`/`Char`) when the user redeclares it. Library over `data` — NO kernel
primitive (invariant #5). -/
def genericPrelude : List Decl :=
  [ .dataD "Option" ["a"]      [("None", []),           ("Some",  [.tName "a"])],
    .dataD "Result" ["e", "a"] [("Err",  [.tName "e"]), ("Ok",    [.tName "a"])] ]

/-- The built-in string STDLIB (ADR-0074, #49 stage 3): `concat`/`reverse`/`eq` as `let rec` folds
over `Str`, injected in scope of EVERY program's body (closing the #50 reuse gap — a program shouldn't
re-inline `concat` the way the tokenizer had to). Each fn is a source string ending in a placeholder
body (`0`); `injectStdlib` parses it, keeps the `let rec` head, and re-roots it over the user body.
Ordered `concat → reverse → eq` so `reverse` (which appends via `concat`) sees it. `concat`/`eq` are
CURRIED so `letRecRow` types them `! {Div}` (multi-arg #47 gap, ADR-0073) — a sound over-approximation:
they terminate but the certifier can't prove it. `reverse` picks up `Div` transitively (it calls
`$concat`). Library over `data` + `let rec` — NO kernel change (invariant #5). -/
def stdlibFnSrcs : List String :=
  [ "let rec concat : Str -> Str -> Str = fun a => fun b => " ++
      "match a { SNil -> b, SCons(c, t) -> SCons(c, ($concat) t b) } in 0",
    -- `reverse` folds via an accumulator: a curried recursive `revApp` (nested in the thunk so it is
    -- NOT exposed) threads the reversed prefix, and `reverse s = revApp SNil s`. A direct single-arg
    -- `reverse` that appends via `$concat` does NOT type-check (buildLetRec's inner knot demands a
    -- single-arg structural fold be self-contained — it can't call another `Div` fn), so the
    -- accumulator is the working shape. `Div` (curried `revApp`) rides the result.
    "let reverse = { let rec revApp : Str -> Str -> Str = fun acc => fun s => " ++
      "match (s : Str) { SNil -> acc, SCons(c, t) -> ($revApp) (SCons(c, acc)) t } in " ++
      "fun s => ($revApp) SNil s } in 0",
    -- `eq` compares char-by-char; `Bool = Unit + Unit` (ADR-0065), `0==0` = true, `0==1` = false. The
    -- SECOND curried param `b` needs a `(b : Str)` ascription so the named-match resolver sees its type
    -- (curried params past the first aren't propagated into elaboration-time match resolution).
    "let rec eq : Str -> Str -> Unit + Unit = fun a => fun b => " ++
      "match a { SNil -> match (b : Str) { SNil -> 0 == 0, SCons(c2, t2) -> 0 == 1 }, " ++
      "SCons(c, t) -> match (b : Str) { SNil -> 0 == 1, " ++
      "SCons(c2, t2) -> if (match c { Char(n) -> match c2 { Char(m) -> n == m } }) " ++
      "then ($eq) t t2 else 0 == 1 } } in 0" ]

/-- Wrap `body` in the string-stdlib `let rec`s (see `stdlibFnSrcs`). INERT for programs that don't
use them: each `let rec … in body` binds a THUNK (a value, `⊥`-row) — the program's row is the body's
row, so an unused `Div`-typed stdlib fn adds NO effect (mirrors the unused `Char`/`Str` ctors). A
user binding of the same name in the body simply SHADOWS the injected one (lexical scope). SKIPPED
when the user redeclares `Str`/`Char` (the injected fns reference the prelude ctors, which the user's
data may not provide) — same discipline as the data prelude's `declared` filter. -/
def wrapFnSrcs (srcs : List String) (body : Surf) : Except String Surf := do
  let wraps ← srcs.mapM (fun src => do
    match ← Bang.Surface.parse src with
    | .letRecS n t f _ => return (fun (b : Surf) => Surf.letRecS n t f b)
    | .lett n rhs _    => return (fun (b : Surf) => Surf.lett n rhs b)
    | _ => .error "prelude fn did not parse as a `let`/`let rec`")
  return wraps.foldr (fun w acc => w acc) body

/-! Does `nm` occur as a free-ish variable reference anywhere in `e` (`surfUsesVar`)? A syntactic
over-approximation (ignores shadowing — a shadowed use just over-injects, costing a little fuel, never
wrong). Used to inject a generic-prelude fn ONLY when the program mentions it, so an unused combinator
costs NO eval fuel (keeping tight-fuel programs green — the string stdlib's `let rec`s are cheap enough
to stay unconditional, these 7 are not in aggregate). -/
mutual
def surfUsesVar (nm : String) : Surf → Bool
  | .var x                         => x == nm
  | .lit _ | .getS | .unitS        => false
  | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
  | .lam _ e | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ => surfUsesVar nm e
  | .lett _ a b | .app a b | .stateS a b | .writeS a b | .pairS a b | .splitS _ _ a b
  | .binopS _ a b                  => surfUsesVar nm a || surfUsesVar nm b
  | .matchS s _ l _ r              => surfUsesVar nm s || surfUsesVar nm l || surfUsesVar nm r
  | .ifS c t e                     => surfUsesVar nm c || surfUsesVar nm t || surfUsesVar nm e
  | .matchD s arms                 => surfUsesVar nm s || dArmsUseVar nm arms
  | .withCapS _ i _ b              => surfUsesVar nm i || surfUsesVar nm b
  | .dotPerform r _ .none          => surfUsesVar nm r
  | .dotPerform r _ (.one a)       => surfUsesVar nm r || surfUsesVar nm a
  | .dotPerform r _ (.two a b)     => surfUsesVar nm r || surfUsesVar nm a || surfUsesVar nm b
  | .letRecS _ _ f b               => surfUsesVar nm f || surfUsesVar nm b
def dArmsUseVar (nm : String) : DArms → Bool
  | .nil            => false
  | .cons _ _ b rest => surfUsesVar nm b || dArmsUseVar nm rest
end

/-- The GENERIC-prelude functions (`genericPrelude` types + the built-in sum `Either`, ADR-0081
annotation-free): per-type maps + the isomorphism conversions, injected in scope of EVERY program's
body — `Option`/`Result`/`Either` come with their combinators built in (the #50 reuse discipline).
Plain `let`s binding THUNKS ⟹ ⊥-row VALUES, so they're INERT for programs that don't use them (unlike
the `Div`-typed string stdlib): an unused prelude fn adds NO effect and leaves a pure program pure.
`mapOption`/`mapResult` are higher-order over generic data (ADR-0081 #55: `match` recovers the
scrutinee's type from its arm ctors, `Some(($f) x)` constructs annotation-free); `bimap` + the isos
range over the built-in sum (`Either = e + a`). The four `*To*` functions WITNESS the `Result ≅ Either`
and `Option ≅ Either Unit` isos — their round-trips (`from ∘ to = id`) are property-tested below. -/
def genericPreludeFnSrcs : List String :=
  [ -- `mapOption f : Option a -> Option b` — map the payload; `None` passes through.
    "let mapOption = { fun f => fun o => match o { None -> None, Some(x) -> Some(($f) x) } } in 0",
    -- `mapResult f : Result e a -> Result e b` — map the SUCCESS side (`Ok`); an `Err` passes through
    -- (Rust's `Result::map`). The error type `e` is untouched.
    "let mapResult = { fun f => fun r => match r { Err(e) -> Err(e), Ok(a) -> Ok(($f) a) } } in 0",
    -- `bimap g f : (e + a) -> (f + b)` — the BIFUNCTOR map over the built-in sum (`Either`): `g` over
    -- `Left`, `f` over `Right` (both sides, unlike `mapResult`'s success-only).
    "let bimap = { fun g => fun f => fun x => match x { Left(e) -> Left(($g) e), Right(a) -> Right(($f) a) } } in 0",
    -- `resultToEither : Result e a -> (e + a)` — `Err ↦ Left`, `Ok ↦ Right` (the iso `to`).
    "let resultToEither = { fun r => match r { Err(e) -> Left(e), Ok(a) -> Right(a) } } in 0",
    -- `eitherToResult : (e + a) -> Result e a` — `Left ↦ Err`, `Right ↦ Ok` (the iso `from`).
    "let eitherToResult = { fun x => match x { Left(e) -> Err(e), Right(a) -> Ok(a) } } in 0",
    -- `optionToEither : Option a -> (Unit + a)` — `None ↦ Left(())`, `Some ↦ Right` (`Option ≅ Either Unit`).
    "let optionToEither = { fun o => match o { None -> Left(()), Some(a) -> Right(a) } } in 0",
    -- `eitherToOption : (Unit + a) -> Option a` — `Left ↦ None`, `Right ↦ Some` (the `from`).
    "let eitherToOption = { fun x => match x { Left(u) -> None, Right(a) -> Some(a) } } in 0" ]

/-- Wrap `body` with each generic-prelude fn (`genericPreludeFnSrcs`) ONLY if `body` mentions its name.
The fns are mutually independent (none calls another), so checking the raw user body is complete. -/
def wrapGenericFns (body : Surf) : Except String Surf := do
  let mut wraps : List (Surf → Surf) := []
  for src in genericPreludeFnSrcs do
    match ← Bang.Surface.parse src with
    | .lett n rhs _ => if surfUsesVar n body then wraps := wraps ++ [fun (b : Surf) => Surf.lett n rhs b]
    | _ => .error "generic prelude fn did not parse as a `let`"
  return wraps.foldr (fun w acc => w acc) body

/-- Inject the injected-in-scope prelude FUNCTIONS: the `Div`-typed string stdlib
(`concat`/`reverse`/`eq`, `stdlibFnSrcs`) — SKIPPED when the user redeclares `Str`/`Char` (the fns
reference the prelude ctors) — and the ⊥-row generic-prelude combinators (`genericPreludeFnSrcs`) —
SKIPPED when the user redeclares ANY of `Option`/`Result`/`Either` (they take over those types). The
two bundles are independent (the generic combinators reference no string types), so they gate
separately. A user binding of the same name in the body simply SHADOWS the injected one. -/
def injectStdlib (declared : List String) (body : Surf) : Except String Surf := do
  let body ← if declared.contains "Option" || declared.contains "Result"
             then pure body else wrapGenericFns body
  if declared.contains "Str" || declared.contains "Char" then
    return body
  wrapFnSrcs stdlibFnSrcs body

/-- Elaborate a whole program: inject the string prelude + stdlib, build the elaboration env, resolve
the body. Returns the elaborated body ALONGSIDE `env.effects` (ADR-0092 D2) — the type-checker's
`.dotPerform` arm needs the program's user-effect table to resolve a `perform` against a declared
`effect`'s op, and `synthSC`/`checkSC` have no separate `ElabEnv` parameter (see `USt.effects`'s
comment) — so `elabProg`'s caller threads the pair into `runInferC`. -/
def elabProg (p : Prog) : Except String (Surf × List (String × EffectInfo)) := do
  let declared := p.decls.filterMap (fun | .dataD n _ _ => some n | _ => none)
  let prelude := (strPrelude ++ genericPrelude).filter (fun | .dataD n _ _ => !declared.contains n | _ => true)
  let body ← injectStdlib declared p.body
  let env ← buildEnv (prelude ++ p.decls)
  let e ← elabS env [] (← expandBFns env none bigFuel body)   -- bounded-fn uses → their monomorphic wrappers, THEN elaborate (bite-2)
  return (e, env.effects)

/-- PUBLIC runnable entry (the `bang` CLI's typed pipeline): parse a program's `trait`/`impl`/`data`
prelude + body, elaborate it (resolve data constructors, named matches, and type-directed operators
like `Vec + Vec`), and lower to a kernel `Comp` ready for `Source.eval`/the machine. A decl-free
program parses to `⟨[], body⟩` and elaborates to itself, so this is a strict SUPERSET of the old
`Surface.lower ∘ parse` runner path — the whole MVP surface becomes runnable from the CLI. -/
public def elaborateToComp (src : String) : Except String Comp := do
  let prog ← Bang.Surface.parseProg src
  let (e, _) ← elabProg prog
  Bang.Surface.lower e

/-- PUBLIC typed runnable entry (the `bang` CLI's DEFAULT pipeline, ADR-0076 #51): parse (located) →
elaborate → **TYPE-CHECK** → lower. The type-check is the same `synthSC`/`runInferC` the `#guard`
gate uses (`check`/`checkProg`), so the run path and the guard path share ONE type gate (SSoT) — an
ill-typed program is now REJECTED with a type error instead of running to a runtime `stuck`
(realizing `type_safety`: well-typed ⟹ never stuck). This is `elaborateToComp` with the check
inserted; the raw (check-free) `elaborateToComp` stays the `--no-typecheck` escape. The error carries
an optional `Span`: a PARSE error is located (`some`, → `line:col`); an elaboration/type error is
POST-HOC located (`Surface.locateInMsg` — the message names a construct, a span-view finds it; #52
Stage B) when it names a locatable token, else un-located (`none` → a plain message; the deferred
per-node span tier). -/
public def checkAndLower (src : String) : Except (String × Option Bang.Surface.Span) Comp := do
  let prog ← Bang.Surface.parseProgLocated src
  let (e, effects) ← (elabProg prog).mapError (fun m => (m, Bang.Surface.locateInMsg src m))
  let _ ← (runInferC (synthSC [] e) effects).mapError (fun m => (m, Bang.Surface.locateInMsg src m))
  (Bang.Surface.lower e).mapError (fun m => (m, Bang.Surface.locateInMsg src m))

/-- Parse + elaborate + CHECK a source program — the decl-aware, typed sibling of `check`. -/
def checkProg (src : String) : Except String (CT × EffRow) := do
  let (e, effects) ← Bang.Surface.parseProg src >>= elabProg
  runInferC (synthSC [] e) effects

/-- Parse + elaborate + check + DISPLAY — the decl-aware, typed sibling of `display`. Re-derives
`effects` alongside the checked type (rather than widening `checkProg`'s established `(CT ×
EffRow)` return type, which `typeStringOfProg`/the REPL's `:t` already depend on) so a DECLARED
user-effect label in the row renders by its SOURCE name (ADR-0092 D2), not silently vanishing. -/
def displayProg (src : String) : String :=
  match (do
      let (e, effects) ← Bang.Surface.parseProg src >>= elabProg
      let (B, φ) ← runInferC (synthSC [] e) effects
      return (B, φ, effects)) with
  | .ok (B, φ, effects) => showType B φ effects
  | .error e            => s!"error: {e}"

/-- TEST-ONLY (ADR-0092 D1/D2, no surface syntax): type `perform` (`.dotPerform`) against a
DECLARED user effect under a HYPOTHETICAL capability binding `capName : Cap ℓ` — the D3 typed
custom-HANDLE rule (the sibling kernel lane's work) is what would normally introduce such a
binding via `handle e with Effect { … }`; until it lands, this internal helper is what lets D1/D2
be asserted end-to-end: "the performer side is already general" (ADR-0092's own grounding fact)
means `.dotPerform`'s typing arm needs NOTHING from D3 to run correctly — it only needs a `Cap ℓ`
in scope, however that binding arrives. `declsSrc` supplies the `effect` decl(s) (+ any `data` the
op signatures reference); `effectName`/`capName` name the effect and the hypothetical binder;
`exprSrc` is the `.dotPerform`-shaped body (`capName.op(args)` or `capName.op`), checked under
`Γ = [(capName, Cap ℓ)]` where `ℓ` is `effectName`'s ALLOCATED label. -/
def checkPerformUnderCap (declsSrc effectName capName exprSrc : String) :
    Except String (CT × EffRow) := do
  let declsProg ← Bang.Surface.parseProg declsSrc
  if declsProg.body != .lit 0 then throw "checkPerformUnderCap: declsSrc must be decls-only (end in a placeholder `0`)"
  let env ← buildEnv declsProg.decls
  match env.effects.lookup effectName with
  | none => throw s!"checkPerformUnderCap: effect '{effectName}' is not declared in declsSrc"
  | some ei => do
      let bodyE ← Bang.Surface.parse exprSrc
      let capTy : IVTy := .cap ei.label
      let ebody ← elabS env [(capName, capTy)] bodyE
      runInferC (synthSC [(capName, capTy)] ebody) env.effects

/-- PUBLIC face of the checker for external tools (the REPL's `:t`, #7): the rendered
`type ! row` of a checked program, or the check error as `.error`. Thin wrapper —
`checkProg`/`showType` stay the SSoT; the `Except` (vs `displayProg`'s inline string)
lets a caller route errors to stderr and keep stdout machine-clean. -/
public def typeStringOfProg (src : String) : Except String String :=
  (checkProg src).map (fun (B, φ) => showType B φ)


/-! ### The TYPED face of the `Outcome` layer (issue #54).

The `Outcome` ADT + `evalToOutcome`/`outcomeIs` live in `Surface` (over the untyped `runFrom`). Here
they get the TWO typed runners, reusing the production entries (`checkAndLower`/`elaborateToComp`) as
SSoT. The split is FORCED by type safety: a well-typed program NEVER goes `.stuck` (`type_safety`:
progress), so `.stuck` is reachable ONLY through the raw (`--no-typecheck`) path — the `Outcome` layer
makes that stratification seam directly assertable. -/

/-- TYPED pipeline (the production default, `checkAndLower`). A parse error keeps its `Span` (`some`);
an elaboration/type error is `typeErr`. Never returns `.stuck` (type safety). -/
def runOutcome (fuel : Nat) (src : String) : Outcome :=
  match checkAndLower src with
  | .error (m, some sp) => .parseErr (some sp) m
  | .error (m, none)    => .typeErr m
  | .ok c               => evalToOutcome (Source.eval fuel c)

/-- UNTYPED escape (`--no-typecheck`, `elaborateToComp`): no type gate, so `.stuck`/`.escaped` are
reachable. `elaborateToComp` parses un-located, so a parse error here carries no span. -/
def runOutcomeRaw (fuel : Nat) (src : String) : Outcome :=
  match elaborateToComp src with
  | .error m => .parseErr none m
  | .ok c    => evalToOutcome (Source.eval fuel c)

/-- Does the typed run report a TYPE error? -/
def assertTypeError (fuel : Nat) (src : String) : Bool :=
  match runOutcome fuel src with | .typeErr _ => true | _ => false

/-- Does the typed run report a located PARSE error at `line:col`? -/
def assertParseErrorAt (fuel : Nat) (src : String) (line col : Nat) : Bool :=
  match runOutcome fuel src with | .parseErr (some sp) _ => sp.line == line && sp.col == col | _ => false

/-- Does the typed run exhaust fuel (`oom`)? Reachable through the type gate (a well-typed diverging
program). -/
def assertTypedOom (fuel : Nat) (src : String) : Bool :=
  match runOutcome fuel src with | .oom => true | _ => false

/-- Parse + elaborate + CHECK + lower + RUN through `Source.eval`, expecting `vint n` — the typed
sibling of `Surface.runYieldsInt` (which stays untyped and decl-free). The typed path checks BEFORE
it runs. Now a thin PROJECTION of the `Outcome` layer (issue #54) over the SAME typed path (so
behaviour is identical — the green corpus is the build-gated proof). -/
def runTypedYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  match (do
      let (e, effects) ← Bang.Surface.parseProg src >>= elabProg
      let _ ← runInferC (synthSC [] e) effects
      Bang.Surface.lower e) with
  | .ok c => outcomeIs (evalToOutcome (Source.eval fuel c)) (.yields (.vint n))
  | .error _ => false

/-! #### Exceptional / error terminals — the typed `Outcome` layer's NEW capability (issue #54). -/

-- a TYPE error: `1 + Left(0)` — the sum injection can't be added to an Int (elaborator rejects).
#guard assertTypeError 20 "1 + Left(0)"
-- a located PARSE error: `let x 3 in x` — the missing `=` (the `3` sits where `=` was wanted) at 1:7.
#guard assertParseErrorAt 20 "let x 3 in x" 1 7
-- an OOM: an unbounded recursion (types fine ⇒ the typed path reaches it) under bounded fuel.
#guard assertTypedOom 60 "let rec loop : Int -> Int = fun n => ($loop)(n + 1) in ($loop) 0"
-- a STUCK: force a NON-thunk (`$3`) — rejected by the type gate, so run RAW (`--no-typecheck`).
#guard (match runOutcomeRaw 20 "$3" with | .stuck => true | _ => false)
-- the typed projection is STRICTLY MORE INFORMATIVE than `runTypedYieldsInt`: where the bespoke
-- helper says only `false`, the `Outcome` names the actual terminal (here: a type error).
#guard (runTypedYieldsInt 20 "1 + Left(0)" 0 == false) && assertTypeError 20 "1 + Left(0)"

/-! #### issue #52 Stage B (option-2 sweep): structural mismatches NAME their bare-variable operand,
so `checkAndLower`'s `.error (m, none)` (an un-located message) becomes `.error (m, some span)` for
the common case — the offending term IS a plain variable, not a compound expression. Each pair below
runs the SAME program through `checkAndLower` twice: the message now carries the quoted name (was
bare), and `Surface.locateInMsg` resolves it to the variable's exact source span (this is the real
producer, not a hand-picked `(src, msg)` pair — the `Surface.lean:1173` sentinel stays a pure-function
unit test of the fallback, decoupled from any actual program). -/

-- `force: not a thunk` — forcing a plain Int variable now names it, locatable at its bind site.
#guard (match checkAndLower "let x = 3 in $x" with
        | .error (m, _) => (m.splitOn "'x'").length > 1
        | .ok _ => false)
#guard (match checkAndLower "let x = 3 in $x" with
        | .error (m, _) => (Bang.Surface.locateInMsg "let x = 3 in $x" m).map (·.loc) == some "1:5"
        | .ok _ => false)
-- `app: callee is not a function` — applying a plain Int variable names it.
#guard (match checkAndLower "let f = 3 in f 5" with
        | .error (m, _) => (Bang.Surface.locateInMsg "let f = 3 in f 5" m).map (·.loc) == some "1:5"
        | .ok _ => false)
-- `match: scrutinee is not a sum` — matching a plain Int variable names it.
#guard (match checkAndLower "let x = 3 in match x { Left(a) -> a, Right(b) -> b }" with
        | .error (m, _) =>
            (Bang.Surface.locateInMsg "let x = 3 in match x { Left(a) -> a, Right(b) -> b }" m).isSome
        | .ok _ => false)
-- `split: scrutinee is not a product` — destructuring a plain Int variable names it.
#guard (match checkAndLower "let p = 3 in let (a, b) = p in a" with
        | .error (m, _) => (Bang.Surface.locateInMsg "let p = 3 in let (a, b) = p in a" m).isSome
        | .ok _ => false)
-- a COMPOUND (non-`.var`) operand stays un-located (the honest, documented residual): forcing a
-- literal PAIR `(1, 2)` is rejected (not a thunk), but the force target is a `pairS`, not a bare
-- variable — `nameHint` correctly contributes nothing, so the message carries no quoted name and
-- `locateInMsg` reports `none` (the fallback the Stage-B doc comment describes, not a regression).
#guard (match checkAndLower "$(1, 2)" with
        | .error (m, _) => (Bang.Surface.locateInMsg "$(1, 2)" m) == none
        | .ok _ => false)

/-! ### Validation ⑥ — the NORTHSTAR: `(1,2) + (3,4)`, resolved, typed, run via the oracle. -/

/-- The demo prelude: an `Add` trait + its `(Int * Int)` instance (component-wise addition,
written in let-normal form — pair components are VALUES in CBPV, so the sums are bound first). -/
def vecProg (body : String) : String :=
  "trait Add { fn add(a, b) -> Self } " ++
  "impl Add for (Int * Int) { fn add(p, q) = " ++
  "let (a, b) = p in (let (c, d) = q in (let x = a + c in (let y = b + d in (x, y)))) } " ++
  body

-- THE NORTHSTAR RUNS: (1,2) + (3,4) = (4,6), resolved through the impl, checked, run via Source.eval.
#guard runTypedYieldsInt 200 (vecProg "let s = (1, 2) + (3, 4) in (let (x, y) = s in x)") 4
#guard runTypedYieldsInt 200 (vecProg "let s = (1, 2) + (3, 4) in (let (x, y) = s in y)") 6
-- the resolved operator DISPLAYS at the instance type.
#guard displayProg (vecProg "(1, 2) + (3, 4)") == "(Int * Int)"
-- resolution is TYPE-directed: Int operands still take the kernel δ-rule under the same decls.
#guard runTypedYieldsInt 50 (vecProg "2 + 3") 5
#guard displayProg (vecProg "1 + 2") == "Int"
-- fail-loud: an operand type with NO impl.
#guard (match checkProg "trait Add { fn add(a, b) -> Self } (1, 2) + (3, 4)" with
        | .error _ => true | _ => false)
-- fail-loud: an impl of an undeclared trait.
#guard (match checkProg "impl Add for (Int * Int) { fn add(p, q) = p } 0" with
        | .error _ => true | _ => false)
-- fail-loud: an impl op that is not in the trait.
#guard (match checkProg "trait Add { fn add(a, b) -> Self } impl Add for (Int * Int) { fn mul(p, q) = p } 0" with
        | .error _ => true | _ => false)
-- plain programs: the typed entry agrees with the decl-free checker.
#guard checkProg "let x = 2 in x + 3" == check "let x = 2 in x + 3"

/-! ## Stage ⑤c — source LAWS discharge on the tested rung (#24 piece 3; ADR-0068 decision 1).

A parsed `law` is CHECKED against the verified interpreter: each sample tuple binds the law's
params (implicitly `Self`-typed, like ops), the Bool-valued body is elaborated (operators resolve
through the impls), lowered, and run via `Source.eval`; the law holds on its sample iff every run
yields true. This is the v1 source-law CEILING — the tested rung, marked `↓` in the report (never
silent); the VERIFIED rung stays Lean-level (`Surface/Trait.lean`'s `mkVerified` instances —
Law-VALUE unification with that machinery awaits Trait's public interface reveal). A law FALSE on
its sample is a fail-loud `checkLaws` error: unconstructible, the same teeth as `Trait.mkTested`. -/

/-- Reify a sample `Val` back to surface syntax (the v1 sample domain: ints + products of them). -/
def valToSurf : Val → Option Surf
  | .vint n   => some (.lit n)
  | .pair a b => do return .pairS (← valToSurf a) (← valToSurf b)
  | _         => none

/-- The sample pool for a value type — small on purpose (every element costs one interpreter
run per law). PUBLIC (#60 seam): the law-runner harness (`Bang.Witness.LawTest`) reuses this as
its Int/prod sample source rather than re-deriving one; no behavior change. -/
public def sampleVT : VT → List Val
  | .int      => [.vint 0, .vint 1, .vint (-2), .vint 7]
  | .prod A B => ((sampleVT A).flatMap fun a => (sampleVT B).map fun b => .pair a b).take 6
  | _         => []

/-- k-tuples over a pool (truncated cartesian power — a law's argument sample). -/
def tuples : Nat → List Val → List (List Val)
  | 0,     _    => [[]]
  | k + 1, pool => ((tuples k pool).flatMap fun t => pool.map fun v => v :: t).take 12

/-- Run ONE law instance: bind `params := args`, wrap the Bool-valued body in
`let #r = body in if #r then 1 else 0` (encoding-agnostic truth read-back), elaborate
(operators resolve), CHECK, lower, and run through `Source.eval`. PUBLIC (#60 seam): this is
the exact per-sample check the law-runner harness (`Bang.Witness.LawTest`) needs to reuse rather
than re-derive (build-on-checkLawOn-don't-rederive) — no behavior change, additive visibility
only. -/
public def checkLawOn (env : ElabEnv) (params : List String) (body : Surf) (args : List Val) : Bool :=
  if params.length != args.length then false else
  let wrapped := (params.zip args).foldr
    (fun (pv : String × Val) acc =>
      match valToSurf pv.2 with
      | some s => .lett pv.1 s acc
      | none   => acc)  -- unsupported sample value ⇒ unbound param ⇒ the check below fails loud
    (Surf.lett "#r" body (.ifS (.var "#r") (.lit 1) (.lit 0)))
  match (do
      let e ← elabS env [] wrapped
      let _ ← runInferC (synthSC [] e)
      Bang.Surface.lower e) with
  | .ok c    => match Source.eval 400 c with
                | .done (.vint 1) => true
                | _               => false
  | .error _ => false

/-- Check EVERY law of every trait against every impl of that trait, on a generated sample.
Returns the discharge report — one `↓ …` line per law, the `Trait.dischargeReport` shape, so
the tested-rung descent is VISIBLE (ADR-0068). A law false on its sample is a fail-loud error. -/
def checkLaws (src : String) : Except String (List String) := do
  let p ← parseProg src
  let env ← buildEnv p.decls
  let mut report : List String := []
  for d in p.decls do
    match d with
    | .implD .. => pure ()
    | .dataD .. => pure ()
    | .fnD ..   => pure ()
    | .effectD .. => pure ()   -- ADR-0092: no laws attached to an effect decl
    | .traitD tn _ _ laws =>
        for other in p.decls do
          match other with
          | .traitD .. => pure ()
          | .dataD ..  => pure ()
          | .fnD ..    => pure ()
          | .effectD .. => pure ()   -- ADR-0092: ditto
          | .implD tn' τTy _ =>
              if tn' == tn && !laws.isEmpty then                -- HK-trait laws are Stage D; Self-only path unchanged
                let τR ← resolveTy env.gen env.aliases τTy      -- named impl targets sample at the closed μ
                for l in laws do
                  let sample := tuples l.params.length (sampleVT (vtyOf τR))
                  if sample.all (checkLawOn env l.params l.body) then
                    report := report ++
                      [s!"↓ {tn}.{l.name} @ {showVTy (vtyOf τR)}: DESCENT [test ({sample.length} samples): source law — the ADR-0068 v1 ceiling] (tested)"]
                  else
                    throw s!"law {tn}.{l.name} FAILS on its sample for {showVTy (vtyOf τR)}"
  return report

/-! ### Validation ⑦ — the northstar WITH its law: checked from source, rung displayed. -/

/-- The full northstar prelude, parametrized by the law: `VecOps` (component-wise `add`, pair
`eq`) for `(Int * Int)`, in let-normal form (pair components are values in CBPV). -/
def vecOpsProg (law : String) (body : String) : String :=
  "trait VecOps { fn add(a, b) -> Self " ++
  "fn eq(a, b) -> (Unit + Unit) " ++
  "law " ++ law ++ " } " ++
  "impl VecOps for (Int * Int) { " ++
  "fn add(p, q) = let (a, b) = p in (let (c, d) = q in (let x = a + c in (let y = b + d in (x, y)))) " ++
  "fn eq(p, q) = let (a, b) = p in (let (c, d) = q in (let e = a == c in (if e then b == d else 0 == 1))) } " ++
  body

/-- The northstar program: the commutativity law + the pair instance. -/
def vecLawProg (body : String) : String :=
  vecOpsProg "comm(a, b): let s = a + b in (let t = b + a in s == t)" body

-- the comm law DISCHARGES on the tested rung — sample-checked via Source.eval, descent VISIBLE.
#guard (match checkLaws (vecLawProg "0") with
        | .ok [s] => s.startsWith "↓ VecOps.comm @ (Int * Int): DESCENT"
        | _       => false)
-- the value path is undisturbed: the lawful program still computes (1,2)+(3,4) = (4,6).
#guard runTypedYieldsInt 400 (vecLawProg "let s = (1, 2) + (3, 4) in (let (x, y) = s in x)") 4
#guard runTypedYieldsInt 400 (vecLawProg "let s = (1, 2) + (3, 4) in (let (x, y) = s in y)") 6
-- a FALSE law is UNCONSTRUCTIBLE: `a + b == a + a` fails its sample, fail-loud.
#guard (match checkLaws (vecOpsProg "bogus(a, b): let s = a + b in (let t = a + a in s == t)" "0") with
        | .error _ => true | _ => false)

/-! ### Validation ⑧ — CONDITIONAL laws (transitivity-shaped) are NOT blocked.

Implication `P → Q` encodes as `if P then Q else 0 == 0` (Bool-valued, so it is a legal law
body today); `law trans(a, b, c)` is a 3-param law sampled as k-tuples. The `=>` sugar and
premise-aware sampling (the truncated cartesian sample can leave a conditional law's premise
rarely true — vacuity) are ergonomics follow-ups, not blockers. -/

/-- An Int-target trait prelude, parametrized by the law (δ-rule ops carry the laws; the impl
exists so `checkLaws` has a trait×impl pair to instantiate). -/
def intOrdProg (law : String) (body : String) : String :=
  "trait IntOrd { fn lt(a, b) -> (Unit + Unit) law " ++ law ++ " } " ++
  "impl IntOrd for Int { fn lt(a, b) = a < b } " ++ body

-- TRANSITIVITY from source, READ AS WRITTEN (the `=>` sugar, #39): 3 params, k-tuple sampled. GREEN.
#guard (match checkLaws (intOrdProg "trans(a, b, c): a < b => b < c => a < c" "0") with
        | .ok [s] => s.startsWith "↓ IntOrd.trans"
        | _       => false)
-- symmetry of `==`, premise NON-vacuous (the sample's diagonal pairs exercise it). GREEN.
#guard (match checkLaws (intOrdProg "sym(a, b): a == b => b == a" "0") with
        | .ok [s] => s.startsWith "↓ IntOrd.sym"
        | _       => false)
-- the RAW if-encoding remains legal (what the sugar desugars to). GREEN.
#guard (match checkLaws (intOrdProg
    "transRaw(a, b, c): let p = a < b in (let q = b < c in (let r = a < c in (if p then (if q then r else 0 == 0) else 0 == 0)))" "0") with
        | .ok [s] => s.startsWith "↓ IntOrd.transRaw"
        | _       => false)
-- a FALSE conditional law is caught NON-vacuOUSLY: (a < b) => (b < a) fails on (0, 1). Fail-loud.
#guard (match checkLaws (intOrdProg "antisym_bogus(a, b): a < b => b < a" "0") with
        | .error _ => true | _ => false)

/-! ## Validation ⑨ — `data` declarations end-to-end (#2, ADR-0069).

Named constructors + named match, from source text, typed and run via the oracle. Recursive
FUNCTIONS stay out of scope (fix + Div, a separate bullet) — the demos construct and destruct. -/

def listProg (body : String) : String :=
  "data IntList = Nil | Cons(Int, IntList) " ++ body

-- construct + destruct a recursive value: head of Cons(7, Nil).
#guard runTypedYieldsInt 400 (listProg "let s = Cons(7, Nil) in match s { Nil -> 0, Cons(h, t) -> h }") 7
-- arms are order-independent (name-keyed, not positional).
#guard runTypedYieldsInt 400 (listProg "let s = Cons(7, Nil) in match s { Cons(h, t) -> h, Nil -> 0 }") 7
-- nested destructuring: the SECOND element of Cons(7, Cons(9, Nil)).
#guard runTypedYieldsInt 600 (listProg
  "let s = Cons(7, Cons(9, Nil)) in match s { Nil -> 0, Cons(h, t) -> match t { Nil -> h, Cons(h2, t2) -> h2 } }") 9
-- the data type DISPLAYS as its structural μ (transparent alias, ADR-0069 decision 3).
#guard displayProg (listProg "Cons(7, Nil)") == "(mu. (Unit + (Int * #0)))"
-- fail-loud: a missing arm · an unknown ctor · payload-arity mismatch at the type level.
#guard (match checkProg (listProg "let s = Nil in match s { Nil -> 0 }") with
        | .error _ => true | _ => false)
#guard (match checkProg (listProg "let s = Nil in match s { Nil -> 0, Snoc(h, t) -> h }") with
        | .error _ => true | _ => false)
#guard (match checkProg (listProg "Cons(7)") with | .error _ => true | _ => false)

/-! ### Validation ⑨b — HIGHER-ORDER constructor payloads (#45): a `Thunk (Int -> Int)` field.

The #45 gap: `checkSV` of a `.thunk` against a `.U` type SYNTHESIZED the thunk (failing on a bare
`fun`, which is check-mode only) instead of pushing the expected computation type IN. These type +
RUN the payload: build the `Box`, destruct it, FORCE the thunk, APPLY the function — the differential
proof that the pushed-in check-mode produced a runnable higher-order value the kernel oracle agrees on.
Before the fix these failed with `unbound variable b` (the `let`-RHS didn't type → the #41 cascade). -/
def boxProg (body : String) : String := "data Box = Box(Thunk (Int -> Int)) " ++ body
-- construct + destruct with a constant arm (the exact #45 reproduction): the RHS now types.
#guard runTypedYieldsInt 200 (boxProg "let b = Box({fun x => x}) in match b { Box(g) -> 7 }") 7
-- FORCE the thunked identity and APPLY it: `($g) 5` = 5.
#guard runTypedYieldsInt 200 (boxProg "let b = Box({fun x => x}) in match b { Box(g) -> ($g) 5 }") 5
-- a NON-identity payload proves the stored function is really run: `(fun x => x + 3) 5` = 8.
#guard runTypedYieldsInt 200 (boxProg "let b = Box({fun x => x + 3}) in match b { Box(g) -> ($g) 5 }") 8
-- the checkSC thunk arm (thunk in COMPUTATION position): an annotated thunk at top level, forced+applied.
#guard runTypedYieldsInt 200 "let f = ( {fun x => x + 1} : Thunk (Int -> Int) ) in ($f) 41" 42

/-! ### Validation ⑨c — μ-ENCODED RECURSION end-to-end (ADR-0073, gated on #45).

Landin's knot with NO new kernel primitive: `data Rec = Rec(Thunk (Rec -> Int -> Int))` (a negative
self-occurrence — `Rec` in its own field's domain) + self-application (`match self { Rec(g) -> ($g)
self … }`). The #45 check-mode fix is what lets the bare recursive `fun` payload type. A bounded
countdown-SUM `5+4+3+2+1+0 = 15` TYPES and RUNS under fuel — the ADR-0073 "μ-encoding, no new
primitive" mechanism, demonstrated. Spelled NATURALLY (`if n == 0 then …` directly, no manual `let c
= n == 0`): the #41 A-normalization now lifts the computation condition, closing the last ergonomic
gap between "recursion runs" and "recursion reads naturally". -/
def recProg : String :=
  "data Rec = Rec(Thunk (Rec -> Int -> Int)) " ++
  "let r = Rec({ ( fun self => ( fun n => " ++
  "(if n == 0 then 0 else (let m = n - 1 in (match self { Rec(g) -> let k = ($g) self m in n + k }))) " ++
  ": Int -> Int ) : Rec -> Int -> Int ) }) in "
#guard runTypedYieldsInt 4000 (recProg ++ "(match r { Rec(g) -> ($g) r 5 })") 15
#guard runTypedYieldsInt 4000 (recProg ++ "(match r { Rec(g) -> ($g) r 3 })") 6

/-! ### Validation ⑨e — `let rec` SURFACE SUGAR (ADR-0073 §1): recursion, user-spellable.

`let rec f : T = <fun> in <body>` desugars (in `elabS`) to the μ-knot above — `Rec = μX. Thunk(X -> T)`
+ Landin self-application — so users write recursion directly, never the raw fold/unfold. `f : Thunk T`
is in scope in its own body; call it `($f) arg`. Annotation-required + monomorphic (v1); NO new kernel
primitive (invariant #5). Spelled NATURALLY (the recursive-call arg `($f)(n-1)` is a computation, now
A-normalized like every other value position, #41). Div-row (ADR-0073 §2) is DEFERRED — see the ADR. -/
-- countdown-sum 5+4+3+2+1+0 = 15, the recursive call written `($sum)(n - 1)` (computation arg).
#guard runTypedYieldsInt 4000
  "let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in ($sum) 5" 15
-- factorial 5! = 120 (multiplicative recursion).
#guard runTypedYieldsInt 4000
  "let rec fac : Int -> Int = fun n => if n == 0 then 1 else n * ($fac)(n - 1) in ($fac) 5" 120
-- a let-BOUND recursive-call arg is equivalent (the pre-#41 spelling still works).
#guard runTypedYieldsInt 4000
  "let rec sum : Int -> Int = fun n => if n == 0 then 0 else (let m = n - 1 in n + ($sum) m) in ($sum) 3" 6
-- the desugar TYPES (checkProg ok); an UNBOUNDED recursion types too but ooms at runtime (the Div
-- fragment — fuel-bounded reference, ADR-0073 §4): it types but does NOT yield.
#guard (match checkProg
  "let rec loop : Int -> Int = fun n => ($loop)(n + 1) in ($loop) 0" with | .ok _ => true | _ => false)
#guard (runTypedYieldsInt 500
  "let rec loop : Int -> Int = fun n => ($loop)(n + 1) in ($loop) 0" 0) == false
-- non-function annotation fail-louds (the desugar needs a `fun` literal).
#guard (match checkProg "let rec x : Int = 5 in x" with | .error _ => true | _ => false)

/-! ### Validation ⑨f — `Div` is TYPE-VISIBLE (ADR-0073 §2, #46): recursion's partiality in the row.

A `let rec`'s CALL-SITE carries `{Div}` (the ADR-0028 total/`Div` seam, made type-visible; `Div` rides
the `U`/judgment per ADR-0019/0020, so `($f) x : … ! {Div}`). RUNTIME is unchanged — `divMark` erases
at lowering (the ⑨e `runTypedYieldsInt` guards above still yield 15/120/6). v1 seeds Div on the OUTER
call-site only (`letRecRow`'s documented under-approximation); #47 makes `letRecRow` conditional. -/
-- (a) a let rec's CALL-SITE row CONTAINS Div.
#guard (match checkProg "let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in ($sum) 5"
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- and DISPLAYS it — the partiality is legible in the type.
#guard displayProg "let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in ($sum) 5"
        == "Int ! {Div}"
-- (b) Div PROPAGATES — a continuation that BINDS-and-USES the recursive call inherits it (join over let).
#guard (match checkProg "let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in (let x = ($sum) 5 in x + 1)"
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- (c) a NON-recursive function's call stays ⊥ — Div is ONLY for `let rec`, not all functions.
#guard (match check "( fun x => x : Int -> Int ) 5" with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard (match check "let x = 3 in x + 1" with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
-- and a plain (non-rec) thunked function — same `Thunk (Int -> Int)` SHAPE as a `let rec`'s `f`, but
-- bound by a normal `let` — its call stays ⊥ (Div is the `let rec` marker, not the thunk shape).
#guard (match check "let f = ( {fun x => x + 1} : Thunk (Int -> Int) ) in ($f) 5" with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)

/-! ### Validation ⑨g — STRUCTURAL termination ELIMINATES Div (ADR-0073 §2 refinement, #47).

`structOK` certifies a `let rec` TOTAL (⊥-row, no Div) iff every recursive call descends on a strict
`data` subterm of the parameter. SOUNDNESS is the contract: a genuinely-partial function must NEVER be
certified. So the guards run BOTH ways — structural-on-`data` flips to ⊥ (and still RUNS identically),
while Int recursion + adversarial structural-LOOKING-but-diverging cases STAY Div. -/
def listRec (defn body : String) : String := "data List = Nil | Cons(Int, List) " ++ defn ++ " " ++ body
def lenDef : String := "let rec len : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> 1 + ($len) t } in"
def smDef  : String := "let rec sm : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> h + ($sm) t } in"
-- CERTIFIED TOTAL: structural recursion on the List tail `t` (a Cons field) ⟹ ⊥-row, no Div.
#guard (match checkProg (listRec lenDef "($len)(Cons(7, Cons(8, Cons(9, Nil))))") with
        | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard displayProg (listRec lenDef "($len)(Cons(7, Cons(8, Cons(9, Nil))))") == "Int"
#guard (match checkProg (listRec smDef "($sm)(Cons(1, Cons(2, Nil)))") with
        | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
-- and it STILL RUNS identically (⊥ vs Div is type-only): len [7,8,9] = 3, sm [1,2] = 3.
#guard runTypedYieldsInt 2000 (listRec lenDef "($len)(Cons(7, Cons(8, Cons(9, Nil))))") 3
#guard runTypedYieldsInt 2000 (listRec smDef  "($sm)(Cons(1, Cons(2, Nil)))") 3
-- TRANSITIVE descent certifies too: recurse on `t2`, a subterm of `t`, a subterm of `xs` (nested match)
-- — the second element, terminating, ⊥-row.
#guard (match checkProg (listRec
        "let rec sec : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> match t { Nil -> h, Cons(h2, t2) -> ($sec) t2 } } in"
        "($sec)(Cons(5, Cons(6, Nil)))") with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
-- mixed calls: ONE structural + ONE on the parameter → the whole function stays Div (ANY bad call taints).
#guard (match checkProg (listRec
        "let rec f : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> ($f) t + ($f) xs } in" "($f)(Cons(1, Nil))")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- adversarial ⑤ (Div/effect CALLEE — the audit's case): a STRUCTURAL `let rec` (so `letRecRow` returns
-- ⊥ for its OWN recursion) whose body CALLS a `Div` function `sum` is NOT silently typed total. The
-- structural ⊥ verdict does NOT strip the callee's Div — instead the μ-knot's recursive thunk must be
-- PURE (`recTy`'s `tThunk` ⟹ ⊥ bound), so a body carrying ANY latent effect (Div from `sum`, or throws
-- from `raise` — both reject identically) EXCEEDS the bound and is REJECTED at type-check ("thunk body
-- effect exceeds the declared bound"). SOUND: the diverging `f` is a TYPE ERROR, never a ⊥ verdict. This
-- rejection is the #45 fold-payload check, INDEPENDENT of #47's ⊥/Div choice (a `let rec`-body-purity
-- limit that predates #47); Div-PROPAGATION instead of rejection would need the deferred #46 Option B
-- machinery (a recursive thunk that carries effects). (`bang eval` still RUNS it — the untyped superset.)
#guard (match checkProg
        ("data List = Nil | Cons(Int, List) let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in " ++
         "(let rec f : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> ($sum) h + ($f) t } in ($f)(Cons(3, Nil)))")
        with | .error _ => true | _ => false)
-- SOUNDNESS — genuinely-partial functions are NOT certified (STAY Div):
-- Int countdown DIVERGES on negative n (unbounded ℤ, no floor, ADR-0067) — `n-1` is no data subterm.
#guard (match checkProg "let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in ($sum) 5"
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- adversarial ①: recurse on the RECONSTRUCTED value `Cons(h, t)` (= xs) — structural-LOOKING (matches a
-- Cons) but the arg is a ctor application, not a bound subterm var → diverges → MUST stay Div.
#guard (match checkProg (listRec
        "let rec f : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> ($f)(Cons(h, t)) } in" "($f)(Cons(1, Nil))")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- adversarial ②: recurse on the PARAMETER unchanged in a branch — not a strict subterm → stays Div.
#guard (match checkProg (listRec
        "let rec f : List -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> ($f) xs } in" "($f)(Cons(1, Nil))")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- adversarial ③: recurse on a field of a DIFFERENT (let-bound) value, not the matched parameter → Div.
#guard (match checkProg (listRec
        "let rec f : List -> Int = fun xs => (let zs = Cons(0, xs) in match zs { Nil -> 0, Cons(h, t) -> ($f) t }) in" "($f)(Cons(1, Nil))")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- adversarial ④ (SHADOWING): the recursion name `f` is RE-BOUND by an inner `let f` — so `($f) t` is
-- NOT the recursion, and the structural arg tells us nothing about it. If the inner `f` called a
-- diverging function the whole thing would diverge, so certifying would be UNSOUND → refuse (stay Div).
#guard (match checkProg (listRec
        "let rec f : List -> Int = fun xs => (let f = ( {fun ys => 0} : Thunk (List -> Int) ) in match xs { Nil -> 0, Cons(h, t) -> ($f) t }) in" "($f)(Cons(1, Nil))")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)

/-! ### Validation ⑨i — EFFECTFUL recursion via a DECLARED row (ADR-0088, #48).

`let rec f : T = …` may now declare a row on `T`'s codomain (`let rec f : Int -> Int ! {throws} = …`),
lifting adversarial ⑤'s rejection: the body is checked `φ_body ⊆ ρ` (the SAME `#45` thunk-row check
above, now generalized — `tyBoth`'s `tThunk`/`tArr` arms read `effOf` instead of hardcoding ⊥, D1) —
inner self-calls type at ρ too (D3), so a recursive `raise`/`get`/`put`/… is no longer a type error
when its row is declared. Absent `! {…}` stays ⊥ (D2 — every guard above this section is UNCHANGED
behavior, the backward-compatibility contract). -/
-- (a) the ADR's own repro: a recursive `raise`, declared `{throws}`, RUNS (caught by the enclosing
-- `handle`) instead of rejecting. `handle` must lexically enclose the WHOLE `let rec` (its cap binder
-- is scoped where installed, not where called — the state/8/design-doc convention).
#guard runTypedYieldsInt 4000
  "handle (let rec f : Int -> Int ! {throws} = fun n => if n == 0 then raise 99 else ($f)(n - 1) in ($f) 3)" 99
-- and the type DISPLAYS `Div` at the call-site (#46/#47: `n - 1` is not a data-subterm descent,
-- so `structOK` stays conservative and `Div` still shows — the declared `{throws}` and the
-- STRUCTURAL `Div` are ORTHOGONAL, exactly D3's claim; case (c) below shows the row WITHOUT Div
-- once the body genuinely IS structural).
#guard displayProg
  "handle (let rec f : Int -> Int ! {throws} = fun n => if n == 0 then raise 99 else ($f)(n - 1) in ($f) 3)"
  == "Int ! {Div}"
-- (b) a state-carrying recursion (a different effect than throws) — the accumulator threads through
-- the ambient `state` handler across recursive calls.
#guard runTypedYieldsInt 4000
  "state 0 in (let rec loop : Int -> Int ! {state} = fun n => if n == 0 then get else (let z = put (get + 1) in ($loop)(n - 1)) in ($loop) 3)"
  3
-- (c) structOK COMPOSES with a declared row (D3's headline claim): a STRUCTURALLY-terminating body
-- (recursion on the List tail `t`, certified total by #47) that ALSO performs a declared `{throws}`
-- types as EXACTLY `{throws}` — NOT `{throws, Div}` — because `structOK`'s ⊥ verdict for the
-- recursion's OWN termination still applies orthogonally; the row only adds the DECLARED effect.
#guard (match checkProg (listRec
        "let rec sm : List -> Int ! {throws} = fun xs => match xs { Nil -> 0, Cons(h, t) -> if h == 0 then raise 999 else h + ($sm) t } in"
        "($sm)(Cons(1, Cons(2, Nil)))")
        with | .ok (_, ρ) => divLabel ∉ ρ ∧ exnLabel ∈ ρ | _ => false)
#guard displayProg (listRec
        "let rec sm : List -> Int ! {throws} = fun xs => match xs { Nil -> 0, Cons(h, t) -> if h == 0 then raise 999 else h + ($sm) t } in"
        "($sm)(Cons(1, Cons(2, Nil)))")
        == "Int ! {throws}"
-- and it RUNS: catches the recursive raise on the zero element (999), same as the untyped shape.
-- `handle` must lexically enclose the WHOLE `let rec … in …` (its cap binder is scoped where
-- installed, not where called — the same rule case (a) documents; `raise`'s cap-lookup resolves
-- lexically through the `let rec` desugar's nested `#g`/self-knot binders, so a `handle` OUTSIDE
-- the `let rec` — even wrapping only the trailing call — cannot see it: `unbound variable: #exn`).
-- `data` decls are Prog-level only (never nest inside an expression, so `handle (…)` cannot wrap
-- `listRec`'s `data List = …` prelude) — written directly (not via `listRec`) so `handle (` opens
-- right where the BODY starts, after the decl, wrapping the whole `let rec … in …`.
#guard runTypedYieldsInt 2000
  ("data List = Nil | Cons(Int, List) handle (let rec sm : List -> Int ! {throws} = " ++
   "fun xs => match xs { Nil -> 0, Cons(h, t) -> if h == 0 then raise 999 else h + ($sm) t } in " ++
   "($sm)(Cons(1, Cons(0, Nil))))")
  999
-- (d) NEGATIVE — the adversarial ⑤ shape (a `let rec` body performing an UNDECLARED effect) still
-- REJECTS exactly as before ADR-0088 (D2's backward-compat contract): no `! {…}` ⟹ ρ = ∅, so a
-- `raise` in the body exceeds the (empty) declared bound.
#guard (match checkProg
  "let rec f : Int -> Int = fun n => if n == 0 then raise 99 else ($f)(n - 1) in handle (($f) 3)"
  with | .error _ => true | _ => false)
-- and the error NAMES the offending effect + the declared bound (agent-first: explicit, concise —
-- not a bare "exceeds the declared bound").
#guard (match checkProg
  "let rec f : Int -> Int = fun n => if n == 0 then raise 99 else ($f)(n - 1) in handle (($f) 3)"
  with | .error m => (m.splitOn "performs {throws}").length > 1 | _ => false)
-- (e) a DECLARED row that under-covers the body's REAL effects still rejects (the row is a checked
-- upper bound, not a trusted annotation) — declaring `{state}` does not license a `raise`.
#guard (match checkProg
  "let rec f : Int -> Int ! {state} = fun n => if n == 0 then raise 99 else ($f)(n - 1) in handle (($f) 3)"
  with | .error _ => true | _ => false)

/-! ### Validation ⑨j — MULTI-ARG / ACCUMULATOR structural descent (ADR-0091, #50).

`structOK` now certifies a CURRIED `let rec f = fun x1 => … => fun xn => body` or a single TUPLED
`let rec f = fun p => let (x1, x2) = p in body` as TOTAL (⊥-row) when ONE fixed slot index strictly
decreases on EVERY recursive call, with every other slot riding free (an accumulator). This is the
design note's (`docs/notes/structok-multiarg-design.md`) two motivating shapes, reconstructed exactly
from the tokenizer's AVOIDED naive form (`ce6d738`'s commit message) — pre-ADR-0091 both RAN correctly
but typed `Div`; this section proves both now certify `⊥` AND still run identically. -/
def listRecA (defn body : String) : String := "data L = LNil | LCons(Int, L) " ++ defn ++ " " ++ body
-- (a) the CURRIED accumulator shape: descent on slot 0 (`xs`), `acc` (slot 1) rides free.
def curriedAccDef : String :=
  "let rec sumAcc : L -> Int -> Int = fun xs => fun acc => " ++
  "match xs { LNil -> acc, LCons(h, t) -> ($sumAcc) t (acc + h) } in"
#guard (match checkProg (listRecA curriedAccDef "($sumAcc) (LCons(1, LCons(2, LCons(3, LNil)))) 0")
        with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard displayProg (listRecA curriedAccDef "($sumAcc) (LCons(1, LCons(2, LCons(3, LNil)))) 0") == "Int"
#guard runTypedYieldsInt 3000 (listRecA curriedAccDef "($sumAcc) (LCons(1, LCons(2, LCons(3, LNil)))) 0") 6
-- (b) the TUPLED accumulator shape: a single parameter `p`, split into `(xs, acc)`, same descent.
def tupleAccDef : String :=
  "let rec sumAccT : (L * Int) -> Int = fun p => let (xs, acc) = p in " ++
  "match xs { LNil -> acc, LCons(h, t) -> ($sumAccT) (t, acc + h) } in"
#guard (match checkProg (listRecA tupleAccDef "($sumAccT) (LCons(1, LCons(2, LCons(3, LNil))), 0)")
        with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard displayProg (listRecA tupleAccDef "($sumAccT) (LCons(1, LCons(2, LCons(3, LNil))), 0)") == "Int"
#guard runTypedYieldsInt 3000 (listRecA tupleAccDef "($sumAccT) (LCons(1, LCons(2, LCons(3, LNil))), 0)") 6
-- (c) NEGATIVE — certification must not LEAK through a non-structural callee (the design note's
-- own soundness check): a total `wrap` calling a GENUINELY `Div`-carrying curried helper (one that
-- recurses on its ACCUMULATOR, not the structural argument — `badAcc` below, deliberately NOT the
-- certified `sumAcc`, whose helper is now honestly total and so would not exercise the leak check)
-- WITHOUT itself declaring `{Div}` still REJECTS (`structOK` never certifies a call to a DIFFERENT
-- function's name as descending — it only checks for `name`-misuse there).
def badAccDef : String :=
  "let rec badAcc : L -> Int -> Int = fun xs => fun n => " ++
  "if n == 0 then 0 else ($badAcc) xs (n - 1) in"
#guard (match checkProg
  (listRecA (badAccDef ++
    " let rec wrap : L -> Int = fun xs => ($badAcc) xs 3 in") "($wrap) (LCons(1, LNil))")
  with | .error _ => true | _ => false)
-- and DECLARING `{Div}` on both makes the SAME shape run (no leak — the caller pays the honest cost).
#guard runTypedYieldsInt 3000
  (listRecA ("let rec badAcc : L -> Int -> Int ! {Div} = fun xs => fun n => " ++
    "if n == 0 then 0 else ($badAcc) xs (n - 1) in " ++
    "let rec wrap : L -> Int ! {Div} = fun xs => ($badAcc) xs 3 in") "($wrap) (LCons(1, LCons(2, LCons(3, LNil))))")
  0
-- (d) DEFAULT-DID-NOT-FLIP — at least one still-`Div` negative case, unrelated to the extension
-- (a curried fn recursing on the ACCUMULATOR instead of the structural argument — slot 1's `n`
-- decreases arithmetically, not structurally; slot 0's `xs` is UNCHANGED every call, so NEITHER
-- slot certifies — every `targetIdx` in the ADR-0091 search fails, correctly staying `Div`).
def curriedBadDef : String :=
  "let rec f : L -> Int -> Int = fun xs => fun n => " ++
  "if n == 0 then 0 else ($f) xs (n - 1) in"
#guard (match checkProg (listRecA curriedBadDef "($f) (LCons(1, LNil)) 3")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- ADVERSARIAL ①–④ PORTED to curried form (the design note's §3.3 obligation: every single-arg
-- adversarial guard needs a multi-arg analogue, since a fixed-slot search must reject each on its
-- OWN designated slot exactly as the single-arg checker did — a slot that fails structurally must
-- still fail when it is one of several, not be rescued by an unrelated free-riding accumulator).
-- ①: recurse on a RECONSTRUCTED value at the target slot — structural-LOOKING, not a bound subterm.
#guard (match checkProg (listRecA
        ("let rec f : L -> Int -> Int = fun xs => fun acc => " ++
         "match xs { LNil -> acc, LCons(h, t) -> ($f) (LCons(h, t)) acc } in")
        "($f) (LCons(1, LNil)) 0")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- ②: recurse on the target-slot PARAMETER unchanged in a branch — not a strict subterm.
#guard (match checkProg (listRecA
        ("let rec f : L -> Int -> Int = fun xs => fun acc => " ++
         "match xs { LNil -> acc, LCons(h, t) -> ($f) xs acc } in")
        "($f) (LCons(1, LNil)) 0")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- ③: recurse on a field of a DIFFERENT (let-bound) value at the target slot, not the matched param.
#guard (match checkProg (listRecA
        ("let rec f : L -> Int -> Int = fun xs => fun acc => " ++
         "(let zs = LCons(0, xs) in match zs { LNil -> acc, LCons(h, t) -> ($f) t acc }) in")
        "($f) (LCons(1, LNil)) 0")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- ④ (SHADOWING): the recursion name `f` is RE-BOUND by an inner `let f` — the structural arg at
-- either slot tells us nothing about the shadowed reference, so BOTH slots must refuse.
#guard (match checkProg (listRecA
        ("let rec f : L -> Int -> Int = fun xs => fun acc => " ++
         "(let f = ( {fun ys => fun a => 0} : Thunk (L -> Int -> Int) ) in " ++
         "match xs { LNil -> acc, LCons(h, t) -> ($f) t acc }) in")
        "($f) (LCons(1, LNil)) 0")
        with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- ⑤ PORTED: a curried STRUCTURAL `let rec` (slot 0 certifiably descends) whose body CALLS a `Div`
-- helper is still REJECTED, not silently stripped of the callee's Div (the #45 fold-payload check,
-- independent of the ⊥/Div choice — same as the single-arg ⑤ above, now through a 2-slot function).
#guard (match checkProg
        ("data L = LNil | LCons(Int, L) let rec sum : Int -> Int = fun n => if n == 0 then 0 else n + ($sum)(n - 1) in " ++
         "(let rec f : L -> Int -> Int = fun xs => fun acc => " ++
         "match xs { LNil -> acc, LCons(h, t) -> ($f) t (acc + ($sum) h) } in ($f) (LCons(3, LNil)) 0)")
        with | .error _ => true | _ => false)
-- arity mismatch — a call with the WRONG number of arguments never certifies (defensive: the
-- elaborator's own type-checking would catch a genuine arity error long before `structOK` runs,
-- but `structOK`'s own arity guard, `callSpine`'s recognized-length ≠ `slots.length`, must reject
-- rather than crash/miscompare — this asserts that guard fires, not merely that SOME error surfaces).
#guard (match checkProg (listRecA
        ("let rec f : L -> Int -> Int = fun xs => fun acc => " ++
         "match xs { LNil -> acc, LCons(h, t) -> ($f) t } in")
        "($f) (LCons(1, LNil)) 0")
        with | .error _ => true | _ => false)

/-! ### Validation ⑨h — STRINGS: `String = List Char` (ADR-0074, #49).

`Char = Char(Int)` (a code point) + `Str = SNil | SCons(Char, Str)` are an INJECTED built-in prelude
(`strPrelude`); string literals `"hi"` desugar (in `pAtom`) to `SCons(Char 104, …)` and char literals
`'a'` to `Char 97`. `length` is a `let rec` structural fold over `Str` → #47-certified TOTAL (`Div ∉ ρ`
— strings are total). All LIBRARY over `data` + `Int` — NO kernel primitive (invariant #5). -/
def lengthDef : String :=
  "let rec length : Str -> Int = fun s => match s { SNil -> 0, SCons(c, rest) -> 1 + ($length) rest } in "
-- `length` runs over a string literal: "abc" → 3, "" → 0.
#guard runTypedYieldsInt 3000 (lengthDef ++ "($length) \"abc\"") 3
#guard runTypedYieldsInt 3000 (lengthDef ++ "($length) \"\"") 0
-- escapes are decoded: "a\nb\tc" is FIVE code points (a · newline · b · tab · c), not seven chars.
#guard runTypedYieldsInt 3000 (lengthDef ++ "($length) \"a\\nb\\tc\"") 5
-- THE #47 PAYOFF: `length` over `Str` is structural recursion on the char-list ⟹ certified TOTAL, Div ∉ ρ.
#guard (match checkProg (lengthDef ++ "($length) \"abc\"") with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
-- a char literal `'a'` is `Char 97`; destructuring recovers the code point.
#guard runTypedYieldsInt 100 "match 'a' { Char(n) -> n }" 97
#guard runTypedYieldsInt 100 "match '\\n' { Char(n) -> n }" 10   -- '\n' = code point 10
-- a string literal TYPES as the `Str` data type (its structural μ), decl-free (the prelude is injected).
#guard (match checkProg "\"hi\"" with | .ok _ => true | _ => false)

/-! ### Validation ⑨h′ — the STRING STDLIB: `concat`/`reverse`/`eq` injected FREE (#49 stage 3, #50).

`concat`/`reverse`/`eq` are `let rec` folds injected in scope of EVERY program (`stdlibFnSrcs`,
`injectStdlib`), so a program uses them WITHOUT re-inlining (the #50 gap the tokenizer hit). Pre-
ADR-0091, ALL were `Div`-typed (curried `let rec` — the old #47 multi-arg gap; they terminate, the
old single-slot certifier couldn't prove it). ADR-0091's single-fixed-slot descent now CERTIFIES
`concat`/`eq` as TOTAL directly (`⊥`-row, `Div ∉ ρ`) — this is #47's own stated contract working as
designed ("Div should mean couldn't prove termination, not is recursive"), not a regression: both
match their FIRST curried param (`a`/`a`) and recurse on its strict subterm (`t`) at that SAME slot
on every call, with the second param (`b`) riding free — EXACTLY ADR-0091's motivating shape. This
flips the pre-ADR-0091 guard below from `divLabel ∈ ρ` to `divLabel ∉ ρ` (see the falsification note
there).

`reverse` STAYS `Div` (unchanged, confirmed by re-testing after the extension) — its internal
`revApp` needs a `(s : Str)` SCRUTINEE ASCRIPTION on its match (a pre-existing, SEPARATE gap: a
curried param past the first isn't otherwise propagated into elaboration-time match resolution,
issue #50 point 3 — without it `revApp` doesn't elaborate AT ALL, "match scrutinee is #…, not
Str"). `scrutMatch` (this file) only recognizes a BARE `.var` scrutinee, not an `.annotS`-wrapped
one, so the ascribed `match (s : Str) { … }` never re-adds `c`/`t` as slot-1 subterms — `structOK`
correctly stays conservative (`false`) rather than guess through the ascription. This is a genuine,
separate limitation (`scrutMatch` seeing through `.annotS` is a small, orthogonal, clearly-sound
follow-up — an ascription never changes WHAT the scrutinee is) that ADR-0091 does not claim to
close; `reverse` staying `Div` here is the CORRECT conservative verdict, not a bug in this unit. -/
-- `concat "ab" "cd"` runs → a real 4-char string (asserted via a locally-defined `length`).
#guard runTypedYieldsInt 3000 (lengthDef ++ "($length) (($concat) \"ab\" \"cd\")") 4
#guard runTypedYieldsInt 3000 (lengthDef ++ "($length) (($concat) \"\" \"cd\")") 2
-- `reverse "abc"` runs (length preserved) AND reverses (its FIRST char is 'c' = code point 99).
#guard runTypedYieldsInt 5000 (lengthDef ++ "($length) (($reverse) \"abc\")") 3
#guard runTypedYieldsInt 5000 "match (($reverse) \"abc\") { SNil -> 0, SCons(c, t) -> match c { Char(n) -> n } }" 99
-- `eq` char-by-char: equal strings → true (then-branch), unequal (content OR length) → false.
#guard runTypedYieldsInt 3000 "if (($eq) \"ab\" \"ab\") then 1 else 0" 1
#guard runTypedYieldsInt 3000 "if (($eq) \"ab\" \"ba\") then 1 else 0" 0
#guard runTypedYieldsInt 3000 "if (($eq) \"a\" \"ab\") then 1 else 0" 0
#guard runTypedYieldsInt 3000 "if (($eq) \"\" \"\") then 1 else 0" 1
-- ADR-0091: USING `concat` no longer forces `Div` — the checker now certifies its curried-accumulator
-- shape directly (slot 0 descends on `a`'s strict subterm `t`; slot 1's `b` rides free every call).
-- FALSIFIED (documented, not asserted here — see the multi-arg regression corpus below for the
-- load-bearing falsification pass): reverting the `structOK`/`letRecRow` extension makes this assert
-- `divLabel ∈ ρ` again (the pre-ADR-0091 behavior) — this guard is the exact site that pins the
-- new, more-precise verdict; a future regression here is a FINDING (the certifier got LESS precise).
#guard (match checkProg "($concat) \"ab\" \"cd\"" with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard (match checkProg "($eq) \"ab\" \"cd\"" with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
-- `reverse` stays Div (the scrutinee-ascription gap above) — a genuine, documented remaining
-- conservatism, not a soundness bug: it terminates, still runs correctly (guards above), the
-- certifier just can't SEE it through the ascription this unit does not touch.
#guard (match checkProg "($reverse) \"ab\"" with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- THE INERT PROOF: a program that does NOT use the stdlib is UNAFFECTED — its row has NO `Div`, and a
-- pure `Int` program still types pure (the injected `let rec`s are dead-but-harmless, like the unused
-- `Char`/`Str` ctors). This is what guarantees the existing corpus is unchanged.
#guard (match checkProg "3" with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard runTypedYieldsInt 100 "3" 3
#guard (match checkProg (lengthDef ++ "($length) \"abc\"") with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)

/-! ### Validation ⑨i — the DOGFOOD: a TOKENIZER written IN BANG (#49 stage 5, "bang writes its own
tools"). `tokenize : Str -> TokList` splits a string on spaces, structurally recursing on the char-list
tail (a subterm) and building tokens RIGHT-TO-LEFT — a space starts a fresh empty head token, a
non-space is CONSed onto the head token of the recursive result (so tokens come out in order, no
reverse needed). Structural ⟹ #47-certified TOTAL. All `let rec` folds over `data`, riding strings —
NO kernel change. Edge policy: split-on-EVERY-space, so leading/trailing/consecutive spaces yield
empty tokens (documented, not hidden; a `filter`-empties pass is stage-3 stdlib). -/
def tokDefs : String :=
  "data TokList = TNil | TCons(Str, TokList) " ++
  "let rec tokenize : Str -> TokList = fun s => match s { SNil -> TCons(SNil, TNil), " ++
  "SCons(c, rest) -> if (match c { Char(n) -> n == 32 }) then TCons(SNil, ($tokenize) rest) " ++
  "else (match (($tokenize) rest) { TNil -> TCons(SCons(c, SNil), TNil), TCons(w, more) -> TCons(SCons(c, w), more) }) } in " ++
  "let rec tokCount : TokList -> Int = fun tl => match tl { TNil -> 0, TCons(w, rest) -> 1 + ($tokCount) rest } in " ++
  "let rec length : Str -> Int = fun s => match s { SNil -> 0, SCons(c, r) -> 1 + ($length) r } in "
-- THE DOGFOOD RUNS: "ab cd ef" (3 words) → 3 tokens; a single word → 1; empty → 1 (one empty token).
#guard runTypedYieldsInt 5000 (tokDefs ++ "($tokCount) (($tokenize) \"ab cd ef\")") 3
#guard runTypedYieldsInt 5000 (tokDefs ++ "($tokCount) (($tokenize) \"abc\")") 1
#guard runTypedYieldsInt 5000 (tokDefs ++ "($tokCount) (($tokenize) \"\")") 1
-- edge (documented): a TRAILING space yields a trailing empty token (split-on-every-space) → 2.
#guard runTypedYieldsInt 5000 (tokDefs ++ "($tokCount) (($tokenize) \"ab \")") 2
-- token CONTENT is a real string: the FIRST token of "hi there" is "hi" (length 2), the SECOND "there" (5).
#guard runTypedYieldsInt 5000 (tokDefs ++ "let toks = ($tokenize) \"hi there\" in (match toks { TNil -> 0, TCons(w, rest) -> ($length) w })") 2
#guard runTypedYieldsInt 5000 (tokDefs ++ "let toks = ($tokenize) \"hi there\" in (match toks { TNil -> 0, TCons(w, rest) -> match rest { TNil -> 0, TCons(w2, more) -> ($length) w2 } })") 5
-- THE #47 PAYOFF: the whole tokenizer pipeline is STRUCTURAL ⟹ certified TOTAL, Div ∉ ρ (strings are total).
#guard (match checkProg (tokDefs ++ "($tokenize) \"ab cd\"") with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)
#guard (match checkProg (tokDefs ++ "($tokCount) (($tokenize) \"ab cd\")") with | .ok (_, ρ) => divLabel ∉ ρ | _ => false)

/-! ### The northstar, in its INTENDED spelling: `Vec` as a NAMED type (ADR-0069 consequence). -/

def vecDataProg (body : String) : String :=
  "data Vec = Vec(Int, Int) " ++
  "trait Add { fn add(a, b) -> Self } " ++
  "impl Add for Vec { fn add(p, q) = " ++
  "match p { Vec(a, b) -> match q { Vec(c, d) -> " ++
  "let x = a + c in (let y = b + d in Vec(x, y)) } } } " ++
  body

-- Vec(1,2) + Vec(3,4) = Vec(4,6) — named ctor intro, resolution through the NAMED impl target,
-- ctor intro INSIDE the impl body (env-build pre-elaboration), named match to project.
#guard runTypedYieldsInt 800 (vecDataProg
  "let v = Vec(1, 2) + Vec(3, 4) in match v { Vec(x, y) -> x }") 4
#guard runTypedYieldsInt 800 (vecDataProg
  "let v = Vec(1, 2) + Vec(3, 4) in match v { Vec(x, y) -> y }") 6

/-! ### Validation ⑨d — VALUE-POSITION A-normalization (#41): computations spelled NATURALLY.

The typed path now A-normalizes computations in value positions (ctor args, match scrutinees, binop
operands, `if` conditions) exactly as `Surface.lower` already does — the checker accepts what the
oracle runs. Each of these FAILED before (`not a value` / a misleading `unbound variable`); now they
type + run. The impl body writes `Vec(a + c, b + d)` DIRECTLY (no `let x = a+c in …` workaround). -/
def vecNatProg (body : String) : String :=
  "data Vec = Vec(Int, Int) trait Add { fn add(a, b) -> Self } " ++
  "impl Add for Vec { fn add(p, q) = match p { Vec(a, b) -> match q { Vec(c, d) -> " ++
  "Vec(a + c, b + d) } } } " ++ body
-- computation in a ctor ARG: `Vec(a + c, b + d)` types (was "not a value" → "unbound v" cascade).
#guard runTypedYieldsInt 800 (vecNatProg "let v = Vec(1, 2) + Vec(3, 4) in match v { Vec(x, y) -> x }") 4
#guard runTypedYieldsInt 800 (vecNatProg "let v = Vec(1, 2) + Vec(3, 4) in match v { Vec(x, y) -> y }") 6
-- computation as a match SCRUTINEE: `match (Vec(1,2) + Vec(3,4)) { … }` (was "not a value").
#guard runTypedYieldsInt 800 (vecNatProg "match (Vec(1, 2) + Vec(3, 4)) { Vec(x, y) -> x }") 4
-- CHAINED trait op `(V+V)+V` — a computation operand of `+`, A-normalized before impl dispatch.
#guard runTypedYieldsInt 900 (vecNatProg
  "let v = Vec(1, 2) + Vec(3, 4) + Vec(10, 20) in match v { Vec(x, y) -> x }") 14
-- NESTED arithmetic in a ctor arg: `a + c + 1` (a binop with a binop operand).
#guard runTypedYieldsInt 900
  ("data Vec = Vec(Int, Int) trait Add { fn add(a, b) -> Self } " ++
   "impl Add for Vec { fn add(p, q) = match p { Vec(a, b) -> match q { Vec(c, d) -> " ++
   "Vec(a + c + 1, b + d) } } } let v = Vec(1, 2) + Vec(3, 4) in match v { Vec(x, y) -> x }") 5
-- computation as a SPLIT scrutinee: `let (x, y) = (Vec-ish product computation) in …`. Here the pair
-- `(1 + 0, 2 + 0)` is a bare computation-product destructured directly (was "not a value").
#guard runTypedYieldsInt 200 "let (x, y) = (1 + 0, 2 + 0) in x + y" 3
-- the DIAGNOSTIC (#41 part 2, in the elaborator → `checkProg`): a let-RHS type error surfaces AS the
-- RHS error, not a downstream "unbound m".
#guard (match checkProg "let m = 1 + Left(0) in m" with
        | .error e => e.startsWith "let-binding 'm':" | _ => false)
-- a non-returner RHS (a bare function bound directly) reports "not a returner", not "unbound f".
#guard (match checkProg "let f = ( fun x => x : Int -> Int ) in 0" with
        | .error e => e.startsWith "let-binding 'f':" | _ => false)

/-! ## Validation ⑩ — named capabilities are TYPED (#3, ADR-0070).

`state <init> as h` (and `handle as h` / `atomically as h`, ADR-0072) binds `h : Cap ℓ`; `h.op`
performs (adding ℓ to the row); the handler discharges ℓ. The checker rejects a label mismatch or a
non-cap receiver. Both the ambient and named forms are identity-dispatched; the type just now names
the cap. -/
-- a handled named-state program is pure (the `as h` binder's handler discharges {state}).
#guard check "state 5 as h in h.get" == .ok (.F .omega .int, ⊥)
#guard display "state 5 as h in h.get" == "Int"
-- the TWO-CELL demo type-checks AND runs to 3 (typed path) — ambient can't express it.
#guard runTypedYieldsInt 90 "state 1 as a in (state 2 as b in (let x = a.get in (let y = b.get in x + y)))" 3
-- put on a named cap, then get, still discharged.
#guard runTypedYieldsInt 60 "state 5 as h in (let z = h.put(7) in h.get)" 7
-- a named transaction cap, fully handled.
#guard displayProg "atomically as t (let r = t.new(100) in (let z = t.write(r, 70) in t.read(r)))" == "Int"

-- REJECTIONS — the cap checker is sound:
-- label mismatch: a state cap has no `raise`.
#guard (match check "state 5 as h in h.raise(9)" with | .error _ => true | _ => false)
-- non-cap receiver: an Int is not a capability.
#guard (match check "let x = 3 in x.get" with | .error _ => true | _ => false)
-- wrong arg type: put expects Int, given a sum.
#guard (match check "state 5 as h in h.put(Left(0))" with | .error _ => true | _ => false)
-- unknown op on a valid cap.
#guard (match check "state 5 as h in h.frobnicate" with | .error _ => true | _ => false)

/-! ## Validation ⑦b — HM polymorphism RUNS end-to-end (ADR-0075 bite-0, the real pipeline).

`runTypedYieldsInt` = parse → elaborate → CHECK (the HM checker) → lower → `Source.eval`. So these
guards prove the polymorphism PAYOFF through the SAME path `bang eval` uses — one `let`-bound generic
definition, used at multiple types, checked and run to a value. (Defined here, after
`runTypedYieldsInt` — the `check`-level typing guards are Validation ⑦ above.) -/
-- id at Int AND (Int * Int): 5 + 1 = 6.
#guard runTypedYieldsInt 200 killerId 6
-- id at Int and Unit (independent instantiations): 5.
#guard runTypedYieldsInt 200 "let id = {fun x => x} in (let a = ($id) 5 in (let u = ($id) () in a))" 5
-- const at Int-arg and (Int*Int)-arg: 5 + 7 = 12.
#guard runTypedYieldsInt 200 killerConst 12
-- ANNOTATED higher-order `compose` — TYPES + RUNS. The ascription binds EVERY curried param
-- (`curryBind`), so `anfSplit` inside the nested `fun g`/`fun x` can synthesize the computation
-- argument `($g) x` (previously a fail-loud "unbound variable g" at elaboration). `inc ∘ dbl` at 5 =
-- inc(dbl(5)) = inc(10) = 11. `($f)`/`($g)` force CONCRETE thunks, so no computation hole is needed —
-- annotation-checked monomorphic higher-order (the inferred/HM higher-order tier is the ICTy follow-on).
def composeAnnSrc := "let c = { ( fun f => fun g => fun x => ($f)(($g) x) : Thunk (Int -> Int) -> Thunk (Int -> Int) -> Int -> Int ) } in let inc = {fun x => x + 1} in let dbl = {fun x => x + x} in ((($c) inc) dbl) 5"
#guard displayProg composeAnnSrc == "Int"
#guard runTypedYieldsInt 500 composeAnnSrc 11
-- ⭐ HM-INFERRED (UNANNOTATED) higher-order `compose` — the ICTy re-rep payoff (bite-0b). Bare
-- `fun f => fun g => fun x => ($f)(($g) x)`: `force` a value-hole unifies it with `U ⊥ (chole)`, `app`
-- a chole callee unifies it with `arr`, `anfSplit`/`let` treat a chole result as a returner (`expectF` →
-- `F ω ?`), and `generalize` DEFAULTS the dangling result chole to `F ω ?` so it quantifies — bare
-- compose now TYPES (bite-0 threw "annotate (higher-order is bite-0b)" right here). PURE-thunk functions
-- only (the `⊥` row; effect-row-poly is item 3).
#guard (match checkProg "let compose = {fun f => fun g => fun x => ($f) (($g) x)} in 0" with | .ok _ => true | _ => false)
-- RUNS: `inc ∘ dbl` at 5 = inc(dbl 5) = inc 10 = 11 — bare compose, no annotation, through `bang eval`.
def composeBareSrc := "let compose = {fun f => fun g => fun x => ($f)(($g) x)} in let inc = {fun x => x + 1} in let dbl = {fun x => x + x} in ((($compose) inc) dbl) 5"
#guard displayProg composeBareSrc == "Int"
#guard runTypedYieldsInt 500 composeBareSrc 11
-- POLYMORPHIC at TWO types in ONE program: `inc ∘ dbl` (middle type Int) AND `fromU ∘ toU` (middle type
-- Unit) — ONE bare `compose`, two instantiations. Without generalizing the result (the chole default),
-- the second use would CLASH on the shared computation hole. 11 + 3 = 14 — the polymorphism proof.
def composeTwoSrc := "let compose = {fun f => fun g => fun x => ($f)(($g) x)} in let inc = {fun x => x + 1} in let dbl = {fun x => x + x} in let toU = {fun x => ()} in let fromU = {fun u => 3} in let r1 = ((($compose) inc) dbl) 5 in let r2 = ((($compose) fromU) toU) 9 in r1 + r2"
#guard (match checkProg composeTwoSrc with | .ok _ => true | _ => false)
#guard runTypedYieldsInt 800 composeTwoSrc 14

/-! ### EFFECT ROW-POLYMORPHISM (ADR-0075 bite-0b item 3) — ONE `compose`, generic over its effect row.
`compose : ∀ρ. (b→c!ρ)→(a→b!ρ)→(a→c!ρ)` (the effect analog of the type-poly two-instance demos). It's
used at TWO rows in ONE program — pure `⊥` (`inc∘dbl`) AND a non-`⊥` `{Div}` row (`countdown∘countdown`,
a `let rec` the termination checker can't certify, ADR-0073) — and RUNS. The row var is `let`-GENERALIZED
(kernel `EffRow` UNTOUCHED; the poly lives in the parallel inference `Row`), so each use instantiates a
FRESH ρ: `r1` pins ρ:=⊥, `r2` pins ρ:={Div}, and they COEXIST — that coexistence IS the row polymorphism
(without generalizing ρ, `r1`'s ⊥ would clash with `r2`'s {Div} on a shared tail). -/
def rowPolyDivSrc := "let rec countdown : Int -> Int = fun n => if n < 1 then 7 else ($countdown)(n - 1) in let compose = {fun p => fun q => fun x => ($p)(($q) x)} in let inc = {fun x => x + 1} in let dbl = {fun x => x + x} in let r1 = ((($compose) inc) dbl) 5 in let r2 = ((($compose) countdown) countdown) 3 in r1 + r2"
-- TYPES, and the program's row carries {Div} (the non-⊥ instantiation is real, not erased to ⊥).
#guard displayProg rowPolyDivSrc == "Int ! {Div}"
#guard (match checkProg rowPolyDivSrc with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- ⭐ RUNS: inc∘dbl at 5 = 11 (ρ=⊥), countdown∘countdown at 3 = 7 (ρ={Div}), 11 + 7 = 18 — the effectful
-- instantiation RUNS (countdown terminates; {Div} = "unproven termination", not a real effect to handle).
#guard runTypedYieldsInt 3000 rowPolyDivSrc 18
-- FINDING (single-ρ first cut): the body-join COLLAPSES ρp,ρq to one shared row var, so `compose` demands
-- its two functions be at the SAME row. Mixing a PURE (⊥) and an EFFECTFUL ({Div}) fn — the task's literal
-- `compose incPure <effectful>` — FAILS loud ("effect row mismatch"). It needs subeffecting (⊥⊆ρ) or
-- independent tails + a real join (full Rémy) — the deferred refinement. Sound (over-approximates), incomplete.
#guard (match checkProg "let rec cd : Int -> Int = fun n => if n < 1 then 7 else ($cd)(n - 1) in let compose = {fun p => fun q => fun x => ($p)(($q) x)} in let inc = {fun x => x + 1} in ((($compose) inc) cd) 3" with | .error _ => true | .ok _ => false)

-- #53 — bare anonymous injections RUN end-to-end through the typed default path (CHECK precedes eval).
#guard runTypedYieldsInt 20 "match Right(7) { Left(a) -> 0, Right(x) -> x }" 7
#guard runTypedYieldsInt 20 "let x = Right(7) in match x { Left(a) -> 0, Right(x) -> x }" 7
#guard runTypedYieldsInt 20 "match Left(3) { Left(a) -> a, Right(x) -> x }" 3

/-! ### GENERIC data types (ADR-0069 bite-1) — `data List a` monomorphized per concrete instantiation.
The kernel only ever sees the closed μ (`List Int` ↦ `μX. Unit + (Int × X)`); a generic ctor elaborates
to a BARE `fold` whose element type an enclosing annotation drives (elaborate-to-mono, kernel untouched). -/

-- ⭐ The keystone: `data List a` PARSES, and a `List Int` program TYPES + RUNS via `bang eval`.
-- `length` over `Cons(1, Cons(2, Cons(3, Nil))) : List Int` = 3. The `: List Int` annotation drives the
-- concrete μ through the nested bare folds; `length`'s match binders (`h : Int`, `t : List Int`) are
-- typed by the checker from the unrolled scrutinee.
def genListLen :=
  "data List a = Nil | Cons(a, List a) " ++
  "let rec length : List Int -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> 1 + ($length) t } in " ++
  "($length) (Cons(1, Cons(2, Cons(3, Nil))) : List Int)"
#guard runTypedYieldsInt 2000 genListLen 3

-- `sum` uses the ELEMENT binder `h : Int` (not just the tail) — proves the checker types the payload
-- field from the concrete instantiation. 10 + 20 + 5 = 35.
def genListSum :=
  "data List a = Nil | Cons(a, List a) " ++
  "let rec sum : List Int -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> h + ($sum) t } in " ++
  "($sum) (Cons(10, Cons(20, Cons(5, Nil))) : List Int)"
#guard runTypedYieldsInt 2000 genListSum 35

-- ⭐ POLYMORPHIC data: the SAME `data List a` decl at TWO distinct element types in ONE program —
-- `List Int` AND `List (Int * Int)`, each with its own monomorphic consumer. 2 + 1 = 3. Proves the
-- decl is generic (not a single monomorphized instance).
def genListTwoTypes :=
  "data List a = Nil | Cons(a, List a) " ++
  "let rec lenI : List Int -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> 1 + ($lenI) t } in " ++
  "let rec lenP : List (Int * Int) -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> 1 + ($lenP) t } in " ++
  "let a = ($lenI) (Cons(1, Cons(2, Nil)) : List Int) in " ++
  "let b = ($lenP) (Cons((7, 8), Nil) : List (Int * Int)) in a + b"
#guard runTypedYieldsInt 3000 genListTwoTypes 3

-- A GENERIC type with TWO params: `data Pair a b = P(a, b)` at `Pair Int (Int * Int)`, projected.
def genPair :=
  "data Pair a b = P(a, b) " ++
  "let p = (P(4, (1, 2)) : Pair Int (Int * Int)) in match p { P(x, y) -> let (m, n) = y in x + m + n }"
#guard runTypedYieldsInt 800 genPair 7

-- ⭐ ANNOTATION-FREE generic introduction (ADR-0079 follow-on, #55): a bare `Cons(1, Nil)` in SYNTH
-- position now TYPES + RUNS — the instantiation `a := Int` is INFERRED from the field `1 : Int` (the
-- element type flows into the template μ's marker-hole; the nested `Nil` is driven to `List Int` by the
-- solved μ). No `: List Int` annotation. Consumed by a `match` to yield an Int the run-oracle can check.
#guard runTypedYieldsInt 800 "data List a = Nil | Cons(a, List a) match (Cons(7, Nil)) { Nil -> 0, Cons(h, t) -> h }" 7
-- `Some(x)` where `x : Int` ⟹ `Option Int`, no annotation; destructured to its payload.
#guard runTypedYieldsInt 400 "data Option a = None | Some(a) match (Some(5)) { None -> 0, Some(v) -> v }" 5
-- annotation-free is ADDITIVE: the SAME decl still accepts an explicit `: List Int` (ADR-0079 check-mode).
#guard runTypedYieldsInt 800 "data List a = Nil | Cons(a, List a) match (Cons(7, Nil) : List Int) { Nil -> 0, Cons(h, t) -> h }" 7
-- the inference is TWO-LEVEL: the element type is itself a generic instantiation — `Cons(1, Nil)` as the
-- head of `Cons(Cons(1,Nil), Nil)`, all annotation-free (the `let rec`'s sig fixes only the OUTER `List
-- (List Int)`; the inner `Cons(1,Nil)` infers `List Int` from its own field). length-of-outer = 1.
#guard runTypedYieldsInt 1500 ("data List a = Nil | Cons(a, List a) " ++
  "let rec len : List (List Int) -> Int = fun xs => match xs { Nil -> 0, Cons(h, t) -> 1 + ($len) t } in " ++
  "($len) (Cons(Cons(1, Nil), Nil))") 1

-- ⭐ THE PARSER-LIBRARY PAYOFF (#55 walls 2+3): a GENERIC combinator that CONSTRUCTS generic data.
-- `omap : (a->b) -> Option a -> Option b` matches a generic value AND rebuilds `Some(($f) x)` — the ONE
-- definition, no annotation. The scrutinee's `Option` structure is recovered from the arm ctors (`None`/
-- `Some` ⟹ `Option`) and unified onto the higher-order `o`. Used here at `a := Int, b := Int` ⟹ 5.
#guard runTypedYieldsInt 800
  ("data Option a = None | Some(a) " ++
   "let omap = { fun f => fun o => match o { None -> None, Some(x) -> Some(($f) x) } } in " ++
   "match (($omap) {fun z => z + 1} (Some(4))) { None -> 0, Some(v) -> v }") 5
-- MATCH THROUGH A HIGHER-ORDER PARSER + a generic PRODUCT split (wall 3): a `mapP` matching `($p) s`,
-- splitting the generic element `r` into `(v, rest)`, rebuilding `Some((w, rest))` — all annotation-free.
-- `mapP {+10} {s ↦ Some((7,s))} "x"` ⟹ Some((17, "x")); firstVal ⟹ 17.
#guard runTypedYieldsInt 1200
  ("data Option a = None | Some(a) " ++
   "let mapP = { fun f => fun p => fun s => match (($p) s) { None -> None, " ++
   "Some(r) -> let (v, rest) = r in let w = ($f) v in Some((w, rest)) } } in " ++
   "match (($mapP) {fun v => v + 10} {fun s => Some((7, s))} \"x\") { None -> 0, Some(r) -> let (v, rest) = r in v }") 17

/-! ### Validation ⑨j — the GENERIC PRELUDE: `Option`/`Result` + their maps + the ISO round-trips vs
the built-in sum `Either` (injected globally, `genericPrelude` + `genericPreludeFnSrcs`). The tagged-sum
data types and their combinators are available with NO `data` declaration — `Some`/`Ok`/`Err` resolve
against the injected prelude the way `"hi"` resolves against `Str`; `Left`/`Right` are the primitive
sum (`Either = e + a`, no decl). The `*To*` conversions witness the `Result ≅ Either` and
`Option ≅ Either Unit` isomorphisms; the round-trip guards (`from ∘ to = id` on samples) are the FIRST
witnessed-iso laws made real through `Source.eval`. -/
-- `Option`/`Result` + their constructors used with NO declaration (the prelude injection). A bare-ctor
-- scrutinee is parenthesized (`match (Some(5)) …`) — the parser's match-scrutinee slot (as in the
-- ADR-0079/0081 generic-data guards above).
#guard runTypedYieldsInt 800 "match (Some(5)) { None -> 0, Some(v) -> v }" 5
#guard runTypedYieldsInt 800 "match (Ok(7)) { Err(e) -> e, Ok(a) -> a }" 7
#guard runTypedYieldsInt 800 "match (Err(3)) { Err(e) -> e, Ok(a) -> a }" 3
-- the INJECTED maps (`mapOption`/`mapResult`/`bimap`), used with no local definition.
#guard runTypedYieldsInt 1000 "match (($mapOption) {fun z => z + 1} (Some(4))) { None -> 0, Some(v) -> v }" 5
#guard runTypedYieldsInt 1000 "match (($mapResult) {fun z => z + 1} (Ok(4))) { Err(e) -> e, Ok(v) -> v }" 5
-- `mapResult` passes an `Err` through untouched (maps the success side only).
#guard runTypedYieldsInt 1000 "match (($mapResult) {fun z => z + 1} (Err(9))) { Err(e) -> e, Ok(v) -> v }" 9
-- `bimap g f` maps BOTH sides: `f` over `Right`, `g` over `Left`.
#guard runTypedYieldsInt 1000 "match (($bimap) {fun e => e + 100} {fun a => a + 1} (Right(4))) { Left(e) -> e, Right(a) -> a }" 5
#guard runTypedYieldsInt 1000 "match (($bimap) {fun e => e + 100} {fun a => a + 1} (Left(4))) { Left(e) -> e, Right(a) -> a }" 104
-- ⭐ THE ISO ROUND-TRIPS (`from ∘ to = id`): the first WITNESSED isomorphisms, checked via `Source.eval`.
-- `eitherToResult ∘ resultToEither = id` on `Ok`/`Err` (Result ≅ Either). Sentinel 99 = round-trip broke.
#guard runTypedYieldsInt 1200 "match (($eitherToResult) (($resultToEither) (Ok(5)))) { Err(e) -> 99, Ok(a) -> a }" 5
#guard runTypedYieldsInt 1200 "match (($eitherToResult) (($resultToEither) (Err(3)))) { Err(e) -> e, Ok(a) -> 99 }" 3
-- `eitherToOption ∘ optionToEither = id` on `Some`/`None` (Option ≅ Either Unit).
#guard runTypedYieldsInt 1200 "match (($eitherToOption) (($optionToEither) (Some(7)))) { None -> 99, Some(v) -> v }" 7
#guard runTypedYieldsInt 1200 "match (($eitherToOption) (($optionToEither) (None : Option Int))) { None -> 0, Some(v) -> v }" 0

/-! ## Stage ⑤d — BOUNDED generic functions (bite-2, ADR-0080): a `Monoid a =>`-bounded `fold`,
MONOMORPHIZED per concrete carrier. `fn sum(xs) : List a -> a where Monoid a = …` is a bounded generic
function; at a concrete use `(sum xs : Int)` the result annotation fixes the carrier, the `Monoid Int`
instance is resolved, and its ops (`empty = 0`, `combine = +`) are spliced into a concrete `let rec`
that RUNS. The dict-vs-mono fork (ADR-0075) is decided for MONOMORPHIZATION — consistent with bite-1's
`monoData` + the raw-splice trait model; kernel untouched (elaborate-to-mono). -/

/-- The Int-Monoid prelude + the bounded `sum` (`fold` over any `Monoid a`). -/
def monoidInt : String :=
  "data List a = Nil | Cons(a, List a) " ++
  "trait Monoid { fn empty() -> Self  fn combine(x, y) -> Self } " ++
  "impl Monoid for Int { fn empty() = 0  fn combine(x, y) = x + y } " ++
  "fn sum(xs) : List a -> a where Monoid a = match xs { Nil -> empty, Cons(h, t) -> ($combine) h (($sum) t) } "

-- THE PAYOFF: the bounded `sum` over the Int Monoid — `sum [1,2,3]` = 6 (empty 0, combine +), RUN via the oracle.
#guard runTypedYieldsInt 4000 (monoidInt ++ "(sum (Cons(1, Cons(2, Cons(3, Nil))) : List Int) : Int)") 6
-- the empty list folds to the Monoid identity `empty` = 0.
#guard runTypedYieldsInt 2000 (monoidInt ++ "(sum (Nil : List Int) : Int)") 0

/-- Two Monoid instances (Int + component-wise `(Int * Int)`) sharing ONE bounded `sum`. -/
def monoidTwo : String :=
  "data List a = Nil | Cons(a, List a) " ++
  "trait Monoid { fn empty() -> Self  fn combine(x, y) -> Self } " ++
  "impl Monoid for Int { fn empty() = 0  fn combine(x, y) = x + y } " ++
  "impl Monoid for (Int * Int) { fn empty() = (0, 0)  fn combine(x, y) = let (a, b) = x in (let (c, d) = y in (a + c, b + d)) } " ++
  "fn sum(xs) : List a -> a where Monoid a = match xs { Nil -> empty, Cons(h, t) -> ($combine) h (($sum) t) } "

-- GENERICITY PROOF: the SAME bounded `sum` at TWO carriers in ONE program — Int (→6) and (Int*Int) (→(4,6)).
-- `6 + 4 + 6 = 16`, so one generic `fold` monomorphized to two distinct instances both RUN.
#guard runTypedYieldsInt 6000 (monoidTwo ++
  "let a = (sum (Cons(1, Cons(2, Cons(3, Nil))) : List Int) : Int) in " ++
  "let vs = (Cons((1, 2), Cons((3, 4), Nil)) : List (Int * Int)) in " ++
  "let p = (sum vs : (Int * Int)) in let (m, n) = p in a + m + n") 16

-- fail-loud: MISSING instance. `sum` bounded by Monoid used at `(Int*Int)` with NO such impl ⟹ type error.
#guard (match checkProg (monoidInt ++ "let vs = (Cons((1, 2), Nil) : List (Int * Int)) in (sum vs : (Int * Int))") with
        | .error _ => true | .ok _ => false)
-- fail-loud: a bound trait that is not declared.
#guard (match checkProg "data List a = Nil | Cons(a, List a) fn f(xs) : List a -> a where Bogus a = match xs { Nil -> 0, Cons(h, t) -> 1 } 0" with
        | .error _ => true | .ok _ => false)

/-! ## Stage ⑤e — HIGHER-KINDED types (bite-3, ADR-0082): the FIRST running `Functor`. A trait whose
parameter `f` is a CONSTRUCTOR (`Type→Type`), a method polymorphic in `a`/`b`, and an `impl Functor for
Option`. At the concrete use `fmap inc (Some 5) : Option Int` the RESULT annotation fixes the carrier
constructor (`f := Option`), the `Functor Option` impl resolves BY CONSTRUCTOR NAME, and its `fmap` body
splices in monomorphically — the bite-2 `bfnWrapper` move keyed on a constructor instead of a type. The
spliced body then type-checks + RUNS with the ordinary generic-data machinery; the kernel never learns
about kinds (elaborate-to-mono, invariant #5 preserved). -/

/-- `trait Functor f` + `impl Functor for Option` over the prelude `Option` (ADR-0083). -/
def functorOption : String :=
  "trait Functor f { fmap : (a -> b) -> f a -> f b } " ++
  "impl Functor for Option { fn fmap(g, x) = match x { None -> None, Some(v) -> Some(($g) v) } } "

-- ⭐ THE DEMO (ADR-0082 Stage C): `fmap inc (Some 5) : Option Int ⇒ Some 6`, RUN via the oracle. `inc`
-- increments; `fmap` over `Option` maps the `Some` payload. The `match` extracts the `6`.
#guard runTypedYieldsInt 3000 (functorOption ++
  "let inc = { fun n => n + 1 } in match (fmap inc (Some(5)) : Option Int) { None -> 0, Some(w) -> w }") 6
-- `fmap` over `None` maps nothing — the structure is preserved. `⇒ None`, so the match yields the sentinel 0.
#guard runTypedYieldsInt 3000 (functorOption ++
  "let inc = { fun n => n + 1 } in match (fmap inc (None : Option Int) : Option Int) { None -> 0, Some(w) -> w }") 0
-- fail-loud: a `Functor` method used at a carrier with NO impl (`Functor Result` is undeclared) ⟹ type/elab error.
#guard (match checkProg (functorOption ++
  "let inc = { fun n => n + 1 } in match (fmap inc (Ok(5) : Result Int Int) : Result Int Int) { Err(e) -> e, Ok(w) -> w }") with
        | .error _ => true | .ok _ => false)

/-! ### Stage ⑤e-B — ABSTRACT-OVER-f (bite-3 Case B, ADR-0082 §5): a function GENERIC over ANY `Functor`.
`twice(g, x) : (a -> a) -> f a -> f a where Functor f = ($fmap) g (($fmap) g x)` never names a concrete
constructor — `f` is ABSTRACT in its body, `fmap` dispatched through the `Functor f` bound. At the use
`twice inc (Some 5) : Option Int` the result annotation pins `f := Option` (injectivity head-solution) and
`a := Int` (arg match), the `Functor Option` impl is spliced, and the whole thing monomorphizes to `mu`
and RUNS. This is the "write once, works for any Functor" payoff — HKT realized at the
Surf pre-pass (whole-program mono, kernel untouched). -/
def functorTwice : String :=
  "trait Functor f { fmap : (a -> b) -> f a -> f b } " ++
  "impl Functor for Option { fn fmap(g, x) = match x { None -> None, Some(v) -> Some(($g) v) } } " ++
  "fn twice(g, x) : (a -> a) -> f a -> f a where Functor f = ($fmap) g (($fmap) g x) "

-- ⭐ THE CASE-B DEMO: `twice inc (Some 5) ⇒ Some 7` — `inc` applied twice THROUGH an ABSTRACT Functor `f`.
#guard runTypedYieldsInt 4000 (functorTwice ++
  "let inc = { fun n => n + 1 } in match (twice inc (Some(5)) : Option Int) { None -> 0, Some(w) -> w }") 7
-- abstract `f` over `None` preserves structure — `twice inc None ⇒ None`, the match yields the sentinel 0.
#guard runTypedYieldsInt 4000 (functorTwice ++
  "let inc = { fun n => n + 1 } in match (twice inc (None : Option Int) : Option Int) { None -> 0, Some(w) -> w }") 0

/-- GENERICITY PROOF: a SECOND `Functor` (`Box`) + the SAME `twice` at BOTH carriers — the write-once payoff. -/
def functorTwiceTwo : String :=
  "data Box a = Box(a) " ++
  "trait Functor f { fmap : (a -> b) -> f a -> f b } " ++
  "impl Functor for Option { fn fmap(g, x) = match x { None -> None, Some(v) -> Some(($g) v) } } " ++
  "impl Functor for Box { fn fmap(g, x) = match x { Box(v) -> Box(($g) v) } } " ++
  "fn twice(g, x) : (a -> a) -> f a -> f a where Functor f = ($fmap) g (($fmap) g x) "

-- ONE generic `twice` at TWO Functors: `Some 5 ⇒ Some 7` (7) AND `Box 5 ⇒ Box 7` (7), summed = 14.
#guard runTypedYieldsInt 6000 (functorTwiceTwo ++
  "let inc = { fun n => n + 1 } in " ++
  "let o = match (twice inc (Some(5)) : Option Int) { None -> 0, Some(w) -> w } in " ++
  "let b = match (twice inc (Box(5)) : Box Int) { Box(w) -> w } in o + b") 14

-- fail-loud: abstract-over-f used at a carrier with NO `Functor` impl (`Functor Result` undeclared) ⟹ error.
#guard (match checkProg (functorTwice ++
  "let inc = { fun n => n + 1 } in match (twice inc (Ok(5) : Result Int Int) : Result Int Int) { Err(e) -> e, Ok(w) -> w }") with
        | .error _ => true | .ok _ => false)

/-! ### Stage A KIND-CHECK (ADR-0082 piece 1): kinds-as-arity. A trait parameter `f` is `Type→Type`
(arity 1), so `f a` is well-kinded but `f a b` (arity 2) is a kind error; a base type like `Int` is not
a constructor, so `Int Int` is unrepresentable. -/
-- WELL-KINDED: `Functor f` with `f a`/`f b` (arity-1 uses) builds + checks (body `0`).
#guard (match checkProg (functorOption ++ "0") with | .ok _ => true | .error _ => false)
-- KIND ERROR: a trait param applied at arity 2 (`f a b`) exceeds the v1 arity-1 kind ceiling — fail-loud.
#guard (match checkProg "trait Bad f { op : f a b -> Int } 0" with | .error _ => true | .ok _ => false)
-- `Int Int` is rejected (`Int` is the base type `tInt`, not a `tApp` head — unrepresentable as an application).
#guard (match checkProg "let x = (3 : Int Int) in x" with | .error _ => true | .ok _ => false)

/-! ## Stage ⑤e-D — MONAD (bite-3 Stage D, ADR-0082): the daily-driver payoff. `trait Monad m` over a
CONSTRUCTOR, `pure : a → m a` + `bind : m a → (a → m b) → m b`, and an `impl Monad for Option`. Two
mechanisms compose here: (1) the Stage-C HK-method dispatch (a use `(bind M K : Option Int)` fixes the
carrier `m := Option` from the result annotation, resolves `Monad Option`, splices `bind`'s body); (2)
CARRIER THREADING — inside `bind M { fun x => … }` the continuation is expanded under the enclosing
`Option` hint, so a BARE `pure e` / `bind …` in it fixes its carrier WITHOUT a per-call `: Option _`
annotation (the error-propagation ergonomics — no annotation pyramid, no match pyramid). `pure`'s carrier
is fixed by: its own annotation, OR the enclosing `bind` hint; un-fixable ⟹ fail-loud (annotation
required — decidability descent, ADR-0075). Monomorphizes to `mu` per use; kernel untouched. -/
def monadOption : String :=
  "trait Monad m { pure : a -> m a, bind : m a -> (a -> m b) -> m b } " ++
  "impl Monad for Option { fn pure(x) = Some(x), fn bind(x, f) = match x { None -> None, Some(v) -> ($f) v } } "

-- ⭐ THE CHAIN (ADR-0082 Stage D demo 1): `pure`/`bind` sequenced, 12 threaded through the match. Only the
-- OUTER bind is annotated; inner `bind`/`pure` fix their carrier from the `Monad Option` hint (threading).
#guard runTypedYieldsInt 4000 (monadOption ++
  "match (bind (Some(5)) { fun x => bind (Some(x+1)) { fun y => pure(y*2) } } : Option Int) { None -> 0, Some(w) -> w }") 12
-- ⭐ SHORT-CIRCUIT (demo 2): the error-propagation payoff — `bind None _ ⇒ None`, `f` never runs, NO match
-- pyramid. Inner `pure` un-annotated (carrier threaded from the outer bind).
#guard runTypedYieldsInt 3000 (monadOption ++
  "match (bind (None : Option Int) { fun x => pure(x+1) } : Option Int) { None -> 0, Some(w) -> w }") 0
-- annotated form also runs (every method carries its own `: Option Int`) — the explicit-annotation fallback.
#guard runTypedYieldsInt 4000 (monadOption ++
  "match (bind (Some(5)) { fun x => (bind (Some(x+1)) { fun y => (pure(y*2) : Option Int) } : Option Int) } : Option Int) { None -> 0, Some(w) -> w }") 12
-- pure alone, annotated.
#guard runTypedYieldsInt 3000 (monadOption ++ "match (pure(5) : Option Int) { None -> 0, Some(w) -> w }") 5
-- fail-loud (demo 3): a `Monad` method at a carrier with NO impl (`Monad Result` undeclared) ⟹ elab/type error.
#guard (match checkProg (monadOption ++
  "match (bind (Ok(5) : Result Int Int) { fun x => (pure(x+1) : Result Int Int) } : Result Int Int) { Err(e) -> e, Ok(w) -> w }") with
        | .error _ => true | .ok _ => false)

/-! ### Monad LAWS (ADR-0068/0082 tested rung): Bool-equations discharged by evaluation at `Option`. Each
compares LHS/RHS `Option Int` structurally (`optEqLaw`), yielding `1` iff the law holds on its sample. -/
/-- Structural `Option Int` equality of two ANNOTATED expressions, `⇒ 1` iff equal (the law-sample
verdict). Both sides are DIRECT match scrutinees (the RHS is duplicated per outer arm rather than
let-bound — an `Option Int` computation let-bound then matched loses its concrete μ at elaboration). -/
def optEqLaw (lhs rhs : String) : String :=
  "match " ++ lhs ++ " { None -> match " ++ rhs ++ " { None -> 1, Some(b) -> 0 }, " ++
  "Some(a) -> match " ++ rhs ++ " { None -> 0, Some(b) -> if a == b then 1 else 0 } }"
-- LEFT identity: `bind (pure a) f = f a` (a := 5, f := λx. Some(x*3)).
#guard runTypedYieldsInt 5000 (monadOption ++ "let f = { fun x => (pure(x*3) : Option Int) } in " ++
  optEqLaw "(bind (pure(5)) f : Option Int)" "(($f) 5 : Option Int)") 1
-- RIGHT identity: `bind m pure = m` (m := Some 7).
#guard runTypedYieldsInt 5000 (monadOption ++
  optEqLaw "(bind (Some(7)) { fun x => pure(x) } : Option Int)" "(Some(7) : Option Int)") 1
-- ASSOCIATIVITY: `bind (bind m f) g = bind m (fun x => bind (f x) g)` (m := Some 5, f := λx.Some(x+1), g := λy.Some(y*10)).
#guard runTypedYieldsInt 8000 (monadOption ++
  "let f = { fun x => (pure(x+1) : Option Int) } in let g = { fun y => (pure(y*10) : Option Int) } in " ++
  optEqLaw "(bind (bind (Some(5)) f) g : Option Int)"
           "(bind (Some(5)) { fun x => bind (($f) x) g } : Option Int)") 1

/-! ### SHOWPIECE — `Parser` as a `Monad` (ADR-0082 Stage D / Q26/Q39). The parser-combinators example's
`Parser` is a bare `Thunk (Str → Option (a × Str))` (a type alias, no ctor head to key an HK impl on); to
make sequencing BE `bind`, `Parser` must be NOMINAL — `data Parser a = Parser(…)` (the constructor-vs-alias
finding for HK instances, ADR-0082 "seam to watch"). With that, `impl Monad for Parser` gives do-notation:
`bind digit { fun a => bind digit { fun b => pure(a*10+b) } }` sequences two digit-parsers, the second's
result depending on the first — monomorphized to `mu`, carrier threaded (only the outer `bind` annotated),
RUN via the oracle. This is the handler-agnostic, law-conformant interface made concrete on a real parser. -/
def parserMonad : String :=
  "data Parser a = Parser(Thunk (Str -> Option (a * Str))) " ++
  "trait Monad m { pure : a -> m a, bind : m a -> (a -> m b) -> m b } " ++
  "impl Monad for Parser { " ++
  "fn pure(x) = Parser({ fun s => Some((x, s)) }), " ++
  "fn bind(p, f) = Parser({ fun s => match p { Parser(g) -> match (($g) s) { " ++
  "None -> None, Some(r) -> let (v, rest) = r in match (($f) v) { Parser(h) -> (($h) rest) } } } }) } " ++
  "let isDigit = { fun n => if 47 < n then (if n < 58 then 0 == 0 else 0 == 1) else 0 == 1 } in " ++
  "let digit = Parser({ fun s => match (s : Str) { SNil -> None, " ++
  "SCons(c, rest) -> match c { Char(n) -> if (($isDigit) n) then Some((n - 48, rest)) else None } } }) in "
-- ⭐ TWO-DIGIT PARSER as a monad: `bind digit (fun a => bind digit (fun b => pure(a*10+b)))` on "34" ⇒ 34.
-- The second parse is SEQUENCED after (and independent of) the first via `bind`; `pure` lifts the result.
#guard runTypedYieldsInt 8000 (parserMonad ++
  "match (bind digit { fun a => bind digit { fun b => pure(a * 10 + b) } } : Parser Int) " ++
  "{ Parser(g) -> match (($g) \"34\") { None -> 0, Some(r) -> let (v, rest) = r in v } }") 34
-- short-input short-circuit: only ONE digit available ⇒ the second `digit` fails ⇒ the whole parse is `None`.
#guard runTypedYieldsInt 8000 (parserMonad ++
  "match (bind digit { fun a => bind digit { fun b => pure(a * 10 + b) } } : Parser Int) " ++
  "{ Parser(g) -> match (($g) \"3\") { None -> 0, Some(r) -> let (v, rest) = r in v } }") 0

/-! ### Validation ⑨k — USER EFFECTS: label allocation + program-derived typing (ADR-0092 D1/D2, #44).

`effect Net { read4 : Int -> Str, … }` declares a named interface; the elaborator allocates its
label (`4 + declIndex` among `effect` decls, D1) and builds a total finite `(label, op) ↦
(argTy?, resTy)` lookup (D2 — the surface-side analogue of the kernel's `[EffSig]`). `perform`
(`h.op(...)`) against a `Cap ℓ` receiver TYPES against this table exactly like the four built-ins —
the kernel needs NOTHING new for this (ADR-0092's own grounding fact: "the performer side is
already general"). The typed custom-HANDLE rule that would normally introduce a `Cap ℓ` binding
(`handle e with Net { … }`) is D3 (a sibling kernel lane, not yet landed), so these guards assert
TYPES under `checkPerformUnderCap`'s hypothetical binding, not runs — v1 can DECLARE + PERFORM a
user effect but nothing in-language discharges it yet.

Op names used below are deliberately NON-colliding with the four built-ins (`read4`/`query`/`ping`/
`echo`/…, not `read`/`get`/`put`/`raise`/`new`/`write`) — see the RESERVED-NAME follow-up ruling
just below: a built-in-NAMED user op is a v1 LOUD error, so a positive test can no longer use one. -/

-- (a) label allocation: the FIRST `effect` decl gets label 4 (right after the four built-ins).
#guard (match Bang.Surface.parseProg "effect Net { read4 : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with
            | .ok env => (env.effects.lookup "Net").map EffectInfo.label == some 4
            | .error _ => false)
        | .error _ => false)
-- and the SECOND effect decl gets label 5 (deterministic by EFFECT-decl order, ADR-0046).
#guard (match Bang.Surface.parseProg "effect Net { read4 : Int -> Int } effect Db { query : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with
            | .ok env => (env.effects.lookup "Net").map EffectInfo.label == some 4
                      && (env.effects.lookup "Db").map EffectInfo.label == some 5
            | .error _ => false)
        | .error _ => false)
-- determinism is PER-SOURCE (same program twice → same labels); reordering the two decls in the
-- SOURCE assigns the labels the other way — this is FINE and expected, not a determinism bug (the
-- guard above already fixes one order; this one fixes the swap, both internally consistent).
#guard (match Bang.Surface.parseProg "effect Db { query : Int -> Int } effect Net { read4 : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with
            | .ok env => (env.effects.lookup "Db").map EffectInfo.label == some 4
                      && (env.effects.lookup "Net").map EffectInfo.label == some 5
            | .error _ => false)
        | .error _ => false)

-- (b) LOUD errors — duplicate effect name (D1).
#guard (match Bang.Surface.parseProg "effect Net { read4 : Int -> Int } effect Net { write4 : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false)
        | .error _ => false)
-- duplicate OP name within one effect block — caught at PARSE time (`pEffectMembers`).
#guard (match Bang.Surface.parseProg "effect Net { read4 : Int -> Int, read4 : Int -> Int } 0" with
        | .error _ => true | .ok _ => false)
-- an effect with NO operations is rejected (an empty interface names nothing to perform).
#guard (match Bang.Surface.parseProg "effect Empty { } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false)
        | .error _ => false)

-- (c) `perform` TYPES against a declared effect's op — the D2 payoff. A 1-ary op (`read4 : Int ->
-- Int`) checks its argument and returns the declared result type, the row gaining the op's label.
#guard (match checkPerformUnderCap "effect Net { read4 : Int -> Int } 0" "Net" "h" "h.read4(5)" with
        | .ok (B, φ) => showCTy B == "Int" && (4 : Label) ∈ φ | .error _ => false)
-- and the row DISPLAYS the effect's SOURCE name, not a bare kernel label (`showRow`'s D2 extension).
#guard (match checkPerformUnderCap "effect Net { read4 : Int -> Int } 0" "Net" "h" "h.read4(5)" with
        | .ok (_, φ) => showRow φ [("Net", ⟨4, []⟩)] == "Net" | .error _ => false)
-- a 0-ary op (a bare result type, no arrow) types with no argument.
#guard (match checkPerformUnderCap "effect Ping { ping : Int } 0" "Ping" "h" "h.ping" with
        | .ok (B, φ) => showCTy B == "Int" && (4 : Label) ∈ φ | .error _ => false)
-- an op's ARGUMENT is CHECKED against its declared type (a type mismatch rejects).
#guard (match checkPerformUnderCap "data Pair = Mk(Int, Int) effect Net { read4 : Int -> Int } 0" "Net" "h" "h.read4(Mk(1, 2))" with
        | .error _ => true | .ok _ => false)
-- a declared DATA type as an op's arg/result works too (D2's "declared data types" scope) — round-
-- trips a value through a user op untouched.
#guard (match checkPerformUnderCap "data Pair = Mk(Int, Int) effect Net { echo : Pair -> Pair } 0" "Net" "h" "h.echo(Mk(1, 2))" with
        | .ok (B, φ) => showCTy B == "(mu. (Int * Int))" && (4 : Label) ∈ φ | .error _ => false)

-- (d) NEGATIVE — an UNDECLARED op at a DECLARED user label is an ELABORATION error (D2: total by
-- construction over what's declared; "no entry" is a genuine source error, never a kernel stuck).
#guard (match checkPerformUnderCap "effect Net { read4 : Int -> Int } 0" "Net" "h" "h.write4(5)" with
        | .error _ => true | .ok _ => false)
-- wrong ARITY (0 args supplied to a 1-ary op) rejects with a named-arity message.
#guard (match checkPerformUnderCap "effect Net { read4 : Int -> Int } 0" "Net" "h" "h.read4" with
        | .error m => (m.splitOn "expects 1 argument").length > 1 | .ok _ => false)
-- and the reverse (1 arg supplied to a 0-ary op).
#guard (match checkPerformUnderCap "effect Ping { ping : Int } 0" "Ping" "h" "h.ping(5)" with
        | .error m => (m.splitOn "expects 0 argument").length > 1 | .ok _ => false)
-- a NON-colliding user op name TYPES fine (the positive control the reservation check below is
-- contrasted against) — dispatch is by the RECEIVER'S label (D1: `ℓ < 4` ⟹ built-in, `ℓ ≥ 4` ⟹
-- user), never by op name alone; this is the mechanism the label-first `.dotPerform` fix landed
-- for, still exercised here even though the exact colliding-name case (`read`) is now rejected
-- one step earlier, at DECLARATION time, by the reservation rule immediately below.
#guard (match checkPerformUnderCap "effect Net { read4 : Int -> Int } 0" "Net" "h" "h.read4(5)" with
        | .ok _ => true | .error _ => false)
-- a `perform` on an UNDECLARED effect label (no `effect` decl at all) still rejects exactly as
-- before ADR-0092 (the pre-existing "not a capability value" / label-mismatch path is unaffected
-- for decl-free programs — checked via the ordinary `checkProg` path, no hypothetical cap needed).
#guard (match checkProg "state 5 as h in h.get" with | .ok _ => true | .error _ => false)

/-! ### Validation ⑨l — BUILT-IN op names are RESERVED in `effect` decls (v1 follow-up ruling).

An `effect` decl whose op name collides with ANY built-in op (`capOpSig`'s own table is the SINGLE
SOURCE OF TRUTH checked here — never a hand-copied name list, so a future built-in addition can't
silently desync this reservation from what `.dotPerform`'s built-in arm recognizes) is a LOUD
elaboration error. Root cause this closes: the label-first `.dotPerform` fix makes ELABORATION
correctly type a user op sharing a built-in's name (dispatch is by label, not name) — but the
MACHINE side (`Bang/Core`, the s4 lane's op-priority guard) has an INDEPENDENT name-keyed check
that a built-in op is never served by a custom clause. A same-named user effect would therefore
TYPE here but could diverge from the machine at runtime once D3/D4 land — a typed-program/machine
gap, exactly the class the Agree differential battery exists to catch. Reserving the names makes
the collision UNREPRESENTABLE in any elaborated program (the elaborator/machine consistency holds
BY CONSTRUCTION, not by two independently-maintained checks agreeing). DEFERRED: real per-effect
NAMESPACING (so a user `Net.get` and the built-in `get` could coexist) is the Q34/Q38
module-interface work's territory — this reservation is the v1 stopgap, not the final design. -/
-- a built-in-named op (`get`, the state built-in) is REJECTED at effect-decl elaboration time.
#guard (match Bang.Surface.parseProg "effect Gt { get : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false)
        | .error _ => false)
-- the error NAMES the offending op + the v1-restriction pointer (agent-first: explicit, concise).
#guard (match Bang.Surface.parseProg "effect Gt { get : Int } 0" with
        | .ok p => (match buildEnv p.decls with
            | .error m => (m.splitOn "'get' is reserved").length > 1 | .ok _ => false)
        | .error _ => false)
-- every OTHER built-in op name is reserved too (`put`/`raise`/`new`/`read`/`write` — the whole
-- `capOpSig` table, not just `get`), confirming the check is `capOpSig`-driven, not a partial list.
#guard (match Bang.Surface.parseProg "effect A { put : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
#guard (match Bang.Surface.parseProg "effect B { raise : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
#guard (match Bang.Surface.parseProg "effect C { new : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
#guard (match Bang.Surface.parseProg "effect D { read : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
#guard (match Bang.Surface.parseProg "effect E { write : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
-- a NON-colliding name (`read4`, not `read`) is ACCEPTED — the reservation is precise (built-in
-- names only), not an over-broad rejection of anything superficially similar.
#guard (match Bang.Surface.parseProg "effect Net { read4 : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with | .ok _ => true | .error _ => false)
        | .error _ => false)
-- a MIXED effect (one reserved name among several non-colliding ones) still rejects — reservation
-- is per-OP, not skipped once the decl has at least one safe name.
#guard (match Bang.Surface.parseProg "effect Mixed { read4 : Int -> Int, get : Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false)
        | .error _ => false)

end Bang.TypeCheck
