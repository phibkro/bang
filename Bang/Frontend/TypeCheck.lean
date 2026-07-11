module

-- `#guard`s run the COMPILED checker over parsed source at the META phase → meta import
-- (the cross-module `#guard` codegen wall; mirrors `Examples.lean`).
meta import Bang.Frontend.Surface
meta import Bang.Core.Semantics     -- runTypedYieldsInt's #guards execute Source.eval (Trait.lean precedent)
meta import Bang.Core.Grade         -- QTT.omega must be META-accessible for the #guards
meta import Bang.Frontend.Format    -- lawInstancesOf (#60) reuses showSurf to render a law body to source text
public import Bang.Frontend.Surface
public import Bang.Core.Typing
public import Bang.Core.Grade      -- QTT (the concrete grade rig)
public import Bang.Frontend.Format  -- ditto (public: lawInstancesOf's OWN signature stays Surf/Ty-free; the import is internal plumbing)

/-!
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
-- `public`: `Bang.Query.holesOf` (#82 `bang holes`) reads this to detect a residual hole in a
-- rendered top-level type/row — a residual VALUE hole extracts to `.tvar (holeBase + n)`
-- (`extractV` above), so a `#N` with `N ≥ holeBase` in a `showTy` string IS an underdetermined
-- position. ONE home for the marker range; the verb references it, never copies `1000000`.
public def holeBase  : Nat := 1000000
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
  | .tEff ns _  => some (effNames ns)
  | .tEffR ls _ => some (List.foldl (fun acc ℓ => insert ℓ acc) (∅ : EffRow) ls)   -- #90: resolved
  | .tArr _ b   => effOf b
  | _           => none

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
  | .tEffR _ t => tyBoth t        -- #90: ditto, the RESOLVED form — `effOf` reads it, not `tyBoth`
  | .tSelf     => let V : VT := .tvar 999; (V, .F .omega V)  -- POISON: `buildEnv` substitutes Self before
                                  -- any tyBoth; a leaked Self surfaces as `#999`, never unifies
  | .tName _   => let V : VT := .tvar 998; (V, .F .omega V)  -- POISON: `resolveTy` closes names before
                                  -- any tyBoth; a leaked name surfaces as `#998` (ADR-0069)
  | .tApp _ _  => let V : VT := .tvar 996; (V, .F .omega V)  -- POISON: `resolveTy` monomorphizes tApp first (bite-1)
  | .tMu b     => let V : VT := .mu (tyBoth b).1;  (V, .F .omega V)
  | .tVar n    => let V : VT := .tvar n;           (V, .F .omega V)
  | .tCap ℓ    => let V : VT := .cap ℓ;            (V, .F .omega V)  -- #84 gap 1: ALREADY resolved by
                                  -- `resolveTyG`'s `"Cap"` special case (never poison — the label is
                                  -- concrete by construction the moment a `tCap` exists)
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
/-- Check-mode value-type comparator: structurally identical to `unifyV`, EXCEPT at a `.U` row it
uses `subRow` (actual ⊆ declared) instead of `unifyRow` (exact MGU equality) — #119's fork-1 fix,
scoped to `checkSC`'s `.app` arm (the one shape that needs a NESTED-row subsumption `subRow` alone
can't give — `subRow` compares only the OUTER row, `.app`'s codomain can bury a `.U` inside a
`.prod`/`.sum`/further `.arr`). `unifyV`/`unifyC`/`unifyRow` stay UNTOUCHED elsewhere (`.lett`/
`.matchS` route through their OWN existing explicit arms instead, which already reach
`checkSV`'s correctly-`subRow`-aware `.thunk` case — no separate comparator needed there; only
`.app`'s codomain has no such existing explicit arm to fall back on). Confirmed NOT to disturb the
`rowPolyDivSrc`/#94 row-polymorphism corpus (both hit `synthSC`'s OWN `.app` arm, never this one —
this arm only fires when an `.app` is itself a `checkSC`-checked TAIL under a declared bound). -/
def subsumeAppV (fuel : Nat) (a b : IVTy) : Infer Unit := do
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
    | .sum a1 a2, .sum b1 b2   => do subsumeAppV fu a1 b1; subsumeAppV fu a2 b2
    | .prod a1 a2, .prod b1 b2 => do subsumeAppV fu a1 b1; subsumeAppV fu a2 b2
    | .mu a1, .mu b1           => subsumeAppV fu a1 b1
    | .U φ B, .U φ' B'         =>                             -- SUBSUMPTION: actual φ ⊆ declared/expected φ'
        do if (← subRow fu φ φ') then subsumeAppC fu B B'
           else do
             let φr  ← resolveRow fu φ
             let φ'r ← resolveRow fu φ'
             let excess := φr.labels \ φ'r.labels
             throw s!"thunk body performs \{{showRow excess}}, exceeding its declared bound \{{showRow φ'r.labels}}"
    | _, _ => throw "type mismatch"
def subsumeAppC (fuel : Nat) (a b : ICTy) : Infer Unit := do
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
    | .F q A, .F q' A'         => if q == q' then subsumeAppV fu A A' else throw "returner grade mismatch"
    | .arr q A B, .arr q' A' B' => if q == q' then do subsumeAppV fu A A'; subsumeAppC fu B B'
                                   else throw "arrow grade mismatch"
    | _, _ => throw "computation type mismatch"
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
reserved-range `tvar`; a residual comp hole fails loud. `effects` (default `[]`): same WALL-3-class
seeding fix as `zonkInferC` below — a fresh `USt` here dropped the effects table for any value
inference that descends into a user-effect perform. -/
def runInferV (act : Infer IVTy) (effects : List (String × EffectInfo) := []) : Except String VT := do
  let iv ← (do zonkV bigFuel (← act)).run' { effects := effects }
  extractV iv
/-- As `runInferC`, but keep the ZONKED `ICTy` (no extraction) — for the elaborator's chole-tolerant
returner probes (`anfSplit`, `let`-RHS), which must inspect a higher-order result WITHOUT failing on a
still-open computation hole. `effects` (ADR-0092 D2, #21 s7probe WALL-3-class fix, default `[]`):
`.run' {}` seeded a FRESH, effects-less `USt` here too (the SAME class of bug `elabBind` had —
`anfSplit`'s `synthSC Γ e'` throwaway run hits `.dotPerform`'s D2 arm on ANY A-normalized user-effect
perform, e.g. `net.fetch(1) + 1`, which needs `handleCustomS`'s A-normalization to see `net`'s
resolved label). Every PRE-existing call site is decl-free or doesn't need `.dotPerform` against a
user effect, so the default keeps them behaviour-identical. -/
def zonkInferC (act : Infer (ICTy × Row)) (effects : List (String × EffectInfo) := []) : Except String (ICTy × EffRow) :=
  (do let (B, φ) ← act; return (← zonkC bigFuel B, (← resolveRow bigFuel φ).labels)).run' { effects := effects }
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
  | .letRecMultiS .. => throw "mutual let rec is desugared away by the elaborator — reaching the checker means elabProg didn't run (#97 item 2)"
  | .lettMulti .. => throw "let-sugar (`;`) is erased by elabProg — reaching the checker means elabProg didn't run (issue #68)"
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
  -- #21 s7probe: `handleCustomS n p h cls body` — the ADR-0092 `handleCustom`/`HasClauses` analogue,
  -- ALGORITHMIC (mirrors `withCapS` immediately above; NO `LabelOccurs`/B-occ re-check here — that
  -- invariant is kernel-proof-only, `synthSC` never re-derives it for ANY built-in handler either,
  -- so this is not a new gap, just the existing algorithm/proof split). `n` MUST be a bare `.var`
  -- naming a DECLARED `effect` (resolved via `env.effects`, exactly `.dotPerform`'s D2 lookup below)
  -- — a non-`.var` `n` is a LOUD diagnostic (#74 pattern: name the construct, not a crash), since
  -- there is no other sense in which `n` could denote an effect at v1.
  --
  -- MECHANICS FINDING (the load-bearing one): the clause loop CANNOT be a `for` over a converted
  -- `List` (tried first) — `sizeOf`-based structural termination can't see through the opaque
  -- `hClausesToList` call, so `synthSV b`'s call inside the loop fails the SAME termination proof
  -- `synthSC`'s explicit `termination_by (sizeOf e, 1)` pins for every OTHER arm. It ALSO can't be a
  -- local `let rec` (tried second) — that joins `synthSC`'s own 4-way mutual group and Lean can't
  -- find a joint measure, breaking the WHOLE file's termination and cascading `sorry`-taint through
  -- every downstream `#guard`. The fix that WORKS mirrors `elabS`/`elabArms` (the `DArms` precedent,
  -- `matchD`'s named-match arms): `HClauses` becomes a genuine THIRD mutual partner
  -- (`checkHClauses`, below), structurally recursing on `HClauses` itself with its own
  -- `termination_by`, called from here as an ordinary mutual-sibling call — exactly how `synthSC`
  -- already calls `synthSV`/`checkSC`. GENERALIZES: any REPEATED-GROUP `Surf` payload (a clause
  -- list, arms, bindings) that needs typing-algorithm recursion back into `synthSC`'s own mutual
  -- group needs this shape, not a `for`/`let rec` — a structural finding for s7design + whoever
  -- implements Stage 7 for real.
  -- ADR-0095 D1 (RULED): `_lbl` (the resolved-label slot) is IGNORED here — `synthSC` re-derives
  -- `ℓ` fresh from `env.effects` every time (the SAME move `.dotPerform`'s D2 arm already makes),
  -- exactly like `elabS` independently re-deriving `capKindLabel` rather than trusting a
  -- possibly-stale tree annotation. The slot exists for `lowerC` (WALL 1's fix), which has no
  -- `env` to re-derive from — `synthSC` is NOT in that position, so it stays state-sourced.
  | .handleCustomS _lbl n p? h cls body => do
      match n with
      | .var effN => do
          let effs ← (do return (← get).effects)
          match effs.find? (fun (nm, _) => nm == effN) with
          | none => throw s!"handle: '{effN}' is not a declared effect"
          | some (_, ei) => do
              let ℓ := ei.label
              -- THE PARAM: `P` is DISCOVERED from the param-init's own synthesized type (no
              -- separate declared param-type exists in the `effect` decl shape, ADR-0092 D1
              -- doesn't carry one) — the same move `state e0 in …` uses to discover `S` from `e0`.
              -- A param-less `Name` (`.none`) synthesizes at `Unit` (the kernel's `Handler.custom`
              -- always carries a `p : Val`, ADR-0092's premise — `.unitS` is the CLOSED value
              -- `lowerC`'s own `.none` arm already lowers to, kept CONSISTENT here).
              let P ← (match p? with
                | .none    => pure (.unit : IVTy)
                | .one p0  => synthSV Γ p0
                | .two _ _ => throw "handle: the param-init takes at most 1 argument")
              -- RET-SHAPE (ADR-0092 D3/D4, the grade wall): v1 requires each clause body's SYNTAX to
              -- be a bare value-shaped expression (no further computation after the resume value).
              -- `checkHClauses` approximates this SEMANTICALLY (no separate `.ret` marker exists in
              -- `Surf`, unlike the kernel's `Comp.ret`) — `b` must SYNTHESIZE at a VALUE type
              -- matching the op's `resTy`, exactly what a value-return would. An effectful body fails
              -- for a DIFFERENT surface reason (`synthSC`/row shape), so ret-shape and "effect-free"
              -- collapse to the same check here — the exact ADR-0092 D4 property ("ret w is
              -- EFFECT-FREE, no φ' to join") showing up as a REUSED mechanism (`synthSV`, which never
              -- carries a row) rather than a dedicated syntactic gate. REPORTED to s7design: the D4
              -- error MESSAGE ("clause body isn't ret-shaped") is not literally what fires — what
              -- fires is `synthSV` rejecting a non-value `Surf` shape, a DIFFERENT, less specific
              -- message; a real implementation needs a dedicated check to match the ADR's promised
              -- diagnostic wording.
              let _ ← checkHClauses Γ effN ei.ops P cls
              -- COVERAGE: every declared op has a clause (the semantic half of ADR-0092's PROGRESS
              -- premise — `∀ op, opArg ℓ op = some _ → clauses.find? ... .isSome`).
              for (op, _, _) in ei.ops do
                if !(Bang.Surface.hClausesToList cls).any (fun (op', _, _) => op' == op) then
                  throw s!"handle: effect '{effN}' op '{op}' has no clause"
              let capTy : IVTy := .cap ℓ
              let (B, φ) ← synthSC ((h, capTy) :: Γ) body   -- h : Cap ℓ in scope (ADR-0092's cap-bind)
              return (B, ← eraseRow bigFuel ℓ φ)                  -- the handler DISCHARGES ℓ
      | _ => throw "handle: the effect name must be a bare identifier naming a declared `effect`"
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
  -- #119 fork-1: a `.lett`-chain's TAIL can be a value-constructor shape (`.pairS`, `.thunk`, …)
  -- carrying its OWN declared row bound (e.g. `buildLetRecMulti`'s pair-of-thunks) — without this
  -- arm, `.lett` falls to the catch-all below, which `synthSC`s the WHOLE chain (losing the tail's
  -- declared-bound context) and exact-equality-unifies the result, tripping the exact bug this
  -- issue reports. Recursing `checkSC` into the RHS keeps every OTHER `.lett` semantic (HM
  -- generalization, the value-restriction) byte-identical to `synthSC`'s own `.lett` arm — the only
  -- change is the TAIL now checks (subsumption-capable) instead of synthesizes (equality only).
  | .lett x e b, expected => do
      let (Ce, φ₁) ← synthSC Γ e
      let (_, A) ← expectF Ce
      let sch ← if isValueSurf e then generalize Γ A else pure ({ body := A } : Scheme)
      let φ₂ ← checkSC ((x, sch) :: Γ) b expected
      joinRow bigFuel φ₁ φ₂
  -- #119 fork-1 (same shape as `.lett` above): a `matchS` ARM'S tail can ALSO be a declared-bound
  -- value shape — pushing `expected` into BOTH arms (rather than `synthSC`-ing the whole match then
  -- unifying post-hoc, `synthSC`'s own `.matchS` arm's approach) lets each arm's tail take ITS OWN
  -- explicit `checkSC` arm (subsumption-capable), not just the outermost catch-all.
  | .matchS s xl el xr er, expected => do match (← resolve bigFuel (← synthSV Γ s)) with
      | .sum A B => do
          let φ₁ ← checkSC ((xl, A) :: Γ) el expected
          let φ₂ ← checkSC ((xr, B) :: Γ) er expected
          joinRow bigFuel φ₁ φ₂
      | .vhole n  => do let A ← freshHole; let B ← freshHole
                        assign n (.sum A B)
                        let φ₁ ← checkSC ((xl, A) :: Γ) el expected
                        let φ₂ ← checkSC ((xr, B) :: Γ) er expected
                        joinRow bigFuel φ₁ φ₂
      | _ => throw s!"match: scrutinee is not a sum{nameHint s}"
  -- #119 fork-1: an `.app` in tail position has no OTHER explicit `checkSC` arm to route the
  -- codomain through (unlike `.lett`/`.matchS`, which recurse into shapes `checkSV`'s already
  -- `subRow`-aware `.thunk` case eventually reaches) — the callee's codomain can bury a declared
  -- row inside a `.prod`/`.sum`/nested `.arr`, so a single top-level `subRow` isn't enough; the
  -- structural `subsumeAppV`/`subsumeAppC` walk (above) descends to every such row. Confirmed this
  -- does NOT reach `synthSC`'s OWN `.app` arm (unchanged) — `rowPolyDivSrc`/#94's row-polymorphism
  -- corpus still gates correctly (their `.app`s run at the top-level `synthSC` entry, never nested
  -- under a `checkSC` declared-bound context).
  | .app f a, expected => do
      let (cf, φ) ← synthSC Γ f
      match (← resolveC bigFuel cf) with
      | .arr _ A B => do
          let _ ← checkSV Γ a A
          let _ ← subsumeAppC bigFuel B expected
          return φ
      | .chole n   => do
          let A ← freshHole; let B ← freshCHole
          assignC n (.arr .omega A B)
          let _ ← checkSV Γ a A
          let _ ← subsumeAppC bigFuel B expected
          return φ
      | _          => throw s!"app: callee is not a function{nameHint f}"
  | e, expected => do
      let (B, φ) ← synthSC Γ e
      let _ ← unifyC bigFuel B expected                 -- HM subsumption (was structural `B = expected`)
      return φ
  termination_by (sizeOf e, 3)

/-- #21 s7probe (ADR-0095 D4 fix): the `HClauses` mutual partner `synthSC`'s `handleCustomS` arm
needs (the `elabS`/`elabArms` precedent — a repeated-group `Surf` payload gets its OWN
structurally-recursive sibling in the SAME mutual block, not a `for`/`let rec`; see the finding
at `handleCustomS`'s call site). Structurally recurses on `cls : HClauses` (decreasing on EVERY
call, including the `synthSC` call on each clause body `b` — `b` is a genuine subterm of
`.cons op x b rest`, so `sizeOf`-based termination sees it directly). Checks each clause's body
against its op's declared `resTy`, under `[argVar : argTy, param : P]` (the ADR-0092
`HasClauses.cons` binder order — `opArg` at idx 0, `P` at idx 1, mirrored here as
list-head-is-idx-0). Per-clause OP membership in the effect's declared ops is checked here too
(an unknown op name is a clause-level diagnostic, distinct from the CALLER's coverage check in
the other direction).

#87 (ADR-0095 D1's own worked example, landed): the binder is spelled the LITERAL surface
identifier `"param"`, not a `#`-prefixed sentinel — `pIdent` (Surface.lean) reserves `param` as a
keyword at every binder position, so no clause-arg/cap-binder/`let`/`fun` name can ever collide
with it, making a plain `Γ`-lookup of `.var "param"` safe by construction (the same discipline
`with`/`resume` already use).

WALL-4 FIX (found live via the ADR-0095 tracer bullet, `n * 10` as a clause body): the body is a
COMPUTATION (`.binopS` reduces via the kernel's `Comp.binop`, needing `synthSC`/`Comp` typing) —
NOT already a bare VALUE the earlier `synthSV`-based check assumed. `synthSV` has no `.binopS`
arm, so ANY non-atomic clause body (arithmetic, an application, …) unconditionally hit its
catch-all `"not a value"` error — this was the root cause of the earlier "lowerV-path
divergence" finding (WALL 4 in the original writeup), not a genuine typed/untyped pipeline
mismatch; the untyped path never RAN this check at all (no `synthSC`/`synthSV` on the untyped
path), which is why it "worked" there and only the TYPED path exposed the bug. Fixed: `synthSC`
(computation typing) + an EXPLICIT ret-shape/effect-free check — ADR-0092 D4's own property
("ret w is EFFECT-FREE, no φ' to join") is now checked DIRECTLY (`φ = botR`), not merely implied
by `synthSV`'s row-blindness (which was wrong, not just imprecise: `synthSV` never even reaches a
row to be blind to). -/
def checkHClauses (Γ : NCtx) (effN : String) (ops : List (String × Option VT × VT)) (P : IVTy) :
    HClauses → Infer Unit
  | .nil => pure ()
  | .cons op x b rest => do
      match ops.find? (fun (n, _, _) => n == op) with
      | none => throw s!"handle: clause '{op}' is not an operation of effect '{effN}'"
      | some (_, argTy?, resTy) => do
          let argTy := embV (argTy?.getD .unit)   -- 0-ary op: `x` binds Unit (placeholder — no 0-ary clause corpus case yet)
          let (Cb, φ) ← synthSC ((x, argTy) :: ("param", P) :: Γ) b
          let _ ← unifyC bigFuel Cb (.F .omega (embV resTy))
          -- ADR-0092 D4 / ADR-0095 D4: the RET-SHAPE / effect-free property, checked explicitly.
          -- A non-empty row here means the clause body PERFORMS before resuming — exactly the v1
          -- restriction ADR-0095 D4 names; the teaching diagnostic fires (not a bare type error).
          let φr ← resolveRow bigFuel φ
          -- `Finset.isEmpty` is noncomputable here (memory: effrow-finset-noncomputable-guard-path)
          -- — `decide (φr.labels = ∅)` over `Finset`'s `DecidableEq` is the corpus-established
          -- workaround for testing row-emptiness in this compiled #guard-reachable path.
          if !(decide (φr.labels = ∅) && φr.tail.isNone) then
            throw s!"handle: clause '{op}' body must be a `ret`-shape value in v1 (no effects before resuming) — a compute-then-return body needs binop typing (ADR-0065) + resumption-grade surfacing (Q27), tracked as the general-body entry gate (ADR-0095 D4)"
          checkHClauses Γ effN ops P rest
  termination_by cls => (sizeOf cls, 4)
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
  | .tCap ℓ    => .tCap ℓ   -- #84 gap 1: closed, no `Self` inside to substitute
  | .tApp n (.one a)   => .tApp n (.one (substSelf target a))              -- inlined (termination sees the subterms)
  | .tApp n (.two a b) => .tApp n (.two (substSelf target a) (substSelf target b))
  | .tVar n    => .tVar n
  | .tMu b     => .tMu   (substSelf target b)
  | .tArr a b  => .tArr  (substSelf target a) (substSelf target b)
  | .tSum a b  => .tSum  (substSelf target a) (substSelf target b)
  | .tProd a b => .tProd (substSelf target a) (substSelf target b)
  | .tThunk t  => .tThunk (substSelf target t)
  | .tEff ns t => .tEff ns (substSelf target t)
  | .tEffR ls t => .tEffR ls (substSelf target t)   -- #90: resolved row, no `Self` inside to substitute

/-- Substitute the concrete carrier `T` for a bound type VARIABLE `tv` in a bounded-fn's declared
type (`List a -> a` at `a := Int` ⟹ `List Int -> Int`). A `.tName tv` is the bound var; any other
`.tName` is a real data name, left for `resolveTy`. Enumerated (a new `Ty` former fails here). -/
def substTyVar (tv : String) (target : Ty) : Ty → Ty
  | .tName n   => if n == tv then target else .tName n
  | .tCap ℓ    => .tCap ℓ   -- #84 gap 1: closed, no bound type var inside to substitute
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
  | .tEffR ls t => .tEffR ls (substTyVar tv target t)   -- #90: resolved row, no bound var inside

/-- Collect the GENUINELY free type-variable names in a `let rec` ascription (ADR-0103 decision
item 2): a `.tName n` that is neither a `data` decl (`gen`) nor a monomorphic `aliases` entry is
exactly the shape `resolveName` would fail loud on today (`resolveTyG`'s `.tName` arm, the #120
wall) — so this is the SAME lookup, run BEFORE resolution to decide "generalizable" vs "typo",
never a second source of truth. Structural, enumerated (a new `Ty` former fails to compile here
until handled — the `substTyVar`/`substSelf` completeness precedent). `.eraseDups` since a tyvar
may occur many times (`List a -> List a -> Int`). -/
def freeTyVars (gen : List (String × GenData)) (aliases : List (String × Ty)) : Ty → List String
  | .tName n    => if (aliases.lookup n).isSome then [] else if (gen.lookup n).isSome then [] else [n]
  | .tCap _     => []
  | .tSelf      => []
  | .tInt       => []
  | .tUnit      => []
  | .tVar _     => []
  -- `Cap Net`'s argument names a DECLARED EFFECT (`resolveTyG`'s #84-gap-1 special case,
  -- `env.effects` — a table this pass never sees), never a `gen`/`aliases` type name and never a
  -- generalizable tyvar — contributes NOTHING here (mirrors `resolveTyG`'s own `.tApp "Cap" …`
  -- interception BEFORE the generic-`gen`-table path). Missing this case mis-flagged
  -- `examples/calc`'s `eval : Cap Eval_Trace -> …` as a bound-free generic over `Eval_Trace`
  -- (confirmed live: `existing-examples-unchanged` regressed until this arm was added).
  | .tApp "Cap" _       => []
  | .tApp _ (.one a)    => freeTyVars gen aliases a
  | .tApp _ (.two a b)  => freeTyVars gen aliases a ++ freeTyVars gen aliases b
  | .tMu b      => freeTyVars gen aliases b
  | .tArr a b   => freeTyVars gen aliases a ++ freeTyVars gen aliases b
  | .tSum a b   => freeTyVars gen aliases a ++ freeTyVars gen aliases b
  | .tProd a b  => freeTyVars gen aliases a ++ freeTyVars gen aliases b
  | .tThunk t   => freeTyVars gen aliases t
  | .tEff _ t   => freeTyVars gen aliases t
  | .tEffR _ t  => freeTyVars gen aliases t
  |>.eraseDups

/-- Match a `let rec` ascription TEMPLATE (containing free tyvars, e.g. `List a -> Int`) against a
concrete call-site annotation for THE SAME slot (e.g. `List Int`), collecting tyvar bindings —
ADR-0103 decision item 3's discovery mechanism, the `hktMatch` precedent specialized to argument-
position carriers (the fold-shape wall, w2, is exactly why THIS family needs its own matcher rather
than reusing `bfnWrapper`'s result-anchored one). A `.tName` in the template binds to the concrete
counterpart (the caller restricts `v` to genuinely-free names via `freeTyVars`); any other shape
mismatch contributes nothing (`hktMatch`'s own "non-aligning shapes contribute nothing" discipline
— this pass only ever WIDENS the candidate set, a later check on the residue catches a genuinely
ill-typed instantiation). -/
def matchTyVars : Ty → Ty → List (String × Ty)
  | .tName v,           c                  => [(v, c)]
  | .tApp _ (.one p),   .tApp _ (.one c)   => matchTyVars p c
  | .tApp _ (.two p q), .tApp _ (.two c d) => matchTyVars p c ++ matchTyVars q d
  | .tArr p q,          .tArr c d          => matchTyVars p c ++ matchTyVars q d
  | .tProd p q,         .tProd c d         => matchTyVars p c ++ matchTyVars q d
  | .tSum p q,          .tSum c d          => matchTyVars p c ++ matchTyVars q d
  | .tThunk p,          .tThunk c          => matchTyVars p c
  | .tEff _ p,          c                  => matchTyVars p c
  | p,                  .tEff _ c          => matchTyVars p c
  | _,                  _                  => []

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
the elaborated call site needs. **#112 fix — two dispatch modes, `knotName` selects between
them:** a 2-PARAM op (the only arity `.binopS` dispatch ever calls, see its `[p, q]` match) is
KNOT-BOUND — `knotName := some "#opknotN"` names a `let rec` (Landin's-knot, ADR-0073/#95)
wrapping the WHOLE elaborated program (built by `elabProg`, not here — `buildEnv` only MINTS the
name and records the op for the wrapper pass; `body` for this case is an inert placeholder,
NEVER spliced), so a self- or backward-referential call resolves through the SAME real recursion
mechanism ordinary `let rec` uses, not textual substitution. Any OTHER arity (0/1/3+ params) keeps
the PRE-#112 behavior: `body` is PRE-ELABORATED at env build (`knotName := none`) and spliced
verbatim wherever it's consulted — safe because `.binopS` is `body`'s ONLY consumer (grep-verified)
and never dispatches a non-2-param op, so a splice-caused self-reference wall can't be reached
through that arity. PUBLIC (#60 seam): forced by `ElabEnv`'s field type — additive visibility
only, no behavior change to non-impl paths. -/
public structure Inst where
  opName   : String
  target   : VT       -- the structural resolution key (ADR-0068 decision 2)
  targetTy : Ty       -- the impl's declared target, for the elaborated annotation
  retTy    : Ty       -- the trait sig's ret type, Self-substituted
  params   : List String
  body     : Surf
  knotName : Option String := none   -- #112: `some` ⟹ dispatch via `($knotName) (a, b)`, ignore `body`

public abbrev InstEnv := List Inst

/-- **#112 fix — one pending KNOT** for a 2-param impl op: the fresh binder name `.binopS`
dispatch will reference, the impl's target type (the knot's tupled-arg domain, `T * T`), the
op's result type, and its RAW (un-elaborated) params/body — elaborated later, inside `letRecS`'s
OWN elaboration arm (`TypeCheck.lean`'s `.letRecS` case), which is what actually resolves a
self- or backward reference through the μ-encoded fixpoint. Kept RAW here (not `Surf`-elaborated)
for the SAME reason `RawOp`/`RawImpl` already are: elaborating too early is precisely the #112 bug. -/
public structure PendingOpKnot where
  knotName : String
  targetTy : Ty
  retTy    : Ty
  p1       : String    -- the op's two Self-typed param NAMES, as declared (`fn eq(p, q) = …`)
  p2       : String
  rawBody  : Surf

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
  pendingKnots : List PendingOpKnot := []              -- #112: 2-param impl ops awaiting `elabProg`'s knot wrap

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

/-- #90: resolve ONE row-annotation name to its label — the four BUILT-INS first (the `effNames`
table, unchanged), else the program's declared user `effect`s (`effects`, ADR-0092 D1/D2's own
table). `none` ⟹ genuinely undeclared, the caller fails loud (never a silent drop — the bug
`resolveTyG`'s `.tEff` arm replaces). Plain (not part of the `resolveTyG`/`monoData` mutual group —
it doesn't recurse into either). -/
def resolveEffName (effects : List (String × EffectInfo)) (n : String) : Option Label :=
  if n = "throws" then some exnLabel
  else if n = "state" then some stateLabel
  else if n = "stm" then some stmLabel
  else if n = "Div" then some divLabel
  else (effects.lookup n).map EffectInfo.label

mutual
/-- Monomorphize `name argTys` to its CLOSED μ (ADR-0069 bite-1). `List Int` ↦ `μX. Unit + (Int × X)`:
substitute the args for the decl's params in every ctor payload (self-reference ↦ the μ-bound var 0),
right-nest into sum/product, μ-wrap. Fuel bounds decl-nesting depth (a cyclic generic instantiation
fail-louds). The kernel only ever sees this closed μ (elaborate-to-mono; kernel untouched). `effects`
(#84 gap 1, default `[]`) is threaded ONLY so this stays in the same mutual group as `resolveTyG`
(no generic `data` decl ever needs it — `Cap` is not a `gen` entry) — the SAME pass-through-for-the-
mutual-group reason `USt.effects` threads through `elabBind`/`anfSplit` (WALL 3, #21 s7probe). -/
def monoData (gen : List (String × GenData)) (aliases : List (String × Ty))
    (effects : List (String × EffectInfo)) :
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
            c.2.mapM (resolveTyG gen aliases effects fuel σ (some (name, gd.params))))
          return .tMu (sumOfTys (openPays.map prodOfTys))

/-- Resolve a type in a GENERIC template context: `σ` substitutes params for concrete args, `self?`
identifies the recursive self-application (↦ the μ-bound `tVar 0` — v1 has no nested self-binders so
depth is always 0, ADR-0069). A `tApp` of ANOTHER (or the same, different-args) generic name recurses
through `monoData`. `tName`s resolve param → σ, else the monomorphic alias env. #84 gap 1: `tApp "Cap"
(.one (.tName effN))` is intercepted BEFORE the generic-`gen`-table path — `Cap` is a BUILT-IN type
former (a capability, not a user `data` decl), resolved against `effects` (ADR-0092 D1/D2's own
`env.effects` table, the SAME lookup `.dotPerform`'s D2 arm and `handleCustomS`'s label-resolve arm
already use) into the CLOSED `tCap ℓ` form — never reaching `monoData`/`gen.lookup`, which has no
entry for "Cap" and would otherwise fail-loud "unknown generic type". -/
def resolveTyG (gen : List (String × GenData)) (aliases : List (String × Ty))
    (effects : List (String × EffectInfo)) :
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
                             else resolveName gen aliases effects n
          | _             => resolveName gen aliases effects n
    | .tApp "Cap" (.one (.tName effN)) =>                    -- #84 gap 1: `Cap Net` (a built-in
        match effects.lookup effN with                        -- former, not a `gen` entry)
        | some ei => .ok (.tCap ei.label)
        | none    => .error s!"'Cap {effN}': '{effN}' is not a declared effect"
    | .tApp "Cap" _ =>
        .error "'Cap' takes exactly one argument naming a declared effect (`Cap Net`)"
    | .tApp n args =>
        match self? with
        | some (sn, sps) =>
            if n == sn && argsAreParams sps args.toList then .ok (.tVar 0)   -- self-recursion → μ-bound var
            else do let args' ← args.toList.mapM (resolveTyG gen aliases effects fuel σ self?)
                    monoData gen aliases effects fuel n args'
        | none => do let args' ← args.toList.mapM (resolveTyG gen aliases effects fuel σ self?)
                     monoData gen aliases effects fuel n args'
    | .tInt      => .ok .tInt
    | .tUnit     => .ok .tUnit
    | .tSelf     => .ok .tSelf
    | .tVar n    => .ok (.tVar n)
    | .tCap ℓ    => .ok (.tCap ℓ)   -- already-resolved (re-entrant resolution, e.g. a `letRecS` re-run)
    | .tMu b     => do return .tMu   (← resolveTyG gen aliases effects fuel σ self? b)
    | .tArr a b  => do return .tArr  (← resolveTyG gen aliases effects fuel σ self? a) (← resolveTyG gen aliases effects fuel σ self? b)
    | .tSum a b  => do return .tSum  (← resolveTyG gen aliases effects fuel σ self? a) (← resolveTyG gen aliases effects fuel σ self? b)
    | .tProd a b => do return .tProd (← resolveTyG gen aliases effects fuel σ self? a) (← resolveTyG gen aliases effects fuel σ self? b)
    | .tThunk t  => do return .tThunk (← resolveTyG gen aliases effects fuel σ self? t)
    -- #90: resolve EACH name in the row annotation against BOTH the four built-ins AND the
    -- program's declared user effects (`effects`) — the row-naming gap `Cap` already fixed for
    -- ITS constructor, generalized to `tEff`'s sibling. An unresolvable name fails loud (never a
    -- silent drop — the OLD `effNames` behavior this replaces for `resolveTyG`'s reachable path).
    | .tEff ns t => do
        let ls ← ns.mapM (fun n => match resolveEffName effects n with
          | some ℓ => pure ℓ
          | none   => throw s!"'{n}' is not a declared effect (row annotation)")
        return .tEffR ls (← resolveTyG gen aliases effects fuel σ self? t)
    | .tEffR ls t => do return .tEffR ls (← resolveTyG gen aliases effects fuel σ self? t)   -- already-resolved

/-- A bare type NAME: a monomorphic alias, else fail-loud (a generic name used WITHOUT args, or a typo).
`effects` is unused here BY CONSTRUCTION — a bare `.tName` can never be `Cap` (that always requires an
argument, `Cap Net`, which `resolveTyG`'s `.tApp "Cap" …` arm intercepts a level up, before a bare-name
`.tName "Cap"` could reach here) — threaded only for the mutual group's uniform signature. -/
def resolveName (gen : List (String × GenData)) (aliases : List (String × Ty))
    (_effects : List (String × EffectInfo)) (n : String) : Except String Ty :=
  match aliases.lookup n with
  | some t => .ok t
  | none   => match gen.lookup n with
              | some _ => .error s!"generic type '{n}' needs type argument(s) (`{n} …`)"
              | none   => .error s!"unknown type name '{n}'"
end

/-- Close a type over the elaboration env: monomorphic names via `aliases`, generic applications
(`List Int`) monomorphized via `monoData` (ADR-0069 bite-1), `Cap Net` via `effects` (#84 gap 1). The
public entry (σ empty, no self). `effects` defaults to `[]` (the WALL-3 `anfSplit`/`elabBind`
precedent) — a caller with no `ElabEnv` in scope (data/trait/impl resolution inside `buildEnv`, which
runs BEFORE `effects` is fully accumulated for later decls) behaves byte-identically to before this
change; only `elabS`'s ascription sites (which run AFTER `buildEnv` completes, `env.effects` in full)
pass the real table. -/
def resolveTy (gen : List (String × GenData)) (aliases : List (String × Ty)) (t : Ty)
    (effects : List (String × EffectInfo) := []) : Except String Ty :=
  resolveTyG gen aliases effects 1000 [] none t

/-! ### Display-time μ re-fold (issue #100)

A `data` decl's closed μ-type (`ci.dataTy` / `monoData`'s output) is what a checked expression's
type actually carries — `showVTy`'s raw `(mu. (Unit + (Int * #0)))` is technically correct but
illegible; a user wrote `List Int`, never a μ. This is the INVERSE of elaboration (ADR-0069):
given a candidate `VT`, find the `data` decl (monomorphic OR generic) whose encoding it matches,
and print the declared name (+ resolved args) instead. Never a GUESS — an unmatched μ (an
anonymous/kernel-level recursive type with no backing `data` decl) still falls back to the raw
`showVTy` rendering unchanged; this is purely ADDITIVE legibility over what already displays. -/

-- `selfFree`/`unifyDataTy`/`showBoundArg`/`foldDataTy`/`foldDataTyOrRaw` all live in ONE `mutual`
-- group below (a doc comment must attach to the first DEF inside `mutual`, never precede the
-- `mutual` keyword itself — a Lean parse rule, not a style choice): `unifyDataTy` calls itself
-- structurally, `foldDataTy` calls `unifyDataTy` and (via `showBoundArg`) itself (nested data
-- types fold too), and `selfFree`/`selfFreeC` are called from `unifyDataTy`.
mutual
/-- Does this `VT`/`CT` contain NO raw `.tvar` (an escaped de-Bruijn self-reference)? Guards
`unifyDataTy`'s bare-param case (`.tName p, v`) below — since unification runs OUTSIDE any μ
binder, any `.tvar` reaching that level is dangling, never a genuine closed argument; without this
guard a NON-recursive decl's bare-param ctor (`Option a`'s `Some(a)`, template `Unit + a`)
over-matches a DIFFERENT recursive decl's closed μ body (`List Int`'s `Unit + (Int × #0)`, binding
`a := (Int × #0)` — a value that still carries the dangling `#0`) — the exact false-positive #100's
fold must refuse (fall through to raw `showVTy`, never a WRONG name). -/
partial def selfFree : VT → Bool
  | .tvar _   => false
  | .sum a b  => selfFree a && selfFree b
  | .prod a b => selfFree a && selfFree b
  | .mu _     => true   -- a NESTED μ CAPTURES its own `.tvar 0` (De Bruijn) — closed from OUR level regardless of what's inside
  | .U _ b    => selfFreeC b
  | _         => true
partial def selfFreeC : CT → Bool
  | .F _ a     => selfFree a
  | .arr _ a b => selfFree a && selfFreeC b

partial def unifyDataTy (selfName : String) : Ty → VT → Option (List (String × VT))
  -- self-recursion (`resolveTyG`'s NULLARY-self case): the template's `tApp selfName params`
  -- became `.tVar 0` at monomorphization time (the μ-bound var, NOT re-wrapped in a nested `.mu`)
  -- — tried BEFORE the generic `.tName`/`.tApp` cases below since `argsAreParams` self-recursion
  -- is a MORE specific match than a bare param would be.
  | .tApp n _,   .tvar 0      => if n == selfName then some [] else none
  | .tName p,    v            => if selfFree v then some [(p, v)] else none
  | .tInt,       .int         => some []
  | .tUnit,      .unit        => some []
  | .tSum a b,   .sum c d     => (· ++ ·) <$> unifyDataTy selfName a c <*> unifyDataTy selfName b d
  | .tProd a b,  .prod c d    => (· ++ ·) <$> unifyDataTy selfName a c <*> unifyDataTy selfName b d
  | .tMu a,      .mu c        => unifyDataTy selfName a c
  | .tVar i,     .tvar j      => if i == j then some [] else none
  | _,           _            => none

/-- Render a resolved param binding (from `unifyDataTy`) — recurses through `foldDataTy` so a
NESTED data type (`Option (List Int)`) folds at every level, not just the outermost. -/
partial def showBoundArg (ctors : List (String × CtorInfo)) (gen : List (String × GenData))
    (v : VT) : String :=
  foldDataTyOrRaw ctors gen v

/-- The actual fold: try every MONOMORPHIC `data` decl first (direct structural equality against
`ci.dataTy`, deduped by `dataName` since every ctor of the same decl carries an identical
`dataTy`), then every GENERIC decl (`gen`, ADR-0069 bite-1) via `unifyDataTy` against each ctor's
OWN template with the OUTER μ substituted in for self — a match names the decl + its resolved args
(recursively folded, `List (List Int)` renders fully). `none` when nothing backing this `VT`
exists (an anonymous/kernel μ, e.g. `impl Add for (Int * Int)`'s product — never `data`-declared,
correctly untouched). Monomorphic decls are tried BEFORE generic ones — a monomorphic decl's
`dataTy` is a closed literal `VT`, cheaper and unambiguous to check first; a generic decl's
unification is only attempted when nothing closed already matched. -/
partial def foldDataTy (ctors : List (String × CtorInfo)) (gen : List (String × GenData)) (τ : VT) :
    Option String :=
  match τ with
  | .mu body =>
      -- monomorphic: any ctor's `dataTy` (params = []) that equals this μ names its decl.
      match ctors.find? (fun (_, ci) => ci.params.isEmpty && vtyOf ci.dataTy == τ) with
      | some (_, ci) => some ci.dataName
      | none =>
        -- generic: try each decl's ctors as ONE right-nested sum-of-products template (mirrors
        -- `monoData`'s own `sumOfTys (openPays.map prodOfTys)` construction) unified against `body`.
        gen.findSome? (fun (dname, gd) =>
          if gd.params.isEmpty then none else
          let template := sumOfTys (gd.ctors.map (fun c => prodOfTys c.2))
          match unifyDataTy dname template body with
          | none      => none
          | some σ    =>
              -- every declared param must have resolved (a template mentioning fewer params than
              -- declared is a decl the fold doesn't recognize — fall through to the raw μ, never a
              -- partial/misleading name).
              let args := gd.params.mapM (fun p => σ.lookup p)
              -- a multi-word rendered arg (`List Int`) is PARENTHESIZED as an application argument
              -- (`Result Unit (List Int)`, not the ambiguous `Result Unit List Int`) — mirrors
              -- `Format.showTy`'s own `parenIf need .atom` convention for `.tApp` args.
              let parenArg (s : String) : String := if s.contains ' ' then s!"({s})" else s
              args.map (fun vs => s!"{dname} " ++ String.intercalate " " (vs.map (fun v => parenArg (showBoundArg ctors gen v))))
        )
  | _ => none

/-- `foldDataTy`, falling back to a STRUCTURAL walk (never the raw `showVTy` wholesale) when `τ`
itself doesn't match a decl — mirrors `showVTy`'s OWN recursive shape (`.sum`/`.prod`/`.U`/etc)
but recurses through `foldDataTyOrRaw`/`foldCTyOrRaw` at every position instead of `showVTy`/
`showCTy`, so a data type BURIED inside a non-matching outer shape still folds (`Thunk!{Div} Int ->
List Int -> Int`, a `let rec`'s `.U`-wrapped arrow type — `safeAt`'s own signature — needs its
`.arr`-nested `List Int` to fold even though the OUTER `.U` itself is not itself a `data` type).
Falling back to bare `showVTy` at the top would lose the fold the instant ONE non-data wrapper
(`.U`, an arrow, a bare product) sits between the checked type and the buried `data` position —
exactly `safeAt`'s case. `showVTy`/`showCTy` themselves stay UNCHANGED (the raw structural
printer; `display`'s decl-free source path and the internal `#guard`s asserting kernel-level
shapes with no backing `data` decl keep their exact existing behavior — this function is the ONLY
decl-aware entry, never called from `showVTy`/`showCTy`'s own recursion). -/
partial def foldDataTyOrRaw (ctors : List (String × CtorInfo)) (gen : List (String × GenData)) (τ : VT) :
    String :=
  match foldDataTy ctors gen τ with
  | some name => name
  | none =>
    match τ with
    | .int      => "Int"
    | .unit     => "Unit"
    | .sum a b  => s!"({foldDataTyOrRaw ctors gen a} + {foldDataTyOrRaw ctors gen b})"
    | .prod a b => s!"({foldDataTyOrRaw ctors gen a} * {foldDataTyOrRaw ctors gen b})"
    | .U φ b    => let r := showRow φ; s!"Thunk{if r.isEmpty then "" else s!"!\{{r}}"} {foldCTyOrRaw ctors gen b}"
    | .cap ℓ    => s!"Cap {ℓ}"
    | .mu a     => s!"(mu. {foldDataTyOrRaw ctors gen a})"   -- an unmatched μ (no backing decl) still folds its INSIDE
    | .tvar n   => s!"#{n}"

/-- `showCTy`'s DECL-AWARE sibling: recurses through the arrow/returner shape exactly like
`showCTy` (a returner displays as its value type; an arrow prints domain -> codomain), folding
EVERY value position through `foldDataTyOrRaw` rather than the raw `showVTy` — so a data type
buried inside an arrow (`List Int -> Int`, `safeAt`'s own signature) folds too, not just a bare
returner. Lives in the SAME `mutual` group (calls `foldDataTyOrRaw` above, which calls this back
for a `.U`-wrapped computation body — the two are mutually recursive, mirroring `showVTy`/
`showCTy`'s own original mutual group exactly). -/
partial def foldCTyOrRaw (ctors : List (String × CtorInfo)) (gen : List (String × GenData)) :
    CT → String
  | .F _ a     => foldDataTyOrRaw ctors gen a
  | .arr _ a b => s!"{foldDataTyOrRaw ctors gen a} -> {foldCTyOrRaw ctors gen b}"
end

/-- `showType`'s DECL-AWARE sibling (issue #100): the SAME `! \{…}` row-suffix convention, but the
value/arrow shape renders through `foldCTyOrRaw` — every `query type`/hover/checker-error site that
has an `ElabEnv` (or just its `ctors`/`gen` tables) in scope should call THIS, not `showType`. -/
def showTypeD (ctors : List (String × CtorInfo)) (gen : List (String × GenData)) (B : CT)
    (φ : EffRow) (effects : List (String × EffectInfo) := []) : String :=
  let r := showRow φ effects
  let body := foldCTyOrRaw ctors gen B
  if r.isEmpty then body else s!"{body} ! \{{r}}"

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
  monoData env.gen env.aliases env.effects 1000 ci.dataName markers

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
  -- #97 item 2: a nested MUTUAL `let rec … and …` group is NOT analyzed for structural descent —
  -- `structOK`'s call-recognizer (`callSpine`) is keyed on a SINGLE function name and cannot
  -- attribute a sibling's self-calls back to per-function descent (the design note's explicitly
  -- flagged, unscoped judgment call: mutual groups conservatively default to `Div` for v1).
  -- Refuse to certify (soundness > completeness) — the SAME discipline `.lettMulti`/
  -- `.handleCustomS` already use for a shape this checker hasn't been extended to read.
  | .letRecMultiS .. => false
  | .lettMulti .. => false  -- unreachable in practice (elabProg erases #68's sugar first); refuse to certify (soundness > completeness)
  | .handleCustomS .. => false  -- #21 s7probe: NOT yet analyzed for #47/ADR-0091 recursion shapes (clause bodies, the carried param) — conservatively refuse to certify (under-certify, never guess)
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
`Rec = μX. Thunk(X -> T)`; the self-knot `{ let #g = unfold sv in ($#g) (fold #g) } : Thunk T`
reconstructs `f` from a self-value (`unfold` returns a RETURNER of the thunk, so it is let-bound
before forcing — the #45 spike's shape). The OUTER knot (the user's call-site binding) is
`divMark`-wrapped when `recRow` is nonempty (see `letRecRow`) → `f : Thunk ! {Div} T`, so
`($f) x : … ! {Div}` (Div rides the `U`/judgment per ADR-0019/0020, NOT the arrow). The INNER knot
stays pure so `recTy`'s `tThunk` (⊥) annotation holds. Emits only ordinary `Surf` the existing
checker + kernel handle.

**`(fold #g)` NOT `sv` as the self-argument (#95 fix, the knot-SHARING encoding).** The self-
application needs TWO things at `sv`'s type `Rec`: the unfolded function (`unfold sv`, forced via
`#g`) AND `sv` ITSELF again, to hand the callee its own knot back. The ORIGINAL encoding wrote the
SECOND occurrence as a bare `sv` — a second free reference to the SAME (growing, embedded) outer
binder. The kernel's substitution (`Comp.substFrom`/`Val.substFrom`, `Bang/Core/Semantics/Subst.lean`
— proof-bearing, untouched here) has NO sharing: whenever the ENCLOSING binder for `sv` fires
(every re-entrant unfold), it copies `sv`'s bound value into EVERY free occurrence independently —
`unfold sv` AND `… sv` each got their OWN full copy, and because `sv`'s value is `fold {inner}`
(the WHOLE recursive closure, `inner` embedding the newly-unfolded `f`-thunk from the PREVIOUS
level), each level's copy-of-a-copy compounded the residual ~2× per unfold — a `2^depth` blowup on
deep re-entrant knots (issue #95; `docs/notes/dogfood-calc-findings.md` wall 1, `scratch/calc95/`).
`fold #g` replaces the SECOND `sv`-reference with `#g` (the just-`unfold`ed, freshly LOCAL binding)
re-wrapped in `fold` — semantically identical (`fold (unfold sv) = sv` by the fold/unfold iso,
ADR-0029) but SYNTACTICALLY it removes `sv` as a free variable from the app-argument position
entirely: the ENCLOSING (growing) `sv` substitution now touches exactly ONE occurrence (`unfold
sv`'s operand) per level, not two, so the per-level residual stays CONSTANT-SIZE instead of
doubling — turning the `2^depth` blowup into `O(depth)`. Measured: `examples/calc/main.bang` on
`--compiled` 873s → ~7s (same value, `11021193`); `scratch/calc95/README.md` has the full
before/after table. -/
def buildLetRec (name : String) (t' : Ty) (funBody' bodyExpr' : Surf) (recRow : EffRow) : Surf :=
  let recTy : Ty := .tMu (.tThunk (.tArr (.tVar 0) t'))     -- μX. Thunk(X -> T)
  let knotBody : String → Surf := fun sv =>
    .lett "#g" (.unfoldS (.var sv)) (.app (.force (.var "#g")) (.foldS (.var "#g")))
  let inner : Surf := .annotS (.lam "#self" (.lett name (.thunk (knotBody "#self")) funBody')) (.tArr recTy t')
  let recVal : Surf := .annotS (.foldS (.thunk inner)) recTy
  let outerKnot : Surf :=                                     -- Div rides the outer (call-site) thunk
    if divLabel ∈ recRow then .thunk (.divMark (knotBody "#rec")) else .thunk (knotBody "#rec")
  .lett "#rec" recVal (.lett name outerKnot bodyExpr')

/-- Right-nest a `Ty` list into ONE product type, `n ≥ 2`: `[T1, T2] ↦ T1 * T2`, `[T1, T2, T3] ↦
T1 * (T2 * T3)`, … — the `splitProd`/`prodOfTys` right-nested-product convention already used for
ctor payloads (ADR-0069/#50), reused here for the H2 μ-knot's pair-of-thunks slot. `[]`/singleton
are unreachable from `buildLetRecMulti`'s own caller (≥ 2 siblings, `elabS`'s `.letRecMultiS` arm
only reaches this with a genuine `and`-chain) — `[t]` degenerates to `t` defensively rather than
poisoning, `[]` is truly unreachable (a bare `.tUnit` placeholder, never hit). -/
def prodOfTysN : List Ty → Ty
  | []        => .tUnit
  | [t]       => t
  | t :: rest => .tProd t (prodOfTysN rest)

/-- Right-nested `splitS`-chain projecting slot `i` (0-indexed) of an `n`-way product bound to
`pv`, running `body` with `slot` bound to the `i`-th component — the `navSum`/`splitProd`
eliminator-descent precedent, specialized to `splitS`'s BINARY elimination (bang has no N-ary
`split`, so an `i > 0` projection walks `i` nested `splitS`s, discarding the FST half each time via
a throwaway `#drop` binder and re-binding `pv` to the SND remainder — `splitS a b p body` is `a =
fst, b = snd`). `n = 1` (a degenerate 1-sibling group; `prodOfTysN`'s own `[t] ↦ t` case) binds the
WHOLE value directly, no split. **The bug this replaced**: the ORIGINAL version short-circuited on
`i + 1 >= n` (the LAST overall index) *before* checking whether any discards had actually happened
yet — for `n = 2, i = 1` that fired on the FIRST call, binding `slot := pv` to the STILL-WHOLE pair
(never having split off slot 0's fst), which type/runtime-failed as `force: not a thunk` (the pair
itself forced, not its snd component) — confirmed live via `bang check`/`bang run` on a 2-sibling
smoke test. The fix: recurse on `n` ALONE (not `i` vs `n` jointly) — `n = 1` is the true base case
(the current `pv` IS the target, whatever `i` started as), and every OTHER step discards fst,
decrements `n`, and recurses on `i - 1` (or `i` itself when `i = 0`, since `i = 0, n > 1` still
needs ONE split to peel off `#slot` from `#drop`). -/
def projectSlot (pv : String) (i n : Nat) (slot : String) (body : Surf) : Surf :=
  if n <= 1 then .lett slot (.var pv) body                          -- degenerate: the value IS the slot
  else if i == 0 then .splitS slot "#drop" (.var pv) body           -- peel fst = the target, done
  else
    -- unique per-depth name for the SND remainder (`#p{n}`, `n` strictly decreasing) — NOT a bare
    -- re-bind of `pv` itself, so no level's `#drop`/remainder can shadow an OUTER level's binder of
    -- the SAME literal name (debugging measure for a live `effect row mismatch` wall; ruling out
    -- accidental name capture through the projection chain before looking elsewhere).
    let pv' := s!"#p{n}"
    .splitS "#drop" pv' (.var pv) (projectSlot pv' (i - 1) (n - 1) slot body)

/-- The H2 tuple-of-thunks μ-knot (#97 item 2, `docs/notes/mutual-rec-design.md`): generalizes
`buildLetRec`'s single self-knot `Rec = μX. Thunk(X → T)` to an N-tuple self-knot `Rec = μX.
Thunk(X → T1 * T2 * … * Tn)` (right-nested product, `prodOfTysN`) so EVERY sibling forces the SAME
shared knot and projects its own slot (`projectSlot`) — giving every sibling visibility of every
OTHER sibling by construction, not by ordering (H1's Bekić-dispatcher alternative was REFUTED on
two independent walls: ctor/generic arity ≤ 2, `Div`-row all-or-nothing certification; see the
design note + the ADR). `names`/`tys`/`bodies'` are PARALLEL lists (sibling order, already
elaborated); `bodyExpr'` is the trailing `in …` tail.

**The CBPV double-thunk trap (probe-banked, `mutual-rec-design.md` finding 2):** each sibling's
re-derivation thunk (`sibThunk` below) MUST `force` its projected slot before returning — a
naive `splitS … in #slot` (no `force`) types "fine" at each isolated sub-step (the checker's
structural unification silently accepts a `U (U ρ arrow)` thunk-of-a-thunk mismatch) but RUNS to
`STUCK`. `sibThunk`'s `.force (.var slot)` is that fix, made structural here so no future N-way
caller can omit it — `scratch/H2Spike-VERIFIED-GREEN.lean`'s `evenThunk`/`oddThunk` is the
byte-for-byte precedent this generalizes. Every sibling REQUIRES its own mandatory type ascription
(ADR-0073's rule generalized — HM cannot break the mutual circularity without one; the grammar
enforces this at parse time, `pLetRecBindings`).

**`Div`-row placement**: mirrors `buildLetRec`'s OWN split exactly — the INNER knot (every
sibling's re-derivation thunk INSIDE `inner`'s own self-referential body) stays PURE (`recTy`'s
`tThunk` (⊥) annotation depends on this, `buildLetRec`'s placement note, #46), while EVERY
sibling's OUTER (call-site) thunk is `divMark`-wrapped when `recRow` is nonempty. `structOK` has
NOT been extended to certify a co-recursive NAME SET (the design note's flagged, unscoped judgment
call), so `elabS`'s `.letRecMultiS` arm always passes a nonempty `recRow` for v1 (every mutual
group defaults to `Div`, sound per `structOK`'s own "default false" discipline) — the extension
point for a future per-sibling/per-group structural certification is `letRecRow`'s call site in
`elabS`, not here (this function stays a pure ENCODING parametrized by `recRow`, mirroring
`buildLetRec`'s own separation of concerns). -/
def buildLetRecMulti (names : List String) (tys : List Ty) (bodies' : List Surf) (bodyExpr' : Surf)
    (recRow : EffRow) : Surf :=
  let n := names.length
  let pairTy : Ty := prodOfTysN tys
  let recTy : Ty := .tMu (.tThunk (.tArr (.tVar 0) pairTy))    -- μX. Thunk(X → T1 * T2 * … * Tn)
  let knotBody : String → Surf := fun sv =>                     -- BYTE-IDENTICAL to buildLetRec's
    .lett "#g" (.unfoldS (.var sv)) (.app (.force (.var "#g")) (.foldS (.var "#g")))  -- own #95-fixed shape
  -- one re-derivation thunk PER sibling: force the shared knot, project + FORCE this sibling's slot
  -- (the double-thunk trap fix, this function's own doc comment). `marked` selects `divMark` on the
  -- knot re-derivation call — `false` for the INNER (self-referential) use, `true` for the OUTER
  -- (call-site) use when `recRow` carries `Div`, exactly `buildLetRec`'s own inner/outer split.
  let sibThunk : Bool → Nat → String → Surf := fun marked i sv =>
    let kb := if marked && divLabel ∈ recRow then .divMark (knotBody sv) else knotBody sv
    .lett "#p" (.force (.thunk kb))
      (projectSlot "#p" i n "#slot" (.force (.var "#slot")))
  let indexed : List (Nat × String × Ty) := (List.range n).zip (names.zip tys)
  -- bind EVERY sibling name to an `.annotS`-ascribed thunk (`Thunk Ti`) — the H2 spike's OWN
  -- verified shape (`H2Spike-VERIFIED-GREEN.lean`'s `evenThunk`/`oddThunk` bindings, BOTH inner
  -- and outer, mandatory per ADR-0073's rule generalized).
  let rec bindSiblings : Bool → String → List (Nat × String × Ty) → Surf → Surf
    | _,      _,  [],               tail => tail
    | marked, sv, (i, nm, ty) :: rest, tail =>
        Surf.lett nm (.annotS (.thunk (sibThunk marked i sv)) (.tThunk ty)) (bindSiblings marked sv rest tail)
  -- the pair VALUE itself: right-nested `pairS` of each sibling's OWN thunked body (already
  -- elaborated `bodies'`), mirroring `buildLetRec`'s `funBody'` slot but N-wide.
  let rec pairVal : List Surf → Surf
    | []        => .unitS
    | [b]       => .thunk b
    | b :: rest => .pairS (.thunk b) (pairVal rest)
  -- #119 FIXED: the pair tail used to need an EXTRA `.annotS`-wrap at its own construction site
  -- (not just at `inner`'s outer `.tArr recTy pairTy`) to force `checkSC`'s EXPLICIT `.annotS` arm
  -- (subsumption-aware) instead of the generic catch-all, which used to unify rows by EXACT
  -- equality when the tail was a `.lett`-chain ending in a bare `.pairS`. `checkSC`'s catch-all
  -- (and `checkSV`'s) now route through `subsumeC`/`subsumeV` — row-subsumption-aware at every
  -- nested `.U`, not just the top-level `.annotS` site — so the inner wrap is no longer load-bearing
  -- (verified: removing it still passes `just verify`'s corpus, incl. this function's own #guards).
  let inner : Surf :=
    .annotS (.lam "#self" (bindSiblings false "#self" indexed (pairVal bodies'))) (.tArr recTy pairTy)
  let recVal : Surf := .annotS (.foldS (.thunk inner)) recTy
  .lett "#rec" recVal (bindSiblings true "#rec" indexed bodyExpr')

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

/-- Qualify one module's identifier: `modname_name` (an ordinary identifier — no new token/AST
node). `_` needs no tokenizer change (already a legal identifier char, nothing in `tokenize`
splits on it), unlike `modname.name` which would collide with the LIVE `.dotPerform` token.
Hoisted here (ahead of its original `## Modules` section, unchanged definition) so `resolveCtor`
below — needed by the `elabS`/`elabArms` mutual block, which precedes `## Modules` in file order —
can reuse the SAME qualification scheme for `Type_Ctor` (ADR-0099) rather than duplicating it. -/
def qualifyName (modName name : String) : String := s!"{modName}_{name}"

/-- **ADR-0099**: resolve a bare (or `Type_Ctor`-qualified) constructor reference against `env.ctors`.
A ctor's true key is `(dataName, ctorName)`, not the bare name alone — `env.ctors` still stores every
entry flat (unchanged representation), so resolution moves from registration-time refusal to a
USE-time lookup here. **Tries the QUALIFIED spelling FIRST** (some candidate whose
`dataName ++ "_" ++ ctorName` — the `qualifyName` convention, ADR-0093 — equals `x` exactly): this
must run before the bare-name filter, since a qualified reference like `IntList_Cons` shares NO bare
ctor name with anything (`candidates` on the bare name alone would be `[]`, wrongly falling through
to "not a ctor"). Only once no candidate's qualified spelling matches does it fall back to the
bare-name ambiguity-set filter (every candidate whose OWN `ctorName` equals `x`): 0 ⟹ `none` (not a
ctor at all, falls through to ordinary var/application handling unchanged); exactly 1 ⟹ that one,
byte-identical to today's `.lookup` for every unambiguous reference; 2+ ⟹ **B012**, `.error` carrying
the full candidate list (dataName × qualified spelling pairs) for the diagnostic to name every
candidate + its fix. -/
def resolveCtor (env : ElabEnv) (x : String) : Option (Except String CtorInfo) :=
  match env.ctors.find? (fun p => qualifyName p.2.dataName p.1 == x) with
  | some ci => some (.ok ci.2)
  | none    =>
      match env.ctors.filter (fun p => p.1 == x) with
      | []   => none
      | [ci] => some (.ok ci.2)
      | cs   =>
          let owners := cs.map (fun p => s!"{p.2.dataName} (as '{qualifyName p.2.dataName p.1}')")
          let ownersStr := String.intercalate ", " owners
          some (.error s!"ambiguous constructor '{x}' — candidates: {ownersStr}")

/-- **#101**: expand a match's wildcard arm `_ -> body` (if present) into one fresh arm per
constructor of the scrutinee's data type NOT already covered by an earlier, EXPLICIT arm — so
every downstream consumer (`elabArms`'s binder typing, the `matchD` arm's `dcs`/`ordered`
exhaustiveness loop) sees an ordinary fully-explicit `DArms` and needs NO wildcard awareness of
its own (one preprocessing seam, zero blast radius on the existing pipeline). Fresh binder names
(`"_w0"`, `"_w1"`, …, sized to each missing ctor's arity) are unused by construction — the
wildcard body binds nothing, so reusing it verbatim under fresh names is safe (no capture: these
names cannot appear free in `body`, since `body` was parsed BEFORE any of them were minted).

The data type is resolved from the FIRST EXPLICIT arm's ctor (`resolveCtor`, ADR-0099) — the
SAME anchor `matchD`'s own post-`elabArms` validation already uses for `c0`; a wildcard is
therefore only resolvable when at least one explicit ctor arm exists to name the type (a
`match s { _ -> e }` with zero explicit arms has no textual anchor — B014, distinct from the
dead-arm case).

Errors (both routed to codeForMsg **B014**, ADR-friendly wording chosen so both anchor on
`"wildcard arm"`):
- `_` appears before the LAST arm: reachability violates the ADR-0069 elimination shape (arms
  after a `_` in decl order are never reached — the SAME "would never fire" property a trailing
  catch-all guarantees in every ML-family match).
- `_` covers ZERO ctors (every ctor already has an explicit arm): dead code, not an error the
  writer intended — the ADR-0069 exhaustiveness check would have accepted the match without it. -/
def expandWildcardArms (env : ElabEnv) (arms : DArms) : Except String DArms := do
  let armsL := armsToList arms
  -- no wildcard at all: pass through unchanged (the overwhelmingly common case, zero cost).
  if !armsL.any (fun a => a.1 == "_") then return arms
  -- reject a non-last wildcard BEFORE anything else (a clear position, independent of whether the
  -- data type even resolves) — `List.findIdx?` locates it; anything after that index is dead.
  let wIdx := armsL.findIdx (fun a => a.1 == "_")
  if wIdx != armsL.length - 1 then
    throw "wildcard arm '_' must be the LAST arm in a match — arms after it can never fire (unreachable)"
  let explicit := armsL.take wIdx   -- every arm before the wildcard (already ctor-named, by construction)
  let (_, _, wBody) := armsL[wIdx]!
  match explicit with
  | [] => throw "wildcard arm '_' needs at least one explicit constructor arm to name the match's data type"
  | (c0, _, _) :: _ =>
    match resolveCtor env c0 with
    | none            => throw s!"unknown constructor '{c0}' in match"
    | some (.error e) => throw e                          -- ADR-0099 B012, unchanged precedent
    | some (.ok ci0)  => do
      let dcs := (env.ctors.filter (fun p => p.2.dataName == ci0.dataName)).map Prod.snd
      let dcs := (dcs.toArray.qsort (fun a b => a.idx < b.idx)).toList
      let covered (cn : String) : Bool :=
        explicit.any (fun a => a.1 == cn || a.1 == qualifyName ci0.dataName cn)
      let missing := dcs.filter (fun ci =>
        match env.ctors.find? (fun p => p.2.dataName == ci.dataName && p.2.idx == ci.idx) with
        | some (cn, _) => !covered cn
        | none         => false)
      if missing.isEmpty then
        throw "wildcard arm '_' covers no constructors — every constructor of this data type already has an explicit arm (dead code)"
      let freshArms := missing.map (fun ci =>
        match env.ctors.find? (fun p => p.2.dataName == ci.dataName && p.2.idx == ci.idx) with
        | some (cn, _) => (cn, (List.range ci.arity).map (fun i => s!"_w{ci.idx}_{i}"), wBody)
        | none         => (s!"#impossible", [], wBody))   -- unreachable: `missing` built from the same `dcs`
      return toDArms (explicit ++ freshArms)

/-- A-normalize a VALUE-position subterm (#41), mirroring `lowerV`-or-`letC` in `Surface.lower` but
at the NAMED elaboration layer (no de-Bruijn shift — a fresh binder just extends `Γ`). Returns the
extended context, a `let`-prefix to wrap around the enclosing construct, and the value-`Surf` to use
in the value slot: a syntactic value passes through (`id` prefix); a computation is bound under a
fresh `#anf`-name (its returner payload type in `Γ`), lifting it ABOVE the construct (so e.g. a
ctor's fold still wraps a VALUE). A non-returner is left for the checker; an untypeable RHS surfaces
its REAL error, not a downstream "unbound variable" (the #41 diagnostic). Fresh names key on `Γ.length`
and shadow innermost-first (as `lower`'s own sentinels do), so nested/sibling binds stay correct.
`effects` (ADR-0092 D2, #21 s7probe WALL-3-class fix, default `[]`): threaded to `zonkInferC`'s
throwaway `synthSC` probe — see that function's own doc comment for the bug this closes (found live
via the ADR-0095 tracer bullet: `net.fetch(1) + 1` A-normalizes the `.binopS`'s left operand through
HERE, and without `effects` the probe wrongly rejected the already-well-typed `.dotPerform`). -/
def anfSplit (Γ : NCtx) (e' : Surf) (effects : List (String × EffectInfo) := []) : Except String (NCtx × (Surf → Surf) × Surf) :=
  if isValueSurf e' then .ok (Γ, id, e')
  else match zonkInferC (synthSC Γ e') effects with
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
use, exactly like the final check. `none` = the RHS is not a returner (and not a higher-order `chole`).

`effects` (ADR-0092 D2, #21 s7probe fix): the throwaway `synthSC Γ e'` call reaches the SAME
`.dotPerform`/`handleCustomS` D2 arms the OUTER `runInferC` call does, and THOSE need `USt.effects` —
`.run' {}` was seeding a completely FRESH, EMPTY-effects `USt` for this inner run, invisible until now
because NO built-in `.dotPerform` op consults `USt.effects` (built-ins resolve via the pure, state-free
`capOpSig`), so the gap had no live consumer before a user-effect `let`-RHS existed. THE MECHANICS
FINDING: a `let`-bound RHS naming a user-effect `perform`/`handleCustomS` construct went through this
UNTHREADED throwaway inference and got a WRONG diagnostic (`receiver's capability label is not a
declared effect` — a genuine false negative, not the real error) instead of typing correctly — found
LIVE by the #21 e2e probe (`let r = h.fetch(5) in r`, `bang check`), not a hypothetical. -/
def elabBind (Γ : NCtx) (e' : Surf) (effects : List (String × EffectInfo) := []) : Except String (Option Scheme) :=
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
  ).run' { effects := effects }

/-- Peel matching `fun`/`->` layers of an ASCRIBED curried lambda, binding EVERY parameter to its
annotated domain — not just the outermost. So a nested `fun g => …` inside `(fun f => fun g => … :
A -> B -> C)` also sees `g : B`; `elabS`'s `.lam` arm threads this extended `Γ` unchanged into the
nested bodies, so `anfSplit` inside a curried fun can synthesize a computation ARGUMENT's type
(`($g) x`) instead of failing on an unbound param. -/
def curryBind : NCtx → Surf → Ty → NCtx
  | Γ, e,          .tEff _ t   => curryBind Γ e t
  | Γ, e,          .tEffR _ t  => curryBind Γ e t   -- #90: the RESOLVED row form — by the time
                                  -- `curryBind` runs (post-`resolveTyG`), a `.tEff` ascription has
                                  -- ALREADY become `.tEffR` — this arm was missing, so a row-annotated
                                  -- arrow (`Cap Net -> Int ! {Net}`) silently fell through to the
                                  -- catch-all (no binding at all), the exact cause of a cap-typed
                                  -- param losing its `Cap ℓ` binding the moment a row was attached.
  | Γ, .thunk e,   .tThunk t   => curryBind Γ e t   -- #84 gap 1: `{fun … => …} : Thunk (A -> B)` —
                                  -- the ONLY v1 surface form that binds a function (a bare un-thunked
                                  -- `fun` is "not a returner", confirmed #4698's own precedent) — peel
                                  -- the thunk/`Thunk` layer together, then fall through to the `.lam`/
                                  -- `.tArr` case below exactly as the un-thunked ascription already does
  | Γ, .lam x b,   .tArr aT bT => curryBind ((x, (embV (vtyOf aT) : IVTy)) :: Γ) b bT
  | Γ, _,          _           => Γ
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
  let Tv := vtyOf (← resolveTy env.gen env.aliases t env.effects)         -- the annotation IS the carrier T
  let some rimpl := env.rawImpls.find? (fun r => r.traitName == bfn.traitName && r.targetVT == Tv)
    | throw s!"no impl of '{bfn.traitName}' for {foldDataTyOrRaw env.ctors env.gen Tv} — the bound '{bfn.traitName} {bfn.tyVar}' is unsatisfied"
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
  | f + 1, .letRecMultiS binds b => do
      return .letRecMultiS (← expandLetRecBindings env carrier? f binds) (← expandBFns env carrier? f b)
  | f + 1, .dotPerform recv op args => do return .dotPerform (← expandBFns env carrier? f recv) op (← expandArgs env carrier? f args)
  | f + 1, .matchD s arms => do
      -- #101: expand a trailing `_` wildcard arm into its missing ctors' arms HERE (this pre-pass,
      -- not `elabS`'s `.matchD` arm) — `expandBFns` already walks the whole tree with `env` in scope
      -- and is fuel-driven (not `sizeOf`-based), so it is the one place a rewrite that can GROW the
      -- arm list is unremarkable; interleaving it into the `elabS`/`elabArms` mutual block instead
      -- breaks that block's structural termination proof (confirmed by a failed build attempt: the
      -- expansion violates `sizeOf (expanded arms) ≤ sizeOf arms0`). Body expansion (`expandArms`,
      -- bounded-fn splicing) then proceeds over the ALREADY-explicit result, unchanged.
      let arms ← expandWildcardArms env arms
      return .matchD (← expandBFns env carrier? f s) (← expandArms env carrier? f arms)
  | f + 1, .lettMulti binds b => do return .lettMulti (← expandLetBindings env carrier? f binds) (← expandBFns env carrier? f b)
  -- #21 s7probe: `handleCustomS` recurses structurally, mirroring `.withCapS`/`.matchD` above —
  -- `n`/`p`/`body` expand directly; `cls` needs the SAME `DArms`-precedent sibling (`expandHClauses`,
  -- below `expandArms`) since bounded-fn expansion is a DIFFERENT concern from typing (this pass has
  -- no termination-measure conflict with `synthSC`'s wall — `expandBFns` is ALREADY fuel-driven, not
  -- `sizeOf`-based, so a mutual `List`/`HClauses` sibling here is unremarkable, unlike the typing arm).
  | f + 1, .handleCustomS lbl n p? h cls b => do
      return .handleCustomS lbl (← expandBFns env carrier? f n) (← expandArgs env carrier? f p?) h
        (← expandHClauses env carrier? f cls) (← expandBFns env carrier? f b)
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

/-- #21 s7probe: `HClauses` expansion (custom-handle clause bodies) — the `expandArms` precedent. -/
def expandHClauses (env : ElabEnv) (carrier? : Option String) : Nat → HClauses → Except String HClauses
  | 0,     _              => .error "bounded-fn expansion out of fuel"
  | _ + 1, .nil           => .ok .nil
  | f + 1, .cons op x b r => do return .cons op x (← expandBFns env carrier? f b) (← expandHClauses env carrier? f r)

/-- `LetBindings` expansion (issue #68's `;`-binding list). -/
def expandLetBindings (env : ElabEnv) (carrier? : Option String) : Nat → LetBindings → Except String LetBindings
  | 0,     _              => .error "bounded-fn expansion out of fuel"
  | _ + 1, .nil           => .ok .nil
  | f + 1, .cons n e rest => do return .cons n (← expandBFns env carrier? f e) (← expandLetBindings env carrier? f rest)
/-- `LetRecBindings` expansion (#97 item 2 mutual `let rec … and …` sibling list) — the
`expandLetBindings` precedent. -/
def expandLetRecBindings (env : ElabEnv) (carrier? : Option String) : Nat → LetRecBindings → Except String LetRecBindings
  | 0,     _                => .error "bounded-fn expansion out of fuel"
  | _ + 1, .nil              => .ok .nil
  | f + 1, .cons n t e rest  => do return .cons n t (← expandBFns env carrier? f e) (← expandLetRecBindings env carrier? f rest)
end

/-- One `let rec … and …` sibling (#97 item 2) AFTER its declared `Ty` is resolved and its function
literal is peeled — `name`, the resolved `T`, the param name, the UN-elaborated param body, and the
resolved param-domain `IVTy` (mirrors `.letRecS`'s own inline `t'`/`dom` locals). -/
structure LRResolved where
  name : String
  ty   : Ty
  pn   : String
  pbody : Surf
  dom  : IVTy

/-- Resolve every sibling's declared `Ty` + peel its function literal (#97 item 2) — pure w.r.t.
`elabS` (no elaboration of any BODY happens here, only `resolveTy` + the `.lam` peel), so this sits
OUTSIDE the `elabS` mutual block entirely; `elabLetRecBindings` (inside the block, below) is the
sibling that actually elaborates each `pbody`, recursing over the ORIGINAL `LetRecBindings` tree
(not this `List`) — Lean's mutual structural-recursion inference needs every sibling's decreasing
argument to share a KNOWN-related type across the whole `elabS`/`elabArms`/`elabHClauses` group; a
freshly-invented `List LRResolved` carrier broke that unification (confirmed: build failed
"Cannot use parameters …" until this list stayed a QUERY table, `elabLetRecBindings` structurally
recursing on `LetRecBindings` itself — the `elabHClauses`/`HClauses` precedent). A non-function
sibling throws immediately (mirrors `.letRecS`'s own "requires a function literal" arm). -/
def resolveLetRecBindingTys (env : ElabEnv) : LetRecBindings → Except String (List LRResolved)
  | .nil               => .ok []
  | .cons nm t fb rest => do
      let t' ← resolveTy env.gen env.aliases t env.effects
      match fb with
      | .lam pn pbody =>
          let dom : IVTy := match tyBoth t' with
            | (_, .arr _ A _) => embV A
            | _               => .tvar 997                      -- POISON: T not a function → fails loud below
          let rest' ← resolveLetRecBindingTys env rest
          return ⟨nm, t', pn, pbody, dom⟩ :: rest'
      | _ => throw s!"mutual let rec sibling '{nm}' requires a function literal: `{nm} : T = fun x => …` (#97 item 2, ADR-0073's rule generalized)"

/-- Every resolved sibling's `f : Thunk T` binding, in order — `letRecMultiS`'s Γ-extension
(mirrors `.letRecS`'s single `(name, uT)`, generalized to N). -/
def letRecBindingUTys : List LRResolved → List (String × Scheme)
  | []      => []
  | r :: rs => (r.name, ({ body := .U botR (embC (ctyOf r.ty)) } : Scheme)) :: letRecBindingUTys rs

def letRecResolvedNames : List LRResolved → List String := List.map (·.name)
def letRecResolvedTys   : List LRResolved → List Ty     := List.map (·.ty)

/-- Look up a resolved sibling by name — `elabLetRecBindings`'s bridge from a `LetRecBindings`
node's bare name (the recursion carrier) to its pre-resolved `LRResolved` (the query table built
ONCE by `resolveLetRecBindingTys`, threaded read-only through the recursion). `none` is
unreachable (every name in the `LetRecBindings` tree was resolved into `table` by construction —
`elabS`'s own `.letRecMultiS` arm builds `table` from the SAME tree it recurses `binds` over). -/
def lrLookup (table : List LRResolved) (nm : String) : Option LRResolved :=
  table.find? (·.name == nm)

/-! ## Bound-free `let rec` monomorphization (ADR-0103, the #120 List-family door)

A pure `Surf → Surf` pre-pass — the `expandBFns` TWIN, run in `elabProg` alongside it, BEFORE
`elabS` — that discovers the finite call-site instantiation set of a bound-free generic `let rec`
(`let rec length : List a -> Int = …`) and emits one monomorphic residue per element (exactly
witness w3's by-hand shape, auto-generated). By the time this pass returns, every surviving
`.letRecS` ascription is concrete (`freeTyVars` on it is `[]`), so `elabS`'s OWN `.letRecS` arm
(the `resolveTy` chokepoint, TypeCheck.lean's `.letRecS` case) runs completely unchanged — the fix
is upstream of it, never in it, preserving that arm's fail-loud typo-catch for every OTHER caller. -/

/-- Peel a curried call spine rooted at `.force (.var name)`: `($name) v1 v2 … vn` ↦ `some [v1, …,
vn]` (the `callSpine` precedent, generalized to any name — `callSpine` itself stays single-purpose
to `structOK`'s certifier). `none` if `e` is not a call on `name` at all. -/
def monoCallSpine (name : String) : Surf → Option (List Surf)
  | .app (.force (.var g)) a => if g == name then some [a] else none
  | .app f a                 => (monoCallSpine name f).map (· ++ [a])
  | _                        => none

/-- Peel `n` domain arrows off a curried `Ty`, returning the DOMAIN list in order (`List a -> List
a -> Int`, `n=2` ↦ `[List a, List a]`) — the ascription-side twin of `monoCallSpine`'s argument
list, so each call argument lines up positionally with the ascription slot it instantiates. -/
def curriedDomains : Nat → Ty → List Ty
  | 0,     _         => []
  | n + 1, .tArr a b => a :: curriedDomains n b
  | _ + 1, t         => [t]   -- fewer arrows than requested: the tail itself (a shape error downstream)

/-- Discover ONE call site's instantiation of `name`'s free tyvars: line up each curried argument
against its ascription DOMAIN (`domains`, `curriedDomains` already applied by the caller), and for
every argument that is an explicit annotation `(e : T)` — ADR-0103 decision item 3's discovery
anchor, the argument-position twin of `bfnWrapper`'s RESULT-anchored annotation (the fold-shape
wall, w2, is exactly why this family cannot reuse that anchor) — `matchTyVars` the domain template
against `T`. An un-annotated argument contributes nothing at this call (never a guess); the caller
decides whether the union still closes every free tyvar. -/
def discoverAtCall (domains : List Ty) (args : List Surf) : List (String × Ty) :=
  (domains.zip args).flatMap (fun (dom, arg) => match arg with
    | .annotS _ concreteTy => matchTyVars dom concreteTy
    | _                    => [])

mutual
/-- Every call site of `name` found in `e`, in LEFT-TO-RIGHT traversal order, as its raw discovered
binding list (`discoverAtCall`, possibly incomplete — completeness is checked by the caller once
every call site is collected). Exhaustive over every `Surf` former (the `letRecBoundNames`/
`qualifyVars` completeness discipline) — a NESTED `let rec`/`letRecMultiS` re-binding `name` shadows
it exactly as `qualifyVars` shadows a qualified name: the shadowed subtree contributes NO further
call sites (a shadowed inner `name` is a genuinely different binding, never a use of the outer one). -/
partial def callSitesOf (name : String) (domains : List Ty) (e : Surf) : List (List (String × Ty)) :=
  let here := match monoCallSpine name e with
    | some args => [discoverAtCall domains args]
    | none      => []
  here ++ match e with
    | .lit _ | .var _ | .getS | .unitS => []
    | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
    | .lam _ e | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ =>
        callSitesOf name domains e
    | .lett _ a b | .stateS a b | .writeS a b | .pairS a b | .splitS _ _ a b | .binopS _ a b =>
        callSitesOf name domains a ++ callSitesOf name domains b
    | .app a b =>
        -- `monoCallSpine` already counted the WHOLE spine (every curried arg) as ONE call site
        -- (`here`, above) when `e` itself is a call on `name` — but it only ever READS the spine's
        -- shape, never descends INTO an argument's own subterms, so an argument that itself
        -- contains a NESTED `name` call (`f ($length xs : T)`, or `name`'s own arg position holding
        -- another `name` call) still needs `b` walked regardless of whether `e` as a whole is
        -- `name`'s spine. Only `a` needs the "already counted" skip (recursing into it again down
        -- a `name`-spine would re-`monoCallSpine`-match the SAME outer call at every curried layer,
        -- double-counting once per argument) — `b` is always walked, spine or not.
        (if (monoCallSpine name e).isSome then [] else callSitesOf name domains a) ++ callSitesOf name domains b
    | .matchS s _ l _ r => callSitesOf name domains s ++ callSitesOf name domains l ++ callSitesOf name domains r
    | .ifS c t el        => callSitesOf name domains c ++ callSitesOf name domains t ++ callSitesOf name domains el
    | .matchD s arms     => callSitesOf name domains s ++ callSitesOfDArms name domains arms
    | .withCapS _ i _ b  => callSitesOf name domains i ++ callSitesOf name domains b
    | .dotPerform r _ .none      => callSitesOf name domains r
    | .dotPerform r _ (.one a)   => callSitesOf name domains r ++ callSitesOf name domains a
    | .dotPerform r _ (.two a b) => callSitesOf name domains r ++ callSitesOf name domains a ++ callSitesOf name domains b
    | .letRecS n _ f b => callSitesOf name domains f ++ (if n == name then [] else callSitesOf name domains b)
    | .letRecMultiS binds b =>
        callSitesOfLRBindings name domains binds ++
        (if (letRecBindingsNames binds).contains name then [] else callSitesOf name domains b)
    | .lettMulti binds b => callSitesOfBindings name domains binds ++ callSitesOf name domains b
    | .handleCustomS _lbl n .none _h cls b       => callSitesOf name domains n ++ callSitesOfHClauses name domains cls ++ callSitesOf name domains b
    | .handleCustomS _lbl n (.one p) _h cls b    => callSitesOf name domains n ++ callSitesOf name domains p ++ callSitesOfHClauses name domains cls ++ callSitesOf name domains b
    | .handleCustomS _lbl n (.two p q) _h cls b  => callSitesOf name domains n ++ callSitesOf name domains p ++ callSitesOf name domains q ++ callSitesOfHClauses name domains cls ++ callSitesOf name domains b
partial def callSitesOfDArms (name : String) (domains : List Ty) : DArms → List (List (String × Ty))
  | .nil              => []
  | .cons _ _ b rest  => callSitesOf name domains b ++ callSitesOfDArms name domains rest
partial def callSitesOfBindings (name : String) (domains : List Ty) : LetBindings → List (List (String × Ty))
  | .nil            => []
  | .cons _ e rest  => callSitesOf name domains e ++ callSitesOfBindings name domains rest
partial def callSitesOfHClauses (name : String) (domains : List Ty) : HClauses → List (List (String × Ty))
  | .nil               => []
  | .cons _ _ b rest   => callSitesOf name domains b ++ callSitesOfHClauses name domains rest
partial def callSitesOfLRBindings (name : String) (domains : List Ty) : LetRecBindings → List (List (String × Ty))
  | .nil               => []
  | .cons n _ e rest   =>
      (if n == name then [] else callSitesOf name domains e) ++ callSitesOfLRBindings name domains rest
end

/-- Complete every discovered call-site binding against `tvs` (`name`'s free-tyvar list, order-
stable from `freeTyVars`): a binding is COMPLETE iff every `tv ∈ tvs` was pinned by SOME annotation
at that call (`discoverAtCall` may have only pinned a subset, or pinned the SAME var twice — the
LAST occurrence wins, mirroring `List.lookup`'s own first-match convention read right-to-left via
`List.reverse` so a later annotation in a multi-arg call overrides an earlier accidental alias).
`none` ⟹ that call site is unmonomorphizable (some free tyvar never annotated) — the caller fails
LOUD naming it, never silently drops it or guesses. -/
def completeInstantiation (tvs : List String) (binding : List (String × Ty)) : Option (List (String × Ty)) :=
  tvs.mapM (fun tv => (binding.reverse.lookup tv).map (tv, ·))

/-- Assign each COMPLETE call-site instantiation a residue index, collapsing call sites that agree
on every tyvar to the SAME index (`List.idxOf`-style first-match) — the distinct-instantiation-set
discovery ADR-0103 decision item 1 asks for (w3: two calls at different types ⟹ two residues; the
witness's own by-hand shape, here auto-derived). Returns the DISTINCT instantiation list (residue
order = FIRST-SEEN order, so residue naming is deterministic across identical input) paired with,
for EACH original call site, which residue index it belongs to. -/
def indexInstantiations (complete : List (List (String × Ty))) :
    List (List (String × Ty)) × List Nat :=
  complete.foldl (fun (distinct, idxs) binding =>
    match distinct.findIdx? (· == binding) with
    | some i => (distinct, idxs ++ [i])
    | none   => (distinct ++ [binding], idxs ++ [distinct.length])
  ) ([], [])

/-- Redirect ONLY the call HEAD (`.force (.var name)` at the spine root) to `freshName`, leaving
every argument untouched (arguments are rewritten separately, by the caller's own recursion — this
is the `qualifyVars`-style "rename the leaf, recurse elsewhere" split, applied to a call-spine head
instead of a bare variable). -/
partial def redirectHead (name freshName : String) : Surf → Surf
  | .app f a         => .app (redirectHead name freshName f) a
  | .force (.var g)  => if g == name then .force (.var freshName) else .force (.var g)
  | e                => e

mutual
/-- Rewrite `e`, redirecting every call site of `name` to ITS OWN residue's fresh name — a SELF-
CONTAINED single pass (no separate discovery pass to stay in lockstep with, avoiding the two-walk
synchronization hazard a split discover-then-redirect design carries): at a recognized call spine,
RE-DISCOVER that ONE site's binding (`discoverAtCall`, the same call `callSitesOf` makes) and look
it up directly in `residues` (a call's binding, once completed against `tvs`, uniquely determines
its residue by construction — `indexInstantiations` grouped by exactly this equality). An
INCOMPLETE call (some free tyvar unpinned) was already rejected by the caller before any residue
existed, so `lookup` failing here is unreachable in the CALL case; it IS reachable in the SELF-CALL
case (`self? = some freshName`; see `monomorphizeOne`), where every self-reference maps to that one
fixed name regardless of its own (irrelevant — a self-call carries no annotation to rediscover)
binding. Exhaustive over every `Surf` former (the `qualifyVars`/`callSitesOf` completeness
discipline); mirrors `callSitesOf`'s OWN `.app`/shadow treatment exactly (both consult
`monoCallSpine` the same way), but needs no index-threading since each redirect is self-determined. -/
partial def redirectCalls (name : String) (domains : List Ty) (tvs : List String)
    (residues : List (List (String × Ty) × String)) (self? : Option String) : Surf → Surf
  | e =>
    match monoCallSpine name e with
    | some args =>
        let freshName? := match self? with
          | some sn => some sn
          | none    =>
              match completeInstantiation tvs (discoverAtCall domains args) with
              | some sub => (residues.find? (fun (s, _) => s == sub)).map (·.2)
              | none     => none   -- unreachable: the caller already rejected incomplete calls
        let e' := match freshName? with
          | some fresh => redirectHead name fresh e
          | none       => e
        -- an argument may itself contain a NESTED call (same-name or otherwise) needing its own
        -- redirect — `monoCallSpine` only reads the spine's shape, never descends. `args` were
        -- consumed structurally above; redirect each independently (order-irrelevant, no shared
        -- counter to desync).
        redirectArgsInHead name domains tvs residues self? e'
    | none =>
    match e with
    | .lit n => .lit n
    | .var x => .var x
    | .getS  => .getS
    | .unitS => .unitS
    | .thunk e   => .thunk   (redirectCalls name domains tvs residues self? e)
    | .force e   => .force   (redirectCalls name domains tvs residues self? e)
    | .raise e   => .raise   (redirectCalls name domains tvs residues self? e)
    | .handle e  => .handle  (redirectCalls name domains tvs residues self? e)
    | .putS e    => .putS    (redirectCalls name domains tvs residues self? e)
    | .atomS e   => .atomS   (redirectCalls name domains tvs residues self? e)
    | .newS e    => .newS    (redirectCalls name domains tvs residues self? e)
    | .readS e   => .readS   (redirectCalls name domains tvs residues self? e)
    | .inlS e    => .inlS    (redirectCalls name domains tvs residues self? e)
    | .inrS e    => .inrS    (redirectCalls name domains tvs residues self? e)
    | .foldS e   => .foldS   (redirectCalls name domains tvs residues self? e)
    | .unfoldS e => .unfoldS (redirectCalls name domains tvs residues self? e)
    | .divMark e => .divMark (redirectCalls name domains tvs residues self? e)
    | .lam x e   => .lam x   (redirectCalls name domains tvs residues self? e)
    | .annotS e t => .annotS (redirectCalls name domains tvs residues self? e) t
    | .lett x a b     => .lett x (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .stateS a b     => .stateS (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .writeS a b     => .writeS (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .pairS a b      => .pairS (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .splitS x y a b => .splitS x y (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .binopS op a b  => .binopS op (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .app a b        => .app (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b)
    | .ifS c t el     => .ifS (redirectCalls name domains tvs residues self? c) (redirectCalls name domains tvs residues self? t) (redirectCalls name domains tvs residues self? el)
    | .matchS s xl l xr r => .matchS (redirectCalls name domains tvs residues self? s) xl (redirectCalls name domains tvs residues self? l) xr (redirectCalls name domains tvs residues self? r)
    | .matchD s arms  => .matchD (redirectCalls name domains tvs residues self? s) (redirectCallsDArms name domains tvs residues self? arms)
    | .withCapS k i x b => .withCapS k (redirectCalls name domains tvs residues self? i) x (redirectCalls name domains tvs residues self? b)
    | .dotPerform r op .none      => .dotPerform (redirectCalls name domains tvs residues self? r) op .none
    | .dotPerform r op (.one a)   => .dotPerform (redirectCalls name domains tvs residues self? r) op (.one (redirectCalls name domains tvs residues self? a))
    | .dotPerform r op (.two a b) => .dotPerform (redirectCalls name domains tvs residues self? r) op (.two (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? b))
    | .letRecS nm t f b =>
        .letRecS nm t (redirectCalls name domains tvs residues self? f)
          (if nm == name then b else redirectCalls name domains tvs residues self? b)
    | .letRecMultiS binds b =>
        .letRecMultiS (redirectCallsLRBindings name domains tvs residues self? binds)
          (if (letRecBindingsNames binds).contains name then b else redirectCalls name domains tvs residues self? b)
    | .lettMulti binds b => .lettMulti (redirectCallsBindings name domains tvs residues self? binds) (redirectCalls name domains tvs residues self? b)
    | .handleCustomS lbl n p? h cls b =>
        .handleCustomS lbl (redirectCalls name domains tvs residues self? n)
          (match p? with
            | .none    => .none
            | .one p   => .one (redirectCalls name domains tvs residues self? p)
            | .two a c => .two (redirectCalls name domains tvs residues self? a) (redirectCalls name domains tvs residues self? c))
          h (redirectCallsHClauses name domains tvs residues self? cls) (redirectCalls name domains tvs residues self? b)
partial def redirectArgsInHead (name : String) (domains : List Ty) (tvs : List String)
    (residues : List (List (String × Ty) × String)) (self? : Option String) : Surf → Surf
  | .app f a => .app (redirectArgsInHead name domains tvs residues self? f) (redirectCalls name domains tvs residues self? a)
  | e        => e   -- reached the call HEAD (`.force (.var freshOrName)`) — already redirected by the caller
partial def redirectCallsDArms (name : String) (domains : List Ty) (tvs : List String)
    (residues : List (List (String × Ty) × String)) (self? : Option String) : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest => .cons c ps (redirectCalls name domains tvs residues self? b) (redirectCallsDArms name domains tvs residues self? rest)
partial def redirectCallsBindings (name : String) (domains : List Ty) (tvs : List String)
    (residues : List (List (String × Ty) × String)) (self? : Option String) : LetBindings → LetBindings
  | .nil            => .nil
  | .cons n e rest  => .cons n (redirectCalls name domains tvs residues self? e) (redirectCallsBindings name domains tvs residues self? rest)
partial def redirectCallsHClauses (name : String) (domains : List Ty) (tvs : List String)
    (residues : List (List (String × Ty) × String)) (self? : Option String) : HClauses → HClauses
  | .nil               => .nil
  | .cons op x b rest  => .cons op x (redirectCalls name domains tvs residues self? b) (redirectCallsHClauses name domains tvs residues self? rest)
partial def redirectCallsLRBindings (name : String) (domains : List Ty) (tvs : List String)
    (residues : List (List (String × Ty) × String)) (self? : Option String) : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons n t e rest   =>
      .cons n t (if n == name then e else redirectCalls name domains tvs residues self? e)
        (redirectCallsLRBindings name domains tvs residues self? rest)
end

mutual
/-- Apply `qTy : Ty → Ty` to EVERY `Ty` slot embedded in a `Surf` tree — the `qualifyDotAccess`
precedent (TypeCheck.lean, module qualification's own `qTy`-threading), specialized here to just
the type-substitution concern (no dot-access/import qualification, so a dedicated function rather
than reusing `qualifyDotAccess` itself across this file's large forward-distance to it). NEEDED
because a `let rec`'s declared ascription is not the ONLY place its tyvar can appear: the function
BODY may carry its own internal ascriptions mentioning the same var (`match (xs : List a) { … }`,
`fun_hktMultiply.hktMatch`-shaped continuations, …) — `monomorphizeOne` closes the OUTER ascription
via `substTyVar`, but every such INNER occurrence must close too, or the residue still contains a
free `a` the checker rejects (confirmed live: an outer-only substitution left `match (xs : List a)`
unclosed, reproducing the #120 wall INSIDE a nominally-monomorphized residue). Exhaustive over
every `Surf` former (the `qualifyDotAccess`/`callSitesOf` completeness discipline). -/
def substTyVarInSurf (qTy : Ty → Ty) : Surf → Surf
  | .lit n       => .lit n
  | .var x       => .var x
  | .getS        => .getS
  | .unitS       => .unitS
  | .thunk e     => .thunk (substTyVarInSurf qTy e)
  | .force e     => .force (substTyVarInSurf qTy e)
  | .raise e     => .raise (substTyVarInSurf qTy e)
  | .handle e    => .handle (substTyVarInSurf qTy e)
  | .putS e      => .putS (substTyVarInSurf qTy e)
  | .atomS e     => .atomS (substTyVarInSurf qTy e)
  | .newS e      => .newS (substTyVarInSurf qTy e)
  | .readS e     => .readS (substTyVarInSurf qTy e)
  | .inlS e      => .inlS (substTyVarInSurf qTy e)
  | .inrS e      => .inrS (substTyVarInSurf qTy e)
  | .foldS e     => .foldS (substTyVarInSurf qTy e)
  | .unfoldS e   => .unfoldS (substTyVarInSurf qTy e)
  | .divMark e   => .divMark (substTyVarInSurf qTy e)
  | .lam x e     => .lam x (substTyVarInSurf qTy e)
  | .annotS e t  => .annotS (substTyVarInSurf qTy e) (qTy t)
  | .lett x a b  => .lett x (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .stateS a b  => .stateS (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .writeS a b  => .writeS (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .pairS a b   => .pairS (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .splitS x y a b => .splitS x y (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .binopS op a b  => .binopS op (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .app a b        => .app (substTyVarInSurf qTy a) (substTyVarInSurf qTy b)
  | .ifS c t e      => .ifS (substTyVarInSurf qTy c) (substTyVarInSurf qTy t) (substTyVarInSurf qTy e)
  | .matchS s xl l xr r => .matchS (substTyVarInSurf qTy s) xl (substTyVarInSurf qTy l) xr (substTyVarInSurf qTy r)
  | .matchD s arms  => .matchD (substTyVarInSurf qTy s) (substTyVarInSurfDArms qTy arms)
  | .withCapS k i n b => .withCapS k (substTyVarInSurf qTy i) n (substTyVarInSurf qTy b)
  | .dotPerform r op .none      => .dotPerform (substTyVarInSurf qTy r) op .none
  | .dotPerform r op (.one a)   => .dotPerform (substTyVarInSurf qTy r) op (.one (substTyVarInSurf qTy a))
  | .dotPerform r op (.two a b) => .dotPerform (substTyVarInSurf qTy r) op (.two (substTyVarInSurf qTy a) (substTyVarInSurf qTy b))
  | .letRecS n t f b => .letRecS n (qTy t) (substTyVarInSurf qTy f) (substTyVarInSurf qTy b)
  | .letRecMultiS binds b => .letRecMultiS (substTyVarInSurfLRBindings qTy binds) (substTyVarInSurf qTy b)
  | .lettMulti binds b => .lettMulti (substTyVarInSurfBindings qTy binds) (substTyVarInSurf qTy b)
  | .handleCustomS lbl n p? h cls b =>
      .handleCustomS lbl (substTyVarInSurf qTy n)
        (match p? with
          | .none    => .none
          | .one p   => .one (substTyVarInSurf qTy p)
          | .two a c => .two (substTyVarInSurf qTy a) (substTyVarInSurf qTy c))
        h (substTyVarInSurfHClauses qTy cls) (substTyVarInSurf qTy b)
def substTyVarInSurfDArms (qTy : Ty → Ty) : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest => .cons c ps (substTyVarInSurf qTy b) (substTyVarInSurfDArms qTy rest)
def substTyVarInSurfBindings (qTy : Ty → Ty) : LetBindings → LetBindings
  | .nil            => .nil
  | .cons n e rest  => .cons n (substTyVarInSurf qTy e) (substTyVarInSurfBindings qTy rest)
def substTyVarInSurfHClauses (qTy : Ty → Ty) : HClauses → HClauses
  | .nil               => .nil
  | .cons op x b rest  => .cons op x (substTyVarInSurf qTy b) (substTyVarInSurfHClauses qTy rest)
def substTyVarInSurfLRBindings (qTy : Ty → Ty) : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons n t e rest   => .cons n (qTy t) (substTyVarInSurf qTy e) (substTyVarInSurfLRBindings qTy rest)
end

mutual
/-- INLINE a bare-variable value alias `let n = m in rest` (`m` a bare `.var`, NOT a call/thunk/
anything else — the narrow shape `mergeModules`'s auto-`use` mechanism produces, ADR-0098:
`aliasDecls`'s `.letD n none (Surf.var (qualifyName modName n))`, e.g. `let take = Prelude_take in
…`): rewrite every free `.var n` in `rest` to `.var m`, then DROP the now-dead alias binding
entirely. NEEDED because `monoCallSpine`'s discovery matches the CALL HEAD `.force (.var name)`
literally against the qualified `let rec`'s OWN name (`Prelude_take`) — a caller writing the
UNQUALIFIED alias (`$take …`, the only spelling a program auto-`use`ing the prelude ever writes)
is invisible to it without this inlining first (confirmed live: `$take 2 xs` through the
`Prelude`-injected alias reported "a use leaves a type variable unresolved" — ZERO call sites
found — until this pass ran first). Non-bare-`.var`-RHS `.lett`s (an ordinary user `let`, or a
computed value) are left completely alone — this is NOT a general copy-propagation optimizer, only
the ONE narrow shape the module system's alias-injection is known to produce. Exhaustive over
every `Surf` former (the `qualifyVars`/`substTyVarInSurf` completeness discipline). -/
partial def inlineVarAliases : Surf → Surf
  | .lit n       => .lit n
  | .var x       => .var x
  | .getS        => .getS
  | .unitS       => .unitS
  | .thunk e     => .thunk (inlineVarAliases e)
  | .force e     => .force (inlineVarAliases e)
  | .raise e     => .raise (inlineVarAliases e)
  | .handle e    => .handle (inlineVarAliases e)
  | .putS e      => .putS (inlineVarAliases e)
  | .atomS e     => .atomS (inlineVarAliases e)
  | .newS e      => .newS (inlineVarAliases e)
  | .readS e     => .readS (inlineVarAliases e)
  | .inlS e      => .inlS (inlineVarAliases e)
  | .inrS e      => .inrS (inlineVarAliases e)
  | .foldS e     => .foldS (inlineVarAliases e)
  | .unfoldS e   => .unfoldS (inlineVarAliases e)
  | .divMark e   => .divMark (inlineVarAliases e)
  | .lam x e     => .lam x (inlineVarAliases e)
  | .annotS e t  => .annotS (inlineVarAliases e) t
  | .lett n (.var m) rest =>
      -- the ONE interesting case: substitute `n ↦ m` through `rest` (`qualifyVars`-style single-
      -- target rename, reused via `qualifyName`'s `modName_name` trick would be wrong here — `m` is
      -- an arbitrary already-qualified name, not `modName ++ "_" ++ n`, so a bespoke inline rename)
      -- THEN recurse (a chain `let a = b in let c = a in …` collapses fully, left-to-right).
      inlineVarAliases (renameVarTo n m rest)
  | .lett x a b  => .lett x (inlineVarAliases a) (inlineVarAliases b)
  | .stateS a b  => .stateS (inlineVarAliases a) (inlineVarAliases b)
  | .writeS a b  => .writeS (inlineVarAliases a) (inlineVarAliases b)
  | .pairS a b   => .pairS (inlineVarAliases a) (inlineVarAliases b)
  | .splitS x y a b => .splitS x y (inlineVarAliases a) (inlineVarAliases b)
  | .binopS op a b  => .binopS op (inlineVarAliases a) (inlineVarAliases b)
  | .app a b        => .app (inlineVarAliases a) (inlineVarAliases b)
  | .ifS c t e      => .ifS (inlineVarAliases c) (inlineVarAliases t) (inlineVarAliases e)
  | .matchS s xl l xr r => .matchS (inlineVarAliases s) xl (inlineVarAliases l) xr (inlineVarAliases r)
  | .matchD s arms  => .matchD (inlineVarAliases s) (inlineVarAliasesDArms arms)
  | .withCapS k i n b => .withCapS k (inlineVarAliases i) n (inlineVarAliases b)
  | .dotPerform r op .none      => .dotPerform (inlineVarAliases r) op .none
  | .dotPerform r op (.one a)   => .dotPerform (inlineVarAliases r) op (.one (inlineVarAliases a))
  | .dotPerform r op (.two a b) => .dotPerform (inlineVarAliases r) op (.two (inlineVarAliases a) (inlineVarAliases b))
  | .letRecS n t f b => .letRecS n t (inlineVarAliases f) (inlineVarAliases b)
  | .letRecMultiS binds b => .letRecMultiS (inlineVarAliasesLRBindings binds) (inlineVarAliases b)
  | .lettMulti binds b => .lettMulti (inlineVarAliasesBindings binds) (inlineVarAliases b)
  | .handleCustomS lbl n p? h cls b =>
      .handleCustomS lbl (inlineVarAliases n)
        (match p? with
          | .none    => .none
          | .one p   => .one (inlineVarAliases p)
          | .two a c => .two (inlineVarAliases a) (inlineVarAliases c))
        h (inlineVarAliasesHClauses cls) (inlineVarAliases b)
partial def inlineVarAliasesDArms : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest => .cons c ps (inlineVarAliases b) (inlineVarAliasesDArms rest)
partial def inlineVarAliasesBindings : LetBindings → LetBindings
  | .nil            => .nil
  | .cons n e rest  => .cons n (inlineVarAliases e) (inlineVarAliasesBindings rest)
partial def inlineVarAliasesHClauses : HClauses → HClauses
  | .nil               => .nil
  | .cons op x b rest  => .cons op x (inlineVarAliases b) (inlineVarAliasesHClauses rest)
partial def inlineVarAliasesLRBindings : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons n t e rest   => .cons n t (inlineVarAliases e) (inlineVarAliasesLRBindings rest)
/-- Rename every FREE `.var n` to `.var m`, shadow-aware (the `qualifyVars` precedent, specialized
to a single arbitrary target rather than `qualifyName`'s `modName_name` construction) — the engine
`inlineVarAliases`'s `.lett n (.var m) rest` arm rides. -/
partial def renameVarTo (n m : String) : Surf → Surf
  | .lit k       => .lit k
  | .var x       => if x == n then .var m else .var x
  | .getS        => .getS
  | .unitS       => .unitS
  | .thunk e     => .thunk (renameVarTo n m e)
  | .force e     => .force (renameVarTo n m e)
  | .raise e     => .raise (renameVarTo n m e)
  | .handle e    => .handle (renameVarTo n m e)
  | .putS e      => .putS (renameVarTo n m e)
  | .atomS e     => .atomS (renameVarTo n m e)
  | .newS e      => .newS (renameVarTo n m e)
  | .readS e     => .readS (renameVarTo n m e)
  | .inlS e      => .inlS (renameVarTo n m e)
  | .inrS e      => .inrS (renameVarTo n m e)
  | .foldS e     => .foldS (renameVarTo n m e)
  | .unfoldS e   => .unfoldS (renameVarTo n m e)
  | .divMark e   => .divMark (renameVarTo n m e)
  | .lam x e     => if x == n then .lam x e else .lam x (renameVarTo n m e)
  | .annotS e t  => .annotS (renameVarTo n m e) t
  | .lett x a b  => if x == n then .lett x (renameVarTo n m a) b else .lett x (renameVarTo n m a) (renameVarTo n m b)
  | .stateS a b  => .stateS (renameVarTo n m a) (renameVarTo n m b)
  | .writeS a b  => .writeS (renameVarTo n m a) (renameVarTo n m b)
  | .pairS a b   => .pairS (renameVarTo n m a) (renameVarTo n m b)
  | .splitS x y a b => .splitS x y (renameVarTo n m a) (if x == n || y == n then b else renameVarTo n m b)
  | .binopS op a b  => .binopS op (renameVarTo n m a) (renameVarTo n m b)
  | .app a b        => .app (renameVarTo n m a) (renameVarTo n m b)
  | .ifS c t e      => .ifS (renameVarTo n m c) (renameVarTo n m t) (renameVarTo n m e)
  | .matchS s xl l xr r =>
      .matchS (renameVarTo n m s) xl (if xl == n then l else renameVarTo n m l)
        xr (if xr == n then r else renameVarTo n m r)
  | .matchD s arms  => .matchD (renameVarTo n m s) (renameVarToDArms n m arms)
  | .withCapS k i x b => .withCapS k (renameVarTo n m i) x (if x == n then b else renameVarTo n m b)
  | .dotPerform r op .none      => .dotPerform (renameVarTo n m r) op .none
  | .dotPerform r op (.one a)   => .dotPerform (renameVarTo n m r) op (.one (renameVarTo n m a))
  | .dotPerform r op (.two a b) => .dotPerform (renameVarTo n m r) op (.two (renameVarTo n m a) (renameVarTo n m b))
  | .letRecS nm t f b => if nm == n then .letRecS nm t f b else .letRecS nm t (renameVarTo n m f) (renameVarTo n m b)
  | .letRecMultiS binds b =>
      if (letRecBindingsNames binds).contains n then .letRecMultiS binds b
      else .letRecMultiS (renameVarToLRBindings n m binds) (renameVarTo n m b)
  | .lettMulti binds b =>
      let (binds', shadowed) := renameVarToBindings n m binds
      .lettMulti binds' (if shadowed then b else renameVarTo n m b)
  | .handleCustomS lbl v p? h cls b =>
      .handleCustomS lbl (renameVarTo n m v)
        (match p? with
          | .none    => .none
          | .one p   => .one (renameVarTo n m p)
          | .two a c => .two (renameVarTo n m a) (renameVarTo n m c))
        h (renameVarToHClauses n m cls) (if h == n then b else renameVarTo n m b)
partial def renameVarToDArms (n m : String) : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest => .cons c ps (if ps.contains n then b else renameVarTo n m b) (renameVarToDArms n m rest)
partial def renameVarToHClauses (n m : String) : HClauses → HClauses
  | .nil               => .nil
  | .cons op x b rest  => .cons op x (if x == n then b else renameVarTo n m b) (renameVarToHClauses n m rest)
partial def renameVarToLRBindings (n m : String) : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons nm t e rest  => .cons nm t (renameVarTo n m e) (renameVarToLRBindings n m rest)
partial def renameVarToBindings (n m : String) : LetBindings → LetBindings × Bool
  | .nil            => (.nil, false)
  | .cons nm e rest =>
      let e' := renameVarTo n m e
      if nm == n then (.cons nm e' rest, true)
      else let (rest', shadowed) := renameVarToBindings n m rest; (.cons nm e' rest', shadowed)
end

/-- Monomorphize ONE bound-free `let rec name : t = fb in bodyExpr` node (ADR-0103): discover every
call site's instantiation (`callSitesOf`), complete + group them into a distinct residue set
(`completeInstantiation`/`indexInstantiations`), redirect every call in `bodyExpr` to its own
residue (`redirectCalls`), and wrap the rewritten body in one concrete `.letRecS` per residue
(order is immaterial — each residue is a closed, mutually-invisible `let rec`, so any nesting order
runs identically; residues are built LAST-discovered-innermost only because `foldr` is the natural
shape over an already-built list). Zero call sites ⟹ DROP the binding (the `expandBFns`/`env.bfns`
precedent: an unreferenced generic costs nothing and produces nothing — ADR-0098's mention-filter
is the same move one layer up). An INCOMPLETE call (some free tyvar never pinned by an annotation)
fails LOUD naming the function, never silently drops that call or guesses its type. Residue names
are `#monoK_name` (`qualifyName` reused verbatim, `K` = the distinct-instantiation index) —
`#`-prefixed so no user identifier can collide (the parser's own sentinel-name convention,
`#anf`/`#rec`/`#g`/…). Every residue's `fb'` is ADDITIONALLY closed via `substTyVarInSurf` (not
just the outer ascription `t'`) — the function BODY's own internal ascriptions (`match (xs : List
a) { … }`) mention the same tyvar and must close too. -/
def monomorphizeOne (name : String) (t : Ty) (fb bodyExpr : Surf) (tvs : List String) :
    Except String Surf := do
  let domains := curriedDomains tvs.length t
  let raw := callSitesOf name domains bodyExpr
  if raw.isEmpty then
    return bodyExpr
  else do
    let complete ← raw.mapM (fun binding =>
      match completeInstantiation tvs binding with
      | some sub => .ok sub
      | none     => .error s!"'{name}': a use leaves a type variable unresolved — annotate the argument (e.g. `({name} arg : List Int)`) so ADR-0103's monomorphization pass can close it")
    let (distinct, _) := indexInstantiations complete
    let freshNames := (List.range distinct.length).map (fun i => qualifyName s!"#mono{i}" name)
    let residues := distinct.zip freshNames
    let bodyExpr' := redirectCalls name domains tvs residues none bodyExpr
    return residues.foldr (fun (sub, freshName) acc =>
      let closeTy : Ty → Ty := fun ty => sub.foldl (fun ty' (tv, c) => substTyVar tv c ty') ty
      let t' := closeTy t
      -- `fb`'s own self-reference is a call site too, but it carries NO annotation to rediscover
      -- (`$length t` inside `length`'s own body, not `($length t : List Int)`) — `self? := some
      -- freshName` short-circuits `redirectCalls`'s discovery step entirely for this walk, so EVERY
      -- self-call redirects uniformly to THIS residue's own fresh name (never a sibling's — the
      -- monomorphic, non-polymorphic-recursion invariant `w4` established). `substTyVarInSurf
      -- closeTy` ADDITIONALLY closes every tyvar occurrence INSIDE `fb`'s body (`match (xs : List
      -- a) { … }`) — the outer ascription `t'` alone does not reach there.
      let fb' := substTyVarInSurf closeTy (redirectCalls name domains tvs residues (some freshName) fb)
      .letRecS freshName t' fb' acc) bodyExpr'

mutual
/-- Bound-free `let rec` monomorphization pre-pass (ADR-0103): a PURE `Surf → Surf` fuel-bounded
rewrite, run in `elabProg` alongside `expandBFns`, BEFORE `elabS`. `.letRecS` is the ONE
interesting case: if its ascription has a free tyvar (`freeTyVars gen aliases t`, the SAME lookup
`resolveTyG` would fail loud on, TypeCheck.lean's `.letRecS`/`resolveTy` chokepoint), monomorphize
it (`monomorphizeOne`) and recurse into the RESULT at `f` (fresh fuel — the result's residues are
concrete by construction: `substTyVar` closed every free tyvar, so `freeTyVars` on a residue's OWN
ascription is `[]`, and the recursive call cannot loop on the SAME node, only reach genuinely
NESTED bound-free `let rec`s elsewhere in the rewritten tree). Every other former maps structurally
(the `expandBFns` completeness precedent — a new `Surf` former fails here until handled). -/
def monomorphizeLetRec (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → Surf → Except String Surf
  | 0,     _ => .error "let rec monomorphization out of fuel"
  | _ + 1, .lit n     => .ok (.lit n)
  | _ + 1, .var x     => .ok (.var x)
  | _ + 1, .unitS     => .ok .unitS
  | _ + 1, .getS      => .ok .getS
  | f + 1, .thunk e   => do return .thunk (← monomorphizeLetRec gen aliases f e)
  | f + 1, .force e   => do return .force (← monomorphizeLetRec gen aliases f e)
  | f + 1, .raise e   => do return .raise (← monomorphizeLetRec gen aliases f e)
  | f + 1, .handle e  => do return .handle (← monomorphizeLetRec gen aliases f e)
  | f + 1, .putS e    => do return .putS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .atomS e   => do return .atomS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .newS e    => do return .newS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .readS e   => do return .readS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .inlS e    => do return .inlS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .inrS e    => do return .inrS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .foldS e   => do return .foldS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .unfoldS e => do return .unfoldS (← monomorphizeLetRec gen aliases f e)
  | f + 1, .divMark e => do return .divMark (← monomorphizeLetRec gen aliases f e)
  | f + 1, .lam x b   => do return .lam x (← monomorphizeLetRec gen aliases f b)
  | f + 1, .lett x e b   => do return .lett x (← monomorphizeLetRec gen aliases f e) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .app g a      => do return .app (← monomorphizeLetRec gen aliases f g) (← monomorphizeLetRec gen aliases f a)
  | f + 1, .stateS a b   => do return .stateS (← monomorphizeLetRec gen aliases f a) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .writeS a b   => do return .writeS (← monomorphizeLetRec gen aliases f a) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .pairS a b    => do return .pairS (← monomorphizeLetRec gen aliases f a) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .binopS op a b => do return .binopS op (← monomorphizeLetRec gen aliases f a) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .ifS c t e    => do return .ifS (← monomorphizeLetRec gen aliases f c) (← monomorphizeLetRec gen aliases f t) (← monomorphizeLetRec gen aliases f e)
  | f + 1, .splitS a b p body => do return .splitS a b (← monomorphizeLetRec gen aliases f p) (← monomorphizeLetRec gen aliases f body)
  | f + 1, .matchS s xl el xr er => do
      return .matchS (← monomorphizeLetRec gen aliases f s) xl (← monomorphizeLetRec gen aliases f el) xr (← monomorphizeLetRec gen aliases f er)
  | f + 1, .withCapS k init n body => do return .withCapS k (← monomorphizeLetRec gen aliases f init) n (← monomorphizeLetRec gen aliases f body)
  | f + 1, .annotS e t => do return .annotS (← monomorphizeLetRec gen aliases f e) t
  | f + 1, .dotPerform recv op args => do return .dotPerform (← monomorphizeLetRec gen aliases f recv) op (← monomorphizeArgs gen aliases f args)
  | f + 1, .matchD s arms => do return .matchD (← monomorphizeLetRec gen aliases f s) (← monomorphizeArms gen aliases f arms)
  | f + 1, .lettMulti binds b => do return .lettMulti (← monomorphizeLetBindings gen aliases f binds) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .handleCustomS lbl n p? h cls b => do
      return .handleCustomS lbl (← monomorphizeLetRec gen aliases f n) (← monomorphizeArgs gen aliases f p?) h
        (← monomorphizeHClauses gen aliases f cls) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .letRecMultiS binds b => do
      return .letRecMultiS (← monomorphizeLRBindings gen aliases f binds) (← monomorphizeLetRec gen aliases f b)
  | f + 1, .letRecS name t fb bodyExpr => do
      match freeTyVars gen aliases t with
      | [] => do return .letRecS name t (← monomorphizeLetRec gen aliases f fb) (← monomorphizeLetRec gen aliases f bodyExpr)
      | tvs => do
          let rewritten ← monomorphizeOne name t fb bodyExpr tvs
          monomorphizeLetRec gen aliases f rewritten
def monomorphizeArgs (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → SurfArgs → Except String SurfArgs
  | 0,     _        => .error "let rec monomorphization out of fuel"
  | _ + 1, .none    => .ok .none
  | f + 1, .one a   => do return .one (← monomorphizeLetRec gen aliases f a)
  | f + 1, .two a b => do return .two (← monomorphizeLetRec gen aliases f a) (← monomorphizeLetRec gen aliases f b)
def monomorphizeArms (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → DArms → Except String DArms
  | 0,     _             => .error "let rec monomorphization out of fuel"
  | _ + 1, .nil          => .ok .nil
  | f + 1, .cons c bs b r => do return .cons c bs (← monomorphizeLetRec gen aliases f b) (← monomorphizeArms gen aliases f r)
def monomorphizeHClauses (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → HClauses → Except String HClauses
  | 0,     _              => .error "let rec monomorphization out of fuel"
  | _ + 1, .nil           => .ok .nil
  | f + 1, .cons op x b r => do return .cons op x (← monomorphizeLetRec gen aliases f b) (← monomorphizeHClauses gen aliases f r)
def monomorphizeLetBindings (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → LetBindings → Except String LetBindings
  | 0,     _              => .error "let rec monomorphization out of fuel"
  | _ + 1, .nil           => .ok .nil
  | f + 1, .cons n e rest => do return .cons n (← monomorphizeLetRec gen aliases f e) (← monomorphizeLetBindings gen aliases f rest)
def monomorphizeLRBindings (gen : List (String × GenData)) (aliases : List (String × Ty)) :
    Nat → LetRecBindings → Except String LetRecBindings
  | 0,     _                => .error "let rec monomorphization out of fuel"
  | _ + 1, .nil              => .ok .nil
  | f + 1, .cons n t e rest  => do return .cons n t (← monomorphizeLetRec gen aliases f e) (← monomorphizeLRBindings gen aliases f rest)
end

/-- #124: the `.matchD` scrutinee-type-mismatch error, teaching-phrase aware. `foldDataTyOrRaw`
(the general-purpose renderer `bang holes`/`bang query type`/`hover` ALSO depend on — its raw
`#N` markers are `Bang.Query.holesOf`'s OWN detection signal, `holeMarkersIn`'s textual scan —
must NOT be changed to prose here; only THIS error-throw site's rendering is teaching-phrase'd,
so the general fold stays byte-identical for every other caller). An unresolved position (`n ≥
holeBase`, the same threshold `holesOf` itself uses) renders as a phrase naming the fix — ascribe
the scrutinee — instead of the bare `#N` a stranger cannot act on (the #124 finding: a curried
`let rec`'s LATER parameter falls through unascribed — `letRecS`'s elaboration arm only threads
the declared type onto the OUTERMOST `.lam` binder, so a match on a later param's value lands
here with an unresolved `paramHole`). -/
def matchScrutineeTyErr (ctors : List (String × CtorInfo)) (gen : List (String × GenData))
    (τ : VT) (dataName : String) (indefiniteArticle : Bool) : String :=
  let rendered := foldDataTyOrRaw ctors gen τ
  let isHole := match τ with | .tvar n => decide (n ≥ holeBase) | _ => false
  let article := if indefiniteArticle then "a " else ""
  if isHole then
    s!"match scrutinee's type is undetermined here (an underdetermined position, shown as \
'{rendered}' internally) — ascribe it, e.g. `match (s : {dataName}) \{ … }`, to pin the type \
BEFORE the match (this is the common shape when a curried `let rec`'s LATER parameter is matched: \
only the OUTERMOST param's declared type is threaded automatically)"
  else
    s!"match scrutinee is {rendered}, not {article}{dataName}"

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
      match resolveCtor env x with             -- a 0-ary ctor use (`Nil`) IS an intro (ADR-0069); ADR-0099 resolution
      | some (.ok ci) => if ci.arity == 0 then
                     -- GENERIC (bite-1/#55): the ctor's TEMPLATE μ (params as markers) — `embVInst` mints
                     -- fresh holes at the annotation, so the element type is INFERRED from context (an
                     -- enclosing concrete annotation OR the fields), no user `: Option Int` required.
                     -- Monomorphic: the concrete `ci.dataTy` annotation, exactly as ADR-0069.
                     if ci.params.isEmpty then .ok (ctorIntro ci .unitS)
                     else genCtorIntro env ci .unitS
                   else .error s!"constructor '{x}' expects {ci.arity} argument(s)"
      | some (.error e) => .error e             -- ADR-0099 B012: ambiguous bare ctor
      | none             => .ok (.var x)
  | _, .getS  => .ok .getS
  | _, .unitS => .ok .unitS
  | Γ, .thunk b  => do return .thunk (← elabS env Γ b)
  | Γ, .force b  => do return .force (← elabS env Γ b)
  -- A-normalize a computation ARGUMENT (#26 part-2), as `.pairS` does: an effect op's arg is
  -- VALUE-position (`checkSV … .int`), so `put (get + 1)` ⟹ `let #anf = get + 1 in put #anf`. A bare
  -- value arg passes through unchanged (`anfSplit`'s `id` prefix), matching `Surface.lower`.
  | Γ, .raise e  => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e' env.effects; return w (.raise v)
  | Γ, .handle e => do return .handle (← elabS env Γ e)
  | Γ, .putS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e' env.effects; return w (.putS v)
  | Γ, .atomS e  => do return .atomS (← elabS env Γ e)
  | Γ, .newS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e' env.effects; return w (.newS v)
  | Γ, .readS e  => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e' env.effects; return w (.readS v)
  -- A-normalize a computation payload (#41), as `.pairS` does: `Left(($g) e)` ⟹ `let #anf = ($g) e in
  -- Left(#anf)`, so the sum injection gets a VALUE payload (a bare `Left(value)` is unchanged).
  | Γ, .inlS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e' env.effects; return w (.inlS v)
  | Γ, .inrS e   => do let e' ← elabS env Γ e; let (_, w, v) ← anfSplit Γ e' env.effects; return w (.inrS v)
  -- state's INITIAL value is value-position (`checkSV e0 .int`) too — A-normalize it like the ops.
  | Γ, .stateS e0 e => do
      let e0' ← elabS env Γ e0
      let (Γ1, w, v0) ← anfSplit Γ e0' env.effects
      return w (.stateS v0 (← elabS env Γ1 e))
  | Γ, .writeS r w  => do
      let r' ← elabS env Γ r
      let w' ← elabS env Γ w
      let (Γ1, wr, rv) ← anfSplit Γ r' env.effects
      let (_,  ww, wv) ← anfSplit Γ1 w' env.effects
      return wr (ww (.writeS rv wv))
  | Γ, .pairS a b   => do                     -- A-normalize computation components (bare pair in comp position), #41
      let a' ← elabS env Γ a
      let b' ← elabS env Γ b
      let (Γ1, wa, va) ← anfSplit Γ a' env.effects
      let (_,  wb, vb) ← anfSplit Γ1 b' env.effects
      return wa (wb (.pairS va vb))
  | Γ, .foldS b     => do return .foldS (← elabS env Γ b)
  | Γ, .unfoldS b   => do return .unfoldS (← elabS env Γ b)
  | Γ, .withCapS kind init name body => do   -- bind name : Cap ℓ so body operands synthesize (ADR-0070)
      let init' ← elabS env Γ init
      let Γ' := match capKindLabel kind with
        | some ℓ => (name, (.cap ℓ : IVTy)) :: Γ
        | none   => Γ
      return .withCapS kind init' name (← elabS env Γ' body)
  -- ADR-0095 WALL-1 FIX (manager-ruled Option A): `elabS` is the ONE place with both the `Surf`
  -- tree and `env.effects` in scope simultaneously — `lowerC` never sees `env.effects` (confirmed
  -- structurally even on the fully-typed `checkAndLower` path, see `lowerC`'s own `.handleCustomS`
  -- arm). So THIS arm RESOLVES `n`'s label against `env.effects` and REWRITES it into the tree's
  -- `label?` slot (`handleCustomS`'s first field) — `lowerC` then reads it back verbatim, a PURE
  -- function of the tree with no `ElabEnv` threading (the rejected alternative: polluting a
  -- structural pass with elaboration state, AND the untyped `elaborateToComp` path lacks a full
  -- `ElabEnv` anyway, so that alternative would dead-end there too). An unresolved `n` (not a
  -- declared effect, or not a bare `.var`) leaves the slot `none` — `lowerC`'s own arm fails loud
  -- on that, never silently defaulting a label.
  | Γ, .handleCustomS _lbl n p? h cls body => do
      let n' ← elabS env Γ n
      let p'? ← (match p? with
        | .none    => (pure .none : Except String SurfArgs)
        | .one p0  => do return .one (← elabS env Γ p0)
        | .two a b => do return .two (← elabS env Γ a) (← elabS env Γ b))
      let lbl' := match n with
        | .var effN => (env.effects.lookup effN).map EffectInfo.label
        | _         => none
      let Γ' := match lbl' with
        | some ℓ => (h, (.cap ℓ : IVTy)) :: Γ
        | none   => Γ
      return .handleCustomS lbl' n' p'? h (← elabHClauses env Γ' cls) (← elabS env Γ' body)
  | Γ, .dotPerform recv op args => do
      let recv' ← elabS env Γ recv
      let args' ← (match args with
        | .none    => (pure .none : Except String SurfArgs)
        | .one a   => do return .one (← elabS env Γ a)
        | .two a b => do return .two (← elabS env Γ a) (← elabS env Γ b))
      return .dotPerform recv' op args'
  | Γ, .app (.var c) a => do                  -- ctor intro `Cons(e, …)` parses as application (ADR-0069)
      match resolveCtor env c with            -- ADR-0099 resolution
      | some (.ok ci) =>
          if ci.arity == 0 then .error s!"constructor '{c}' takes no arguments"
          else do
            -- A-normalize the payload so the fold wraps a VALUE (computations lifted above, #41). A
            -- multi-field payload is a `pairS` whose own arm already lifts its fields into a returner;
            -- this bind then lifts that returner above the fold. Inner/outer `#anf` names may coincide
            -- at equal depth but shadow innermost-first (as `lower`'s sentinels do), so it stays correct.
            let a' ← elabS env Γ a
            let (_, w, v) ← anfSplit Γ a' env.effects
            -- GENERIC (bite-1/#55): the TEMPLATE μ (params as markers) — `embVInst` mints fresh holes, so
            -- the element type is INFERRED from the fields (`Cons(1, Nil)` ⟹ `a := Int`, no annotation).
            if ci.params.isEmpty then return w (ctorIntro ci v)
            else return w (← genCtorIntro env ci v)
      | some (.error e) => .error e           -- ADR-0099 B012: ambiguous bare ctor
      | none             => do return .app (.var c) (← elabS env Γ a)
  | Γ, .app f a     => do                     -- A-normalize a computation ARGUMENT (`($f)(n-1)`), #41
      let f' ← elabS env Γ f
      let a' ← elabS env Γ a
      let (_, wrap, av) ← anfSplit Γ a' env.effects
      return wrap (.app f' av)
  | Γ, .ifS c t e   => do                     -- A-normalize a computation condition (`n == 0`), #41
      let c' ← elabS env Γ c
      let (Γ1, wrap, cv) ← anfSplit Γ c' env.effects
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
      let t' ← resolveTy env.gen env.aliases t env.effects
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
  -- `let rec f : T1 = e1 and g : T2 = e2 … in body` (#97 item 2) → the H2 tuple-of-thunks μ-knot
  -- (`buildLetRecMulti`'s own doc comment has the full encoding). Every sibling must be a function
  -- literal (mirroring `.letRecS`'s own requirement immediately above — one un-annotated `fun` per
  -- sibling is what `pLetRecBindings`'s grammar always produces) and elaborates its body with EVERY
  -- sibling name bound (mutual visibility) PLUS its own param, exactly generalizing `.letRecS`'s
  -- single-name `(pn, dom) :: (name, uT) :: Γ` binding to N names. `resolveLetRecBindingTys`/
  -- `letRecBindingUTys`/`elabLetRecBindings` (below, mutual siblings of `elabS`) do the two-pass
  -- work: resolve every `Ty` + extend Γ with EVERY sibling's `uT` FIRST (so each sibling's body sees
  -- every OTHER sibling), then elaborate each body under that shared, fully-extended Γsibs.
  | Γ, .letRecMultiS binds bodyExpr => do
      let resolved ← resolveLetRecBindingTys env binds
      let Γsibs := letRecBindingUTys resolved ++ Γ
      let bodies' ← elabLetRecBindings env Γsibs resolved binds
      let bodyExpr' ← elabS env Γsibs bodyExpr
      let names := letRecResolvedNames resolved
      let tys := letRecResolvedTys resolved
      -- `structOK` is NOT extended to certify a co-recursive NAME SET (the design note's flagged,
      -- unscoped judgment call) — every mutual group conservatively carries `Div`, sound per
      -- `structOK`'s own "default false" discipline (`buildLetRecMulti`'s own doc comment).
      return buildLetRecMulti names tys bodies' bodyExpr' {divLabel}
  | _, .divMark _ =>
      .error "divMark is internal (#46 let rec Div-marker) — it is EMITTED by the elaborator, never received"
  | _, .lettMulti .. =>
      .error "let-sugar (`;`, issue #68) is erased by elabProg before elabS ever runs — reaching here is a bug"
  | Γ, .lett x e b  => do
      let e' ← elabS env Γ e
      match elabBind Γ e' env.effects with      -- report the RHS's REAL error, not a downstream unbound (#41)
      | .ok (some sch) => return .lett x e' (← elabS env ((x, sch) :: Γ) b)
      | .ok none       =>
          -- #121: a bare `fun` RHS is the single most common trigger of "not a returner" (a
          -- functional programmer's most natural `let f = fun x => …`) — name the REAL fix (thunk
          -- the RHS) instead of the generic `$x` suggestion, which doesn't even parse at this
          -- position (`$` forces a THUNK to a value; a bare `fun` is already a computation, not a
          -- thunk, so there is nothing here for `$` to force).
          match e with
          | .lam .. => throw s!"let-binding '{x}': a bare function is a computation (a \"returner\"), not a value — a top-level `let` binds a VALUE, so wrap it in a thunk: `let {x} = \{fun … => …}` (see `examples/caesar`)"
          | _        => throw s!"let-binding '{x}': value is not a returner — wrap it in a thunk (\{…}), or bind a value"
      | .error m       => throw s!"let-binding '{x}': {m}"
  | Γ, .matchS s xl el xr er => do
      let s' ← elabS env Γ s
      let (Γ1, wrap, sv) ← anfSplit Γ s' env.effects       -- A-normalize a computation scrutinee, #41
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
      let (Γ1, wrap, p') ← anfSplit Γ p0 env.effects       -- A-normalize a computation scrutinee, #41
      let Γ' := match runInferV (synthSV Γ1 p') with
        | .ok (.prod A B) => (b, embV B) :: (a, embV A) :: Γ1
        -- #55: the scrutinee's product structure isn't known yet (a generic Option's element `a` bound to
        -- `(v * rest)`, still an opaque marker at elaboration). Bind the fields to placeholder holes so the
        -- body elaborates; the CHECKER's `splitS` invents the product (`.vhole ⟹ prod`) and unifies.
        | _               => (b, (paramHole (Γ1.length + 1) : IVTy)) :: (a, (paramHole Γ1.length : IVTy)) :: Γ1
      return wrap (.splitS a b p' (← elabS env Γ' body))
  | Γ, .annotS (.lam x b) t => do   -- an ascribed lam's body sees its param's type (as in checking)
      let t' ← resolveTy env.gen env.aliases t env.effects  -- data names + `Cap Net` (#84 gap 1) close here
      let Γ' := curryBind Γ (.lam x b) t'      -- bind EVERY curried param, not just the outermost
      return .annotS (← elabS env Γ' (.lam x b)) t'
  | Γ, .annotS (.thunk (.lam x b)) t => do   -- #84 gap 1: `{fun … => …} : Thunk (A -> B)` — the ONLY
      -- v1 surface form that binds a FUNCTION (`let f = fun x => …` un-thunked is "not a returner",
      -- #4698's own precedent) — mirrors the un-thunked `.annotS (.lam x b) t` arm immediately above,
      -- peeling the `.thunk`/`Thunk` layer via `curryBind`'s new case before the SAME curried-bind walk.
      let t' ← resolveTy env.gen env.aliases t env.effects
      let Γ' := curryBind Γ (.thunk (.lam x b)) t'
      return .annotS (.thunk (← elabS env Γ' (.lam x b))) t'
  | Γ, .annotS e t => do return .annotS (← elabS env Γ e) (← resolveTy env.gen env.aliases t env.effects)
  | Γ, .matchD s arms => do                    -- named match → unfold + matchS chain (ADR-0069)
      -- #101: a `_` wildcard arm is expanded to its missing ctors' arms by a SEPARATE fuel-driven
      -- pre-pass (`expandWildcards`, the `expandBFns` precedent) that runs over the WHOLE program
      -- before `elabS` starts — NOT here. Interleaving the expansion into this mutual `elabS`/
      -- `elabArms` block breaks its `sizeOf`-based termination proof (the expansion only ever
      -- GROWS `arms`, so `sizeOf (expanded arms) ≤ sizeOf arms0` is false — confirmed by a failed
      -- `termination_by` build attempt). By the time `elabS` reaches this arm, `arms` is already
      -- fully explicit — zero wildcard awareness needed anywhere in this mutual block.
      let s0 ← elabS env Γ s
      let (Γ, wrap, s0') ← anfSplit Γ s0 env.effects       -- A-normalize a computation scrutinee, #41
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
            match resolveCtor env c0 with       -- ADR-0099: the FIRST arm's ctor seeds ci0, matchD's
                                                 -- existing type-directed context (ADR-0099 §1's
                                                 -- "resolveCtor naturally runs inside it")
            | some (.ok ci0) =>
                if ci0.params.isEmpty then pure (s0', ([] : List (String × List IVTy)))
                else match runInferV (synthSV Γ s0') with
                     | .ok τ@(.mu _) => pure (s0', genBinderTable env.ctors ci0.dataName τ)   -- concrete: bite-1
                     | _ => do let tmpl ← genTemplateTy env ci0                                -- unknown: template-drive
                               pure (.annotS s0' tmpl, genBinderTable env.ctors ci0.dataName (vtyOf tmpl))
            | some (.error e) => .error e       -- ADR-0099 B012: ambiguous first-arm ctor
            | none => pure (s0', [])
        | [] => pure (s0', ([] : List (String × List IVTy))))
      let arms' ← elabArms env binderTys Γ arms   -- bodies elaborated under ctor-typed Γ
      match armsToList arms' with
      | [] => .error "match needs at least one arm"
      | armsL@((c0, _, _) :: _) =>
        match resolveCtor env c0 with           -- ADR-0099 resolution
        | none => .error s!"unknown constructor '{c0}' in match"
        | some (.error e) => .error e           -- ADR-0099 B012: ambiguous first-arm ctor
        | some (.ok ci0) => do
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
                  if τ != vtyOf ci0.dataTy then throw (matchScrutineeTyErr env.ctors env.gen τ ci0.dataName false)
                else match τ with
                     | .mu _ => pure ()
                     | _     => throw (matchScrutineeTyErr env.ctors env.gen τ ci0.dataName true)
            | .error e => throw s!"match scrutinee: {e}"
            -- order arms by ctor position (pure bookkeeping — no recursion below)
            let mut ordered : List (List String × Surf) := []
            for ci in dcs do
              match env.ctors.find? (fun p => p.2.dataName == ci.dataName && p.2.idx == ci.idx) with
              | none => throw "impossible: ctor without a name key"
              | some (cn, _) =>
                -- ADR-0099: an arm may spell this ctor BARE (`cn`, e.g. `Nil`) or QUALIFIED
                -- (`Type_Ctor`, e.g. `IntList_Nil`) — a cross-type collision forces the qualified
                -- spelling (§Migration), so both must match here, not just the bare name.
                let qn := qualifyName ci.dataName cn
                match armsL.find? (fun a => a.1 == cn || a.1 == qn) with
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
      let (Γ1, wa, a') ← anfSplit Γ a0 env.effects
      let (Γ2, wb, b') ← anfSplit Γ1 b0 env.effects
      match runInferV (synthSV Γ2 a') with
      | .ok .int  => return wa (wb (.binopS op a' b'))   -- the kernel δ-rule path (ADR-0065)
      | .error _  => return wa (wb (.binopS op a' b'))   -- non-value operand: leave it; the checker rules
      | .ok τ =>
        match asHole τ with
        | some _ => return wa (wb (.binopS op a' b'))     -- HOLE operand (bare-`fun` param): defer to the checker
        | none =>
          match env.insts.find? (fun i => i.opName == binopName op && i.target == τ) with
          | none => .error s!"no impl provides '{binopName op}' for {foldDataTyOrRaw env.ctors env.gen τ}"
          | some inst =>
              match inst.params, inst.knotName with
              -- #112: KNOT dispatch — app the `letRecS`-bound name (`elabProg` wraps the whole
              -- program in these, see `wrapPendingKnots`) to a TUPLED argument, mirroring exactly
              -- how the knot itself is built (`fun pq => let (p, q) = pq in …`, the tupled-single-
              -- arg encoding that sidesteps `letRecS`'s separate curried-arity gap — de-risked
              -- against self- AND backward-referential impls this session, see `Inst`'s doc comment).
              | [_, _], some kn => return wa (wb (.app (.force (.var kn)) (.pairS a' b')))
              -- pre-#112 splice path — unreachable for a genuinely 2-param op post-fix (every 2-param
              -- op now gets `some kn` from `buildEnv`), kept only so the match stays exhaustive/total.
              | [p, q], none    =>
                  let fnTy : Ty := .tArr inst.targetTy (.tArr inst.targetTy inst.retTy)
                  return wa (wb (.app (.app (.annotS (.lam p (.lam q inst.body)) fnTy) a') b'))
              | _, _ => .error s!"'{inst.opName}': operator resolution needs exactly 2 params (got {inst.params.length})"
  -- #97 item 2: adding `elabLetRecBindings` (a NEW mutual sibling, recursing on `LetRecBindings`,
  -- a type the block's structural-recursion inference has no prior size relation for) broke pure
  -- inference across the WHOLE `elabS`/`elabArms`/`elabHClauses` group — explicit `termination_by`
  -- on every sibling, the `synthSC`/`checkHClauses` precedent (`(sizeOf recursedArg, tiebreak)`),
  -- fixes it uniformly (confirmed: pre-existing inference held before this addition).
  termination_by _ e => (sizeOf e, 0)

/-- Elaborate named-match arm BODIES structurally over `DArms`, each under its ctor's
payload-typed Γ (unknown ctor / wrong arity ⇒ un-extended Γ here; the `matchD` arm's
validation fail-louds right after). -/
def elabArms (env : ElabEnv) (binderTys : List (String × List IVTy)) : NCtx → DArms → Except String DArms
  | _, .nil => .ok .nil
  | Γ, .cons c bs b r => do
      -- ADR-0099: an arm may spell its ctor QUALIFIED (`Type_Ctor`) when a cross-type collision
      -- forced it — `binderTys` is keyed on the BARE name (`genBinderTable`), so a direct `.lookup c`
      -- misses; every entry here shares ONE `dataName` (this table is built per-scrutinee in
      -- `matchD`), so try each entry's OWN qualified spelling as a fallback key.
      let binderLookup : Option (List IVTy) :=
        (binderTys.lookup c).orElse (fun _ =>
          (binderTys.find? (fun p => (env.ctors.lookup p.1).any (fun ci => qualifyName ci.dataName p.1 == c))).map Prod.snd)
      let Γa := match binderLookup with
        -- GENERIC (bite-1): concrete field types derived from the scrutinee's μ (`genBinderTable`).
        | some tys =>
            (match bs, tys with
             | [b1], [t1]         => (b1, (t1 : Scheme)) :: Γ
             | [b1, b2], [t1, t2] => (b2, (t2 : Scheme)) :: (b1, (t1 : Scheme)) :: Γ
             | _, _               => Γ)
        -- MONOMORPHIC: the ctor's own closed payload types (ADR-0069), unchanged. ADR-0099: an
        -- AMBIGUOUS `c` here just leaves Γ un-extended (mirroring the pre-existing `none` case) —
        -- `matchD`'s OWN `resolveCtor env c0` call (on the first arm) is what actually reports the
        -- B012 for this match; a non-first ambiguous arm name still gets caught there too, since
        -- `dcs`/`armsL` validation runs against the SAME (single, now-resolved) `ci0.dataName`.
        | none => match resolveCtor env c with
          | some (.ok ci) =>
              (match bs, ci.payloadClosed with
               | [b1], [t1]         => (b1, embV (vtyOf t1)) :: Γ
               | [b1, b2], [t1, t2] => (b2, embV (vtyOf t2)) :: (b1, embV (vtyOf t1)) :: Γ
               | _, _               => Γ)
          | some (.error _) => Γ
          | none             => Γ
      let b' ← elabS env Γa b
      let r' ← elabArms env binderTys Γ r
      .ok (.cons c bs b' r')
  termination_by _ arms => (sizeOf arms, 1)

/-- #21 s7probe / #85 fix: `HClauses` elaboration (custom-handle clause bodies) — the `elabArms`
precedent. **Correction to the s7probe-era claim this doc comment used to make** ("there is no
per-clause binder to add at elaboration"): that is FALSE — `elabS`'s `.binopS` arm A-normalizes
NESTED operands via `anfSplit`, which runs `synthSC`/`zonkInferC` on the operand's Γ IMMEDIATELY
(elaboration-time, not deferred to `checkHClauses`). A clause body with only ATOMIC operands
(`n * 10`) never triggers this (`anfSplit`'s `isValueSurf` short-circuit), which is why the bug
stayed hidden until a NESTED binop (`n * 3 + 1`) forced a real `anfSplit` lookup of `n` — issue #85,
the exact WALL-3 throwaway-context class (`stage7-elab-probe.md`): a Γ missing the clause's OWN
binders. Fix: extend Γ with `x` (the op-arg) and `param` (the carried-param binder, matching
`checkHClauses`'s later `(x, argTy) :: ("param", P) :: Γ` binding ORDER exactly, so `checkHClauses`
re-typing the SAME tree sees consistent de-Bruijn positions) — bound to FRESH HOLES here (elaboration
doesn't need the real op/param types, only that `x`/`param` resolve STRUCTURALLY so `anfSplit`'s
throwaway inference can find them; `checkHClauses` still supplies the real types at check-time).
#87: `param` is the LITERAL surface identifier (not a `#`-sentinel) — safe because `pIdent`
reserves it at every binder position, so `x` here can never literally BE `"param"`. -/
def elabHClauses (env : ElabEnv) (Γ : NCtx) : HClauses → Except String HClauses
  | .nil              => .ok .nil
  | .cons op x b rest => do
      let Γ' := (x, ({ body := paramHole Γ.length } : Scheme))
               :: ("param", ({ body := paramHole (Γ.length + 1) } : Scheme)) :: Γ
      let b' ← elabS env Γ' b
      let rest' ← elabHClauses env Γ rest
      .ok (.cons op x b' rest')
  termination_by cls => (sizeOf cls, 2)
/-- Elaborate every sibling's body (#97 item 2) under `Γsibs`, recursing over the ORIGINAL
`LetRecBindings` tree (the `elabHClauses`/`HClauses` structural-recursion precedent — see
`resolveLetRecBindingTys`'s own doc comment for why a derived `List LRResolved` carrier breaks
mutual termination inference). `table` is the pre-resolved lookup (`resolveLetRecBindingTys`'s
output) threaded read-only; the CALLER (`letRecMultiS`'s own `elabS` arm) has ALREADY extended
`Γsibs` with EVERY sibling's `f : Thunk T` binding (mutual visibility), so this only adds each
sibling's OWN param before elaborating its `pbody` — the `.letRecS` precedent's `(pn, dom) ::
(name, uT) :: Γ` binding, minus the already-shared `uT`s. Returns each sibling's elaborated
`.annotS (.lam pn pbody') t'` (the SAME shape `buildLetRecMulti`'s `bodies'` parameter expects),
in `binds`' order. `lrLookup` returning `none` throws loud (an internal-invariant violation, per
its own doc comment — never silently drops a sibling). -/
def elabLetRecBindings (env : ElabEnv) (Γsibs : NCtx) (table : List LRResolved) :
    LetRecBindings → Except String (List Surf)
  | .nil                  => .ok []
  -- `fb`/`t` come DIRECTLY off the `.cons` pattern (genuine subterms — `sizeOf`-visible), not off
  -- an `lrLookup` result: a lookup-derived `r.pbody` breaks the termination proof (Lean cannot
  -- relate an opaque `List.find?` result's field to `rest`'s size). Only `pn`/`dom` (the peeled
  -- param name/domain, NOT re-derivable from `fb`/`t` alone without re-running `resolveTy`) come
  -- from `table` — `fb` itself, matched here, MUST be `.lam pn _` (guaranteed by
  -- `resolveLetRecBindingTys` already having validated every sibling is a function literal; a
  -- mismatch here is an internal-invariant violation, thrown loud, never silently guessed).
  | .cons nm _t fb rest    => do
      match lrLookup table nm, fb with
      | some r, .lam pn pbody =>
          let pbody' ← elabS env ((pn, r.dom) :: Γsibs) pbody
          let rest' ← elabLetRecBindings env Γsibs table rest
          -- `r.ty` (RESOLVED, from `table`) — NOT the pattern's own raw `_t` (still an UNRESOLVED
          -- name-based `.tEff [names] _`, never run through `resolveTy`). Using the raw `_t` here
          -- was the actual root cause of a live `effect row mismatch` wall on any sibling whose
          -- OWN function-body annotation (this one) never got resolved against `env.effects`,
          -- while `buildLetRecMulti`'s OUTER re-derivation-thunk ascriptions (built from `tys`,
          -- which IS `r.ty`-sourced via `letRecResolvedTys`) correctly used the RESOLVED
          -- `.tEffR [label]` form — the two ascriptions disagreed on an unresolved-vs-resolved row
          -- reading of the SAME declared type, and `unifyC`/`subRow` saw them as genuinely
          -- different rows (confirmed via a throwaway inlined `#guard` dumping the elaborated tree:
          -- the inner function-body annotation showed `Ty.tEff ["Div"] …` while every OTHER
          -- ascription in the SAME knot showed `Ty.tEffR [3] …`).
          .ok (.annotS (.lam pn pbody') r.ty :: rest')
      | none, _ => throw s!"internal: mutual let rec sibling '{nm}' missing from its own resolved table (#97 item 2)"
      | _, _    => throw s!"internal: mutual let rec sibling '{nm}' is not a function literal despite passing resolveLetRecBindingTys (#97 item 2)"
  termination_by binds => (sizeOf binds, 3)
end

/-- Build the elaboration environment from a program's decl prelude, IN ORDER (a data type may
reference itself + earlier decls; forward references fail loud). Data: encode the μ body
(self ↦ `tVar 0` — no surface μ syntax means self never sits under a nested binder, so depth 0
is always right) and the closed binder-typing payloads (self ↦ the closed μ). Impls: resolve the
target, validate against the trait (op name + param arity). **#112 fix — dispatch mechanism, not
just registration order:** a 2-param op (`.binopS`'s ONLY dispatchable arity) is deferred to
`env.pendingKnots` — NOT elaborated here — so `elabProg` can knot-bind it via `letRecS`'s existing
μ-encoded fixpoint (real recursion, ADR-0073/#95) once the WHOLE program is assembled; this is
what lets a self- or backward-referential call (`tx == ty` on `Self`, or an earlier impl's op)
resolve, where the OLD single-pass splice-based scheme could not (ADR-0097 §3's "recursive-carrier
wall" — confirmed, this session, that a signature-only two-pass ALSO fails: `.binopS` splices
`inst.body` as an already-elaborated VALUE, so a self-call bakes in whatever `insts[idx]` holds AT
ITS OWN elaboration time, not after — no ordering of a signature-then-body two-pass closes that,
only real recursion does). Any OTHER arity (0/1/3+ params) is UNCHANGED from before: PRE-ELABORATED
against the env-so-far here (nested ctors + earlier ops resolve; a self-recursive one still
fail-louds — but `.binopS` never dispatches that arity anyway, so this residual gap is UNREACHABLE
through the operator surface, see `Inst`'s doc comment). PUBLIC (#60 seam): the law-runner harness
needs a real `ElabEnv` (trait/impl-derived) to drive `checkLawOn`, and this is the only constructor
of one from a parsed decl list — no behavior change to non-impl decls, additive visibility only. -/
public def buildEnv (ds : List Decl) : Except String ElabEnv := do
  let mut aliases : List (String × Ty) := []
  let mut ctors   : List (String × CtorInfo) := []
  let mut insts   : InstEnv := []
  let mut pendingKnots : List PendingOpKnot := []
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
          -- ADR-0099: only a SAME-TYPE duplicate (two ctors named `c.1` inside THIS `data`'s own
          -- `cs` list) still refuses — that collision has no bare-name resolution story (which
          -- ctor would the bare name even mean within one type?). A cross-type collision (another
          -- `data` decl elsewhere already owning `c.1`) is no longer a registration-time error —
          -- resolution moves to USE time (`resolveCtor`, below).
          if (ctors.filter (fun p => p.2.dataName == n)).any (fun p => p.1 == c.1) then
            throw s!"duplicate constructor '{c.1}'"
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
          -- ADR-0099: same-type-only duplicate refusal — see the mono `.dataD` arm's comment above.
          if (ctors.filter (fun p => p.2.dataName == n)).any (fun p => p.1 == c.1) then
            throw s!"duplicate constructor '{c.1}'"
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
                  match od.params with
                  -- #112: the 2-param arity `.binopS` actually dispatches — defer to a KNOT, never
                  -- splice. `insts` still gets an entry (so `env.insts.find?` at the call site
                  -- resolves the op NAME/target to something) but `body` is an inert placeholder;
                  -- `knotName` is what dispatch actually uses (see `Inst`'s doc comment).
                  | [p1, p2] =>
                      let kn := s!"#opknot{insts.length}"
                      insts := insts ++ [⟨od.name, vtyOf τR, τR, retR, od.params, .var "#unreachable-knot-placeholder", some kn⟩]
                      pendingKnots := pendingKnots ++ [⟨kn, τR, retR, p1, p2, od.body⟩]
                  -- 0/1/3+-param ops: UNCHANGED pre-#112 behavior — pre-elaborate + splice. Safe:
                  -- `.binopS` never dispatches this arity (its own match requires exactly `[p, q]`),
                  -- so a splice-caused self-reference wall is structurally unreachable here.
                  | _ =>
                      let bodyΓ : NCtx := od.params.map (fun p => (p, embV (vtyOf τR)))
                      let ebody ← elabS ⟨insts, ctors, aliases, gen, [], [], [], [], [], [], []⟩ bodyΓ od.body
                      insts := insts ++ [⟨od.name, vtyOf τR, τR, retR, od.params, ebody, none⟩]
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
          -- ADR-0095 D5 / #93: `resume` is reserved so the future explicit `resume(w)` clause
          -- form (and the eventual multi-shot first-class continuation, Q22/Q27) can land
          -- without breaking any existing program that would otherwise use the name. This is
          -- the OP-NAME half only — the BINDER half (a clause arg-binder, `let`/`fun` name, or
          -- bare reference to `resume` — D5's OWN text: "reserved as an op name AND a binder")
          -- is `pIdent`/`pAtom`'s reserved-word-list entries in `Bang/Frontend/Surface.lean`,
          -- the SAME mechanism `with` (D1) already uses — see those arms' own doc comments.
          if opName == "resume" then
            throw s!"effect {n}: op 'resume' is reserved for the future explicit resume form (ADR-0095 D5 — see issue #93)"
          -- #87: `param` needs the SAME dual reservation `resume` has — `pHClause`'s clause HEAD
          -- (the op name, `op(x) => body`) is ALSO parsed via `pIdent`, so an `effect` declaring an
          -- op literally named `param` would type-check here but make its OWN clause unparseable
          -- (`param(y) => …` is rejected as a reserved-keyword binder, not a clause head) — an
          -- effect with no writable clause for one of its own ops, caught here instead of leaving a
          -- silently-undischargeable op for the coverage check to reject later with a confusing
          -- "no clause" message that hides the real cause.
          if opName == "param" then
            throw s!"effect {n}: op 'param' is reserved for the carried-param clause binder (ADR-0095 D1 — see issue #87)"
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
    | .letD .. | .letRecD .. => pure ()
      -- ADR-0093 D5 (operator ruling): a top-level `let`/`let rec` DECL is a BINDER, not a static
      -- environment entry like `data`/`trait`/`effect` — it never enters `ElabEnv` at all. Instead
      -- it is desugared BEFORE `buildEnv` ever runs (`foldLetDecls`, below) into nested
      -- `Surf.lett`/`Surf.letRecS` wrapping the trailing body — the SAME "wrap the body in a let"
      -- idiom `mergeModules`'s `use`-hoist (and `injectPrelude`'s auto-`use`, ADR-0098) already
      -- use. By the time
      -- `buildEnv` sees a decl list, every `letD`/`letRecD` has ALREADY been folded into `p.body`
      -- (see `elabProg`'s new pre-pass) — this arm exists only so the match stays exhaustive for
      -- a caller that hands `buildEnv` a RAW (pre-fold) decl list (the `mergeModules` internals,
      -- which qualify `letD`/`letRecD` bodies before folding happens).
  return ⟨insts, ctors, aliases, gen, bfns, rawImpls, hktTraits, hktMethodOf, hktImpls, effects, pendingKnots⟩

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
problem — the isos below convert between `Result`/`Option` and this built-in sum). `List a` is
DELIBERATELY NOT here (ADR-0103's own residual finding, not fixed by this pass): its NATURAL ctor
names `Nil`/`Cons` collide, as an UNCONDITIONAL injection, with SEVERAL pre-existing corpus fixtures
that independently chose the SAME bare names for their OWN differently-named list-shaped `data`
decls (`listProg`'s `data IntList = Nil | Cons(…)`, confirmed live: ADR-0099 ambiguous-bare-ctor
errors cascade the moment `List`'s `Nil`/`Cons` become globally visible). `take`/`drop`
(`Prelude.bang`) still work standalone or against a program's OWN `data List a` — only the
convenience of a KERNEL-PROVIDED `List` (so `Cons(…) : List Int` resolves with zero declaration,
matching `Option`/`Result`) is deferred; see the ADR-0103 implementation report. Each type here is
filtered out (like `Str`/`Char`) when the user redeclares it. Library over `data` — NO kernel
primitive (invariant #5). -/
def genericPrelude : List Decl :=
  [ .dataD "Option" ["a"]      [("None", []),           ("Some",  [.tName "a"])],
    .dataD "Result" ["e", "a"] [("Err",  [.tName "e"]), ("Ok",    [.tName "a"])] ]

/-! ## Modules (ADR-0093 D2/D3/D4) — merge-to-flat, PURE half.

File resolution (reading `tokenizer.bang` off disk, same-dir-then-root, cycle detection across the
FILE graph) is `Main.lean`'s job (IO). Everything HERE is a pure function over already-parsed
`Prog`s: qualification + visibility + decl-merge, producing ONE flat `Prog` that `elabProg`/
`buildEnv` consume completely unchanged (D4 — "the kernel never learns modules exist", the fourth
elaborate-away application after ADR-0075/0088/0091). -/

/-- The full set of a module's TOP-LEVEL names that qualification must rename: every decl's own
name, PLUS (for a `data` decl) its constructors — D2's "ctors travel with their type". Function
PARAMETER names are never in this set (they're bound locally; renaming only exact `.var` LEAVES —
never a binder — is safe precisely because a binder can only ever SHADOW a top-level name, never
BE renamed by this pass, so shadowing behaves exactly as it does today). -/
def moduleTopNames (decls : List Decl) : List String :=
  decls.flatMap (fun d => match d with
    | .dataD n _ cs => n :: cs.map (·.1)
    | _             => [d.name])

/-! Rename every FREE occurrence of a name in `names` to `qualifyName modName ·`, everywhere in a
`Surf` — an AST walk (not a token/reprint round-trip, so it needs no `Format` dependency and cannot
silently miss a constructor: every `Surf`/`SurfArgs`/`DArms` arm is listed, mirroring `surfUsesVar`'s
existing exhaustive-walk precedent). A binder that SHADOWS one of `names` (`fun lex => …` inside the
module rebinding its own export) stops the rename at that subtree — ordinary lexical shadowing,
not a module concern. -/
mutual
def qualifyVars (modName : String) (names : List String) : Surf → Surf
  | .lit n       => .lit n
  | .var x       => if names.contains x then .var (qualifyName modName x) else .var x
  | .thunk e     => .thunk (qualifyVars modName names e)
  | .force e     => .force (qualifyVars modName names e)
  | .lett n a b  => if names.contains n then .lett n (qualifyVars modName names a) b   -- shadowed past `n`: stop renaming `n` in `b`
                    else .lett n (qualifyVars modName names a) (qualifyVars modName names b)
  | .lam n e     => if names.contains n then .lam n e else .lam n (qualifyVars modName names e)
  | .app a b     => .app (qualifyVars modName names a) (qualifyVars modName names b)
  | .raise e     => .raise (qualifyVars modName names e)
  | .handle e    => .handle (qualifyVars modName names e)
  | .getS        => .getS
  | .putS e      => .putS (qualifyVars modName names e)
  | .stateS a b  => .stateS (qualifyVars modName names a) (qualifyVars modName names b)
  | .atomS e     => .atomS (qualifyVars modName names e)
  | .newS e      => .newS (qualifyVars modName names e)
  | .readS e     => .readS (qualifyVars modName names e)
  | .writeS a b  => .writeS (qualifyVars modName names a) (qualifyVars modName names b)
  | .inlS e      => .inlS (qualifyVars modName names e)
  | .inrS e      => .inrS (qualifyVars modName names e)
  | .pairS a b   => .pairS (qualifyVars modName names a) (qualifyVars modName names b)
  | .matchS s lx e1 ry e2 =>
      .matchS (qualifyVars modName names s) lx
        (if names.contains lx then e1 else qualifyVars modName names e1) ry
        (if names.contains ry then e2 else qualifyVars modName names e2)
  | .splitS a b p body =>
      .splitS a b (qualifyVars modName names p)
        (if names.contains a || names.contains b then body else qualifyVars modName names body)
  | .binopS op a b => .binopS op (qualifyVars modName names a) (qualifyVars modName names b)
  | .ifS c t e     => .ifS (qualifyVars modName names c) (qualifyVars modName names t) (qualifyVars modName names e)
  | .annotS e t    => .annotS (qualifyVars modName names e) t
  | .unitS         => .unitS
  | .foldS e       => .foldS (qualifyVars modName names e)
  | .unfoldS e     => .unfoldS (qualifyVars modName names e)
  | .matchD s arms => .matchD (qualifyVars modName names s) (qualifyDArmsVars modName names arms)
  | .withCapS k i n b =>
      .withCapS k (qualifyVars modName names i) n (if names.contains n then b else qualifyVars modName names b)
  | .dotPerform r op .none      => .dotPerform (qualifyVars modName names r) op .none
  | .dotPerform r op (.one a)   => .dotPerform (qualifyVars modName names r) op (.one (qualifyVars modName names a))
  | .dotPerform r op (.two a b) => .dotPerform (qualifyVars modName names r) op (.two (qualifyVars modName names a) (qualifyVars modName names b))
  | .letRecS n t f b => if names.contains n then .letRecS n t f b
                         else .letRecS n t (qualifyVars modName names f) (qualifyVars modName names b)
  -- #97 item 2: a mutual group's siblings are ALL simultaneously in scope of EACH OTHER'S bodies
  -- (that is the whole point of `letRecMultiS` over a plain sequential `letRecS` chain) — so unlike
  -- `.lettMulti`'s SEQUENTIAL shadowing, if ANY sibling name shadows one of `names`, that name is
  -- shadowed for EVERY sibling's RHS (not just the ones textually after it) and for `b`.
  | .letRecMultiS binds b =>
      let siblingNames := letRecBindingsNames binds
      let names' := names.filter (fun n => !siblingNames.contains n)
      .letRecMultiS (qualifyLetRecBindingsVars modName names' binds) (qualifyVars modName names' b)
  | .divMark e     => .divMark (qualifyVars modName names e)
  | .lettMulti binds b =>
      -- issue #68: SEQUENTIAL shadowing through the `;`-chain — mirrors `.lett`'s OWN rule (a
      -- binding matching one of `names` shadows it for everything AFTER, including `b`), just
      -- threaded across `LetBindings.cons` instead of nested `.lett`s. `qualifyLetBindingsVars`
      -- returns whether ANY binding shadowed (⟹ stop qualifying `b`, matching `.lett`'s own arm).
      let (binds', shadowed) := qualifyLetBindingsVars modName names binds
      .lettMulti binds' (if shadowed then b else qualifyVars modName names b)
  -- #21 s7probe: `h` (the cap binder) shadows exactly like `.withCapS`'s own `n` above; `x` inside
  -- each clause shadows PER-CLAUSE (`qualifyHClausesVars`'s own arm, the `qualifyDArmsVars` precedent).
  | .handleCustomS lbl n p? h cls b =>
      .handleCustomS lbl (qualifyVars modName names n)
        (match p? with
          | .none    => .none
          | .one p   => .one (qualifyVars modName names p)
          | .two a b' => .two (qualifyVars modName names a) (qualifyVars modName names b'))
        h (qualifyHClausesVars modName names cls)
        (if names.contains h then b else qualifyVars modName names b)
def qualifyDArmsVars (modName : String) (names : List String) : DArms → DArms
  | .nil              => .nil
  | .cons c ps b rest =>
      .cons c ps (if ps.any names.contains then b else qualifyVars modName names b) (qualifyDArmsVars modName names rest)
def qualifyHClausesVars (modName : String) (names : List String) : HClauses → HClauses
  | .nil                => .nil
  | .cons op x b rest =>
      .cons op x (if names.contains x then b else qualifyVars modName names b) (qualifyHClausesVars modName names rest)
/-- Qualify a `;`-binding chain (issue #68), threading shadowing sequentially: once a binding's
name matches one of `names`, EVERY later binding's RHS (and the eventual body) stops being
qualified — mirroring `.lett`'s own "shadowed past `n`" rule, applied binding-by-binding. Each
binding's OWN RHS `e` is always qualified (it is evaluated in the OUTER scope, before its own
name is bound — the same reading `.lett`'s `a` gets). Returns the qualified chain plus whether
shadowing was ever triggered (the caller uses this to decide `body`'s own qualification, matching
`.lett`'s `if names.contains n then … b … else …`). -/
def qualifyLetBindingsVars (modName : String) (names : List String) : LetBindings → LetBindings × Bool
  | .nil            => (.nil, false)
  | .cons n e rest  =>
      let e' := qualifyVars modName names e
      if names.contains n then (.cons n e' rest, true)   -- shadowed from HERE on: rest stays UNqualified
      else
        let (rest', shadowed) := qualifyLetBindingsVars modName names rest
        (.cons n e' rest', shadowed)
/-- Qualify a `let rec … and …` sibling chain (#97 item 2): `names` has ALREADY had every sibling
name filtered out by the caller (`.letRecMultiS`'s own arm above) — every sibling RHS sees the SAME
already-filtered `names`, since mutual siblings are simultaneously in scope of each other (no
sequential shadowing threading needed here, unlike `qualifyLetBindingsVars`). -/
def qualifyLetRecBindingsVars (modName : String) (names : List String) : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons n t e rest    => .cons n t (qualifyVars modName names e) (qualifyLetRecBindingsVars modName names rest)
end

/-! Rename a `Ty.tName`/`Ty.tApp` occurrence of an imported `data` type to its qualified form
(`geom_Pair`) — EXCEPT one this file `use`d (`use tokenizer (Token)` keeps `Token` unqualified in
an ascription too, mirroring `qualifyDArmsAccess`'s ctor-pattern rule: `use` is the ONE mechanism
that hoists a name into unqualified scope, D2). `dataTyOwners` maps a type name to its owning
module; `usedNames` is the flat set of names this file's `use`s named. -/
mutual
def qualifyTyName (dataTyOwners : List (String × String)) (usedNames : List String) : Ty → Ty
  | .tInt        => .tInt
  | .tUnit       => .tUnit
  | .tArr a b    => .tArr (qualifyTyName dataTyOwners usedNames a) (qualifyTyName dataTyOwners usedNames b)
  | .tSum a b    => .tSum (qualifyTyName dataTyOwners usedNames a) (qualifyTyName dataTyOwners usedNames b)
  | .tProd a b   => .tProd (qualifyTyName dataTyOwners usedNames a) (qualifyTyName dataTyOwners usedNames b)
  | .tThunk a    => .tThunk (qualifyTyName dataTyOwners usedNames a)
  | .tSelf       => .tSelf
  | .tName n     => if usedNames.contains n then .tName n
                     else match dataTyOwners.lookup n with
                          | some modName => .tName (qualifyName modName n)
                          | none         => .tName n
  | .tApp n args => if usedNames.contains n then .tApp n (qualifyTyArgs dataTyOwners usedNames args)
                     else match dataTyOwners.lookup n with
                          | some modName => .tApp (qualifyName modName n) (qualifyTyArgs dataTyOwners usedNames args)
                          | none         => .tApp n (qualifyTyArgs dataTyOwners usedNames args)
  | .tMu a       => .tMu (qualifyTyName dataTyOwners usedNames a)
  | .tVar i      => .tVar i
  | .tCap ℓ      => .tCap ℓ   -- #84 gap 1: never appears pre-elaboration (the parser only ever
                                -- produces `tApp "Cap" (.one (.tName effN))`, resolved to `tCap`
                                -- LATER by `resolveTyG` — this qualification pass runs BEFORE that,
                                -- so this arm is unreachable in practice; enumerated for totality,
                                -- matching the file's "no catch-all" discipline)
  | .tEff ns a   => .tEff ns (qualifyTyName dataTyOwners usedNames a)
  | .tEffR ls a  => .tEffR ls (qualifyTyName dataTyOwners usedNames a)   -- #90: same unreachable-
                                -- pre-elaboration reasoning as `tCap` above — enumerated for totality
def qualifyTyArgs (dataTyOwners : List (String × String)) (usedNames : List String) : TyArgs → TyArgs
  | .one a   => .one (qualifyTyName dataTyOwners usedNames a)
  | .two a b => .two (qualifyTyName dataTyOwners usedNames a) (qualifyTyName dataTyOwners usedNames b)
end


/-- Qualify one `Decl`'s internal bodies (trait law bodies / impl op bodies / a bounded fn's body) —
`data`/`effect` decls carry no `Surf` but DO carry `Ty`s that can reference ANOTHER decl of the
SAME module (`data Total = T(Helper)`) — those get qualified too (`qTy`, built from `names` as an
intra-module `dataTyOwners` with no `usedNames` exclusion, since every name in `names` is this
module's OWN top-level name and must qualify unconditionally here — the entry-file cross-module
rewrite that DOES need a `usedNames` exclusion is `qualifyTyName`'s other call site, in
`mergeModules` directly).

`.letRecD`'s own SELF-reference is special: `qualifyDeclName` (below) unconditionally renames a
`letRecD`'s binding name to its qualified form (`fac` ⟹ `lib_fac`, no `usedCtors`-style exclusion
— unlike a ctor, a `let rec`'s binding site always qualifies since the `use`-hoist alias needs a
qualified target to point at). So when `n` was excluded from `names` (because THIS file `use`d
it, #97), the self-call inside `e` must still be rewritten — `names` alone would leave `$fac`
unqualified inside a body now bound as `lib_fac`, an unbound-variable at elaboration (issue #97:
`use Mod (f)` hoisted a plain `let` cleanly but broke a `pub let rec`'s recursive self-call,
because ordinary `names`-filtering that keeps a `use`d name unqualified is right for EXTERNAL
references but wrong for `letRecD`'s one INTERNAL reference to its own now-always-qualified
name). `n :: names` restores exactly that one name for this decl's own body walk (a `List.contains`
membership check downstream, so the extra copy if `n` was already present is harmless), leaving the
shared `names` list (and every OTHER decl's qualification) untouched. -/
def qualifyDeclBody (modName : String) (names : List String) : Decl → Decl :=
  let qTy := qualifyTyName (names.map (·, modName)) []
  fun d => match d with
  | .dataD n ps cs        => .dataD n ps (cs.map (fun (c, tys) => (c, tys.map qTy)))
  | .effectD n ops        => .effectD n (ops.map (fun (op, ty) => (op, qTy ty)))
  | .traitD n ps ops laws =>
      .traitD n ps ops (laws.map (fun l => { l with body := qualifyVars modName names l.body }))
  | .implD n t ops        =>
      .implD n (qTy t) (ops.map (fun o => { o with body := qualifyVars modName names o.body }))
  | .fnD n ps ty tr tv b  => .fnD n ps (qTy ty) tr tv (qualifyVars modName names b)
  | .letD n ty e          => .letD n (ty.map qTy) (qualifyVars modName names e)
  | .letRecD n t e        => .letRecD n (qTy t) (qualifyVars modName (n :: names) e)

/-- Rename a `Decl`'s OWN top-level name (and a `data`'s ctors) to its qualified form — the
"declaration side" of qualification, paired with `qualifyDeclBody`'s "reference side". A ctor
NAMED in `usedCtors` stays BARE in the merged decl list (a `use`d ctor is meant to be written
unqualified, and a `data` decl's ctor list can rename each ctor independently — nothing requires
uniform renaming across one type's ctors) — the TYPE name itself still always qualifies (there is
no unqualified-type-name analogue: `use tokenizer (Token)` hoists the CTORS `Token` carries per
D2's "ctors travel with their type" wording, read literally as ctors, not the type name, which
`qualifyTyName`'s OWN `usedNames` exclusion handles separately at ascription sites). -/
def qualifyDeclName (modName : String) (usedCtors : List String) : Decl → Decl
  | .dataD n ps cs        =>
      .dataD (qualifyName modName n) ps (cs.map (fun (c, tys) => (if usedCtors.contains c then c else qualifyName modName c, tys)))
  | .effectD n ops        => .effectD (qualifyName modName n) ops
  | .traitD n ps ops laws => .traitD (qualifyName modName n) ps ops laws
  | .implD n t ops        => .implD n t ops          -- an impl's "name" is its TRAIT (already qualified via the trait's own decl)
  | .fnD n ps ty tr tv b  => .fnD (qualifyName modName n) ps ty tr tv b
  | .letD n ty e          => .letD (qualifyName modName n) ty e
  | .letRecD n t e        => .letRecD (qualifyName modName n) t e

/-- Qualify a whole parsed module `Prog`: every top-level name (`moduleTopNames`) becomes
`modname_name`, everywhere in every decl body AND the trailing body expression — EXCEPT a ctor this
file `use`d (`usedCtors`, kept bare so the importing file's unqualified reference resolves). Only
`pub`-visible names are importABLE (`mergeModules` enforces that at the exposure boundary), but
qualification renames every OTHER top-level name (pub or not) uniformly — a private decl still
needs to be REACHABLE by its own qualified name from another decl of the same module. -/
def qualifyModule (modName : String) (usedCtors : List String) (p : Prog) : Prog :=
  let names := (moduleTopNames p.decls).filter (fun n => !usedCtors.contains n)
  { p with
    decls := p.decls.map (fun d => qualifyDeclName modName usedCtors (qualifyDeclBody modName names d))
    body  := qualifyVars modName names p.body }


/-- Is `n` a PUBLICLY-visible name of module `modP` (D3)? Visible either directly
(`modP.pubNames.contains n`, the decl's OWN name) or as a CTOR of a `pub data` type (D3: "a `pub
data` exports its ctors all-or-nothing") — `pubNames` only ever records a decl's OWN name
(`Decl.name`, never a ctor), so a ctor's publicity is a SEPARATE lookup against its owning `pub
data`'s ctor list. Shared by `firstPrivateUse` (the `use`-path gate) and `firstPrivateDotAccess`
(the qualified-access gate, #73) — ONE visibility predicate, two call sites naming a name. -/
def isPubName (modP : Prog) (n : String) : Bool :=
  modP.pubNames.contains n ||
  modP.decls.any (fun d => match d with
    | .dataD dn _ cs => modP.pubNames.contains dn && cs.any (fun (c, _) => c == n)
    | _              => false)

/-- Does `p`'s header only reference NAMES the resolved module set actually exports (D3 — private
by default)? Returns the first violation as `(modName, name)` if `use tokenizer (secret)` names a
non-`pub` decl of `tokenizer` — the loud error names BOTH the module and the specific private name
(agent-first: the error teaches the fix, not just "unknown name"). `resolved` maps a module name to
its (unqualified, pre-merge) `Prog`, so visibility is checked against the ORIGINAL `pubNames`. -/
def firstPrivateUse (resolved : List (String × Prog)) (p : Prog) : Option (String × String) :=
  p.uses.findSome? (fun u =>
    match resolved.lookup u.modName with
    | none      => none    -- unresolved import is a SEPARATE (IO-layer) error, not this function's job
    | some modP => (u.names.find? (fun n => !isPubName modP n)).map (fun n => (u.modName, n)))

/-! Does a BARE QUALIFIED reference (`Mod.name`, `.dotPerform (.var m) op _` with `m` a known
import) anywhere in `e` name a NON-`pub` decl of the module it qualifies (#73 — D3's enforcement
hole: `firstPrivateUse` above only ever gated the `use` path, so `$(Bare.plain) 41` bypassed
visibility entirely even though `use Bare (plain)` correctly rejected the same name). Mirrors
`surfUsesVar`'s exhaustive-traversal shape (a query over `Surf`, paired with the REWRITE
`qualifyDotAccess` performs on the same shape) rather than `firstPrivateUse`'s flat list scan,
because a qualified access can appear ANYWHERE in an expression tree, not just in a header's `use`
list. Only the two-arg qualified shapes (`.dotPerform (.var m) op _`) are checked — an
`m`-that-isn't-an-import, or a receiver that itself needs recursing into, is walked structurally
the same way `qualifyDotAccess` recurses. First violation wins (short-circuit via `orElse`, no
worse than `findSome?`'s laziness). -/
mutual
def firstPrivateDotAccess (resolved : List (String × Prog)) : Surf → Option (String × String)
  | .dotPerform (.var m) op _ =>
      match resolved.lookup m with
      | some modP => if isPubName modP op then none else some (m, op)
      | none      => none    -- `m` isn't a known import (an ordinary capability receiver) — not this function's job
  | .dotPerform r _ args           => firstPrivateDotAccess resolved r <|> argsFirstPrivateDotAccess resolved args
  | .lit _ | .var _ | .getS | .unitS => none
  | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
  | .lam _ e | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ => firstPrivateDotAccess resolved e
  | .lett _ a b | .app a b | .stateS a b | .writeS a b | .pairS a b | .splitS _ _ a b
  | .binopS _ a b                  => firstPrivateDotAccess resolved a <|> firstPrivateDotAccess resolved b
  | .matchS s _ l _ r              => firstPrivateDotAccess resolved s <|> firstPrivateDotAccess resolved l <|> firstPrivateDotAccess resolved r
  | .ifS c t e                     => firstPrivateDotAccess resolved c <|> firstPrivateDotAccess resolved t <|> firstPrivateDotAccess resolved e
  | .matchD s arms                 => firstPrivateDotAccess resolved s <|> dArmsFirstPrivateDotAccess resolved arms
  | .withCapS _ i _ b              => firstPrivateDotAccess resolved i <|> firstPrivateDotAccess resolved b
  | .letRecS _ _ f b               => firstPrivateDotAccess resolved f <|> firstPrivateDotAccess resolved b
  -- #68 sugar: this walk runs PRE-erasure (mergeModules operates on raw per-file trees), so
  -- `.lettMulti` is reachable — scan every binding RHS, then the body (Surface.lean:214).
  | .lettMulti binds b             => bindsFirstPrivateDotAccess resolved binds <|> firstPrivateDotAccess resolved b
  -- #21 s7probe: scan `n`/`p`/every clause body/`body`, the `withCapS` precedent immediately above.
  | .handleCustomS _lbl n p? _h cls b =>
      firstPrivateDotAccess resolved n <|> argsFirstPrivateDotAccess resolved p?
        <|> hClausesFirstPrivateDotAccess resolved cls <|> firstPrivateDotAccess resolved b
  -- #97 item 2: scan every sibling RHS, then the body — the `.lettMulti` precedent immediately above.
  | .letRecMultiS binds b           => lrBindsFirstPrivateDotAccess resolved binds <|> firstPrivateDotAccess resolved b
def bindsFirstPrivateDotAccess (resolved : List (String × Prog)) : LetBindings → Option (String × String)
  | .nil           => none
  | .cons _ e rest => firstPrivateDotAccess resolved e <|> bindsFirstPrivateDotAccess resolved rest
def lrBindsFirstPrivateDotAccess (resolved : List (String × Prog)) : LetRecBindings → Option (String × String)
  | .nil             => none
  | .cons _ _ e rest => firstPrivateDotAccess resolved e <|> lrBindsFirstPrivateDotAccess resolved rest
def dArmsFirstPrivateDotAccess (resolved : List (String × Prog)) : DArms → Option (String × String)
  | .nil             => none
  | .cons _ _ b rest => firstPrivateDotAccess resolved b <|> dArmsFirstPrivateDotAccess resolved rest
def hClausesFirstPrivateDotAccess (resolved : List (String × Prog)) : HClauses → Option (String × String)
  | .nil               => none
  | .cons _ _ b rest   => firstPrivateDotAccess resolved b <|> hClausesFirstPrivateDotAccess resolved rest
def argsFirstPrivateDotAccess (resolved : List (String × Prog)) : SurfArgs → Option (String × String)
  | .none    => none
  | .one a   => firstPrivateDotAccess resolved a
  | .two a b => firstPrivateDotAccess resolved a <|> firstPrivateDotAccess resolved b
end

/-- Scan every decl body + the trailing body of `p` for the first private qualified access
(`firstPrivateDotAccess`) — the PROGRAM-LEVEL wrapper `mergeModules` gates the entry file with,
mirroring how `firstPrivateUse` gates `p.uses`. Decl bodies checked: `traitD`'s laws, `implD`'s
op bodies, `fnD`/`letD`/`letRecD`'s bodies — every place a `Surf` expression lives in a `Decl`. -/
def firstPrivateDotAccessProg (resolved : List (String × Prog)) (p : Prog) : Option (String × String) :=
  p.decls.findSome? (fun d => match d with
    | .traitD _ _ _ laws => laws.findSome? (fun l => firstPrivateDotAccess resolved l.body)
    | .implD _ _ ops     => ops.findSome? (fun o => firstPrivateDotAccess resolved o.body)
    | .fnD _ _ _ _ _ b   => firstPrivateDotAccess resolved b
    | .letD _ _ e        => firstPrivateDotAccess resolved e
    | .letRecD _ _ e     => firstPrivateDotAccess resolved e
    | .dataD ..          => none
    | .effectD ..        => none)
  <|> firstPrivateDotAccess resolved p.body

/-! Rewrite BARE qualified access (`tokenizer.lex`, parsed as `.dotPerform (.var "tokenizer") "lex"
.none` since `.` is the SAME token `h.get` uses — ADR-0070) into the ordinary qualified identifier
`.var "tokenizer_lex"`, for every `modName` in `imports`. Restricted to the EXACT nullary-dot shape
with a bare-`var` receiver naming a KNOWN import (never touching a real capability call: an
undeclared-import receiver, or one WITH arguments, is left as `.dotPerform` unchanged — so a
program using both `import net` and a capability named `net` cannot arise, since a name is either
an import or isn't; the elaborator's own duplicate-name checks catch a real collision).

`ctorOwners : List (String × String)` maps an UN-`use`d imported ctor name to its owning module —
needed because a `data` CONSTRUCTOR PATTERN (`match p { Mk(a, b) -> … }`, `DArms.cons "Mk" …`) is a
bare `String` the elaborator resolves by exact-match against the ctor table, never a `Surf.var`, so
the ordinary value-reference rewrite above cannot reach it. Without a `use`, a bare-`import`ed
module's ctor PATTERNS must be written qualified (`geom_Mk(a, b)`) by the user — v1 does not
rewrite an unqualified pattern name to its qualified form under bare `import` (only `use` hoists a
ctor to unqualified scope, matching D2's ctor-travel wording, which names `use` as the hoisting
mechanism, not `import`). This function DOES still rewrite the *pattern* to its qualified name
when the name matches a `ctorOwners` entry, so `mergeModules` can offer this rewrite once it knows
which ctors came from where (kept general here rather than special-cased to a single call site). -/
mutual
def qualifyDotAccess (imports : List String) (ctorOwners : List (String × String)) (qTy : Ty → Ty) : Surf → Surf
  | .dotPerform (.var m) op .none =>
      if imports.contains m then .var (qualifyName m op)
      else .dotPerform (qualifyDotAccess imports ctorOwners qTy (.var m)) op .none
  | .dotPerform (.var m) op args =>
      -- a qualified CTOR call (`geom.Mk(3, 4)`) is the SAME shape as a nullary qualified access,
      -- just applied to args afterward: `geom_Mk(3, 4)` re-parses as `.app (.var "geom_Mk") …` —
      -- but `Mk(3, 4)` at the SURFACE is `pCtor`'s own token-adjacent form, not `.app`, so here we
      -- rebuild it as an ordinary application of the qualified ctor NAME to the (qualified) args —
      -- `.app (.var qualified) arg` for 1 arg, and nested `.app`s for 2 (matching how a 2-ary ctor
      -- constructor CALL already lowers via `pairS`, since ctor args are always exactly a pair at
      -- the surface — see `pCtor`'s `≤2`-arity note).
      if imports.contains m then
        match args with
        | .none      => .var (qualifyName m op)
        | .one a     => .app (.var (qualifyName m op)) (qualifyDotAccess imports ctorOwners qTy a)
        | .two a b   => .app (.var (qualifyName m op))
            (.pairS (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b))
      else .dotPerform (qualifyDotAccess imports ctorOwners qTy (.var m)) op (qualifyDotAccessArgs imports ctorOwners qTy args)
  | .dotPerform r op args   => .dotPerform (qualifyDotAccess imports ctorOwners qTy r) op (qualifyDotAccessArgs imports ctorOwners qTy args)
  | .lit n                  => .lit n
  | .var x                  => .var x
  | .thunk e                => .thunk (qualifyDotAccess imports ctorOwners qTy e)
  | .force e                => .force (qualifyDotAccess imports ctorOwners qTy e)
  | .lett n a b             => .lett n (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
  | .lam n e                => .lam n (qualifyDotAccess imports ctorOwners qTy e)
  | .app a b                => .app (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
  | .raise e                => .raise (qualifyDotAccess imports ctorOwners qTy e)
  | .handle e                => .handle (qualifyDotAccess imports ctorOwners qTy e)
  | .getS                   => .getS
  | .putS e                 => .putS (qualifyDotAccess imports ctorOwners qTy e)
  | .stateS a b              => .stateS (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
  | .atomS e                 => .atomS (qualifyDotAccess imports ctorOwners qTy e)
  | .newS e                  => .newS (qualifyDotAccess imports ctorOwners qTy e)
  | .readS e                 => .readS (qualifyDotAccess imports ctorOwners qTy e)
  | .writeS a b               => .writeS (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
  | .inlS e                  => .inlS (qualifyDotAccess imports ctorOwners qTy e)
  | .inrS e                  => .inrS (qualifyDotAccess imports ctorOwners qTy e)
  | .pairS a b                => .pairS (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
  | .matchS s lx e1 ry e2      => .matchS (qualifyDotAccess imports ctorOwners qTy s) lx (qualifyDotAccess imports ctorOwners qTy e1) ry (qualifyDotAccess imports ctorOwners qTy e2)
  | .splitS a b p body        => .splitS a b (qualifyDotAccess imports ctorOwners qTy p) (qualifyDotAccess imports ctorOwners qTy body)
  | .binopS op a b            => .binopS op (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
  | .ifS c t e                 => .ifS (qualifyDotAccess imports ctorOwners qTy c) (qualifyDotAccess imports ctorOwners qTy t) (qualifyDotAccess imports ctorOwners qTy e)
  | .annotS e t                => .annotS (qualifyDotAccess imports ctorOwners qTy e) (qTy t)
  | .unitS                    => .unitS
  | .foldS e                  => .foldS (qualifyDotAccess imports ctorOwners qTy e)
  | .unfoldS e                => .unfoldS (qualifyDotAccess imports ctorOwners qTy e)
  | .matchD s arms             => .matchD (qualifyDotAccess imports ctorOwners qTy s) (qualifyDArmsAccess imports ctorOwners qTy arms)
  | .withCapS k i n b           => .withCapS k (qualifyDotAccess imports ctorOwners qTy i) n (qualifyDotAccess imports ctorOwners qTy b)
  | .letRecS n t f b            => .letRecS n (qTy t) (qualifyDotAccess imports ctorOwners qTy f) (qualifyDotAccess imports ctorOwners qTy b)
  | .divMark e                  => .divMark (qualifyDotAccess imports ctorOwners qTy e)
  | .lettMulti binds b           => .lettMulti (qualifyLetBindingsAccess imports ctorOwners qTy binds) (qualifyDotAccess imports ctorOwners qTy b)
  -- #21 s7probe: the `withCapS` precedent immediately above — `n`/`p`/every clause body/`body` all
  -- recurse; `h` (the cap binder) is left AS-IS (no qualification target, matching `withCapS`'s `n`).
  | .handleCustomS lbl n p? h cls b =>
      .handleCustomS lbl (qualifyDotAccess imports ctorOwners qTy n) (qualifyDotAccessArgs imports ctorOwners qTy p?) h
        (qualifyHClausesAccess imports ctorOwners qTy cls) (qualifyDotAccess imports ctorOwners qTy b)
  -- #97 item 2: the `.letRecS`/`.lettMulti` precedent — every sibling's type + RHS + the body recurse.
  | .letRecMultiS binds b        => .letRecMultiS (qualifyLetRecBindingsAccess imports ctorOwners qTy binds) (qualifyDotAccess imports ctorOwners qTy b)
def qualifyDotAccessArgs (imports : List String) (ctorOwners : List (String × String)) (qTy : Ty → Ty) : SurfArgs → SurfArgs
  | .none      => .none
  | .one a     => .one (qualifyDotAccess imports ctorOwners qTy a)
  | .two a b   => .two (qualifyDotAccess imports ctorOwners qTy a) (qualifyDotAccess imports ctorOwners qTy b)
def qualifyDArmsAccess (imports : List String) (ctorOwners : List (String × String)) (qTy : Ty → Ty) : DArms → DArms
  | .nil               => .nil
  | .cons c ps b rest  =>
      let c' := match ctorOwners.lookup c with
        | some modName => qualifyName modName c
        | none         => c
      .cons c' ps (qualifyDotAccess imports ctorOwners qTy b) (qualifyDArmsAccess imports ctorOwners qTy rest)
def qualifyHClausesAccess (imports : List String) (ctorOwners : List (String × String)) (qTy : Ty → Ty) : HClauses → HClauses
  | .nil                 => .nil
  | .cons op x b rest     => .cons op x (qualifyDotAccess imports ctorOwners qTy b) (qualifyHClausesAccess imports ctorOwners qTy rest)
def qualifyLetBindingsAccess (imports : List String) (ctorOwners : List (String × String)) (qTy : Ty → Ty) : LetBindings → LetBindings
  | .nil            => .nil
  | .cons n e rest  => .cons n (qualifyDotAccess imports ctorOwners qTy e) (qualifyLetBindingsAccess imports ctorOwners qTy rest)
def qualifyLetRecBindingsAccess (imports : List String) (ctorOwners : List (String × String)) (qTy : Ty → Ty) : LetRecBindings → LetRecBindings
  | .nil               => .nil
  | .cons n t e rest    => .cons n (qTy t) (qualifyDotAccess imports ctorOwners qTy e) (qualifyLetRecBindingsAccess imports ctorOwners qTy rest)
end

/-- Rewrite a MODULE's OWN bare qualified access (`Json.JNull`) to ITS OWN imports/uses, BEFORE
`qualifyModule` renames the module's own top-level names. A transitively-imported module (e.g.
`Print.bang`, itself `import Json`-ing) is loaded by `Main.lean`'s resolver as a RAW, unqualified
`Prog` — its own `Json.JNull` reference is still `.dotPerform (.var "Json") "JNull" .none` when
`mergeModules` sees it, since only the ENTRY file's bare access used to get this treatment. Without
this pass, a transitively-imported module's own qualified references are never rewritten, and its
merged decl body still names the UNQUALIFIED `Json` — an "unbound variable" at elaboration, caught
dogfooding the JSON split (`examples/json/Print.bang`, which imports `Json` for `Json.JNull` etc).
`resolved` is the GLOBAL resolution list (every module knows every OTHER module's ctor/data-type
ownership regardless of who imports what — the rewrite target is universal, only the SOURCE
module's own `imports`/`uses` decide what's eligible to rewrite FROM inside it). -/
def qualifyModuleOwnImports (resolved : List (String × Prog)) (p : Prog) : Prog :=
  let usedNamesLiteral := p.uses.flatMap (fun u => u.names)
  let usedNames := usedNamesLiteral ++ resolved.flatMap (fun (_, modP) =>
    modP.decls.flatMap (fun d => match d with
      | .dataD n _ cs => if usedNamesLiteral.contains n then cs.map (·.1) else []
      | _             => []))
  let importNames := p.imports.map (·.modName) ++ p.uses.map (·.modName)
  let allCtorOwners : List (String × String) := resolved.flatMap (fun (modName, modP) =>
    modP.decls.flatMap (fun d => match d with
      | .dataD _ _ cs => cs.map (fun (c, _) => (c, modName))
      | _             => []))
  let ctorOwners := allCtorOwners.filter (fun (c, _) => !usedNames.contains c)
  let dataTyOwners : List (String × String) := resolved.flatMap (fun (modName, modP) =>
    modP.decls.flatMap (fun d => match d with | .dataD n _ _ => [(n, modName)] | _ => []))
  let qTy := qualifyTyName dataTyOwners usedNames
  let usedPlainFns : List (String × String) := p.uses.flatMap (fun u =>
    u.names.filterMap (fun n =>
      if (allCtorOwners.lookup n).isSome || (dataTyOwners.lookup n).isSome then none else some (n, u.modName)))
  let decls := p.decls.map (fun d => match d with
    | .dataD n ps cs        => .dataD n ps (cs.map (fun (c, tys) => (c, tys.map qTy)))
    | .effectD n ops        => .effectD n (ops.map (fun (op, ty) => (op, qTy ty)))
    | .traitD n ps ops laws => .traitD n ps ops (laws.map (fun l => { l with body := qualifyDotAccess importNames ctorOwners qTy l.body }))
    | .implD n t ops        => .implD n (qTy t) (ops.map (fun o => { o with body := qualifyDotAccess importNames ctorOwners qTy o.body }))
    | .fnD n ps ty tr tv b  => .fnD n ps (qTy ty) tr tv (qualifyDotAccess importNames ctorOwners qTy b)
    | .letD n ty e          => .letD n (ty.map qTy) (qualifyDotAccess importNames ctorOwners qTy e)
    | .letRecD n t e        => .letRecD n (qTy t) (qualifyDotAccess importNames ctorOwners qTy e))
  let body := qualifyDotAccess importNames ctorOwners qTy p.body
  let aliasDecls : List Decl := usedPlainFns.map (fun (n, modName) => .letD n none (Surf.var (qualifyName modName n)))
  { p with decls := aliasDecls ++ decls, body := body }

/-- Merge the entry program `p` with its resolved imports (`resolved : List (String × Prog)`,
UNQUALIFIED as parsed, in DEPENDENCY order — each module before anything that imports it, so a
transitive import's own quals are already applied to it by the time it's folded in): qualify each
imported module's decls (`qualifyModule`), prepend them (topological order = decl-list order,
matching how the existing `prelude ++ p.decls` convention already threads dependency-first), rewrite
the entry file's OWN bare qualified access (`tokenizer.lex` → `tokenizer_lex`, `qualifyDotAccess`),
and hoist each `use`d name into unqualified scope via a wrapping `let` (`use tokenizer (lex)` ⟹
`let lex = tokenizer_lex in <body>` — the SAME "wrap the body in a let" idiom `injectPrelude`
(ADR-0098) rides too, since it is just ANOTHER caller of this same `use`-hoist). Visibility (D3)
is checked FIRST, against BOTH surfaces a
private name can be named from: the `use` header (`firstPrivateUse`) AND a bare qualified
`Mod.name` reference anywhere in the entry file's decls/body (`firstPrivateDotAccessProg`, #73 fix
— previously `tokenizer.secret` silently RESOLVED via `qualifyDotAccess`'s rewrite to
`tokenizer_secret`, which a private decl still merges in as reachable-by-its-own-module per the
comment below, so the qualified path bypassed D3 entirely even though the semantically-equivalent
`use tokenizer (secret)` correctly rejected the same name). Both checks throw the SAME message
shape before any qualification happens, naming the exact `(module, name)` pair D3's wording
requires. -/
public def mergeModules (resolved : List (String × Prog)) (p : Prog) : Except String Prog := do
  match firstPrivateUse resolved p with
  | some (modName, name) =>
      throw s!"'{name}' is private to module '{modName}' (use `pub` to export it, ADR-0093 D3)"
  | none => pure ()
  match firstPrivateDotAccessProg resolved p with
  | some (modName, name) =>
      throw s!"'{name}' is private to module '{modName}' (use `pub` to export it, ADR-0093 D3)"
  | none => pure ()
  -- `usedNames` starts from the LITERAL `use` list, then EXPANDS: `use mod (Ty)` naming a `data`
  -- type's OWN name also hoists its ctors unqualified (D2 — "ctors travel with their type", read
  -- literally: naming the TYPE is enough, not just naming a ctor directly).
  let usedNamesLiteral := p.uses.flatMap (fun u => u.names)
  let usedNames := usedNamesLiteral ++ resolved.flatMap (fun (_, modP) =>
    modP.decls.flatMap (fun d => match d with
      | .dataD n _ cs => if usedNamesLiteral.contains n then cs.map (·.1) else []
      | _             => []))
  let mut mergedDecls : List Decl := []
  for (modName, modP) in resolved do
    -- FIRST rewrite `modP`'s OWN bare qualified access to ITS OWN imports (`qualifyModuleOwnImports`
    -- — a transitively-imported module can itself `import` something, e.g. `Print.bang` importing
    -- `Json`; without this pass its `Json.JNull` reference stays unrewritten and becomes an unbound
    -- variable once merged), THEN rewrite ITS OWN top-level names to their qualified form
    -- (`qualifyModule` — so `modP`'s reference to `Json.JNull` — now `Json_JNull` — is NOT
    -- re-qualified a second time as if `Json_JNull` were one of `modP`'s OWN names).
    let modOwn := qualifyModuleOwnImports resolved modP
    let modQ := qualifyModule modName usedNames modOwn
    -- EVERY decl of an imported module is merged in (private ones included) — a private decl must
    -- still be REACHABLE so another decl of the SAME module (already merged) can call it. D3's
    -- visibility is enforced at the NAME-EXPOSURE boundary (`firstPrivateUse` above, gating what
    -- THIS file's `use`/qualified access may NAME), not by omitting the decl from the kernel term —
    -- exactly mirroring how a private field still exists in a compiled Rust crate.
    mergedDecls := mergedDecls ++ modQ.decls
  let importNames := resolved.map Prod.fst
  -- CLASSIFY every resolved module's names so `use`/qualified access rewrites each the RIGHT way —
  -- a `data` type name, a data CONSTRUCTOR, and a plain `fn`/`effect`/`trait` name are three
  -- DIFFERENT surface positions (a type ascription's `Ty.tName`, a match PATTERN's bare `String`,
  -- and an ordinary `Surf.var` reference respectively), so one uniform `let`-alias (which only
  -- works for the third kind — ctors and type names are never first-class VALUES a `let` can
  -- bind) is unsound. `ctorOwners` covers kind 2 (pattern rewrite for an UN-`use`d ctor — `use`
  -- keeps a ctor BARE both in the merged decl list, `qualifyModule` above, and here, so there is
  -- nothing to rewrite for it; only a bare `import`'s ctor needs the qualified pattern spelling).
  -- Type names (kind 1) are handled by `qualifyTyName` (ascriptions/decl signatures) below. Only
  -- kind 3 (plain functions) gets the `let`-alias wrap.
  let allCtorOwners : List (String × String) := resolved.flatMap (fun (modName, modP) =>
    modP.decls.flatMap (fun d => match d with
      | .dataD _ _ cs => cs.map (fun (c, _) => (c, modName))
      | _             => []))
  let ctorOwners : List (String × String) :=
    allCtorOwners.filter (fun (c, _) => !usedNames.contains c)
  let dataTyOwners : List (String × String) := resolved.flatMap (fun (modName, modP) =>
    modP.decls.flatMap (fun d => match d with | .dataD n _ _ => [(n, modName)] | _ => []))
  -- a `use`d name that is a PLAIN fn/effect/trait (not a ctor, not a data type) gets the
  -- `let`-alias wrap — the one kind for which that mechanism is sound. Classified against the
  -- UNFILTERED `allCtorOwners` (not `ctorOwners`, which excludes `use`d ctors BY DESIGN — using
  -- the filtered set here would misclassify a `use`d ctor as a "plain fn").
  let usedPlainFns : List (String × String) := p.uses.flatMap (fun u =>
    u.names.filterMap (fun n =>
      if (allCtorOwners.lookup n).isSome || (dataTyOwners.lookup n).isSome then none else some (n, u.modName)))
  let qTy := qualifyTyName dataTyOwners usedNames
  let entryDecls := p.decls.map (fun d => match d with
    | .dataD n ps cs        => .dataD n ps (cs.map (fun (c, tys) => (c, tys.map qTy)))
    | .effectD n ops        => .effectD n (ops.map (fun (op, ty) => (op, qTy ty)))
    | .traitD n ps ops laws => .traitD n ps ops (laws.map (fun l => { l with body := qualifyDotAccess importNames ctorOwners qTy l.body }))
    | .implD n t ops        => .implD n (qTy t) (ops.map (fun o => { o with body := qualifyDotAccess importNames ctorOwners qTy o.body }))
    | .fnD n ps ty tr tv b  => .fnD n ps (qTy ty) tr tv (qualifyDotAccess importNames ctorOwners qTy b)
    | .letD n ty e          => .letD n (ty.map qTy) (qualifyDotAccess importNames ctorOwners qTy e)
    | .letRecD n t e        => .letRecD n (qTy t) (qualifyDotAccess importNames ctorOwners qTy e))
  let body := qualifyDotAccess importNames ctorOwners qTy p.body
  -- `use`-hoisted plain-fn aliases are injected as `letD` decls at the FRONT of the entry file's
  -- own decls (not wrapped only around `p.body`) — a `use`d name must be visible from WITHIN
  -- another entry-file decl too (e.g. a top-level `let main = ($double) 21`, ADR-0093 D5's own
  -- payoff case), not just the trailing body. `foldLetDecls` (elabProg) folds ALL `letD`s in decl
  -- order regardless of origin, so prepending here gives the alias the OUTERMOST scope — every
  -- other decl and the body see it, exactly matching where a `use` line sits in source (always
  -- before every decl it can affect, per the header-then-decls grammar).
  let aliasDecls : List Decl := usedPlainFns.map (fun (n, modName) => .letD n none (Surf.var (qualifyName modName n)))
  return { imports := [], uses := [], pubNames := p.pubNames, decls := mergedDecls ++ aliasDecls ++ entryDecls,
            body := body, isLibrary := p.isLibrary }

/-! Fold every `letD`/`letRecD` in `ds` into `tail`, RIGHTMOST-first (a `foldr`), producing nested
`Surf.lett`/`Surf.letRecS` wrapping `tail` — the SAME "wrap the body in a let" idiom
`wrapFnSrcs`/`wrapGenericFns`/`mergeModules`'s `use`-hoist already use (ADR-0093 D5, operator
ruling: `let`/`let rec` decls are BINDERS, never static environment entries — this is their ONLY
elaboration path; `buildEnv` no-ops on them by construction). Decl ORDER is preserved: an earlier
`let` is the OUTER binder (so a later decl, or the tail, can reference it) — `foldr` with the LIST
in its original order does exactly this (`foldr f z [a, b, c] = f a (f b (f c z))`, so `a`'s
`lett`/`letRecS` wraps EVERYTHING after it, `b`'s wraps what's after IT, etc.), matching ordinary
nested-`let` scoping. Non-let decls pass through unchanged in a SEPARATE list (returned alongside)
for `buildEnv`. -/
def foldLetDecls (ds : List Decl) (tail : Surf) : List Decl × Surf :=
  let nonLetDecls := ds.filter (fun d => match d with | .letD .. | .letRecD .. => false | _ => true)
  let body := ds.foldr (fun d acc => match d with
    | .letD n ty e   => Surf.lett n (match ty with | some t => Surf.annotS e t | none => e) acc
    | .letRecD n t e => Surf.letRecS n t e acc
    | _              => acc) tail
  (nonLetDecls, body)

/-! Does `nm` occur as a free-ish variable reference anywhere in `e` (`surfUsesVar`)? A syntactic
over-approximation (ignores shadowing — a shadowed use just over-injects, costing a little fuel,
never wrong). Used to filter the prelude's auto-`use` list (ADR-0098 §auto-use) down to the names a
program ACTUALLY mentions, before `injectPrelude` constructs the synthetic `use` clause —
`mergeModules`'s alias-injection (and hence a program's fuel cost) is driven entirely by the `use`
list it's handed, so filtering HERE keeps an unused prelude entry at ZERO fuel cost, exactly
preserving the retired `wrapGenericFns`'s conditional-injection discipline (Config.run's CK machine
decrements fuel once per `letC` step regardless of whether the binder is ever forced — an
UNCONDITIONAL 21-entry prelude merge would tax every program ~21 fuel steps it never asked for; the
tight-fuel corpus, `#guard`s at fuel 20-50, falsified that shape directly). Mirrors
`Bang.Query.surfUsesVar` arm-for-arm (that copy lives DOWNSTREAM of this file — `Query.lean`
imports `Diagnostics.lean` imports `TypeCheck.lean` — so importing it back here would cycle; this
stays the upstream original, same discipline as before ADR-0098). -/
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
  | .lettMulti binds b             => letBindingsUseVar nm binds || surfUsesVar nm b
  -- `x`/`h` are BINDERS (a clause's arg / the cap name) — like every other binder-shadowing site
  -- here (`.lam _ e`, `.matchS s _ l _ r`), the shadow is NOT modeled (the whole function is a
  -- syntactic OVER-approximation, per its own doc comment: shadowed uses just cost a little extra
  -- fuel, never wrong).
  | .handleCustomS _lbl n .none _h cls b       => surfUsesVar nm n || hClausesUseVar nm cls || surfUsesVar nm b
  | .handleCustomS _lbl n (.one p) _h cls b    => surfUsesVar nm n || surfUsesVar nm p || hClausesUseVar nm cls || surfUsesVar nm b
  | .handleCustomS _lbl n (.two p q) _h cls b  => surfUsesVar nm n || surfUsesVar nm p || surfUsesVar nm q || hClausesUseVar nm cls || surfUsesVar nm b
  -- #97 item 2: sibling names are BINDERS (like `x`/`h` above), not modeled as shadows — an
  -- over-approximation, never wrong (same discipline).
  | .letRecMultiS binds b          => letRecBindingsUseVar nm binds || surfUsesVar nm b
def dArmsUseVar (nm : String) : DArms → Bool
  | .nil            => false
  | .cons _ _ b rest => surfUsesVar nm b || dArmsUseVar nm rest
def letBindingsUseVar (nm : String) : LetBindings → Bool
  | .nil            => false
  | .cons _ e rest  => surfUsesVar nm e || letBindingsUseVar nm rest
def hClausesUseVar (nm : String) : HClauses → Bool
  | .nil               => false
  | .cons _ _ b rest   => surfUsesVar nm b || hClausesUseVar nm rest
def letRecBindingsUseVar (nm : String) : LetRecBindings → Bool
  | .nil               => false
  | .cons _ _ e rest   => surfUsesVar nm e || letRecBindingsUseVar nm rest
end

/-! #97 item 2's H3 diagnostic: "forward reference to a sibling `let rec`" teaching message. Every
existing NESTED `let rec` (the pre-#97 workaround for a mutual-looking shape — an outer `let rec`
with sibling INNER `let rec`s in its body) can only call EARLIER siblings, never a LATER one — the
inner functions are bound SEQUENTIALLY (`.lett`-style nesting), unlike the genuine simultaneous
visibility `.letRecMultiS`'s `and`-chain now gives. A forward reference surfaces at `synthSC`'s
ORDINARY "unbound variable" check (the desugared tree has already lost the `letRecS`/`letRecMultiS`
shape by the time that check runs — `elabProg` fully expands the μ-knot before `synthSC` ever sees
the tree), so this diagnostic runs POST-HOC: collect every name ANY `letRecS`/`letRecMultiS`
ANYWHERE in the ORIGINAL (pre-elaboration) tree binds, then check whether the unbound name is one of
them. -/
mutual
/-- Every name bound by a `letRecS`/`letRecMultiS` ANYWHERE in `e` (a syntactic over-approximation
— the `surfUsesVar` precedent: costs nothing to collect a name from an unreachable branch, never
wrong to include one). Walks the WHOLE tree (not scope-aware) because the diagnostic only needs "is
X a sibling `let rec` name SOMEWHERE in this program", not a scope-exact answer — a false-positive
match (a name that HAPPENS to be a `let rec` binder elsewhere, unrelated to the actual unbound
reference) still produces a technically-imprecise but HARMLESS hint (worst case: slightly
over-eager teaching text on a genuinely-different bug), never a wrong ANSWER (the underlying
"unbound variable" error still fires either way — this only decides the MESSAGE). -/
def letRecBoundNames : Surf → List String
  | .letRecS n _ f b               => n :: (letRecBoundNames f ++ letRecBoundNames b)
  | .letRecMultiS binds b          => letRecBindingsNamesTC binds ++ letRecBoundNames b
  | .lit _ | .var _ | .getS | .unitS => []
  | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
  | .lam _ e | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ => letRecBoundNames e
  | .lett _ a b | .app a b | .stateS a b | .writeS a b | .pairS a b | .splitS _ _ a b
  | .binopS _ a b                  => letRecBoundNames a ++ letRecBoundNames b
  | .matchS s _ l _ r              => letRecBoundNames s ++ letRecBoundNames l ++ letRecBoundNames r
  | .ifS c t e                     => letRecBoundNames c ++ letRecBoundNames t ++ letRecBoundNames e
  | .matchD s arms                 => letRecBoundNames s ++ letRecBoundNamesDArms arms
  | .withCapS _ i _ b              => letRecBoundNames i ++ letRecBoundNames b
  | .dotPerform r _ .none          => letRecBoundNames r
  | .dotPerform r _ (.one a)       => letRecBoundNames r ++ letRecBoundNames a
  | .dotPerform r _ (.two a b)     => letRecBoundNames r ++ letRecBoundNames a ++ letRecBoundNames b
  | .lettMulti binds b             => letRecBoundNamesBindings binds ++ letRecBoundNames b
  | .handleCustomS _lbl n .none _h cls b       => letRecBoundNames n ++ letRecBoundNamesHClauses cls ++ letRecBoundNames b
  | .handleCustomS _lbl n (.one p) _h cls b    => letRecBoundNames n ++ letRecBoundNames p ++ letRecBoundNamesHClauses cls ++ letRecBoundNames b
  | .handleCustomS _lbl n (.two p q) _h cls b  => letRecBoundNames n ++ letRecBoundNames p ++ letRecBoundNames q ++ letRecBoundNamesHClauses cls ++ letRecBoundNames b
def letRecBoundNamesDArms : DArms → List String
  | .nil              => []
  | .cons _ _ b rest  => letRecBoundNames b ++ letRecBoundNamesDArms rest
def letRecBoundNamesBindings : LetBindings → List String
  | .nil            => []
  | .cons _ e rest  => letRecBoundNames e ++ letRecBoundNamesBindings rest
def letRecBoundNamesHClauses : HClauses → List String
  | .nil               => []
  | .cons _ _ b rest   => letRecBoundNames b ++ letRecBoundNamesHClauses rest
def letRecBindingsNamesTC : LetRecBindings → List String
  | .nil               => []
  | .cons n _ e rest   => n :: (letRecBoundNames e ++ letRecBindingsNamesTC rest)
end

/-- H3's message rewrite: if `msg` is the ordinary "unbound variable X" shape AND `X` is bound by
SOME `letRecS`/`letRecMultiS` anywhere in `prog`'s trailing body (`letRecBoundNames`), replace it
with the B0NN teaching diagnostic (DiagCodes.lean registers the anchor); otherwise `msg` passes
through UNCHANGED (every other diagnostic family is untouched — this is a pure ADDITIVE retrofit,
the same "codes are retrofitted onto existing strings" discipline `DiagCodes.lean`'s own header
documents). `X`'s bare identifier is recovered the SAME way `locateInMsg` already does (the
"unbound variable " prefix-strip), so the two stay in lockstep by construction. -/
def rewriteForwardRefMsg (prog : Prog) (msg : String) : String :=
  if "unbound variable ".isPrefixOf msg then
    let x := (msg.drop "unbound variable ".length).toString
    if (letRecBoundNames prog.body).contains x then
      s!"'{x}' is a sibling `let rec` defined later — siblings cannot forward-reference through nested `let rec` (v1 has no mutual visibility that way; use `let rec f : T1 = e1 and g : T2 = e2 in body` instead, #97 item 2). Reorder so every sibling calls only EARLIER siblings + the outer knot (leaf-level rules first), or restructure into ONE self-recursive function, or use the mutual `and`-chain form."
    else msg
  else msg

/-- Every `Surf` body attached to a `Decl` (mirrors `Bang.Query.declBodies`, upstream copy for the
same cycle reason as `surfUsesVar` above): a `fnD`/`letD`/`letRecD`'s own body/rhs; `dataD`/
`effectD` carry no `Surf`; `traitD`/`implD` are excluded too (a prelude entry is never referenced
from a law/method body in v1's corpus, and `Prelude.bang` itself declares neither). -/
def declBodiesTC : Decl → List Surf
  | .fnD _ _ _ _ _ b => [b]
  | .letD _ _ e      => [e]
  | .letRecD _ _ e   => [e]
  | .dataD ..  | .effectD .. | .traitD .. | .implD .. => []

/-- Does `nm` occur anywhere in `p` — its trailing body OR any decl's own body (a name mentioned
only inside another top-level `let`'s definition, not the trailing expression, must still trigger
the prelude alias — e.g. `let main = ($double) 21` with no other body, ADR-0093 D5's own precedent
for "a decl's body is a real use site too"). -/
def progUsesVar (nm : String) (p : Prog) : Bool :=
  surfUsesVar nm p.body || p.decls.any (fun d => (declBodiesTC d).any (surfUsesVar nm))

/-- The prelude module's SOURCE, embedded into the binary at COMPILE time (ADR-0098 §embed):
`Prelude.bang` is ordinary bang source living at the repo root, checked/fmt'd/tested like any
module — `include_str` bakes its bytes into the `.olean`/executable so `bang` stays a single
self-contained binary with no runtime search path (a path-based alternative would need the file
findable at RUN time relative to an install location no v1 packaging story fixes; embedding makes
the SOURCE FILE the only single source of truth — there is no second copy to drift, since the
compiled bytes ARE `Prelude.bang`'s bytes, re-derived on every build). Path is relative to THIS
file's own directory (`Bang/Frontend/`), two levels up to the repo root — Lean's `include_str`
resolves relative to the including `.lean` file, independent of build CWD. -/
def preludeSrc : String := include_str "../../Prelude.bang"

/-- The prelude, PARSED once (`Prog`, unqualified — `mergeModules` qualifies it per-elaboration
exactly like any other resolved import). A parse failure here is a BUILD-time bug (the embedded
source is fixed at compile time, gated by `test-modules.sh`'s own `bang check Prelude.bang` leg
and this file's own `#guard`s below) — `.get!` is sound because `Prelude.bang` is committed,
checked source, not user input; a broken prelude fails LOUD at `lake build`, never at runtime. -/
def preludeProg : Prog := (Bang.Surface.parseProg preludeSrc).toOption.get!

/-- Every `pub` name the prelude exports — the auto-`use` list (ADR-0098 §auto-use): a program
implicitly gets `use Prelude (name₁, name₂, …)` naming every one of these, with NO explicit
`use`/`import` line needed. Precomputed once (not per-elaboration) since `preludeProg` is fixed. -/
def preludePubNames : List String := preludeProg.pubNames

/-- DESCRIPTIVE signatures for the reference doc (`docs/reference/language.md`'s Standard-library/
Generic-prelude tables, `tools/gen-reference.py`'s `extract_prelude_section`) — hand-maintained
PROSE, not verified syntax: bang's surface has no `forall`/generic function-type ascription (an
attempt at `pub let mapOption : (a -> b) -> Option a -> Option b = …` rejects with "unknown type
name 'a'" — generics elaborate to MONO, ADR-0075/0079, so a top-level ascription can only ever name
a CONCRETE type), so a generic entry's real signature cannot live IN `Prelude.bang` as checked
syntax the way `concat : Str -> Str -> Str` does. This table is this fact's one acknowledged
escape hatch — `Prelude.bang` stays comment-free (matching the `examples/*.bang` convention:
`bang fmt` strips `--` comments, so a commented module permanently fails `bang lint`'s
`fmt-divergence` check; verified live — reintroducing per-entry doc comments here made `bang lint
Prelude.bang` flag every one). Consistency with the RUNNING code is enforced by the corpus
`#guard`s (⑨h′/⑨j/⑨k below), which exercise every entry against these exact signatures — a
signature drifting from reality breaks a `#guard`, not silently. -/
def preludeSigs : List (String × String) :=
  [ ("concat", "Str -> Str -> Str"),
    ("eq", "Str -> Str -> Unit + Unit"),
    ("mapOption", "(a -> b) -> Option a -> Option b"),
    ("mapResult", "(a -> b) -> Result e a -> Result e b"),
    ("bimap", "(e -> f) -> (a -> b) -> (e + a) -> (f + b)"),
    ("resultToEither", "Result e a -> (e + a)"),
    ("eitherToResult", "(e + a) -> Result e a"),
    ("optionToEither", "Option a -> (Unit + a)"),
    ("eitherToOption", "(Unit + a) -> Option a"),
    ("withDefault", "a -> Option a -> a"),
    ("fst", "(a, b) -> a"),
    ("snd", "(a, b) -> b"),
    ("abs", "Int -> Int"),
    ("min", "Int -> Int -> Int"),
    ("max", "Int -> Int -> Int"),
    ("const", "a -> b -> a"),
    ("isDigit", "Char -> Unit + Unit"),
    ("isAlpha", "Char -> Unit + Unit"),
    ("toUpper", "Char -> Char"),
    ("toLower", "Char -> Char"),
    ("take", "Int -> List a -> List a"),
    ("drop", "Int -> List a -> List a") ]

/-- Auto-`use` the prelude into `p` (ADR-0098): merge a TRIMMED `preludeProg` — containing only the
decls the program actually MENTIONS (`progUsesVar`) — in as a resolved module named `"Prelude"`,
with those same names pre-added to `p`'s own `uses`. The user never writes `use Prelude (…)`
themselves.

Trimming `preludeProg.decls` (not just the `use` alias list) is load-bearing: `mergeModules` folds
EVERY decl of a resolved module into `mergedDecls` unconditionally (`use`-selectivity only controls
the unqualified ALIAS, not whether the qualified `Prelude_name` decl itself is merged), and
`foldLetDecls` later wraps the body in one `let` PER decl in the final list — so an untrimmed merge
would still pay `Config.run`'s one-fuel-per-`letC` cost for all 21 entries regardless of a filtered
`use`. Trimming the SOURCE module is sound here specifically because NO prelude entry calls another
top-level prelude entry (verified: `concat`/`eq` self-recurse, `reverse` nests its own PRIVATE
`revApp`, but none references a SIBLING top-level name) — so there is no cross-entry closure to
compute; each mentioned name's own decl is everything it needs. This is the general fix
`mergeModules` itself doesn't need YET (an ordinary user `import`/`use` already opts into its
target's full decl cost deliberately) but the always-on prelude specifically requires (every
program pays it, not just ones that opt in) — a genuinely NEW cost `injectStdlib`'s old bucket-gate
never had, closed here rather than deferred.

Composes with the module resolver's OWN `mergeModules` call transparently: for a multi-file
program, `p` here is already the once-merged `Prog` (`imports`/`uses` cleared to `[]` by that
earlier merge, ADR-0093 D4) — merging AGAIN with the (trimmed) prelude as the sole resolved module
is just `mergeModules`'s ordinary multi-import shape, run a second time. For the single-file fast
path, this is the ONLY merge that ever runs. An EMPTY mention set short-circuits before any merge
(zero fuel, zero decls — matches a program with no `use` header at all).

Shadowing/suppression falls out of `mergeModules`'s EXISTING decl-ordering for free (ADR-0098
§auto-use, no special-case code): the auto-`use` aliases are prepended before the entry file's own
decls (`mergeModules`'s `aliasDecls ++ entryDecls`), so a user's own top-level `let`/`data` of the
SAME name is the INNERMOST (later) binder and lexically SHADOWS the prelude one — verified live
(`#guard` below: a user `abs` overrides the prelude `abs`). This is STRICTLY finer-grained than the
retired `injectStdlib`'s all-or-nothing `declared.contains "Str"/"Option"` bucket gate: each of the
21 prelude names shadows INDEPENDENTLY, not as two coarse bundles. A name COLLISION between the
prelude and a module the user separately `use`s is the SAME loud multi-import error `mergeModules`
already gives two colliding `use`s (ADR-0046) — no new error path. -/
def injectPrelude (p : Prog) : Except String Prog :=
  let mentioned := preludePubNames.filter (progUsesVar · p)
  if mentioned.isEmpty then pure p
  else
    let trimmedPrelude := { preludeProg with
      pubNames := mentioned, decls := preludeProg.decls.filter (fun d => mentioned.contains d.name) }
    mergeModules [("Prelude", trimmedPrelude)] { p with uses := p.uses ++ [⟨"Prelude", mentioned⟩] }

/-! ## `deriving (Eq, Ord)` — the structural derive handler (ADR-0097, issue #109)

A `data Foo = C₀(…) | C₁(…) | … deriving (Eq, Ord)` clause (parsed into `Prog.derivesFor`,
Surface.lean) expands to an ordinary `Decl.traitD` + `Decl.implD` pair, indistinguishable at the
kernel boundary from a hand-written one (ADR-0097's "Layer F" framing — the SAME elaborate-away
move `ADR-0069`/`0075`/`0088`/`0091`/`0093` already use). §2's codegen: same-tag structural fold for
`Eq` (AND over payload-slot `==`, different-tag ⇒ `false`); decl-order tag comparison + lexicographic
payload for `Ord`. §3a: recursive carriers (`Cons(Int, IntList)`) are IN SCOPE — the generated
`impl`'s 2-param op rides the SAME `#112` knot-based `let rec` dispatch (`buildEnv`'s `.implD` arm,
`wrapPendingKnots`) any hand-written 2-param impl op does, so a self-referential `tx == ty` (on the
carrier's own recursive field) resolves through real recursion, not a splice.

**Trait sourcing (ADR-0097 §2's decision (a), scoped per §6/Revisit-if's stopgap):** rather than
importing a `Prelude.bang`-declared `trait Eq`/`trait Ord` (deferred — see the two gaps this
session found, not yet closed: `mergeModules`'s `qualifyDeclName` unconditionally qualifies a
`.traitD`'s OWN name to `ModName_Name` with no `usedPlainFns`-style un-qualification alias for
trait names, unlike a plain fn; and `bang test`'s law discovery, `lawInstancesOf`/
`lawInstanceOpCallDiagnostics`, parses RAW source directly with no prelude/module-merge step at
all, so a prelude-only trait declaration would be invisible to `bang test` on a decls-only derived
program), the handler emits a MINIMAL inline `trait Eq`/`trait Ord` declaration itself — ONLY when
the program doesn't already declare a trait of that name (a user's own hand-written `trait Eq`
wins; the handler then targets IT instead, matching whatever op/law shape the user chose, mirroring
how `#108`'s ctor namespacing needs no derive-handler awareness because the fold is always
self-type-scoped). This keeps every derive-handler-touched program SELF-CONTAINED (no module merge,
no qualification, no `bang test` blind spot) — the exact shape ADR-0097's own witnesses ran, and
what `examples/trait-recursive-{eq,ord}` already encode by hand. Superseded once `Prelude.bang`
ships a canonical `trait Eq`/`trait Ord` AND both gaps above are closed (ADR-0097's own "Revisit
if"). -/

/-- The canonical `Eq`/`Ord` trait declarations this handler targets — SAME shape ADR-0097 §2's
worked examples and `examples/trait-recursive-{eq,ord}` hand-write, so a generated impl is
behaviorally IDENTICAL to those (the differential oracle this handler is built to match). One law
each (`refl`/`irrefl` — deliberately minimal, not the full `symm`/`trans`/total-order set ADR-0097
§2 sketches for the eventual `Prelude.bang` version): a stopgap ships the SMALLEST law that still
demonstrates `bang test`'s free law-discovery (ADR-0097 §5), not the full canonical law suite,
which belongs on the (not-yet-shipped) prelude declaration this stands in for. -/
def eqTraitDecl : Decl :=
  .traitD "Eq" [] [⟨"eq", ["a", "b"], .tSum .tUnit .tUnit, .tArr .tSelf (.tArr .tSelf (.tSum .tUnit .tUnit))⟩]
    [⟨"refl", ["a"], .binopS .eq (.var "a") (.var "a")⟩]

def ordTraitDecl : Decl :=
  .traitD "Ord" [] [⟨"lt", ["a", "b"], .tSum .tUnit .tUnit, .tArr .tSelf (.tArr .tSelf (.tSum .tUnit .tUnit))⟩]
    [⟨"irrefl", [], .binopS .eq (.lit 0) (.lit 0)⟩]

/-- `true`/`false` as the SAME `Unit + Unit` encoding every hand-written law/impl in the corpus
uses (`0 == 0` / `0 == 1`, ADR-0097 §2's worked examples) — the derive handler's fold emits these
verbatim at a base case, never a `Bool`-typed literal (v1 has none). -/
def deriveTrueS : Surf := .binopS .eq (.lit 0) (.lit 0)
def deriveFalseS : Surf := .binopS .eq (.lit 0) (.lit 1)

/-- Does `t` mention a FUNCTION type anywhere in its structure? (`.tArr` at ANY depth, including
nested inside a product/sum/thunk payload slot.) ADR-0097 §4: a ctor payload slot of function type
is refused outright (`Eq`/`Ord` are undecidable on functions) — VACUOUS in v1 today (`resolveTy`'s
`CtorInfo` shape admits no function-typed payload, ADR-0069), but the handler asserts the policy
now per the ADR's own "state it now so a future payload-kind extension does not silently
mis-derive" rationale. -/
def tyHasArrow : Ty → Bool
  | .tArr .. => true
  | .tSum a b | .tProd a b => tyHasArrow a || tyHasArrow b
  | .tThunk a | .tEff _ a | .tEffR _ a => tyHasArrow a
  | .tMu a => tyHasArrow a
  | _ => false

/-- Fresh field-binder names for a ctor's arity-≤2 payload (ADR-0069: ≤ 2 fields in v1, nest
tuples beyond that) — `x0`/`x1` for the LEFT scrutinee's binders, `y0`/`y1` for the RIGHT, so a
same-ctor arm's two bound-variable sets never collide (`matchD`'s outer arm binds `x*`, the nested
inner arm binds `y*`, both visible together in the innermost body). -/
def deriveFieldNames (pfx : String) (arity : Nat) : List String :=
  (List.range arity).map (fun i => s!"{pfx}{i}")

/-- The `Eq` fold body for one (outer ctor, inner ctor) pair (ADR-0097 §2): same ctor ⇒ AND-fold
`x_i == y_i` over every payload slot (nested `let`+`if`, the exact `headEq`/`tailEq` shape
`examples/trait-recursive-eq` hand-writes — recursing via bare `==`, which dispatches through
`env.insts`/the `#112` knot for a `Self`-typed field exactly like a hand-written impl, or the
kernel δ-rule for `Int`); different ctor ⇒ `false`, unconditionally (payload never inspected). -/
def eqArmBody (outerArity innerArity : Nat) : Surf :=
  if outerArity != innerArity then deriveFalseS   -- unreachable in practice (matching ctor identity
                                                    -- implies matching arity, ADR-0069) — defensive.
  else
    let xs := deriveFieldNames "x" outerArity
    let ys := deriveFieldNames "y" innerArity
    match xs, ys with
    | [], []             => deriveTrueS                                    -- nullary ctor: trivially equal
    | [x0], [y0]          => .binopS .eq (.var x0) (.var y0)                -- 1 field: bare `==`
    | [x0, x1], [y0, y1] =>                                                 -- 2 fields: AND-fold
        .lett "#headEq" (.binopS .eq (.var x0) (.var y0))
          (.lett "#tailEq" (.binopS .eq (.var x1) (.var y1))
            (.ifS (.var "#headEq") (.var "#tailEq") deriveFalseS))
    | _, _ => deriveFalseS   -- unreachable: arity ≤ 2 in v1 (ADR-0069), defensive fallback.

/-- The full `Eq.eq` fold over ALL (outer, inner) ctor pairs of `cs` — a `matchD`-of-`matchD`
diagonal, ADR-0097 §2's exact shape. Each outer arm's binders are `x0..`; each nested inner arm
(one per ctor of `cs` again) is `y0..` when it's the SAME ctor as the outer arm (payload-wise
fold), else `deriveFalseS` (payload unused, so its binders are irrelevant — bound but unread). -/
def eqFoldBody (cs : List (String × List Ty)) (pVar qVar : String) : Surf :=
  let outerArms := cs.map (fun (outerCtor, outerTys) =>
    let xs := deriveFieldNames "x" outerTys.length
    let innerArms := cs.map (fun (innerCtor, innerTys) =>
      let ys := deriveFieldNames "y" innerTys.length
      let body := if innerCtor == outerCtor then eqArmBody outerTys.length innerTys.length else deriveFalseS
      (innerCtor, ys, body))
    (outerCtor, xs, .matchD (.var qVar) (toDArms innerArms)))
  .matchD (.var pVar) (toDArms outerArms)

/-- The `Ord` fold body for one (outer ctor, inner ctor) pair (ADR-0097 §2): same ctor ⇒
lexicographic ladder over payload slots (`if hx < hy then true else if hy < hx then false else
recurse-next-slot`, `examples/trait-recursive-ord`'s exact shape); DIFFERENT ctor ⇒ the OUTER
ctor's decl-order INDEX compared against the INNER's (`outerIdx < innerIdx`, ADR-0097 §2's
"ctor-index order = decl order, the tag IS the ordinal" — ADR-0069's sum-by-decl-order encoding). -/
def ordArmBody (outerIdx innerIdx outerArity innerArity : Nat) : Surf :=
  if outerIdx != innerIdx then
    if outerIdx < innerIdx then deriveTrueS else deriveFalseS
  else if outerArity != innerArity then deriveFalseS   -- defensive: same idx ⇒ same ctor ⇒ same arity
  else
    let xs := deriveFieldNames "x" outerArity
    let ys := deriveFieldNames "y" innerArity
    match xs, ys with
    | [], []             => deriveFalseS                                    -- nullary vs nullary: never strictly less
    | [x0], [y0]          => .binopS .lt (.var x0) (.var y0)                 -- 1 field: bare `<`
    | [x0, x1], [y0, y1] =>                                                  -- 2 fields: lexicographic ladder
        .ifS (.binopS .lt (.var x0) (.var y0)) deriveTrueS
          (.ifS (.binopS .lt (.var y0) (.var x0)) deriveFalseS
            (.binopS .lt (.var x1) (.var y1)))
    | _, _ => deriveFalseS   -- unreachable: arity ≤ 2 in v1 (ADR-0069), defensive fallback.

/-- The full `Ord.lt` fold over ALL (outer, inner) ctor pairs of `cs` — mirrors `eqFoldBody`'s
`matchD`-of-`matchD` shape exactly, threading each ctor's DECL-ORDER INDEX (its position in `cs`,
ADR-0069's ordinal) into `ordArmBody` instead of a same/different-ctor Bool. -/
def ordFoldBody (cs : List (String × List Ty)) (pVar qVar : String) : Surf :=
  let indexed := cs.zipIdx
  let outerArms := indexed.map (fun ((outerCtor, outerTys), outerIdx) =>
    let xs := deriveFieldNames "x" outerTys.length
    let innerArms := indexed.map (fun ((innerCtor, innerTys), innerIdx) =>
      let ys := deriveFieldNames "y" innerTys.length
      (innerCtor, ys, ordArmBody outerIdx innerIdx outerTys.length innerTys.length))
    (outerCtor, xs, .matchD (.var qVar) (toDArms innerArms)))
  .matchD (.var pVar) (toDArms outerArms)

/-- Expand ONE `(dataName, deriveList)` entry (`Prog.derivesFor`) into the `Decl`s it contributes:
a stopgap `trait Eq`/`trait Ord` declaration IFF the program doesn't already declare a trait of
that name (the "target the user's own trait if present" rule, this section's header comment), plus
the generated `impl <Trait> for <dataName> { fn <op>(p, q) = <fold> }`. Refuses (LOUD error, ADR-0046)
a function-typed payload slot anywhere in `cs` (ADR-0097 §4 — vacuous in v1 today, asserted anyway)
and an unrecognized derive name (only `Eq`/`Ord` are tier-1, ADR-0097's own scope). -/
def expandOneDerive (existingTraitNames : List String) (dataName : String)
    (cs : List (String × List Ty)) (deriveName : String) : Except String (List Decl) := do
  if cs.any (fun (_, tys) => tys.any tyHasArrow) then
    throw s!"cannot derive '{deriveName}' for '{dataName}': a constructor payload is function-typed \
(Eq/Ord are undecidable on functions, ADR-0097 §4)"
  match deriveName with
  | "Eq" =>
      let traitDecl := if existingTraitNames.contains "Eq" then [] else [eqTraitDecl]
      let implDecl := Decl.implD "Eq" (Ty.tName dataName)
        [⟨"eq", ["p", "q"], eqFoldBody cs "p" "q"⟩]
      pure (traitDecl ++ [implDecl])
  | "Ord" =>
      let traitDecl := if existingTraitNames.contains "Ord" then [] else [ordTraitDecl]
      let implDecl := Decl.implD "Ord" (Ty.tName dataName)
        [⟨"lt", ["p", "q"], ordFoldBody cs "p" "q"⟩]
      pure (traitDecl ++ [implDecl])
  | other => throw s!"unknown derive '{other}' for '{dataName}' — v1 supports only 'Eq'/'Ord' (ADR-0097 tier 1)"

/-- **The derive handler's PUBLIC entry (#109, ADR-0097).** Expand every `Prog.derivesFor` entry
into its `trait`/`impl` decls, APPENDING them AFTER `p.decls` — every derived `impl`'s target
`data` decl (and, when the program hand-declares its own `trait Eq`/`trait Ord`, that trait too)
textually PRECEDES it, matching `buildEnv`'s own "IN ORDER" contract (`buildEnv`'s doc comment,
TypeCheck.lean: "a data type may reference itself + earlier decls; forward references fail loud")
and mirroring hand-written impl placement in the ADR's own worked examples and
`examples/trait-recursive-*`.

A stopgap trait declaration (`eqTraitDecl`/`ordTraitDecl`) is added AT MOST ONCE per program even
if multiple `data` decls derive the SAME trait (`Eq` on both `Box` and `IntList` in one program) —
tracked via a running `traits already emitted or user-declared` set threaded through the fold,
avoiding a `buildEnv` "duplicate trait" surprise (today unenforced, ADR-0097 doesn't want to be the
first thing that trips it). Runs BEFORE `injectPrelude`/`eraseLettMultiProg` in `elabProg`'s
pipeline, and is called directly by `lawInstancesOf`/`lawInstanceOpCallDiagnostics`/
`unreachableIntImplDiagnostics` (via `parseProgWithDerives`, below) so `bang test`'s raw-source law
discovery sees the SAME expanded decls `elabProg` does — closing the gap a `Prelude.bang`-sourced
trait would have left open (this section's header comment). -/
public def expandDerives (p : Prog) : Except String Prog := do
  if p.derivesFor.isEmpty then pure p
  else
    let existingTraitNames := p.decls.filterMap (fun d => match d with | .traitD n .. => some n | _ => none)
    let mut newDecls : List Decl := []
    let mut seenStopgapTraits : List String := existingTraitNames
    for (dataName, derives) in p.derivesFor do
      match p.decls.find? (fun d => match d with | .dataD n _ _ => n == dataName | _ => false) with
      | none => throw s!"'deriving' names '{dataName}', which is not a 'data' decl in this program"
      -- #122: a GENERIC carrier (`ps` non-empty, e.g. `data Box a = …`) has no monomorphic
      -- `Ty.tName dataName` for the generated `impl <Trait> for {dataName}` to target — `resolveName`
      -- would hit its own `generic type needs type argument(s)` error at an impl site that names no
      -- concrete instantiation. Refuse LOUD (ADR-0046) at the decl site instead of letting that
      -- confusing downstream error surface — generic-carrier deriving is a real future slice
      -- (monomorphize the fold PER INSTANTIATION, ADR-0097 §6 "Revisit if"), not implemented here.
      | some (.dataD _ (_ :: _) _) =>
          throw s!"cannot derive for '{dataName}': it is a GENERIC data type (has type parameters) — \
v1's derive handler only targets MONOMORPHIC carriers (ADR-0097 §6). Either drop the type parameter \
(a monomorphic alias like 'data {dataName}I = …(Int)…') or hand-write the 'impl' for the specific \
instantiation you need."
      | some (.dataD _ [] cs) =>
          for deriveName in derives do
            let ds ← expandOneDerive seenStopgapTraits dataName cs deriveName
            for d in ds do
              match d with
              | .traitD n .. => seenStopgapTraits := n :: seenStopgapTraits
              | _ => pure ()
            newDecls := newDecls ++ ds
      | some _ => throw s!"'deriving' names '{dataName}', which is not a 'data' decl in this program"
    pure { p with decls := p.decls ++ newDecls }

/-- `parseProg` FOLLOWED by `expandDerives` (#109) — the ONE place law discovery
(`lawInstancesOf`/`lawInstanceOpCallDiagnostics`/`unreachableIntImplDiagnostics`) and `elabProg`'s
own `Bang.Surface.parseProg src >>= elabProg` callers should reach for instead of a bare
`parseProg`, so a `deriving`-only decls file (no hand-written `trait`/`impl` at all) still
discovers its derived impl's laws under `bang test` — `bang test`'s `runTest` (Main.lean) parses
RAW source with zero module/prelude resolution, so if the derive expansion happened only inside
`elabProg`'s deeper pipeline, `bang test` would see zero decls and report "no trait laws found"
even though a `deriving`-generated impl (with a freely-attached law, ADR-0097 §5) exists. -/
def parseProgWithDerives (src : String) : Except String Prog :=
  Bang.Surface.parseProg src >>= expandDerives

/-- **#112 fix.** Wrap `body` in one `let rec` per PENDING 2-param impl-op knot (`env.pendingKnots`,
DECL ORDER — each subsequent `let rec` nests OUTSIDE the previous, so it sees every earlier knot's
name in scope, mirroring `buildEnv`'s pre-#112 "earlier ops resolve" guarantee while ALSO giving
self-reference for free — the μ-encoded fixpoint (`buildLetRec`, ADR-0073/#95) is REAL recursion,
not a splice, so `tx == ty` inside `eq`'s own body resolves through the SAME mechanism an ordinary
`let rec` uses). TUPLED single-arg encoding (`fun pq => let (p1, p2) = pq in rawBody`), NOT curried
(`fun p1 => fun p2 => …`) — de-risked this session: `letRecS`'s elaboration arm
(`TypeCheck.lean`'s `.letRecS` case) only threads the DECLARED type onto the OUTERMOST `.lam`
binder; a curried second parameter falls through the GENERIC `.lam` arm instead, which mints it a
FRESH HOLE rather than the arrow's second domain — a separate, pre-existing gap this fix does NOT
touch (consuming `letRecS` as-is per this slice's scope). A FORWARD reference (an EARLIER knot
calling a LATER one) still fails here — `let rec` alone only ever sees itself + prior bindings;
TRUE mutual/forward impl dispatch needs `buildLetRecMulti`'s N-way tuple-of-thunks generalization
of `buildLetRec` (a separate, in-flight lane's scope — not built or touched here). -/
def wrapPendingKnots (knots : List PendingOpKnot) (body : Surf) : Surf :=
  knots.foldr (fun k acc =>
      let domTy : Ty := .tProd k.targetTy k.targetTy
      let knotTy : Ty := .tArr domTy k.retTy
      let knotFun : Surf := .lam "#pq" (.splitS k.p1 k.p2 (.var "#pq") k.rawBody)
      Surf.letRecS k.knotName knotTy knotFun acc)
    body

/-- Elaborate a whole program: auto-`use` the prelude module (ADR-0098), build the elaboration env,
resolve the body. Returns the elaborated body ALONGSIDE `env.effects` (ADR-0092 D2) — the
type-checker's `.dotPerform` arm needs the program's user-effect table to resolve a `perform`
against a declared `effect`'s op, and `synthSC`/`checkSC` have no separate `ElabEnv` parameter (see
`USt.effects`'s comment) — so `elabProg`'s caller threads the pair into `runInferC`.

`injectPrelude` FIRST: it runs its own `mergeModules` pass (needs `Prog`'s still-separate
`imports`/`uses`/`decls`/`body` fields), so it must precede `eraseLettMultiProg`/`foldLetDecls`
(which fold decls into ONE `Surf` tree `mergeModules` cannot re-enter). `eraseLettMultiProg` NEXT
(issue #68): resolves every `.lettMulti` sugar marker — in any decl's body or the program's own
trailing body, INCLUDING the prelude's own decls now merged in — to plain `.lett` chains before ANY
of `foldLetDecls`/`expandBFns`/`elabS`/qualification ever run. This is why none of those functions
(nor `synthSC`/`structOKRest`) have their own `.lettMulti` arm: by the time they see a real program,
there is none left in the tree (matching `letRecS`/`matchD`'s own "pre-resolved, reaching here is a
bug" convention) — only `Bang.Format` (the printer) and the module-qualification passes that run
BEFORE this (`qualifyVars`/`qualifyDotAccess`/`Bang.Query.surfUsesVar`, on raw per-file `Surf`
before `mergeModules` hands a merged `Prog` here) need to see through the marker transparently.

`strPrelude`/`genericPrelude` (the `data` types `Char`/`Str`/`Option`/`Result`) stay INJECTED
DIRECTLY here, not via the module mechanism — they are foundational to how literals PARSE
(`"hi"`/`'a'` desugar straight to `SCons`/`Char` ctor names) and to annotation-free generic
introduction (ADR-0081), so they precede `Prelude.bang`'s own elaboration (its `pub let`s reference
`Str`/`Char`/`Option`/`Result` ctors, which must already be in `buildEnv`'s `ElabEnv` for THEM to
type-check) — out of ADR-0098's scope (only the FUNCTION strings moved to a module).

`expandDerives` (#109, ADR-0097) runs FIRST of all, before `injectPrelude` — it only touches
`p.decls`/`p.derivesFor` (both already populated by the parser, `Prog`'s still-unmerged shape) and
must land its generated `trait`/`impl` decls before `injectPrelude`'s mention-filter walk and
`eraseLettMultiProg`'s per-decl `.lettMulti` erasure both see them (a generated impl's body carries
no `.lettMulti` marker today, but running derive-expansion first keeps the ordering uniform with
every other decl-shaped pass in this pipeline).

Also returns `env.ctors`/`env.gen` (issue #100) — the μ-re-fold display sites (`displayProg`,
`typeStringOfProg{,P}`) need the SAME decl env `elabS`'s own error messages already fold through
(`foldDataTyOrRaw`), and re-parsing/re-`buildEnv`-ing a second time just to recover it would risk
drift from whatever THIS elaboration actually resolved (e.g. prelude-injection order). Additive
tuple fields — every existing `(e, effects)`/`(e, _)` destructure widens to match. -/
def elabProg (p : Prog) :
    Except String (Surf × List (String × EffectInfo) × List (String × CtorInfo) × List (String × GenData)) := do
  let p ← expandDerives p
  let p ← injectPrelude p
  let p := Bang.Surface.eraseLettMultiProg p
  let (nonLetDecls, foldedBody) := foldLetDecls p.decls p.body
  let declared := nonLetDecls.filterMap (fun | .dataD n _ _ => some n | _ => none)
  let prelude := (strPrelude ++ genericPrelude).filter (fun | .dataD n _ _ => !declared.contains n | _ => true)
  let env ← buildEnv (prelude ++ nonLetDecls)
  -- #112: knot-wrap BEFORE `elabS` (RAW `letRecS` nodes feeding its OWN `.letRecS` arm, which does
  -- the real elaboration+fixpoint-build) — NOT wrap an already-elaborated body, which would need a
  -- second `elabS` pass over the wrapper alone.
  let wrapped := wrapPendingKnots env.pendingKnots (← expandBFns env none bigFuel foldedBody)
  -- ADR-0103: monomorphize every bound-free `let rec` (`take : Int -> List a -> List a`) BEFORE
  -- `elabS` — the `expandBFns` twin, running on the SAME `wrapped` tree. Independent of bounded-fn
  -- expansion (a disjoint surface: `let rec … : T = …` vs `fn … where Trait`, ADR-0103's "one
  -- construct per problem" ruling keeps them as separate constructs, so pass ORDER between the two
  -- is immaterial — neither can produce input the other needs to see). By the time `elabS` runs,
  -- every surviving `.letRecS` ascription is concrete; the `resolveTy` chokepoint (`elabS`'s OWN
  -- `.letRecS` arm) is UNCHANGED. `inlineVarAliases` runs FIRST: the module system's auto-`use`
  -- injection (ADR-0098) makes an unqualified prelude call (`$take …`) an ALIAS reference (`let
  -- take = Prelude_take in …`), not a DIRECT call on the qualified `let rec`'s own name — discovery
  -- (`monoCallSpine`) only recognizes the latter, so the alias must be collapsed away first
  -- (confirmed live: `$take` through the injected alias was invisible to discovery without this).
  let dealiased := inlineVarAliases wrapped
  let monomorphized ← monomorphizeLetRec env.gen env.aliases bigFuel dealiased
  let e ← elabS env [] monomorphized   -- bounded-fn uses/mono residues → elaborate (bite-2 + ADR-0103)
  return (e, env.effects, env.ctors, env.gen)

/-- PUBLIC runnable entry (the `bang` CLI's typed pipeline): parse a program's `trait`/`impl`/`data`
prelude + body, elaborate it (resolve data constructors, named matches, and type-directed operators
like `Vec + Vec`), and lower to a kernel `Comp` ready for `Source.eval`/the machine. A decl-free
program parses to `⟨[], body⟩` and elaborates to itself, so this is a strict SUPERSET of the old
`Surface.lower ∘ parse` runner path — the whole MVP surface becomes runnable from the CLI. -/
public def elaborateToComp (src : String) : Except String Comp := do
  let prog ← Bang.Surface.parseProg src
  let (e, _, _, _) ← elabProg prog
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
  let (e, effects, _, _) ← (elabProg prog).mapError (fun m => (m, Bang.Surface.locateInMsg src m))
  -- #97 item 2 H3: an "unbound variable" from THIS step may be a forward reference to a sibling
  -- `let rec` — rewrite to the teaching diagnostic BEFORE locating (the rewritten message still
  -- names the same identifier, so `locateInMsg`'s span-finder is unaffected).
  let _ ← (runInferC (synthSC [] e) effects).mapError
    (fun m => let m' := rewriteForwardRefMsg prog m; (m', Bang.Surface.locateInMsg src m'))
  (Bang.Surface.lower e).mapError (fun m => (m, Bang.Surface.locateInMsg src m))

/-- PUBLIC typed runnable entry, `Prog`-taking (ADR-0093 D4 — the module resolver's own seam): the
SAME `checkAndLower` pipeline (elaborate → TYPE-CHECK → lower), starting from an already-parsed
`Prog` rather than re-parsing source text. `Main.lean`'s module resolver hands `mergeModules`'
merged `Prog` here DIRECTLY — no print-then-reparse round-trip through `Bang.Format.showProg`
(which would work, since `showProg`/`parseProg` already round-trip, but is strictly more work for
no benefit: the merged `Prog` is already the exact AST the single-file pipeline would parse to). No
span support (a synthesized multi-file `Prog` has no single contiguous source text a `Span` could
index into) — a caller wanting located errors for a MULTI-file program is out of v1 scope (ADR-0093
doesn't sketch cross-file diagnostics; the entry FILE's own parse errors are still located by
`Main.lean`'s resolver before this ever runs, since `mergeModules` only accepts already-parsed
`Prog`s). -/
public def checkAndLowerProg (prog : Prog) : Except String Comp := do
  let (e, effects, _, _) ← elabProg prog
  let _ ← runInferC (synthSC [] e) effects
  Bang.Surface.lower e

/-- `Prog`-taking sibling of `elaborateToComp` — the raw (check-free) `--no-typecheck` escape for
an already-merged multi-file program. Same rationale as `checkAndLowerProg`: the module resolver
already has a `Prog`, not source text, so this skips re-parsing. -/
public def elaborateToCompProg (prog : Prog) : Except String Comp := do
  let (e, _, _, _) ← elabProg prog
  Bang.Surface.lower e

/-- Parse + elaborate + CHECK a source program — the decl-aware, typed sibling of `check`. -/
def checkProg (src : String) : Except String (CT × EffRow) := do
  let (e, effects, _, _) ← Bang.Surface.parseProg src >>= elabProg
  runInferC (synthSC [] e) effects

/-- The ROW of a checked program — the minimal public projection of `checkProg` (whose full
`CT × EffRow` return references the module-private `CT`). Consumers: the Q43 proof-export
total-only gate (`φ = ∅` ⟺ proof-eligible) needs exactly the row, structurally. -/
public def checkProgRow (src : String) : Except String EffRow :=
  (checkProg src).map (·.2)

/-- Parse + elaborate + check + DISPLAY — the decl-aware, typed sibling of `display`. Re-derives
`effects` alongside the checked type (rather than widening `checkProg`'s established `(CT ×
EffRow)` return type, which `typeStringOfProg`/the REPL's `:t` already depend on) so a DECLARED
user-effect label in the row renders by its SOURCE name (ADR-0092 D2), not silently vanishing.
Renders through `showTypeD` (issue #100), not bare `showType` — a `data`-backed μ in the checked
type folds back to its declared name (`List Int`, not `(mu. (Unit + (Int * #0)))`); `ctors`/`gen`
come straight off THIS `elabProg` call (no second `buildEnv`). -/
def displayProg (src : String) : String :=
  match (do
      let (e, effects, ctors, gen) ← Bang.Surface.parseProg src >>= elabProg
      let (B, φ) ← runInferC (synthSC [] e) effects
      return (B, φ, effects, ctors, gen)) with
  | .ok (B, φ, effects, ctors, gen) => showTypeD ctors gen B φ effects
  | .error e                        => s!"error: {e}"

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
`type ! row` of a checked program, or the check error as `.error`. Renders through `showTypeD`
(issue #100), same as `displayProg` — `checkProg`'s established `(CT × EffRow)` return type stays
UNWIDENED (its own doc comment's constraint: `CT` is module-private), so this calls `elabProg`
directly (mirroring `displayProg`'s own inline pattern) rather than routing through `checkProg`,
to recover `ctors`/`gen` for the fold. -/
public def typeStringOfProg (src : String) : Except String String := do
  let (e, effects, ctors, gen) ← Bang.Surface.parseProg src >>= elabProg
  let (B, φ) ← runInferC (synthSC [] e) effects
  return showTypeD ctors gen B φ effects

/-- Prog-taking sibling of `typeStringOfProg` (mirrors `checkAndLowerProg` beside
`checkAndLower`) — the per-declaration query seam `bang query type`/`effects`/`symbols` (#80)
needs: given an already-parsed `Prog`, check its trailing `body` and render `type ! row` as one
string (a String, not `CT × EffRow` — `CT` is module-private, the `checkProgRow` rationale). A
caller wanting "the type of decl `foo`" builds a `Prog` with the same `decls`/`imports`/`uses`
and `body := .var "foo"` — sidestepping print-then-reparse, which `runCheck`'s doc comment
names unsound for a resolved multi-file `Prog`. Renders through `showTypeD` (issue #100) — this is
the DIRECT path `bang query type`/hover/`symbols` ride, so it is the highest-value fold site. -/
public def typeStringOfProgP (prog : Prog) : Except String String := do
  let (e, effects, ctors, gen) ← elabProg prog
  let (B, φ) ← runInferC (synthSC [] e) effects
  return showTypeD ctors gen B φ effects


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

/-- Does the typed run report EITHER a parse error OR a type error (#87's binder-reservation
guards) — the assertion cares only that the program is REJECTED, not at which pipeline stage; a
reserved-keyword-as-binder failure is a parse error (`pIdent`), while an unresolved-op-shape
failure (the fake `param.set(x)` write-attempt guard) surfaces at elaboration. -/
def assertParseErrorOrTypeError (fuel : Nat) (src : String) : Bool :=
  match runOutcome fuel src with | .parseErr _ _ => true | .typeErr _ => true | _ => false

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
      let (e, effects, _, _) ← Bang.Surface.parseProg src >>= elabProg
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
only.

**#112:** MUST `wrapPendingKnots env.pendingKnots` before `elabS`, same as `elabProg` — a law body
can dispatch a 2-param op via `.binopS` (`a == a`, `IntOrd.trans`'s `a < b`, …), which now resolves
via `.app (.force (.var knotName)) …` (see `Inst`'s doc comment); without the wrap, `knotName`
would be an unbound variable at THIS call site, since `elabProg` is not in the chain here — this
is a SEPARATE `elabS env [] …` call, matching `elaborateToComp`'s own by construction, not by
sharing the pre-#112 splice's implicit no-wrapper-needed property. -/
public def checkLawOn (env : ElabEnv) (params : List String) (body : Surf) (args : List Val) : Bool :=
  if params.length != args.length then false else
  let wrapped := (params.zip args).foldr
    (fun (pv : String × Val) acc =>
      match valToSurf pv.2 with
      | some s => .lett pv.1 s acc
      | none   => acc)  -- unsupported sample value ⇒ unbound param ⇒ the check below fails loud
    (wrapPendingKnots env.pendingKnots (Surf.lett "#r" body (.ifS (.var "#r") (.lit 1) (.lit 0))))
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
    | .letD .. => pure ()      -- ADR-0093 D5: no laws attached to a plain let/let-rec decl either
    | .letRecD .. => pure ()
    | .traitD tn _ _ laws =>
        for other in p.decls do
          match other with
          | .traitD .. => pure ()
          | .dataD ..  => pure ()
          | .fnD ..    => pure ()
          | .effectD .. => pure ()   -- ADR-0092: ditto
          | .letD .. => pure ()
          | .letRecD .. => pure ()
          | .implD tn' τTy _ =>
              if tn' == tn && !laws.isEmpty then                -- HK-trait laws are Stage D; Self-only path unchanged
                let τR ← resolveTy env.gen env.aliases τTy env.effects  -- named impl targets sample at the closed μ
                for l in laws do
                  let sample := tuples l.params.length (sampleVT (vtyOf τR))
                  if sample.all (checkLawOn env l.params l.body) then
                    report := report ++
                      [s!"↓ {tn}.{l.name} @ {foldDataTyOrRaw env.ctors env.gen (vtyOf τR)}: DESCENT [test ({sample.length} samples): source law — the ADR-0068 v1 ceiling] (tested)"]
                  else
                    throw s!"law {tn}.{l.name} FAILS on its sample for {foldDataTyOrRaw env.ctors env.gen (vtyOf τR)}"
  return report

/-! #74 fix: a law body — or any expression — is diagnosed as calling a TRAIT OP BY NAME
(`eq(x, x)`/`eq x x`, either the tuple-call or curried-call SHAPE `appSpine` recognizes uniformly)
when the language has NO EXECUTION PATH for that call at all. ADR-0068 wires trait-op resolution
EXCLUSIVELY through the overloaded OPERATOR (`env.insts` is consulted in exactly one place, the
`.binopS` elaboration arm) — there is no `.app`-shaped resolution rule, so `eq(x, x)` reaches
`Source.eval` as a genuinely unbound callee and dies with the opaque kernel message `app: callee is
not a function ('eq')`. This is a REAL v1 constraint (confirmed: even a SIBLING op of the SAME impl
cannot call another op of that impl by name), not a splice/context bug — the fix is diagnostic, not
structural: detect the shape and report the actual constraint instead of a bare runtime crash. -/
mutual
def firstBareOpCall (opNames : List String) : Surf → Option String
  | e =>
    match appSpine e with
    | some (h, _ :: _) => if opNames.contains h then some h else firstBareOpCallStep opNames e
    | _                => firstBareOpCallStep opNames e
def firstBareOpCallStep (opNames : List String) : Surf → Option String
  | .var _ | .lit _ | .getS | .unitS => none
  | .thunk e | .force e | .raise e | .handle e | .putS e | .atomS e | .newS e | .readS e
  | .lam _ e | .inlS e | .inrS e | .foldS e | .unfoldS e | .divMark e | .annotS e _ => firstBareOpCall opNames e
  | .lett _ a b | .app a b | .stateS a b | .writeS a b | .pairS a b | .splitS _ _ a b
  | .binopS _ a b                  => firstBareOpCall opNames a <|> firstBareOpCall opNames b
  | .matchS s _ l _ r              => firstBareOpCall opNames s <|> firstBareOpCall opNames l <|> firstBareOpCall opNames r
  | .ifS c t e                     => firstBareOpCall opNames c <|> firstBareOpCall opNames t <|> firstBareOpCall opNames e
  | .matchD s arms                 => firstBareOpCall opNames s <|> dArmsFirstBareOpCall opNames arms
  | .withCapS _ i _ b              => firstBareOpCall opNames i <|> firstBareOpCall opNames b
  | .dotPerform r _ .none          => firstBareOpCall opNames r
  | .dotPerform r _ (.one a)       => firstBareOpCall opNames r <|> firstBareOpCall opNames a
  | .dotPerform r _ (.two a b)     => firstBareOpCall opNames r <|> firstBareOpCall opNames a <|> firstBareOpCall opNames b
  | .letRecS _ _ f b               => firstBareOpCall opNames f <|> firstBareOpCall opNames b
  -- #68 sugar: the law-diagnostic walk can see raw (pre-erasure) trees — cover `.lettMulti`
  -- like `.lett`: every binding RHS, then the body.
  | .lettMulti binds b             => bindsFirstBareOpCall opNames binds <|> firstBareOpCall opNames b
  -- #21 s7probe: scan `n`/`p`/every clause body/`body`, the `withCapS` precedent above — fitting
  -- closure: this IS the #74 diagnostic-pattern function this probe's brief cites by name.
  | .handleCustomS _lbl n p? _h cls b =>
      firstBareOpCall opNames n <|> argsFirstBareOpCall opNames p?
        <|> hClausesFirstBareOpCall opNames cls <|> firstBareOpCall opNames b
  -- #97 item 2: every sibling RHS, then the body — the `.lettMulti` precedent immediately above.
  | .letRecMultiS binds b          => lrBindsFirstBareOpCall opNames binds <|> firstBareOpCall opNames b
def bindsFirstBareOpCall (opNames : List String) : LetBindings → Option String
  | .nil           => none
  | .cons _ e rest => firstBareOpCall opNames e <|> bindsFirstBareOpCall opNames rest
def lrBindsFirstBareOpCall (opNames : List String) : LetRecBindings → Option String
  | .nil             => none
  | .cons _ _ e rest => firstBareOpCall opNames e <|> lrBindsFirstBareOpCall opNames rest
def argsFirstBareOpCall (opNames : List String) : SurfArgs → Option String
  | .none    => none
  | .one a   => firstBareOpCall opNames a
  | .two a b => firstBareOpCall opNames a <|> firstBareOpCall opNames b
def dArmsFirstBareOpCall (opNames : List String) : DArms → Option String
  | .nil             => none
  | .cons _ _ b rest => firstBareOpCall opNames b <|> dArmsFirstBareOpCall opNames rest
def hClausesFirstBareOpCall (opNames : List String) : HClauses → Option String
  | .nil                => none
  | .cons _ _ b rest    => firstBareOpCall opNames b <|> hClausesFirstBareOpCall opNames rest
end

-- `add(a, b)` (tuple-call) is caught: `add` is a declared trait op, applied to a pair.
#guard firstBareOpCall ["add"] (.app (.var "add") (.pairS (.var "a") (.var "b"))) == some "add"
-- `add a b` (curried-call) is caught too — the SAME shape `appSpine` sees either way.
#guard firstBareOpCall ["add"] (.app (.app (.var "add") (.var "a")) (.var "b")) == some "add"
-- an ORDINARY operator (`a == b`, `.binopS`) is NOT a bare op call — that's the SUPPORTED path.
#guard firstBareOpCall ["eq"] (.binopS Bang.BinOp.eq (.var "a") (.var "b")) == none
-- a name that ISN'T one of the trait's ops (an ordinary local var applied to args) is not flagged.
#guard firstBareOpCall ["eq"] (.app (.var "f") (.var "x")) == none
-- nested inside a `let`/`if` — the traversal reaches every subexpression, not just the top.
#guard firstBareOpCall ["eq"] (.lett "r" (.app (.var "eq") (.pairS (.var "x") (.var "x"))) (.var "r")) == some "eq"

/-- **PUBLIC (#60 seam):** enumerate every LAW INSTANCE in a program — one entry per (trait law ×
matching impl), exactly the pairs `checkLaws` itself walks above, reused structurally (same
trait×impl match, not re-derived). Each entry is `(traitName, lawName, params, body)`, `body`
rendered to SOURCE TEXT (`Bang.Format.showSurf`) rather than the internal `Surf` AST — this keeps
the export's OWN signature entirely `Surf`/`Ty`-free (the narrower alternative preferred over the
broader visibility markers: no new type exposure, just four strings/list-of-strings per instance).
A law-runner harness (`Bang.Witness.LawTest`, #60) can drive each entry's `body` + `params` through
its OWN source-string generation/sampling without needing `ElabEnv`/`Val`/`VT` at all. -/
public def lawInstancesOf (src : String) : Except String (List (String × String × List String × String)) := do
  let p ← parseProgWithDerives src
  let mut out : List (String × String × List String × String) := []
  for d in p.decls do
    match d with
    | .traitD tn _ _ laws =>
        for other in p.decls do
          match other with
          | .implD tn' _ _ =>
              if tn' == tn && !laws.isEmpty then
                for l in laws do
                  out := out ++ [(tn, l.name, l.params, Bang.Format.showSurf l.body)]
          | _ => pure ()
    | _ => pure ()
  return out

/-- **PUBLIC (#60/#74 seam):** for every law instance `lawInstancesOf` would discover, ALSO report
whether its BODY calls a trait op BY NAME (`firstBareOpCall`, against THAT trait's own declared op
names, `sigs.map (·.name)`) — the shape the language has no execution path for (see
`firstBareOpCall`'s docstring). Returns one entry PER LAW INSTANCE, in the SAME order
`lawInstancesOf` would enumerate them (`(traitName, lawName, badOpName?)`), so a caller can zip the
two lists positionally without re-deriving the trait×impl walk a second time (kept as a SEPARATE
function rather than widening `lawInstancesOf`'s own additive/stable 4-tuple signature, which
existing `#guard`s and `LawTest.lean` already destructure). -/
public def lawInstanceOpCallDiagnostics (src : String) : Except String (List (String × String × Option String)) := do
  let p ← parseProgWithDerives src
  let mut out : List (String × String × Option String) := []
  for d in p.decls do
    match d with
    | .traitD tn _ sigs laws =>
        let opNames := sigs.map (·.name)
        for other in p.decls do
          match other with
          | .implD tn' _ _ =>
              if tn' == tn && !laws.isEmpty then
                for l in laws do
                  out := out ++ [(tn, l.name, firstBareOpCall opNames l.body)]
          | _ => pure ()
    | _ => pure ()
  return out

-- a law body calling its OWN trait op by name IS flagged, naming the op (the #74 shape — the
-- stranger's exact program modulo cosmetic naming).
#guard (match lawInstanceOpCallDiagnostics
    "trait Eq { fn eq(a, b) -> Int law refl(x): eq(x, x) == 1 } impl Eq for Int { fn eq(a, b) = a } 0" with
        | .ok [("Eq", "refl", some "eq")] => true | _ => false)
-- (the companion "IS NOT flagged for the supported operator-only shape" guard lives further down,
-- once `intOrdProg` is in scope — see the `lawInstanceOpCallDiagnostics` block near `intOrdProg`.)

/-! #74 fix, part 2: an `impl <Trait> for Int` targeting an op that ALIASES a built-in binop
(`add`/`sub`/`mul`/`div`/`lt`/`eq` — `binopName`'s own reverse map) is SILENTLY DEAD — `Int`
operands hit the kernel's own δ-rule (`.binopS`'s `.ok .int` arm, checked BEFORE `env.insts` is
ever consulted) unconditionally, so the impl's op body can never be reached through the operator
its own trait declares it for. Confirmed structurally (the SAME code path #74's diagnosis walked):
not a hypothetical, a REAL v1 gap an author can trip over silently — `impl Eq for Int` type-checks
and BUILDS fine, it simply never runs. Fail-loud here beats a silently-inert impl. -/
public def unreachableIntImplDiagnostics (src : String) : Except String (List (String × String)) := do
  let p ← parseProgWithDerives src
  let mut out : List (String × String) := []
  for d in p.decls do
    match d with
    | .implD tn .tInt ops =>
        for od in ops do
          if [Bang.BinOp.add, .sub, .mul, .div, .lt, .eq].any (fun op => binopName op == od.name) then
            out := out ++ [(tn, od.name)]
    | _ => pure ()
  return out

-- `impl Eq for Int`'s `eq` op aliases the built-in `==` — flagged as unreachable.
#guard (match unreachableIntImplDiagnostics
    "trait Eq { fn eq(a, b) -> Int } impl Eq for Int { fn eq(a, b) = a }" with
        | .ok [("Eq", "eq")] => true | _ => false)
-- an impl targeting a NON-`Int` type (the real, WORKING corpus shape — `(Int * Int)`) is not
-- flagged: `.binopS`'s δ-rule only shortcuts `Int` operands, so `env.insts` IS reached for anything
-- else.
#guard (match unreachableIntImplDiagnostics
    "trait Eq2 { fn eq(a, b) -> Int } impl Eq2 for (Int * Int) { fn eq(a, b) = 1 }" with
        | .ok [] => true | _ => false)
-- an `impl … for Int` whose op DOESN'T alias any built-in name (an ordinary custom op, e.g. `dbl`)
-- is not flagged — only the SIX operator-aliased names are actually shadowed.
#guard (match unreachableIntImplDiagnostics
    "trait Dbl { fn dbl(a, b) -> Int } impl Dbl for Int { fn dbl(a, b) = a }" with
        | .ok [] => true | _ => false)

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

-- `lawInstanceOpCallDiagnostics` companion: a law body using ONLY the overloaded operator (the
-- supported v1 shape, `IntOrd`'s real corpus convention — `a < b`, never `lt(a, b)`) is NOT
-- flagged. Confirms the detector doesn't over-fire on the language's actually-working law shape.
#guard (match lawInstanceOpCallDiagnostics (intOrdProg "trans(a, b, c): a < b => b < c => a < c" "0") with
        | .ok [("IntOrd", "trans", none)] => true | _ => false)

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
-- the data type DISPLAYS by its DECLARED name (issue #100's display-time re-fold), not the raw
-- structural μ ADR-0069 decision 3's transparent-alias encoding produces underneath.
#guard displayProg (listProg "Cons(7, Nil)") == "IntList"
-- fail-loud: a missing arm · an unknown ctor · payload-arity mismatch at the type level.
#guard (match checkProg (listProg "let s = Nil in match s { Nil -> 0 }") with
        | .error _ => true | _ => false)
#guard (match checkProg (listProg "let s = Nil in match s { Nil -> 0, Snoc(h, t) -> h }") with
        | .error _ => true | _ => false)
#guard (match checkProg (listProg "Cons(7)") with | .error _ => true | _ => false)

/-! ### Validation ⑨a — ADR-0099: constructors are TYPE-namespaced (#108).

The four `docs/decisions/witness-0099/*.bang` witnesses, promoted into the corpus (hand-verified
against the real `bang` binary at ADR-0099 design time; expectations here are the SAME programs run
through the SAME `checkProg`/`runTypedYieldsInt` oracle helpers Validation ⑨ already uses — never
guessed). `List a`'s `Nil`/`Cons` and `IntList`'s `Nil`/`Cons` co-present is the collision this ADR
resolves: a cross-type bare-name collision is a USE-time ambiguity (B012), not a registration-time
refusal. -/
def collidingListsProg (body : String) : String :=
  "data List a = Nil | Cons(a, List a) data IntList = Nil | Cons(Int, IntList) " ++ body

-- w0: two `data` decls sharing bare ctor names, UNUSED — nothing is ambiguous, no registration-time
-- refusal (the pre-#108 behavior was `error: duplicate constructor 'Nil'` even here).
#guard runTypedYieldsInt 200 (collidingListsProg "0") 0
-- w1: the #105/#108 acceptance case — a prelude-shaped `List a` and a user `IntList` coexist, each
-- matched via ITS OWN qualified ctor names (`IntList_Nil`/`IntList_Cons`) since the bare names
-- collide (both types are in scope).
#guard runTypedYieldsInt 600 (collidingListsProg
  "let xs = IntList_Cons(7, IntList_Nil) in match xs { IntList_Nil -> 0, IntList_Cons(h, t) -> h }") 7
-- w2: a BARE ambiguous ctor reference is a LOUD B012 error naming both owning types + the qualified
-- spellings — never a silent pick of "whichever `data` decl came first".
#guard (match checkProg (collidingListsProg "Nil") with
        | .error m => (m.splitOn "ambiguous constructor 'Nil'").length > 1
            && (m.splitOn "IntList (as 'IntList_Nil')").length > 1
            && (m.splitOn "List (as 'List_Nil')").length > 1
        | .ok _ => false)
-- w3: a bare ctor name only ONE in-scope type owns still resolves bare — the common (non-colliding)
-- case is untouched by namespacing. `L`/`LNil`/`LCons` has no cross-type collision with `IntList`.
def nonCollidingListsProg (body : String) : String :=
  "data L = LNil | LCons(Int, L) data IntList = Nil | Cons(Int, IntList) " ++ body
#guard runTypedYieldsInt 600 (nonCollidingListsProg
  "let xs = Cons(7, Nil) in match xs { Nil -> 0, Cons(h, t) -> h }") 7

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

/-! ### Validation ⑨j′ — MUTUAL `let rec … and …` (#97 item 2, H2 tuple-of-thunks μ-knot).

`let rec f : T1 = e1 and g : T2 = e2 … in body` (grammar: `Bang.Surface.pLetRecBindings`;
elaboration: `elabS`'s `.letRecMultiS` arm → `buildLetRecMulti`) generalizes ⑨e's single-function
knot to an N-tuple self-knot every sibling shares — each sibling forces the SAME knot and projects
its own slot, giving MUTUAL visibility by construction (not textual ordering). Every mutual group
conservatively carries `Div` (⑨g's structural certification is NOT extended to co-recursive name
sets — a documented, unscoped gap, see the ADR), so every sibling needs the explicit `! {Div}`
annotation ⑨f already demonstrates for the single-function case. -/
-- even/odd, the CANONICAL 2-way mutual pair — genuinely alternating calls, no base-case guard
-- collapse possible (each sibling's ONLY recursive exit is through the OTHER).
def evenOddProg (arg : Int) (call : String) : String :=
  s!"let rec even : Int -> Int ! \{Div} = fun n => " ++
    "let c = n == 0 in if c then 1 else let n1 = n - 1 in ($odd) n1 " ++
    "and odd : Int -> Int ! {Div} = fun n => " ++
    "let c = n == 0 in if c then 0 else let n1 = n - 1 in ($even) n1 " ++
    s!"in (${call}) {arg}"
#guard runTypedYieldsInt 4000 (evenOddProg 10 "even") 1
#guard runTypedYieldsInt 4000 (evenOddProg 10 "odd") 0
#guard runTypedYieldsInt 4000 (evenOddProg 7 "even") 0
#guard runTypedYieldsInt 4000 (evenOddProg 7 "odd") 1
#guard runTypedYieldsInt 4000 (evenOddProg 0 "even") 1
#guard runTypedYieldsInt 4000 (evenOddProg 1 "even") 0
-- DIFFERENTIAL vs the hand-fused single-function equivalent (today's nested-`let rec` workaround
-- shape, `⑨g`'s `smDef`/`lenDef` precedent) — same computed value at every tested `n`, confirming
-- the mutual sugar is not just "typechecks" but semantically EQUIVALENT to the manual encoding it
-- replaces (the H2 spike's own differential falsifier, now through the REAL grammar).
def fusedParityProg (parity arg : Int) : String :=
  s!"let rec fused : Int -> Int -> Int ! \{Div} = fun p => fun n => " ++
    "let c = n == 0 in if c then (1 - p) else " ++
    "let p1 = 1 - p in let n1 = n - 1 in ($fused) p1 n1 " ++
    s!"in ($fused) {parity} {arg}"
#guard runTypedYieldsInt 4000 (fusedParityProg 0 10) 1
#guard runTypedYieldsInt 4000 (fusedParityProg 1 10) 0
#guard runTypedYieldsInt 4000 (fusedParityProg 0 7) 0
#guard runTypedYieldsInt 4000 (fusedParityProg 1 7) 1
#guard (runTypedYieldsInt 4000 (evenOddProg 10 "even") 1) == (runTypedYieldsInt 4000 (fusedParityProg 0 10) 1)
#guard (runTypedYieldsInt 4000 (evenOddProg 7 "odd") 1) == (runTypedYieldsInt 4000 (fusedParityProg 1 7) 1)
-- a LEAF sibling (references NO sibling name, including itself) alongside one that calls it — the
-- root-caused wall (`elabLetRecBindings` using the unresolved `Ty` + `checkSC`'s catch-all doing
-- exact row unification instead of subsumption on the pair tail) is now a PERMANENT regression
-- guard, not just a scratchpad repro.
#guard runTypedYieldsInt 2000
  ("let rec f : Int -> Int ! {Div} = fun n => n " ++
   "and g : Int -> Int ! {Div} = fun n => let c = n == 0 in if c then n else ($f) n " ++
   "in ($g) 3") 3
-- a THREE-way fully-cyclic group (confirms the N-tuple projection generalizes past N=2) — each
-- sibling's ONLY base case is its own turn in the a→b→c→a… cycle; 9 decrements from `a` lands
-- back on `a`'s own base case (9 mod 3 == 0).
#guard runTypedYieldsInt 4000
  ("let rec a : Int -> Int ! {Div} = fun n => " ++
   "let z1 = n == 0 in if z1 then 1 else let n1 = n - 1 in ($b) n1 " ++
   "and b : Int -> Int ! {Div} = fun n => " ++
   "let z2 = n == 0 in if z2 then 2 else let n1 = n - 1 in ($c) n1 " ++
   "and c : Int -> Int ! {Div} = fun n => " ++
   "let z3 = n == 0 in if z3 then 3 else let n1 = n - 1 in ($a) n1 " ++
   "in ($a) 9") 1
-- a MUTUAL group's CALL-SITE row contains Div (⑨f's precedent, generalized) — the conservative
-- default (structural certification is NOT extended to co-recursive sets).
#guard (match checkProg (evenOddProg 10 "even") with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
-- a sibling MISSING its own mandatory type ascription fails loud (ADR-0073's rule generalized —
-- the grammar itself enforces this, `pLetRecBindings` always requires `: Ty` per sibling, so this
-- guard documents the PARSE-level rejection of an attempted omission, not an elaborator check).
#guard (match Bang.Surface.parseProg "let rec f : Int -> Int = fun n => n and g = fun n => n in ($f) 3" with
        | .error _ => true | .ok _ => false)
-- a non-function sibling (mirrors ⑨e's single-function "requires a function literal" guard).
#guard (match checkProg "let rec f : Int -> Int = fun n => n and x : Int = 5 in ($f) 3" with
        | .error _ => true | _ => false)

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

`concat`/`reverse`/`eq` are `let rec` folds in `Prelude.bang`, auto-`use`d (ADR-0098, `injectPrelude`)
into scope of every program that mentions them, so a program uses them WITHOUT re-inlining (the #50
gap the tokenizer hit). Pre-
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

/-! ### Strings & Characters (issue #65: the stranger-test's documented blind spot).
The generated reference had NO Str/Char/string-literal coverage — every string fact was
reverse-engineered from example source (strip the examples and ship-ability dropped 8.5→4/10).
Self-contained (no `lengthDef`-style prelude prepend) so `tools/gen-reference.py` picks each one
up as a plain `runTypedYieldsInt N "src" val` example — these ARE the reference-doc content, not
a second hand-copied set. Every fact here is a CITE, not a claim: run through `bang eval` first,
then pinned as a `#guard` (never the reverse).

CODEPOINT ENCODING (closing GAP B — the stranger's guess): `Char.toNat` (Lean 4 stdlib) is a
Unicode SCALAR VALUE, not an ASCII byte — `'é'` (U+00E9) yields 233, not a UTF-8 byte sequence.
Every literal in this corpus happens to fall in the ASCII range (0–127) because that is what the
examples need, NOT because the mechanism enforces it — stating "ASCII" would be an overclaim the
reference must not repeat. -/

-- IDIOM 1 (match a string): destructure `SNil`/`SCons(Char(n), rest)` to read its first code point.
#guard runTypedYieldsInt 100 "match \"ab\" { SNil -> 0, SCons(c, t) -> match c { Char(n) -> n } }" 97
-- IDIOM 1, the empty string: `SNil` (no `SCons` to destructure).
#guard runTypedYieldsInt 100 "match \"\" { SNil -> 0, SCons(c, t) -> match c { Char(n) -> n } }" 0
-- IDIOM 2 (build a char from a code point): `Char <n>` introduces; round-tripping recovers `n`.
#guard runTypedYieldsInt 100 "match (Char 97) { Char(n) -> n }" 97
-- IDIOM 3 (common code point constants, all ASCII per the codepoint-encoding note above): space.
#guard runTypedYieldsInt 100 "match ' ' { Char(n) -> n }" 32
-- IDIOM 3: the digit range '0'-'9'.
#guard runTypedYieldsInt 100 "match '0' { Char(n) -> n }" 48
#guard runTypedYieldsInt 100 "match '9' { Char(n) -> n }" 57
-- IDIOM 3: the lowercase letter range 'a'-'z'.
#guard runTypedYieldsInt 100 "match 'a' { Char(n) -> n }" 97
#guard runTypedYieldsInt 100 "match 'z' { Char(n) -> n }" 122
-- IDIOM 3: the uppercase letter range 'A'-'Z'.
#guard runTypedYieldsInt 100 "match 'A' { Char(n) -> n }" 65
#guard runTypedYieldsInt 100 "match 'Z' { Char(n) -> n }" 90
-- the auto-`use`d STDLIB (free in every program, no import needed — `Prelude.bang`, ADR-0098): `concat`.
#guard runTypedYieldsInt 3000 "match (($concat) \"foo\" \"bar\") { SNil -> 0, SCons(c, t) -> match c { Char(n) -> n } }" 102
-- the injected STDLIB: `eq`, structural string equality.
#guard runTypedYieldsInt 3000 "if (($eq) \"cat\" \"cat\") then 1 else 0" 1
#guard runTypedYieldsInt 3000 "if (($eq) \"cat\" \"dog\") then 1 else 0" 0

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

/-! ### #119 — the row-subsumption asymmetry (fork-1): `checkSC`'s `.annotS` arm ALREADY used
`subRow` (declared ⊇ actual) correctly; the generic catch-all (`synthSC` + `unifyC`'s `.U`-row
EQUALITY) did not, so a declared-bound value REACHING the catch-all (a `.lett`-chain tail, a
`matchS` arm tail, an `.app` tail) got a FALSE B003 row mismatch even though its ACTUAL row is a
genuine subset of its DECLARED bound. Each demo below: the payload's declared `Thunk (… ! {Div})`
is wider than what its body actually performs (no real Div anywhere) — exactly the "leaf sibling
declared Div but never performs it" shape `buildLetRecMulti` hit live (#97). Fixed via explicit
`checkSC` arms for `.lett`/`.matchS` (routing the tail back through `checkSC`, which reaches
`checkSV`'s pre-existing `subRow`-aware `.thunk` case) and a dedicated row-subsumption-aware
structural comparator (`subsumeAppV`/`subsumeAppC`) for `.app`'s codomain (the one shape with no
other explicit arm to fall back on). RED-BEFORE: each of these three `checkProg`s failed
("effect row mismatch"/"computation type mismatch") on the PRE-fix catch-all (confirmed live by
disabling each new arm in turn and rebuilding — `buildLetRecMulti`'s OWN `.annotS`-wrap workaround,
now removed, hit the identical wall at the SAME `unifyRow` exact-equality call). -/

-- (1) a `.lett`-chain TAIL ending in a pair-of-declared-Div-thunks (byte-identical shape to
-- `buildLetRecMulti`'s pair-of-thunks knot, minus the μ-encoding — the minimal isolation).
def rowSubL119Src := "let pair = ({let x = 1 in ({fun n => n + x}, {fun n => n + x})} : Thunk (Thunk (Int -> Int ! {Div}) * Thunk (Int -> Int ! {Div}))) in let (a, b) = $(pair) in ($(a) 4) + ($(b) 6)"
#guard (match checkProg rowSubL119Src with | .ok _ => true | _ => false)
#guard runTypedYieldsInt 500 rowSubL119Src 12

-- (2) a `matchS` ARM tail ending in the same pair-of-declared-Div-thunks shape.
def rowSubM119Src := "let pair = ({match Right(7) { Left(a) -> ({fun n => n + a}, {fun n => n + a}), Right(x) -> ({fun n => n + x}, {fun n => n + x}) }} : Thunk (Thunk (Int -> Int ! {Div}) * Thunk (Int -> Int ! {Div}))) in let (a, b) = $(pair) in ($(a) 1) + ($(b) 2)"
#guard (match checkProg rowSubM119Src with | .ok _ => true | _ => false)
#guard runTypedYieldsInt 500 rowSubM119Src 17

-- (3) an `.app` TAIL: an unannotated callee (`mkPair`, fully INFERRED at ⊥ internally) applied and
-- the RESULT checked against an outer declared `{Div}` bound — the one shape with no OTHER
-- explicit `checkSC` arm, needing `subsumeAppV`/`subsumeAppC`'s own structural descent.
def rowSubA119Src := "let mkPair = {fun z => ({fun n => n + z}, {fun n => n + z})} in let pair = ({$(mkPair) 1} : Thunk (Thunk (Int -> Int ! {Div}) * Thunk (Int -> Int ! {Div}))) in let (a, b) = $(pair) in ($(a) 4) + ($(b) 6)"
#guard (match checkProg rowSubA119Src with | .ok _ => true | _ => false)
#guard runTypedYieldsInt 500 rowSubA119Src 12

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

/-! ### Validation ⑨i-bis — issue #101: the WILDCARD match arm `_`.

`_ -> body` expands to one fresh arm per constructor NOT already covered by an earlier explicit
arm (`expandWildcardArms`, ADR-0069's own elaboration shape unchanged — the kernel sees an
ordinary fully-explicit `matchS` chain). Positive cases run through `runTypedYieldsInt` (the
run-oracle); the three error shapes (misplaced, unanchored, dead) through
`assertParseErrorOrTypeError` (elaboration-stage, `.typeErr` bucket per `runOutcome`'s split). -/

-- a 3-ctor type, ONE explicit arm + wildcard covering the other two — picks the wildcard body.
#guard runTypedYieldsInt 400 "data Color = Red | Green | Blue match Red { Red -> 1, _ -> 0 }" 1
#guard runTypedYieldsInt 400 "data Color = Red | Green | Blue match Green { Red -> 1, _ -> 0 }" 0
#guard runTypedYieldsInt 400 "data Color = Red | Green | Blue match Blue { Red -> 1, _ -> 0 }" 0
-- a 2-ctor recursive type: `_` covers the UNNAMED `Nil` case, `Cons` stays explicit and binds its payload.
#guard runTypedYieldsInt 800
  "data List a = Nil | Cons(a, List a) match (Cons(7, Nil)) { Cons(h, t) -> h, _ -> 0 }" 7
#guard runTypedYieldsInt 800
  "data List a = Nil | Cons(a, List a) match (Nil : List Int) { Cons(h, t) -> h, _ -> 99 }" 99
-- wildcard covering exactly ONE of three ctors (the other two named explicitly) — no wasted expansion.
#guard runTypedYieldsInt 400
  "data Color = Red | Green | Blue match Blue { Red -> 1, Green -> 2, _ -> 3 }" 3
-- GENERIC data (ADR-0069 bite-1): the wildcard's fresh binders are typed no differently than an
-- explicit arm's would be — irrelevant here since the wildcard body ignores its payload, but the
-- expansion must still resolve `Cons`'s GENERIC arity (2) to mint exactly 2 fresh binder names.
#guard runTypedYieldsInt 800
  "data List a = Nil | Cons(a, List a) match (Cons(1, Cons(2, Nil)) : List Int) { Nil -> 0, _ -> 42 }" 42
-- NESTED match: an inner wildcard and an outer wildcard, independently expanded.
#guard runTypedYieldsInt 1200
  ("data List a = Nil | Cons(a, List a) " ++
   "match (Cons(3, Cons(7, Nil))) { Cons(h, t) -> match t { Cons(h2, t2) -> h2, _ -> (0 - 1) }, _ -> (0 - 2) }") 7
#guard runTypedYieldsInt 1200
  ("data List a = Nil | Cons(a, List a) " ++
   "match (Cons(3, Nil)) { Cons(h, t) -> match t { Cons(h2, t2) -> h2, _ -> (0 - 1) }, _ -> (0 - 2) }") (0 - 1)

-- B014 error 1: `_` before the LAST arm (arms after it are unreachable — rejected, not silently
-- dropped). Asserts the EXACT message (via `runOutcome`, not just "some error fired") — pre-#101,
-- `_` was an unrecognized ctor name and ALSO rejected, so a bare `assertParseErrorOrTypeError`
-- would pass vacuously without exercising this fix; pinning the message text makes the guard
-- meaningful (it fails loud if the wildcard-position check regresses to a different diagnostic).
-- NOTE: `locateInMsg` (issue #52 Stage B) POST-HOC locates the first single-quoted token in an
-- elaboration message — `'_'` is the first quote here, and `_` genuinely occurs in the source, so
-- `locateToken` FINDS it and `checkAndLower` reports this as a `.parseErr (some sp)`, not
-- `.typeErr` (an accidental-but-harmless side effect of #52's generic quoted-name heuristic firing
-- on a wildcard's own quoting convention — not a v1 bug, just a bucketing quirk this guard must
-- match rather than fight); both branches are asserted so the guard is honest about which fires.
#guard (match runOutcome 400 "data Color = Red | Green | Blue match Red { _ -> 1, Green -> 2 }" with
  | .typeErr m           => m == "wildcard arm '_' must be the LAST arm in a match — arms after it can never fire (unreachable)"
  | .parseErr (some _) m => m == "wildcard arm '_' must be the LAST arm in a match — arms after it can never fire (unreachable)"
  | _                    => false)
-- B014 error 2: `_` alone with no explicit arm to anchor the match's data type (same `locateInMsg`
-- quirk: `'_'` quote-locates).
#guard (match runOutcome 400 "data Color = Red | Green | Blue match Green { _ -> 42 }" with
  | .typeErr m           => m == "wildcard arm '_' needs at least one explicit constructor arm to name the match's data type"
  | .parseErr (some _) m => m == "wildcard arm '_' needs at least one explicit constructor arm to name the match's data type"
  | _                    => false)
-- B014 error 3: `_` covers NOTHING — every ctor already has an explicit arm (dead code).
#guard (match runOutcome 400
    ("data List a = Nil | Cons(a, List a) " ++
     "match (Nil : List Int) { Nil -> 1, Cons(h, t) -> h, _ -> 99 }") with
  | .typeErr m           => m == "wildcard arm '_' covers no constructors — every constructor of this data type already has an explicit arm (dead code)"
  | .parseErr (some _) m => m == "wildcard arm '_' covers no constructors — every constructor of this data type already has an explicit arm (dead code)"
  | _                    => false)
-- B014's `codeForMsg` contract (all three messages) is asserted in `DiagCodes.lean` itself — that
-- module is DOWNSTREAM of this one (`Diagnostics.lean` imports `DiagCodes.lean` imports
-- `TypeCheck.lean`), so it cannot be re-imported here (the SAME cycle `surfUsesVar`'s doc comment
-- names above); the exact three message strings are kept byte-identical between the two files by
-- construction, since both are copied from `expandWildcardArms`'s literal `throw` text.

/-! ### Validation ⑨j — the GENERIC PRELUDE: `Option`/`Result` + their maps + the ISO round-trips vs
the built-in sum `Either` (the tagged-sum TYPES injected globally, `genericPrelude`; their COMBINATORS
— `mapOption`/`mapResult`/`bimap`/the isos — auto-`use`d from `Prelude.bang`, ADR-0098). The tagged-sum
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

/-! ### Validation ⑨k — issue #105 FIRST-SLICE PRELUDE: `fst`/`snd`/`abs`/`min`/`max`/`withDefault`/
`const` + the char-class kit (`isDigit`/`isAlpha`/`toUpper`/`toLower`), all `Prelude.bang` entries
auto-`use`d (ADR-0098; docs/notes/stdlib-prelude-survey.md §3 — the first slice, ordered by dogfood
demand). Each is used FREE with no local `let`/declaration (the injection under test); the char-kit guards use
`(Char 97)`-style ctor-application (a `Char` literal `'a'` desugars to the SAME `Char 97`, both are
exercised — see the `let c = 'a'`-style guards below). No List entry ships in this slice — the survey
found NO free injected generic `List a` exists (only per-program user `data List a` declarations,
e.g. `monoidInt` above); the list-independent subset ships alone, see the design-finding note below. -/
-- `fst`/`snd` — the dogfood-json TOP papercut. `p` a literal pair.
#guard runTypedYieldsInt 400 "($fst) (3, 4)" 3
#guard runTypedYieldsInt 400 "($snd) (3, 4)" 4
-- `abs` — negative and positive/zero branches (both dogfooders hand-rolled `0 - n`).
#guard runTypedYieldsInt 400 "($abs) (0 - 7)" 7
#guard runTypedYieldsInt 400 "($abs) 7" 7
#guard runTypedYieldsInt 400 "($abs) 0" 0
-- `min`/`max` — curried; both orderings (the `<` branch and its else).
#guard runTypedYieldsInt 400 "(($min) 3) 7" 3
#guard runTypedYieldsInt 400 "(($min) 7) 3" 3
#guard runTypedYieldsInt 400 "(($max) 3) 7" 7
#guard runTypedYieldsInt 400 "(($max) 7) 3" 7
-- `const x y = x` — the `id` companion; used at two distinct 2nd-arg types (Int, a pair) like the
-- test-local `const` at ⑦b, proving the injected one generalizes the same way.
#guard runTypedYieldsInt 400 "(($const) 5) 9" 5
#guard runTypedYieldsInt 400 "(($const) 7) (1, 2)" 7
-- `withDefault d o` — `Some` returns the payload, `None` returns the default (both arms, Option's
-- two ctors — mirrors the `mapOption`/`mapResult` Err/Ok-both-arms discipline above).
#guard runTypedYieldsInt 400 "(($withDefault) 0) (Some(9))" 9
#guard runTypedYieldsInt 400 "(($withDefault) 42) (None : Option Int)" 42
-- CHAR KIT — `isDigit`: the '0'-'9' boundary (47 fails-low, 48/57 the inclusive ends, 58 fails-high).
#guard runTypedYieldsInt 400 "if (($isDigit) (Char 48)) then 1 else 0" 1
#guard runTypedYieldsInt 400 "if (($isDigit) (Char 57)) then 1 else 0" 1
#guard runTypedYieldsInt 400 "if (($isDigit) (Char 97)) then 1 else 0" 0
-- `isAlpha`: both letter ranges (upper/lower) true, a digit false — the non-letter edge.
#guard runTypedYieldsInt 400 "if (($isAlpha) (Char 65)) then 1 else 0" 1
#guard runTypedYieldsInt 400 "if (($isAlpha) (Char 122)) then 1 else 0" 1
#guard runTypedYieldsInt 400 "if (($isAlpha) (Char 53)) then 1 else 0" 0
-- `toUpper`/`toLower` — TOTAL: the letter-shift case AND the non-letter passthrough case each.
#guard runTypedYieldsInt 400 "match (($toUpper) (Char 97)) { Char(n) -> n }" 65
#guard runTypedYieldsInt 400 "match (($toUpper) (Char 53)) { Char(n) -> n }" 53
#guard runTypedYieldsInt 400 "match (($toLower) (Char 65)) { Char(n) -> n }" 97
#guard runTypedYieldsInt 400 "match (($toLower) (Char 53)) { Char(n) -> n }" 53
-- shadowing: a user `let abs = …` in the body WINS over the injected one (lexical scope contract).
#guard runTypedYieldsInt 400 "let abs = { fun n => 999 } in ($abs) (0 - 7)" 999
-- INERT for unused: the whole #105 bucket adds no effect to a program that never mentions any of it.
-- `EffRow.isEmpty`/`.card` are NONCOMPUTABLE in the compiled `#guard` path — `decide (ρ = ∅)` is the
-- computable emptiness idiom (rides Finset's `DecidableEq`), matching `showRow`'s own usage.
#guard (match checkProg "3" with | .ok (_, ρ) => decide (ρ = ∅) | _ => false)

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
-- ADR-0095 D5 / #93: `resume` is reserved (NOT a built-in op — reserved for the FUTURE explicit
-- resume(w) form) so its later arrival is additive, never a breaking change.
#guard (match Bang.Surface.parseProg "effect F { resume : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
-- ...and the diagnostic names the reason (the future form + the issue), not a bare rejection.
#guard (match Bang.Surface.parseProg "effect F { resume : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with
            | .error m => (m.splitOn "future explicit resume").length > 1 | .ok _ => false)
        | .error _ => false)
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
-- #87: `param` gets the SAME dual reservation `resume` does — an `effect` declaring an op named
-- `param` would type-check but leave that op's clause UNPARSEABLE (`param(y) => …`'s clause HEAD
-- is also `pIdent`-routed), so it is rejected here, at decl elaboration, with a diagnostic naming
-- the real reason.
#guard (match Bang.Surface.parseProg "effect G { param : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with | .error _ => true | .ok _ => false) | .error _ => false)
#guard (match Bang.Surface.parseProg "effect G { param : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with
            | .error m => (m.splitOn "carried-param clause binder").length > 1 | .ok _ => false)
        | .error _ => false)

/-! ### #93 continued — the BINDER half of D5's reservation. The OP-NAME half (the corpus
immediately above) already covers `effect Foo { resume : … }`; D5's OWN text is "reserved as an
op name AND a binder" — the binder half (a clause arg-binder, a `let`/`fun` name, or a bare
reference to `resume`) is a SEPARATE mechanism, `pIdent`/`pAtom`'s reserved-word-list entries in
`Bang/Frontend/Surface.lean` (the SAME mechanism `with`, D1's own reservation, already uses) —
`pEffectMembers` parses an op name directly off the token stream, never through `pIdent`, so the
op-name check above cannot also cover binders; this is why the reservation needs both mechanisms,
not one. -/

-- `resume` as a BINDER — a `let`-bound name — is rejected at PARSE time.
#guard (match Bang.Surface.parseProg "let resume = 5 in resume" with
        | .error _ => true | .ok _ => false)

-- `resume` as a handler CLAUSE's arg-binder is rejected at PARSE time too (the exact position D5's
-- future explicit form would bind it in).
#guard (match Bang.Surface.parseProg "effect Net { fetch : Int -> Int } handle net.fetch(1) with Net as net { fetch(resume) => resume * 10 }" with
        | .error _ => true | .ok _ => false)

-- a NON-colliding name (`resumed`, not `resume`) is ACCEPTED — the reservation is precise, not an
-- over-broad rejection of anything superficially similar (the `read4`-vs-`read` precedent, #92).
#guard (match Bang.Surface.parseProg "effect Foo { resumed : Int -> Int } 0" with
        | .ok p => (match buildEnv p.decls with | .ok _ => true | .error _ => false)
        | .error _ => false)
#guard (match Bang.Surface.parseProg "let resumed = 5 in resumed" with
        | .ok _ => true | .error _ => false)

/-! ### ADR-0095 D1 (RULED) `handle e with Name as h { … }` — the REAL SURFACE corpus (#21
s7probe/#44 Stage 7 e2e battery). Kernel-adjacent complement to `examples/handle-custom-*`
(the run-oracle gate, `tools/check-examples.sh`): these `#guard`s pin the TYPE-CHECK verdicts and
the D4 teaching diagnostic, catching a regression at `just check`/compiled-`#guard` speed rather
than only at the slower example-run gate. `checkProg`/`checkAndLower` are the SAME production
pipeline `bang check`/`bang run` use (no separate test-only path). -/

-- the ADR-0095 D1 tracer bullet's OWN worked example (renamed read→fetch — `read` collides with
-- the STM built-in's reserved name, #21 s7probe Finding 5) types cleanly.
#guard (match checkProg
    "effect Net { fetch : Int -> Int } handle (net.fetch(1)) + (net.fetch(2)) with Net as net { fetch(n) => n * 10 }"
  with | .ok _ => true | .error _ => false)

-- the Stage-2 kernel's `customResume`/`customAbortCoexist` #guards (`Eval.lean`), ported to
-- SOURCE TEXT, both type-check (the `bang eval` RUN-oracle check lives in
-- `examples/handle-custom-resume` / `examples/handle-custom-abort-coexist`, gated by
-- `tools/check-examples.sh` — this #guard pins the FASTER type-check-only verdict alongside it).
#guard (match checkProg
    "effect Reader { fetch : Int -> Int } handle (let r = net.fetch(5) in r + 1) with (Reader 100) as net { fetch(x) => x + 100 }"
  with | .ok _ => true | .error _ => false)
#guard (match checkProg
    "effect Reader { fetch : Int -> Int } handle (handle (let r = raise 42 in net.fetch(5)) with (Reader 100) as net { fetch(x) => x + 100 })"
  with | .ok _ => true | .error _ => false)

-- `runInferV` `effects` seeding (plan 003 — the fifth WALL-3-class candidate, verdict LATENT):
-- a user-effect perform inside a THUNK bound by `let`, reached under a binop (the elaborator's
-- `runInferV` A-normalization probes). Pins the seeding contract: this types cleanly — the
-- throwaway `runInferV` probes are non-fatal on failure and the CHECKER (seeded via
-- `runInferC env.effects`) rules, so `runInferV`'s default `effects := []` stays
-- behaviour-identical at every pre-existing call site.
#guard (match checkProg
    "effect Net { fetch : Int -> Int } handle (let t = {net.fetch(1)} in $t) + 0 with Net as net { fetch(n) => n * 10 }"
  with | .ok _ => true | .error _ => false)

-- `with` is RESERVED (#21 s7probe Finding 3 — without it, `pApp`'s application-fold silently
-- swallowed `with Name {…}` as an ordinary application chain instead of erroring): a program
-- using `with` as a bare identifier is rejected at PARSE time.
#guard (match Bang.Surface.parseProg "effect Net { fetch : Int -> Int } let with = 5 with" with
        | .error _ => true | .ok _ => false)

-- missing clause coverage (`ping` has no clause) is a clause-level diagnostic naming the effect
-- + the uncovered op, not a bare crash.
#guard (match checkProg
    "effect Net { fetch : Int -> Int, ping : Int -> Int } handle net.fetch(1) with Net as net { fetch(n) => n }"
  with
  | .error m => (m.splitOn "has no clause").length > 1
  | .ok _    => false)

-- an unknown op name in a clause head is a clause-level diagnostic naming the effect.
#guard (match checkProg
    "effect Net { fetch : Int -> Int } handle net.fetch(1) with Net as net { fetch(n) => n, ping(n) => n }"
  with
  | .error m => (m.splitOn "is not an operation of effect").length > 1
  | .ok _    => false)

-- ADR-0095 D4 (RULED): the TEACHING diagnostic — a clause body that performs an effect before
-- resuming (here, `raise n`) is REJECTED with the specific v1-restriction message naming ADR-0065
-- + Q27 (the general-body entry gate), never a bare type-mismatch. #21 s7probe WALL-4 fix:
-- `checkHClauses` now types clause bodies via `synthSC` (computations) + an explicit
-- ret-shape/effect-free row check, not `synthSV` (which had no `.binopS` arm and rejected EVERY
-- non-atomic clause body for the wrong reason before this fix).
#guard (match checkProg
    "effect Net { fetch : Int -> Int } handle net.fetch(1) with Net as net { fetch(n) => raise n }"
  with
  | .error m => (m.splitOn "ret").length > 1 && (m.splitOn "ADR-0065").length > 1 && (m.splitOn "Q27").length > 1
  | .ok _    => false)

/-! ### #90 — row annotations (`T ! {…}`) could only name the four BUILT-IN effects (`throws`/
`state`/`stm`/`Div`) — `effNames`/`effOf` matched a fixed literal-string list, no `env.effects`
access, so a USER effect name in a row annotation silently resolved to nothing (defaulting the
declared bound to `∅`, ADR-0088 D2). Fixed the SAME way `Cap` was fixed (#84 gap 1): `resolveTyG`'s
`.tEff` arm now resolves EACH name (built-in OR user, via the new `resolveEffName` helper) into the
closed `Ty.tEffR` form (labels, not names) — `tyBoth`/`effOf` read it verbatim, no further env
needed.

**Also found + fixed while closing this out**: `curryBind` (the ascribed-lambda param-binding walk,
#84 gap 1's own construct) was missing a `.tEffR` case — its `.tEff _ t => curryBind Γ e t` arm
peeled `.tEff`, but by the time `curryBind` runs (AFTER `resolveTy`), a `.tEff` ascription has
ALREADY become `.tEffR` — the OLD arm never matched, so a row-annotated arrow (`Cap Net -> Int !
{Net}`) silently fell through `curryBith`'s catch-all (NO binding at all), losing the cap-typed
param's `Cap ℓ` binding the instant a row was attached. A non-exhaustive match with a catch-all, so
this compiled clean and only surfaced as a runtime "not a capability value" — exactly the kind of
gap the #85/#86 fixes were also closing (a binder silently missing, not a type error). -/

-- the row-annotation NAMES a user effect correctly: `Thunk (Cap Net -> Int ! {Net})` resolves,
-- types, and RUNS end to end (the #84 gap-1 pipeline that was `checkProg`-only until this fix).
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } let get2 = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) ) in handle (($get2) net) with Net as net { fetch(n) => n * 10 }"
    30

-- DIAGNOSTIC: an undeclared effect name in a row annotation fails loud, naming it — never a
-- silent empty-row default (the bug this issue closes).
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let f = ( {fun x => x} : Thunk (Int -> Int ! {Ghost}) ) in 0"
  with
  | .error m => (m.splitOn "Ghost").length > 1 && (m.splitOn "not a declared effect").length > 1
  | .ok _    => false)

-- mixed built-in + user names in ONE row annotation both resolve (`throws` AND `Net`).
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let f = ( {fun net => (net.fetch(1)) + (raise 1)} : Thunk (Cap Net -> Int ! {throws, Net}) ) in 0"
  with | .ok _ => true | .error _ => false)

-- the #84 gap-2 WRAPPER PATTERN (operator-ruled, no kernel change): a reusable INSTALLER function
-- (`fun body => handle (($body)(net)) with Net as net { … }`) composed with SEPARATELY-declared
-- effectful logic (`fun net => …`) — this is exactly what the row-annotation gap blocked (the
-- installer's own row-check pinned an empty bound before `logic`'s actual `{Net}` row was known).
-- Now types AND runs.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } let test = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n * 10 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in let logic = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) ) in ($test) logic"
    30

-- the PER-STAGE STORY itself: ONE logic function, TWO installer wrappers (`test`/`prod`, each
-- installing a DIFFERENT handler) — the same shared business logic means something different
-- under each stage. `30005 = 30*1000 + 5` (test's `n*10` vs prod's `n+1`, both over `1+2`).
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } let test = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n * 10 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in let prod = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n + 1 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in let logic = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) ) in (($test) logic) * 1000 + (($prod) logic)"
    30005

-- RUNTIME-SELECTING between two SEPARATELY-NAMED installer bindings works (they share ONE type,
-- so the `if`'s branches unify structurally — no row-polymorphic REUSE needed): the wrapper
-- pattern's "runtime-selectable" claim, confirmed live, not just narrated.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } let test = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n * 10 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in let prod = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n + 1 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in let logic = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) ) in let selector = (if 1 < 2 then test else prod) in ($selector) logic"
    30

-- DIAGNOSTIC / KNOWN GATE (#94, operator-ruled OUT of this lane's scope — a type-system-design
-- question, subeffecting vs full Rémy row polymorphism, not a local elaboration fix): reusing the
-- SAME installer BINDING against operands at genuinely DIFFERENT effect rows in one program still
-- fails — the pre-existing, already-`#guard`-pinned `unifyRow` "single shared row var" incompleteness
-- (`rowPolyDivSrc`'s "compose pure ∘ effectful" wall), confirmed here against the wrapper pattern
-- specifically so a future #94 fix has a repro that exercises #84's actual construct, not just
-- `rowPolyDivSrc`'s original `compose`.
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let test = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n * 10 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in let logic = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) ) in let pureBody = ( {fun net => 99} : Thunk (Cap Net -> Int) ) in (($test) logic) + (($test) pureBody)"
  with | .error _ => true | .ok _ => false)

/-! ### #85 — a NESTED binop in a handler clause body lost the clause's own binder. `elabHClauses`
(elaboration, runs BEFORE `checkHClauses`) never extended Γ with the clause's `x`/`#param` binders —
its own doc comment claimed "there is no per-clause binder to add at elaboration", which is false:
`elabS`'s `.binopS` arm A-normalizes NESTED operands via `anfSplit`, which runs `synthSC`/
`zonkInferC` on the SAME Γ immediately (elaboration-time). A clause body with only ATOMIC operands
(`n * 10`) never hits this (`anfSplit`'s `isValueSurf` short-circuit skips the lookup entirely) —
which is exactly why the bug stayed hidden until a NESTED binop (`n * 3 + 1`, `(n * 3) + 1`) forced
a real Γ lookup of `n` that failed. The WALL-3 throwaway-context class (`stage7-elab-probe.md`),
generalized to a THIRD occurrence. Fixed: `elabHClauses` now binds `x`/`#param` to fresh holes
before elaborating the clause body — mirroring `checkHClauses`'s later real-typed binding, same
ORDER, so both passes agree on de-Bruijn position. -/

-- the repro triple (all three ports of the reported bug, run-oracle checked): a single atomic
-- binop clause body (ALREADY worked, pinned so a future change can't silently re-break it), then
-- the two NESTED-binop shapes that failed before this fix — `n * 3 + 1` is the DST consumer's own
-- LCG shape (ctr-design.md §RE2), now running in the tested superset.
#guard runTypedYieldsInt 200
    "effect Net { pick : Int -> Int } handle net.pick(1) with Net as net { pick(n) => n * 10 }" 10
#guard runTypedYieldsInt 200
    "effect Net { pick : Int -> Int } handle net.pick(1) with Net as net { pick(n) => n * 3 + 1 }" 4
#guard runTypedYieldsInt 200
    "effect Net { pick : Int -> Int } handle net.pick(1) with Net as net { pick(n) => (n * 3) + 1 }" 4

-- #86 (SAME root cause as #85, a sibling trigger found independently by stranger-test round 3):
-- a MULTI-clause handler lost its clause binder even with BARE bodies, the moment a SECOND clause
-- existed — closed by the identical `elabHClauses` fix above (it binds `x`/`#param` for EVERY
-- clause, not just the one performed). Repro triple from #86's own report, all fixed:
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { a(n) => n, b(n) => n }" 5
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { a(n) => n + 1, b(n) => n + 1 }" 6
-- combined: multi-clause AND a nested binop in the performed clause (#85 ⊔ #86 in one program).
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { a(n) => n + n * 2, b(n) => n }" 15

/-! ### #87 — the parameter-carrying form's `init` becomes CLAUSE-NAMEABLE via the literal
identifier `param` (ADR-0095 D1's own worked example, `tick(u) => param + 1`). Landed by (1)
`pIdent` (Surface.lean) reserving `param` as a BINDER keyword — the SAME move as `resume`/`with`
— so no clause-arg/cap-binder/`let`/`fun` name can shadow it, and (2) `lowerHClauses`/
`checkHClauses`/`elabHClauses` pushing the LITERAL string `"param"` (not a `#`-sentinel) onto the
binder context, so `.var "param"` resolves via the SAME ordinary `lookup`/`Γ`-lookup every other
identifier uses. The reference's former "known v1 limitation" bullet is RETIRED by this slice
(`tools/gen-reference.py` updated accordingly). -/

-- ACCEPT: a bare `param` clause body resumes with the carried init value directly (no arithmetic).
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as net { fetch(x) => param }" 100
-- ACCEPT: `param` in a compound position, both operand orders (`x + param` / `param + x`) — the
-- ORIGINAL #87 report's own motivating shape (`fetch(x) => x + param`, README's stated intent).
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as net { fetch(x) => x + param }" 105
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as net { fetch(x) => param + x }" 105
-- ACCEPT: the `letC` CONTINUATION after the one-shot resume also observes the correct value —
-- mirrors `examples/handle-custom-resume`'s own `(5+100)+1` shape, now reading `param` for real
-- instead of hardcoding the literal `100` the way #87's report found.
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } handle (let r = net.fetch(5) in r + 1) with (R 100) as net { fetch(x) => x + param }" 106
-- ACCEPT: `param` inside a NESTED binop in the clause body (the #85 WALL-3 class, re-verified for
-- the param binder specifically — `anfSplit`'s throwaway inference must resolve `param` too, not
-- just the op-arg).
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as net { fetch(x) => x * 2 + param }" 110
-- NON-COLLISION: an identifier whose name merely SHADOWS-LOOKING (`paramX`, a distinct
-- identifier that is not the reserved word), bound INSIDE the handled expression (an ordinary
-- `let … in …`, not a decl-level binding), still resolves normally alongside `param` in the
-- clause body — the reservation is exact-string, not a prefix block.
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } handle (let paramX = 7 in net.fetch(paramX)) with (R 100) as net { fetch(x) => x + param }" 107
-- NON-COLLISION: a DIFFERENT effect's param-less handler, NESTED OUTSIDE a param-carrying one,
-- both actually PERFORMED and composed with `+` INSIDE the outer handled body — the binder push
-- is per-`handleCustomS` install, not a global name that could leak across handlers. Mirrors the
-- ADR-0095 corpus's OWN nested-`handle` composition shape (line ~5376 above: `handle (handle …
-- with … as … { … })`) — v1 composes multiple handlers by NESTING `handle`, not by chaining a
-- second `with` on one `handle`.
#guard runTypedYieldsInt 200
    "effect R { fetch : Int -> Int } effect Q { ping : Int -> Int } handle ((handle (net.fetch(5)) with (R 100) as net { fetch(x) => x + param }) + (q.ping(1))) with Q as q { ping(n) => n }" 106

-- REJECT: `param` cannot be used as a clause-arg binder — reserved at every binder position.
#guard assertParseErrorOrTypeError 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as net { fetch(param) => param + 1 }"
-- REJECT: `param` cannot be used as the `as h` capability binder either (same binder-reservation
-- mechanism, `pIdent` is the SINGLE site every binder position routes through).
#guard assertParseErrorOrTypeError 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as param { fetch(x) => x }"
-- REJECT: `param` cannot be bound by an ordinary `let` either — confirms the reservation is
-- BINDER-POSITION-wide (`pIdent`), not special-cased to the handler clause syntax only.
#guard assertParseErrorOrTypeError 200 "let param = 5 in param + 1"
-- REJECT: no param-WRITE surface exists — there is no `put`-like clause syntax for the carried
-- param in v1 (ADR-0092 D5 is explicitly deferred); attempting a plausible-looking write spelling
-- is simply an ordinary elaboration error (unbound `set`/assignment forms), not a silently-
-- accepted mutation. `param = …` inside a clause body is parsed as an EQUALITY/comparison
-- expression (`==`'s sibling), not an assignment — confirms v1 has no write surface to guard.
#guard assertParseErrorOrTypeError 200
    "effect R { fetch : Int -> Int } handle net.fetch(5) with (R 100) as net { fetch(x) => param.set(x) }"

/-! ### #84 gap 1 — caps-through-functions: `Cap Net` ascribes a function param to a named effect's
capability type, so shared effectful logic can be a function called under EACH stage's own `handle …
with`. `.dotPerform`'s typing arm (`.cap ℓ` case above) ALREADY dispatches correctly off ANY receiver
synthesizing `Cap ℓ` — the surface gap was the ASCRIPTION: `Cap Net` parses as an ordinary `tApp "Cap"
(.one (.tName "Net"))` (no new grammar — `Cap` rides the existing generic-application parser) and
`resolveTyG` now special-cases the head name `"Cap"`, resolving the argument against `env.effects`
into the closed `Ty.tCap ℓ` ↦ kernel `VT.cap ℓ` (mirrors the `tName`/`tApp` ADR-0069
"poison-until-resolved" precedent).

**Surface-syntax finding (v1, pre-existing, not this gap's doing):** `fun` has NO inline per-parameter
ascription (`fun (x : T) => …` does not parse — confirmed against `Bang/Frontend/Surface.lean`'s
keyword-rule table, `"fun" => … [.kw "fun", .refI, .kw "=>", .refE]`, `.refI` is a BARE identifier).
The v1 way to type a lambda's parameter is the OUTER ascription `(fun x => body : A -> B)` — `curryBind`
walks it. Reaching that path for a NAMED (`let`-bound) function additionally requires THUNKING (a bare
`let f = fun x => …` is documented+guarded as "not a returner" — see `#4698`'s own corpus a few
hundred lines up) — so the full v1 spelling is `let f = ({fun x => body} : Thunk (A -> B ! {ρ}))`.
`curryBind` + a new `elabS` arm (`.annotS (.thunk (.lam x b)) t`) were extended to peel this thunk
layer identically to the un-thunked case.

**Scope note, UPDATED (#90 landed as this lane's slice 2):** at the time this section first landed,
row annotations (`T ! {…}`) could not name a USER-declared effect — `effNames`/`effOf` were static,
matching only the four built-ins by literal string, no `env.effects` access. That gap is now CLOSED
(see the `#90` section above) — `Thunk (Cap Net -> Int ! {Net})` resolves, types, and RUNS. The
corpus immediately below still proves the RECEIVER-DISPATCH mechanism directly (mirroring
`checkPerformUnderCap`, ADR-0070's `#3` validation) as a minimal, row-independent witness; the
`#90` section above carries the FULL end-to-end pipeline test (parse→elaborate→check→lower→
`Source.eval`) this note used to describe as blocked. -/

-- the MECHANISM (#84's actual ask): a capability bound in Γ under a NAME other than the `as h`
-- binder — exactly what a function PARAMETER would be — still dispatches `.dotPerform` correctly.
-- `checkPerformUnderCap` seeds Γ directly (`(capName, Cap ℓ) :: []`, the SAME shape `curryBind`
-- produces for an ascribed `fun net => …`), so this is a direct proof that `.dotPerform`'s typing
-- arm is receiver-agnostic — it was ALREADY true before this lane; the surface gap was ascription.
#guard (match checkPerformUnderCap "effect Net { fetch : Int -> Int } 0" "Net" "net" "(net.fetch(1)) + (net.fetch(2))"
  with | .ok _ => true | .error _ => false)

-- the ASCRIPTION (`Cap Net` resolving through `resolveTyG`/`tCap`): an identity function over a cap
-- (`fun net => net`, thunked+ascribed the v1 way) types at `Thunk (Cap Net -> Cap Net)` — proves the
-- surface `Cap Net` → `tCap ℓ` → kernel `VT.cap ℓ` pipeline resolves correctly, independent of the
-- row-annotation gap (this function performs NOTHING, so its row bound is honestly `{}`).
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let get2 = ( {fun net => net} : Thunk (Cap Net -> Cap Net) ) in 0"
  with | .ok _ => true | .error _ => false)

-- COMBINED: the ascribed cap-typed identity, APPLIED under a `handle … with` (so the ascription, the
-- application, and the `as`-bound cap flowing IN as the argument all compose) — types end to end.
-- `.dotPerform`'s receiver must SYNTHESIZE AS A VALUE (`synthSV`, ADR-0095's own s7probe Finding 2);
-- `($get2)(net)` is a COMPUTATION (a force+application), so it is let-bound first (A-normalized by
-- hand) before `.fetch` performs on the resulting value — the same shape `anfSplit` produces
-- automatically for OTHER computation-position operands, applied here by hand at the call site.
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let get2 = ( {fun net => net} : Thunk (Cap Net -> Cap Net) ) in handle (let n2 = ($get2)(net) in n2.fetch(1)) with Net as net { fetch(n) => n * 10 }"
  with | .ok _ => true | .error _ => false)

-- DIAGNOSTIC: `Cap` naming an UNDECLARED effect fails loud, naming the bad effect — never a silent
-- fallthrough to `monoData`'s "unknown generic type" (which would be a confusing wrong-layer error).
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let get2 = ( {fun net => net} : Thunk (Cap Ghost -> Cap Ghost) ) in 0"
  with
  | .error m => (m.splitOn "Ghost").length > 1 && (m.splitOn "not a declared effect").length > 1
  | .ok _    => false)

-- DIAGNOSTIC: `Cap` applied to more/fewer than one argument fails loud, naming the constraint.
#guard (match checkProg "effect Net { fetch : Int -> Int } let get2 = ( {fun net => net} : Thunk (Cap -> Cap) ) in 0" with
  | .error m => (m.splitOn "Cap").length > 1
  | .ok _    => false)

-- DIAGNOSTIC: an UN-ascribed cap param used as a `.dotPerform` receiver still fails the ORIGINAL
-- "receiver is not a capability value" diagnostic (v1 has no cap inference — ascription is
-- REQUIRED) — confirms gap 1 closes via ascription, not a silent whole-program inference fallback.
#guard (match checkProg
    "effect Net { fetch : Int -> Int } let get2 = {fun net => net.fetch(1)} in handle (($get2) net) with Net as net { fetch(n) => n * 10 }"
  with
  | .error m => (m.splitOn "not a capability value").length > 1
  | .ok _    => false)

/-! ### `lawInstancesOf` (#60 seam) — enumerates real trait×impl law instances, body rendered
back to source text via `showSurf`, reusing the existing `vecLawProg`/`intOrdProg` corpus. -/

-- a single-law, single-impl program yields exactly one instance, params/name/rendered-body exact.
-- (the body is a nested let-chain, so it renders through the CANONICAL one-block form, issue #71.)
#guard (match lawInstancesOf (vecLawProg "0") with
        | .ok [("VecOps", "comm", ["a", "b"], body)] =>
            body == "let s = a + b; t = b + a in s == t"
        | _ => false)
-- a MULTI-LAW trait (IntOrd's `trans`, ADR-0068 conditional-law corpus) yields one instance per
-- law, ALL against the same impl — the trait×impl cross product, not just the first law.
#guard (match lawInstancesOf (intOrdProg "trans(a, b, c): a < b => b < c => a < c" "0") with
        | .ok [("IntOrd", "trans", ["a", "b", "c"], _)] => true
        | _ => false)
-- a program with NO impl of the trait yields NO instances (a law with nothing to check against
-- is correctly absent, not a phantom entry) — `checkLaws`'s own `!laws.isEmpty` gate mirrored.
#guard (match lawInstancesOf "trait Add { fn add(a, b) -> Self law comm(a, b): add a b == add b a } 0" with
        | .ok [] => true | _ => false)
-- a MULTI-TRAIT program (VecOps + IntOrd both present) discovers BOTH instances — confirming
-- discovery is program-wide, not scoped to "the first trait found".
#guard (match lawInstancesOf (vecOpsProg "comm(a, b): let s = a + b in (let t = b + a in s == t)"
    (intOrdProg "trans(a, b, c): a < b => b < c => a < c" "0")) with
        | .ok [("VecOps", "comm", _, _), ("IntOrd", "trans", _, _)] => true
        | _ => false)
-- a malformed program still fails LOUD through the same `parseProg` gate `checkLaws` uses.
#guard (match lawInstancesOf "let x = in" with | .error _ => true | .ok _ => false)

/-! ### Modules (ADR-0093) — the v1 ORACLE: `elaborate(import-merged) ≡ elaborate(hand-qualified)`.

Each case builds the merged `Prog` PROGRAMMATICALLY via `mergeModules` (mirroring how a real
multi-file program would resolve) and checks it evaluates to the SAME value `Source.eval` gives a
single hand-concatenated-and-qualified file — the differential guard the ADR names as v1's proof
obligation. `runTypedYieldsInt`-style: elaborate → check → lower → `Source.eval`. -/

/-- Run a merged `Prog` end to end (elaborate → check → lower → `Source.eval`), returning the
resulting `Int` (or `none` on any failure) — the module-merge analogue of the existing
`runYieldsInt`/`runTypedYieldsInt` corpus helpers, specialized to `Prog` (which already carries its
decl prelude, unlike the bare-`Surf` helpers). -/
def runMergedYieldsInt (fuel : Nat) (p : Prog) : Option Int :=
  match elabProg p with
  | .error _ => none
  | .ok (e, effects, _, _) =>
      match runInferC (synthSC [] e) effects with
      | .error _ => none
      | .ok _ =>
          match Bang.Surface.lower e with
          | .error _  => none
          | .ok c     => match Bang.Source.eval fuel c with
                          | .done (.vint n) => some n
                          | _ => none

-- a single `pub data` module + an entry file `import`-ing it (bare qualified access): the
-- MERGED program agrees with the hand-qualified single-file equivalent. A BARE `import` (no
-- `use`) does not hoist the ctor NAME into unqualified scope — the match PATTERN must spell the
-- qualified ctor (`geom_Mk`) too, exactly as the hand-qualified form would (D2 names `use`, not
-- bare `import`, as the hoisting mechanism).
#guard
  let modP : Prog := (Bang.Surface.parseProg "pub data Pair = Mk(Int, Int) 0").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg
    "import geom let p = geom.Mk(3, 4) in match (p : geom_Pair) { geom_Mk(a, b) -> a + b }").toOption.get!
  match mergeModules [("geom", modP)] entryP with
  | .error _ => false
  | .ok merged =>
      let handQualified : Prog := (Bang.Surface.parseProg
        "data geom_Pair = geom_Mk(Int, Int) let p = geom_Mk(3, 4) in match (p : geom_Pair) { geom_Mk(a, b) -> a + b }").toOption.get!
      runMergedYieldsInt 200 merged == some 7 && runMergedYieldsInt 200 merged == runMergedYieldsInt 200 handQualified

-- `use mod (Name)` hoists a `data` type's UNQUALIFIED constructor names too (D2 — "ctors travel
-- with their type"): a ctor is never a first-class VALUE in this language (ADR-0069 — a nonzero-
-- arity ctor referenced bare is a checked ARITY error, not an ordinary variable), so `use`'s hoist
-- for a ctor is realized by keeping it BARE in the merged decl list (`qualifyModule`'s `usedCtors`
-- exclusion), not a `let`-alias — the hand-qualified equivalent is simply `data geom_Pair =
-- Mk(Int, Int)` (qualified TYPE name, bare CTOR name), no extra `let` needed.
#guard
  let modP : Prog := (Bang.Surface.parseProg "pub data Pair = Mk(Int, Int) 0").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "use geom (Mk) match (Mk(3, 4) : geom_Pair) { Mk(a, b) -> a + b }").toOption.get!
  match mergeModules [("geom", modP)] entryP with
  | .error _ => false
  | .ok merged =>
      let handQualified : Prog := (Bang.Surface.parseProg
        "data geom_Pair = Mk(Int, Int) match (Mk(3, 4) : geom_Pair) { Mk(a, b) -> a + b }").toOption.get!
      runMergedYieldsInt 200 merged == some 7 && runMergedYieldsInt 200 merged == runMergedYieldsInt 200 handQualified

-- a PRIVATE decl (no `pub`) is unreachable via `use` — `mergeModules` fails LOUD, naming both the
-- decl and the module (D3).
#guard
  let modP : Prog := (Bang.Surface.parseProg "data Secret = Hidden(Int) 0").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "use hidden (Secret) 0").toOption.get!
  match mergeModules [("hidden", modP)] entryP with
  | .error m => (m.splitOn "private").length > 1 && (m.splitOn "hidden").length > 1 && (m.splitOn "Secret").length > 1
  | .ok _    => false

-- #73 fix: a PRIVATE decl is likewise unreachable via BARE QUALIFIED access (`bare.plain`) — the
-- enforcement hole the stranger-test found (`use`'s gate above didn't cover this shape; a bare
-- qualified reference silently resolved via `qualifyDotAccess`'s rewrite with no visibility check
-- at all). Same loud-error shape, same two names. `data Marker = M` terminates `plain`'s bound
-- expression before the trailing `0` — a bare literal FOLLOWED by another literal would otherwise
-- parse the `0` as an APPLICATION argument to the thunk (`{fun x => x+1} 0`), the same
-- value-followed-by-atom ambiguity the `let`-decl corpus above already works around.
#guard
  let modP : Prog := (Bang.Surface.parseProg "let plain = {fun x => x + 1} data Marker = M 0").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "import bare let main = $(bare.plain) 41").toOption.get!
  match mergeModules [("bare", modP)] entryP with
  | .error m => (m.splitOn "private").length > 1 && (m.splitOn "bare").length > 1 && (m.splitOn "plain").length > 1
  | .ok _    => false

-- companion positive: a `pub`-qualified BARE reference still merges + runs (D3 is "private, not
-- deleted", not "qualified access disabled") — proves the #73 fix didn't over-tighten the gate.
#guard
  let modP : Prog := (Bang.Surface.parseProg "pub let plain = {fun x => x + 1} data Marker = M 0").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "import bare $(bare.plain) 41").toOption.get!
  match mergeModules [("bare", modP)] entryP with
  | .error _ => false
  | .ok merged => runMergedYieldsInt 200 merged == some 42

-- a two-decl module (one pub, one private) merges correctly: the pub decl is reachable, the
-- private one still usable INTERNALLY by another decl of the SAME module (D3's "private, not
-- deleted" semantics) — `Helper` (private data) is referenced by `pub data Total`'s OWN payload
-- type, and the entry file only ever names `Total`. `use calc (Total)` naming the TYPE also hoists
-- its ctor `T` unqualified (D2 — "ctors travel with their type").
#guard
  let modP : Prog := (Bang.Surface.parseProg
    "data Helper = H(Int) pub data Total = T(Helper) 0").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "use calc (Total) match (T(calc_H(15)) : calc_Total) { T(h) -> match (h : calc_Helper) { calc_H(n) -> n } }").toOption.get!
  match mergeModules [("calc", modP)] entryP with
  | .error _ => false
  | .ok merged => runMergedYieldsInt 200 merged == some 15

-- REGRESSION (caught dogfooding the JSON split, `examples/json/Print.bang`): a TRANSITIVELY-
-- imported module's OWN `import`/qualified access must ALSO be rewritten, not just the entry
-- file's. `printer` (imported by the entry file) itself `import`s `boxmod` and references
-- `boxmod.wrap` — without `qualifyModuleOwnImports`, `printer`'s merged body still names the
-- UNQUALIFIED `boxmod`, an unbound-variable error once merged.
#guard
  let boxModP : Prog := (Bang.Surface.parseProg "pub data Box = Wrap(Int)").toOption.get!
  -- `printer`'s OWN bare qualified access to `boxmod.Wrap` (a VALUE-position ctor CALL, the exact
  -- shape `Print.bang`'s `Json.JNull` reference broke on) must be rewritten to `boxmod_Wrap` when
  -- `printer` itself is qualified — this is `qualifyModuleOwnImports`'s load-bearing case.
  let printerModP : Prog := (Bang.Surface.parseProg
    "import boxmod pub let build = {boxmod.Wrap 7}").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg
    "import printer match ($(printer.build) : boxmod_Box) { Wrap(n) -> n }").toOption.get!
  match mergeModules [("boxmod", boxModP), ("printer", printerModP)] entryP with
  | .error _ => false
  | .ok merged => runMergedYieldsInt 200 merged == some 7

/-! ### ADR-0093 D5 (operator ruling, 2026-07-09) — top-level `let`/`let rec` DECLS actually RUN.

`foldLetDecls`'s desugaring is proven end-to-end via `runTypedYieldsInt` (parse → elaborate →
type-check → lower → `Source.eval`), not just structurally (the `parsesTo`/round-trip guards above
only prove the AST shape) — this is the "does the ADR's own payoff actually happen" check. -/

-- a single top-level `let` decl, referenced by the trailing body. `data Marker` terminates the
-- bound expression before the body — a bare literal FOLLOWED by an identifier (`3 x`) would
-- otherwise parse as an APPLICATION (`(3) x`), the same ambiguity this whole corpus works around.
#guard runTypedYieldsInt 50 "let x = 3 data Marker = M x + 1" 4
-- MULTIPLE let decls, in order — a later one sees an earlier one (nested-let scoping). A second
-- `data` decl (a reserved keyword, never a valid application-argument atom) terminates `y`'s bound
-- expression before the trailing `x + y` — the same disambiguating role `data Marker` already
-- plays after `x`'s own binding.
#guard runTypedYieldsInt 50 "let x = 3 data Marker = M let y = x + 1 data Marker2 = M2 x + y" 7
-- a top-level `let rec` decl recurses, exactly like the expression-level `let rec` it desugars to
-- (ADR-0073's declared-row discipline carries over unchanged — same `Div` row). `data Marker`
-- terminates the bound expression before the trailing call (the SAME "value followed by another
-- atom parses as application" ambiguity this whole file's `let`-decl corpus works around).
-- `data Marker = M` (bare ctor, no payload — a payload-carrying `M(...)` would instead have its
-- FOLLOWING `(` swallowed as a ctor-payload TYPE, not a value application; the separator here must
-- be follow-by-a-KEYWORD, not follow-by-`(`) then `let call = …` isolates the recursive CALL as
-- its own decl, avoiding both this and the earlier literal-adjacency traps in one move.
#guard runTypedYieldsInt 200
  "let rec fact : Int -> Int ! {Div} = fun n => if n < 2 then 1 else n * ($fact (n - 1)) data Marker = M let call = ($fact) 5 data Marker2 = M2 call" 120
-- `let`/`let rec` decls compose with OTHER decl kinds (`data`), interleaved.
#guard runTypedYieldsInt 50
  "data Pair = Mk(Int, Int) let p = Mk(3, 4) match (p : Pair) { Mk(a, b) -> a + b }" 7
-- `main` is now literally a `let` decl (D5's whole point) — a script that DEFINES `main` and then
-- REFERENCES it in its trailing body runs exactly like any other `let`, proving the entry-point
-- form has no special elaboration path (D5: no main-only special case).
#guard runTypedYieldsInt 50 "let main = 42 data Marker = M main" 42
-- the OPTIONAL type ascription (D5 ruling point (c)) actually type-checks + runs — an `Int`-typed
-- `let x : Int = 3` is not just accepted structurally, the ascription round-trips through the
-- REAL type checker (a wrong ascription, e.g. `let x : Unit = 3`, would be caught below).
#guard runTypedYieldsInt 50 "let x : Int = 3 data Marker = M x + 1" 4
#guard (match Bang.TypeCheck.checkAndLower "let x : Unit = 3 data Marker = M x" with
        | .error _ => true | .ok _ => false)

-- `use`-hoisting a `pub let rec` plain function: the merged program's `use`-bound function
-- reference agrees with a hand-inlined `let double = lib_double in …` form (the SAME `use`-wrap
-- mechanism `mergeModules` already applies to a ctor covers a plain fn too, via the OPPOSITE
-- mechanism — a fn IS a first-class value, so it gets the `let`-alias a ctor cannot use).
#guard
  let modP : Prog := (Bang.Surface.parseProg "pub let rec double : Int -> Int = fun n => n + n").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "use lib (double) ($double) 21").toOption.get!
  match mergeModules [("lib", modP)] entryP with
  | .error _ => false
  | .ok merged => runMergedYieldsInt 200 merged == some 42

-- the SAME `use`-hoisted plain function, referenced from WITHIN another entry-file `letD` DECL
-- (not just the trailing body) — the exact `main.bang` shape D5 exists for: `let main = ($double)
-- 21` must see the `use`-hoisted `double` alias. Caught a REAL bug: the alias was originally
-- wrapped only around `p.body`, so a decl-scoped reference (like a `let main`) couldn't see it —
-- fixed by injecting the alias as a `letD` PREPENDED to the entry decls (outermost scope, so
-- `foldLetDecls` wraps everything after it, decls included).
#guard
  let modP : Prog := (Bang.Surface.parseProg "pub let rec double : Int -> Int = fun n => n + n").toOption.get!
  -- library mode (D5's third case) is NOT what makes `main` OBSERVABLE — its `body` is the
  -- unobservable `.lit 0` placeholder, so a decl-scoped test needs a REAL trailing body that
  -- references `main`, exactly like the earlier "main is a let decl" runtime guard does.
  let entryP : Prog := (Bang.Surface.parseProg "use lib (double) let main = ($double) 21 data Marker = M main").toOption.get!
  match mergeModules [("lib", modP)] entryP with
  | .error _ => false
  | .ok merged => runMergedYieldsInt 200 merged == some 42

-- #97: `use Mod (f)` hoisting a SELF-RECURSIVE `pub let rec` (unlike `double` above, which never
-- calls itself — this is the shape that actually exercised the bug: `qualifyDeclName` always
-- qualifies a `letRecD`'s OWN binding name to `lib_fac`, so the body's SELF-call must be qualified
-- too, or it stays "unbound variable fac" after the merge, even though `fac` was correctly
-- EXCLUDED from external-reference qualification (so the `use`-hoist alias itself stays sound).
-- The oracle: the SAME program hand-qualified (`let rec lib_fac = … $lib_fac … in ($lib_fac) 4`)
-- must agree with the merged `use`-hoisted form, and both compute the real factorial 4! = 24.
#guard
  let modP : Prog :=
    (Bang.Surface.parseProg
      "pub let rec fac : Int -> Int = fun n => if n < 1 then 1 else n * ($fac) (n - 1)").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "use lib (fac) ($fac) 4").toOption.get!
  let handQualified : Prog :=
    (Bang.Surface.parseProg
      "let rec lib_fac : Int -> Int = fun n => if n < 1 then 1 else n * ($lib_fac) (n - 1) in ($lib_fac) 4").toOption.get!
  match mergeModules [("lib", modP)] entryP with
  | .error _ => false
  | .ok merged =>
      runMergedYieldsInt 200 merged == some 24 &&
      runMergedYieldsInt 200 merged == runMergedYieldsInt 200 handQualified

-- negative control alongside the fix: a NON-`pub` `let rec` must stay blocked by the D3 privacy
-- gate exactly like a non-pub plain `let` — the rec-hoist fix touches only the QUALIFICATION of
-- an already-permitted `use`, never the visibility check that runs before it.
#guard
  let modP : Prog :=
    (Bang.Surface.parseProg
      "let rec secretFac : Int -> Int = fun n => if n < 1 then 1 else n * ($secretFac) (n - 1)").toOption.get!
  let entryP : Prog := (Bang.Surface.parseProg "use lib (secretFac) ($secretFac) 4").toOption.get!
  match mergeModules [("lib", modP)] entryP with
  | .error msg => (msg.splitOn "private").length > 1
  | .ok _       => false

/-! ### Clause-shape MATRIX (plan 002) — systematic coverage of the silently-missing-binder
family's predicted hiding places: nesting depth × op position × clause/handler configuration.
Each axis value appears in at least one ACCEPTED program; the matrix is a regression net for
context-threading (Γ / effects-table) in clause elaboration, not a semantics spec. -/

-- matrix: 1-op effect, bare clause body, atomic perform-site operand (baseline sanity cell).
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle net.fetch(3) with Net as net { fetch(n) => n }" 3

-- matrix: 1-op effect, nested-binop clause body depth 3, atomic perform-site operand.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle net.fetch(2) with Net as net { fetch(n) => ((n + 1) * 2) + (n * 3) }" 12

-- matrix: 1-op effect, `let … in` clause body, atomic perform-site operand.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle net.fetch(4) with Net as net { fetch(n) => let m = n * 2 in m + 1 }" 9

-- matrix: 1-op effect, immediately-applied-lambda clause body.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle net.fetch(5) with Net as net { fetch(n) => ($({fun m => m + 1})) n }" 6

-- matrix: 1-op effect, bare clause body, compound-LEFT perform-site operand.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle (net.fetch(1) + 2) + 3 with Net as net { fetch(n) => n * 10 }" 15

-- matrix: 1-op effect, bare clause body, compound-RIGHT perform-site operand.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle 3 + (2 + net.fetch(1)) with Net as net { fetch(n) => n * 10 }" 15

-- matrix: 1-op effect, bare clause body, perform-site in a `let` RHS.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle (let r = net.fetch(2) in r + 1) with Net as net { fetch(n) => n * 10 }" 21

-- matrix: 1-op effect, bare clause body, perform-site inside a forced thunk (plan-003 shape,
-- REPEATED here as an explicit matrix cell rather than only living in the plan-003 section).
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle (let t = {net.fetch(1)} in $t) + 0 with Net as net { fetch(n) => n * 10 }" 10

-- matrix: 2-op effect, decl order (a then b), both bodies bare, performed op is FIRST in decl order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { a(n) => n + 1, b(n) => n + 2 }" 6

-- matrix: 2-op effect, decl order (a then b), both bodies bare, performed op is SECOND in decl order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.b(5) with Two as two { a(n) => n + 1, b(n) => n + 2 }" 7

-- matrix: 2-op effect, REVERSE clause decl order (the #86 shape: handler clauses written `b` then
-- `a` while the effect declares `a` then `b`), performed op is the one declared FIRST but written
-- LAST in the handler.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { b(n) => n + 2, a(n) => n + 1 }" 6

-- matrix: 2-op effect, REVERSE clause decl order, performed op is the one declared SECOND but
-- written FIRST in the handler.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.b(5) with Two as two { b(n) => n + 2, a(n) => n + 1 }" 7

-- matrix: 2-op effect, reverse clause order, performed clause's body is a NESTED binop (compound),
-- the OTHER clause's body stays bare — the #85⊔#86 combination with an asymmetric body shape.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { b(n) => n, a(n) => (n + 1) * 2 }" 12

-- matrix: 2-op effect, decl order, one clause's body uses its param in a COMPOUND expression while
-- the other clause's body is BARE (the axis explicitly named in the plan) — performed op is the
-- COMPOUND one.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(5) with Two as two { a(n) => n * 2 + 1, b(n) => n }" 11

-- matrix: 2-op effect, decl order, compound/bare asymmetry as above but performed op is the BARE
-- one (proves the untouched compound clause's binder was still bound at elaboration time even
-- though it's never exercised by THIS run).
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.b(5) with Two as two { a(n) => n * 2 + 1, b(n) => n }" 5

-- matrix: 2-op effect, compound-LEFT perform-site operand, decl order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle (two.a(3) + 1) + two.b(2) with Two as two { a(n) => n * 10, b(n) => n * 100 }" 231

-- matrix: 2-op effect, compound-RIGHT perform-site operand, reverse clause order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle 1 + (two.a(3) + two.b(2)) with Two as two { b(n) => n * 100, a(n) => n * 10 }" 231

-- matrix: 2-op effect, perform-site in a `let` RHS, reverse clause order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle (let r = two.b(4) in r + two.a(1)) with Two as two { b(n) => n * 10, a(n) => n + 1 }" 42

-- matrix: 2-op effect, `let … in` clause body on the performed clause, decl order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(6) with Two as two { a(n) => let m = n + 1 in m * 2, b(n) => n }" 14

-- matrix: 3-op effect, decl order, all bodies bare, performed op is the MIDDLE one (the position
-- least like either endpoint).
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.b(5) with Three as three { a(n) => n + 1, b(n) => n + 2, c(n) => n + 3 }" 7

-- matrix: 3-op effect, REVERSE clause decl order (c, b, a), performed op is the one declared FIRST.
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.a(5) with Three as three { c(n) => n + 3, b(n) => n + 2, a(n) => n + 1 }" 6

-- matrix: 3-op effect, REVERSE clause decl order, performed op is the one declared LAST but written
-- FIRST in the handler.
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.c(5) with Three as three { c(n) => n + 3, b(n) => n + 2, a(n) => n + 1 }" 8

-- matrix: 3-op effect, SCRAMBLED clause decl order (b, a, c — neither forward nor pure reverse),
-- performed op is the MIDDLE-declared one, body is a nested binop.
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.b(4) with Three as three { b(n) => (n + 1) * 2, a(n) => n, c(n) => n }" 10

-- matrix: 3-op effect, all THREE ops performed and combined in one binop chain, decl order handler
-- — exercises every clause's binder in a single program.
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.a(1) + three.b(2) + three.c(3) with Three as three { a(n) => n * 10, b(n) => n * 100, c(n) => n * 1000 }" 3210

-- matrix: 3-op effect, all three ops performed, REVERSE clause decl order.
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.a(1) + three.b(2) + three.c(3) with Three as three { c(n) => n * 1000, b(n) => n * 100, a(n) => n * 10 }" 3210

-- matrix: 3-op effect, nested-binop clause body depth 3 on the performed clause, scrambled decl
-- order handler.
#guard runTypedYieldsInt 200
    "effect Three { a : Int -> Int, b : Int -> Int, c : Int -> Int } handle three.c(2) with Three as three { b(n) => n, c(n) => ((n + 1) * 2) + (n * 3) , a(n) => n }" 12

-- N/A (matrix axis dropped, confirmed against the parser, not assumed): the plan's "2-arg op
-- (`fetch : Int -> Int -> Int`) with the param used at each position" axis. `pHClause`
-- (`Bang/Frontend/Surface.lean` ~1432-1447) parses EXACTLY one `(x)` per clause — v1's
-- `EffectInfo` op sigs are documented 0/1-ary only ("D3's curry-desugar is future work"), and
-- `pHClause`'s own doc comment says so explicitly: "no declared op takes 2 args currently".
-- A 2-arg op clause `fetch(x, y) => …` is not v1-expressible syntax, so this axis cannot produce
-- a `#guard` (would be a parse-error cell, not a semantics cell) — replaced below with two
-- additional cells from the already-valid axes (nesting × perform-site position) to keep the
-- matrix's coverage intent (≥25 cells) without a syntactically-doomed guard.

-- matrix: 1-op effect, clause body is a nested binop AND uses `let … in`, atomic perform-site —
-- combines the "nested binop depth 3" and "let-body" body-shape axes in one clause.
#guard runTypedYieldsInt 200
    "effect Net { fetch : Int -> Int } handle net.fetch(3) with Net as net { fetch(n) => let m = n + 1 in (m * 2) + (n * 3) }" 17

-- matrix: 2-op effect, immediately-applied-lambda clause body on the performed clause, reverse
-- clause decl order.
#guard runTypedYieldsInt 200
    "effect Two { a : Int -> Int, b : Int -> Int } handle two.a(3) with Two as two { b(n) => n, a(n) => ($({fun m => m * 2})) n }" 6

-- final count: 28 new #guards in this matrix subsection (excludes the plan-003/#85/#86 guards it
-- deliberately re-exercises in NEW combinations rather than duplicates verbatim). The multi-arg-op
-- axis is documented N/A above (not v1-expressible), per the plan's own contingency.

end Bang.TypeCheck

