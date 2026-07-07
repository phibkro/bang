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
open Bang.EffectRow (EffRow Label)

/-- The concrete instantiation the surface uses: effect rows are `Finset Label`, grades are QTT. -/
abbrev VT := VTy EffRow QTT
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

mutual
/-- A value inference type: a kernel `VTy` shape plus unification `vhole`s. `tvar` still carries BOTH
the μ-recursion vars (0-2) and the ∀-scheme RIGIDs (`rigidBase + i`); only unification holes moved to
the proper `vhole` constructor. -/
inductive IVTy where
  | int   : IVTy
  | unit  : IVTy
  | sum   : IVTy → IVTy → IVTy
  | prod  : IVTy → IVTy → IVTy
  | U     : EffRow → ICTy → IVTy
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
  | .U φ b    => .U φ (embC b)
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
  | .U φ b    => do return .U φ (← extractC b)
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
  arity : Nat := 0
  body  : IVTy

instance : Coe IVTy Scheme := ⟨fun v => ⟨0, v⟩⟩

abbrev NCtx := List (String × Scheme)   -- named typing context, innermost first (= `List.lookup` keys)

/-- Interpret a surface `Ty` into BOTH its value reading (`.1`) and computation reading (`.2`) in one
structural pass — `tArr`/`tThunk` are computations (`arr`/the wrapped `F`); a non-arrow as a value is
itself, as a computation a returner `F` of that value type. One recursion (no mutual block, no
termination obligation). -/
def tyBoth : Ty → VT × CT
  | .tInt      => let V : VT := .int;              (V, .F .omega V)
  | .tUnit     => let V : VT := .unit;             (V, .F .omega V)
  | .tSum  a b => let V : VT := .sum  (tyBoth a).1 (tyBoth b).1; (V, .F .omega V)
  | .tProd a b => let V : VT := .prod (tyBoth a).1 (tyBoth b).1; (V, .F .omega V)
  | .tThunk t  => let V : VT := .U ⊥ (tyBoth t).2; (V, .F .omega V)
  | .tArr  a b => let f : CT := .arr .omega (tyBoth a).1 (tyBoth b).2; (.U ⊥ f, f)  -- fn VALUE = thunked arrow
  | .tEff  _ t => tyBoth t        -- effect annotation is checker-level (effOf); dropped from the kernel type
  | .tSelf     => let V : VT := .tvar 999; (V, .F .omega V)  -- POISON: `buildEnv` substitutes Self before
                                  -- any tyBoth; a leaked Self surfaces as `#999`, never unifies
  | .tName _   => let V : VT := .tvar 998; (V, .F .omega V)  -- POISON: `resolveTy` closes names before
                                  -- any tyBoth; a leaked name surfaces as `#998` (ADR-0069)
  | .tMu b     => let V : VT := .mu (tyBoth b).1;  (V, .F .omega V)
  | .tVar n    => let V : VT := .tvar n;           (V, .F .omega V)
@[inline] def vtyOf (t : Ty) : VT := (tyBoth t).1
@[inline] def ctyOf (t : Ty) : CT := (tyBoth t).2

/-- Map effect NAMES to the kernel label row (the inverse of `effName`). -/
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

/-- The unification state: a fresh-variable counter + the value-hole and comp-hole substitutions. -/
structure USt where
  fresh  : Nat := 0
  subst  : List (Nat × IVTy) := []
  csubst : List (Nat × ICTy) := []

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
    | .U φ b    => return .U φ (← zonkC fu b)
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
    | .U φ B, .U φ' B'         => if φ == φ' then unifyC fu B B' else throw "thunk row mismatch"
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
  for (_, s) in Γ do
    envHoles := envHoles ++ freeHolesV (← zonkV bigFuel s.body)
  let genHoles := ((freeHolesV Az).filter (fun m => !envHoles.contains m)).eraseDups
  return ⟨genHoles.length, abstractV genHoles Az⟩

/-- INSTANTIATE a scheme with a fresh hole per quantified variable (independent holes per use-site). -/
def instantiate (s : Scheme) : Infer IVTy := do
  let mut insts : List IVTy := []
  for _ in List.range s.arity do insts := insts ++ [← freshHole]
  return instV insts s.body

/-- Look a name up and instantiate its scheme (the `var` rule). -/
def lookupInst (Γ : NCtx) (x : String) : Infer IVTy := do
  match Γ.lookup x with
  | some s => instantiate s
  | none   => throw s!"unbound variable {x}"

/-- μ-unroll an `IVTy` μ-BODY (concrete data types only — resolved `data` decls are hole-free). Extract
to the kernel, apply the kernel's own `VTy.unrollMu`, re-embed. -/
def unrollI (A : IVTy) : Infer IVTy := do
  match extractV A with
  | .ok Ak    => return embV (VTy.unrollMu Ak)
  | .error e  => throw s!"unrollMu on a non-concrete μ: {e}"

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
/-- As `runInferV`, for a computation type + its row. -/
def runInferC (act : Infer (ICTy × EffRow)) : Except String (CT × EffRow) := do
  let (Bz, φ) ← (do let (B, φ) ← act; return (← zonkC bigFuel B, φ)).run' {}
  return (← extractC Bz, φ)
/-- As `runInferC`, but keep the ZONKED `ICTy` (no extraction) — for the elaborator's chole-tolerant
returner probes (`anfSplit`, `let`-RHS), which must inspect a higher-order result WITHOUT failing on a
still-open computation hole. -/
def zonkInferC (act : Infer (ICTy × EffRow)) : Except String (ICTy × EffRow) :=
  (do let (B, φ) ← act; return (← zonkC bigFuel B, φ)).run' {}


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

-- Termination: the rank (synth = 0, check = 1) breaks the `check t → synth t` subsumption tie, as
-- in the spike; every other call is on a structural subterm of the `Surf`.
mutual
/-- Synthesize the value type of a `Surf` read as a VALUE. -/
def synthSV (Γ : NCtx) (e : Surf) : Infer IVTy :=
  match e with
  | .lit _     => return .int
  | .var x     => lookupInst Γ x                       -- HM: instantiate the scheme with fresh holes
  | .thunk b   => do let (B, φ) ← synthSC Γ b; return .U φ B
  | .pairS a b => do return .prod (← synthSV Γ a) (← synthSV Γ b)
  | .unitS     => return .unit
  | .annotS b t => do let A := embV (vtyOf t); let _ ← checkSV Γ b A; return A
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
  | .thunk b,   .U φ B    => do
      let φ' ← checkSC Γ b B
      if φ' ⊆ φ then return () else throw "thunk body effect exceeds the declared bound"
  | .annotS b t, expected => do
      let A := embV (vtyOf t)
      let _ ← checkSV Γ b A
      unifyV bigFuel A expected                         -- HM subsumption (was structural `A = expected`)
  | e, expected => do
      let A ← synthSV Γ e
      unifyV bigFuel A expected                         -- HM subsumption (was structural `A = expected`)
  termination_by (sizeOf e, 2)

/-- Synthesize the computation type + effect row of a `Surf` read as a COMPUTATION. -/
def synthSC (Γ : NCtx) (e : Surf) : Infer (ICTy × EffRow) :=
  match e with
  | .lit _   => return (.F .omega .int, ⊥)
  | .var x   => do return (.F .omega (← lookupInst Γ x), ⊥)   -- `ret` of the instantiated scheme
  | .thunk b => do let (B, φ) ← synthSC Γ b; return (.F .omega (.U φ B), ⊥)
  | .pairS a b => do return (.F .omega (.prod (← synthSV Γ a) (← synthSV Γ b)), ⊥)  -- value ⇒ ret
  -- force: the thunk's type must be `U φ B`. HM (bite-0b): a value HOLE here is an unknown thunk — the
  -- higher-order case (`$g` where `g` is a bare param). Unify it with `U ⊥ (chole)` (a fresh computation
  -- hole) and return the chole: now the result IS a computation type the checker can carry (bite-0
  -- threw "annotate" here — `CTy` had no hole). The `⊥` row is the bite-0b limitation (row-poly is item
  -- 3): `compose` composes PURE-thunk functions; an effectful thunk hole would need a row var.
  | .force b => do
      match (← resolve bigFuel (← synthSV Γ b)) with
      | .U φ B    => return (B, φ)
      | .vhole n  => do let C ← freshCHole; assign n (.U ⊥ C); return (C, ⊥)
      | _         => throw "force: not a thunk"
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
      let sch ← if isValueSurf e then generalize Γ A else pure (⟨0, A⟩ : Scheme)
      let (B, φ₂) ← synthSC ((x, sch) :: Γ) b
      return (B, φ₁ ⊔ φ₂)
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
      | _          => throw "app: callee is not a function"
  | .binopS op a b => do
      let _ ← checkSV Γ a .int; let _ ← checkSV Γ b .int
      return (.F .omega (binopResTy op), ⊥)
  | .ifS c t e => do
      let _ ← checkSV Γ c boolTy
      let (C, φ₁) ← synthSC Γ t
      let φ₂ ← checkSC Γ e C
      return (C, φ₁ ⊔ φ₂)
  | .matchS s xl el xr er => do match (← resolve bigFuel (← synthSV Γ s)) with
      | .sum A B => do
          let (C, φ₁) ← synthSC ((xl, A) :: Γ) el
          let φ₂ ← checkSC ((xr, B) :: Γ) er C
          return (C, φ₁ ⊔ φ₂)
      | _ => throw "match: scrutinee is not a sum"
  | .splitS a b p body => do match (← resolve bigFuel (← synthSV Γ p)) with
      | .prod A B => synthSC ((b, B) :: (a, A) :: Γ) body
      | _ => throw "split: scrutinee is not a product"
  | .annotS b t => do
      let C := embC (ctyOf t)
      let φ ← checkSC Γ b C
      match effOf t with                              -- declared row (if any) is an upper bound — ④b
      | some ρ => if φ ⊆ ρ then return (C, φ) else throw "inferred effect exceeds the declared row"
      | none   => return (C, φ)
  -- ── effects (ADR-0066 ④): each op ADDS its label to the row; handlers DISCHARGE it (`Finset.erase`).
  -- v1 simplification (marked): operation payload/result types are fixed to the surface convention
  -- (state cell + TVar contents + exn payload are `Int`, ADR-0030) — no payload-type threading yet.
  | .raise e     => do let _ ← checkSV Γ e .int; return (.F .omega .int, {exnLabel})    -- result = payload (v1)
  | .handle e    => do let (B, φ) ← synthSC Γ e; return (B, φ.erase exnLabel)            -- discharge throws
  | .getS        => return (.F .omega .int, {stateLabel})
  | .putS e      => do let _ ← checkSV Γ e .int; return (.F .omega .unit, {stateLabel})
  | .stateS e0 e => do let _ ← checkSV Γ e0 .int; let (B, φ) ← synthSC Γ e; return (B, φ.erase stateLabel)
  | .atomS e     => do let (B, φ) ← synthSC Γ e; return (B, φ.erase stmLabel)            -- discharge stm
  | .newS e      => do let _ ← checkSV Γ e .int; return (.F .omega .int, {stmLabel})     -- TVar ref = Int (ADR-0030)
  | .readS e     => do let _ ← checkSV Γ e .int; return (.F .omega .int, {stmLabel})
  | .writeS r w  => do let _ ← checkSV Γ r .int; let _ ← checkSV Γ w .int; return (.F .omega .unit, {stmLabel})
  -- ── ADR-0069 (data) ──
  | .unitS     => return (.F .omega .unit, ⊥)
  | .unfoldS b => do match (← resolve bigFuel (← synthSV Γ b)) with   -- T_Unfold mirrored: F 1 (A[μ.A/0]), pure
                     | .mu A => do let U ← unrollI A; return (.F 1 U, ⊥)
                     | _     => throw "unfold: not a μ value"
  | .matchD .. => throw "named match is elaborated away on the typed path — reaching the checker means the data env lacked its constructors (ADR-0069)"
  | .letRecS .. => throw "let rec is desugared away by the elaborator — reaching the checker means elabProg didn't run (ADR-0073)"
  | .divMark e => do let (B, φ) ← synthSC Γ e; return (B, insert divLabel φ)  -- #46: mark the row divergent
  -- ── ADR-0070 (named capabilities) ──
  | .withCapS kind init name body => do
      match capKindLabel kind with
      | none => throw s!"with: unknown handler kind '{kind}'"
      | some ℓ => do
          if kind = "state" then let _ ← checkSV Γ init .int   -- the initial cell value is Int
          let capTy : IVTy := .cap ℓ
          let (B, φ) ← synthSC ((name, capTy) :: Γ) body   -- name : Cap ℓ in scope
          return (B, φ.erase ℓ)                                 -- the handler DISCHARGES ℓ
  | .dotPerform recv op args => do
      match (← resolve bigFuel (← synthSV Γ recv)) with
      | .cap ℓ =>
          match capOpSig op with
          | none => throw s!"unknown capability op '{op}'"
          | some (ℓ', argTys, resTy) =>
              if ℓ != ℓ' then throw s!"cap op '{op}' expects a different capability (label mismatch)"
              else
                -- match SurfArgs to the op's arity: each arg is a syntactic subterm (termination).
                match args, argTys with
                | .none,    []       => return (.F .omega (embV resTy), {ℓ})
                | .one a,   [t]      => do let _ ← checkSV Γ a (embV t); return (.F .omega (embV resTy), {ℓ})
                | .two a b, [t1, t2] => do let _ ← checkSV Γ a (embV t1); let _ ← checkSV Γ b (embV t2)
                                          return (.F .omega (embV resTy), {ℓ})
                | _, _ => throw s!"cap op '{op}' expects {argTys.length} argument(s)"
      | _ => throw s!"cap op '{op}': receiver is not a capability value (Cap ℓ)"
  -- HM (#53): a bare anonymous injection in COMPUTATION position lowers to `ret (inj v)` — a value ⇒
  -- ret, with a fresh hole for the unfilled variant (mirrors the `synthSV` arm and `pairS` here).
  -- `fold` still needs an expected μ type (its unrolling is not a hole the unifier can invent).
  | .inlS p => do return (.F .omega (.sum (← synthSV Γ p) (← freshHole)), ⊥)
  | .inrS p => do return (.F .omega (.sum (← freshHole) (← synthSV Γ p)), ⊥)
  | .foldS _ => throw "fold needs an expected μ type — annotate (ctor elaboration provides it)"
  -- NO catch-all: synthSC now ENUMERATES every Surf constructor, so a NEW feature fails to compile
  -- here until it is typed — pipeline-completeness by construction (the operator's enforcement ask).
  termination_by (sizeOf e, 1)

/-- Check a `Surf` read as a COMPUTATION against an expected computation type. -/
def checkSC (Γ : NCtx) (e : Surf) (expected : ICTy) : Infer EffRow :=
  match e, expected with
  | .lam x b,   .arr _ A B => checkSC ((x, A) :: Γ) b B
  -- value-constructors in computation position lower to `ret v` — check the value against `A` of `F A`.
  | .inlS b,    .F _ (.sum A B)  => do let _ ← checkSV Γ (.inlS b) (.sum A B); return ⊥
  | .inrS b,    .F _ (.sum A B)  => do let _ ← checkSV Γ (.inrS b) (.sum A B); return ⊥
  | .pairS a b, .F _ (.prod A B) => do let _ ← checkSV Γ (.pairS a b) (.prod A B); return ⊥
  | .foldS b,   .F _ (.mu A)     => do let _ ← checkSV Γ (.foldS b) (.mu A); return ⊥
  | .thunk t,   .F _ (.U φ B)    => do let _ ← checkSV Γ (.thunk t) (.U φ B); return ⊥
  | .annotS b t, expected => do
      let C := embC (ctyOf t)
      let φ ← checkSC Γ b C
      let _ ← unifyC bigFuel C expected                 -- HM subsumption (was structural `C ≠ expected`)
      match effOf t with
        | some ρ => if φ ⊆ ρ then return φ else throw "inferred effect exceeds the declared row"
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
This is what makes effect-typed signatures legible: you run the checker and SEE `Int -> Int ! {throws}`. -/

/-- Map an effect label back to its surface name (the inverse of the lowering's `exnLabel`/… choice). -/
def effName (ℓ : Label) : String :=
  if ℓ = exnLabel then "throws" else if ℓ = stateLabel then "state"
  else if ℓ = stmLabel then "stm" else if ℓ = divLabel then "Div" else s!"e{ℓ}"

/-- Render an effect row as `throws, state` by decidable membership of the known labels (computable —
`Finset.toList` is noncomputable; the surface has exactly these four labels: throws·state·stm·Div). -/
def showRow (φ : EffRow) : String :=
  String.intercalate ", " <|
    (if exnLabel ∈ φ then [effName exnLabel] else []) ++
    (if stateLabel ∈ φ then [effName stateLabel] else []) ++
    (if stmLabel ∈ φ then [effName stmLabel] else []) ++
    (if divLabel ∈ φ then [effName divLabel] else [])

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

/-- Render a computation's full type: the value/arrow shape plus its effect row as a `! {…}` suffix. -/
def showType (B : CT) (φ : EffRow) : String :=
  let r := showRow φ
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
  | .tVar n    => .tVar n
  | .tMu b     => .tMu   (substSelf target b)
  | .tArr a b  => .tArr  (substSelf target a) (substSelf target b)
  | .tSum a b  => .tSum  (substSelf target a) (substSelf target b)
  | .tProd a b => .tProd (substSelf target a) (substSelf target b)
  | .tThunk t  => .tThunk (substSelf target t)
  | .tEff ns t => .tEff ns (substSelf target t)

/-- One resolvable instance op: the resolution key (`opName` × structural `target`) plus what
the elaborated call site needs. `body` is PRE-ELABORATED at env build (ADR-0069 upgraded
piece-2's raw splice: nested ctors and earlier ops inside an impl body now resolve). -/
structure Inst where
  opName   : String
  target   : VT       -- the structural resolution key (ADR-0068 decision 2)
  targetTy : Ty       -- the impl's declared target, for the elaborated annotation
  retTy    : Ty       -- the trait sig's ret type, Self-substituted
  params   : List String
  body     : Surf

abbrev InstEnv := List Inst

/-- One data constructor's elaboration record (ADR-0069). -/
structure CtorInfo where
  dataName      : String
  idx           : Nat        -- position in decl order (the sum injection)
  total         : Nat        -- constructor count (right-nested sum shape)
  arity         : Nat        -- payload arity (≤ 2 in v1)
  payloadClosed : List Ty    -- payload types, the data's own name resolved to the CLOSED μ
  dataTy        : Ty         -- the closed μ type (`tMu body`)

/-- The full elaboration environment: instance ops + data constructors + type aliases. -/
structure ElabEnv where
  insts   : InstEnv
  ctors   : List (String × CtorInfo)
  aliases : List (String × Ty)

/-- Close a type over the alias env: every `tName` resolves or fail-louds. Enumerated. -/
def resolveTy (aliases : List (String × Ty)) : Ty → Except String Ty
  | .tName n   => match aliases.lookup n with
                  | some t => .ok t
                  | none   => .error s!"unknown type name '{n}'"
  | .tInt      => .ok .tInt
  | .tUnit     => .ok .tUnit
  | .tSelf     => .ok .tSelf
  | .tVar n    => .ok (.tVar n)
  | .tMu b     => do return .tMu   (← resolveTy aliases b)
  | .tArr a b  => do return .tArr  (← resolveTy aliases a) (← resolveTy aliases b)
  | .tSum a b  => do return .tSum  (← resolveTy aliases a) (← resolveTy aliases b)
  | .tProd a b => do return .tProd (← resolveTy aliases a) (← resolveTy aliases b)
  | .tThunk t  => do return .tThunk (← resolveTy aliases t)
  | .tEff ns t => do return .tEff ns (← resolveTy aliases t)

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

/-- Inject a payload at ctor position `i` of `n` (right-nested sum; `n = 1` ⇒ no sum wrapper). -/
def injSum : Nat → Nat → Surf → Surf
  | 0,     1, p => p
  | 0,     _, p => .inlS p
  | i + 1, n, p => .inrS (injSum i (n - 1) p)

/-- The elaborated ctor intro: the injected payload, μ-folded, ANNOTATED at the data type —
check-mode then drives T_Fold via `unrollMu`; no new typing rule. -/
def ctorIntro (ci : CtorInfo) (payload : Surf) : Surf :=
  .annotS (.foldS (injSum ci.idx ci.total payload)) ci.dataTy

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

mutual
/-- **The #47 structural-termination certifier — SOUND, deliberately incomplete.** `structOK name
matchable subterms body` = `true` iff EVERY occurrence of the recursive function `name` in `body` is a
call `($name) v` whose argument `v` is a STRICT SUBTERM of the recursion parameter — a field pattern-
bound by `match`/`let (..)`-ing the parameter (or an already-established subterm). `matchable` tracks
the parameter + its subterms (things you may match to descend); `subterms` tracks the strict subterms
(the only legal recursive-call arguments). Well-founded by the FINITE DEPTH of a `data` value: each
call strips ≥1 constructor, so no infinite descent.

CONSERVATIVE BY CONSTRUCTION — the default is `false` (⟹ the caller keeps `Div`). Anything not
manifestly structural is rejected: a bare `name`, a `$name` not applied to a subterm, a call on a
non-subterm (`($f) x`, `($f)(n-1)` on `Int` — ℤ has no data-floor, ADR-0067), `name` passed as a value,
or a match on a NON-parameter value (its fields are not subterms of the parameter). Sound under
shadowing (every binder shadows via `shadowAdd`). Missing a terminating function (→ `Div`) is fine;
certifying a diverging one is a SOUNDNESS BUG, so we never guess.

DEFERRED (conservatively `Div`, each needs more than this syntactic check): multi-argument / curried
recursion (`letRecRow` rejects a nested `fun`), lexicographic descent, well-founded numeric MEASURES
(needs a `Nat`/floor type — ADR-0067's ℤ is unbounded), and subterm-aliasing through `let`. -/
def structOK (name : String) (matchable subterms : List String) : Surf → Bool
  | .lit _          => true
  | .unitS          => true
  | .getS           => true
  | .var g          => g != name                    -- a bare `name` (used as a value) is non-structural
  | .thunk e        => structOK name matchable subterms e
  | .force (.var g) => g != name                    -- `$name` NOT immediately applied to a subterm → reject
  | .force e        => structOK name matchable subterms e
  | .app (.force (.var g)) a =>
      if g == name then
        match a with | .var v => subterms.contains v | _ => false   -- structural iff arg is a subterm var
      else structOK name matchable subterms a                       -- callee `$g` (g ≠ name) is name-free
  | .app f a        => structOK name matchable subterms f && structOK name matchable subterms a
  -- Binders that RE-BIND the recursion name shadow it — `$name` there is NOT the recursion, so the
  -- structural argument tells us nothing about it. REFUSE to certify (soundness > completeness).
  | .lett v e b     => v != name && structOK name matchable subterms e &&
                       structOK name (shadowAdd [v] false matchable) (shadowAdd [v] false subterms) b
  | .lam v b        => v != name &&
                       structOK name (shadowAdd [v] false matchable) (shadowAdd [v] false subterms) b
  | .ifS c t e      => structOK name matchable subterms c && structOK name matchable subterms t
                       && structOK name matchable subterms e
  | .binopS _ a b   => structOK name matchable subterms a && structOK name matchable subterms b
  | .pairS a b      => structOK name matchable subterms a && structOK name matchable subterms b
  | .inlS e         => structOK name matchable subterms e
  | .inrS e         => structOK name matchable subterms e
  | .foldS e        => structOK name matchable subterms e
  | .unfoldS e      => structOK name matchable subterms e
  | .raise e        => structOK name matchable subterms e
  | .handle e       => structOK name matchable subterms e
  | .putS e         => structOK name matchable subterms e
  | .stateS a b     => structOK name matchable subterms a && structOK name matchable subterms b
  | .atomS e        => structOK name matchable subterms e
  | .newS e         => structOK name matchable subterms e
  | .readS e        => structOK name matchable subterms e
  | .writeS a b     => structOK name matchable subterms a && structOK name matchable subterms b
  | .annotS e _     => structOK name matchable subterms e
  | .divMark e      => structOK name matchable subterms e
  | .matchS s xl el xr er =>
      xl != name && xr != name &&
      let sm := scrutMatch matchable s
      structOK name matchable subterms s &&
      structOK name (shadowAdd [xl] sm matchable) (shadowAdd [xl] sm subterms) el &&
      structOK name (shadowAdd [xr] sm matchable) (shadowAdd [xr] sm subterms) er
  | .splitS a b p body =>
      a != name && b != name &&
      let sm := scrutMatch matchable p
      structOK name matchable subterms p &&
      structOK name (shadowAdd [a, b] sm matchable) (shadowAdd [a, b] sm subterms) body
  | .matchD s arms  =>
      structOK name matchable subterms s && structOKArms name matchable subterms (scrutMatch matchable s) arms
  | .withCapS _ init v body =>
      v != name && structOK name matchable subterms init &&
      structOK name (shadowAdd [v] false matchable) (shadowAdd [v] false subterms) body
  | .dotPerform recv _ args =>
      structOK name matchable subterms recv && structOKArgs name matchable subterms args
  | .letRecS gname _ fb bd =>                         -- nested let rec: a re-bound `gname` shadows our name
      gname != name && structOK name matchable subterms fb && structOK name matchable subterms bd
/-- Per-arm structural check: a matchable scrutinee (`sm`) makes each arm's pattern binders strict
subterms of the parameter; a non-matchable one only shadows them. -/
def structOKArms (name : String) (matchable subterms : List String) (sm : Bool) : DArms → Bool
  | .nil => true
  | .cons _ bs b r =>
      !bs.contains name &&                            -- an arm binder shadowing the recursion name → reject
      structOK name (shadowAdd bs sm matchable) (shadowAdd bs sm subterms) b &&
      structOKArms name matchable subterms sm r
def structOKArgs (name : String) (matchable subterms : List String) : SurfArgs → Bool
  | .none    => true
  | .one a   => structOK name matchable subterms a
  | .two a b => structOK name matchable subterms a && structOK name matchable subterms b
end

/-- The effect row a `let rec` CALL-SITE carries (#46/#47, ADR-0073 §2). Recursion may not terminate —
the ADR-0028 total/`Div` seam, made type-visible — UNLESS the #47 structural check (`structOK`) proves
every recursive call descends on a strict `data` subterm, in which case the function is in the TOTAL
fragment and carries `⊥` (no `Div`). SOUND, incomplete: an uncertified function conservatively keeps
`{divLabel}` (it still RUNS, fuel-bounded — the `Div` escape hatch is what lets the check be aggressive
without a rejection tax). v1 certifies SINGLE-parameter DIRECT structural recursion; measures /
multi-arg / lexicographic are deferred (see `structOK`) — those stay `Div`.

Placement note (#46, unchanged): `Div` is seeded on the OUTER knot only (`buildLetRec`); the inner
self-calls are typed pure `⊥` (Option A) — operationally sound since `Div` has no runtime semantics. -/
def letRecRow (name : String) (funBody : Surf) : EffRow :=
  match funBody with
  | .lam x body =>
      match body with
      | .lam _ _ => {divLabel}                                   -- curried / multi-arg: DEFERRED → Div
      | _        => if structOK name [x] [] body then ∅ else {divLabel}
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
        return some (⟨ms.length, abstractV ms Az⟩ : Scheme)
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
      | some ci => if ci.arity == 0 then .ok (ctorIntro ci .unitS)
                   else .error s!"constructor '{x}' expects {ci.arity} argument(s)"
      | none    => .ok (.var x)
  | _, .getS  => .ok .getS
  | _, .unitS => .ok .unitS
  | Γ, .thunk b  => do return .thunk (← elabS env Γ b)
  | Γ, .force b  => do return .force (← elabS env Γ b)
  | Γ, .raise e  => do return .raise (← elabS env Γ e)
  | Γ, .handle e => do return .handle (← elabS env Γ e)
  | Γ, .putS e   => do return .putS (← elabS env Γ e)
  | Γ, .atomS e  => do return .atomS (← elabS env Γ e)
  | Γ, .newS e   => do return .newS (← elabS env Γ e)
  | Γ, .readS e  => do return .readS (← elabS env Γ e)
  | Γ, .inlS e   => do return .inlS (← elabS env Γ e)
  | Γ, .inrS e   => do return .inrS (← elabS env Γ e)
  | Γ, .stateS e0 e => do return .stateS (← elabS env Γ e0) (← elabS env Γ e)
  | Γ, .writeS r w  => do return .writeS (← elabS env Γ r) (← elabS env Γ w)
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
            return w (ctorIntro ci v)
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
      let Γ' := if (Γ.lookup x).isSome then Γ else (x, (⟨0, paramHole Γ.length⟩ : Scheme)) :: Γ
      return .lam x (← elabS env Γ' b)
  -- `let rec f : T = <fun> in <body>` → the μ-encoded fixpoint (Landin's knot, ADR-0073; NO new
  -- kernel primitive — invariant #5). `Rec = μX. Thunk(X -> T)`; the self-knot `{ let #g = unfold sv
  -- in ($#g) sv } : Thunk T` reconstructs `f` from a self-value, so `f : Thunk T` is in scope in its
  -- OWN body (and the outer body) — call it as `($f) arg`. `unfold` is a RETURNER of the thunk, so it
  -- is let-bound before forcing (the #45 spike's shape, generalized per-function; monomorphic + the
  -- `: T` annotation drives check-mode on the recursive `fun`). The whole thing type-checks + lowers
  -- through the EXISTING checker/kernel — the desugar emits only ordinary `Surf`.
  | Γ, .letRecS name t (.lam pn pbody) bodyExpr => do
      let t' ← resolveTy env.aliases t
      let uT : IVTy := .U ⊥ (embC (ctyOf t'))                  -- f : Thunk T
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
        | _              => (Γ1, Γ1)
      return wrap (.matchS sv xl (← elabS env Γl el) xr (← elabS env Γr er))
  | Γ, .splitS a b p body => do
      let p0 ← elabS env Γ p
      let (Γ1, wrap, p') ← anfSplit Γ p0       -- A-normalize a computation scrutinee, #41
      let Γ' := match runInferV (synthSV Γ1 p') with
        | .ok (.prod A B) => (b, embV B) :: (a, embV A) :: Γ1
        | _               => Γ1
      return wrap (.splitS a b p' (← elabS env Γ' body))
  | Γ, .annotS (.lam x b) t => do   -- an ascribed lam's body sees its param's type (as in checking)
      let t' ← resolveTy env.aliases t         -- data names in user ascriptions close here (ADR-0069)
      let Γ' := curryBind Γ (.lam x b) t'      -- bind EVERY curried param, not just the outermost
      return .annotS (← elabS env Γ' (.lam x b)) t'
  | Γ, .annotS e t => do return .annotS (← elabS env Γ e) (← resolveTy env.aliases t)
  | Γ, .matchD s arms => do                    -- named match → unfold + matchS chain (ADR-0069)
      let s0 ← elabS env Γ s
      let (Γ, wrap, s') ← anfSplit Γ s0        -- A-normalize a computation scrutinee, #41
      let arms' ← elabArms env Γ arms          -- bodies elaborated STRUCTURALLY (ctor-typed Γ)
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
            let expected := vtyOf ci0.dataTy
            match runInferV (synthSV Γ s') with
            | .ok τ => if τ != expected then throw s!"match scrutinee is {showVTy τ}, not {ci0.dataName}"
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
def elabArms (env : ElabEnv) : NCtx → DArms → Except String DArms
  | _, .nil => .ok .nil
  | Γ, .cons c bs b r => do
      let Γa := match env.ctors.lookup c with
        | some ci =>
            (match bs, ci.payloadClosed with
             | [b1], [t1]         => (b1, embV (vtyOf t1)) :: Γ
             | [b1, b2], [t1, t2] => (b2, embV (vtyOf t2)) :: (b1, embV (vtyOf t1)) :: Γ
             | _, _               => Γ)
        | none => Γ
      let b' ← elabS env Γa b
      let r' ← elabArms env Γ r
      .ok (.cons c bs b' r')
end

/-- Build the elaboration environment from a program's decl prelude, IN ORDER (a data type may
reference itself + earlier decls; forward references fail loud). Data: encode the μ body
(self ↦ `tVar 0` — no surface μ syntax means self never sits under a nested binder, so depth 0
is always right) and the closed binder-typing payloads (self ↦ the closed μ). Impls: resolve
the target, validate against the trait (op name + param arity), and PRE-ELABORATE op bodies
against the env-so-far — nested ctors and EARLIER ops resolve; a self-recursive op fail-louds
as an unresolved operator (out of scope until `fix` lands, ADR-0069). -/
def buildEnv (ds : List Decl) : Except String ElabEnv := do
  let mut aliases : List (String × Ty) := []
  let mut ctors   : List (String × CtorInfo) := []
  let mut insts   : InstEnv := []
  let mut traits  : List (String × List OpSig) := []
  for d in ds do
    match d with
    | .dataD n cs => do
        if cs.isEmpty then throw s!"data {n}: needs at least one constructor"
        if (aliases.lookup n).isSome then throw s!"duplicate type name '{n}'"
        let openPays ← cs.mapM (fun c => c.2.mapM (resolveTy ((n, Ty.tVar 0) :: aliases)))
        let closed := Ty.tMu (sumOfTys (openPays.map prodOfTys))
        let closedPays ← cs.mapM (fun c => c.2.mapM (resolveTy ((n, closed) :: aliases)))
        aliases := (n, closed) :: aliases
        let mut i := 0
        for (c, cp) in cs.zip closedPays do
          if (ctors.lookup c.1).isSome then throw s!"duplicate constructor '{c.1}'"
          if cp.length > 2 then throw s!"constructor '{c.1}': payload arity ≤ 2 in v1 (nest tuples)"
          ctors := (c.1, ⟨n, i, cs.length, cp.length, cp, closed⟩) :: ctors
          i := i + 1
    | .traitD n sigs _ => traits := (n, sigs) :: traits
    | .implD tn τTy ops =>
        match traits.lookup tn with
        | none => throw s!"impl of undeclared trait '{tn}'"
        | some sigs => do
            let τR ← resolveTy aliases τTy
            for od in ops do
              match sigs.find? (fun s => s.name == od.name) with
              | none => throw s!"impl '{tn}' defines '{od.name}', which is not an op of the trait"
              | some sig => do
                  if od.params.length != sig.params.length then
                    throw s!"'{od.name}': impl has {od.params.length} params, the trait declares {sig.params.length}"
                  let retR ← resolveTy aliases (substSelf τR sig.retTy)
                  let bodyΓ : NCtx := match od.params with
                    | [p]    => [(p, embV (vtyOf τR))]
                    | [p, q] => [(q, embV (vtyOf τR)), (p, embV (vtyOf τR))]
                    | _      => []
                  let ebody ← elabS ⟨insts, ctors, aliases⟩ bodyΓ od.body
                  insts := insts ++ [⟨od.name, vtyOf τR, τR, retR, od.params, ebody⟩]
  return ⟨insts, ctors, aliases⟩

/-- The built-in string prelude (ADR-0074): `Char` = a code point (a newtype over `Int`, distinct so
you can't mix a char and a number), `Str` = a monomorphic char-list. Injected before every program so
string/char literals (`"hi"`, `'a'`) resolve, UNLESS the program declares `Char`/`Str` itself. Library
code over `data` + `Int` — NO kernel primitive (invariant #5). -/
def strPrelude : List Decl :=
  [ .dataD "Char" [("Char", [.tInt])],
    .dataD "Str"  [("SNil", []), ("SCons", [.tName "Char", .tName "Str"])] ]

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
def injectStdlib (declared : List String) (body : Surf) : Except String Surf := do
  if declared.contains "Str" || declared.contains "Char" then
    return body
  let wraps ← stdlibFnSrcs.mapM (fun src => do
    match ← Bang.Surface.parse src with
    | .letRecS n t f _ => return (fun (b : Surf) => Surf.letRecS n t f b)
    | .lett n rhs _    => return (fun (b : Surf) => Surf.lett n rhs b)
    | _ => .error "string-stdlib prelude fn did not parse as a `let`/`let rec`")
  return wraps.foldr (fun w acc => w acc) body

/-- Elaborate a whole program: inject the string prelude + stdlib, build the elaboration env, resolve the body. -/
def elabProg (p : Prog) : Except String Surf := do
  let declared := p.decls.filterMap (fun | .dataD n _ => some n | _ => none)
  let prelude := strPrelude.filter (fun | .dataD n _ => !declared.contains n | _ => true)
  let body ← injectStdlib declared p.body
  elabS (← buildEnv (prelude ++ p.decls)) [] body

/-- PUBLIC runnable entry (the `bang` CLI's typed pipeline): parse a program's `trait`/`impl`/`data`
prelude + body, elaborate it (resolve data constructors, named matches, and type-directed operators
like `Vec + Vec`), and lower to a kernel `Comp` ready for `Source.eval`/the machine. A decl-free
program parses to `⟨[], body⟩` and elaborates to itself, so this is a strict SUPERSET of the old
`Surface.lower ∘ parse` runner path — the whole MVP surface becomes runnable from the CLI. -/
public def elaborateToComp (src : String) : Except String Comp := do
  let prog ← Bang.Surface.parseProg src
  let e ← elabProg prog
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
  let e ← (elabProg prog).mapError (fun m => (m, Bang.Surface.locateInMsg src m))
  let _ ← (runInferC (synthSC [] e)).mapError (fun m => (m, Bang.Surface.locateInMsg src m))
  (Bang.Surface.lower e).mapError (fun m => (m, Bang.Surface.locateInMsg src m))

/-- Parse + elaborate + CHECK a source program — the decl-aware, typed sibling of `check`. -/
def checkProg (src : String) : Except String (CT × EffRow) := do
  runInferC (synthSC [] (← Bang.Surface.parseProg src >>= elabProg))

/-- Parse + elaborate + check + DISPLAY — the decl-aware, typed sibling of `display`. -/
def displayProg (src : String) : String :=
  match checkProg src with
  | .ok (B, φ) => showType B φ
  | .error e   => s!"error: {e}"

/-- Parse + elaborate + CHECK + lower + RUN through `Source.eval`, expecting `vint n` — the
typed sibling of `Surface.runYieldsInt` (which stays untyped and decl-free). The typed path
checks BEFORE it runs. -/
def runTypedYieldsInt (fuel : Nat) (src : String) (n : Int) : Bool :=
  match (do
      let e ← Bang.Surface.parseProg src >>= elabProg
      let _ ← runInferC (synthSC [] e)
      Bang.Surface.lower e) with
  | .ok c => match Source.eval fuel c with
             | .done (.vint m) => m == n
             | _               => false
  | .error _ => false

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
run per law). -/
def sampleVT : VT → List Val
  | .int      => [.vint 0, .vint 1, .vint (-2), .vint 7]
  | .prod A B => ((sampleVT A).flatMap fun a => (sampleVT B).map fun b => .pair a b).take 6
  | _         => []

/-- k-tuples over a pool (truncated cartesian power — a law's argument sample). -/
def tuples : Nat → List Val → List (List Val)
  | 0,     _    => [[]]
  | k + 1, pool => ((tuples k pool).flatMap fun t => pool.map fun v => v :: t).take 12

/-- Run ONE law instance: bind `params := args`, wrap the Bool-valued body in
`let #r = body in if #r then 1 else 0` (encoding-agnostic truth read-back), elaborate
(operators resolve), CHECK, lower, and run through `Source.eval`. -/
def checkLawOn (env : ElabEnv) (params : List String) (body : Surf) (args : List Val) : Bool :=
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
    | .traitD tn _ laws =>
        for other in p.decls do
          match other with
          | .traitD .. => pure ()
          | .dataD ..  => pure ()
          | .implD tn' τTy _ =>
              if tn' == tn then
                let τR ← resolveTy env.aliases τTy      -- named impl targets sample at the closed μ
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
`injectStdlib`), so a program uses them WITHOUT re-inlining (the #50 gap the tokenizer hit). All are
`Div`-typed (curried `let rec` — the #47 multi-arg gap; they terminate, the certifier can't prove it).
The wrapping is INERT for programs that don't use them: a `let rec … in body` binds a THUNK (a value,
`⊥`-row), so the program's row is the body's — an unused stdlib fn adds NO effect (proven below:
plain programs stay `Div ∉ ρ` and the WHOLE existing corpus is unchanged). -/
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
-- USING the stdlib puts `Div` in the row (curried `let rec`, #47 gap) — the honest over-approximation.
#guard (match checkProg "($concat) \"ab\" \"cd\"" with | .ok (_, ρ) => divLabel ∈ ρ | _ => false)
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

-- #53 — bare anonymous injections RUN end-to-end through the typed default path (CHECK precedes eval).
#guard runTypedYieldsInt 20 "match Right(7) { Left(a) -> 0, Right(x) -> x }" 7
#guard runTypedYieldsInt 20 "let x = Right(7) in match x { Left(a) -> 0, Right(x) -> x }" 7
#guard runTypedYieldsInt 20 "match Left(3) { Left(a) -> a, Right(x) -> x }" 3

end Bang.TypeCheck
