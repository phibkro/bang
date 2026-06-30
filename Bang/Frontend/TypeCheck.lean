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

abbrev NCtx := List (String × VT)   -- named typing context, innermost first (= `List.lookup` keys)

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
@[inline] def vtyOf (t : Ty) : VT := (tyBoth t).1
@[inline] def ctyOf (t : Ty) : CT := (tyBoth t).2

/-- Map effect NAMES to the kernel label row (the inverse of `effName`). -/
def effNames (ns : List String) : EffRow :=
  ns.foldl (fun acc n =>
    if n = "throws" then insert exnLabel acc
    else if n = "state" then insert stateLabel acc
    else if n = "stm" then insert stmLabel acc else acc) ∅

/-- The DECLARED effect bound of an ascribed type, if any (`none` = unconstrained, stay inferred —
the optional-annotation philosophy). A function's bound is its codomain's. -/
def effOf : Ty → Option EffRow
  | .tEff ns _ => some (effNames ns)
  | .tArr _ b  => effOf b
  | _          => none

/-- Bool is `1 + 1` (ADR-0065); comparisons return it, arithmetic returns `Int`. -/
def boolTy : VT := .sum .unit .unit
def binopResTy : BinOp → VT
  | .lt | .eq => boolTy
  | _         => .int

-- Termination: the rank (synth = 0, check = 1) breaks the `check t → synth t` subsumption tie, as
-- in the spike; every other call is on a structural subterm of the `Surf`.
mutual
/-- Synthesize the value type of a `Surf` read as a VALUE. -/
def synthSV (Γ : NCtx) (e : Surf) : Except String VT :=
  match e with
  | .lit _     => .ok .int
  | .var x     => match Γ.lookup x with | some A => .ok A | none => .error s!"unbound variable {x}"
  | .thunk b   => do let (B, φ) ← synthSC Γ b; return .U φ B
  | .pairS a b => do return .prod (← synthSV Γ a) (← synthSV Γ b)
  | .annotS b t => do let A := vtyOf t; let _ ← checkSV Γ b A; return A
  | .inlS _    => .error "Left(_) needs an expected sum type — annotate `(Left e : A + B)`"
  | .inrS _    => .error "Right(_) needs an expected sum type — annotate `(Right e : A + B)`"
  | _          => .error "not a value (wrap a computation in braces)"
  termination_by (sizeOf e, 0)

/-- Check a `Surf` read as a VALUE against an expected value type. -/
def checkSV (Γ : NCtx) (e : Surf) (expected : VT) : Except String Unit :=
  match e, expected with
  | .inlS b,    .sum A _  => checkSV Γ b A
  | .inrS b,    .sum _ B  => checkSV Γ b B
  | .pairS a b, .prod A B => do let _ ← checkSV Γ a A; checkSV Γ b B
  | .annotS b t, expected => do
      let A := vtyOf t
      let _ ← checkSV Γ b A
      if A = expected then .ok () else .error "ascription does not match expected type"
  | e, expected => do
      let A ← synthSV Γ e
      if A = expected then .ok () else .error "value type mismatch"
  termination_by (sizeOf e, 2)

/-- Synthesize the computation type + effect row of a `Surf` read as a COMPUTATION. -/
def synthSC (Γ : NCtx) (e : Surf) : Except String (CT × EffRow) :=
  match e with
  | .lit _   => .ok (.F .omega .int, ⊥)
  | .var x   => match Γ.lookup x with
                | some A => .ok (.F .omega A, ⊥)
                | none   => .error s!"unbound variable {x}"
  | .thunk b => do let (B, φ) ← synthSC Γ b; return (.F .omega (.U φ B), ⊥)
  | .pairS a b => do return (.F .omega (.prod (← synthSV Γ a) (← synthSV Γ b)), ⊥)  -- value ⇒ ret
  | .force b => do match (← synthSV Γ b) with
                   | .U φ B => return (B, φ)
                   | _      => .error "force: not a thunk"
  | .lett x e b => do match (← synthSC Γ e) with
                      | (.F _ A, φ₁) => do let (B, φ₂) ← synthSC ((x, A) :: Γ) b; return (B, φ₁ ⊔ φ₂)
                      | _            => .error "let: head is not a returner"
  | .app f a => do match (← synthSC Γ f) with
                   | (.arr _ A B, φ) => do let _ ← checkSV Γ a A; return (B, φ)
                   | _               => .error "app: callee is not a function"
  | .binopS op a b => do
      let _ ← checkSV Γ a .int; let _ ← checkSV Γ b .int
      return (.F .omega (binopResTy op), ⊥)
  | .ifS c t e => do
      let _ ← checkSV Γ c boolTy
      let (C, φ₁) ← synthSC Γ t
      let φ₂ ← checkSC Γ e C
      return (C, φ₁ ⊔ φ₂)
  | .matchS s xl el xr er => do match (← synthSV Γ s) with
      | .sum A B => do
          let (C, φ₁) ← synthSC ((xl, A) :: Γ) el
          let φ₂ ← checkSC ((xr, B) :: Γ) er C
          return (C, φ₁ ⊔ φ₂)
      | _ => .error "match: scrutinee is not a sum"
  | .splitS a b p body => do match (← synthSV Γ p) with
      | .prod A B => synthSC ((b, B) :: (a, A) :: Γ) body
      | _ => .error "split: scrutinee is not a product"
  | .annotS b t => do
      let C := ctyOf t
      let φ ← checkSC Γ b C
      match effOf t with                              -- declared row (if any) is an upper bound — ④b
      | some ρ => if φ ⊆ ρ then return (C, φ) else .error "inferred effect exceeds the declared row"
      | none   => return (C, φ)
  -- ── effects (ADR-0066 ④): each op ADDS its label to the row; handlers DISCHARGE it (`Finset.erase`).
  -- v1 simplification (marked): operation payload/result types are fixed to the surface convention
  -- (state cell + TVar contents + exn payload are `Int`, ADR-0030) — no payload-type threading yet.
  | .raise e     => do let _ ← checkSV Γ e .int; return (.F .omega .int, {exnLabel})    -- result = payload (v1)
  | .handle e    => do let (B, φ) ← synthSC Γ e; return (B, φ.erase exnLabel)            -- discharge throws
  | .getS        => .ok (.F .omega .int, {stateLabel})
  | .putS e      => do let _ ← checkSV Γ e .int; return (.F .omega .unit, {stateLabel})
  | .stateS e0 e => do let _ ← checkSV Γ e0 .int; let (B, φ) ← synthSC Γ e; return (B, φ.erase stateLabel)
  | .atomS e     => do let (B, φ) ← synthSC Γ e; return (B, φ.erase stmLabel)            -- discharge stm
  | .newS e      => do let _ ← checkSV Γ e .int; return (.F .omega .int, {stmLabel})     -- TVar ref = Int (ADR-0030)
  | .readS e     => do let _ ← checkSV Γ e .int; return (.F .omega .int, {stmLabel})
  | .writeS r w  => do let _ ← checkSV Γ r .int; let _ ← checkSV Γ w .int; return (.F .omega .unit, {stmLabel})
  -- check-mode-only intros: fail loud (synthesis has no expected type to drive them).
  | .lam _ _ => .error "fun needs an expected arrow type — annotate `(fun x => e : A -> B)`"
  | .inlS _  => .error "Left(_) needs an expected sum type — annotate `(Left e : A + B)`"
  | .inrS _  => .error "Right(_) needs an expected sum type — annotate `(Right e : A + B)`"
  -- NO catch-all: synthSC now ENUMERATES every Surf constructor, so a NEW feature fails to compile
  -- here until it is typed — pipeline-completeness by construction (the operator's enforcement ask).
  termination_by (sizeOf e, 1)

/-- Check a `Surf` read as a COMPUTATION against an expected computation type. -/
def checkSC (Γ : NCtx) (e : Surf) (expected : CT) : Except String EffRow :=
  match e, expected with
  | .lam x b,   .arr _ A B => checkSC ((x, A) :: Γ) b B
  -- value-constructors in computation position lower to `ret v` — check the value against `A` of `F A`.
  | .inlS b,    .F _ (.sum A B)  => do let _ ← checkSV Γ (.inlS b) (.sum A B); return ⊥
  | .inrS b,    .F _ (.sum A B)  => do let _ ← checkSV Γ (.inrS b) (.sum A B); return ⊥
  | .pairS a b, .F _ (.prod A B) => do let _ ← checkSV Γ (.pairS a b) (.prod A B); return ⊥
  | .annotS b t, expected => do
      let C := ctyOf t
      let φ ← checkSC Γ b C
      if C ≠ expected then .error "ascription does not match expected type"
      else match effOf t with
        | some ρ => if φ ⊆ ρ then .ok φ else .error "inferred effect exceeds the declared row"
        | none   => .ok φ
  | e, expected => do
      let (B, φ) ← synthSC Γ e
      if B = expected then .ok φ else .error "computation type mismatch"
  termination_by (sizeOf e, 3)
end

/-- End-to-end at the SURFACE: parse a source string, then type-check it as a computation. -/
def check (src : String) : Except String (CT × EffRow) := do
  let e ← Bang.Surface.parse src
  synthSC [] e

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

-- REJECTIONS — the surface checker is sound:
#guard (match check "1 + Left(0)" with | .error _ => true | _ => false)         -- non-Int operand
#guard (match check "( fun x => x : Int -> Int ) Left(0)" with | .error _ => true | _ => false)  -- arg type
#guard (match check "( 3 : Int + Int )" with | .error _ => true | _ => false)    -- 3 is not a sum

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
  else if ℓ = stmLabel then "stm" else s!"e{ℓ}"

/-- Render an effect row as `throws, state` by decidable membership of the known labels (computable —
`Finset.toList` is noncomputable; the surface has exactly these three labels). -/
def showRow (φ : EffRow) : String :=
  String.intercalate ", " <|
    (if exnLabel ∈ φ then [effName exnLabel] else []) ++
    (if stateLabel ∈ φ then [effName stateLabel] else []) ++
    (if stmLabel ∈ φ then [effName stmLabel] else [])

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

end Bang.TypeCheck
