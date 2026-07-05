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
  | .unitS     => .ok .unit
  | .annotS b t => do let A := vtyOf t; let _ ← checkSV Γ b A; return A
  | .inlS _    => .error "Left(_) needs an expected sum type — annotate `(Left e : A + B)`"
  | .inrS _    => .error "Right(_) needs an expected sum type — annotate `(Right e : A + B)`"
  | .foldS _   => .error "fold needs an expected μ type — annotate (ctor elaboration provides it)"
  | _          => .error "not a value (wrap a computation in braces)"
  termination_by (sizeOf e, 0)

/-- Check a `Surf` read as a VALUE against an expected value type. -/
def checkSV (Γ : NCtx) (e : Surf) (expected : VT) : Except String Unit :=
  match e, expected with
  | .inlS b,    .sum A _  => checkSV Γ b A
  | .inrS b,    .sum _ B  => checkSV Γ b B
  | .pairS a b, .prod A B => do let _ ← checkSV Γ a A; checkSV Γ b B
  -- T_Fold mirrored (ADR-0069): `fold v : μ.A` ⇐ `v : A[μ.A/0]` — the kernel's own unrollMu.
  | .foldS b,   .mu A     => checkSV Γ b (VTy.unrollMu A)
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
  -- ── ADR-0069 (data) ──
  | .unitS     => .ok (.F .omega .unit, ⊥)
  | .unfoldS b => do match (← synthSV Γ b) with        -- T_Unfold mirrored: F 1 (A[μ.A/0]), pure
                     | .mu A => .ok (.F 1 (VTy.unrollMu A), ⊥)
                     | _     => .error "unfold: not a μ value"
  | .matchD .. => .error "named match is elaborated away on the typed path — reaching the checker means the data env lacked its constructors (ADR-0069)"
  -- ── ADR-0070 (named capabilities) ──
  | .withCapS kind init name body => do
      match capKindLabel kind with
      | none => .error s!"with: unknown handler kind '{kind}'"
      | some ℓ => do
          if kind = "state" then let _ ← checkSV Γ init .int   -- the initial cell value is Int
          let (B, φ) ← synthSC ((name, .cap ℓ) :: Γ) body       -- name : Cap ℓ in scope
          return (B, φ.erase ℓ)                                 -- the handler DISCHARGES ℓ
  | .dotPerform recv op args => do
      match (← synthSV Γ recv) with
      | .cap ℓ =>
          match capOpSig op with
          | none => .error s!"unknown capability op '{op}'"
          | some (ℓ', argTys, resTy) =>
              if ℓ != ℓ' then .error s!"cap op '{op}' expects a different capability (label mismatch)"
              else
                -- match SurfArgs to the op's arity: each arg is a syntactic subterm (termination).
                match args, argTys with
                | .none,    []       => .ok (.F .omega resTy, {ℓ})
                | .one a,   [t]      => do let _ ← checkSV Γ a t; return (.F .omega resTy, {ℓ})
                | .two a b, [t1, t2] => do let _ ← checkSV Γ a t1; let _ ← checkSV Γ b t2
                                          return (.F .omega resTy, {ℓ})
                | _, _ => .error s!"cap op '{op}' expects {argTys.length} argument(s)"
      | _ => .error s!"cap op '{op}': receiver is not a capability value (Cap ℓ)"
  -- check-mode-only intros: fail loud (synthesis has no expected type to drive them).
  | .lam _ _ => .error "fun needs an expected arrow type — annotate `(fun x => e : A -> B)`"
  | .inlS _  => .error "Left(_) needs an expected sum type — annotate `(Left e : A + B)`"
  | .inrS _  => .error "Right(_) needs an expected sum type — annotate `(Right e : A + B)`"
  | .foldS _ => .error "fold needs an expected μ type — annotate (ctor elaboration provides it)"
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
  | .foldS b,   .F _ (.mu A)     => do let _ ← checkSV Γ (.foldS b) (.mu A); return ⊥
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
  | Γ, .pairS a b   => do return .pairS (← elabS env Γ a) (← elabS env Γ b)
  | Γ, .foldS b     => do return .foldS (← elabS env Γ b)
  | Γ, .unfoldS b   => do return .unfoldS (← elabS env Γ b)
  | Γ, .withCapS kind init name body => do   -- bind name : Cap ℓ so body operands synthesize (ADR-0070)
      let init' ← elabS env Γ init
      let Γ' := match capKindLabel kind with
        | some ℓ => (name, (.cap ℓ : VT)) :: Γ
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
      | some ci => if ci.arity == 0 then .error s!"constructor '{c}' takes no arguments"
                   else do return ctorIntro ci (← elabS env Γ a)
      | none    => do return .app (.var c) (← elabS env Γ a)
  | Γ, .app f a     => do return .app (← elabS env Γ f) (← elabS env Γ a)
  | Γ, .ifS c t e   => do return .ifS (← elabS env Γ c) (← elabS env Γ t) (← elabS env Γ e)
  | Γ, .lam x b     => do return .lam x (← elabS env Γ b)
  | Γ, .lett x e b  => do
      let e' ← elabS env Γ e
      let Γ' := match synthSC Γ e' with
        | .ok (.F _ A, _) => (x, A) :: Γ
        | _               => Γ
      return .lett x e' (← elabS env Γ' b)
  | Γ, .matchS s xl el xr er => do
      let s' ← elabS env Γ s
      let (Γl, Γr) := match synthSV Γ s' with
        | .ok (.sum A B) => ((xl, A) :: Γ, (xr, B) :: Γ)
        | _              => (Γ, Γ)
      return .matchS s' xl (← elabS env Γl el) xr (← elabS env Γr er)
  | Γ, .splitS a b p body => do
      let p' ← elabS env Γ p
      let Γ' := match synthSV Γ p' with
        | .ok (.prod A B) => (b, B) :: (a, A) :: Γ
        | _               => Γ
      return .splitS a b p' (← elabS env Γ' body)
  | Γ, .annotS (.lam x b) t => do   -- an ascribed lam's body sees its param's type (as in checking)
      let t' ← resolveTy env.aliases t         -- data names in user ascriptions close here (ADR-0069)
      let Γ' := match tyBoth t' with
        | (_, .arr _ A _) => (x, A) :: Γ
        | _               => Γ
      return .annotS (.lam x (← elabS env Γ' b)) t'
  | Γ, .annotS e t => do return .annotS (← elabS env Γ e) (← resolveTy env.aliases t)
  | Γ, .matchD s arms => do                    -- named match → unfold + matchS chain (ADR-0069)
      let s' ← elabS env Γ s
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
            match synthSV Γ s' with
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
            return .lett "#u" (.unfoldS s') (buildMatch ordered "#u")
  | Γ, .binopS op a b => do
      let a' ← elabS env Γ a
      let b' ← elabS env Γ b
      match synthSV Γ a' with
      | .ok .int  => return .binopS op a' b'   -- the kernel δ-rule path (ADR-0065), untouched
      | .error _  => return .binopS op a' b'   -- non-value operand: leave it; the checker rules as today
      | .ok τ =>
          match env.insts.find? (fun i => i.opName == binopName op && i.target == τ) with
          | none => .error s!"no impl provides '{binopName op}' for {showVTy τ}"
          | some inst =>
              match inst.params with
              | [p, q] =>
                  let fnTy : Ty := .tArr inst.targetTy (.tArr inst.targetTy inst.retTy)
                  return .app (.app (.annotS (.lam p (.lam q inst.body)) fnTy) a') b'
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
             | [b1], [t1]         => (b1, vtyOf t1) :: Γ
             | [b1, b2], [t1, t2] => (b2, vtyOf t2) :: (b1, vtyOf t1) :: Γ
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
                    | [p]    => [(p, vtyOf τR)]
                    | [p, q] => [(q, vtyOf τR), (p, vtyOf τR)]
                    | _      => []
                  let ebody ← elabS ⟨insts, ctors, aliases⟩ bodyΓ od.body
                  insts := insts ++ [⟨od.name, vtyOf τR, τR, retR, od.params, ebody⟩]
  return ⟨insts, ctors, aliases⟩

/-- Elaborate a whole program: build the elaboration env from the decl prelude, resolve the body. -/
def elabProg (p : Prog) : Except String Surf := do
  elabS (← buildEnv p.decls) [] p.body

/-- PUBLIC runnable entry (the `bang` CLI's typed pipeline): parse a program's `trait`/`impl`/`data`
prelude + body, elaborate it (resolve data constructors, named matches, and type-directed operators
like `Vec + Vec`), and lower to a kernel `Comp` ready for `Source.eval`/the machine. A decl-free
program parses to `⟨[], body⟩` and elaborates to itself, so this is a strict SUPERSET of the old
`Surface.lower ∘ parse` runner path — the whole MVP surface becomes runnable from the CLI. -/
public def elaborateToComp (src : String) : Except String Comp := do
  let prog ← Bang.Surface.parseProg src
  let e ← elabProg prog
  Bang.Surface.lower e

/-- Parse + elaborate + CHECK a source program — the decl-aware, typed sibling of `check`. -/
def checkProg (src : String) : Except String (CT × EffRow) := do
  synthSC [] (← Bang.Surface.parseProg src >>= elabProg)

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
      let _ ← synthSC [] e
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
      let _ ← synthSC [] e
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

/-! ## Validation ⑩ — named capabilities are TYPED (#3, ADR-0070).

`with H as h` binds `h : Cap ℓ`; `h.op` performs (adding ℓ to the row); the handler discharges ℓ.
The checker rejects a label mismatch or a non-cap receiver. Both the ambient and named forms are
identity-dispatched; the type just now names the cap. -/
-- a handled named-state program is pure (the `with` discharges {state}).
#guard check "with state 5 as h in h.get" == .ok (.F .omega .int, ⊥)
#guard display "with state 5 as h in h.get" == "Int"
-- the TWO-CELL demo type-checks AND runs to 3 (typed path) — ambient can't express it.
#guard runTypedYieldsInt 90 "with state 1 as a in (with state 2 as b in (let x = a.get in (let y = b.get in x + y)))" 3
-- put on a named cap, then get, still discharged.
#guard runTypedYieldsInt 60 "with state 5 as h in (let z = h.put(7) in h.get)" 7
-- a named transaction cap, fully handled.
#guard displayProg "with atomically as t in (let r = t.new(100) in (let z = t.write(r, 70) in t.read(r)))" == "Int"

-- REJECTIONS — the cap checker is sound:
-- label mismatch: a state cap has no `raise`.
#guard (match check "with state 5 as h in h.raise(9)" with | .error _ => true | _ => false)
-- non-cap receiver: an Int is not a capability.
#guard (match check "let x = 3 in x.get" with | .error _ => true | _ => false)
-- wrong arg type: put expects Int, given a sum.
#guard (match check "with state 5 as h in h.put(Left(0))" with | .error _ => true | _ => false)
-- unknown op on a valid cap.
#guard (match check "with state 5 as h in h.frobnicate" with | .error _ => true | _ => false)

end Bang.TypeCheck
