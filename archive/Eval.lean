import Bang.EffectRow

/-!
# bang-lang definitional interpreter `eval` (the K2 reference)

A fuel-bounded, **total** definitional interpreter for the pinned core. This is
the executable `eval` the VM will be *calculated from* (ADR-0004, Bahr–Hutton);
it is NOT the machine. See **ADR-0008** for the shape and the rationale.

Design (ADR-0008):
* **Free-monad / algebraic-effects** presentation: an effectful computation is a
  tree `Comp` whose `op` nodes carry an effect request *and its resumption*
  (`Value → Comp`). The resumption is exactly what the K2/K3 calculation will
  defunctionalize into machine code — so the reference holds it as a function,
  not as a reified stack (that stack is the calculation's *output*).
* **CPS interpreter**: `eval` threads an explicit continuation `Value → Comp`, so
  it builds the `Comp` tree directly with no separate (non-structural) `bind`.
* **Deep handlers** as a fold (`handleC`) that re-installs itself on resume and
  *forwards* unhandled ops outward.
* **Total via fuel**: every recursive driver matches on `Nat` fuel and decays to
  an explicit `oom` (out-of-fuel) constructor — never a faked value, never a
  `partial def` (which would have no equational lemmas for the calculation).
* **Effect labels are reused from `Bang.EffectRow`** (`Label = ℕ`): a program's
  effect row is the `Finset` of labels it can emit (`effectsOf`), so rows-as-sets
  is literally the K1 model (ADR-0001), not a parallel notion.
* **Call-by-name**: bindings hold *descriptions* (thunks); `$` forces to WHNF.

DEFERRED here (honest TODOs, never faked — ADR-0008):
* multi-shot handlers — needs the resumption reified as data; our `Comp.op`
  resumption is a host function used ≤ once by the sample handlers.
* STM — the one privileged primitive (ADR-0003); a machine primitive, not a
  handler. Not modelled as an effect.
* `:` / `=` reactivity (ADR-0005) — not implemented; CBN may need revisiting then.
* divergence beyond fuel — surfaced as `oom`, not distinguished from true loops.
* nested deep patterns (a constructor pattern *inside* a constructor pattern)
  match against still-unforced thunk args, so they simply fail to match here
  rather than forcing mid-match; top-level constructor/literal patterns work.
-/

namespace Bang.Eval

open Bang.EffectRow (Label)

abbrev Name   := String
abbrev CtorId := String
abbrev OpId   := String      -- "get" | "put" | "raise"

/-! ## Syntax -/

/-- Patterns. Sub-patterns of a `pcon` that are themselves `pcon`/`plit` match
against the (still lazy) constructor argument and therefore fail to match in v0
(see header). `pvar`/`pwild` sub-patterns bind the lazy argument unforced. -/
inductive Pat where
  | pwild
  | pvar  : Name → Pat
  | plit  : Int → Pat
  | pcon  : CtorId → List Pat → Pat
deriving Repr

/- Core expressions and the handler-spec they can install. These are mutually
recursive: `Expr.handle` carries a `HandlerSpec`, and `HandlerSpec.stateH`
carries the `Expr` for its initial state — so they share one `mutual` block.
Parens-group (ADR-0007) is *not* a node: grouping is plain subexpression nesting
with no force, so the description/value distinction lives entirely in where
`force` sits. -/
mutual
inductive Expr where
  | lit     : Int → Expr
  | unit    : Expr
  | var     : Name → Expr
  | lam     : Name → Expr → Expr
  | app     : Expr → Expr → Expr
  | thnk    : Expr → Expr                       -- an explicit description literal (delay)
  | force   : Expr → Expr                       -- `$e` : force to WHNF
  | letE    : Name → Expr → Expr → Expr         -- `let x = e1; e2` (immutable, CBN)
  | con     : CtorId → List Expr → Expr         -- constructor application (lazy args)
  | matchE  : Expr → List (Pat × Expr) → Expr
  | ifE     : Expr → Expr → Expr → Expr         -- forces the condition to a Bool con
  | binop   : String → Expr → Expr → Expr       -- + - * < ==  (force both to ints)
  | perform : Label → OpId → Expr → Expr        -- effect op: perform ℓ.op(arg)
  | handle  : HandlerSpec → Expr → Expr         -- install a handler around the body
/-- Which handler to install. The state handler's initial state is an expression
forced at install time. -/
inductive HandlerSpec where
  | stateH  : Label → Expr → HandlerSpec
  | throwsH : Label → HandlerSpec
end

/-! ## Values and computations -/

/-- WHNF values plus first-class thunks (descriptions). `Env` is a list because
the core is post-elaboration: a closure carries exactly the bindings the front
end captured (ADR-0006 lives above `eval`; the `Env` is its denotation). Nested
through `List`/`Prod`, so a plain (nested) inductive suffices. -/
inductive Value where
  | vunit
  | vint   : Int → Value
  | vclos  : Name → Expr → List (Name × Value) → Value     -- λ x. body  with captured env
  | vcon   : CtorId → List Value → Value                   -- saturated constructor (lazy args)
  | vthunk : Expr → List (Name × Value) → Value            -- unforced description
deriving Inhabited

abbrev Env := List (Name × Value)

/-- A computation: a tree of effect requests over a `Value` result. `op` carries
the effect `Label`, the operation, its (forced) argument, and **the resumption**.
`oom`/`wrong` are the two loud terminal failures (out-of-fuel vs genuinely stuck).
-/
inductive Comp where
  | pure  : Value → Comp
  | op    : Label → OpId → Value → (Value → Comp) → Comp
  | oom   : Comp
  | wrong : String → Comp

/-- Installed handlers. `state` threads its current state `Value` through the
fold; `throws` discards the resumption on `raise`. -/
inductive Handler where
  | state  : Label → Value → Handler
  | throws : Label → Handler

/-! ## Helpers (pure, structural) -/

def lookupEnv (x : Name) : Env → Option Value
  | []          => none
  | (y, v) :: r => if x = y then some v else lookupEnv x r

/-- A primitive binary op on two forced ints. Comparisons yield the Bool ADT
`True`/`False` (no separate Bool value — ADTs cover it). `none` = bad operands. -/
def prim (op : String) (a b : Int) : Option Value :=
  match op with
  | "+" => some (.vint (a + b))
  | "-" => some (.vint (a - b))
  | "*" => some (.vint (a * b))
  | "<" => some (.vcon (if a < b then "True" else "False") [])
  | "==" => some (.vcon (if a = b then "True" else "False") [])
  | _   => none

/- Match one pattern against a WHNF value, producing the bindings or `none`.
Structural on the pattern. Nested `pcon`/`plit` sub-patterns see lazy `vthunk`
args and fail (v0 limitation, see header) — never crash. `matchPat`/`matchPats`
are mutually recursive. -/
mutual
def matchPat : Pat → Value → Option Env
  | .pwild,      _            => some []
  | .pvar x,     v            => some [(x, v)]
  | .plit n,     .vint m      => if n = m then some [] else none
  | .plit _,     _            => none
  | .pcon c ps,  .vcon c' vs  =>
      if c = c' ∧ ps.length = vs.length then matchPats ps vs else none
  | .pcon _ _,   _            => none
/-- Match a list of sub-patterns against a list of values, concatenating bindings. -/
def matchPats : List Pat → List Value → Option Env
  | [],      []      => some []
  | p :: ps, v :: vs => match matchPat p v, matchPats ps vs with
                        | some b1, some b2 => some (b1 ++ b2)
                        | _,       _       => none
  | _,       _       => none
end

/-! ## The handler fold (standalone, fuel-bounded — ADR-0008)

`handleC fuel h c k` interprets the computation `c` under handler `h`, then feeds
the handled result to the outer continuation `k`. It threads `k` into the `pure`
leaves and **forwards** any op the handler does not own. Deep: resuming re-wraps
`h` around the resumption (`fun r => handleC fuel h (kont r) k`). -/
def handleC (fuel : Nat) (h : Handler) (c : Comp) (k : Value → Comp) : Comp :=
  match fuel with
  | 0          => .oom
  | Nat.succ f =>
    match h, c with
    | _,            .oom        => .oom
    | _,            .wrong s    => .wrong s
    -- throws: `raise` discards the resumption; the block's value becomes Err e,
    -- a normal value becomes Ok v.
    | .throws _,    .pure v     => k (.vcon "Ok" [v])
    | .throws ℓ,    .op ℓ' o a kont =>
        if ℓ' = ℓ ∧ o = "raise" then k (.vcon "Err" [a])
        else .op ℓ' o a (fun r => handleC f (.throws ℓ) (kont r) k)
    -- state: get resumes with the current state, put updates it and resumes ().
    | .state _ _,   .pure v     => k v
    | .state ℓ s,   .op ℓ' o a kont =>
        if ℓ' = ℓ then
          match o with
          | "get" => handleC f (.state ℓ s) (kont s) k
          | "put" => handleC f (.state ℓ a) (kont .vunit) k
          | _     => .op ℓ' o a (fun r => handleC f (.state ℓ s) (kont r) k)
        else .op ℓ' o a (fun r => handleC f (.state ℓ s) (kont r) k)
termination_by fuel

/-! ## The interpreter (CPS, fuel-bounded, total — ADR-0008)

`eval fuel env e k` evaluates `e` to a `Value` and feeds it to `k`, building the
`Comp` tree. `forceV` reduces a value to WHNF (forcing thunks, effectfully).
`matchArms` tries match arms in order. `deepForce` fully evaluates a value for
display (used only by `run`). All four are mutually recursive on `fuel`. -/
mutual

def eval (fuel : Nat) (env : Env) (e : Expr) (k : Value → Comp) : Comp :=
  match fuel with
  | 0          => .oom
  | Nat.succ f =>
    match e with
    | .lit n      => k (.vint n)
    | .unit       => k .vunit
    | .var x      => match lookupEnv x env with
                     | some v => k v
                     | none   => .wrong s!"unbound variable {x}"
    | .lam x b    => k (.vclos x b env)
    | .thnk e'    => k (.vthunk e' env)                       -- a description, unforced
    | .force e'   => eval f env e' (fun v => forceV f v k)    -- `$e`
    | .app fe ae  =>
        eval f env fe (fun fv => forceV f fv (fun fv' =>
          match fv' with
          | .vclos x b cenv => eval f ((x, .vthunk ae env) :: cenv) b k   -- CBN: arg as description
          | _               => .wrong "application of a non-function"))
    | .letE x e1 e2 => eval f ((x, .vthunk e1 env) :: env) e2 k           -- CBN let
    | .con c args => k (.vcon c (args.map (fun a => .vthunk a env)))      -- lazy constructor args
    | .matchE s arms =>
        eval f env s (fun sv => forceV f sv (fun sv' => matchArms f env sv' arms k))
    | .ifE c t e' =>
        eval f env c (fun cv => forceV f cv (fun cv' =>
          match cv' with
          | .vcon "True"  [] => eval f env t k
          | .vcon "False" [] => eval f env e' k
          | _                => .wrong "if-condition is not a Bool"))
    | .binop op a b =>
        eval f env a (fun av => forceV f av (fun av' =>
          eval f env b (fun bv => forceV f bv (fun bv' =>
            match av', bv' with
            | .vint x, .vint y => match prim op x y with
                                  | some r => k r
                                  | none   => .wrong s!"bad binop {op}"
            | _, _             => .wrong "binop on non-integers"))))
    | .perform ℓ o argE =>
        eval f env argE (fun av => forceV f av (fun av' => .op ℓ o av' k))  -- k IS the resumption
    | .handle (.throwsH ℓ) body =>
        handleC f (.throws ℓ) (eval f env body .pure) k
    | .handle (.stateH ℓ initE) body =>
        eval f env initE (fun s0d => forceV f s0d (fun s0 =>
          handleC f (.state ℓ s0) (eval f env body .pure) k))
  termination_by fuel

/-- Force a value to weak head normal form, performing effects along the way. -/
def forceV (fuel : Nat) (v : Value) (k : Value → Comp) : Comp :=
  match fuel with
  | 0          => .oom
  | Nat.succ f =>
    match v with
    | .vthunk e env => eval f env e (fun w => forceV f w k)   -- keep forcing to WHNF
    | other         => k other
  termination_by fuel

/-- Try match arms in order; on the first matching pattern, evaluate its RHS. -/
def matchArms (fuel : Nat) (env : Env) (v : Value)
    (arms : List (Pat × Expr)) (k : Value → Comp) : Comp :=
  match fuel with
  | 0          => .oom
  | Nat.succ f =>
    match arms with
    | []            => .wrong "no pattern matched"
    | (p, rhs) :: r => match matchPat p v with
                       | some bs => eval f (bs ++ env) rhs k
                       | none    => matchArms f env v r k
  termination_by fuel

end

/-! ## Running a program (force the result for display) -/

/- Deep-force a value (force to WHNF, then recursively force constructor args)
for a concrete display normal form. Used only by `run`. Fuel-bounded. -/
mutual
def deepForce (fuel : Nat) (v : Value) (k : Value → Comp) : Comp :=
  match fuel with
  | 0          => .oom
  | Nat.succ f =>
    forceV f v (fun w =>
      match w with
      | .vcon c args => deepForceList f args [] (fun args' => k (.vcon c args'))
      | other        => k other)
  termination_by fuel
/-- Deep-force a list of values left to right, accumulating the forced prefix. -/
def deepForceList (fuel : Nat) (vs : List Value) (acc : List Value)
    (k : List Value → Comp) : Comp :=
  match fuel with
  | 0          => .oom
  | Nat.succ f =>
    match vs with
    | []      => k acc.reverse
    | v :: r  => deepForce f v (fun v' => deepForceList f r (v' :: acc) k)
  termination_by fuel
end

/-- The observable outcome of running a closed program. -/
inductive RunResult where
  | value     : Value → RunResult           -- a deep-forced result value
  | uncaught  : Label → OpId → RunResult     -- an effect escaped every handler (loud)
  | stuck     : String → RunResult           -- genuinely wrong program (loud)
  | outOfFuel : RunResult                    -- ran past the fuel budget (inconclusive)

/-- Interpret a finished `Comp` into a `RunResult`. -/
def finish : Comp → RunResult
  | .pure v       => .value v
  | .op ℓ o _ _   => .uncaught ℓ o
  | .wrong s      => .stuck s
  | .oom          => .outOfFuel

/-- Run a closed expression: evaluate, then deep-force the result for display. -/
def run (fuel : Nat) (e : Expr) : RunResult :=
  finish (eval fuel [] e (fun v => deepForce fuel v .pure))

/-! ## Effect rows reuse the verified `Finset` model (ADR-0001)

`effectsOf` is the *static* over-approximation of the effects an expression can
emit: the `Finset` of labels on its `perform` nodes, with `handle` discharging
the handled label. This is the dynamic shadow of the unifier's subset/union — and
it is the SAME `Finset Label` algebra the K1 oracle is verified over, reused, not
re-invented. (It is not needed to *run* a program; it ties `eval` to the row model.) -/
mutual
def effectsOf : Expr → Finset Label
  | .lit _ | .unit | .var _ => ∅
  | .lam _ b | .thnk b | .force b => effectsOf b
  | .app a b | .binop _ a b => effectsOf a ∪ effectsOf b
  | .letE _ a b => effectsOf a ∪ effectsOf b
  | .con _ args => effectsOfList args
  | .matchE s arms => effectsOf s ∪ effectsOfArms arms
  | .ifE c t e => effectsOf c ∪ effectsOf t ∪ effectsOf e
  | .perform ℓ _ argE => insert ℓ (effectsOf argE)
  | .handle (.throwsH ℓ) body => (effectsOf body).erase ℓ
  | .handle (.stateH ℓ initE) body => effectsOf initE ∪ (effectsOf body).erase ℓ
/-- Union of effects over a list of subexpressions (structural helper). -/
def effectsOfList : List Expr → Finset Label
  | []      => ∅
  | e :: r  => effectsOf e ∪ effectsOfList r
/-- Union of effects over match arms' right-hand sides (structural helper). -/
def effectsOfArms : List (Pat × Expr) → Finset Label
  | []        => ∅
  | pe :: r   => effectsOf pe.2 ∪ effectsOfArms r
end

end Bang.Eval
