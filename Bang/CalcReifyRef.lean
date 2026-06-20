import Bang.CalcReify

/-!
# A denotational reference for the reification machine (`CalcReify`)

ADR-0015 argued that `CalcReify` is the one machine with *no in-Lean reference
`eval`* to diff against, because Lean's strict positivity forbids a value type
that embeds a resumption (`vcont : (Value → …) → Value` is rejected), and the
source language has **first-class resumptions** (`resume k v`, `k` a value). So
any reference's value domain would have to contain resumptions too — the same
wall.

This file shows the escape is real and concrete. The trick is **call-by-push-value
+ a free monad**:

* a **free monad** `Comp` over the single operation `perform : Int ⇝ Int`. The
  resumption is a genuine Lean function `Int → Comp`, but it sits in the
  *codomain* of `perf`'s argument — a **positive** occurrence — so `Comp` passes
  strict positivity, where `Value` could not.
* **values vs computations are split** (CBPV): a resumption is a *value*, kept in
  the environment as an `Entry.ek` (a real `Int → Comp` closure), never inside
  `Comp`'s result. `Comp` only ever *returns* an `Int`.
* every interpreter operation (`bind`, `handle`, `eval`) recurses with **fuel**,
  because `resume`/`handle` re-run a captured continuation `k w` that is not a
  structural subterm — exactly why the machine needed fuel too.

The result is a direct CPS interpreter that is a faithful mirror of the
independent TS interpreter (`harness/src/reify-cps.ts`), now *in Lean*. It is the
object the open bisimulation (`exec ∘ compile ≡ eval`, ADR-0015) is stated
against; the `rfl` checks below validate it against the same seven demonstrators
the machine satisfies — a second, independent in-Lean cross-check.

**What this file does NOT yet contain:** the simulation `exec (compile e) ≈ run`.
That proof relates the machine's defunctionalized `Kont` to this interpreter's
real `Comp` continuations — a machine/interpreter bisimulation, the research-grade
residual (ADR-0015). It is deliberately left as documented future work rather than
asserted with `sorry`. This file is `sorry`-free: it asserts only what it proves.
-/

namespace Bang.CalcReifyRef

open Bang.CalcReify (Src)

/-- Free monad over `perform : Int ⇝ Int`. `perf p k` is "perform with payload
`p`, then continue with the resumed value via `k`". The continuation `k : Int →
Comp` is a real function in **positive** position — the escape from positivity. -/
inductive Comp where
  | ret   : Int → Comp
  | perf  : Int → (Int → Comp) → Comp
  | stuck : Comp
deriving Inhabited

/-- Environment entries (CBPV values): an int, or a reified resumption held as a
genuine `Int → Comp` closure — the representation `CalcReify.Value` cannot hold. -/
inductive Entry where
  | ev : Int → Entry
  | ek : (Int → Comp) → Entry

abbrev REnv := List Entry

/-- Free-monad bind: thread `f` past the first `perform`. Fuel-bounded because the
`perf` case rebuilds the continuation `fun w => bind … (k w) f` and `k w` is not a
structural subterm. -/
def bind : Nat → Comp → (Int → Comp) → Comp
  | 0,      _,        _ => .stuck
  | _+1,    .ret n,   f => f n
  | _+1,    .stuck,   _ => .stuck
  | fuel+1, .perf p k, f => .perf p (fun w => bind fuel (k w) f)

mutual

/-- Evaluate a source term to a computation tree under environment `env`. Mirrors
`harness/src/reify-cps.ts`'s `evalE` exactly. -/
def eval : Nat → REnv → Src → Comp
  | 0,      _,   _ => .stuck
  | _+1,    _,   .val n => .ret n
  | _+1,    env, .var i =>
      match env[i]? with
      | some (.ev n) => .ret n
      | _            => .stuck          -- a bare resumption is not an int result
  | fuel+1, env, .add a b =>
      bind fuel (eval fuel env a) (fun x => bind fuel (eval fuel env b) (fun y => .ret (x + y)))
  | fuel+1, env, .letE e1 e2 =>
      bind fuel (eval fuel env e1) (fun v => eval fuel (.ev v :: env) e2)
  | fuel+1, env, .perform e =>
      bind fuel (eval fuel env e) (fun p => .perf p (fun w => .ret w))
  | fuel+1, env, .handle clause body =>
      handleC fuel (eval fuel env body) clause env
  | fuel+1, env, .resume k v =>
      -- a resumption is a value bound in scope: `k` is a variable holding an `ek`
      match k with
      | .var i =>
          match env[i]? with
          | some (.ek res) => bind fuel (eval fuel env v) (fun w => res w)
          | _              => .stuck
      | _ => .stuck

/-- Deep handler: fold the clause over a body computation. On `perf`, run the
clause with the payload at index 0 and the resumption (re-installing this handler —
deep) at index 1, then the install-time env. A clause that itself performs
directly yields a standing `perf` — single handler depth (ADR-0015): the top-level
observation treats it as unhandled. -/
def handleC : Nat → Comp → Src → REnv → Comp
  | 0,      _,        _,      _    => .stuck
  | _+1,    .ret n,   _,      _    => .ret n
  | _+1,    .stuck,   _,      _    => .stuck
  | fuel+1, .perf p k, clause, cEnv =>
      let res : Int → Comp := fun w => handleC fuel (k w) clause cEnv
      eval fuel (.ev p :: .ek res :: cEnv) clause

end

/-- Observe a closed program: a `ret`urned int is the result; a standing `perf`
(unhandled), a `stuck`, or fuel exhaustion are all `none` — matching the machine's
`run : … → Option Value` conflation of out-of-fuel and stuck into `none`. -/
def run (fuel : Nat) (e : Src) : Option Int :=
  match eval fuel [] e with
  | .ret n => some n
  | _      => none

/-! ## Validation: the seven `CalcReify` demonstrators, this time against the
denotational reference. Same programs, same answers as the machine's `rfl`
demonstrators — an independent in-Lean confirmation that the reference and the
machine agree (alongside the TS cross-check). -/

section Demos
open Bang.CalcReify.Src

-- body `add (perform 5) 1000`: the captured continuation is "λr. r + 1000".
private def bodyP : Src := add (perform (val 5)) (val 1000)

-- one-shot, NON-TAIL  →  (7+1000)+100 = 1107
example : run 1000 (handle (add (resume (var 1) (val 7)) (val 100)) bodyP) = some 1107 := by rfl
-- one-shot, tail  →  1007
example : run 1000 (handle (resume (var 1) (val 7)) bodyP) = some 1007 := by rfl
-- MULTI-SHOT (resume twice)  →  2027
example : run 1000 (handle (add (resume (var 1) (val 7)) (resume (var 1) (val 20))) bodyP) = some 2027 := by rfl
-- ZERO-shot (continuation discarded)  →  999
example : run 1000 (handle (val 999) bodyP) = some 999 := by rfl
-- normal return passes through  →  42
example : run 1000 (handle (var 0) (val 42)) = some 42 := by rfl
-- re-handling (perform inside a resumption)  →  7+7 = 14
example : run 1000 (handle (resume (var 1) (val 7)) (add (perform (val 1)) (perform (val 2)))) = some 14 := by rfl
-- payload reaches the clause  →  5+3 = 8
example : run 1000 (letE (val 5) (handle (add (var 0) (resume (var 1) (val 3))) (perform (var 0)))) = some 8 := by rfl

-- stuck shapes: unhandled top perform, resume of a non-resumption, unbound var
example : run 1000 (perform (val 5)) = none := by rfl
example : run 1000 (resume (val 3) (val 4)) = none := by rfl
example : run 1000 (var 7) = none := by rfl
-- a direct perform in a clause is unhandled (single handler depth)
example : run 1000 (handle (perform (val 1)) bodyP) = none := by rfl

end Demos

end Bang.CalcReifyRef
