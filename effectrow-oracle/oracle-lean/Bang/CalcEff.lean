/-!
# K3 start: effects — a general handler machine calculated from `eval` (Throws)

The first effect stage (roadmap K3; Bahr–Hutton *Monadic Compiler Calculation*
2022 + Hutton–Wright exception-machine lineage). We add **general algebraic
handlers** (`perform`/`handle`, label-dispatched, nesting, forwarding) over a
minimal arithmetic+`let` base, with **Throws** as the first operation.

`raise` is **zero-shot** (it discards its continuation), so this increment needs
no continuation reification — that is deferred to the resumption-using effects
(`State`, one-shot). What *does* fall out of the calculation is the Hutton–Wright
**exception machine, generalised to labelled handlers**: a runtime **handler
stack**, with `MARK ℓ recovery` (install), `UNMARK` (pop on normal completion),
and `THROW ℓ` (unwind to the nearest ℓ-handler) — derived, not designed.

Design notes (vs the closure machines):
* The source is total (exceptions short-circuit but don't diverge), so **`eval`
  is total, no fuel** — it returns an `Outcome` (a value, or a propagating
  effect). Values are `Int` here (no closures yet; compose with `CalcCBN` later).
* The **machine** `exec` is still fuel-bounded — `THROW` jumps to recovery code,
  which isn't a structural subterm — and carries a handler stack, returning a
  machine `Result` (halt, or an uncaught effect).
* Correctness (next): relate `eval`'s `Outcome` to the machine's `Result` —
  `ret v ↔ halt [v]`, `exc ℓ p ↔ uncaught ℓ p` — via the playbook.
-/

namespace Bang.CalcEff

abbrev Label := Nat

/-! ## Source and its total denotational semantics -/

inductive Src where
  | val     : Int → Src
  | add     : Src → Src → Src
  | var     : Nat → Src
  | letE    : Src → Src → Src
  | perform : Label → Src → Src         -- raise effect ℓ carrying the value of the arg
  | handle  : Label → Src → Src → Src   -- handle ℓ onRaise body  (onRaise binds the payload at index 0)
deriving Repr, Inhabited

abbrev Env := List Int

/-- The result of evaluating: a normal value, or a propagating effect (`raise`)
carrying its label and payload, looking for a handler. -/
inductive Outcome where
  | ret : Int → Outcome
  | exc : Label → Int → Outcome
deriving Repr, DecidableEq, Inhabited

/-- Total, structural semantics. `add`/`let`/`perform` short-circuit on a
propagating effect; `handle` catches its own label (running the recovery with the
payload bound) and forwards the rest. -/
def eval : Env → Src → Outcome
  | _,   .val n  => .ret n
  | env, .var i  => match env[i]? with | some v => .ret v | none => .ret 0
  | env, .add x y =>
      match eval env x with
      | .exc l p => .exc l p
      | .ret a   => match eval env y with
                    | .exc l p => .exc l p
                    | .ret b   => .ret (a + b)
  | env, .letE e1 e2 =>
      match eval env e1 with
      | .exc l p => .exc l p
      | .ret v   => eval (v :: env) e2
  | env, .perform l argE =>
      match eval env argE with
      | .exc l' p => .exc l' p
      | .ret e    => .exc l e            -- raise ℓ with the payload
  | env, .handle l onRaise body =>
      match eval env body with
      | .ret v    => .ret v              -- normal completion: pass through
      | .exc l' p => if l' = l then eval (p :: env) onRaise   -- caught: run recovery, payload at index 0
                     else .exc l' p                            -- forward to an outer handler

/-! ## The machine — derived, not designed

The handler stack and `MARK`/`UNMARK`/`THROW` fall out of the `perform`/`handle`
cases of the calculation spec (Hutton–Wright, generalised to labels):

* `handle ℓ onRaise body` → `MARK ℓ recovery :: compile body (UNMARK :: c)`, where
  `recovery = BIND :: compile onRaise (UNBIND :: c)`: install a handler frame
  capturing (ℓ, recovery, env, stack); run the body; `UNMARK` pops the frame on
  normal completion. The recovery, when reached, `BIND`s the payload (so `onRaise`
  sees it at index 0), runs `onRaise`, `UNBIND`s, and continues with `c`.
* `perform ℓ argE` → `compile argE (THROW ℓ :: c)`: evaluate the payload, then
  `THROW ℓ` unwinds the handler stack to the nearest ℓ-frame, restores its
  env+stack, pushes the payload, and jumps to its recovery. `c` is discarded — the
  continuation is abandoned (zero-shot). No matching frame ⇒ an uncaught effect. -/

inductive Instr where
  | PUSH   : Int → Instr
  | ADD    : Instr
  | LOOKUP : Nat → Instr
  | BIND   : Instr
  | UNBIND : Instr
  | MARK   : Label → List Instr → Instr   -- install a handler: label + recovery code
  | UNMARK : Instr                         -- pop the handler frame (body finished normally)
  | THROW  : Label → Instr                 -- unwind to the nearest handler for the label
deriving Inhabited

abbrev Code  := List Instr
abbrev Stack := List Int

/-- A handler frame on the machine's handler stack: the label it catches, its
recovery code, and the env+value-stack to restore on unwinding. -/
structure Frame where
  label : Label
  recovery : Code
  savedEnv : Env
  savedStack : Stack
deriving Inhabited

abbrev HStack := List Frame

/-- The machine's outcome: a normal halt (final value stack) or an effect that
escaped every handler. -/
inductive Result where
  | halt     : Stack → Result
  | uncaught : Label → Int → Result
deriving Repr, DecidableEq, Inhabited

def compile : Src → Code → Code
  | .val n,       c => Instr.PUSH n :: c
  | .add x y,     c => compile x (compile y (Instr.ADD :: c))
  | .var i,       c => Instr.LOOKUP i :: c
  | .letE e1 e2,  c => compile e1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c))
  | .perform l e, c => compile e (Instr.THROW l :: c)
  | .handle l onRaise body, c =>
      Instr.MARK l (Instr.BIND :: compile onRaise (Instr.UNBIND :: c))
        :: compile body (Instr.UNMARK :: c)

/-- Unwind the handler stack to the nearest frame catching `l`; restore its
env+stack, push the payload, and run its recovery. No frame ⇒ uncaught. -/
def unwind (exec : Code → Env → Stack → HStack → Option Result)
    (l : Label) (p : Int) : HStack → Option Result
  | []          => some (.uncaught l p)
  | fr :: hs    =>
      if fr.label = l
      then exec fr.recovery fr.savedEnv (p :: fr.savedStack) hs
      else unwind exec l p hs

/-- The machine. Fuel-bounded (`THROW` jumps to recovery code). -/
def exec : Nat → Code → Env → Stack → HStack → Option Result
  | 0,    _,       _,   _, _  => none
  | _+1,  [],      _,   s, _  => some (.halt s)
  | f+1,  i :: c,  env, s, hs =>
    match i, s with
    | Instr.PUSH n,   s              => exec f c env (n :: s) hs
    | Instr.ADD,      (b :: a :: s)  => exec f c env ((a + b) :: s) hs
    | Instr.LOOKUP i, s              => match env[i]? with
                                        | some v => exec f c env (v :: s) hs
                                        | none   => none
    | Instr.BIND,     (v :: s)       => exec f c (v :: env) s hs
    | Instr.UNBIND,   s              => match env with
                                        | _ :: env' => exec f c env' s hs
                                        | []        => none
    | Instr.MARK l rec, s            => exec f c env s ({ label := l, recovery := rec,
                                                          savedEnv := env, savedStack := s } :: hs)
    | Instr.UNMARK,   s              => match hs with
                                        | _ :: hs' => exec f c env s hs'   -- drop the handler frame
                                        | []       => none
    | Instr.THROW l,  (p :: _)       => unwind (exec f) l p hs
    | _,              _              => none                                -- stuck
  termination_by fuel => fuel
  decreasing_by all_goals simp_wf

/-- Run a closed program: enough fuel, empty env/stack/handler-stack. -/
def run (fuel : Nat) (e : Src) : Option Result := exec fuel (compile e []) [] [] []

/-! ## Correctness (PROOF PENDING — harness-green, proof is the next step)

The handler machine is calculated and **differentially tested green** against the
reference `eval` (`evaleff` vs `execeff`: catch / forward / nest / recover /
uncaught + a fuzz) — the standing guarantee (invariant 1).

The Lean equivalence `compile_correct` (below) is shipped as `sorry` with a plan,
as each machine first was. It is the **hardest so far** — the new complexity is
the **handler stack + unwinding**, so the simulation is *two-part* (reuses the
playbook fuel-alignment, adds an exc/unwind invariant):

* **`exec_succ`/`exec_mono`** — fuel monotonicity; the `THROW` arm recurses through
  `unwind` (which itself recurses on the handler stack).
* **`sim`** — by induction on `e`, two outcomes proved together:
  - *ret*: `eval env e = ret v → ∀ c s hs F r, exec F c env (v::s) hs = some r →
    ∃ F', exec F' (compile e c) env s hs = some r` (as before, now carrying `hs`);
  - *exc*: `eval env e = exc ℓ p → ∀ c s hs, ∃ F', exec F' (compile e c) env s hs
    = unwind … ℓ p hs` — a raise compiles to a `THROW` that unwinds `hs` exactly as
    `eval`'s exception propagates. The `handle` case links the two: a caught
    exception (eval runs the recovery) matches the machine unwinding to that frame
    and running its recovery code; `MARK`/`UNMARK` bracket the body.
* **`compile_correct`** — corollary: `run` halts on `[v]` for `ret v`, and reports
  `uncaught ℓ p` for `exc ℓ p`. -/

/-- Map a reference `Outcome` to the machine `Result` it should produce. -/
def outcomeToResult : Outcome → Result
  | .ret n   => .halt [n]
  | .exc l p => .uncaught l p

theorem compile_correct (e : Src) :
    ∃ F, run F e = some (outcomeToResult (eval [] e)) := by
  sorry

end Bang.CalcEff
