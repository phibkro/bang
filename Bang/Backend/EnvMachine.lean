module

public import Bang.Core.Semantics
public import Bang.Backend.AbstractMachine

-- The mini-Agree `#guard`s run `runE`/`Source.eval` (compiled code) at the META phase, so the
-- modules providing the compiled call-chain (`Comp` constructors, `Comp.substFrom`, `Source.eval`,
-- `idDispatch`) must be `meta import`ed too — same shape as `Bang/Core/Semantics/Eval.lean`'s
-- `capMigrate*` guards, the cross-module `#guard` codegen wall.
meta import Bang.Core.Semantics

/-!
# EnvMachine — the environment/closure calculated machine (ADR-0094, #61 fix)

## THE DESIGN PIN (slice 1 — state it falsifiably; this file confirms it by build + probe)

ADR-0094 fixes #61's measured cliff (per-step `Comp.subst` at ~1 ms/step —
O(knot-body-size) per unfold; `docs/notes/hang-61-diagnosis.md`) by moving the
**calculated-machine** reduction from whole-term substitution to
**environment lookup + closures**, leaving `Source.eval` as the unchanged
substitution SPEC (option A1 of `docs/notes/envsem-survey.md`).

**The pin (falsifiable):** closures CANNOT live in kernel `Val` — the census is
26 constructors and untouchable (invariant #5; `tools/check-primitives.sh`) — so
the machine layer gets its OWN value domain, `MVal`, with a closure constructor
(`mvclos M ρ`) carrying an environment `ρ : MEnv`, embeddings *into* it (`evalV`,
which closes a syntactic `Val` under `ρ`) and READBACK *out* of it (`readback`,
the observation boundary that maps an `MVal` back to a kernel `Val`). PLFA's
`clos M γ` IS literally a separate domain (`@wadler-kokke-plfa-bigstep`); this is
the standard CESK shape (Van Horn–Might, Ager et al.). **Confirmation** = this
file builds EXIT 0 (the domain + `evalE` + `readback` typecheck) AND the mini-Agree
`#guard` below passes (a pure program through `evalE`/`readback` ≡ `Source.eval`).

**FALLBACK if the pin fails on a wall that can't be routed:** ADR-0094 §D names
thunk-sharing memoization (option D) as the priced fallback — STOP-and-SHOW before
switching, never silently.

## Slice 1 scope — the PURE fragment ONLY

`evalE` here covers `ret`/`lam`/`app`/`letC`/`force` (+ the ADT value formers, which
are pure structural data). The EFFECT arms (`perform`/`handle`/state/txn/custom) and
the id-first OP dispatch are slice 2 — the Stage-4 κ machinery is
representation-orthogonal and should thread unchanged onto this env-shaped focus.

The `evalE_agrees_evalD` **correspondence STATEMENT** (the PLFA `γ≈ₑσ` shape) compiles
here with a `sorry` body — proving it is slice 3, and its statement must generalize
from the empty env to an arbitrary `ρ` + the `≈ₑ` premise for the induction to fire
(PLFA's own warning, `envsem-survey.md` §2).

## Why this is a NEW file, not an edit to `evalD`

The existing substitution `evalD` (`AbstractMachine.lean`) is load-bearing for the
whole landed spine up to `evalD_agrees_source`. Slice 1 introduces the env machine
ALONGSIDE it (parallel, non-invasive); the re-derivation of `compile`/`exec`/the
bridge over `evalE` is slices 3–4. Nothing in `AbstractMachine.lean` is touched.
-/

namespace Bang.EnvMachine

open Bang (Val Comp Result BinOp)

-- Module reveal: the env-machine defs (`MVal`/`MEnv`/`evalV`/`evalE`/`readback`/`runE`) are unfolded
-- by the `#guard` codegen and the (slice-3) correspondence proof, so bodies cross the boundary.
@[expose] public section

/-! ## The machine value domain (the pin's separate domain)

`MVal` mirrors the kernel `Val` census EXCEPT: the binding-carrying suspended
computation `vthunk M` becomes a **closure** `mvclos M ρ` — a `Comp` paired with the
environment it closed over. `vvar` VANISHES from `MVal`: environment values are
*ground* (a de Bruijn index is resolved to an `MVal` by env lookup during eval, never
stored as a value). This is the CESK invariant. Kernel `Val`'s `vcap n ℓ` rides across
unchanged (a closed identity, no env). -/
mutual
inductive MVal : Type where
  | mvunit : MVal
  | mvint  : Int → MVal
  | mvcap  : Nat → Bang.EffectRow.Label → MVal
  -- the closure: `vthunk M`'s env analog — a suspended `Comp` M plus the env ρ it captured.
  | mvclos : Comp → MEnv → MVal
  -- structural ADT value formers (pure data over MVal), mirroring kernel Val.
  | minl   : MVal → MVal
  | minr   : MVal → MVal
  | mpair  : MVal → MVal → MVal
  | mfold  : MVal → MVal
/-- The environment: a de Bruijn-indexed list of ground machine values (index 0 = nearest binder). -/
inductive MEnv : Type where
  | nil  : MEnv
  | cons : MVal → MEnv → MEnv
end

instance : Inhabited MVal := ⟨.mvunit⟩
instance : Inhabited MEnv := ⟨.nil⟩

@[inherit_doc] infixr:67 " ∷ₑ " => MEnv.cons

namespace MEnv

/-- Lookup the `i`-th environment entry (0 = nearest binder). Out-of-range ⇒ `mvunit`
(source-unreachable for a closed, well-scoped program — the env always covers its free vars). -/
def get : MEnv → Nat → MVal
  | .nil,       _       => .mvunit
  | .cons v _,  0       => v
  | .cons _ ρ,  (n + 1) => get ρ n

end MEnv

/-! ## Embedding IN: close a syntactic `Val` under an environment

`evalV ρ v` resolves `v`'s free variables against `ρ`, producing a ground `MVal`.
The ONLY constructor that captures the env is `vthunk M ↦ mvclos M ρ` — every other
former is structural. `vvar i ↦ ρ.get i` is the O(1) lookup that replaces the O(body)
`Comp.subst`, dissolving #61's per-step cost (survey §5). -/
def evalV (ρ : MEnv) : Val → MVal
  | .vunit      => .mvunit
  | .vint n     => .mvint n
  | .vvar i     => ρ.get i
  | .vcap n ℓ   => .mvcap n ℓ
  | .vthunk M   => .mvclos M ρ                 -- CAPTURE: the closure closes M over the current env
  | .inl w      => .minl (evalV ρ w)
  | .inr w      => .minr (evalV ρ w)
  | .pair w₁ w₂ => .mpair (evalV ρ w₁) (evalV ρ w₂)
  | .fold w     => .mfold (evalV ρ w)

/-! ## The eval terminal

A pure computation runs to one of two terminals: a returner `mret mv` (a `ret v`
produced value `mv`) or a function `mlam M ρ` (a `lam M` closed over `ρ` — the
function-closure). Mirrors `evalD`'s `Outcome.term (ret v | lam M)`, env-shaped. -/
inductive MTerm : Type where
  | mret : MVal → MTerm            -- a returner produced this machine value
  | mlam : Comp → MEnv → MTerm     -- a function: body M closed over env ρ
  deriving Inhabited

/-! ## `evalE` — the environment big-step over the PURE fragment

Fuel-indexed (mirrors `evalD`'s outer `Nat`), threading only the environment `ρ`
(the effect stores σ/τ/κ arrive in slice 2). Reduction is LOOKUP, never whole-term
substitution:

* `ret v`   → `mret (evalV ρ v)`         (close the returned value under ρ)
* `lam M`   → `mlam M ρ`                 (close the function body over ρ)
* `letC M N`→ run M to `mret mv`; run N under `mv ∷ ρ`   (bind, don't subst)
* `app M v` → run M to `mlam N ρ'`; run N under `evalV ρ v ∷ ρ'`  (β = extend the closure env)
* `force w` → `evalV ρ w` must be `mvclos M ρ'`; run M under ρ'   (force = enter the closure)
* ADT elims (`case`/`split`/`unfold`) → scrutinee is a value; bind its components, run the branch.
* `binop`   → δ-rule on `mvint`s (pure).

Non-pure focuses (`perform`/`handle`) ⇒ `none` here (slice-1 out-of-scope; slice 2 adds them). -/
def evalE : Nat → MEnv → Comp → Option MTerm
  | 0,          _, _          => none
  | Nat.succ _, ρ, .ret v     => some (.mret (evalV ρ v))
  | Nat.succ _, ρ, .lam M     => some (.mlam M ρ)
  | Nat.succ f, ρ, .letC M N  =>
      (evalE f ρ M).bind (fun t => match t with
        | .mret mv    => evalE f (mv ∷ₑ ρ) N          -- BIND the returned value; run the continuation
        | .mlam _ _   => none)                          -- ill-typed: letC of a function
  | Nat.succ f, ρ, .app M v   =>
      (evalE f ρ M).bind (fun t => match t with
        | .mlam N ρ'  => evalE f (evalV ρ v ∷ₑ ρ') N   -- β: extend the CLOSURE's env with the argument
        | .mret _     => none)                          -- ill-typed: app of a non-function
  | Nat.succ f, ρ, .force w   =>
      match evalV ρ w with
      | .mvclos M ρ' => evalE f ρ' M                    -- force = enter the closure (run M under its captured env)
      | _            => none                             -- ill-typed: force of a non-thunk value
  -- ADT eliminators (pure — the scrutinee is a value; bind its components, run the branch).
  | Nat.succ f, ρ, .case w N₁ N₂ =>
      match evalV ρ w with
      | .minl mv => evalE f (mv ∷ₑ ρ) N₁
      | .minr mv => evalE f (mv ∷ₑ ρ) N₂
      | _        => none
  | Nat.succ f, ρ, .split w N =>
      match evalV ρ w with
      -- N binds fst at idx 1, snd at idx 0 (kernel convention, IR.lean:132 / the nested `Comp.subst`
      -- in evalD's split arm): index 0 = nearest = snd, so push SND at the head, FST behind it.
      | .mpair mv mw => evalE f (mw ∷ₑ mv ∷ₑ ρ) N
      | _            => none
  | Nat.succ _, ρ, .unfold w =>
      match evalV ρ w with
      | .mfold mv => some (.mret mv)
      | _         => none
  -- δ-rule (ADR-0065): binop on two ints (pure).
  | Nat.succ _, ρ, .binop op v w =>
      match evalV ρ v, evalV ρ w with
      | .mvint a, .mvint b => some (.mret (evalVOfBinop (op.eval a b)))
      | _,        _        => none
  | _,          _, _          => none              -- perform/handle/oom/wrong: out of slice-1 scope
where
  /-- `BinOp.eval` yields a kernel `Val` (`vint`/`boolVal`); lift it into `MVal` (closed, ρ-free —
  the δ-result is always a ground first-order value: `mvint` or a `bool` = `minl/minr mvunit`). -/
  evalVOfBinop : Val → MVal
    | .vint n     => .mvint n
    | .inl w      => .minl (evalVOfBinop w)
    | .inr w      => .minr (evalVOfBinop w)
    | .vunit      => .mvunit
    | _           => .mvunit                          -- unreachable: BinOp.eval only makes vint/bool

/-! ## Embedding OUT: readback (the observation boundary)

`readback : MVal → Val` maps a machine value back to a kernel `Val` — the boundary at
which `Agree`/`evalD_agrees_source` observe a result. On GROUND first-order data
(`mvunit`/`mvint`/caps/sums/products/folds) it is a structural relabelling. On a
CLOSURE `mvclos M ρ` it must reconstruct the substitution the closure defers: apply
the readback-env as a parallel substitution into `M`, i.e. `vthunk (M with ρ read back
and substituted)`. Slice 1 only OBSERVES first-order results (what the mini-Agree probe
and #61's JSON dogfood produce), so the closure arm is stated with the intended shape
and left as the point where the env↔subst correspondence (slice 3) is discharged.

The closure readback uses `readbackEnv ρ` — the list of read-back env values — fed to a
parallel substitution `substEnv`. Defining `substEnv` faithfully (it must reproduce the
`Comp.subst`-composition the env defers) is slice-3 work; here it is a labelled PLACEHOLDER
(identity) so the STATEMENT-level readback typechecks and the correspondence can be phrased. -/

/-- Parallel substitution of a readback-env `γ : List Val` into `M` — the reconstruction of the
`Comp.subst`-composition a closure defers. **Slice-3 obligation** (the env↔subst correspondence
core): faithful `substEnv` reproduces, on the closure body, exactly the substitutions env-lookup
elided. A labelled IDENTITY PLACEHOLDER at probe stage so `readback`'s closure arm + the `γ≈ₑσ`
statement typecheck; first-order readback (all the mini-Agree probe and #61 dogfood observe) never
reaches it, and the correspondence theorem carrying it is itself `sorry` (slice 3). -/
def substEnv (_γ : List Val) (M : Comp) : Comp := M   -- PLACEHOLDER: slice-3 replaces with the faithful fold

mutual
def readback : MVal → Val
  | .mvunit       => .vunit
  | .mvint n      => .vint n
  | .mvcap n ℓ    => .vcap n ℓ
  | .minl w       => .inl (readback w)
  | .minr w       => .inr (readback w)
  | .mpair w₁ w₂  => .pair (readback w₁) (readback w₂)
  | .mfold w      => .fold (readback w)
  -- CLOSURE readback: `vthunk (M under the read-back env, substituted in)`. The faithful
  -- `substEnv` is slice-3 (the env↔subst correspondence core); stated here so first-order
  -- readback + the correspondence statement compile.
  | .mvclos M ρ   => .vthunk (substEnv (readbackEnv ρ) M)
def readbackEnv : MEnv → List Val
  | .nil       => []
  | .cons v ρ  => readback v :: readbackEnv ρ
end

/-! ## The `γ≈ₑσ` correspondence — the STATEMENT (slice-3 proof)

The load-bearing bridge (PLFA `BigStep`, `envsem-survey.md` §2): an environment `ρ`
*corresponds* to a kernel substitution `σ : List Val` when reading back each env entry
gives the matching substitution entry. Then env-eval and the substitution reference
agree at the readback boundary. -/

/-- `ρ ≈ₑ σ` — the environment/substitution agreement. Pointwise: reading back `ρ`'s entries
reproduces `σ`. This IS the env/closure well-formedness invariant the env machine carries
(survey §2: "for any variable x, the closure γ x is equivalent to the term σ x"). -/
def EnvAgrees (ρ : MEnv) (σ : List Val) : Prop := readbackEnv ρ = σ

/-- **The correspondence STATEMENT** (PLFA `γ≈ₑσ`; slice-3 proof).

If `evalE` runs `M` under `ρ` to a returner `mret mv`, and `ρ` agrees with a substitution
`σ`, then the substitution reference `evalD` (over the σ-substituted term) returns the
read-back value. Generalized from the empty env to an arbitrary `ρ`/`σ` per PLFA's warning
(the induction won't fire on the empty-env special case).

`sorry` body — this is the slice-3 obligation; slice 1 confirms only that the statement
TYPECHECKS (the domains + readback compose) and that the mini-Agree probe below holds
concretely. -/
theorem evalE_agrees_evalD (f : Nat) (ρ : MEnv) (σ : List Val) (M : Comp) (mv : MVal)
    (_hagree : EnvAgrees ρ σ)
    (_h : evalE f ρ M = some (.mret mv)) :
    ∃ F g' σ' τ' κ',
      Bang.CalcVM.evalD F 0 [] [] [] (substEnv σ M)
        = some (.term (.ret (readback mv)), g', σ', τ', κ') := by
  sorry -- SLICE-3: the PLFA γ≈ₑσ induction (generalize-from-empty-env; env↔subst correspondence)

/-! ## Mini-Agree probe — the PIN'S EXECUTABLE CONFIRMATION

A pure program run through `evalE` + `readback` must yield the same value the verified
`Source.eval` reference produces. This is the *necessary* value-agreement check that
de-risks the whole env representation before the big weave (working-method: refute-first
with the executable oracle). A green `#guard` here IS the pin confirmed for the pure
fragment; a red one refutes the domain shape for the price of this file.

`runE` closes an empty-env eval and reads back a returner to a `Result Val`, exactly the
shape `Source.eval` yields, so the two are directly comparable. -/
def runE (fuel : Nat) (M : Comp) : Result Val :=
  match evalE fuel .nil M with
  | some (.mret mv) => .done (readback mv)
  | _               => .stuck              -- a function-terminal or stuck: no first-order value

/-- `runE` and `Source.eval` agree on a pure program (the mini-Agree). -/
def MiniAgree (fuel : Nat) (M : Comp) (v : Val) : Prop :=
  runE fuel M = .done v ∧ Bang.Source.eval fuel M = .done v

/-- `runE` yields exactly `done (vint n)` (Bool projector — `Val` derives only `Inhabited`, so no
`DecidableEq`; mirrors the kernel's `yieldsInt`). BOTH `runE` and `Source.eval` are compared through
this same projector so a green `#guard` witnesses value-agreement without decidable `Val` equality. -/
private def yieldsIntE (r : Result Val) (n : Int) : Bool :=
  match r with | .done (.vint m) => m == n | _ => false

-- Each guard asserts BOTH engines project to the same int — the mini-Agree, `#guard`-gated.
-- ── β through a closure: `(λ. ret #0) 5` ⇒ 5 (app extends the closure env; ret reads #0 back). ──
#guard yieldsIntE (runE 8 (.app (.lam (.ret (.vvar 0))) (.vint 5))) 5
#guard yieldsIntE (Bang.Source.eval 8 (.app (.lam (.ret (.vvar 0))) (.vint 5))) 5

-- ── let-binding: `let x = (λ.ret #0) 5 in ret x` ⇒ 5 (letC binds; no whole-body subst). ──
#guard yieldsIntE (runE 10 (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0)))) 5
#guard yieldsIntE (Bang.Source.eval 10 (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0)))) 5

-- ── force∘thunk: `force (thunk (ret 9))` ⇒ 9 (force = enter the closure `mvclos (ret 9) ρ`). ──
#guard yieldsIntE (runE 8 (.force (.vthunk (.ret (.vint 9))))) 9
#guard yieldsIntE (Bang.Source.eval 8 (.force (.vthunk (.ret (.vint 9))))) 9

-- ── a nested closure that CAPTURES its env: `let x = 7 in force (thunk (ret x))` ⇒ 7.
--    The thunk closes over ρ = [7]; forcing it reads #0 from the captured env — the exact
--    env-capture the substitution machine did by copying `x` into the thunk body. ──
#guard yieldsIntE (runE 12 (.letC (.ret (.vint 7)) (.force (.vthunk (.ret (.vvar 0)))))) 7
#guard yieldsIntE (Bang.Source.eval 12 (.letC (.ret (.vint 7)) (.force (.vthunk (.ret (.vvar 0)))))) 7

-- ── δ-rule through binds: `let a = 3 in let b = 4 in a + b` ⇒ 7. ──
#guard yieldsIntE (runE 14
  (.letC (.ret (.vint 3)) (.letC (.ret (.vint 4)) (.binop .add (.vvar 1) (.vvar 0))))) 7
#guard yieldsIntE (Bang.Source.eval 14
  (.letC (.ret (.vint 3)) (.letC (.ret (.vint 4)) (.binop .add (.vvar 1) (.vvar 0))))) 7

-- ── ADT: `case (inl 5) of inl x => x | inr _ => 99` ⇒ 5. ──
#guard yieldsIntE (runE 8 (.case (.inl (.vint 5)) (.ret (.vvar 0)) (.ret (.vint 99)))) 5
#guard yieldsIntE (Bang.Source.eval 8 (.case (.inl (.vint 5)) (.ret (.vvar 0)) (.ret (.vint 99)))) 5

-- ── product: `split (3,4) as (a,b) in a` ⇒ 3 (split binds fst@1, snd@0). ──
#guard yieldsIntE (runE 8 (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1)))) 3
#guard yieldsIntE (Bang.Source.eval 8 (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1)))) 3

/-- The mini-Agree, tying `runE` to `Source.eval` on the β case (both `.done (vint 5)`) — the
env machine's readback ≡ the verified substitution reference on the pure fragment. -/
example : MiniAgree 12 (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.vint 5) := ⟨by rfl, by rfl⟩

/-- The env-capture mini-Agree: `let x = 7 in force (thunk (ret x))` ⇒ 7 through BOTH engines.
This is the load-bearing witness — the closure captured `x` from the env, and reading it back
gives the same value the substitution reference got by copying `x` into the thunk body. -/
example : MiniAgree 14 (.letC (.ret (.vint 7)) (.force (.vthunk (.ret (.vvar 0))))) (.vint 7) :=
  ⟨by rfl, by rfl⟩

end -- public section
end Bang.EnvMachine
