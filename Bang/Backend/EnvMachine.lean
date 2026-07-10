module

public import Bang.Core.Semantics
public import Bang.Backend.AbstractMachine

-- The mini-Agree `#guard`s run `runE`/`Source.eval` (compiled code) at the META phase, so the
-- modules providing the compiled call-chain must be `meta import`ed too — same shape as
-- `Bang/Core/Semantics/Eval.lean`'s `capMigrate*` guards, the cross-module `#guard` codegen wall.
-- Semantics: `Comp` constructors, `Comp.substFrom`, `Source.eval`, `idDispatch`.
-- AbstractMachine: `isTxnOp` (the txn-op guard `evalE` shares — single source of truth, not re-defined).
meta import Bang.Core.Semantics
meta import Bang.Backend.AbstractMachine

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

/-! ## The eval terminal + outcome

A pure computation runs to one of two terminals: a returner `mret mv` (a `ret v`
produced value `mv`) or a function `mlam M ρ` (a `lam M` closed over `ρ` — the
function-closure). Mirrors `evalD`'s `Outcome.term (ret v | lam M)`, env-shaped. -/
inductive MTerm : Type where
  | mret : MVal → MTerm            -- a returner produced this machine value
  | mlam : Comp → MEnv → MTerm     -- a function: body M closed over env ρ
  deriving Inhabited

/-- The env-machine outcome — the exact env-shaped image of `evalD`'s `Outcome`
(`AbstractMachine.lean`): a normal `mterm` terminal, or a `mraised n op mv` — a
throws-`up` en route to handler IDENTITY `n` (route-B, ADR-0052; the payload is an `MVal`).
`letC`/`app` short-circuit on `mraised`; `handle`'s throws arm catches it. -/
inductive MOutcome : Type where
  | mterm   : MTerm → MOutcome
  | mraised : Nat → Bang.OpId → MVal → MOutcome
  deriving Inhabited

/-! ## The env-shaped effect stores (slice 2)

The exact env images of `evalD`'s `SStore`/`THeap`/`CStore` (`AbstractMachine.lean`),
keyed by capability IDENTITY (`Nat`, globally fresh) — the KIND-FIRST-STORES idiom
carries over unchanged (per-kind stores matching per-kind dispatch). The ONLY
representational change is the payload type: kernel `Val` becomes machine `MVal`, and
the CUSTOM store additionally carries the install-time environment `MEnv` the clause
bodies closed over (the closure again: a clause `Comp` has free vars — param at idx 1,
op-arg at idx 0 — over whatever env was live at `handle`-install). Op-disjointness across
kinds (state/txn/custom op-sets disjoint) makes the three parallel stores sound exactly as
in `evalD` — a shared label resolves unambiguously by op-id within the resolved frame. -/
abbrev ESStore := List (Nat × MVal)                                    -- state cells (σ image)
abbrev ETHeap  := List (Nat × List MVal)                               -- txn heaps  (τ image)
abbrev ECStore := List (Nat × (MVal × List (Bang.OpId × Comp) × MEnv)) -- custom frames (κ image): (param, clauses, install-env)

/-- Nearest stored state cell for identity `n` (innermost wins; ids are globally fresh ⇒ unique). -/
def ESStore.get? (σ : ESStore) (n : Nat) : Option MVal := (σ.find? (·.1 = n)).map (·.2)
/-- In-place update the nearest state cell for `n` (mirrors `SStore.put`; unbound ⇒ unchanged). -/
def ESStore.put : ESStore → Nat → MVal → ESStore
  | [],            _, _ => []
  | (n0, w) :: σ, n, v => if n0 = n then (n0, v) :: σ else (n0, w) :: ESStore.put σ n v

/-- Nearest stored txn heap for identity `n`. -/
def ETHeap.get? (τ : ETHeap) (n : Nat) : Option (List MVal) := (τ.find? (·.1 = n)).map (·.2)
/-- In-place update the nearest txn heap for `n` (mirrors `THeap.put`). -/
def ETHeap.put : ETHeap → Nat → List MVal → ETHeap
  | [],            _, _ => []
  | (n0, w) :: τ, n, Θ => if n0 = n then (n0, Θ) :: τ else (n0, w) :: ETHeap.put τ n Θ

/-- Nearest stored custom frame `(param, clauses, install-env)` for identity `n`. -/
def ECStore.get? (κ : ECStore) (n : Nat) : Option (MVal × List (Bang.OpId × Comp) × MEnv) :=
  (κ.find? (·.1 = n)).map (·.2)

/-- Read a TVar index (an `mvint i`) out of a machine value (`mtvarIdx`; the `MVal` image of
`tvarIdx`). Malformed ⇒ `none`. -/
def mtvarIdx : MVal → Option Nat
  | .mvint n => if n ≥ 0 then some n.toNat else none
  | _        => none

/-- Service a transaction op against a machine heap `Θ` (the `MVal` image of `txnService`,
`AbstractMachine.lean`): `newTVar v` appends+returns the index; `readTVar (mvint i)` reads cell `i`
(TOTAL, default `mvint 0`); `writeTVar (mpair (mvint i) w)` sets cell `i`, returns unit. -/
def mtxnService (op : Bang.OpId) (v : MVal) (Θ : List MVal) : MVal × List MVal :=
  if op = "newTVar" then (.mvint Θ.length, Θ ++ [v])
  else if op = "readTVar" then (Θ.getD ((mtvarIdx v).getD 0) (.mvint 0), Θ)
  else
    match v with
    | .mpair iv w => (.mvunit, Θ.set ((mtvarIdx iv).getD 0) w)
    | _           => (.mvunit, Θ)

/-! ## `evalE` — the environment big-step (pure fragment + EFFECT ARMS, slice 2)

Fuel-indexed (mirrors `evalD`'s outer `Nat`), now threading the fresh-id counter `g`, the
three MVal-keyed effect stores (σ/τ/κ), AND the environment `ρ` — the exact env image of
`evalD`'s state. Reduction is env LOOKUP, never whole-term substitution. **The id-first
dispatch order is PRESERVED EXACTLY** (operator-ruled, freshly proven; the env rework must
not perturb it): `perform (vcap n ℓ)` resolves by IDENTITY `n` through σ→τ→κ in order; the
op selects the operation WITHIN the resolved frame's kind; an op the resolved kind does not
handle RAISES (fail-loud, never falls through to another store).

* `ret`/`lam`/`app`/`letC`/`force`/ADT/`binop` — the pure fragment (slice 1), now `mraised`-
  short-circuiting on `letC`/`app` (mirrors `evalD`).
* `perform (vcap n) op v` — id-first σ→τ→κ dispatch; state get/put, txn service, custom
  INLINE clause-service run under the frame's install-env (`arg ∷ param ∷ ρ_install`).
* `handle h M` — MINT `id := g`, BIND `mvcap id ℓ` into ρ at index 0 (the env analog of
  `evalD`'s `subst (vcap id ℓ) M`), recurse with `g+1`; push/pop the per-kind store entry;
  throws CATCHES `mraised id "raise"` (zero-shot abort, KEEP the at-raise stores). -/
def evalE : Nat → Nat → ESStore → ETHeap → ECStore → MEnv → Comp →
    Option (MOutcome × Nat × ESStore × ETHeap × ECStore)
  | 0,          _, _, _, _, _, _          => none
  | Nat.succ _, g, σ, τ, κ, ρ, .ret v     => some (.mterm (.mret (evalV ρ v)), g, σ, τ, κ)
  | Nat.succ _, g, σ, τ, κ, ρ, .lam M     => some (.mterm (.mlam M ρ), g, σ, τ, κ)
  | Nat.succ f, g, σ, τ, κ, ρ, .letC M N  =>
      (evalE f g σ τ κ ρ M).bind (fun p => match p with
        | (.mterm (.mret mv), g', σ', τ', κ') => evalE f g' σ' τ' κ' (mv ∷ₑ ρ) N   -- BIND, run the continuation
        | (.mterm (.mlam _ _), _, _, _, _)    => none                               -- ill-typed: letC of a function
        | (.mraised n op w, g', σ', τ', κ')   => some (.mraised n op w, g', σ', τ', κ')) -- propagate the raise
  | Nat.succ f, g, σ, τ, κ, ρ, .app M v   =>
      (evalE f g σ τ κ ρ M).bind (fun p => match p with
        | (.mterm (.mlam N ρ'), g', σ', τ', κ') => evalE f g' σ' τ' κ' (evalV ρ v ∷ₑ ρ') N -- β: extend the closure env
        | (.mterm (.mret _), _, _, _, _)        => none                             -- ill-typed: app of a non-function
        | (.mraised n op w, g', σ', τ', κ')     => some (.mraised n op w, g', σ', τ', κ')) -- propagate the raise
  | Nat.succ f, g, σ, τ, κ, ρ, .force w   =>
      match evalV ρ w with
      | .mvclos M ρ' => evalE f g σ τ κ ρ' M            -- force = enter the closure (run M under its captured env)
      | _            => none                             -- ill-typed: force of a non-thunk value
  -- perform (vcap n ℓ) op v: dispatch BY IDENTITY n, σ→τ→κ IN ORDER (route-B, id-first — PRESERVED
  -- EXACTLY from evalD). The op selects the operation WITHIN the resolved kind; an op the resolved
  -- kind doesn't handle RAISES (fail-loud), never falls through. n in no store ⇒ raise.
  | Nat.succ f, g, σ, τ, κ, ρ, .perform w op v =>
      match evalV ρ w with
      | .mvcap n _ℓ =>
          let arg := evalV ρ v
          match σ.get? n with
          -- STATE frame: get returns the cell (σ unchanged); put threads cell := arg in place; else raise.
          | some s =>
              if op = "get" then some (.mterm (.mret s), g, σ, τ, κ)
              else if op = "put" then some (.mterm (.mret .mvunit), g, σ.put n arg, τ, κ)
              else some (.mraised n op arg, g, σ, τ, κ)
          | none =>
          match τ.get? n with
          -- TRANSACTION frame: service the stm op against the heap, thread Θ := Θ' in place; else raise.
          | some Θ =>
              if Bang.CalcVM.isTxnOp op then
                let (r, Θ') := mtxnService op arg Θ
                some (.mterm (.mret r), g, σ, τ.put n Θ', κ)
              else some (.mraised n op arg, g, σ, τ, κ)
          | none =>
          match κ.get? n with
          -- CUSTOM frame: INLINE-SERVICE the clause under the frame's INSTALL-ENV (the closure over
          -- ρ_install captured at handle-install), binding op-arg at idx 0, param at idx 1 — the env
          -- image of evalD's `subst p (subst (shift v) clause.2)`. κ unchanged (frame stays live).
          | some (p, cls, ρ_inst) =>
              match cls.find? (·.1 == op) with
              | some clause => evalE f g σ τ κ (arg ∷ₑ p ∷ₑ ρ_inst) clause.2
              | none        => some (.mraised n op arg, g, σ, τ, κ)          -- op unserviced by this custom frame ⇒ raise
          | none => some (.mraised n op arg, g, σ, τ, κ)                     -- n in no store ⇒ raise
      | _ => none                                                            -- ill-typed: perform on a non-cap
  -- handle h M: MINT id := g, BIND `mvcap id ℓ` into ρ at index 0 (the env analog of evalD's
  -- `subst (vcap id ℓ) M` — handle binds the cap at idx 0, IR.lean:124), recurse with g+1; push/pop
  -- the per-kind store entry; throws CATCHES `mraised id "raise"` (zero-shot abort, keep at-raise stores).
  | Nat.succ f, g, σ, τ, κ, ρ, .handle h M =>
      let id := g
      let ρ' := MVal.mvcap id (Handler.label h) ∷ₑ ρ
      match h with
      | .state _ s =>
          (evalE f (g+1) (⟨id, evalV ρ s⟩ :: σ) τ κ ρ' M).bind (fun p => match p with
            | (.mterm (.mret v), g', σ', τ', κ')  => some (.mterm (.mret v), g', σ'.tail, τ', κ')  -- POP
            | (.mterm (.mlam _ _), _, _, _, _)    => none
            | (.mraised n op' w, g', σ', τ', κ')  => some (.mraised n op' w, g', σ'.tail, τ', κ'))  -- forward; pop
      | .transaction _ Θ =>
          (evalE f (g+1) σ (⟨id, Θ.map (evalV ρ)⟩ :: τ) κ ρ' M).bind (fun p => match p with
            | (.mterm (.mret v), g', σ', τ', κ')  => some (.mterm (.mret v), g', σ', τ'.tail, κ')  -- POP
            | (.mterm (.mlam _ _), _, _, _, _)    => none
            | (.mraised n op' w, g', σ', τ', κ')  => some (.mraised n op' w, g', σ', τ'.tail, κ'))  -- forward; pop
      | .custom _ p cls =>
          -- CUSTOM install: push (id ↦ (param, clauses, ρ)) — the clause bodies close over the CURRENT
          -- ρ (their install-env). POP on exit; a raise FORWARDS. Structural sibling of `state`.
          (evalE f (g+1) σ τ (⟨id, (evalV ρ p, cls, ρ)⟩ :: κ) ρ' M).bind (fun q => match q with
            | (.mterm (.mret v), g', σ', τ', κ')  => some (.mterm (.mret v), g', σ', τ', κ'.tail)  -- POP
            | (.mterm (.mlam _ _), _, _, _, _)    => none
            | (.mraised n op' w, g', σ', τ', κ')  => some (.mraised n op' w, g', σ', τ', κ'.tail))  -- forward; pop
      | .throws _ =>
          (evalE f (g+1) σ τ κ ρ' M).bind (fun p => match p with
            | (.mterm (.mret v), g', σ', τ', κ')  => some (.mterm (.mret v), g', σ', τ', κ')
            | (.mterm (.mlam _ _), _, _, _, _)    => none
            | (.mraised n op' w, g', σ', τ', κ')  =>
                -- CAUGHT (zero-shot abort) iff the raise targets THIS handler's identity. KEEP at-raise stores.
                if n = id ∧ op' = "raise" then some (.mterm (.mret w), g', σ', τ', κ')
                else some (.mraised n op' w, g', σ', τ', κ'))
  -- ADT eliminators (pure — the scrutinee is a value; bind its components, run the branch).
  | Nat.succ f, g, σ, τ, κ, ρ, .case w N₁ N₂ =>
      match evalV ρ w with
      | .minl mv => evalE f g σ τ κ (mv ∷ₑ ρ) N₁
      | .minr mv => evalE f g σ τ κ (mv ∷ₑ ρ) N₂
      | _        => none
  | Nat.succ f, g, σ, τ, κ, ρ, .split w N =>
      match evalV ρ w with
      -- N binds fst at idx 1, snd at idx 0 (kernel convention, IR.lean:132): index 0 = snd (head), fst behind.
      | .mpair mv mw => evalE f g σ τ κ (mw ∷ₑ mv ∷ₑ ρ) N
      | _            => none
  | Nat.succ _, g, σ, τ, κ, ρ, .unfold w =>
      match evalV ρ w with
      | .mfold mv => some (.mterm (.mret mv), g, σ, τ, κ)
      | _         => none
  -- δ-rule (ADR-0065): binop on two ints (pure).
  | Nat.succ _, g, σ, τ, κ, ρ, .binop op v w =>
      match evalV ρ v, evalV ρ w with
      | .mvint a, .mvint b => some (.mterm (.mret (evalVOfBinop (op.eval a b))), g, σ, τ, κ)
      | _,        _        => none
  | _,          _, _, _, _, _, _          => none              -- oom/wrong/ill-formed scrutinee
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

/-- Sequential substitution of a readback-env `γ : List Val` into `M` — the reconstruction of the
`Comp.subst`-composition a closure/environment defers. **Slice-3 core** (the env↔subst correspondence):
the env is `v₀ ∷ v₁ ∷ … ∷ nil` with `vᵢ` at de Bruijn index `i`; substituting it into `M` is filling
index 0 with `v₀` (which shifts what was index 1 down to index 0), then repeating for `v₁`, etc. So it
is a LEFT FOLD of the kernel's single `Comp.subst` over `γ` — exactly the composition `evalV`/`evalE`
elided by resolving each index to `ρ.get i` instead of copying. `substEnv [] M = M` (a closed term is
unchanged); this is the standard "environment = a pending simultaneous substitution" identity (PLFA
`BigStep`; Pierce TAPL §6.2 shift/subst calculus). -/
def substEnv : List Val → Comp → Comp
  | [],      M => M
  | v :: γ, M => substEnv γ (Comp.subst v M)

/-! ### The closing-substitution engine — TRANSPLANTED from the LR spine (task #15 retires it)

`substEnv` is BYTE-IDENTICAL to `Bang.Meta.LR.closeC`. The commutation lemma the correspondence
induction turns on (`substEnv_cons_subst` below) already exists as `Bang.Meta.BinaryLR.closeC_subst_comm`,
riding a `Val.Closed` swap engine. Per the operator ruling (2026-07-10, on task #11): the DESTINATION is
option (A) — hoist that engine to `Bang/Core/Semantics/Subst.lean` so LR and this machine share ONE
source — but SEQUENCED (s5grind is actively in `Bang/Meta/BinaryLR.lean`; two writers on one file is the
trap). So the engine is TRANSPLANTED here as a SANCTIONED, TRACKED duplicate; **task #15 hoists it to Core
and deletes these copies post-s5grind — the green build after retirement proves the duplicate was faithful.**
Every transplanted decl carries the `TODO(hoist, task #15)` marker. Bodies are verbatim from LR/BinaryLR
(behavior-preserving copies). -/

-- TODO(hoist, task #15): faithful duplicate of Bang.Meta.LR.Val.Closed engine — retired by the post-s5grind hoist.
/-- A value with no free de Bruijn indices (fixed by shift at every cutoff). -/
def Val.ClosedE (v : Val) : Prop := ∀ k, Val.shiftFrom k v = v

-- TODO(hoist, task #15): duplicate of Bang.Meta.LR.Val.Closed.{shift,shiftFrom_eq,subst_at}.
theorem Val.ClosedE.shift {v : Val} (h : Val.ClosedE v) : Val.shift v = v := h 0
theorem Val.ClosedE.shiftFrom_eq {v : Val} (h : Val.ClosedE v) (k : Nat) : Val.shiftFrom k v = v := h k
theorem Val.ClosedE.subst_at {v : Val} (h : Val.ClosedE v) (k : Nat) (w : Val) :
    Val.substFrom k w v = v := by
  conv_lhs => rw [← h.shiftFrom_eq k]; exact Bang.Val.substFrom_shiftFrom k w v

-- TODO(hoist, task #15): duplicate of Bang.Meta.BinaryLR.{shiftN,shiftN_closed}.
/-- Iterated `Val.shift` (weaken past `d` binders). -/
def shiftNE : Nat → Val → Val
  | 0,     v => v
  | d + 1, v => Val.shift (shiftNE d v)
theorem shiftNE_closed {v : Val} (h : Val.ClosedE v) : ∀ d, shiftNE d v = v
  | 0     => rfl
  | d + 1 => by show Val.shift (shiftNE d v) = v; rw [shiftNE_closed h d, h.shift]

-- TODO(hoist, task #15): duplicate of Bang.Meta.BinaryLR.closeCUnderBinders (`closeC` = substEnv here).
/-- Apply the closing env `δ` to a term sitting under `d` fresh binders (each filler weakened + substituted
at level `d`). `closeUnderBindersE 0 = substEnv`. -/
def closeUnderBindersE (d : Nat) : List Val → Comp → Comp
  | [],     c => c
  | v :: δ, c => closeUnderBindersE d δ (Comp.substFrom d (shiftNE d v) c)

-- TODO(hoist, task #15): duplicate of Bang.Meta.BinaryLR.{Val,Comp,Handler}.substFrom_swap_closed (ADJACENT swap).
mutual
theorem Val.substFrom_swap_closedE :
    ∀ {v w : Val}, Val.ClosedE v → Val.ClosedE w → ∀ (k : Nat) (t : Val),
      Val.substFrom k w (Val.substFrom (k + 1) v t) = Val.substFrom k v (Val.substFrom k w t)
  | _, _, _, _, _, .vunit => rfl
  | _, _, _, _, _, .vint _ => rfl
  | _, _, _, _, _, .vcap _ _ => rfl
  | v, w, hv, hw, k, .vvar i => by
      rcases Nat.lt_trichotomy i k with hlt | heq | hgt
      · simp only [Val.substFrom, if_neg (show ¬ i = k + 1 by omega), if_neg (show ¬ i > k + 1 by omega),
          if_neg (show ¬ i = k by omega), if_neg (show ¬ i > k by omega)]
      · subst heq
        simp only [Val.substFrom, if_neg (show ¬ i = i + 1 by omega), if_neg (show ¬ i > i + 1 by omega),
          if_true, hw.subst_at i v]
      · rcases Nat.lt_trichotomy i (k + 1) with hk1 | heq1 | hgt1
        · omega
        · subst heq1
          simp only [Val.substFrom, if_true, hv.subst_at k w,
            if_neg (show ¬ k + 1 = k by omega), if_pos (show k + 1 > k by omega), Nat.add_sub_cancel]
        · simp only [Val.substFrom, if_neg (show ¬ i = k + 1 by omega), if_pos (show i > k + 1 by omega),
            if_neg (show ¬ i = k by omega), if_pos (show i > k by omega),
            if_neg (show ¬ i - 1 = k by omega), if_pos (show i - 1 > k by omega)]
  | v, w, hv, hw, k, .vthunk M => by
      simp only [Val.substFrom]; rw [Comp.substFrom_swap_closedE hv hw k M]
  | v, w, hv, hw, k, .inl u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closedE hv hw k u]
  | v, w, hv, hw, k, .inr u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closedE hv hw k u]
  | v, w, hv, hw, k, .pair u₁ u₂ => by
      simp only [Val.substFrom]
      rw [Val.substFrom_swap_closedE hv hw k u₁, Val.substFrom_swap_closedE hv hw k u₂]
  | v, w, hv, hw, k, .fold u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closedE hv hw k u]
theorem Comp.substFrom_swap_closedE :
    ∀ {v w : Val}, Val.ClosedE v → Val.ClosedE w → ∀ (k : Nat) (t : Comp),
      Comp.substFrom k w (Comp.substFrom (k + 1) v t) = Comp.substFrom k v (Comp.substFrom k w t)
  | v, w, hv, hw, k, .ret u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closedE hv hw k u]
  | v, w, hv, hw, k, .binop op a b => by
      simp only [Comp.substFrom]; rw [Val.substFrom_swap_closedE hv hw k a, Val.substFrom_swap_closedE hv hw k b]
  | v, w, hv, hw, k, .letC M N => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Comp.substFrom_swap_closedE hv hw k M, Comp.substFrom_swap_closedE hv hw (k + 1) N]
  | v, w, hv, hw, k, .force u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closedE hv hw k u]
  | v, w, hv, hw, k, .lam M => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Comp.substFrom_swap_closedE hv hw (k + 1) M]
  | v, w, hv, hw, k, .app M u => by
      simp only [Comp.substFrom]
      rw [Comp.substFrom_swap_closedE hv hw k M, Val.substFrom_swap_closedE hv hw k u]
  | v, w, hv, hw, k, .perform cp op u => by
      simp only [Comp.substFrom]
      rw [Val.substFrom_swap_closedE hv hw k cp, Val.substFrom_swap_closedE hv hw k u]
  | v, w, hv, hw, k, .handle h M => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Handler.substFrom_swap_closedE hv hw k h, Comp.substFrom_swap_closedE hv hw (k + 1) M]
  | v, w, hv, hw, k, .case u N₁ N₂ => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Val.substFrom_swap_closedE hv hw k u,
        Comp.substFrom_swap_closedE hv hw (k + 1) N₁, Comp.substFrom_swap_closedE hv hw (k + 1) N₂]
  | v, w, hv, hw, k, .split u N => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Val.substFrom_swap_closedE hv hw k u, Comp.substFrom_swap_closedE hv hw (k + 2) N]
  | v, w, hv, hw, k, .unfold u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closedE hv hw k u]
  | _, _, _, _, _, .oom => rfl
  | _, _, _, _, _, .wrong _ => rfl
theorem Handler.substFrom_swap_closedE :
    ∀ {v w : Val}, Val.ClosedE v → Val.ClosedE w → ∀ (k : Nat) (h : Handler),
      Handler.substFrom k w (Handler.substFrom (k + 1) v h) = Handler.substFrom k v (Handler.substFrom k w h)
  | v, w, hv, hw, k, .state ℓ s => by simp only [Handler.substFrom]; rw [Val.substFrom_swap_closedE hv hw k s]
  | _, _, _, _, _, .throws _ => rfl
  | _, _, _, _, _, .transaction _ _ => rfl
  | _, _, _, _, _, .custom _ _ _ => rfl
end

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

/-- Readback of a machine TERMINAL to the substitution machine's `Outcome` (the general-terminal
correspondence target, ruling (A) 2026-07-10). A returner `mret mv` reads back to `ret (readback mv)`;
a function `mlam N ρ` reads back to `lam` of its body closed under ONE binder over the captured env
(`closeUnderBindersE 1 (readbackEnv ρ) N` — the env analog of evalD's `lam N` terminal). 3b's `mraised`
slots in when effects wire. -/
def readbackTerm : MTerm → Bang.CalcVM.Outcome
  | .mret mv   => .term (.ret (readback mv))
  | .mlam N ρ  => .term (.lam (closeUnderBindersE 1 (readbackEnv ρ) N))

/-! ## The `γ≈ₑσ` correspondence — the STATEMENT (slice-3 proof)

The load-bearing bridge (PLFA `BigStep`, `envsem-survey.md` §2): an environment `ρ`
*corresponds* to a kernel substitution `σ : List Val` when reading back each env entry
gives the matching substitution entry. Then env-eval and the substitution reference
agree at the readback boundary. -/

/-- `ρ ≈ₑ σ` — the environment/substitution agreement. Pointwise: reading back `ρ`'s entries
reproduces `σ`. This IS the env/closure well-formedness invariant the env machine carries
(survey §2: "for any variable x, the closure γ x is equivalent to the term σ x"). -/
def EnvAgrees (ρ : MEnv) (σ : List Val) : Prop := readbackEnv ρ = σ

/-! ### The substEnv calculus — the env↔subst commutation (slice-3 crux, transplanted engine)

`substEnv γ` commutes with pushing a fresh index-0 binder: the machine's `w ∷ₑ ρ` env-extension is
the substitution machine's `Comp.subst w` under a `closeUnderBindersE 1 γ` (the tail env lifted past
the new binder). This is the CRUX every binding case of the correspondence induction reduces to. The
proof is transplanted `closeC_subst_comm` (task #15 retires the copy); it needs each filler CLOSED —
the `Val.ClosedE` premise, TRUE by construction from readback (a ground MVal reads back to a closed
`Val`). -/

/-- `substEnv` on an empty env is the identity; on a cons it fills index 0 then folds the tail. -/
@[simp] theorem substEnv_nil (M : Comp) : substEnv [] M = M := rfl
@[simp] theorem substEnv_cons (v : Val) (γ : List Val) (M : Comp) :
    substEnv (v :: γ) M = substEnv γ (Comp.subst v M) := rfl

-- TODO(hoist, task #15): duplicate of Bang.Meta.BinaryLR.closeC_subst_comm, restated against substEnv.
/-- **THE CRUX** (= `closeC_subst_comm`): filling a fresh level-0 binder with a CLOSED `w` after applying
the closing env `γ` lifted past one binder equals applying `w :: γ` directly. Closes the binding cases of
`evalE_agrees_evalD` — the env-extension `w ∷ₑ ρ` matches `Comp.subst w` under the lifted tail. -/
theorem substEnv_cons_subst {γ : List Val} (hγ : ∀ v ∈ γ, Val.ClosedE v)
    {w : Val} (_hw : Val.ClosedE w) (N : Comp) :
    (closeUnderBindersE 1 γ N).subst w = substEnv (w :: γ) N := by
  -- substEnv (w :: γ) N = substEnv γ (Comp.subst w N); induction on γ (verbatim closeC_subst_comm).
  show (closeUnderBindersE 1 γ N).subst w = substEnv γ (Comp.subst w N)
  induction γ generalizing N with
  | nil => rfl
  | cons v γ ih =>
    have hv : Val.ClosedE v := hγ v List.mem_cons_self
    have hγ' : ∀ u ∈ γ, Val.ClosedE u := fun u hu => hγ u (List.mem_cons_of_mem v hu)
    simp only [closeUnderBindersE, substEnv, shiftNE, hv.shift]
    rw [ih hγ' (Comp.substFrom 1 v N)]
    congr 1
    exact Comp.substFrom_swap_closedE hv _hw 0 N

/-! ### The 2-binder crux (`split`; transplanted `closeC_subst2_comm` + `_ge` swap, task #15 retires) -/

-- TODO(hoist, task #15): duplicate of Bang.Meta.BinaryLR.{Val,Comp,Handler}.substFrom_swap_closed_ge.
mutual
theorem Val.substFrom_swap_closed_geE :
    ∀ {u w : Val}, Val.ClosedE u → Val.ClosedE w → ∀ (i j : Nat), i ≤ j → ∀ (t : Val),
      Val.substFrom i w (Val.substFrom (j + 1) u t) = Val.substFrom j u (Val.substFrom i w t)
  | _, _, _, _, _, _, _,   .vunit => rfl
  | _, _, _, _, _, _, _,   .vint _ => rfl
  | _, _, _, _, _, _, _,   .vcap _ _ => rfl
  | u, w, hu, hw, i, j, hij, .vvar m => by
      rcases Nat.lt_trichotomy m i with hmi | hmi | hmi
      · simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega), if_neg (show ¬ m > j + 1 by omega),
          if_neg (show ¬ m = i by omega), if_neg (show ¬ m > i by omega),
          if_neg (show ¬ m = j by omega), if_neg (show ¬ m > j by omega)]
      · subst hmi
        simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega),
          if_neg (show ¬ m > j + 1 by omega), if_true]
        rw [hw.subst_at j u]
      · rcases Nat.lt_trichotomy m (j + 1) with hmj | hmj | hmj
        · simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega), if_neg (show ¬ m > j + 1 by omega),
            if_neg (show ¬ m = i by omega), if_pos (show m > i by omega),
            if_neg (show ¬ m - 1 = j by omega), if_neg (show ¬ m - 1 > j by omega)]
        · subst hmj
          simp only [Val.substFrom, if_true,
            if_neg (show ¬ j + 1 = i by omega), if_pos (show j + 1 > i by omega), Nat.add_sub_cancel]
          rw [hu.subst_at i w]
        · simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega), if_pos (show m > j + 1 by omega),
            if_neg (show ¬ m - 1 = i by omega), if_pos (show m - 1 > i by omega),
            if_neg (show ¬ m = i by omega), if_pos (show m > i by omega),
            if_neg (show ¬ m - 1 = j by omega), if_pos (show m - 1 > j by omega)]
  | u, w, hu, hw, i, j, hij, .vthunk M => by
      simp only [Val.substFrom]; rw [Comp.substFrom_swap_closed_geE hu hw i j hij M]
  | u, w, hu, hw, i, j, hij, .inl t => by
      simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .inr t => by
      simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .pair a b => by
      simp only [Val.substFrom]
      rw [Val.substFrom_swap_closed_geE hu hw i j hij a, Val.substFrom_swap_closed_geE hu hw i j hij b]
  | u, w, hu, hw, i, j, hij, .fold t => by
      simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij t]
theorem Comp.substFrom_swap_closed_geE :
    ∀ {u w : Val}, Val.ClosedE u → Val.ClosedE w → ∀ (i j : Nat), i ≤ j → ∀ (t : Comp),
      Comp.substFrom i w (Comp.substFrom (j + 1) u t) = Comp.substFrom j u (Comp.substFrom i w t)
  | u, w, hu, hw, i, j, hij, .ret t => by
      simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .binop op a b => by
      simp only [Comp.substFrom]
      rw [Val.substFrom_swap_closed_geE hu hw i j hij a, Val.substFrom_swap_closed_geE hu hw i j hij b]
  | u, w, hu, hw, i, j, hij, .letC M N => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Comp.substFrom_swap_closed_geE hu hw i j hij M,
        Comp.substFrom_swap_closed_geE hu hw (i + 1) (j + 1) (by omega) N]
  | u, w, hu, hw, i, j, hij, .force t => by
      simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .lam M => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Comp.substFrom_swap_closed_geE hu hw (i + 1) (j + 1) (by omega) M]
  | u, w, hu, hw, i, j, hij, .app M t => by
      simp only [Comp.substFrom]
      rw [Comp.substFrom_swap_closed_geE hu hw i j hij M, Val.substFrom_swap_closed_geE hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .perform cp op t => by
      simp only [Comp.substFrom]
      rw [Val.substFrom_swap_closed_geE hu hw i j hij cp, Val.substFrom_swap_closed_geE hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .handle hd M => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Handler.substFrom_swap_closed_geE hu hw i j hij hd,
        Comp.substFrom_swap_closed_geE hu hw (i + 1) (j + 1) (by omega) M]
  | u, w, hu, hw, i, j, hij, .case t N₁ N₂ => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Val.substFrom_swap_closed_geE hu hw i j hij t,
        Comp.substFrom_swap_closed_geE hu hw (i + 1) (j + 1) (by omega) N₁,
        Comp.substFrom_swap_closed_geE hu hw (i + 1) (j + 1) (by omega) N₂]
  | u, w, hu, hw, i, j, hij, .split t N => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Val.substFrom_swap_closed_geE hu hw i j hij t,
        Comp.substFrom_swap_closed_geE hu hw (i + 2) (j + 2) (by omega) N]
  | u, w, hu, hw, i, j, hij, .unfold t => by
      simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij t]
  | _, _, _, _, _, _, _, .oom => rfl
  | _, _, _, _, _, _, _, .wrong _ => rfl
theorem Handler.substFrom_swap_closed_geE :
    ∀ {u w : Val}, Val.ClosedE u → Val.ClosedE w → ∀ (i j : Nat), i ≤ j → ∀ (hd : Handler),
      Handler.substFrom i w (Handler.substFrom (j + 1) u hd)
        = Handler.substFrom j u (Handler.substFrom i w hd)
  | u, w, hu, hw, i, j, hij, .state ℓ s => by
      simp only [Handler.substFrom]; rw [Val.substFrom_swap_closed_geE hu hw i j hij s]
  | _, _, _, _, _, _, _, .throws _ => rfl
  | _, _, _, _, _, _, _, .transaction _ _ => rfl
  | _, _, _, _, _, _, _, .custom _ _ _ => rfl
end

/-- `closeUnderBindersE 0 = substEnv` (level-0 subst, no weakening). -/
theorem closeUnderBindersE_zero (γ : List Val) (c : Comp) : closeUnderBindersE 0 γ c = substEnv γ c := by
  induction γ generalizing c with
  | nil => rfl
  | cons v γ ih => simp only [closeUnderBindersE, substEnv, Comp.subst, shiftNE]; exact ih _

/-- Level-0 descent through `closeUnderBindersE (d+1)` for a CLOSED filler (drops the binder-depth by one;
non-adjacent swap). Engine behind the 2-binder split crux. -/
theorem closeUnderBindersE_subst0 (d : Nat) {γ : List Val} (hγ : ∀ v ∈ γ, Val.ClosedE v)
    {w : Val} (hw : Val.ClosedE w) (N : Comp) :
    Comp.substFrom 0 w (closeUnderBindersE (d + 1) γ N) = closeUnderBindersE d γ (Comp.substFrom 0 w N) := by
  induction γ generalizing N with
  | nil => rfl
  | cons v γ ih =>
    have hv : Val.ClosedE v := hγ v List.mem_cons_self
    have hγ' : ∀ u ∈ γ, Val.ClosedE u := fun u hu => hγ u (List.mem_cons_of_mem v hu)
    simp only [closeUnderBindersE, shiftNE_closed hv]
    rw [ih hγ' (Comp.substFrom (d + 1) v N)]
    congr 1
    exact Comp.substFrom_swap_closed_geE hv hw 0 d (Nat.zero_le d) N

/-- **THE 2-BINDER CRUX** (`split`): filling the two binders of `closeUnderBindersE 2 γ N` (inner
`shift w`, outer `v`, the `split (pair v w) N ↦ subst v (subst (shift w) N)` reduct) = closing
`subst v (subst w N)`. Closes the `split` case of the correspondence. -/
theorem substEnv_cons2_subst {γ : List Val} (hγ : ∀ u ∈ γ, Val.ClosedE u)
    {v w : Val} (hv : Val.ClosedE v) (hw : Val.ClosedE w) (N : Comp) :
    Comp.subst v (Comp.subst (Val.shift w) (closeUnderBindersE 2 γ N)) = substEnv γ (Comp.subst v (Comp.subst w N)) := by
  rw [show Val.shift w = w from hw.shift]
  show Comp.substFrom 0 v (Comp.substFrom 0 w (closeUnderBindersE (1 + 1) γ N))
    = substEnv γ (Comp.substFrom 0 v (Comp.substFrom 0 w N))
  rw [closeUnderBindersE_subst0 1 hγ hw N]
  rw [closeUnderBindersE_subst0 0 hγ hv (Comp.substFrom 0 w N), closeUnderBindersE_zero]

/-! ### `substEnv` distribution over the term constructors (slice-3a infra)

The correspondence induction reduces `substEnv γ (F …)` to `F (substEnv γ …)` at every non-binding
component and `closeUnderBindersE d γ …` under each binder (`d` = the former's binder count). These are
STRUCTURAL (induction on `γ`; the single `Comp.subst` step unfolds the constructor's `substFrom` clause)
— no closedness consumed. `substEnvV` is the value-level fold (the `closeV` analog), needed for the
value-carrying formers (`ret`/`case`/`split`/`unfold`/`app`/`force`/`binop`). These are BYTE-IDENTICAL
to `Bang.Meta.BinaryLR.closeC_*`/`closeV_*` (task #15 retires the duplicate). -/

-- TODO(hoist, task #15): duplicate of Bang.Meta.LR.closeV — the value-level closing fold.
/-- Sequential substitution of a readback-env `γ` into a VALUE (the value-level `substEnv`). -/
def substEnvV : List Val → Val → Val
  | [],      v => v
  | u :: γ,  v => substEnvV γ (Val.subst u v)

@[simp] theorem substEnvV_nil (v : Val) : substEnvV [] v = v := rfl

@[simp] theorem substEnv_ret (γ : List Val) (w : Val) :
    substEnv γ (Comp.ret w) = Comp.ret (substEnvV γ w) := by
  induction γ generalizing w with
  | nil => rfl
  | cons v γ ih => simp only [substEnv, substEnvV, Comp.subst, Comp.substFrom]; exact ih _

@[simp] theorem substEnv_force (γ : List Val) (w : Val) :
    substEnv γ (Comp.force w) = Comp.force (substEnvV γ w) := by
  induction γ generalizing w with
  | nil => rfl
  | cons v γ ih => simp only [substEnv, substEnvV, Comp.subst, Comp.substFrom]; exact ih _

@[simp] theorem substEnv_app (γ : List Val) (M : Comp) (w : Val) :
    substEnv γ (Comp.app M w) = Comp.app (substEnv γ M) (substEnvV γ w) := by
  induction γ generalizing M w with
  | nil => rfl
  | cons v γ ih => simp only [substEnv, substEnvV, Comp.subst, Comp.substFrom]; exact ih _ _

@[simp] theorem substEnv_unfold (γ : List Val) (w : Val) :
    substEnv γ (Comp.unfold w) = Comp.unfold (substEnvV γ w) := by
  induction γ generalizing w with
  | nil => rfl
  | cons v γ ih => simp only [substEnv, substEnvV, Comp.subst, Comp.substFrom]; exact ih _

@[simp] theorem substEnv_binop (γ : List Val) (op : BinOp) (a b : Val) :
    substEnv γ (Comp.binop op a b) = Comp.binop op (substEnvV γ a) (substEnvV γ b) := by
  induction γ generalizing a b with
  | nil => rfl
  | cons v γ ih => simp only [substEnv, substEnvV, Comp.subst, Comp.substFrom]; exact ih _ _

@[simp] theorem substEnv_letC (γ : List Val) (M N : Comp) :
    substEnv γ (Comp.letC M N) = Comp.letC (substEnv γ M) (closeUnderBindersE 1 γ N) := by
  induction γ generalizing M N with
  | nil => rfl
  | cons v γ ih =>
    simp only [substEnv, closeUnderBindersE, Comp.subst, Comp.substFrom, shiftNE]
    exact ih _ _

@[simp] theorem substEnv_lam (γ : List Val) (M : Comp) :
    substEnv γ (Comp.lam M) = Comp.lam (closeUnderBindersE 1 γ M) := by
  induction γ generalizing M with
  | nil => rfl
  | cons v γ ih =>
    simp only [substEnv, closeUnderBindersE, Comp.subst, Comp.substFrom, shiftNE]
    exact ih _

@[simp] theorem substEnv_case (γ : List Val) (w : Val) (N₁ N₂ : Comp) :
    substEnv γ (Comp.case w N₁ N₂)
      = Comp.case (substEnvV γ w) (closeUnderBindersE 1 γ N₁) (closeUnderBindersE 1 γ N₂) := by
  induction γ generalizing w N₁ N₂ with
  | nil => rfl
  | cons v γ ih =>
    simp only [substEnv, substEnvV, closeUnderBindersE, Comp.subst, Val.subst, Comp.substFrom, shiftNE]
    exact ih _ _ _

@[simp] theorem substEnv_split (γ : List Val) (w : Val) (N : Comp) :
    substEnv γ (Comp.split w N) = Comp.split (substEnvV γ w) (closeUnderBindersE 2 γ N) := by
  induction γ generalizing w N with
  | nil => rfl
  | cons v γ ih =>
    simp only [substEnv, substEnvV, closeUnderBindersE, Comp.subst, Val.subst, Comp.substFrom, shiftNE]
    exact ih _ _

/-! ### Closedness of the readback env (slice-3a: the closed-filler side condition)

The crux `substEnv_cons_subst` needs each filler `Val.ClosedE`. The env values a PURE evaluation binds
are read-back machine values; a machine value reads back closed exactly when it is *well-formed* —
every closure inside captures an env covering its body's free vars. We package this as `MVal.WF`
(reads back closed) + `MEnv.WF` (every entry WF) and thread it as the induction's side condition,
mirroring the resume map's "each `readbackEnv ρ` entry is `Val.ClosedE`" hypothesis. -/

/-- A machine value is well-formed iff it reads back to a CLOSED kernel value. The env-machine's
well-scopedness invariant at the value level: a ground `MVal` (no closures, or closures whose captured
env covers their body) reads back with no dangling de Bruijn index. -/
def MVal.WF (mv : MVal) : Prop := Val.ClosedE (readback mv)

/-- An environment is well-formed iff every entry is. Equivalently: every `readbackEnv ρ` entry is
`Val.ClosedE` — exactly the crux's closed-filler side condition, threaded through binder extensions. -/
def MEnv.WF (ρ : MEnv) : Prop := ∀ v ∈ readbackEnv ρ, Val.ClosedE v

theorem MEnv.WF.nil : MEnv.WF .nil := by intro v hv; simp only [readbackEnv, List.not_mem_nil] at hv

theorem MEnv.WF.cons {mv : MVal} {ρ : MEnv} (hmv : MVal.WF mv) (hρ : MEnv.WF ρ) :
    MEnv.WF (mv ∷ₑ ρ) := by
  intro v hv
  simp only [readbackEnv, List.mem_cons] at hv
  rcases hv with h | h
  · exact h ▸ hmv
  · exact hρ v h

/-- The env-closedness hypothesis in the crux's `∀ v ∈ γ` form, from `MEnv.WF`. -/
theorem MEnv.WF.closedEnv {ρ : MEnv} (hρ : MEnv.WF ρ) : ∀ v ∈ readbackEnv ρ, Val.ClosedE v := hρ

/-! ### The value-level correspondence `readback ∘ evalV = substEnvV ∘ readbackEnv`

`substEnvV` picks index `i` out of a CLOSED env exactly as `ρ.get i` does — the env-lookup ↔ subst
identity (`substEnvV_vvar`). Lifted structurally, `substEnvV (readbackEnv ρ) v = readback (evalV ρ v)`
(the value analog of the crux; the closure case bottoms out on `substEnv`/`readbackEnv` definitionally). -/

/-- Closing a CLOSED value is the identity (each `Val.subst` in the fold leaves it fixed). -/
theorem closeVE_closed {v : Val} (hv : Val.ClosedE v) : ∀ γ : List Val, substEnvV γ v = v
  | []      => rfl
  | u :: γ  => by
      rw [substEnvV, show Val.subst u v = v from hv.subst_at 0 u]; exact closeVE_closed hv γ

/-- On a CLOSED env, `substEnvV` on an IN-RANGE `vvar i` selects entry `i` — the env-lookup ↔ subst
identity. The later substitutions fix the selected closed value; before the hit each `Val.subst`
renumbers down. -/
theorem substEnvV_vvar {γ : List Val} (hγ : ∀ v ∈ γ, Val.ClosedE v) {i : Nat} (hi : i < γ.length) :
    substEnvV γ (Val.vvar i) = γ[i] := by
  induction γ generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons u γ ih =>
    have hu : Val.ClosedE u := hγ u List.mem_cons_self
    have hγ' : ∀ v ∈ γ, Val.ClosedE v := fun v hv => hγ v (List.mem_cons_of_mem u hv)
    cases i with
    | zero =>
      simp only [substEnvV, Val.subst, Val.substFrom, if_pos rfl, List.getElem_cons_zero]
      exact closeVE_closed hu γ
    | succ j =>
      have hj : j < γ.length := by simp only [List.length_cons] at hi; omega
      simp only [substEnvV, Val.subst, Val.substFrom, if_neg (Nat.succ_ne_zero j),
        if_pos (Nat.succ_pos j), Nat.add_sub_cancel, List.getElem_cons_succ]
      exact ih hγ' hj

/-! ### Well-scopedness (slice-3a: the source-side scope invariant)

A term is well-scoped under `n` binders when its free de Bruijn indices are all `< n` — captured, per
the existing `shiftFrom`-fixpoint idiom, as "shifting at any cutoff `≥ n` is the identity" (`ClosedE` is
`ScopedV 0`). This is the invariant `evalV`/`evalE` preserve: a value evaluated under `ρ` and read back
is CLOSED exactly when the source term is scoped under `|ρ|`. Needed because a closure `mvclos M ρ` reads
back to `vthunk (substEnv (readbackEnv ρ) M)`, closed only if `M`'s frees are covered by `ρ`. -/

/-- `v`'s free de Bruijn indices are all `< n` (shift at any cutoff `≥ n` fixes it). `ScopedV 0 = ClosedE`. -/
def Val.ScopedV (n : Nat) (v : Val) : Prop := ∀ k, n ≤ k → Val.shiftFrom k v = v
/-- `M`'s free de Bruijn indices are all `< n`. -/
def Comp.ScopedC (n : Nat) (M : Comp) : Prop := ∀ k, n ≤ k → Comp.shiftFrom k M = M

theorem Val.ScopedV.closedE_zero {v : Val} (h : Val.ScopedV 0 v) : Val.ClosedE v :=
  fun k => h k (Nat.zero_le k)

/-- A `vvar i` scoped under `n` has `i < n` (the shift at cutoff `n` would bump it otherwise). -/
theorem Val.ScopedV.vvar_lt {n i : Nat} (h : Val.ScopedV n (Val.vvar i)) : i < n := by
  by_contra hlt
  have := h n (Nat.le_refl n)
  simp only [Val.shiftFrom, if_neg (by omega : ¬ i < n)] at this
  exact absurd (Val.vvar.inj this) (by omega)

/-! #### `Comp.ScopedC` decomposition (into subterm scope at the right binder depth)

Every eval case decomposes the source term's scope into scope of its parts: non-binding components stay
at `n`, a `d`-binder body descends to `n + d` (letC/lam/case body = `n+1`, split body = `n+2`, the value
components of ADT/perform/binop stay at `n`). Route-agnostic: needed by any invariant-bundle shape. -/

theorem Comp.ScopedC.ret_inv {n : Nat} {w : Val} (h : Comp.ScopedC n (Comp.ret w)) : Val.ScopedV n w := by
  intro k hk; have := h k hk; simp only [Comp.shiftFrom, Comp.ret.injEq] at this; exact this
theorem Comp.ScopedC.force_inv {n : Nat} {w : Val} (h : Comp.ScopedC n (Comp.force w)) :
    Val.ScopedV n w := by
  intro k hk; have := h k hk; simp only [Comp.shiftFrom, Comp.force.injEq] at this; exact this
theorem Comp.ScopedC.unfold_inv {n : Nat} {w : Val} (h : Comp.ScopedC n (Comp.unfold w)) :
    Val.ScopedV n w := by
  intro k hk; have := h k hk; simp only [Comp.shiftFrom, Comp.unfold.injEq] at this; exact this
theorem Comp.ScopedC.binop_inv {n : Nat} {op : BinOp} {a b : Val}
    (h : Comp.ScopedC n (Comp.binop op a b)) : Val.ScopedV n a ∧ Val.ScopedV n b := by
  constructor <;> intro k hk <;>
    · have := h k hk; simp only [Comp.shiftFrom, Comp.binop.injEq] at this
      first | exact this.2.1 | exact this.2.2
theorem Comp.ScopedC.app_inv {n : Nat} {M : Comp} {w : Val} (h : Comp.ScopedC n (Comp.app M w)) :
    Comp.ScopedC n M ∧ Val.ScopedV n w := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;>
    · have := h k hk; simp only [Comp.shiftFrom, Comp.app.injEq] at this
      first | exact this.1 | exact this.2
theorem Comp.ScopedC.letC_inv {n : Nat} {M N : Comp} (h : Comp.ScopedC n (Comp.letC M N)) :
    Comp.ScopedC n M ∧ Comp.ScopedC (n + 1) N := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have := h k hk; simp only [Comp.shiftFrom, Comp.letC.injEq] at this; exact this.1
  · have := h (k - 1) (by omega); simp only [Comp.shiftFrom, Comp.letC.injEq] at this
    rw [show k = (k - 1) + 1 by omega]; exact this.2
theorem Comp.ScopedC.lam_inv {n : Nat} {M : Comp} (h : Comp.ScopedC n (Comp.lam M)) :
    Comp.ScopedC (n + 1) M := by
  intro k hk; have := h (k - 1) (by omega)
  simp only [Comp.shiftFrom, Comp.lam.injEq] at this
  rw [show k = (k - 1) + 1 by omega]; exact this
theorem Comp.ScopedC.case_inv {n : Nat} {w : Val} {N₁ N₂ : Comp}
    (h : Comp.ScopedC n (Comp.case w N₁ N₂)) :
    Val.ScopedV n w ∧ Comp.ScopedC (n + 1) N₁ ∧ Comp.ScopedC (n + 1) N₂ := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := h k hk; simp only [Comp.shiftFrom, Comp.case.injEq] at this; exact this.1
  · have := h (k - 1) (by omega); simp only [Comp.shiftFrom, Comp.case.injEq] at this
    rw [show k = (k - 1) + 1 by omega]; exact this.2.1
  · have := h (k - 1) (by omega); simp only [Comp.shiftFrom, Comp.case.injEq] at this
    rw [show k = (k - 1) + 1 by omega]; exact this.2.2
theorem Comp.ScopedC.split_inv {n : Nat} {w : Val} {N : Comp} (h : Comp.ScopedC n (Comp.split w N)) :
    Val.ScopedV n w ∧ Comp.ScopedC (n + 2) N := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have := h k hk; simp only [Comp.shiftFrom, Comp.split.injEq] at this; exact this.1
  · have := h (k - 2) (by omega); simp only [Comp.shiftFrom, Comp.split.injEq] at this
    rw [show k = (k - 2) + 2 by omega]; exact this.2

/-! ### Closedness of `substEnv`/`substEnvV` from scope (slice-3a: the WF-preservation core)

Closing a term SCOPED under `|γ|` over a CLOSED env `γ` yields a CLOSED term — the fold substitutes
each free index with a closed filler, dropping the scope by one each step to `ScopedV 0 = ClosedE`.
This is what makes `evalV`/`evalE` results read back closed (a closure `mvclos M ρ` reads back closed
because `M` scoped + `readbackEnv ρ` closed ⇒ `substEnv (readbackEnv ρ) M` closed). Transplanted
`shiftFrom_substFrom_closed` (the closed-filler shift/subst commutation) + `closeV_closed_scoped`
from BinaryLR (task #15 retires). -/

-- TODO(hoist, task #15): duplicate of Bang.Meta.BinaryLR.{Val,Comp,Handler}.shiftFrom_substFrom_closed.
mutual
theorem Val.shiftFrom_substFrom_closedE :
    ∀ {u : Val}, Val.ClosedE u → ∀ (k i : Nat), i ≤ k → ∀ (t : Val),
      Val.shiftFrom k (Val.substFrom i u t) = Val.substFrom i u (Val.shiftFrom (k + 1) t)
  | _, _,  _, _, _,    .vunit => rfl
  | _, _,  _, _, _,    .vint _ => rfl
  | _, _,  _, _, _,    .vcap _ _ => rfl
  | u, hu, k, i, hik,  .vvar j => by
      rcases Nat.lt_trichotomy j i with hji | hji | hji
      · rw [Val.substFrom, if_neg (by omega), if_neg (by omega),
          Val.shiftFrom, if_pos (by omega : j < k),
          Val.shiftFrom, if_pos (by omega : j < k + 1),
          Val.substFrom, if_neg (by omega), if_neg (by omega)]
      · subst hji
        rw [Val.substFrom, if_pos rfl, hu.shiftFrom_eq,
          Val.shiftFrom, if_pos (by omega : j < k + 1), Val.substFrom, if_pos rfl]
      · rw [Val.substFrom, if_neg (by omega), if_pos (by omega : j > i)]
        rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
        · rw [Val.shiftFrom, if_pos (by omega : j - 1 < k),
            Val.shiftFrom, if_pos (by omega : j < k + 1),
            Val.substFrom, if_neg (by omega), if_pos (by omega : j > i)]
        · rw [Val.shiftFrom, if_neg (by omega : ¬ j - 1 < k),
            Val.shiftFrom, if_neg (by omega : ¬ j < k + 1),
            Val.substFrom, if_neg (by omega), if_pos (by omega : j + 1 > i),
            show j - 1 + 1 = j + 1 - 1 by omega]
  | u, hu, k, i, hik,  .vthunk M => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Comp.shiftFrom_substFrom_closedE hu k i hik M]
  | u, hu, k, i, hik,  .inl w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik w]
  | u, hu, k, i, hik,  .inr w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik w]
  | u, hu, k, i, hik,  .pair a b => by
      simp only [Val.shiftFrom, Val.substFrom]
      rw [Val.shiftFrom_substFrom_closedE hu k i hik a, Val.shiftFrom_substFrom_closedE hu k i hik b]
  | u, hu, k, i, hik,  .fold w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik w]
theorem Comp.shiftFrom_substFrom_closedE :
    ∀ {u : Val}, Val.ClosedE u → ∀ (k i : Nat), i ≤ k → ∀ (t : Comp),
      Comp.shiftFrom k (Comp.substFrom i u t) = Comp.substFrom i u (Comp.shiftFrom (k + 1) t)
  | u, hu, k, i, hik, .ret w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik w]
  | u, hu, k, i, hik, .binop op a b => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Val.shiftFrom_substFrom_closedE hu k i hik a, Val.shiftFrom_substFrom_closedE hu k i hik b]
  | u, hu, k, i, hik, .letC M N => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Comp.shiftFrom_substFrom_closedE hu k i hik M,
        Comp.shiftFrom_substFrom_closedE hu (k + 1) (i + 1) (by omega) N]
  | u, hu, k, i, hik, .force w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik w]
  | u, hu, k, i, hik, .lam M => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Comp.shiftFrom_substFrom_closedE hu (k + 1) (i + 1) (by omega) M]
  | u, hu, k, i, hik, .app M w => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Comp.shiftFrom_substFrom_closedE hu k i hik M, Val.shiftFrom_substFrom_closedE hu k i hik w]
  | u, hu, k, i, hik, .perform cp op w => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Val.shiftFrom_substFrom_closedE hu k i hik cp, Val.shiftFrom_substFrom_closedE hu k i hik w]
  | u, hu, k, i, hik, .handle hd M => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Handler.shiftFrom_substFrom_closedE hu k i hik hd,
        Comp.shiftFrom_substFrom_closedE hu (k + 1) (i + 1) (by omega) M]
  | u, hu, k, i, hik, .case w N₁ N₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Val.shiftFrom_substFrom_closedE hu k i hik w,
        Comp.shiftFrom_substFrom_closedE hu (k + 1) (i + 1) (by omega) N₁,
        Comp.shiftFrom_substFrom_closedE hu (k + 1) (i + 1) (by omega) N₂]
  | u, hu, k, i, hik, .split w N => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Val.shiftFrom_substFrom_closedE hu k i hik w,
        Comp.shiftFrom_substFrom_closedE hu (k + 2) (i + 2) (by omega) N]
  | u, hu, k, i, hik, .unfold w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik w]
  | _, _, _, _, _, .oom => rfl
  | _, _, _, _, _, .wrong _ => rfl
theorem Handler.shiftFrom_substFrom_closedE :
    ∀ {u : Val}, Val.ClosedE u → ∀ (k i : Nat), i ≤ k → ∀ (hd : Handler),
      Handler.shiftFrom k (Handler.substFrom i u hd) = Handler.substFrom i u (Handler.shiftFrom (k + 1) hd)
  | u, hu, k, i, hik, .state ℓ s => by
      simp only [Handler.shiftFrom, Handler.substFrom]; rw [Val.shiftFrom_substFrom_closedE hu k i hik s]
  | _, _, _, _, _, .throws _ => rfl
  | _, _, _, _, _, .transaction _ _ => rfl
  | _, _, _, _, _, .custom _ _ _ => rfl
end

/-- Substituting the level-0 binder of an `(m+1)`-scoped VALUE with a CLOSED filler drops scope to `m`. -/
theorem Val.ScopedV.subst_closed {m : Nat} {u v : Val} (hu : Val.ClosedE u)
    (hv : Val.ScopedV (m + 1) v) : Val.ScopedV m (Val.subst u v) := by
  intro k hk
  rw [Val.subst, Val.shiftFrom_substFrom_closedE hu k 0 (Nat.zero_le k) v, hv (k + 1) (by omega)]
/-- The same for a COMPUTATION. -/
theorem Comp.ScopedC.subst_closed {m : Nat} {u : Val} {M : Comp} (hu : Val.ClosedE u)
    (hM : Comp.ScopedC (m + 1) M) : Comp.ScopedC m (Comp.subst u M) := by
  intro k hk
  rw [Comp.subst, Comp.shiftFrom_substFrom_closedE hu k 0 (Nat.zero_le k) M, hM (k + 1) (by omega)]

/-- Closing a VALUE scoped under `|γ|` over a CLOSED env yields a CLOSED value. -/
theorem substEnvV_closed : ∀ {γ : List Val} {v : Val},
    (∀ u ∈ γ, Val.ClosedE u) → Val.ScopedV γ.length v → Val.ClosedE (substEnvV γ v)
  | [],     v, _,  hv => fun k => hv k (Nat.zero_le k)
  | u :: γ, v, hγ, hv => by
      have hu : Val.ClosedE u := hγ u List.mem_cons_self
      have hγ' : ∀ w ∈ γ, Val.ClosedE w := fun w hw => hγ w (List.mem_cons_of_mem u hw)
      rw [substEnvV]
      exact substEnvV_closed hγ'
        (Val.ScopedV.subst_closed hu (by simpa only [List.length_cons] using hv))
/-- Closing a COMPUTATION scoped under `|γ|` over a CLOSED env yields a CLOSED computation. -/
theorem substEnv_closed : ∀ {γ : List Val} {M : Comp},
    (∀ u ∈ γ, Val.ClosedE u) → Comp.ScopedC γ.length M → Comp.ScopedC 0 (substEnv γ M)
  | [],     M, _,  hM => hM
  | u :: γ, M, hγ, hM => by
      have hu : Val.ClosedE u := hγ u List.mem_cons_self
      have hγ' : ∀ w ∈ γ, Val.ClosedE w := fun w hw => hγ w (List.mem_cons_of_mem u hw)
      rw [substEnv]
      exact substEnv_closed hγ'
        (Comp.ScopedC.subst_closed hu (by simpa only [List.length_cons] using hM))

/-! ### The 3a purity invariant (FACTORED from closedness — ruling rider, 2026-07-10)

`MVal.WF`/`MEnv.WF` (above) are the REUSABLE closedness core (reads-back-closed) slice 3b keeps
UNCHANGED over store-held values. The purity discipline the PURE fragment additionally needs — every
closure in reach carries an `EffectFree`, `ScopedC`-under-its-env body, so `force`/`app` never run
effectful captured code — is a SEPARATE layer. 3b takes only the closedness core; 3a stacks purity on
top. Kept factored per the ruling rider so 3b EXTENDS rather than reshapes (no "pure" baked into `WF`). -/

/-! A computation is in the PURE fragment (`EffectFree`) when it — AND every thunk it can RETURN or run
— performs no effect and installs no handler. `EffectFree` must descend into VALUE thunks (`ValEF`),
not just sub-computations: `ret (vthunk (perform …))` is effect-free AT TOP yet returns an effectful
closure, so `force`/`app` on it would perform — the deep fragment excludes that. Mutual `EffectFree`
(over `Comp`) / `ValEF` (over `Val`, = "every `vthunk` body is `EffectFree`"). This makes `MVal.PureV`
of an evaluated value follow from `ValEF` of the source value + `MEnv.PureV` of the env. -/
mutual
def EffectFree : Comp → Prop
  | .ret v         => ValEF v
  | .letC M N      => EffectFree M ∧ EffectFree N
  | .force v       => ValEF v
  | .lam M         => EffectFree M
  | .app M v       => EffectFree M ∧ ValEF v
  | .perform _ _ _ => False
  | .handle _ _    => False
  | .case v N₁ N₂  => ValEF v ∧ EffectFree N₁ ∧ EffectFree N₂
  | .split v N     => ValEF v ∧ EffectFree N
  | .unfold v      => ValEF v
  | .binop _ a b   => ValEF a ∧ ValEF b
  | .oom           => True
  | .wrong _       => True
def ValEF : Val → Prop
  | .vunit       => True
  | .vint _      => True
  | .vvar _      => True
  | .vcap _ _    => True
  | .vthunk M    => EffectFree M
  | .inl w       => ValEF w
  | .inr w       => ValEF w
  | .pair w₁ w₂  => ValEF w₁ ∧ ValEF w₂
  | .fold w      => ValEF w
end

/-! The purity invariant on machine values / envs (the 3a layer over closedness): every closure a value
reaches has an `EffectFree` body `ScopedC` under its captured env's length. Mutual over `MVal`/`MEnv`
to descend the closure's env. `force`/`app` entering `mvclos M ρ'` then get `EffectFree M` + the env
invariant to fire the IH — the fix for wrinkle 3 (closures carry arbitrary captured code). -/
mutual
def MVal.PureV : MVal → Prop
  | .mvunit       => True
  | .mvint _      => True
  | .mvcap _ _    => True
  -- a closure's captured env is itself WELL-FORMED: WF (reads back closed — needed so the crux fires in
  -- the body's sub-cases), PureV (its own closures are effect-free), and the body is EffectFree + scoped
  -- under the env. This IS the combined `Good` closure discipline the ruling approved.
  | .mvclos M ρ   =>
      EffectFree M ∧ Comp.ScopedC (readbackEnv ρ).length M ∧ MEnv.WF ρ ∧ MEnv.PureV ρ
  | .minl w       => MVal.PureV w
  | .minr w       => MVal.PureV w
  | .mpair w₁ w₂  => MVal.PureV w₁ ∧ MVal.PureV w₂
  | .mfold w      => MVal.PureV w
def MEnv.PureV : MEnv → Prop
  | .nil       => True
  | .cons v ρ  => MVal.PureV v ∧ MEnv.PureV ρ
end

theorem MEnv.PureV.head {mv : MVal} {ρ : MEnv} (h : MEnv.PureV (mv ∷ₑ ρ)) : MVal.PureV mv := by
  unfold MEnv.PureV at h; exact h.1
theorem MEnv.PureV.tail {mv : MVal} {ρ : MEnv} (h : MEnv.PureV (mv ∷ₑ ρ)) : MEnv.PureV ρ := by
  unfold MEnv.PureV at h; exact h.2
theorem MEnv.PureV.cons {mv : MVal} {ρ : MEnv} (hmv : MVal.PureV mv) (hρ : MEnv.PureV ρ) :
    MEnv.PureV (mv ∷ₑ ρ) := by unfold MEnv.PureV; exact ⟨hmv, hρ⟩

/-- A `PureV` env's in-range lookup is `PureV`. Out of range gives `mvunit` (also `PureV`), so the
bound `i < |readbackEnv ρ|` is not even needed — but we keep the general form. -/
theorem MEnv.PureV.get : ∀ {ρ : MEnv}, MEnv.PureV ρ → ∀ (i : Nat), MVal.PureV (ρ.get i)
  | .nil, _, _ => by simp only [MEnv.get, MVal.PureV]
  | .cons v ρ, h, 0 => by simp only [MEnv.get]; exact h.head
  | .cons v ρ, h, j + 1 => by simp only [MEnv.get]; exact MEnv.PureV.get h.tail j

/-- Well-formedness of a machine TERMINAL (the closedness core, over the terminal readback). A returner
is WF iff its value is; a function `mlam N ρ` is WF iff its captured env is WF and its body `N` is scoped
under `|readbackEnv ρ| + 1` (one binder) — exactly what makes `readbackTerm` a closed `lam`. -/
def MTerm.WF : MTerm → Prop
  | .mret mv  => MVal.WF mv
  | .mlam N ρ => MEnv.WF ρ ∧ Comp.ScopedC ((readbackEnv ρ).length + 1) N

/-- Purity of a machine TERMINAL. A returner: its value `PureV`. A function `mlam N ρ`: its body
`EffectFree` + scoped, and its captured env `Good` (WF ∧ PureV) — the closure discipline, at a terminal. -/
def MTerm.PureV : MTerm → Prop
  | .mret mv  => MVal.PureV mv
  | .mlam N ρ =>
      EffectFree N ∧ Comp.ScopedC ((readbackEnv ρ).length + 1) N ∧ MEnv.WF ρ ∧ MEnv.PureV ρ

/-! ### The value correspondence `readback ∘ evalV = substEnvV ∘ readbackEnv`

For a `v` scoped under `|ρ|` with `ρ` well-formed, evaluating `v` under `ρ` then reading back equals
substituting the read-back env into `v`. Structural induction on `v`: `vvar` uses the lookup identity
(`substEnvV_vvar` + `readbackEnv` index-matching), the CLOSURE `vthunk M` bottoms out DEFINITIONALLY
(both sides are `vthunk (substEnv (readbackEnv ρ) M)` — the closure defers, no recursion into `M`). -/

/-- `readbackEnv` and `MEnv.get` match at every in-range index (`readbackEnv` is `MEnv.get` read back). -/
theorem readbackEnv_getElem : ∀ (ρ : MEnv) {i : Nat} (hi : i < (readbackEnv ρ).length),
    (readbackEnv ρ)[i] = readback (ρ.get i)
  | .nil, i, hi => by simp only [readbackEnv, List.length_nil] at hi; exact absurd hi (Nat.not_lt_zero i)
  | .cons u ρ, 0, _ => by simp only [readbackEnv, List.getElem_cons_zero, MEnv.get]
  | .cons u ρ, j + 1, hi => by
      simp only [readbackEnv, List.length_cons] at hi
      simp only [readbackEnv, List.getElem_cons_succ, MEnv.get]
      exact readbackEnv_getElem ρ (by omega)

/-- `substEnvV` pushes through a `vthunk`: closing a suspended `Comp` is closing its body (`substEnv`).
The DEFINITIONAL bridge that lets the closure case of the value correspondence bottom out. -/
@[simp] theorem substEnvV_vthunk (γ : List Val) (M : Comp) :
    substEnvV γ (Val.vthunk M) = Val.vthunk (substEnv γ M) := by
  induction γ generalizing M with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, substEnv, Val.subst, Val.substFrom, Comp.subst]; exact ih _

/-- `substEnvV` structural push-through the ADT/atom formers (used by the value correspondence). -/
@[simp] theorem substEnvV_vunit (γ : List Val) : substEnvV γ Val.vunit = Val.vunit := by
  induction γ with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih
@[simp] theorem substEnvV_vint (γ : List Val) (n : Int) : substEnvV γ (Val.vint n) = Val.vint n := by
  induction γ with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih
@[simp] theorem substEnvV_vcap (γ : List Val) (n : Nat) (ℓ : Bang.EffectRow.Label) :
    substEnvV γ (Val.vcap n ℓ) = Val.vcap n ℓ := by
  induction γ with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih
@[simp] theorem substEnvV_inl (γ : List Val) (w : Val) :
    substEnvV γ (Val.inl w) = Val.inl (substEnvV γ w) := by
  induction γ generalizing w with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih _
@[simp] theorem substEnvV_inr (γ : List Val) (w : Val) :
    substEnvV γ (Val.inr w) = Val.inr (substEnvV γ w) := by
  induction γ generalizing w with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih _
@[simp] theorem substEnvV_pair (γ : List Val) (w₁ w₂ : Val) :
    substEnvV γ (Val.pair w₁ w₂) = Val.pair (substEnvV γ w₁) (substEnvV γ w₂) := by
  induction γ generalizing w₁ w₂ with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih _ _
@[simp] theorem substEnvV_fold (γ : List Val) (w : Val) :
    substEnvV γ (Val.fold w) = Val.fold (substEnvV γ w) := by
  induction γ generalizing w with
  | nil => rfl
  | cons u γ ih => simp only [substEnvV, Val.subst, Val.substFrom]; exact ih _

/-- Scope projects into the single-child ADT formers (`inl`/`inr`/`fold`). -/
theorem Val.ScopedV.inl_inv {n : Nat} {w : Val} (h : Val.ScopedV n (Val.inl w)) : Val.ScopedV n w := by
  intro k hk; have := h k hk; simp only [Val.shiftFrom, Val.inl.injEq] at this; exact this
theorem Val.ScopedV.inr_inv {n : Nat} {w : Val} (h : Val.ScopedV n (Val.inr w)) : Val.ScopedV n w := by
  intro k hk; have := h k hk; simp only [Val.shiftFrom, Val.inr.injEq] at this; exact this
theorem Val.ScopedV.fold_inv {n : Nat} {w : Val} (h : Val.ScopedV n (Val.fold w)) : Val.ScopedV n w := by
  intro k hk; have := h k hk; simp only [Val.shiftFrom, Val.fold.injEq] at this; exact this
theorem Val.ScopedV.pair_inv {n : Nat} {w₁ w₂ : Val} (h : Val.ScopedV n (Val.pair w₁ w₂)) :
    Val.ScopedV n w₁ ∧ Val.ScopedV n w₂ := by
  constructor <;> intro k hk <;>
    · have := h k hk; simp only [Val.shiftFrom, Val.pair.injEq] at this
      first | exact this.1 | exact this.2

/-- **THE VALUE CORRESPONDENCE** (`readback ∘ evalV = substEnvV ∘ readbackEnv`). For a `v` well-scoped
under `|ρ|` with `ρ` well-formed, evaluating `v` under `ρ` and reading back = substituting the read-back
env. Structural on `v`; the closure case is DEFINITIONAL (`substEnvV_vthunk`). -/
theorem readback_evalV {ρ : MEnv} (hρ : MEnv.WF ρ) :
    ∀ {v : Val}, Val.ScopedV (readbackEnv ρ).length v →
      readback (evalV ρ v) = substEnvV (readbackEnv ρ) v
  | .vunit, _ => by simp only [evalV, readback, substEnvV_vunit]
  | .vint _, _ => by simp only [evalV, readback, substEnvV_vint]
  | .vcap _ _, _ => by simp only [evalV, readback, substEnvV_vcap]
  | .vvar i, hv => by
      have hi : i < (readbackEnv ρ).length := hv.vvar_lt
      rw [substEnvV_vvar hρ hi, readbackEnv_getElem ρ hi]
      simp only [evalV]
  | .vthunk M, _ => by simp only [evalV, readback, substEnvV_vthunk]
  | .inl w, hv => by simp only [evalV, readback, substEnvV_inl]; rw [readback_evalV hρ hv.inl_inv]
  | .inr w, hv => by simp only [evalV, readback, substEnvV_inr]; rw [readback_evalV hρ hv.inr_inv]
  | .pair w₁ w₂, hv => by
      simp only [evalV, readback, substEnvV_pair]
      rw [readback_evalV hρ hv.pair_inv.1, readback_evalV hρ hv.pair_inv.2]
  | .fold w, hv => by simp only [evalV, readback, substEnvV_fold]; rw [readback_evalV hρ hv.fold_inv]

/-! ### `evalV` preserves the invariants (slice-3a: results are WF ∧ PureV)

Evaluating a scoped, `ValEF` source value under a WF/PureV env produces a WF (reads-back-closed) and
PureV machine value — the bound-value obligations of the `_pure` induction's binder cases. `evalV_WF`
routes through the value correspondence + `substEnvV_closed`; `evalV_PureV` is structural on `v`, the
`vthunk` case producing `mvclos M ρ` whose purity is exactly `EffectFree M` (from `ValEF (vthunk M)`)
∧ scope ∧ the env's `PureV`. -/

/-- `evalV` of a scoped value under a WF env reads back closed (the value's `MVal.WF`). -/
theorem evalV_WF {ρ : MEnv} (hρ : MEnv.WF ρ) {v : Val}
    (hv : Val.ScopedV (readbackEnv ρ).length v) : MVal.WF (evalV ρ v) := by
  unfold MVal.WF
  rw [readback_evalV hρ hv]
  exact substEnvV_closed (by simpa only [MEnv.WF] using hρ) hv

/-- `evalV` of a `ValEF` value under a `PureV` env is `PureV` (the value's `MVal.PureV`). Structural on
`v`; `vthunk M ↦ mvclos M ρ` gets `EffectFree M` from `ValEF (vthunk M)`, scope from the hyp, env-purity
from `hρ`. Needs the source value scoped so the closure's body-scope obligation is met. -/
theorem evalV_PureV {ρ : MEnv} (hWFρ : MEnv.WF ρ) (hρ : MEnv.PureV ρ) :
    ∀ {v : Val}, ValEF v → Val.ScopedV (readbackEnv ρ).length v → MVal.PureV (evalV ρ v)
  | .vunit, _, _ => by simp only [evalV, MVal.PureV]
  | .vint _, _, _ => by simp only [evalV, MVal.PureV]
  | .vcap _ _, _, _ => by simp only [evalV, MVal.PureV]
  | .vvar i, _, _ => by
      -- ρ.get i is a stored env value; PureV of the env's entries transfers (total, no range needed).
      simp only [evalV]
      exact MEnv.PureV.get hρ i
  | .vthunk M, hEF, hsc => by
      simp only [evalV, MVal.PureV]
      refine ⟨hEF, ?_, hWFρ, hρ⟩
      -- vthunk M scoped under n means M scoped under n (thunk doesn't bind); readback env length = n.
      intro k hk; have := hsc k hk
      simp only [Val.shiftFrom, Val.vthunk.injEq] at this; exact this
  | .inl w, hEF, hsc => by
      simp only [evalV, MVal.PureV]
      exact evalV_PureV hWFρ hρ (by simpa only [ValEF] using hEF) hsc.inl_inv
  | .inr w, hEF, hsc => by
      simp only [evalV, MVal.PureV]
      exact evalV_PureV hWFρ hρ (by simpa only [ValEF] using hEF) hsc.inr_inv
  | .pair w₁ w₂, hEF, hsc => by
      simp only [evalV, MVal.PureV]
      have hEF' : ValEF w₁ ∧ ValEF w₂ := by simpa only [ValEF] using hEF
      exact ⟨evalV_PureV hWFρ hρ hEF'.1 hsc.pair_inv.1, evalV_PureV hWFρ hρ hEF'.2 hsc.pair_inv.2⟩
  | .fold w, hEF, hsc => by
      simp only [evalV, MVal.PureV]
      exact evalV_PureV hWFρ hρ (by simpa only [ValEF] using hEF) hsc.fold_inv

/-- The δ-result round-trips: `readback (evalVOfBinop (BinOp.eval op x y)) = BinOp.eval op x y`.
`BinOp.eval` only makes `vint`/`boolVal` (`inl/inr vunit`), each fixed by `evalVOfBinop`∘`readback`. -/
theorem readback_evalVOfBinop_eval (op : BinOp) (x y : Int) :
    readback (evalE.evalVOfBinop (Bang.BinOp.eval op x y)) = Bang.BinOp.eval op x y := by
  cases op <;> simp only [Bang.BinOp.eval]
  · simp only [evalE.evalVOfBinop, readback]
  · simp only [evalE.evalVOfBinop, readback]
  · simp only [evalE.evalVOfBinop, readback]
  · simp only [evalE.evalVOfBinop, readback]
  · rcases Bool.eq_false_or_eq_true (decide (x < y)) with hb | hb <;>
      simp only [hb, Bang.boolVal, evalE.evalVOfBinop, readback]
  · rcases Bool.eq_false_or_eq_true (decide (x = y)) with hb | hb <;>
      simp only [hb, Bang.boolVal, evalE.evalVOfBinop, readback]

/-- The δ-result is CLOSED (`vint`/`boolVal` are ground — no free de Bruijn index). -/
theorem BinOp_eval_closedE (op : BinOp) (x y : Int) : Val.ClosedE (Bang.BinOp.eval op x y) := by
  intro k; cases op <;> simp only [Bang.BinOp.eval]
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases Bool.eq_false_or_eq_true (decide (x < y)) with hb | hb <;>
      simp only [hb, Bang.boolVal, Val.shiftFrom]
  · rcases Bool.eq_false_or_eq_true (decide (x = y)) with hb | hb <;>
      simp only [hb, Bang.boolVal, Val.shiftFrom]

/-- The δ-result's MVal image is `PureV` (a first-order ground value — no closures). -/
theorem evalVOfBinop_eval_pureV (op : BinOp) (x y : Int) :
    MVal.PureV (evalE.evalVOfBinop (Bang.BinOp.eval op x y)) := by
  cases op <;> simp only [Bang.BinOp.eval]
  · simp only [evalE.evalVOfBinop, MVal.PureV]
  · simp only [evalE.evalVOfBinop, MVal.PureV]
  · simp only [evalE.evalVOfBinop, MVal.PureV]
  · simp only [evalE.evalVOfBinop, MVal.PureV]
  · rcases Bool.eq_false_or_eq_true (decide (x < y)) with hb | hb <;>
      simp only [hb, Bang.boolVal, evalE.evalVOfBinop, MVal.PureV]
  · rcases Bool.eq_false_or_eq_true (decide (x = y)) with hb | hb <;>
      simp only [hb, Bang.boolVal, evalE.evalVOfBinop, MVal.PureV]

/-! ### The PURE-fragment correspondence (`_pure`, slice-3a)

The empty-store, `EffectFree` sub-theorem the resume map sequences first. Fuel is MATCHED: `evalE` and
`evalD` recurse structurally on the SAME term shape, so a success at `evalE` fuel `f` gives an `evalD`
success at the SAME `f` (no fuel-monotonicity needed — the recursion depths coincide). The conclusion
is STRENGTHENED with `MVal.WF mv ∧ MVal.PureV mv`: the binder cases extend the env with a bound value
and must re-establish both invariants to fire the IH (IH-strengthening; ruling 2026-07-10 task #11).
Stores stay `[]` throughout (`EffectFree` ⇒ no `perform`/`handle` ⇒ σ/τ/κ untouched, outcome never
`mraised`). Counters `g`/`G` are free (no cap minted in the pure fragment). -/
theorem evalE_agrees_evalD_pure :
    ∀ (f : Nat) (γ : List Val) (M : Comp) (t : MTerm) (ρ : MEnv) (g G g' : Nat)
      (eσ eσ' : ESStore) (eτ eτ' : ETHeap) (eκ eκ' : ECStore)
      (dσ : Bang.CalcVM.SStore) (dτ : Bang.CalcVM.THeap) (dκ : Bang.CalcVM.CStore),
      EnvAgrees ρ γ → MEnv.WF ρ → MEnv.PureV ρ → EffectFree M → Comp.ScopedC γ.length M →
      evalE f g eσ eτ eκ ρ M = some (.mterm t, g', eσ', eτ', eκ') →
      (eσ' = eσ ∧ eτ' = eτ ∧ eκ' = eκ) ∧
      (Bang.CalcVM.evalD f G dσ dτ dκ (substEnv γ M)
          = some (readbackTerm t, G, dσ, dτ, dκ)) ∧ MTerm.WF t ∧ MTerm.PureV t := by
  intro f
  induction f with
  | zero => intro γ M t ρ g G g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ _ _ _ _ _ h; simp [evalE] at h
  | succ f ih =>
    intro γ M t ρ g G g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ hagree hWF hPure hEF hSc h
    have hγ : ∀ v ∈ γ, Val.ClosedE v := hagree ▸ hWF
    have hlen : (readbackEnv ρ).length = γ.length := by rw [show readbackEnv ρ = γ from hagree]
    cases M with
    | ret v =>
      -- evalE: t = mret (evalV ρ v), stores unchanged; evalD (ret (substEnvV γ v)) = ret (readback ..).
      simp only [evalE, Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
      obtain ⟨ht, -, hσ, hτ, hκ⟩ := h
      have hsc : Val.ScopedV γ.length v := hlen ▸ (hSc.ret_inv)
      have hEFv : ValEF v := by simpa only [EffectFree] using hEF
      subst ht
      refine ⟨⟨hσ.symm, hτ.symm, hκ.symm⟩, ?_, evalV_WF hWF (hlen ▸ hsc),
        evalV_PureV hWF hPure hEFv (hlen ▸ hsc)⟩
      simp only [substEnv_ret, readbackTerm, Bang.CalcVM.evalD, readback_evalV hWF (hlen ▸ hsc),
        show readbackEnv ρ = γ from hagree]
    | lam M =>
      -- evalE (lam M) = mterm (mlam M ρ), stores unchanged; evalD (lam (closeUnderBindersE 1 γ M)).
      simp only [evalE, Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
      obtain ⟨ht, -, hσ, hτ, hκ⟩ := h
      have hScM : Comp.ScopedC (γ.length + 1) M := hSc.lam_inv
      have hEFM : EffectFree M := by simpa only [EffectFree] using hEF
      have hγeq : readbackEnv ρ = γ := hagree
      subst ht
      refine ⟨⟨hσ.symm, hτ.symm, hκ.symm⟩, ?_, ⟨hWF, hlen ▸ hScM⟩, ⟨hEFM, hlen ▸ hScM, hWF, hPure⟩⟩
      simp only [substEnv_lam, readbackTerm, Bang.CalcVM.evalD, hγeq]
    | force w =>
      -- evalE: evalV ρ w = mvclos M' ρ' ⇒ run M' under ρ'. evalD: force (vthunk (substEnv (rbEnv ρ') M')).
      have hsc : Val.ScopedV γ.length w := hlen ▸ hSc.force_inv
      have hEFw : ValEF w := by simpa only [EffectFree] using hEF
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mvclos M' ρ' =>
        rw [hw] at h
        -- purity of the closure ⇒ its body EffectFree + scoped, its env PureV.
        have hpc : MVal.PureV (MVal.mvclos M' ρ') := by
          have := evalV_PureV hWF hPure hEFw (hlen ▸ hsc); rw [hw] at this; exact this
        have hpc' := by simpa only [MVal.PureV] using hpc
        have hEFM' : EffectFree M' := hpc'.1
        have hscM' : Comp.ScopedC (readbackEnv ρ').length M' := hpc'.2.1
        have hWFρ' : MEnv.WF ρ' := hpc'.2.2.1
        have hPρ' : MEnv.PureV ρ' := hpc'.2.2.2
        obtain ⟨hst, hd, hWFt, hPt⟩ := ih (readbackEnv ρ') M' t ρ' g G g' eσ eσ' eτ eτ' eκ eκ'
          dσ dτ dκ rfl hWFρ' hPρ' hEFM' hscM' h
        refine ⟨hst, ?_, hWFt, hPt⟩
        -- substEnv γ (force w) = force (substEnvV γ w) = force (vthunk (substEnv (rbEnv ρ') M')).
        have hrb : substEnvV γ w = Val.vthunk (substEnv (readbackEnv ρ') M') := by
          rw [show γ = readbackEnv ρ from hagree.symm, ← readback_evalV hWF (hlen ▸ hsc), hw]; rfl
        rw [substEnv_force, hrb]
        simpa only [Bang.CalcVM.evalD] using hd
      | _ => rw [hw] at h; simp at h
    | letC M N =>
      -- evalE: run M ⇒ mret mw, bind (mw ∷ₑ ρ), run N ⇒ mret mv. evalD: letC-SUBST via the crux.
      obtain ⟨hEFM, hEFN⟩ := (by simpa only [EffectFree] using hEF : EffectFree M ∧ EffectFree N)
      obtain ⟨hScM, hScN⟩ := hSc.letC_inv
      simp only [evalE, Option.bind_eq_bind] at h
      cases hM : evalE f g eσ eτ eκ ρ M with
      | none => rw [hM] at h; simp at h
      | some p =>
        rw [hM] at h
        obtain ⟨out, g₁, σ₁, τ₁, κ₁⟩ := p
        cases out with
        | mterm tM => cases tM with
          | mret mw =>
            simp only [Option.bind_some] at h
            -- IH on M (terminal mret mw): stores unchanged, M's evalD run, mw is WF ∧ PureV.
            obtain ⟨⟨hσ₁, hτ₁, hκ₁⟩, hdM, hWFmw, hPmw⟩ :=
              ih γ M (.mret mw) ρ g G g₁ eσ σ₁ eτ τ₁ eκ κ₁ dσ dτ dκ hagree hWF hPure hEFM (hlen ▸ hScM) hM
            simp only [MTerm.WF] at hWFmw; simp only [MTerm.PureV] at hPmw
            -- N runs under (mw ∷ₑ ρ) at M's output stores σ₁ τ₁ κ₁; IH on N gives the tail correspondence.
            have hagreeN : EnvAgrees (mw ∷ₑ ρ) (readback mw :: γ) := by
              simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hagree]
            have hWFN : MEnv.WF (mw ∷ₑ ρ) := MEnv.WF.cons hWFmw hWF
            have hPureN : MEnv.PureV (mw ∷ₑ ρ) := MEnv.PureV.cons hPmw hPure
            have hScN' : Comp.ScopedC (readback mw :: γ).length N := by
              simpa only [List.length_cons] using hScN
            obtain ⟨hstN, hdN, hWFt, hPt⟩ :=
              ih (readback mw :: γ) N t (mw ∷ₑ ρ) g₁ G g' σ₁ eσ' τ₁ eτ' κ₁ eκ'
                dσ dτ dκ hagreeN hWFN hPureN hEFN hScN' h
            -- final store-eq: eσ'=σ₁=eσ (compose the two invariance triples).
            obtain ⟨hstN1, hstN2, hstN3⟩ := hstN
            have hst : eσ' = eσ ∧ eτ' = eτ ∧ eκ' = eκ := ⟨hstN1.trans hσ₁, hstN2.trans hτ₁, hstN3.trans hκ₁⟩
            refine ⟨hst, ?_, hWFt, hPt⟩
            -- evalD (letC (substEnv γ M) (closeUnderBindersE 1 γ N)); run M ⇒ ret (readback mw),
            -- then (closeUnderBindersE 1 γ N).subst (readback mw) = substEnv (readback mw :: γ) N (CRUX).
            have hcrux : substEnv (readback mw :: γ) N = (closeUnderBindersE 1 γ N).subst (readback mw) :=
              (substEnv_cons_subst hγ hWFmw N).symm
            simp only [substEnv_letC, Bang.CalcVM.evalD, Option.bind_eq_bind]
            rw [show Bang.CalcVM.evalD f G dσ dτ dκ (substEnv γ M) = _ from hdM]
            simp only [readbackTerm, Option.bind_some]
            rw [← hcrux]; exact hdN
          | mlam _ _ => simp only [Option.bind_some] at h; exact absurd h (by simp)
        | mraised n op w => simp only [Option.bind_some] at h; exact absurd h (by simp)
    | app M v =>
      -- evalE: run M ⇒ mlam N' ρ', β under (evalV ρ v ∷ₑ ρ') N'. evalD: app-β via the crux.
      obtain ⟨hScM, hScv⟩ := hSc.app_inv
      obtain ⟨hEFM, hEFv⟩ := (by simpa only [EffectFree] using hEF : EffectFree M ∧ ValEF v)
      have hscv : Val.ScopedV γ.length v := hlen ▸ hScv
      have hWFav : MVal.WF (evalV ρ v) := evalV_WF hWF (hlen ▸ hscv)
      have hPav : MVal.PureV (evalV ρ v) := evalV_PureV hWF hPure hEFv (hlen ▸ hscv)
      simp only [evalE, Option.bind_eq_bind] at h
      cases hM : evalE f g eσ eτ eκ ρ M with
      | none => rw [hM] at h; simp at h
      | some p =>
        rw [hM] at h
        obtain ⟨out, g₁, σ₁, τ₁, κ₁⟩ := p
        cases out with
        | mterm tM => cases tM with
          | mlam N' ρ' =>
            simp only [Option.bind_some] at h
            -- IH on M (terminal mlam N' ρ'): store-invariance, evalD ⇒ lam (closeUnderBindersE 1 (rbEnv ρ') N'),
            -- and the closure's WF/PureV (its env Good, its body EffectFree + scoped).
            obtain ⟨⟨hσ₁, hτ₁, hκ₁⟩, hdM, hWFlam, hPlam⟩ :=
              ih γ M (.mlam N' ρ') ρ g G g₁ eσ σ₁ eτ τ₁ eκ κ₁ dσ dτ dκ hagree hWF hPure hEFM (hlen ▸ hScM) hM
            obtain ⟨hWFρ', hscN'⟩ := (by simpa only [MTerm.WF] using hWFlam : MEnv.WF ρ' ∧ Comp.ScopedC ((readbackEnv ρ').length + 1) N')
            obtain ⟨hEFN', -, -, hPρ'⟩ :=
              (by simpa only [MTerm.PureV] using hPlam :
                EffectFree N' ∧ Comp.ScopedC ((readbackEnv ρ').length + 1) N' ∧ MEnv.WF ρ' ∧ MEnv.PureV ρ')
            -- N' runs under (evalV ρ v ∷ₑ ρ'); env agrees with readback (evalV ρ v) :: readbackEnv ρ'.
            have hagreeN : EnvAgrees (evalV ρ v ∷ₑ ρ') (readback (evalV ρ v) :: readbackEnv ρ') := by
              simp only [EnvAgrees, readbackEnv]
            have hWFN : MEnv.WF (evalV ρ v ∷ₑ ρ') := MEnv.WF.cons hWFav hWFρ'
            have hPureN : MEnv.PureV (evalV ρ v ∷ₑ ρ') := MEnv.PureV.cons hPav hPρ'
            have hScN'' : Comp.ScopedC (readback (evalV ρ v) :: readbackEnv ρ').length N' := by
              simpa only [List.length_cons] using hscN'
            obtain ⟨hstN, hdN, hWFt, hPt⟩ :=
              ih (readback (evalV ρ v) :: readbackEnv ρ') N' t (evalV ρ v ∷ₑ ρ') g₁ G g'
                σ₁ eσ' τ₁ eτ' κ₁ eκ' dσ dτ dκ hagreeN hWFN hPureN hEFN' hScN'' h
            obtain ⟨hstN1, hstN2, hstN3⟩ := hstN
            refine ⟨⟨hstN1.trans hσ₁, hstN2.trans hτ₁, hstN3.trans hκ₁⟩, ?_, hWFt, hPt⟩
            -- crux: (closeUnderBindersE 1 (rbEnv ρ') N').subst (readback (evalV ρ v))
            --        = substEnv (readback (evalV ρ v) :: readbackEnv ρ') N'.
            have hcrux : substEnv (readback (evalV ρ v) :: readbackEnv ρ') N'
                = (closeUnderBindersE 1 (readbackEnv ρ') N').subst (readback (evalV ρ v)) :=
              (substEnv_cons_subst (by simpa only [MEnv.WF] using hWFρ') hWFav N').symm
            have hrbv : substEnvV γ v = readback (evalV ρ v) := by
              rw [show γ = readbackEnv ρ from hagree.symm, readback_evalV hWF (hlen ▸ hscv)]
            simp only [substEnv_app, hrbv, Bang.CalcVM.evalD, Option.bind_eq_bind]
            rw [show Bang.CalcVM.evalD f G dσ dτ dκ (substEnv γ M) = _ from hdM]
            simp only [readbackTerm, Option.bind_some]
            rw [← hcrux]; exact hdN
          | mret _ => simp only [Option.bind_some] at h; exact absurd h (by simp)
        | mraised n op w => simp only [Option.bind_some] at h; exact absurd h (by simp)
    | case w N₁ N₂ =>
      -- evalE: evalV ρ w = minl mv' ⇒ run N₁ under (mv' ∷ₑ ρ); minr ⇒ N₂. evalD: case-branch via crux.
      obtain ⟨hScw, hScN₁, hScN₂⟩ := hSc.case_inv
      obtain ⟨hEFw, hEFN₁, hEFN₂⟩ := (by simpa only [EffectFree] using hEF : ValEF w ∧ EffectFree N₁ ∧ EffectFree N₂)
      have hscw : Val.ScopedV γ.length w := hlen ▸ hScw
      have hWFsc : MVal.WF (evalV ρ w) := evalV_WF hWF (hlen ▸ hscw)
      have hPsc : MVal.PureV (evalV ρ w) := evalV_PureV hWF hPure hEFw (hlen ▸ hscw)
      have hrbw : substEnvV γ w = readback (evalV ρ w) := by
        rw [show γ = readbackEnv ρ from hagree.symm, readback_evalV hWF (hlen ▸ hscw)]
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | minl mv' =>
        rw [hw] at h
        have hWFmv' : MVal.WF mv' := by
          rw [hw] at hWFsc; simp only [MVal.WF, readback] at hWFsc
          exact (Val.ScopedV.inl_inv (fun k _ => hWFsc k)).closedE_zero
        have hPmv' : MVal.PureV mv' := by rw [hw] at hPsc; simpa only [MVal.PureV] using hPsc
        have hagreeN : EnvAgrees (mv' ∷ₑ ρ) (readback mv' :: γ) := by
          simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hagree]
        have hScN₁' : Comp.ScopedC (readback mv' :: γ).length N₁ := by
          simpa only [List.length_cons] using hScN₁
        obtain ⟨hst, hd, hWFt, hPt⟩ :=
          ih (readback mv' :: γ) N₁ t (mv' ∷ₑ ρ) g G g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ
            hagreeN (MEnv.WF.cons hWFmv' hWF) (MEnv.PureV.cons hPmv' hPure) hEFN₁ hScN₁' h
        refine ⟨hst, ?_, hWFt, hPt⟩
        have hcrux : substEnv (readback mv' :: γ) N₁ = (closeUnderBindersE 1 γ N₁).subst (readback mv') :=
          (substEnv_cons_subst hγ hWFmv' N₁).symm
        simp only [substEnv_case, hrbw, hw, readback, Bang.CalcVM.evalD]
        rw [← hcrux]; exact hd
      | minr mv' =>
        rw [hw] at h
        have hWFmv' : MVal.WF mv' := by
          rw [hw] at hWFsc; simp only [MVal.WF, readback] at hWFsc
          exact (Val.ScopedV.inr_inv (fun k _ => hWFsc k)).closedE_zero
        have hPmv' : MVal.PureV mv' := by rw [hw] at hPsc; simpa only [MVal.PureV] using hPsc
        have hagreeN : EnvAgrees (mv' ∷ₑ ρ) (readback mv' :: γ) := by
          simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hagree]
        have hScN₂' : Comp.ScopedC (readback mv' :: γ).length N₂ := by
          simpa only [List.length_cons] using hScN₂
        obtain ⟨hst, hd, hWFt, hPt⟩ :=
          ih (readback mv' :: γ) N₂ t (mv' ∷ₑ ρ) g G g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ
            hagreeN (MEnv.WF.cons hWFmv' hWF) (MEnv.PureV.cons hPmv' hPure) hEFN₂ hScN₂' h
        refine ⟨hst, ?_, hWFt, hPt⟩
        have hcrux : substEnv (readback mv' :: γ) N₂ = (closeUnderBindersE 1 γ N₂).subst (readback mv') :=
          (substEnv_cons_subst hγ hWFmv' N₂).symm
        simp only [substEnv_case, hrbw, hw, readback, Bang.CalcVM.evalD]
        rw [← hcrux]; exact hd
      | _ => rw [hw] at h; simp at h
    | split w N =>
      -- evalE: evalV ρ w = mpair mv₁ mv₂ ⇒ run N under (mv₂ ∷ₑ mv₁ ∷ₑ ρ). evalD: split via the 2-binder crux.
      obtain ⟨hScw, hScN⟩ := hSc.split_inv
      obtain ⟨hEFw, hEFN⟩ := (by simpa only [EffectFree] using hEF : ValEF w ∧ EffectFree N)
      have hscw : Val.ScopedV γ.length w := hlen ▸ hScw
      have hWFsc : MVal.WF (evalV ρ w) := evalV_WF hWF (hlen ▸ hscw)
      have hPsc : MVal.PureV (evalV ρ w) := evalV_PureV hWF hPure hEFw (hlen ▸ hscw)
      have hrbw : substEnvV γ w = readback (evalV ρ w) := by
        rw [show γ = readbackEnv ρ from hagree.symm, readback_evalV hWF (hlen ▸ hscw)]
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mpair mv₁ mv₂ =>
        rw [hw] at h
        rw [hw] at hWFsc hPsc
        simp only [MVal.WF, readback] at hWFsc
        simp only [MVal.PureV] at hPsc
        have hWF₁ : MVal.WF mv₁ := (Val.ScopedV.pair_inv (fun k _ => hWFsc k)).1.closedE_zero
        have hWF₂ : MVal.WF mv₂ := (Val.ScopedV.pair_inv (fun k _ => hWFsc k)).2.closedE_zero
        -- N runs under (mv₂ ∷ₑ mv₁ ∷ₑ ρ); env agrees with readback mv₂ :: readback mv₁ :: γ.
        have hagreeN : EnvAgrees (mv₂ ∷ₑ mv₁ ∷ₑ ρ) (readback mv₂ :: readback mv₁ :: γ) := by
          simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hagree]
        have hWFN : MEnv.WF (mv₂ ∷ₑ mv₁ ∷ₑ ρ) := MEnv.WF.cons hWF₂ (MEnv.WF.cons hWF₁ hWF)
        have hPureN : MEnv.PureV (mv₂ ∷ₑ mv₁ ∷ₑ ρ) := MEnv.PureV.cons hPsc.2 (MEnv.PureV.cons hPsc.1 hPure)
        have hScN' : Comp.ScopedC (readback mv₂ :: readback mv₁ :: γ).length N := by
          simpa only [List.length_cons] using hScN
        obtain ⟨hst, hd, hWFt, hPt⟩ :=
          ih (readback mv₂ :: readback mv₁ :: γ) N t (mv₂ ∷ₑ mv₁ ∷ₑ ρ) g G g'
            eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ hagreeN hWFN hPureN hEFN hScN' h
        refine ⟨hst, ?_, hWFt, hPt⟩
        -- readback (mpair mv₁ mv₂) = pair (readback mv₁) (readback mv₂), matching evalD's pair scrutinee.
        have hcrux : substEnv (readback mv₂ :: readback mv₁ :: γ) N
            = Comp.subst (readback mv₁) (Comp.subst (Val.shift (readback mv₂)) (closeUnderBindersE 2 γ N)) := by
          rw [substEnv_cons2_subst hγ hWF₁ hWF₂ N]; simp only [substEnv, Comp.subst]
        simp only [substEnv_split, hrbw, hw, readback, Bang.CalcVM.evalD]
        rw [hcrux] at hd; exact hd
      | _ => rw [hw] at h; simp at h
    | unfold w =>
      -- evalE: evalV ρ w must be mfold mv ⇒ mret mv. evalD: unfold (fold (readback mv)) ⇒ ret (readback mv).
      have hsc : Val.ScopedV γ.length w := hlen ▸ hSc.unfold_inv
      have hEFw : ValEF w := by simpa only [EffectFree] using hEF
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mfold mw =>
        rw [hw] at h
        simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
        obtain ⟨ht, -, hσ, hτ, hκ⟩ := h
        subst ht
        -- readback (evalV ρ w) = substEnvV γ w, and = fold (readback mw).
        have hrb : substEnvV γ w = Val.fold (readback mw) := by
          rw [show γ = readbackEnv ρ from hagree.symm, ← readback_evalV hWF (hlen ▸ hsc), hw]; rfl
        have hWFmw : MVal.WF mw := by
          have := evalV_WF hWF (hlen ▸ hsc); rw [hw] at this
          simp only [MVal.WF, readback] at this
          exact (Val.ScopedV.fold_inv (fun k _ => this k)).closedE_zero
        have hPmw : MVal.PureV mw := by
          have := evalV_PureV hWF hPure hEFw (hlen ▸ hsc); rw [hw] at this
          simpa only [MVal.PureV] using this
        refine ⟨⟨hσ.symm, hτ.symm, hκ.symm⟩, ?_, hWFmw, hPmw⟩
        simp only [substEnv_unfold, hrb, readbackTerm, Bang.CalcVM.evalD]
      | _ => rw [hw] at h; simp at h
    | binop op a b =>
      -- evalE: evalV ρ a = mvint x, evalV ρ b = mvint y ⇒ mret (evalVOfBinop (op.eval x y)).
      obtain ⟨hSca, hScb⟩ := hSc.binop_inv
      obtain ⟨hEFa, hEFb⟩ := (by simpa only [EffectFree] using hEF : ValEF a ∧ ValEF b)
      have hsca : Val.ScopedV γ.length a := hlen ▸ hSca
      have hscb : Val.ScopedV γ.length b := hlen ▸ hScb
      simp only [evalE] at h
      cases ha : evalV ρ a with
      | mvint x =>
        cases hb : evalV ρ b with
        | mvint y =>
          rw [ha, hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
          obtain ⟨ht, -, hσ, hτ, hκ⟩ := h
          subst ht
          -- substEnvV γ a = readback (mvint x) = vint x; likewise b.
          have hrba : substEnvV γ a = Val.vint x := by
            rw [show γ = readbackEnv ρ from hagree.symm, ← readback_evalV hWF (hlen ▸ hsca), ha]; rfl
          have hrbb : substEnvV γ b = Val.vint y := by
            rw [show γ = readbackEnv ρ from hagree.symm, ← readback_evalV hWF (hlen ▸ hscb), hb]; rfl
          refine ⟨⟨hσ.symm, hτ.symm, hκ.symm⟩, ?_, ?_, evalVOfBinop_eval_pureV op x y⟩
          · simp only [substEnv_binop, hrba, hrbb, readbackTerm, Bang.CalcVM.evalD,
              readback_evalVOfBinop_eval]
          · simp only [MTerm.WF, MVal.WF, readback_evalVOfBinop_eval]; exact BinOp_eval_closedE op x y
        | _ => rw [ha, hb] at h; simp at h
      | _ => rw [ha] at h; simp at h
    | perform w op v => simp only [EffectFree] at hEF
    | handle hd M => simp only [EffectFree] at hEF
    | oom => simp [evalE] at h
    | wrong s => simp [evalE] at h

/-! ## Slice 3b — the effect-store correspondence (STATEMENT + RESUME MAP; the weave is a fresh unit)

The pure fragment (`evalE_agrees_evalD_pure`, above) covers `EffectFree` M over empty stores. 3b closes
the full headline `evalE_agrees_evalD` (below) by relaxing `EffectFree` and threading a correspondence
between `evalE`'s MVal-keyed stores (σ/τ/κ) and `evalD`'s Val-keyed stores. This block STATES that
correspondence + the `Good`-extension over store-held values so the effect theorem COMPILES with a
labelled sorry; the weave is a fresh IC (envm3).

KEY STRUCTURAL FACT (why this is SIMPLER than `run_evalD`'s bridge): both machines key stores by the
SAME generative IDENTITY `Nat` (`Label = Nat`; `evalD` pushes `SStore.push id s` at the mint), and both
carry PARALLEL per-kind stores in the SAME order. So the correspondence is a POINTWISE-UNDER-READBACK
match of two lists with identical keys — NOT an HStack projection (`run_evalD`'s `Corr = σ = hsStates hs`
projects a stack; here there is no stack to project, just `readback` on each entry). `run_evalD`'s
`Corr`/`TCorr`/`CCorr` are the SHAPE to mirror (per-kind, id-keyed, op-disjoint); `StoresBelow`/
`StoresDisjoint` (the id-first freshness backbone) port ACROSS UNCHANGED — they are already stated over
`evalD`'s stores, and `evalE` mints ids identically (`handle` uses `g`, bumps `g+1`), so the SAME
`StoresBelow`/`StoresDisjoint` invariants on the `evalD` side transfer through the key-identical
correspondence. -/

/-- The state-store correspondence: `evalE`'s `ESStore` reads back to `evalD`'s `SStore` pointwise —
same keys, `readback` on each stored `MVal`. -/
def SStoreCorr (eσ : ESStore) (dσ : Bang.CalcVM.SStore) : Prop :=
  dσ = eσ.map (fun p => (p.1, readback p.2))

/-- The txn-heap correspondence: each heap cell reads back (a `List MVal` maps to a `List Val`). -/
def THeapCorr (eτ : ETHeap) (dτ : Bang.CalcVM.THeap) : Prop :=
  dτ = eτ.map (fun p => (p.1, p.2.map readback))

/-- The custom-store correspondence. `evalE` stores `(n, (mv_p, cls, ρ_inst))` — a param, RAW clauses,
and the install-env the clauses closed over. `evalD` stores `(n, (v_p, cls'))` — a param and clauses
ALREADY CLOSED over the install-env, leaving the TWO service binders (param at 1, op-arg at 0) open.
So the param reads back and each clause body is `closeUnderBindersE 2 (readbackEnv ρ_inst)` of the raw
`evalE` clause — the closure relationship at the store level (`evalD`'s perform does `subst p (subst
(shift v) clause.2)` on the already-closed body; `evalE`'s runs the raw body under `arg ∷ p ∷ ρ_inst`,
and 3a's crux-family equates the two). -/
def CStoreCorr (eκ : ECStore) (dκ : Bang.CalcVM.CStore) : Prop :=
  dκ = eκ.map (fun p =>
    (p.1, (readback p.2.1,
      p.2.2.1.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv p.2.2.2) c.2)))))

/-- The combined store correspondence (all three per-kind stores related, in lockstep). -/
def StoresCorr (eσ : ESStore) (eτ : ETHeap) (eκ : ECStore)
    (dσ : Bang.CalcVM.SStore) (dτ : Bang.CalcVM.THeap) (dκ : Bang.CalcVM.CStore) : Prop :=
  SStoreCorr eσ dσ ∧ THeapCorr eτ dτ ∧ CStoreCorr eκ dκ

/-- The `Good`-extension over STORE-HELD values (the ruling's 3b rider — factored so 3b EXTENDS, not
reshapes). Every value the three `evalE` stores hold is WF (reads back closed) and PureV (its closures
are `Good`); custom frames additionally carry an install-env that must itself be WF ∧ PureV and cover
its clauses' free vars (the scope obligation for `CStoreCorr`'s `closeUnderBindersE 2` to be closed).
This is the store-level twin of `MEnv.WF`/`MEnv.PureV`, and it rides the 3b induction exactly as the
env invariants ride 3a. -/
def StoresGood (eσ : ESStore) (eτ : ETHeap) (eκ : ECStore) : Prop :=
  (∀ p ∈ eσ, MVal.WF p.2 ∧ MVal.PureV p.2)
  ∧ (∀ p ∈ eτ, ∀ mv ∈ p.2, MVal.WF mv ∧ MVal.PureV mv)
  ∧ (∀ p ∈ eκ, (MVal.WF p.2.1 ∧ MVal.PureV p.2.1) ∧ MEnv.WF p.2.2.2 ∧ MEnv.PureV p.2.2.2
       ∧ (∀ c ∈ p.2.2.1, Comp.ScopedC ((readbackEnv p.2.2.2).length + 2) c.2 ∧ EffectFree c.2))

/-- **SLICE 3b — the effect-store correspondence (STATEMENT; the weave is envm3).**

Generalizes `evalE_agrees_evalD_pure` off the pure fragment: arbitrary M (no `EffectFree`), arbitrary
`Good`-related input stores, over a general terminal. `readbackTermS` extends `readbackTerm` to the
`mraised` terminal (the third `evalD` `Outcome`). The conclusion threads the store correspondence
forward (output stores stay related) and the id-counter through the mint.

RESUME MAP (envm3 — the weave; 3a's infra is ALL reusable, the cruxes are PROVEN):

- FUEL-matched induction on `f`, cases on `M`, as in `_pure`. The 9 PURE cases are ALREADY structurally
  proven in `_pure`; port them by relaxing `EffectFree M` to `EffectFree`-of-the-non-store-touching
  parts and carrying `StoresGood` + `StoresCorr` through unchanged (they don't touch stores).
- `perform (vcap n ℓ) op v` — mirror `evalD`'s id-first σ→τ→κ arm CASE-FOR-CASE:
    * STATE: `eσ.get? n = some s` ⟺ (via `SStoreCorr`) `dσ.get? n = some (readback s)`; get returns it,
      put threads `eσ.put n arg ⟺ dσ.put n (readback arg)` — need `SStoreCorr`-preservation under `put`
      (a NEW lemma; the readback-map commutes with `put` — MISSING, state + prove).
    * TXN: `eτ.get? n` ⟺ `dτ.get? n` under readback; `mtxnService` ⟺ `txnService` under readback
      (a NEW lemma `mtxnService_readback` — MISSING; the MVal/Val stm-service agree pointwise).
    * CUSTOM: `eκ.get? n = some (p,cls,ρ_inst)` ⟺ `dκ.get? n = some (readback p, closed-cls)`; the clause
      sub-eval `arg ∷ p ∷ ρ_inst ⊢ clause.2` ⟺ `evalD (subst p (subst (shift v) closed-clause))` — closes
      by the 2-BINDER crux `substEnv_cons2_subst` (PROVEN, 3a) applied to the clause body. This is the
      case where 3a's cruxes pay off directly.
    * The `handlesOp`-mismatch RAISE arms need `StoresDisjoint` (ported from `AbstractMachine.lean`) so a
      mismatched op raises identically on both sides (the id resolves in at most one store).
- `handle h M` — the MINT: `evalE` pushes `(g, image)` keyed by `g` and recurses at `g+1`; `evalD` pushes
  `(g, val-image)` and recurses at `g+1`. The pushed entries are related by construction (`evalV ρ s` ⟺
  `readback (evalV ρ s)` = `substEnvV γ s`, from 3a's value correspondence); POP is `.tail` on both,
  which preserves `StoresCorr` (list tails commute with the readback-map). throws-CATCH: the `mraised
  n "raise"` terminal ⟺ `evalD`'s `raised n "raise"`, caught identically. `StoresBelow` (ported) makes
  the mint FRESH so `StoresDisjoint` is push-stable.
- WALLS ALREADY VISIBLE (the MISSING lemmas to state+prove first, all mechanical readback-commutations):
    (W1) `SStoreCorr`/`THeapCorr`/`CStoreCorr` preservation under `get?` (agreement), `put`, `push`,
         `.tail` — the readback-map commutes with each store op. ~6 small lemmas.
    (W2) `mtxnService_readback` — the stm service agrees under readback (newTVar/readTVar/writeTVar).
    (W3) `readbackTermS` for `mraised` + its `MTerm`-WF/PureV extension (trivial — payload is a value).
    (W4) porting `StoresBelow`/`StoresDisjoint` + their push/put preservation from `AbstractMachine.lean`
         (they are `evalD`-side already; re-state over the correspondence or import — check one-writer).
  None of these is a refutation risk; all are the same readback-commutation shape 3a's distribution
  lemmas already exemplify. STOP-and-SHOW the assembled statement was this block; the weave is envm3.

`sorry` — the 3b weave (statement + resume map only; see the WALLS above). -/
theorem evalE_agrees_evalD_effect :
    ∀ (f : Nat) (γ : List Val) (M : Comp) (t : MTerm) (ρ : MEnv) (g G g' : Nat)
      (eσ eσ' : ESStore) (eτ eτ' : ETHeap) (eκ eκ' : ECStore)
      (dσ : Bang.CalcVM.SStore) (dτ : Bang.CalcVM.THeap) (dκ : Bang.CalcVM.CStore),
      EnvAgrees ρ γ → MEnv.WF ρ → MEnv.PureV ρ → Comp.ScopedC γ.length M →
      StoresGood eσ eτ eκ → StoresCorr eσ eτ eκ dσ dτ dκ →
      evalE f g eσ eτ eκ ρ M = some (.mterm t, g', eσ', eτ', eκ') →
      ∃ (G' : Nat) (dσ' : Bang.CalcVM.SStore) (dτ' : Bang.CalcVM.THeap) (dκ' : Bang.CalcVM.CStore),
        Bang.CalcVM.evalD f G dσ dτ dκ (substEnv γ M)
            = some (readbackTerm t, G', dσ', dτ', dκ')
          ∧ StoresCorr eσ' eτ' eκ' dσ' dτ' dκ' ∧ MTerm.WF t ∧ MTerm.PureV t := by
  sorry

/-- **The correspondence STATEMENT** (PLFA `γ≈ₑσ`; slice-3 proof).

If `evalE` runs `M` under `ρ` to a returner `mret mv`, and `ρ` agrees with a substitution
`σ`, then the substitution reference `evalD` (over the σ-substituted term) returns the
read-back value. Generalized from the empty env to an arbitrary `ρ`/`σ` per PLFA's warning
(the induction won't fire on the empty-env special case).

RESUME MAP (slice-3b — the effect-store correspondence, the ONLY remaining work here):

- SLICE 3a is DONE: `evalE_agrees_evalD_pure` (above) proves this correspondence for the PURE fragment
  (empty stores, `EffectFree` M) over a GENERAL terminal, axiom-clean. Its infra — `readbackTerm`,
  `MTerm.WF`/`MTerm.PureV`, the single + 2-binder cruxes, `readback_evalV`, `evalV_WF`/`evalV_PureV`,
  `substEnv_closed`, the `Good` closure discipline (`MVal.PureV`/`MEnv.WF`) — is ALL reusable by 3b.
- 3b closes THIS headline by (a) relaxing `EffectFree` and (b) threading a store-correspondence
  MVal-store ↔ Val-store through readback — the analog of `run_evalD`'s `Corr`/`TCorr`/`CCorr` +
  `StoresBelow`/`StoresDisjoint` (`AbstractMachine.lean`). Relate `evalE`'s σ/τ/κ (MVal) to `evalD`'s
  (Val) pointwise-under-readback; mirror the id-first σ→τ→κ dispatch + the throws-catch case-for-case;
  `mraised` slots into `readbackTerm` as the third terminal. STOP-and-SHOW the correspondence-statement
  shape BEFORE the weave (heavy sub-unit; the mandatory checkpoint).

`sorry` — the 3b effect-store weave (3a pure fragment PROVEN; see `evalE_agrees_evalD_pure`). -/
theorem evalE_agrees_evalD (f : Nat) (γ : List Val) (M : Comp) (mv : MVal)
    (eσ : ESStore) (eτ : ETHeap) (eκ : ECStore) (ρ : MEnv) (g' : Nat)
    (eσ' : ESStore) (eτ' : ETHeap) (eκ' : ECStore)
    (_hagree : EnvAgrees ρ γ)
    (_h : evalE f 0 eσ eτ eκ ρ M = some (.mterm (.mret mv), g', eσ', eτ', eκ')) :
    ∃ F g'' σ' τ' κ',
      Bang.CalcVM.evalD F 0 [] [] [] (substEnv γ M)
        = some (.term (.ret (readback mv)), g'', σ', τ', κ') := by
  sorry -- SLICE-3 induction (see RESUME MAP above): crux proven; grind patterned on sim/run_evalD

/-! ## Mini-Agree probe — the PIN'S EXECUTABLE CONFIRMATION

A pure program run through `evalE` + `readback` must yield the same value the verified
`Source.eval` reference produces. This is the *necessary* value-agreement check that
de-risks the whole env representation before the big weave (working-method: refute-first
with the executable oracle). A green `#guard` here IS the pin confirmed for the pure
fragment; a red one refutes the domain shape for the price of this file.

`runE` closes an empty-env, empty-store eval (counter 0) and reads back a returner to a
`Result Val`, exactly the shape `Source.eval` yields, so the two are directly comparable. -/
def runE (fuel : Nat) (M : Comp) : Result Val :=
  match evalE fuel 0 [] [] [] .nil M with
  | some (.mterm (.mret mv), _, _, _, _) => .done (readback mv)
  | _                                    => .stuck   -- a function-terminal, a raise, or stuck: no first-order value

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

-- ── DEEP closure capture (slice-3 de-risk for substEnv's fold order): a thunk closes over a
--    MULTI-LAYER env `[y=4, x=3]`, is passed as an argument through a lambda, and forced INSIDE the
--    lambda body — so the closure surfaces at a boundary the substitution machine handles by copying
--    x,y into the thunk body. `let x=3 in let y=4 in (λf. force f) (thunk (x+y))` ⇒ 7.
--    At the thunk site env is y∷x∷…, so x=vvar 1, y=vvar 0; the thunk body is `binop add (vvar 1)(vvar 0)`.
--    This is the exact composition substEnv's LEFT FOLD must reproduce — a divergence here refutes the
--    fold order BEFORE the induction grind. Both engines must agree at 7. ──
private def deepClosureWitness : Comp :=
  .letC (.ret (.vint 3))                                   -- x = 3   (x at idx 0 here)
    (.letC (.ret (.vint 4))                                -- y = 4   (y at idx 0, x shifted to idx 1)
      (.app (.lam (.force (.vvar 0)))                      -- (λf. force f)  applied to…
        (.vthunk (.binop .add (.vvar 1) (.vvar 0)))))      -- …thunk(x+y): x=vvar1, y=vvar0 under [y,x]
#guard yieldsIntE (runE 20 deepClosureWitness) 7
#guard yieldsIntE (Bang.Source.eval 20 deepClosureWitness) 7

/-! ### EFFECT-arm mini-Agree (slice 2) — one program per arm through BOTH engines, falsified.

The rider: grow the battery WITH the arms so the cheap refutation keeps paying every slice. Each
witness is a well-typed effect program (borrowed from the `evalD` Agree battery / the kernel custom
`#guard`s) run through `runE`/`readback` AND `Source.eval`, both projected via `yieldsIntE`. A green
pair witnesses the env-threaded effect arm agrees with the verified substitution reference. -/

-- STATE: `handle (state ℓ 0) (put 7; get)` ⇒ 7 — the resumptive store threads the put; get reads it.
-- (env: handle binds the cap into ρ; put/get resolve by identity through the σ-image store.)
private def stateWitness : Comp :=
  .handle (.state 1 (.vint 0)) (.letC (.perform (.vvar 0) "put" (.vint 7)) (.perform (.vvar 1) "get" .vunit))
#guard yieldsIntE (runE 80 stateWitness) 7
#guard yieldsIntE (Bang.Source.eval 80 stateWitness) 7

-- STATE default read: `handle (state ℓ 5) (get ())` ⇒ 5.
#guard yieldsIntE (runE 40 (.handle (.state 1 (.vint 5)) (.perform (.vvar 0) "get" .vunit))) 5
#guard yieldsIntE (Bang.Source.eval 40 (.handle (.state 1 (.vint 5)) (.perform (.vvar 0) "get" .vunit))) 5

-- TXN: `handle (transaction ℓ []) (newTVar 9; readTVar 0)` ⇒ 9 — the heap threads through both ops.
private def txnWitness : Comp :=
  .handle (.transaction 2 [])
    (.letC (.perform (.vvar 0) "newTVar" (.vint 9)) (.perform (.vvar 1) "readTVar" (.vvar 0)))
#guard yieldsIntE (runE 40 txnWitness) 9
#guard yieldsIntE (Bang.Source.eval 40 txnWitness) 9

-- TXN abort-rollback: outer throws over `transaction (newTVar 100; writeTVar 0:=70; raise 100)` ⇒ 100
-- — the raise escapes the txn frame (zero-shot), the write-delta is discarded, the abort payload is
-- the ORIGINAL balance. Exercises: txn service + custom-of-a-cross-kind raise + throws catch together.
private def txnAbortWitness : Comp :=
  .handle (.throws 0)
    (.handle (.transaction 2 [])
      (.letC (.perform (.vvar 0) "newTVar" (.vint 100))
        (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 70)))
          (.perform (.vvar 3) "raise" (.vint 100)))))
#guard yieldsIntE (runE 80 txnAbortWitness) 100
#guard yieldsIntE (Bang.Source.eval 80 txnAbortWitness) 100

-- CUSTOM: a `{Reader}` handler (param 100) services `read 5` by the clause `arg + param = 105`, RESUMING
-- the letC continuation `105 + 1 = 106`. The env analog runs the clause under the INSTALL-ENV (arg@0,
-- param@1, ρ_install) — the closure-of-the-clause the slice-2 custom store carries.
private def customWitness : Comp :=
  .handle (.custom 1 (.vint 100) [("read", .binop .add (.vvar 0) (.vvar 1))])
    (.letC (.perform (.vvar 0) "read" (.vint 5)) (.binop .add (.vvar 0) (.vint 1)))
#guard yieldsIntE (runE 200 customWitness) 106
#guard yieldsIntE (Bang.Source.eval 200 customWitness) 106

-- CUSTOM abort coexist: custom frame BETWEEN a raise and its throws handler; `raise 42` aborts PAST
-- the custom frame to throws ⇒ 42 (the read continuation never runs). Shows custom dispatch doesn't
-- break a coexisting built-in's zero-shot abort — the id-first σ→τ→κ order + throws catch, together.
private def customAbortWitness : Comp :=
  .handle (.throws 2)
    (.handle (.custom 1 (.vint 100) [("read", .binop .add (.vvar 0) (.vvar 1))])
      (.letC (.perform (.vvar 1) "raise" (.vint 42)) (.perform (.vvar 0) "read" (.vint 5))))
#guard yieldsIntE (runE 200 customAbortWitness) 42
#guard yieldsIntE (Bang.Source.eval 200 customAbortWitness) 42

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
