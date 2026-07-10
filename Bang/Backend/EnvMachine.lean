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

/-- **The correspondence STATEMENT** (PLFA `γ≈ₑσ`; slice-3 proof).

If `evalE` runs `M` under `ρ` to a returner `mret mv`, and `ρ` agrees with a substitution
`σ`, then the substitution reference `evalD` (over the σ-substituted term) returns the
read-back value. Generalized from the empty env to an arbitrary `ρ`/`σ` per PLFA's warning
(the induction won't fire on the empty-env special case).

`sorry` body — this is the slice-3 obligation; slice 1 confirms only that the statement
TYPECHECKS (the domains + readback compose) and that the mini-Agree probe below holds
concretely. -/
theorem evalE_agrees_evalD (f : Nat) (γ : List Val) (M : Comp) (mv : MVal)
    (eσ : ESStore) (eτ : ETHeap) (eκ : ECStore) (ρ : MEnv) (g' : Nat)
    (eσ' : ESStore) (eτ' : ETHeap) (eκ' : ECStore)
    (_hagree : EnvAgrees ρ γ)
    (_h : evalE f 0 eσ eτ eκ ρ M = some (.mterm (.mret mv), g', eσ', eτ', eκ')) :
    ∃ F g'' σ' τ' κ',
      Bang.CalcVM.evalD F 0 [] [] [] (substEnv γ M)
        = some (.term (.ret (readback mv)), g'', σ', τ', κ') := by
  sorry -- SLICE-3: the PLFA γ≈ₑσ induction (generalize-from-empty-env; env↔subst correspondence)

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
