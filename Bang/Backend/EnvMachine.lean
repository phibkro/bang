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

The `evalE_agrees_evalD` **correspondence** (the PLFA `γ≈ₑσ` shape) is PROVEN here (slice 3,
ruling #6/#1): its `_gen`/`_effect` engine generalizes from the empty env to an arbitrary `ρ`
+ the `≈ₑ` premise so the induction fires (PLFA's own warning, `envsem-survey.md` §2), and the
top-level headline is the empty-store corollary.

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

-- RETIRED (task #15): the transplanted closing-substitution ENGINE is HOISTED to
-- `Bang/Core/Semantics/Subst.lean` §1.3c. `Val.ClosedE` is now an `abbrev` of the hoisted `Val.Closed`,
-- so its dotted accessors (`.shift`/`.shiftFrom_eq`/`.subst_at`) resolve straight to the hoisted proofs
-- and the local copies are deleted. `shiftNE`/`closeUnderBindersE` stay `def`s BYTE-IDENTICAL to the
-- hoisted `shiftN`/`closeCUnderBinders` (they carry `simp only [·]`/`rw [·]` unfold sites the machine's
-- distribution lemmas depend on), and the crux lemmas below delegate to the hoisted engine by defeq —
-- so the former swap/commutation mutuals are deleted. The green build IS the proof the copies were faithful.
/-- A value with no free de Bruijn indices — the machine's alias of the hoisted `Val.Closed`. -/
abbrev Val.ClosedE (v : Val) : Prop := Val.Closed v

/-- Iterated `Val.shift` (weaken past `d` binders) — byte-identical to the hoisted `shiftN`. -/
def shiftNE : Nat → Val → Val
  | 0,     v => v
  | d + 1, v => Val.shift (shiftNE d v)

/-- A closed value is fixed by `shiftNE d` — the `shiftNE`-stated adapter of the hoisted `shiftN_closed`
(the swap ENGINE it rode is retired; this thin fact over the machine's own `shiftNE` def stays). -/
theorem shiftNE_closed {v : Val} (h : Val.ClosedE v) : ∀ d, shiftNE d v = v
  | 0     => rfl
  | d + 1 => by show Val.shift (shiftNE d v) = v; rw [shiftNE_closed h d, h.shift]

/-- Apply the closing env `δ` to a term under `d` fresh binders — byte-identical to hoisted
`closeCUnderBinders`. -/
def closeUnderBindersE (d : Nat) : List Val → Comp → Comp
  | [],     c => c
  | v :: δ, c => closeUnderBindersE d δ (Comp.substFrom d (shiftNE d v) c)
-- RETIRED (task #15): the adjacent substitution-swap mutual ({Val,Comp,Handler}.substFrom_swap_closedE)
-- is HOISTED as {Val,Comp,Handler}.substFrom_swap_closed (Bang/Core/Semantics/Subst.lean §1.3c). The
-- crux `substEnv_cons_subst` below consumes the hoisted `closeC_subst_comm` directly.

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

/-- **W3 (envm3)**: readback of a machine OUTCOME to `evalD`'s `Outcome`, extending `readbackTerm` to the
`mraised` terminal (the third `evalD` `Outcome`). A `mterm t` reads back as `readbackTerm t`; a `mraised
n op mv` reads back as `raised n op (readback mv)` — the payload is a value, so the extension is
structural. This is the conclusion target of the outcome-GENERAL `_gen` lemma the 3b induction needs
(the term-only `evalE_agrees_evalD_effect` is its `mterm`-half corollary). -/
def readbackTermS : MOutcome → Bang.CalcVM.Outcome
  | .mterm t        => readbackTerm t
  | .mraised n op mv => .raised n op (readback mv)

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

/-- **THE CRUX** (= the hoisted `closeC_subst_comm`): filling a fresh level-0 binder with a CLOSED `w`
after applying the closing env `γ` lifted past one binder equals applying `w :: γ` directly. Closes the
binding cases of `evalE_agrees_evalD` — the env-extension `w ∷ₑ ρ` matches `Comp.subst w` under the
lifted tail. Delegates to the hoisted engine (task #15): `substEnv`/`closeUnderBindersE`/`Val.ClosedE`
are aliases of `closeC`/`closeCUnderBinders`/`Val.Closed`, so this is exactly `closeC_subst_comm`. -/
theorem substEnv_cons_subst {γ : List Val} (hγ : ∀ v ∈ γ, Val.ClosedE v)
    {w : Val} (_hw : Val.ClosedE w) (N : Comp) :
    (closeUnderBindersE 1 γ N).subst w = substEnv (w :: γ) N := by
  -- substEnv (w :: γ) N = substEnv γ (Comp.subst w N); induction on γ. Same shape as the hoisted
  -- `closeC_subst_comm` (task #15), now consuming the hoisted `Comp.substFrom_swap_closed` swap.
  show (closeUnderBindersE 1 γ N).subst w = substEnv γ (Comp.subst w N)
  induction γ generalizing N with
  | nil => rfl
  | cons v γ ih =>
    have hv : Val.ClosedE v := hγ v List.mem_cons_self
    have hγ' : ∀ u ∈ γ, Val.ClosedE u := fun u hu => hγ u (List.mem_cons_of_mem v hu)
    simp only [closeUnderBindersE, substEnv, shiftNE, hv.shift]
    rw [ih hγ' (Comp.substFrom 1 v N)]
    congr 1
    exact Comp.substFrom_swap_closed hv _hw 0 N

/-! ### The 2-binder crux (`split`) — over the hoisted `_ge` swap engine (task #15) -/

-- RETIRED (task #15): the non-adjacent swap mutual ({Val,Comp,Handler}.substFrom_swap_closed_geE) is
-- HOISTED as {Val,Comp,Handler}.substFrom_swap_closed_ge (Bang/Core/Semantics/Subst.lean §1.3c). The
-- level-0-descent helpers below stay `def`-local (they thread `closeUnderBindersE`, the machine's own
-- def) but consume the hoisted `_ge` swap; the 2-binder crux keeps its structure over them.

/-- `closeUnderBindersE 0 = substEnv` (level-0 subst, no weakening). -/
theorem closeUnderBindersE_zero (γ : List Val) (c : Comp) : closeUnderBindersE 0 γ c = substEnv γ c := by
  induction γ generalizing c with
  | nil => rfl
  | cons v γ ih => simp only [closeUnderBindersE, substEnv, Comp.subst, shiftNE]; exact ih _

/-- Level-0 descent through `closeUnderBindersE (d+1)` for a CLOSED filler (drops the binder-depth by one;
non-adjacent swap). Engine behind the 2-binder split crux; consumes the hoisted `Comp.substFrom_swap_closed_ge`. -/
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
    exact Comp.substFrom_swap_closed_ge hv hw 0 d (Nat.zero_le d) N

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

@[simp] theorem substEnv_perform (γ : List Val) (cp : Val) (op : Bang.OpId) (w : Val) :
    substEnv γ (Comp.perform cp op w) = Comp.perform (substEnvV γ cp) op (substEnvV γ w) := by
  induction γ generalizing cp w with
  | nil => rfl
  | cons v γ ih => simp only [substEnv, substEnvV, Comp.subst, Comp.substFrom]; exact ih _ _

/-- The handler-payload closing fold (`Handler.substFrom` folded over `γ`) — the `substEnv` analog for
a handler. -/
def substEnvH : List Val → Handler → Handler
  | [],     h => h
  | v :: γ, h => substEnvH γ (Handler.substFrom 0 v h)

/-- `substEnv` distributes into a `handle`: the handler payload substitutes (via `substEnvH`) and the
body closes under ONE binder (handle binds the cap at 0). The three handler kinds' payloads: `state s`
substitutes `s`; `transaction Θ`/`custom p cls` are IDENTITY on their payloads (closed, ADR-0030/0085) —
so their `substEnv` image keeps `Θ`/`(p, cls)` verbatim. -/
@[simp] theorem substEnv_handle (γ : List Val) (h : Handler) (M : Comp) :
    substEnv γ (Comp.handle h M) = Comp.handle (substEnvH γ h) (closeUnderBindersE 1 γ M) := by
  induction γ generalizing h M with
  | nil => rfl
  | cons v γ ih =>
    simp only [substEnv, closeUnderBindersE, Comp.subst, Comp.substFrom, shiftNE, substEnvH]
    exact ih _ _

@[simp] theorem substEnvH_state (γ : List Val) (ℓ : Bang.EffectRow.Label) (s : Val) :
    substEnvH γ (Handler.state ℓ s) = Handler.state ℓ (substEnvV γ s) := by
  induction γ generalizing s with
  | nil => rfl
  | cons v γ ih => simp only [substEnvH, Handler.substFrom, substEnvV, Val.subst]; exact ih _
@[simp] theorem substEnvH_transaction (γ : List Val) (ℓ : Bang.EffectRow.Label) (Θ : List Val) :
    substEnvH γ (Handler.transaction ℓ Θ) = Handler.transaction ℓ Θ := by
  induction γ with
  | nil => rfl
  | cons v γ ih => simp only [substEnvH, Handler.substFrom]; exact ih
@[simp] theorem substEnvH_custom (γ : List Val) (ℓ : Bang.EffectRow.Label) (p : Val)
    (cls : List (Bang.OpId × Comp)) :
    substEnvH γ (Handler.custom ℓ p cls) = Handler.custom ℓ p cls := by
  induction γ with
  | nil => rfl
  | cons v γ ih => simp only [substEnvH, Handler.substFrom]; exact ih
@[simp] theorem substEnvH_throws (γ : List Val) (ℓ : Bang.EffectRow.Label) :
    substEnvH γ (Handler.throws ℓ) = Handler.throws ℓ := by
  induction γ with
  | nil => rfl
  | cons v γ ih => simp only [substEnvH, Handler.substFrom]; exact ih
/-- `Handler.label` is preserved by the closing fold (it only rewrites payloads, never the label). -/
@[simp] theorem substEnvH_label (γ : List Val) (h : Handler) :
    Handler.label (substEnvH γ h) = Handler.label h := by
  cases h with
  | state ℓ s => simp only [substEnvH_state, Handler.label]
  | transaction ℓ Θ => simp only [substEnvH_transaction]
  | custom ℓ p cls => simp only [substEnvH_custom]
  | throws ℓ => simp only [substEnvH_throws]

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
theorem Comp.ScopedC.perform_inv {n : Nat} {cp w : Val} {op : Bang.OpId}
    (h : Comp.ScopedC n (Comp.perform cp op w)) : Val.ScopedV n cp ∧ Val.ScopedV n w := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;>
    · have := h k hk; simp only [Comp.shiftFrom, Comp.perform.injEq] at this
      first | exact this.1 | exact this.2.2
theorem Comp.ScopedC.handle_inv {n : Nat} {hdl : Handler} {M : Comp}
    (h : Comp.ScopedC n (Comp.handle hdl M)) : Comp.ScopedC (n + 1) M := by
  intro k hk; have := h (k - 1) (by omega)
  simp only [Comp.shiftFrom, Comp.handle.injEq] at this
  rw [show k = (k - 1) + 1 by omega]; exact this.2

/-- Scope MONOTONICITY: a term scoped under `a` is scoped under any `b ≥ a` (a smaller free-index bound
is also a larger one). Immediate from the `∀ k ≥ n, shiftFrom k = id` phrasing. -/
theorem Comp.ScopedC.mono {a b : Nat} {M : Comp} (h : Comp.ScopedC a M) (hab : a ≤ b) :
    Comp.ScopedC b M := fun k hk => h k (Nat.le_trans hab hk)
theorem Val.ScopedV.mono {a b : Nat} {v : Val} (h : Val.ScopedV a v) (hab : a ≤ b) :
    Val.ScopedV b v := fun k hk => h k (Nat.le_trans hab hk)

/-! ### `substFrom`-above-scope is identity — the close-is-identity engine (ruling #6, task #11)

`Comp.substFrom d w M = M` when `M` is `ScopedC d` (M has no free index `≥ d`, so the substitution at
level `d` touches nothing). Derived from `substFrom d w (shiftFrom d M) = M` (the round-trip below) by
rewriting `shiftFrom d M = M` (the `ScopedC d` witness). The round-trip is a TRANSPLANT of the private
`Bang.Comp.substFrom_shiftFrom`/`Handler.substFrom_shiftFrom` (public `Val.substFrom_shiftFrom` at the
leaves) — task #15 retires the transplant with the rest. -/

-- TODO(hoist, task #15): faithful duplicate of the private Bang.{Comp,Handler}.substFrom_shiftFrom.
mutual
theorem Comp.substFrom_shiftFromE (k : Nat) (v : Val) :
    ∀ t : Comp, Comp.substFrom k v (Comp.shiftFrom k t) = t
  | .ret w       => by simp only [Comp.shiftFrom, Comp.substFrom, Bang.Val.substFrom_shiftFrom k v w]
  | .letC M N    => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Comp.substFrom_shiftFromE k v M, Comp.substFrom_shiftFromE (k + 1) (Val.shift v) N]
  | .force w     => by simp only [Comp.shiftFrom, Comp.substFrom, Bang.Val.substFrom_shiftFrom k v w]
  | .lam M       => by
      simp only [Comp.shiftFrom, Comp.substFrom, Comp.substFrom_shiftFromE (k + 1) (Val.shift v) M]
  | .app M w     => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Comp.substFrom_shiftFromE k v M, Bang.Val.substFrom_shiftFrom k v w]
  | .perform cp op w   => by simp only [Comp.shiftFrom, Comp.substFrom,
      Bang.Val.substFrom_shiftFrom k v cp, Bang.Val.substFrom_shiftFrom k v w]
  | .handle h M  => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Handler.substFrom_shiftFromE k v h, Comp.substFrom_shiftFromE (k + 1) (Val.shift v) M]
  | .case w N₁ N₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom, Bang.Val.substFrom_shiftFrom k v w,
        Comp.substFrom_shiftFromE (k + 1) (Val.shift v) N₁,
        Comp.substFrom_shiftFromE (k + 1) (Val.shift v) N₂]
  | .split w N   => by
      simp only [Comp.shiftFrom, Comp.substFrom, Bang.Val.substFrom_shiftFrom k v w,
        Comp.substFrom_shiftFromE (k + 2) (Val.shift (Val.shift v)) N]
  | .unfold w    => by simp only [Comp.shiftFrom, Comp.substFrom, Bang.Val.substFrom_shiftFrom k v w]
  | .binop op w₁ w₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Bang.Val.substFrom_shiftFrom k v w₁, Bang.Val.substFrom_shiftFrom k v w₂]
  | .oom         => rfl
  | .wrong _     => rfl
theorem Handler.substFrom_shiftFromE (k : Nat) (v : Val) :
    ∀ h : Handler, Handler.substFrom k v (Handler.shiftFrom k h) = h
  | .state ℓ s       => by simp only [Handler.shiftFrom, Handler.substFrom, Bang.Val.substFrom_shiftFrom k v s]
  | .throws _        => rfl
  | .transaction _ _ => rfl
  | .custom _ _ _    => rfl
end

/-- `substFrom` at a cutoff `≥` the scope is the IDENTITY: a term scoped under `d` has no free index at
`d` or above, so substituting at level `d` fixes it. The close-is-identity primitive. -/
theorem Comp.ScopedC.substFrom_eq {d : Nat} {M : Comp} (h : Comp.ScopedC d M) (w : Val) :
    Comp.substFrom d w M = M := by
  conv_lhs => rw [← h d (Nat.le_refl d)]
  exact Comp.substFrom_shiftFromE d w M

/-- **CLOSE-IS-IDENTITY BELOW THRESHOLD** (ruling #6): closing a `ScopedC d` body over ANY env at binder
depth `d` is the identity — every filler substitutes at level `d`, which the body's scope makes vacuous.
This is what collapses `CStoreCorr`'s `closeUnderBindersE 2` clause-map to the identity on a payload-closed
(`ScopedC 2`) clause, so it agrees with `evalD`'s RAW-`cls` push at the custom-handle install. -/
theorem closeUnderBindersE_scoped_id {d : Nat} {M : Comp} (h : Comp.ScopedC d M) :
    ∀ γ : List Val, closeUnderBindersE d γ M = M
  | [] => rfl
  | v :: γ => by
      rw [closeUnderBindersE, h.substFrom_eq (shiftNE d v)]
      exact closeUnderBindersE_scoped_id h γ

/-! ### `Comp.HandlerWF` — the handler-payload-scope premise (ADR-0030/0085; the txn/custom obligation)

`Comp.ScopedC` is IDENTITY on `transaction`/`custom` handler payloads (`Handler.shiftFrom` leaves `Θ`,
`p`, `cls` untouched, on purpose — the CK focus is always closed, ADR-0025/0030/0085), so scope alone
CANNOT witness that a `transaction`'s heap cells or a `custom`'s clauses are closed/scoped. But the
`_gen` correspondence's `handle` case NEEDS exactly that:

- TXN: `evalE` pushes `Θ.map (evalV ρ)` while `evalD` pushes the RAW `Θ`; `THeapCorr` on the pushed
  frames forces `readback (evalV ρ θ) = θ` for each `θ ∈ Θ`, i.e. `Val.ClosedE θ` (each heap cell is
  closed — ADR-0030's "transaction heaps are closed" invariant, made explicit).
- CUSTOM: the handler's clause bodies are PAYLOAD-CLOSED — free only in their own two service binders
  (op-arg at 0, param at 1), i.e. ABSOLUTE `Comp.ScopedC 2 c.2` (NOT `n + 2` relative) — and `p` closed
  (`Val.ScopedV 0 p`). This mirrors the kernel's payload-identity substitution on custom (ruling #6,
  task #11): a clause open into the enclosing scope would hit dangling indices at clause-run, so the
  absolute premise excludes exactly the junk `Comp.subst`/`Handler.shiftFrom` already treat as closed.
  It makes `closeUnderBindersE 2 (readbackEnv ρ) c.2 = c.2`, so `CStoreCorr`'s clause map is IDENTITY
  and agrees with `evalD`'s RAW-`cls` push at the custom-handle install.

`Comp.HandlerWF n M` states this at EVERY `handle` reachable in `M`, index-tracked (the binder depth `n`
descends by 1 into a `handle`/`letC`/`lam`/`case` body, by 2 into `split`; a custom handler's clause
bodies are checked at ABSOLUTE scope 2 — payload-closed, per ruling #6). It is MUTUAL with `Val.HandlerWF`
(descending through every
value position, chiefly `vthunk`'s captured `Comp`) so the invariant rides thunks/closures the same way
`ScopedC`/`ScopedV` do — the `force`/`app` entry points re-enter a captured body, so a body's handlers
must be constrained THROUGH the value that carries it. It is the machine-side twin of the kernel's
closed-heap discipline: a caller (the headline / `_effect`, over a well-formed program) discharges it
structurally. -/
mutual
def Comp.HandlerWF : Nat → Comp → Prop
  | n, .ret v        => Val.HandlerWF n v
  | n, .force w      => Val.HandlerWF n w
  | n, .unfold w     => Val.HandlerWF n w
  | n, .binop _ v w  => Val.HandlerWF n v ∧ Val.HandlerWF n w
  | _, .oom          => True
  | _, .wrong _      => True
  | n, .perform c _ v => Val.HandlerWF n c ∧ Val.HandlerWF n v
  | n, .letC M N     => Comp.HandlerWF n M ∧ Comp.HandlerWF (n + 1) N
  | n, .lam M        => Comp.HandlerWF (n + 1) M
  | n, .app M w      => Comp.HandlerWF n M ∧ Val.HandlerWF n w
  | n, .case w N₁ N₂ => Val.HandlerWF n w ∧ Comp.HandlerWF (n + 1) N₁ ∧ Comp.HandlerWF (n + 1) N₂
  | n, .split w N    => Val.HandlerWF n w ∧ Comp.HandlerWF (n + 2) N
  | n, .handle h M   =>
      (match h with
        | .state _ s => Val.HandlerWF n s
        | .throws _ => True
        | .transaction _ Θ => ∀ θ ∈ Θ, Val.ClosedE θ ∧ ∀ m, Val.HandlerWF m θ
        -- CUSTOM: PAYLOAD-CLOSED (ruling #6, task #11). The clause bodies are free only in their own
        -- two service binders (op-arg at 0, param at 1) — ABSOLUTE scope 2, NOT `n+2` relative — and
        -- the param `p` is closed (`ScopedV 0`). This states the kernel's own contract: `Comp.subst`/
        -- `Handler.shiftFrom` are DELIBERATELY identity on a custom payload ("the CK focus is always
        -- closed", ADR-0025/0030/0085 · Subst.lean:75-89), so a clause open INTO the enclosing scope is
        -- semantically meaningless under payload-identity substitution (its extra frees never get bound).
        -- Elaboration emits exactly payload-closed handlers, so the premise is real at every entry.
        -- Each clause is scoped (`ScopedC 2`); the clause bodies' own handler-wellformedness rides
        -- `Comp.HandlerWFClauses` — a MUTUAL sibling that recurses STRUCTURALLY on the clause LIST
        -- (destructuring `(_, body) :: cs`), the termination-safe way to state `HandlerWF 2` per clause
        -- (a direct recursive `HandlerWF` call on `c.2` here is not a structural subterm ⇒ non-terminating).
        | .custom _ p cls => (Val.ScopedV 0 p ∧ Val.HandlerWF 0 p) ∧ (∀ c ∈ cls, Comp.ScopedC 2 c.2)
            ∧ Comp.HandlerWFClauses cls)
      ∧ Comp.HandlerWF (n + 1) M
def Val.HandlerWF : Nat → Val → Prop
  | _, .vunit    => True
  | _, .vint _   => True
  | _, .vvar _   => True
  | _, .vcap _ _ => True
  | n, .vthunk M => Comp.HandlerWF n M
  | n, .inl w    => Val.HandlerWF n w
  | n, .inr w    => Val.HandlerWF n w
  | n, .pair w₁ w₂ => Val.HandlerWF n w₁ ∧ Val.HandlerWF n w₂
  | n, .fold w   => Val.HandlerWF n w
/-- Handler-wellformedness of a custom handler's CLAUSE LIST, at the payload-closed absolute scope 2.
Recurses STRUCTURALLY on the list (destructures `(_, body) :: cs`), which exposes `body` as a direct
subterm — the termination-safe way to require `Comp.HandlerWF 2` of each clause body (a direct recursive
`HandlerWF` call inside the `custom` obligation is not a structural subterm of the `handle`). -/
def Comp.HandlerWFClauses : List (Bang.OpId × Comp) → Prop
  | []             => True
  | (_, body) :: cs => Comp.HandlerWF 2 body ∧ Comp.HandlerWFClauses cs
end

theorem Comp.HandlerWF.ret_inv {n : Nat} {v : Val} (h : Comp.HandlerWF n (Comp.ret v)) :
    Val.HandlerWF n v := by simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.force_inv {n : Nat} {w : Val} (h : Comp.HandlerWF n (Comp.force w)) :
    Val.HandlerWF n w := by simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.unfold_inv {n : Nat} {w : Val} (h : Comp.HandlerWF n (Comp.unfold w)) :
    Val.HandlerWF n w := by simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.binop_inv {n : Nat} {op : BinOp} {a b : Val}
    (h : Comp.HandlerWF n (Comp.binop op a b)) : Val.HandlerWF n a ∧ Val.HandlerWF n b := by
  simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.letC_inv {n : Nat} {M N : Comp} (h : Comp.HandlerWF n (Comp.letC M N)) :
    Comp.HandlerWF n M ∧ Comp.HandlerWF (n + 1) N := by simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.lam_inv {n : Nat} {M : Comp} (h : Comp.HandlerWF n (Comp.lam M)) :
    Comp.HandlerWF (n + 1) M := by simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.app_inv {n : Nat} {M : Comp} {w : Val} (h : Comp.HandlerWF n (Comp.app M w)) :
    Comp.HandlerWF n M ∧ Val.HandlerWF n w := by simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.case_inv {n : Nat} {w : Val} {N₁ N₂ : Comp}
    (h : Comp.HandlerWF n (Comp.case w N₁ N₂)) :
    Val.HandlerWF n w ∧ Comp.HandlerWF (n + 1) N₁ ∧ Comp.HandlerWF (n + 1) N₂ := by
  simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.split_inv {n : Nat} {w : Val} {N : Comp}
    (h : Comp.HandlerWF n (Comp.split w N)) : Val.HandlerWF n w ∧ Comp.HandlerWF (n + 2) N := by
  simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.perform_inv {n : Nat} {c w : Val} {op : Bang.OpId}
    (h : Comp.HandlerWF n (Comp.perform c op w)) : Val.HandlerWF n c ∧ Val.HandlerWF n w := by
  simp only [Comp.HandlerWF] at h; exact h
theorem Comp.HandlerWF.handle_body {n : Nat} {hdl : Handler} {M : Comp}
    (h : Comp.HandlerWF n (Comp.handle hdl M)) : Comp.HandlerWF (n + 1) M := by
  cases hdl <;> (simp only [Comp.HandlerWF] at h; exact h.2)
theorem Comp.HandlerWF.handle_state {n : Nat} {ℓ : Bang.EffectRow.Label} {s : Val} {M : Comp}
    (h : Comp.HandlerWF n (Comp.handle (Handler.state ℓ s) M)) : Val.HandlerWF n s := by
  simp only [Comp.HandlerWF] at h; exact h.1
theorem Comp.HandlerWF.handle_txn {n : Nat} {ℓ : Bang.EffectRow.Label} {Θ : List Val} {M : Comp}
    (h : Comp.HandlerWF n (Comp.handle (Handler.transaction ℓ Θ) M)) :
    ∀ θ ∈ Θ, Val.ClosedE θ ∧ ∀ m, Val.HandlerWF m θ := by
  simp only [Comp.HandlerWF] at h; exact h.1
theorem Comp.HandlerWF.handle_custom {n : Nat} {ℓ : Bang.EffectRow.Label} {p : Val}
    {cls : List (Bang.OpId × Comp)} {M : Comp}
    (h : Comp.HandlerWF n (Comp.handle (Handler.custom ℓ p cls) M)) :
    (Val.ScopedV 0 p ∧ Val.HandlerWF 0 p) ∧ (∀ c ∈ cls, Comp.ScopedC 2 c.2)
      ∧ Comp.HandlerWFClauses cls := by
  simp only [Comp.HandlerWF] at h; exact h.1

/-- Per-CLAUSE `HandlerWF 2` from the clause-list invariant `Comp.HandlerWFClauses cls` (walk the list). -/
theorem Comp.HandlerWFClauses.get {cls : List (Bang.OpId × Comp)}
    (h : Comp.HandlerWFClauses cls) : ∀ c ∈ cls, Comp.HandlerWF 2 c.2 := by
  induction cls with
  | nil => intro c hc; simp only [List.not_mem_nil] at hc
  | cons c cs ih =>
      obtain ⟨_, body⟩ := c
      simp only [Comp.HandlerWFClauses] at h
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h.1
      · exact ih h.2 d hd

/-! `Comp.HandlerWF`/`Val.HandlerWF` MONOTONICITY: the index `n` only gates state-payload obligations
(`Val.HandlerWF n s`), which descend structurally; the txn/custom payload obligations are `n`-INDEPENDENT
(closed / absolute-scope-2). So a larger `n` is weaker — every witness at `a` is a witness at any `b ≥ a`. -/
mutual
theorem Comp.HandlerWF.mono : ∀ (M : Comp) (a b : Nat), a ≤ b → Comp.HandlerWF a M → Comp.HandlerWF b M
  | .ret v,        a, b, hab, h => by simp only [Comp.HandlerWF] at h ⊢; exact Val.HandlerWF.mono v a b hab h
  | .force w,      a, b, hab, h => by simp only [Comp.HandlerWF] at h ⊢; exact Val.HandlerWF.mono w a b hab h
  | .unfold w,     a, b, hab, h => by simp only [Comp.HandlerWF] at h ⊢; exact Val.HandlerWF.mono w a b hab h
  | .binop _ v w,  a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢
      exact ⟨Val.HandlerWF.mono v a b hab h.1, Val.HandlerWF.mono w a b hab h.2⟩
  | .oom,          _, _, _,   _ => by simp only [Comp.HandlerWF]
  | .wrong _,      _, _, _,   _ => by simp only [Comp.HandlerWF]
  | .perform c _ v, a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢
      exact ⟨Val.HandlerWF.mono c a b hab h.1, Val.HandlerWF.mono v a b hab h.2⟩
  | .letC M N,     a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢
      exact ⟨Comp.HandlerWF.mono M a b hab h.1, Comp.HandlerWF.mono N (a+1) (b+1) (by omega) h.2⟩
  | .lam M,        a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢; exact Comp.HandlerWF.mono M (a+1) (b+1) (by omega) h
  | .app M w,      a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢
      exact ⟨Comp.HandlerWF.mono M a b hab h.1, Val.HandlerWF.mono w a b hab h.2⟩
  | .case w N₁ N₂, a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢
      exact ⟨Val.HandlerWF.mono w a b hab h.1, Comp.HandlerWF.mono N₁ (a+1) (b+1) (by omega) h.2.1,
        Comp.HandlerWF.mono N₂ (a+1) (b+1) (by omega) h.2.2⟩
  | .split w N,    a, b, hab, h => by
      simp only [Comp.HandlerWF] at h ⊢
      exact ⟨Val.HandlerWF.mono w a b hab h.1, Comp.HandlerWF.mono N (a+2) (b+2) (by omega) h.2⟩
  | .handle hdl M, a, b, hab, h => by
      cases hdl with
      | state _ s =>
          simp only [Comp.HandlerWF] at h ⊢
          exact ⟨Val.HandlerWF.mono s a b hab h.1, Comp.HandlerWF.mono M (a+1) (b+1) (by omega) h.2⟩
      | throws _ =>
          simp only [Comp.HandlerWF] at h ⊢
          exact ⟨h.1, Comp.HandlerWF.mono M (a+1) (b+1) (by omega) h.2⟩
      | transaction _ Θ =>
          simp only [Comp.HandlerWF] at h ⊢
          exact ⟨h.1, Comp.HandlerWF.mono M (a+1) (b+1) (by omega) h.2⟩
      | custom _ p cls =>
          simp only [Comp.HandlerWF] at h ⊢
          exact ⟨h.1, Comp.HandlerWF.mono M (a+1) (b+1) (by omega) h.2⟩
theorem Val.HandlerWF.mono : ∀ (v : Val) (a b : Nat), a ≤ b → Val.HandlerWF a v → Val.HandlerWF b v
  | .vunit,    _, _, _,   _ => by simp only [Val.HandlerWF]
  | .vint _,   _, _, _,   _ => by simp only [Val.HandlerWF]
  | .vvar _,   _, _, _,   _ => by simp only [Val.HandlerWF]
  | .vcap _ _, _, _, _,   _ => by simp only [Val.HandlerWF]
  | .vthunk M, a, b, hab, h => by simp only [Val.HandlerWF] at h ⊢; exact Comp.HandlerWF.mono M a b hab h
  | .inl w,    a, b, hab, h => by simp only [Val.HandlerWF] at h ⊢; exact Val.HandlerWF.mono w a b hab h
  | .inr w,    a, b, hab, h => by simp only [Val.HandlerWF] at h ⊢; exact Val.HandlerWF.mono w a b hab h
  | .pair w₁ w₂, a, b, hab, h => by
      simp only [Val.HandlerWF] at h ⊢
      exact ⟨Val.HandlerWF.mono w₁ a b hab h.1, Val.HandlerWF.mono w₂ a b hab h.2⟩
  | .fold w,   a, b, hab, h => by simp only [Val.HandlerWF] at h ⊢; exact Val.HandlerWF.mono w a b hab h
end

/-! ### Closedness of `substEnv`/`substEnvV` from scope (slice-3a: the WF-preservation core)

Closing a term SCOPED under `|γ|` over a CLOSED env `γ` yields a CLOSED term — the fold substitutes
each free index with a closed filler, dropping the scope by one each step to `ScopedV 0 = ClosedE`.
This is what makes `evalV`/`evalE` results read back closed (a closure `mvclos M ρ` reads back closed
because `M` scoped + `readbackEnv ρ` closed ⇒ `substEnv (readbackEnv ρ) M` closed). Transplanted
`shiftFrom_substFrom_closed` (the closed-filler shift/subst commutation) + `closeV_closed_scoped`
from BinaryLR (task #15 retires). -/

-- RETIRED (task #15): the closed-filler shift/subst commutation mutual
-- ({Val,Comp,Handler}.shiftFrom_substFrom_closedE) is HOISTED as {Val,Comp,Handler}.shiftFrom_substFrom_closed
-- (Bang/Core/Semantics/Subst.lean §1.3c). The `subst_closed` consumers below use the hoisted names.

/-- Substituting the level-0 binder of an `(m+1)`-scoped VALUE with a CLOSED filler drops scope to `m`. -/
theorem Val.ScopedV.subst_closed {m : Nat} {u v : Val} (hu : Val.ClosedE u)
    (hv : Val.ScopedV (m + 1) v) : Val.ScopedV m (Val.subst u v) := by
  intro k hk
  rw [Val.subst, Val.shiftFrom_substFrom_closed hu k 0 (Nat.zero_le k) v, hv (k + 1) (by omega)]
/-- The same for a COMPUTATION. -/
theorem Comp.ScopedC.subst_closed {m : Nat} {u : Val} {M : Comp} (hu : Val.ClosedE u)
    (hM : Comp.ScopedC (m + 1) M) : Comp.ScopedC m (Comp.subst u M) := by
  intro k hk
  rw [Comp.subst, Comp.shiftFrom_substFrom_closed hu k 0 (Nat.zero_le k) M, hM (k + 1) (by omega)]

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

/-! `EffectFree ⇒ HandlerWF` (vacuously, at any index): an `EffectFree` term has NO `handle`/`perform`,
so `HandlerWF`'s only non-trivial obligations (at `handle` nodes) never arise. This is what lets the
`PureV → WFClos` bridge produce the closure clause's new `HandlerWF` conjunct from `PureV`'s `EffectFree`
body. Mutual over `Comp`/`Val` (the thunk descent), mirroring `EffectFree`/`ValEF`. -/
mutual
theorem EffectFree.handlerWF : ∀ {M : Comp}, EffectFree M → ∀ n, Comp.HandlerWF n M
  | .ret v, h, n => by simp only [Comp.HandlerWF]; exact (by simpa only [EffectFree] using h : ValEF v).handlerWF n
  | .force w, h, n => by simp only [Comp.HandlerWF]; exact (by simpa only [EffectFree] using h : ValEF w).handlerWF n
  | .unfold w, h, n => by simp only [Comp.HandlerWF]; exact (by simpa only [EffectFree] using h : ValEF w).handlerWF n
  | .binop _ a b, h, n => by
      simp only [Comp.HandlerWF]
      obtain ⟨ha, hb⟩ := (by simpa only [EffectFree] using h : ValEF a ∧ ValEF b)
      exact ⟨ha.handlerWF n, hb.handlerWF n⟩
  | .oom, _, n => by simp only [Comp.HandlerWF]
  | .wrong _, _, n => by simp only [Comp.HandlerWF]
  | .letC M N, h, n => by
      simp only [Comp.HandlerWF]
      obtain ⟨hM, hN⟩ := (by simpa only [EffectFree] using h : EffectFree M ∧ EffectFree N)
      exact ⟨hM.handlerWF n, hN.handlerWF (n + 1)⟩
  | .lam M, h, n => by
      simp only [Comp.HandlerWF]
      exact (by simpa only [EffectFree] using h : EffectFree M).handlerWF (n + 1)
  | .app M w, h, n => by
      simp only [Comp.HandlerWF]
      obtain ⟨hM, hw⟩ := (by simpa only [EffectFree] using h : EffectFree M ∧ ValEF w)
      exact ⟨hM.handlerWF n, hw.handlerWF n⟩
  | .case w N₁ N₂, h, n => by
      simp only [Comp.HandlerWF]
      obtain ⟨hw, hN₁, hN₂⟩ := (by simpa only [EffectFree] using h : ValEF w ∧ EffectFree N₁ ∧ EffectFree N₂)
      exact ⟨hw.handlerWF n, hN₁.handlerWF (n + 1), hN₂.handlerWF (n + 1)⟩
  | .split w N, h, n => by
      simp only [Comp.HandlerWF]
      obtain ⟨hw, hN⟩ := (by simpa only [EffectFree] using h : ValEF w ∧ EffectFree N)
      exact ⟨hw.handlerWF n, hN.handlerWF (n + 2)⟩
  | .perform _ _ _, h, _ => absurd h (by simp only [EffectFree, not_false_eq_true])
  | .handle _ _, h, _ => absurd h (by simp only [EffectFree, not_false_eq_true])
theorem ValEF.handlerWF : ∀ {v : Val}, ValEF v → ∀ n, Val.HandlerWF n v
  | .vunit, _, n => by simp only [Val.HandlerWF]
  | .vint _, _, n => by simp only [Val.HandlerWF]
  | .vvar _, _, n => by simp only [Val.HandlerWF]
  | .vcap _ _, _, n => by simp only [Val.HandlerWF]
  | .vthunk M, h, n => by simp only [Val.HandlerWF]; exact (by simpa only [ValEF] using h : EffectFree M).handlerWF n
  | .inl w, h, n => by simp only [Val.HandlerWF]; exact (by simpa only [ValEF] using h : ValEF w).handlerWF n
  | .inr w, h, n => by simp only [Val.HandlerWF]; exact (by simpa only [ValEF] using h : ValEF w).handlerWF n
  | .pair w₁ w₂, h, n => by
      simp only [Val.HandlerWF]
      obtain ⟨h₁, h₂⟩ := (by simpa only [ValEF] using h : ValEF w₁ ∧ ValEF w₂)
      exact ⟨h₁.handlerWF n, h₂.handlerWF n⟩
  | .fold w, h, n => by simp only [Val.HandlerWF]; exact (by simpa only [ValEF] using h : ValEF w).handlerWF n
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

/-! ### `WFClos` — the effect-fragment closure invariant (`PureV` minus `EffectFree`, envm3)

`MVal.PureV`'s closure clause bundles FOUR facts: `EffectFree M ∧ ScopedC … ∧ MEnv.WF ρ ∧ MEnv.PureV ρ`.
In the PURE fragment all four hold and `_pure` threads `PureV`. In the EFFECT fragment a returner may be
`ret (vthunk N)` with an EFFECTFUL `N` (machine-checked: `effect_pureV_refutation_witness`), so the
`EffectFree` clause is FALSE — but the `force`/`app` closure-entry cases still need the env-WF + body-scope
the bundle carried (and `MVal.WF = ClosedE (readback)` cannot decompose them). So `WFClos` is exactly
`PureV` MINUS the `EffectFree` clause: the closure discipline that survives effects.

RELATION (ruling #2 rider, kept as a comment since factoring PureV THROUGH WFClos would churn the proven
3a cases' positional `simp only [MVal.PureV]` extractions): `MVal.PureV mv → MVal.WFClos mv` pointwise —
`PureV`'s closure clause is `EffectFree ∧ WFClos`'s clause. The two predicates run in parallel; `PureV` is
the strictly stronger (pure-fragment) one, `WFClos` the effect-fragment one. -/
mutual
def MVal.WFClos : MVal → Prop
  | .mvunit       => True
  | .mvint _      => True
  | .mvcap _ _    => True
  -- the closure discipline WITHOUT EffectFree: env reads back closed (so the crux fires), env's own
  -- closures are WFClos, body scoped under the env — everything `force`/`app` need, effects allowed.
  -- HandlerWF rides the closure clause AS ScopedC's sibling (manager ruling 2026-07-10): `Handler.shiftFrom`
  -- is identity on txn/custom payloads, so ScopedC can never witness them — the closed-focus design pushes
  -- that obligation onto the closure invariant, exactly where `force`/`app` re-enter a captured body.
  | .mvclos M ρ   =>
      Comp.ScopedC (readbackEnv ρ).length M ∧ Comp.HandlerWF (readbackEnv ρ).length M
        ∧ MEnv.WF ρ ∧ MEnv.WFClos ρ
  | .minl w       => MVal.WFClos w
  | .minr w       => MVal.WFClos w
  | .mpair w₁ w₂  => MVal.WFClos w₁ ∧ MVal.WFClos w₂
  | .mfold w      => MVal.WFClos w
def MEnv.WFClos : MEnv → Prop
  | .nil       => True
  | .cons v ρ  => MVal.WFClos v ∧ MEnv.WFClos ρ
end

theorem MEnv.WFClos.head {mv : MVal} {ρ : MEnv} (h : MEnv.WFClos (mv ∷ₑ ρ)) : MVal.WFClos mv := by
  unfold MEnv.WFClos at h; exact h.1
theorem MEnv.WFClos.tail {mv : MVal} {ρ : MEnv} (h : MEnv.WFClos (mv ∷ₑ ρ)) : MEnv.WFClos ρ := by
  unfold MEnv.WFClos at h; exact h.2
theorem MEnv.WFClos.cons {mv : MVal} {ρ : MEnv} (hmv : MVal.WFClos mv) (hρ : MEnv.WFClos ρ) :
    MEnv.WFClos (mv ∷ₑ ρ) := by unfold MEnv.WFClos; exact ⟨hmv, hρ⟩

/-- A `WFClos` env's lookup is `WFClos` (out-of-range gives `mvunit`, also `WFClos`). -/
theorem MEnv.WFClos.get : ∀ {ρ : MEnv}, MEnv.WFClos ρ → ∀ (i : Nat), MVal.WFClos (ρ.get i)
  | .nil, _, _ => by simp only [MEnv.get, MVal.WFClos]
  | .cons v ρ, h, 0 => by simp only [MEnv.get]; exact h.head
  | .cons v ρ, h, j + 1 => by simp only [MEnv.get]; exact MEnv.WFClos.get h.tail j

/-! `PureV → WFClos` pointwise (the rider's relation, as a lemma so it's usable, not just prose):
`PureV`'s stronger closure clause implies `WFClos`'s. Mutual over `MVal`/`MEnv`. -/
mutual
theorem MVal.PureV.wfclos : ∀ {mv : MVal}, MVal.PureV mv → MVal.WFClos mv
  | .mvunit, _ => by simp only [MVal.WFClos]
  | .mvint _, _ => by simp only [MVal.WFClos]
  | .mvcap _ _, _ => by simp only [MVal.WFClos]
  | .mvclos M ρ, h => by
      obtain ⟨hEF, hsc, hWF, hP⟩ := (by simpa only [MVal.PureV] using h :
        EffectFree M ∧ Comp.ScopedC (readbackEnv ρ).length M ∧ MEnv.WF ρ ∧ MEnv.PureV ρ)
      exact ⟨hsc, hEF.handlerWF _, hWF, hP.wfclos⟩
  | .minl w, h => by simp only [MVal.WFClos]; exact (by simpa only [MVal.PureV] using h : MVal.PureV w).wfclos
  | .minr w, h => by simp only [MVal.WFClos]; exact (by simpa only [MVal.PureV] using h : MVal.PureV w).wfclos
  | .mpair w₁ w₂, h => by
      obtain ⟨h₁, h₂⟩ := (by simpa only [MVal.PureV] using h : MVal.PureV w₁ ∧ MVal.PureV w₂)
      exact ⟨h₁.wfclos, h₂.wfclos⟩
  | .mfold w, h => by simp only [MVal.WFClos]; exact (by simpa only [MVal.PureV] using h : MVal.PureV w).wfclos
theorem MEnv.PureV.wfclos : ∀ {ρ : MEnv}, MEnv.PureV ρ → MEnv.WFClos ρ
  | .nil, _ => by simp only [MEnv.WFClos]
  | .cons v ρ, h => by
      obtain ⟨hv, hρ⟩ := (by simpa only [MEnv.PureV] using h : MVal.PureV v ∧ MEnv.PureV ρ)
      exact ⟨hv.wfclos, hρ.wfclos⟩
end

/-- Purity of a machine TERMINAL, the `WFClos` form (effect fragment). Returner: its value `WFClos`.
Function `mlam N ρ`: body scoped under one binder + captured env WF ∧ WFClos — NO `EffectFree`. -/
def MTerm.WFClos : MTerm → Prop
  | .mret mv  => MVal.WFClos mv
  | .mlam N ρ =>
      -- HandlerWF rides the mlam closure clause AS ScopedC's sibling (manager ruling 2026-07-10) —
      -- the returned lambda is `app`-entered, running N; its handler payloads must be constrained
      -- through the terminal, exactly as the mvclos closure clause carries HandlerWF for `force`.
      Comp.ScopedC ((readbackEnv ρ).length + 1) N ∧ Comp.HandlerWF ((readbackEnv ρ).length + 1) N
        ∧ MEnv.WF ρ ∧ MEnv.WFClos ρ

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

/-- `evalV` of ANY value (no `ValEF` needed) under a `WF ∧ WFClos` env is `WFClos` (the effect-fragment
analog of `evalV_PureV`). The `vthunk M ↦ mvclos M ρ` case drops the `EffectFree M` obligation `PureV`
required — a closure over an EFFECTFUL body is `WFClos` (its env-shape + body-scope are all that's
constrained). Structural on `v`, needs only the source scoped so the closure's body-scope obligation holds. -/
theorem evalV_WFClos {ρ : MEnv} (hWFρ : MEnv.WF ρ) (hρ : MEnv.WFClos ρ) :
    ∀ {v : Val}, Val.ScopedV (readbackEnv ρ).length v →
      Val.HandlerWF (readbackEnv ρ).length v → MVal.WFClos (evalV ρ v)
  | .vunit, _, _ => by simp only [evalV, MVal.WFClos]
  | .vint _, _, _ => by simp only [evalV, MVal.WFClos]
  | .vcap _ _, _, _ => by simp only [evalV, MVal.WFClos]
  | .vvar i, _, _ => by simp only [evalV]; exact MEnv.WFClos.get hρ i
  | .vthunk M, hsc, hHW => by
      simp only [evalV, MVal.WFClos]
      refine ⟨?_, (by simpa only [Val.HandlerWF] using hHW), hWFρ, hρ⟩
      intro k hk; have := hsc k hk
      simp only [Val.shiftFrom, Val.vthunk.injEq] at this; exact this
  | .inl w, hsc, hHW => by
      simp only [evalV, MVal.WFClos]
      exact evalV_WFClos hWFρ hρ hsc.inl_inv (by simpa only [Val.HandlerWF] using hHW)
  | .inr w, hsc, hHW => by
      simp only [evalV, MVal.WFClos]
      exact evalV_WFClos hWFρ hρ hsc.inr_inv (by simpa only [Val.HandlerWF] using hHW)
  | .pair w₁ w₂, hsc, hHW => by
      simp only [evalV, MVal.WFClos]
      obtain ⟨hHW₁, hHW₂⟩ := (by simpa only [Val.HandlerWF] using hHW :
        Val.HandlerWF (readbackEnv ρ).length w₁ ∧ Val.HandlerWF (readbackEnv ρ).length w₂)
      exact ⟨evalV_WFClos hWFρ hρ hsc.pair_inv.1 hHW₁, evalV_WFClos hWFρ hρ hsc.pair_inv.2 hHW₂⟩
  | .fold w, hsc, hHW => by
      simp only [evalV, MVal.WFClos]
      exact evalV_WFClos hWFρ hρ hsc.fold_inv (by simpa only [Val.HandlerWF] using hHW)

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

/-! ## Slice 3b — the effect-store correspondence (PROVEN; ruling #6/#1)

The pure fragment (`evalE_agrees_evalD_pure`, above) covers `EffectFree` M over empty stores. 3b closes
the full headline `evalE_agrees_evalD` (below) by relaxing `EffectFree` and threading a correspondence
between `evalE`'s MVal-keyed stores (σ/τ/κ) and `evalD`'s Val-keyed stores. This block STATES that
correspondence + the `Good`-extension over store-held values; the `_gen`/`_effect` engine and the
custom-handle install arm are PROVEN (axiom-clean), so the effect theorem and headline are sorry-free.

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
  (∀ p ∈ eσ, MVal.WF p.2 ∧ MVal.WFClos p.2)
  ∧ (∀ p ∈ eτ, ∀ mv ∈ p.2, MVal.WF mv ∧ MVal.WFClos mv)
  ∧ (∀ p ∈ eκ, (MVal.WF p.2.1 ∧ MVal.WFClos p.2.1) ∧ MEnv.WF p.2.2.2 ∧ MEnv.WFClos p.2.2.2
       ∧ (∀ c ∈ p.2.2.1, Comp.ScopedC ((readbackEnv p.2.2.2).length + 2) c.2
            ∧ Comp.HandlerWF ((readbackEnv p.2.2.2).length + 2) c.2))

/-- A state cell fetched from a `StoresGood` σ is `WF ∧ WFClos`. -/
theorem StoresGood.get_state {eσ : ESStore} {eτ : ETHeap} {eκ : ECStore} {n : Nat} {s : MVal}
    (hG : StoresGood eσ eτ eκ) (hget : eσ.get? n = some s) : MVal.WF s ∧ MVal.WFClos s := by
  simp only [ESStore.get?, Option.map_eq_some_iff] at hget
  obtain ⟨p, hfind, hs⟩ := hget
  have hmem := List.mem_of_find?_eq_some hfind
  have := hG.1 p hmem; rw [hs] at this; exact this

/-- A custom frame fetched from a `StoresGood` κ carries its `(param, clauses, install-env)` goodness. -/
theorem StoresGood.get_custom {eσ : ESStore} {eτ : ETHeap} {eκ : ECStore} {n : Nat}
    {p : MVal} {cls : List (Bang.OpId × Comp)} {ρ_inst : MEnv}
    (hG : StoresGood eσ eτ eκ) (hget : eκ.get? n = some (p, cls, ρ_inst)) :
    (MVal.WF p ∧ MVal.WFClos p) ∧ MEnv.WF ρ_inst ∧ MEnv.WFClos ρ_inst
      ∧ (∀ c ∈ cls, Comp.ScopedC ((readbackEnv ρ_inst).length + 2) c.2
           ∧ Comp.HandlerWF ((readbackEnv ρ_inst).length + 2) c.2) := by
  simp only [ECStore.get?, Option.map_eq_some_iff] at hget
  obtain ⟨q, hfind, hq⟩ := hget
  have hmem := List.mem_of_find?_eq_some hfind
  have := hG.2.2 q hmem; rw [hq] at this; exact this

/-- The σ-clause of `StoresGood` is preserved under `put` of a good value (list lemma). -/
private theorem sstore_put_good {n : Nat} {arg : MVal} (harg : MVal.WF arg ∧ MVal.WFClos arg) :
    ∀ {eσ : ESStore}, (∀ p ∈ eσ, MVal.WF p.2 ∧ MVal.WFClos p.2) →
      ∀ q ∈ eσ.put n arg, MVal.WF q.2 ∧ MVal.WFClos q.2
  | [], _, q, hq => by simp only [ESStore.put, List.not_mem_nil] at hq
  | (k, w) :: eσ, hσ, q, hq => by
      simp only [ESStore.put] at hq
      by_cases hk : k = n
      · simp only [hk, if_true, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact harg
        · exact hσ q (List.mem_cons_of_mem _ hq)
      · simp only [hk, if_false, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hσ (k, w) List.mem_cons_self
        · exact sstore_put_good harg (fun p hp => hσ p (List.mem_cons_of_mem _ hp)) q hq

theorem StoresGood.put_state {eσ : ESStore} {eτ : ETHeap} {eκ : ECStore} {n : Nat} {arg : MVal}
    (hG : StoresGood eσ eτ eκ) (harg : MVal.WF arg ∧ MVal.WFClos arg) :
    StoresGood (eσ.put n arg) eτ eκ :=
  ⟨sstore_put_good harg hG.1, hG.2.1, hG.2.2⟩

/-- The stm service output heap is `WF ∧ WFClos` cell-wise when the input heap and arg are (txn `put`). -/
theorem mtxnService_good {op : Bang.OpId} {arg : MVal} {Θ : List MVal}
    (harg : MVal.WF arg ∧ MVal.WFClos arg)
    (hΘ : ∀ mv ∈ Θ, MVal.WF mv ∧ MVal.WFClos mv) :
    ∀ mv ∈ (mtxnService op arg Θ).2, MVal.WF mv ∧ MVal.WFClos mv := by
  simp only [mtxnService]
  by_cases hnew : op = "newTVar"
  · simp only [hnew, if_true]
    intro mv hmv; rw [List.mem_append] at hmv
    rcases hmv with hmv | hmv
    · exact hΘ mv hmv
    · simp only [List.mem_singleton] at hmv; rw [hmv]; exact harg
  · simp only [hnew, if_false]
    by_cases hread : op = "readTVar"
    · simp only [hread, if_true]; exact hΘ
    · simp only [hread, if_false]
      cases arg with
      | mpair iv w =>
          intro mv hmv
          have hw : MVal.WF w ∧ MVal.WFClos w := by
            obtain ⟨hWFp, hWCp⟩ := harg
            simp only [MVal.WF, readback] at hWFp; simp only [MVal.WFClos] at hWCp
            exact ⟨(by simp only [MVal.WF]; exact (Val.ScopedV.pair_inv (fun k _ => hWFp k)).2.closedE_zero),
                   hWCp.2⟩
          -- Θ.set i w's members are Θ's members or w; both good.
          rcases List.mem_or_eq_of_mem_set hmv with hmv | rfl
          · exact hΘ mv hmv
          · exact hw
      | _ => intro mv hmv; exact hΘ mv hmv

/-- `getD` of a good list at a good default is good (member-or-default). -/
private theorem mval_getD_good {d : MVal} (hd : MVal.WF d ∧ MVal.WFClos d) :
    ∀ {Θ : List MVal} (i : Nat), (∀ mv ∈ Θ, MVal.WF mv ∧ MVal.WFClos mv) →
      MVal.WF (Θ.getD i d) ∧ MVal.WFClos (Θ.getD i d)
  | [], _, _ => by simp only [List.getD, List.getElem?_nil, Option.getD_none]; exact hd
  | a :: Θ, 0, hΘ => by simp only [List.getD_cons_zero]; exact hΘ a List.mem_cons_self
  | a :: Θ, i + 1, hΘ => by
      simp only [List.getD_cons_succ]
      exact mval_getD_good hd i (fun mv hmv => hΘ mv (List.mem_cons_of_mem _ hmv))

/-- The stm service RESULT value is `WF ∧ WFClos`: `newTVar` returns an index (`mvint`), `readTVar`
a heap cell or the default (both good), `writeTVar` unit. -/
theorem mtxnService_result_good {op : Bang.OpId} {arg : MVal} {Θ : List MVal}
    (hΘ : ∀ mv ∈ Θ, MVal.WF mv ∧ MVal.WFClos mv) :
    MVal.WF (mtxnService op arg Θ).1 ∧ MVal.WFClos (mtxnService op arg Θ).1 := by
  have hint : ∀ z : Int, MVal.WF (MVal.mvint z) ∧ MVal.WFClos (MVal.mvint z) :=
    fun z => ⟨by simp only [MVal.WF, readback]; intro k; rfl, by simp only [MVal.WFClos]⟩
  have hunit : MVal.WF MVal.mvunit ∧ MVal.WFClos MVal.mvunit :=
    ⟨by simp only [MVal.WF, readback]; intro k; rfl, by simp only [MVal.WFClos]⟩
  simp only [mtxnService]
  by_cases hnew : op = "newTVar"
  · simp only [hnew, if_true]; exact hint _
  · simp only [hnew, if_false]
    by_cases hread : op = "readTVar"
    · simp only [hread, if_true]; exact mval_getD_good (hint 0) _ hΘ
    · simp only [hread, if_false]
      cases arg with
      | mpair iv w => exact hunit
      | _ => exact hunit

/-- The τ-clause of `StoresGood` is preserved under `put` of a good heap (list lemma). -/
private theorem theap_put_good {n : Nat} {Θ' : List MVal}
    (hΘ' : ∀ mv ∈ Θ', MVal.WF mv ∧ MVal.WFClos mv) :
    ∀ {eτ : ETHeap}, (∀ p ∈ eτ, ∀ mv ∈ p.2, MVal.WF mv ∧ MVal.WFClos mv) →
      ∀ q ∈ eτ.put n Θ', ∀ mv ∈ q.2, MVal.WF mv ∧ MVal.WFClos mv
  | [], _, q, hq => by simp only [ETHeap.put, List.not_mem_nil] at hq
  | (k, w) :: eτ, hτ, q, hq => by
      intro mv hmv
      simp only [ETHeap.put] at hq
      by_cases hk : k = n
      · simp only [hk, if_true, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hΘ' mv hmv
        · exact hτ q (List.mem_cons_of_mem _ hq) mv hmv
      · simp only [hk, if_false, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hτ (k, w) List.mem_cons_self mv hmv
        · exact theap_put_good hΘ' (fun p hp => hτ p (List.mem_cons_of_mem _ hp)) q hq mv hmv

theorem StoresGood.put_txn {eσ : ESStore} {eτ : ETHeap} {eκ : ECStore} {n : Nat} {Θ' : List MVal}
    (hG : StoresGood eσ eτ eκ) (hΘ' : ∀ mv ∈ Θ', MVal.WF mv ∧ MVal.WFClos mv) :
    StoresGood eσ (eτ.put n Θ') eκ :=
  ⟨hG.1, theap_put_good hΘ' hG.2.1, hG.2.2⟩

/-- **WEDGE WITNESS (envm3, 2026-07-10) — `StoresGood`'s `PureV`/`EffectFree` clauses are over-strong
for the effect fragment (a THIRD `PureV`-refutation, same root as `effect_pureV_refutation_witness`).**
`StoresGood` demands every stored value be `MVal.PureV` (and every custom clause `EffectFree`). But the
effect fragment LEGITIMATELY stores effectful-bodied closures: `perform cap "put" (thunk N)` with an
effectful `N` puts `mvclos N ρ` into the state cell, and custom handler clauses are typically effectful
(they `perform`/resume). This witness pins that a WF-but-NOT-PureV value exists, so `StoresGood` cannot
be preserved forward under such a `put`/mint — the `_gen` perform/handle cases can't discharge the
`StoresGood eσ' eτ' eκ'` conclusion as stated.

FIX (same as ruling #2): `StoresGood` should thread `WFClos` not `PureV`, and DROP the custom clauses'
`EffectFree c.2` (a clause body may perform). Then it is preservable + true in the effect fragment. -/
theorem storesGood_pureV_wedge :
    MVal.WF (.mvclos (.handle (.throws 0) (.ret .vunit)) .nil)
    ∧ ¬ MVal.PureV (.mvclos (.handle (.throws 0) (.ret .vunit)) .nil) := by
  refine ⟨?_, ?_⟩
  · -- WF: the closure reads back to a CLOSED vthunk (empty env, closed body).
    simp only [MVal.WF, readback, readbackEnv, substEnv]
    intro k; simp only [Val.shiftFrom, Comp.shiftFrom, Val.shiftFrom, Bang.Handler.shiftFrom]
  · -- ¬PureV: the closure's body `handle …` is NOT EffectFree (EffectFree (handle _ _) = False).
    simp only [MVal.PureV, EffectFree, not_false_eq_true, false_and, not_false_iff]

/-! ### W1 — store-op ↔ readback-map commutations (the 3b store backbone, envm3)

Each per-kind store op (`get?`/`put`/`push`/`.tail`) commutes with the `readback`-map that IS the
correspondence (`SStoreCorr`/`THeapCorr`/`CStoreCorr`). These are the mechanical readback-commutation
lemmas the resume map names as W1 — the same shape 3a's distribution lemmas already exemplify. The
`find?` structure is shared (`evalD`'s and `evalE`'s stores are `List (Nat × _)` keyed identically), so
the map slides through `find?`/`getD` by the standard `List.find?_map`/`List.map` rewrites. -/

/-- `SStore.get?` commutes with the readback-map: reading key `n` from `evalE`'s σ then reading back
equals reading key `n` from the readback-image store. (both directions of the `get?` agreement.) -/
theorem SStore.get?_readback (eσ : ESStore) (n : Nat) :
    Bang.CalcVM.SStore.get? (eσ.map (fun p => (p.1, readback p.2))) n
      = (eσ.get? n).map readback := by
  induction eσ with
  | nil => rfl
  | cons a eσ ih =>
    simp only [List.map_cons, Bang.CalcVM.SStore.get?, ESStore.get?, List.find?]
    by_cases h : a.1 = n
    · simp only [h, decide_true, Option.map_some]
    · simp only [h, decide_false]
      simpa only [Bang.CalcVM.SStore.get?, ESStore.get?] using ih

/-- `SStore.put` commutes with the readback-map: putting `readback arg` on the image equals imaging the
`put arg`. -/
theorem SStore.put_readback (eσ : ESStore) (n : Nat) (arg : MVal) :
    Bang.CalcVM.SStore.put (eσ.map (fun p => (p.1, readback p.2))) n (readback arg)
      = (eσ.put n arg).map (fun p => (p.1, readback p.2)) := by
  induction eσ with
  | nil => rfl
  | cons a eσ ih =>
    obtain ⟨k, w⟩ := a
    simp only [List.map_cons, Bang.CalcVM.SStore.put, ESStore.put]
    by_cases h : k = n
    · simp only [h, if_true, List.map_cons]
    · simp only [h, if_false, List.map_cons, ih]

/-- `THeap.get?` commutes with the readback-map (`readback`-lifted per cell). -/
theorem THeap.get?_readback (eτ : ETHeap) (n : Nat) :
    Bang.CalcVM.THeap.get? (eτ.map (fun p => (p.1, p.2.map readback))) n
      = (eτ.get? n).map (List.map readback) := by
  induction eτ with
  | nil => rfl
  | cons a eτ ih =>
    simp only [List.map_cons, Bang.CalcVM.THeap.get?, ETHeap.get?, List.find?]
    by_cases h : a.1 = n
    · simp only [h, decide_true, Option.map_some]
    · simp only [h, decide_false]
      simpa only [Bang.CalcVM.THeap.get?, ETHeap.get?] using ih

/-- `THeap.put` commutes with the readback-map. -/
theorem THeap.put_readback (eτ : ETHeap) (n : Nat) (Θ : List MVal) :
    Bang.CalcVM.THeap.put (eτ.map (fun p => (p.1, p.2.map readback))) n (Θ.map readback)
      = (eτ.put n Θ).map (fun p => (p.1, p.2.map readback)) := by
  induction eτ with
  | nil => rfl
  | cons a eτ ih =>
    obtain ⟨k, w⟩ := a
    simp only [List.map_cons, Bang.CalcVM.THeap.put, ETHeap.put]
    by_cases h : k = n
    · simp only [h, if_true, List.map_cons]
    · simp only [h, if_false, List.map_cons, ih]

/-- `CStore.get?` commutes with the readback-map (each frame's `(param, clauses, install-env)` reads back
to `(readback param, closed-clauses)` — the `CStoreCorr` image). -/
theorem CStore.get?_readback (eκ : ECStore) (n : Nat) :
    Bang.CalcVM.CStore.get? (eκ.map (fun p => (p.1, (readback p.2.1,
        p.2.2.1.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv p.2.2.2) c.2)))))) n
      = (eκ.get? n).map (fun t => (readback t.1,
          t.2.1.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv t.2.2) c.2)))) := by
  induction eκ with
  | nil => rfl
  | cons a eκ ih =>
    simp only [List.map_cons, Bang.CalcVM.CStore.get?, ECStore.get?, List.find?]
    by_cases h : a.1 = n
    · simp only [h, decide_true, Option.map_some]
    · simp only [h, decide_false]
      simpa only [Bang.CalcVM.CStore.get?, ECStore.get?] using ih

/-! ### W2 — the stm service agrees under readback (`mtxnService` ⟺ `txnService`, envm3) -/

/-- The TVar-index projector agrees under readback: `mtvarIdx` on an `MVal` equals `tvarIdx` on its
readback. Both project only the `mvint`/`vint` case identically. -/
theorem mtvarIdx_readback (v : MVal) : Bang.tvarIdx (readback v) = mtvarIdx v := by
  cases v <;> rfl

/-- `getD` commutes with a map when the default is the map of the machine default (local; avoids a
Mathlib import path that doesn't reach this module). -/
theorem getD_map_readback (Θ : List MVal) (n : Nat) :
    (Θ.map readback).getD n (readback (MVal.mvint 0)) = readback (Θ.getD n (MVal.mvint 0)) := by
  induction Θ generalizing n with
  | nil => cases n <;> rfl
  | cons a Θ ih => cases n with
    | zero => rfl
    | succ n => simpa only [List.map_cons, List.getD_cons_succ] using ih n

/-- **W2**: the machine stm service `mtxnService` agrees with the reference `txnService` under readback —
result value reads back, and the output heap reads back cell-wise. Case on the three stm ops; `newTVar`
uses `Θ.length` (preserved by `.map`), `readTVar` uses `getD` (readback commutes with `getD` at the
`mtvarIdx`-projected index), `writeTVar` uses `List.set` (readback commutes with `set`). -/
theorem mtxnService_readback (op : Bang.OpId) (arg : MVal) (Θ : List MVal) :
    Bang.CalcVM.txnService op (readback arg) (Θ.map readback)
      = (readback (mtxnService op arg Θ).1, (mtxnService op arg Θ).2.map readback) := by
  simp only [Bang.CalcVM.txnService, mtxnService]
  by_cases hnew : op = "newTVar"
  · simp only [hnew, if_true, List.length_map, List.map_append, List.map_cons, List.map_nil, readback]
  · simp only [hnew, if_false]
    by_cases hread : op = "readTVar"
    · simp only [hread, if_true, mtvarIdx_readback]
      rw [show (Val.vint 0) = readback (MVal.mvint 0) from rfl, getD_map_readback]
    · simp only [hread, if_false]
      cases arg with
      | mpair iv w =>
          simp only [readback, mtvarIdx_readback, Bang.storeSet, readback, List.map_set]
      | _ => simp only [readback]

/-! ### SLICE 3b — the effect-store correspondence (the weave, envm3)

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

The weave lives in `evalE_agrees_evalD_gen` below (the outcome-general engine); the frozen
`evalE_agrees_evalD_effect` is its `mterm`-half corollary. -/

/-- **The OUTCOME-GENERAL 3b engine (envm3).** The inductive core `evalE_agrees_evalD_effect` is the
`mterm`-half of: for ANY `MOutcome` (terminal OR `mraised`), an `evalE` success maps to an `evalD`
success at the read-back outcome, threading the store correspondence + `Good` extension forward.

Generalizing over the outcome is REQUIRED for the induction: `letC`/`app`/`perform`/`handle` recurse into
sub-evals that may RAISE, so the IH must cover the raise outcome (the `sim` exemplar in
`AbstractMachine.lean` conjoins a term-half and a raise-half for exactly this reason).

KEY SIMPLIFICATION (why NO `StoresDisjoint` premise is needed — the resume map's W4 dissolves): both
machines key stores by the SAME identity and `StoresCorr` gives PER-STORE `get?` agreement (W1's
`get?_readback` family), so the σ→τ→κ dispatch cascade takes the IDENTICAL branch on both sides
without a cross-kind disjointness argument. `run_evalD`'s `sim` needed disjointness only because it
related a store to a DIFFERENT structure (an HStack); here both sides are id-keyed lists.

The output WF is stated per-outcome: a `mterm t` yields `MTerm.WF t ∧ MTerm.PureV t`; a `mraised n op mv`
yields `MVal.WF mv ∧ MVal.PureV mv` (the raise payload). -/
theorem evalE_agrees_evalD_gen :
    ∀ (f : Nat) (γ : List Val) (M : Comp) (out : MOutcome) (ρ : MEnv) (g g' : Nat)
      (eσ eσ' : ESStore) (eτ eτ' : ETHeap) (eκ eκ' : ECStore)
      (dσ : Bang.CalcVM.SStore) (dτ : Bang.CalcVM.THeap) (dκ : Bang.CalcVM.CStore),
      EnvAgrees ρ γ → MEnv.WF ρ → MEnv.WFClos ρ → Comp.ScopedC γ.length M →
      Comp.HandlerWF γ.length M →
      StoresGood eσ eτ eκ → StoresCorr eσ eτ eκ dσ dτ dκ →
      evalE f g eσ eτ eκ ρ M = some (out, g', eσ', eτ', eκ') →
      ∃ (dσ' : Bang.CalcVM.SStore) (dτ' : Bang.CalcVM.THeap) (dκ' : Bang.CalcVM.CStore),
        Bang.CalcVM.evalD f g dσ dτ dκ (substEnv γ M)
            = some (readbackTermS out, g', dσ', dτ', dκ')
          ∧ StoresCorr eσ' eτ' eκ' dσ' dτ' dκ' ∧ StoresGood eσ' eτ' eκ'
          ∧ (∀ t, out = .mterm t → MTerm.WF t ∧ MTerm.WFClos t)
          ∧ (∀ n op mv, out = .mraised n op mv → MVal.WF mv ∧ MVal.WFClos mv) := by
  intro f
  induction f with
  | zero =>
    intro γ M out ρ g g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ _ _ _ _ _ _ _ h; simp [evalE] at h
  | succ f ih =>
    intro γ M out ρ g g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ hag hWF hP hSc hHWF hG hC h
    have hγ : ∀ v ∈ γ, Val.ClosedE v := hag ▸ hWF
    have hlen : (readbackEnv ρ).length = γ.length := by rw [show readbackEnv ρ = γ from hag]
    cases M with
    | ret v =>
      -- out = mret (evalV ρ v), stores unchanged; evalD (ret (substEnvV γ v)) = ret (readback ..).
      simp only [evalE, Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
      obtain ⟨hout, hgc, hσ, hτ, hκ⟩ := h
      have hsc : Val.ScopedV γ.length v := hlen ▸ (hSc.ret_inv)
      subst hout hgc hσ hτ hκ
      refine ⟨dσ, dτ, dκ, ?_, hC, hG, ?_, by rintro n op mv ⟨⟩⟩
      · simp only [substEnv_ret, readbackTermS, readbackTerm, Bang.CalcVM.evalD,
          readback_evalV hWF (hlen ▸ hsc), show readbackEnv ρ = γ from hag]
      · rintro t ⟨rfl⟩
        exact ⟨evalV_WF hWF (hlen ▸ hsc),
          evalV_WFClos hWF hP (hlen ▸ hsc) (hlen ▸ hHWF.ret_inv)⟩
    | lam M =>
      -- out = mlam M ρ, stores unchanged; evalD (lam (closeUnderBindersE 1 γ M)).
      simp only [evalE, Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
      obtain ⟨hout, hgc, hσ, hτ, hκ⟩ := h
      have hScM : Comp.ScopedC (γ.length + 1) M := hSc.lam_inv
      have hHWM : Comp.HandlerWF (γ.length + 1) M := hHWF.lam_inv
      subst hout hgc hσ hτ hκ
      refine ⟨dσ, dτ, dκ, ?_, hC, hG, ?_, by rintro n op mv ⟨⟩⟩
      · simp only [substEnv_lam, readbackTermS, readbackTerm, Bang.CalcVM.evalD,
          show readbackEnv ρ = γ from hag]
      · rintro t ⟨rfl⟩
        exact ⟨⟨hWF, hlen ▸ hScM⟩, hlen ▸ hScM, hlen ▸ hHWM, hWF, hP⟩
    | force w =>
      -- evalV ρ w = mvclos M' ρ' ⇒ run M' under ρ'. evalD: force (vthunk (substEnv (rbEnv ρ') M')).
      have hsc : Val.ScopedV γ.length w := hlen ▸ hSc.force_inv
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mvclos M' ρ' =>
        rw [hw] at h
        -- WFClos of the closure gives its body-scope + env-WF + env-WFClos (no EffectFree needed).
        have hwfc : MVal.WFClos (MVal.mvclos M' ρ') := by
          have := evalV_WFClos hWF hP (hlen ▸ hsc) (hlen ▸ hHWF.force_inv); rw [hw] at this; exact this
        obtain ⟨hscM', hHWM', hWFρ', hWFCρ'⟩ := (by simpa only [MVal.WFClos] using hwfc :
          Comp.ScopedC (readbackEnv ρ').length M' ∧ Comp.HandlerWF (readbackEnv ρ').length M'
            ∧ MEnv.WF ρ' ∧ MEnv.WFClos ρ')
        obtain ⟨dσ', dτ', dκ', hd, hC', hG', hWt, hRt⟩ :=
          ih (readbackEnv ρ') M' out ρ' g g' eσ eσ' eτ eτ' eκ eκ'
            dσ dτ dκ rfl hWFρ' hWFCρ' hscM' hHWM' hG hC h
        refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt, hRt⟩
        have hrb : substEnvV γ w = Val.vthunk (substEnv (readbackEnv ρ') M') := by
          rw [show γ = readbackEnv ρ from hag.symm, ← readback_evalV hWF (hlen ▸ hsc), hw]; rfl
        rw [substEnv_force, hrb]
        simpa only [Bang.CalcVM.evalD] using hd
      | _ => rw [hw] at h; simp at h
    | letC M N =>
      obtain ⟨hScM, hScN⟩ := hSc.letC_inv
      obtain ⟨hHWM, hHWN⟩ := hHWF.letC_inv
      simp only [evalE, Option.bind_eq_bind] at h
      cases hM : evalE f g eσ eτ eκ ρ M with
      | none => rw [hM] at h; simp at h
      | some p =>
        rw [hM] at h
        obtain ⟨outM, g₁, σ₁, τ₁, κ₁⟩ := p
        cases outM with
        | mterm tM => cases tM with
          | mret mw =>
            simp only [Option.bind_some] at h
            -- IH on M (terminal mret mw): evalD M ⇒ ret (readback mw), stores → σ₁ τ₁ κ₁ (corr dσ₁…), mw WFClos.
            obtain ⟨dσ₁, dτ₁, dκ₁, hdM, hCM, hGM, hWtM, -⟩ :=
              ih γ M (.mterm (.mret mw)) ρ g g₁ eσ σ₁ eτ τ₁ eκ κ₁ dσ dτ dκ
                hag hWF hP (hlen ▸ hScM) (hlen ▸ hHWM) hG hC hM
            obtain ⟨hWFmw, hWCmw⟩ := hWtM _ rfl
            simp only [MTerm.WF] at hWFmw; simp only [MTerm.WFClos] at hWCmw
            -- N runs under (mw ∷ₑ ρ) at M's output stores; IH on N gives the tail.
            have hagN : EnvAgrees (mw ∷ₑ ρ) (readback mw :: γ) := by
              simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hag]
            have hWFN : MEnv.WF (mw ∷ₑ ρ) := MEnv.WF.cons hWFmw hWF
            have hWCN : MEnv.WFClos (mw ∷ₑ ρ) := MEnv.WFClos.cons hWCmw hP
            have hScN' : Comp.ScopedC (readback mw :: γ).length N := by
              simpa only [List.length_cons] using hScN
            have hHWN' : Comp.HandlerWF (readback mw :: γ).length N := by
              simpa only [List.length_cons] using (hlen ▸ hHWN : Comp.HandlerWF (γ.length + 1) N)
            obtain ⟨dσ', dτ', dκ', hdN, hC', hG', hWt', hRt'⟩ :=
              ih (readback mw :: γ) N out (mw ∷ₑ ρ) g₁ g' σ₁ eσ' τ₁ eτ' κ₁ eκ'
                dσ₁ dτ₁ dκ₁ hagN hWFN hWCN hScN' hHWN' hGM hCM h
            refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt', hRt'⟩
            have hcrux : substEnv (readback mw :: γ) N = (closeUnderBindersE 1 γ N).subst (readback mw) :=
              (substEnv_cons_subst hγ hWFmw N).symm
            simp only [substEnv_letC, Bang.CalcVM.evalD, Option.bind_eq_bind]
            rw [show Bang.CalcVM.evalD f g dσ dτ dκ (substEnv γ M) = _ from hdM]
            simp only [readbackTermS, readbackTerm, Option.bind_some]
            rw [← hcrux]; exact hdN
          | mlam _ _ => simp only [Option.bind_some] at h; exact absurd h (by simp)
        | mraised n op w =>
          -- M RAISES ⇒ letC short-circuits: out = mraised n op w. IH on M (raise-half) gives evalD raised.
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hout, hg, hσ, hτ, hκ⟩ := h
          obtain ⟨dσ₁, dτ₁, dκ₁, hdM, hCM, hGM, -, hRM⟩ :=
            ih γ M (.mraised n op w) ρ g g₁ eσ σ₁ eτ τ₁ eκ κ₁ dσ dτ dκ
              hag hWF hP (hlen ▸ hScM) (hlen ▸ hHWM) hG hC hM
          obtain ⟨hWFw, hWCw⟩ := hRM n op w rfl
          subst hout hg hσ hτ hκ
          refine ⟨dσ₁, dτ₁, dκ₁, ?_, hCM, hGM, by rintro t ⟨⟩, ?_⟩
          · simp only [substEnv_letC, Bang.CalcVM.evalD, Option.bind_eq_bind]
            rw [show Bang.CalcVM.evalD f g dσ dτ dκ (substEnv γ M) = _ from hdM]
            simp only [readbackTermS, Option.bind_some]
          · rintro n' op' mv' ⟨rfl, rfl, rfl⟩; exact ⟨hWFw, hWCw⟩
    | app M v =>
      obtain ⟨hScM, hScv⟩ := hSc.app_inv
      obtain ⟨hHWM, hHWv⟩ := hHWF.app_inv
      have hscv : Val.ScopedV γ.length v := hlen ▸ hScv
      have hWFav : MVal.WF (evalV ρ v) := evalV_WF hWF (hlen ▸ hscv)
      have hWCav : MVal.WFClos (evalV ρ v) := evalV_WFClos hWF hP (hlen ▸ hscv) (hlen ▸ hHWv)
      simp only [evalE, Option.bind_eq_bind] at h
      cases hM : evalE f g eσ eτ eκ ρ M with
      | none => rw [hM] at h; simp at h
      | some p =>
        rw [hM] at h
        obtain ⟨outM, g₁, σ₁, τ₁, κ₁⟩ := p
        cases outM with
        | mterm tM => cases tM with
          | mlam N' ρ' =>
            simp only [Option.bind_some] at h
            obtain ⟨dσ₁, dτ₁, dκ₁, hdM, hCM, hGM, hWtM, -⟩ :=
              ih γ M (.mterm (.mlam N' ρ')) ρ g g₁ eσ σ₁ eτ τ₁ eκ κ₁ dσ dτ dκ
                hag hWF hP (hlen ▸ hScM) (hlen ▸ hHWM) hG hC hM
            obtain ⟨hWFlam, hWClam⟩ := hWtM _ rfl
            obtain ⟨hWFρ', hscN'⟩ := (by simpa only [MTerm.WF] using hWFlam :
              MEnv.WF ρ' ∧ Comp.ScopedC ((readbackEnv ρ').length + 1) N')
            obtain ⟨-, hHWN', -, hWCρ'⟩ := (by simpa only [MTerm.WFClos] using hWClam :
              Comp.ScopedC ((readbackEnv ρ').length + 1) N' ∧ Comp.HandlerWF ((readbackEnv ρ').length + 1) N'
                ∧ MEnv.WF ρ' ∧ MEnv.WFClos ρ')
            have hagN : EnvAgrees (evalV ρ v ∷ₑ ρ') (readback (evalV ρ v) :: readbackEnv ρ') := by
              simp only [EnvAgrees, readbackEnv]
            have hWFN : MEnv.WF (evalV ρ v ∷ₑ ρ') := MEnv.WF.cons hWFav hWFρ'
            have hWCN : MEnv.WFClos (evalV ρ v ∷ₑ ρ') := MEnv.WFClos.cons hWCav hWCρ'
            have hScN'' : Comp.ScopedC (readback (evalV ρ v) :: readbackEnv ρ').length N' := by
              simpa only [List.length_cons] using hscN'
            have hHWN'' : Comp.HandlerWF (readback (evalV ρ v) :: readbackEnv ρ').length N' := by
              simpa only [List.length_cons] using hHWN'
            obtain ⟨dσ', dτ', dκ', hdN, hC', hG', hWt', hRt'⟩ :=
              ih (readback (evalV ρ v) :: readbackEnv ρ') N' out (evalV ρ v ∷ₑ ρ') g₁ g'
                σ₁ eσ' τ₁ eτ' κ₁ eκ' dσ₁ dτ₁ dκ₁ hagN hWFN hWCN hScN'' hHWN'' hGM hCM h
            refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt', hRt'⟩
            have hcrux : substEnv (readback (evalV ρ v) :: readbackEnv ρ') N'
                = (closeUnderBindersE 1 (readbackEnv ρ') N').subst (readback (evalV ρ v)) :=
              (substEnv_cons_subst (by simpa only [MEnv.WF] using hWFρ') hWFav N').symm
            have hrbv : substEnvV γ v = readback (evalV ρ v) := by
              rw [show γ = readbackEnv ρ from hag.symm, readback_evalV hWF (hlen ▸ hscv)]
            simp only [substEnv_app, hrbv, Bang.CalcVM.evalD, Option.bind_eq_bind]
            rw [show Bang.CalcVM.evalD f g dσ dτ dκ (substEnv γ M) = _ from hdM]
            simp only [readbackTermS, readbackTerm, Option.bind_some]
            rw [← hcrux]; exact hdN
          | mret _ => simp only [Option.bind_some] at h; exact absurd h (by simp)
        | mraised n op w =>
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hout, hg, hσ, hτ, hκ⟩ := h
          obtain ⟨dσ₁, dτ₁, dκ₁, hdM, hCM, hGM, -, hRM⟩ :=
            ih γ M (.mraised n op w) ρ g g₁ eσ σ₁ eτ τ₁ eκ κ₁ dσ dτ dκ
              hag hWF hP (hlen ▸ hScM) (hlen ▸ hHWM) hG hC hM
          obtain ⟨hWFw, hWCw⟩ := hRM n op w rfl
          have hrbv : substEnvV γ v = readback (evalV ρ v) := by
            rw [show γ = readbackEnv ρ from hag.symm, readback_evalV hWF (hlen ▸ hscv)]
          subst hout hg hσ hτ hκ
          refine ⟨dσ₁, dτ₁, dκ₁, ?_, hCM, hGM, by rintro t ⟨⟩, ?_⟩
          · simp only [substEnv_app, hrbv, Bang.CalcVM.evalD, Option.bind_eq_bind]
            rw [show Bang.CalcVM.evalD f g dσ dτ dκ (substEnv γ M) = _ from hdM]
            simp only [readbackTermS, Option.bind_some]
          · rintro n' op' mv' ⟨rfl, rfl, rfl⟩; exact ⟨hWFw, hWCw⟩
    | case w N₁ N₂ =>
      obtain ⟨hScw, hScN₁, hScN₂⟩ := hSc.case_inv
      obtain ⟨hHWw, hHWN₁, hHWN₂⟩ := hHWF.case_inv
      have hscw : Val.ScopedV γ.length w := hlen ▸ hScw
      have hWFsc : MVal.WF (evalV ρ w) := evalV_WF hWF (hlen ▸ hscw)
      have hWCsc : MVal.WFClos (evalV ρ w) := evalV_WFClos hWF hP (hlen ▸ hscw) (hlen ▸ hHWw)
      have hrbw : substEnvV γ w = readback (evalV ρ w) := by
        rw [show γ = readbackEnv ρ from hag.symm, readback_evalV hWF (hlen ▸ hscw)]
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | minl mv' =>
        rw [hw] at h
        have hWFmv' : MVal.WF mv' := by
          rw [hw] at hWFsc; simp only [MVal.WF, readback] at hWFsc
          exact (Val.ScopedV.inl_inv (fun k _ => hWFsc k)).closedE_zero
        have hWCmv' : MVal.WFClos mv' := by rw [hw] at hWCsc; simpa only [MVal.WFClos] using hWCsc
        have hagN : EnvAgrees (mv' ∷ₑ ρ) (readback mv' :: γ) := by
          simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hag]
        have hScN₁' : Comp.ScopedC (readback mv' :: γ).length N₁ := by
          simpa only [List.length_cons] using hScN₁
        have hHWN₁' : Comp.HandlerWF (readback mv' :: γ).length N₁ := by
          simpa only [List.length_cons] using (hlen ▸ hHWN₁ : Comp.HandlerWF (γ.length + 1) N₁)
        obtain ⟨dσ', dτ', dκ', hd, hC', hG', hWt', hRt'⟩ :=
          ih (readback mv' :: γ) N₁ out (mv' ∷ₑ ρ) g g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ
            hagN (MEnv.WF.cons hWFmv' hWF) (MEnv.WFClos.cons hWCmv' hP) hScN₁' hHWN₁' hG hC h
        refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt', hRt'⟩
        have hcrux : substEnv (readback mv' :: γ) N₁ = (closeUnderBindersE 1 γ N₁).subst (readback mv') :=
          (substEnv_cons_subst hγ hWFmv' N₁).symm
        simp only [substEnv_case, hrbw, hw, readback, Bang.CalcVM.evalD]
        rw [← hcrux]; exact hd
      | minr mv' =>
        rw [hw] at h
        have hWFmv' : MVal.WF mv' := by
          rw [hw] at hWFsc; simp only [MVal.WF, readback] at hWFsc
          exact (Val.ScopedV.inr_inv (fun k _ => hWFsc k)).closedE_zero
        have hWCmv' : MVal.WFClos mv' := by rw [hw] at hWCsc; simpa only [MVal.WFClos] using hWCsc
        have hagN : EnvAgrees (mv' ∷ₑ ρ) (readback mv' :: γ) := by
          simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hag]
        have hScN₂' : Comp.ScopedC (readback mv' :: γ).length N₂ := by
          simpa only [List.length_cons] using hScN₂
        have hHWN₂' : Comp.HandlerWF (readback mv' :: γ).length N₂ := by
          simpa only [List.length_cons] using (hlen ▸ hHWN₂ : Comp.HandlerWF (γ.length + 1) N₂)
        obtain ⟨dσ', dτ', dκ', hd, hC', hG', hWt', hRt'⟩ :=
          ih (readback mv' :: γ) N₂ out (mv' ∷ₑ ρ) g g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ
            hagN (MEnv.WF.cons hWFmv' hWF) (MEnv.WFClos.cons hWCmv' hP) hScN₂' hHWN₂' hG hC h
        refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt', hRt'⟩
        have hcrux : substEnv (readback mv' :: γ) N₂ = (closeUnderBindersE 1 γ N₂).subst (readback mv') :=
          (substEnv_cons_subst hγ hWFmv' N₂).symm
        simp only [substEnv_case, hrbw, hw, readback, Bang.CalcVM.evalD]
        rw [← hcrux]; exact hd
      | _ => rw [hw] at h; simp at h
    | split w N =>
      obtain ⟨hScw, hScN⟩ := hSc.split_inv
      obtain ⟨hHWw, hHWN⟩ := hHWF.split_inv
      have hscw : Val.ScopedV γ.length w := hlen ▸ hScw
      have hWFsc : MVal.WF (evalV ρ w) := evalV_WF hWF (hlen ▸ hscw)
      have hWCsc : MVal.WFClos (evalV ρ w) := evalV_WFClos hWF hP (hlen ▸ hscw) (hlen ▸ hHWw)
      have hrbw : substEnvV γ w = readback (evalV ρ w) := by
        rw [show γ = readbackEnv ρ from hag.symm, readback_evalV hWF (hlen ▸ hscw)]
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mpair mv₁ mv₂ =>
        rw [hw] at h
        rw [hw] at hWFsc hWCsc
        simp only [MVal.WF, readback] at hWFsc
        simp only [MVal.WFClos] at hWCsc
        have hWF₁ : MVal.WF mv₁ := (Val.ScopedV.pair_inv (fun k _ => hWFsc k)).1.closedE_zero
        have hWF₂ : MVal.WF mv₂ := (Val.ScopedV.pair_inv (fun k _ => hWFsc k)).2.closedE_zero
        have hagN : EnvAgrees (mv₂ ∷ₑ mv₁ ∷ₑ ρ) (readback mv₂ :: readback mv₁ :: γ) := by
          simp only [EnvAgrees, readbackEnv]; rw [show readbackEnv ρ = γ from hag]
        have hWFN : MEnv.WF (mv₂ ∷ₑ mv₁ ∷ₑ ρ) := MEnv.WF.cons hWF₂ (MEnv.WF.cons hWF₁ hWF)
        have hWCN : MEnv.WFClos (mv₂ ∷ₑ mv₁ ∷ₑ ρ) :=
          MEnv.WFClos.cons hWCsc.2 (MEnv.WFClos.cons hWCsc.1 hP)
        have hScN' : Comp.ScopedC (readback mv₂ :: readback mv₁ :: γ).length N := by
          simpa only [List.length_cons] using hScN
        have hHWN' : Comp.HandlerWF (readback mv₂ :: readback mv₁ :: γ).length N := by
          simpa only [List.length_cons] using (hlen ▸ hHWN : Comp.HandlerWF (γ.length + 2) N)
        obtain ⟨dσ', dτ', dκ', hd, hC', hG', hWt', hRt'⟩ :=
          ih (readback mv₂ :: readback mv₁ :: γ) N out (mv₂ ∷ₑ mv₁ ∷ₑ ρ) g g'
            eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ hagN hWFN hWCN hScN' hHWN' hG hC h
        refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt', hRt'⟩
        have hcrux : substEnv (readback mv₂ :: readback mv₁ :: γ) N
            = Comp.subst (readback mv₁) (Comp.subst (Val.shift (readback mv₂)) (closeUnderBindersE 2 γ N)) := by
          rw [substEnv_cons2_subst hγ hWF₁ hWF₂ N]; simp only [substEnv, Comp.subst]
        simp only [substEnv_split, hrbw, hw, readback, Bang.CalcVM.evalD]
        rw [hcrux] at hd; exact hd
      | _ => rw [hw] at h; simp at h
    | unfold w =>
      -- evalV ρ w = mfold mw ⇒ mret mw. evalD unfold (fold (readback mw)) ⇒ ret (readback mw).
      have hsc : Val.ScopedV γ.length w := hlen ▸ hSc.unfold_inv
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mfold mw =>
        rw [hw] at h
        simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
        obtain ⟨hout, hgc, hσ, hτ, hκ⟩ := h
        subst hout hgc hσ hτ hκ
        have hrb : substEnvV γ w = Val.fold (readback mw) := by
          rw [show γ = readbackEnv ρ from hag.symm, ← readback_evalV hWF (hlen ▸ hsc), hw]; rfl
        have hwfc : MVal.WFClos (MVal.mfold mw) := by
          have := evalV_WFClos hWF hP (hlen ▸ hsc) (hlen ▸ hHWF.unfold_inv); rw [hw] at this; exact this
        have hWFmw : MVal.WF mw := by
          have := evalV_WF hWF (hlen ▸ hsc); rw [hw] at this
          simp only [MVal.WF, readback] at this
          exact (Val.ScopedV.fold_inv (fun k _ => this k)).closedE_zero
        refine ⟨dσ, dτ, dκ, ?_, hC, hG, ?_, by rintro n op mv ⟨⟩⟩
        · simp only [substEnv_unfold, hrb, readbackTermS, readbackTerm, Bang.CalcVM.evalD]
        · rintro t ⟨rfl⟩
          exact ⟨hWFmw, by simpa only [MVal.WFClos] using hwfc⟩
      | _ => rw [hw] at h; simp at h
    | binop op a b =>
      -- evalV ρ a = mvint x, evalV ρ b = mvint y ⇒ mret (evalVOfBinop (op.eval x y)).
      obtain ⟨hSca, hScb⟩ := hSc.binop_inv
      have hsca : Val.ScopedV γ.length a := hlen ▸ hSca
      have hscb : Val.ScopedV γ.length b := hlen ▸ hScb
      simp only [evalE] at h
      cases ha : evalV ρ a with
      | mvint x =>
        cases hb : evalV ρ b with
        | mvint y =>
          rw [ha, hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
          obtain ⟨hout, hgc, hσ, hτ, hκ⟩ := h
          subst hout hgc hσ hτ hκ
          have hrba : substEnvV γ a = Val.vint x := by
            rw [show γ = readbackEnv ρ from hag.symm, ← readback_evalV hWF (hlen ▸ hsca), ha]; rfl
          have hrbb : substEnvV γ b = Val.vint y := by
            rw [show γ = readbackEnv ρ from hag.symm, ← readback_evalV hWF (hlen ▸ hscb), hb]; rfl
          have hWFres : MTerm.WF (MTerm.mret (evalE.evalVOfBinop (Bang.BinOp.eval op x y))) := by
            simp only [MTerm.WF, MVal.WF, readback_evalVOfBinop_eval]; exact BinOp_eval_closedE op x y
          refine ⟨dσ, dτ, dκ, ?_, hC, hG, ?_, by rintro n op mv ⟨⟩⟩
          · simp only [substEnv_binop, hrba, hrbb, readbackTermS, readbackTerm, Bang.CalcVM.evalD,
              readback_evalVOfBinop_eval]
          · rintro t ⟨rfl⟩
            exact ⟨hWFres, (evalVOfBinop_eval_pureV op x y).wfclos⟩
        | _ => rw [ha, hb] at h; simp at h
      | _ => rw [ha] at h; simp at h
    | perform w op v =>
      obtain ⟨hScw, hScv⟩ := hSc.perform_inv
      obtain ⟨hHWc, hHWv⟩ := hHWF.perform_inv
      have hscw : Val.ScopedV γ.length w := hlen ▸ hScw
      have hscv : Val.ScopedV γ.length v := hlen ▸ hScv
      have hWFarg : MVal.WF (evalV ρ v) := evalV_WF hWF (hlen ▸ hscv)
      have hWCarg : MVal.WFClos (evalV ρ v) := evalV_WFClos hWF hP (hlen ▸ hscv) (hlen ▸ hHWv)
      have hArgGood : MVal.WF (evalV ρ v) ∧ MVal.WFClos (evalV ρ v) := ⟨hWFarg, hWCarg⟩
      have hrbarg : substEnvV γ v = readback (evalV ρ v) := by
        rw [show γ = readbackEnv ρ from hag.symm, readback_evalV hWF (hlen ▸ hscv)]
      obtain ⟨hCσ, hCτ, hCκ⟩ := hC
      simp only [evalE] at h
      cases hw : evalV ρ w with
      | mvcap n ℓ =>
        rw [hw] at h
        simp only at h  -- reduce the `match (mvcap n ℓ)` iota-redex so the store matches surface
        have hrbw : substEnvV γ w = Val.vcap n ℓ := by
          rw [show γ = readbackEnv ρ from hag.symm, ← readback_evalV hWF (hlen ▸ hscw), hw]; rfl
        -- the evalD focus: perform (vcap n ℓ) op (readback arg).
        have hsubst : substEnv γ (Comp.perform w op v)
            = Comp.perform (Val.vcap n ℓ) op (readback (evalV ρ v)) := by
          simp only [substEnv_perform, hrbw, hrbarg]
        -- per-store get? agreement (W1).
        have hσeq : Bang.CalcVM.SStore.get? dσ n = (eσ.get? n).map readback := by
          rw [hCσ]; exact SStore.get?_readback eσ n
        cases hσget : eσ.get? n with
        | some s =>
          rw [hσget] at h
          simp only at h
          have hsGood := hG.get_state hσget
          have hσD : Bang.CalcVM.SStore.get? dσ n = some (readback s) := by rw [hσeq, hσget]; rfl
          by_cases hop : op = "get"
          · -- GET: mret s ↔ ret (readback s), σ unchanged.
            rw [if_pos hop] at h
            simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
            obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
            subst hout hgc hσ' hτ' hκ'
            refine ⟨dσ, dτ, dκ, ?_, ⟨hCσ, hCτ, hCκ⟩, hG, ?_, by rintro n op mv ⟨⟩⟩
            · rw [hsubst]
              simp only [Bang.CalcVM.evalD, hσD, hop, if_true, readbackTermS, readbackTerm]
            · rintro t ⟨rfl⟩; exact hsGood
          · by_cases hop2 : op = "put"
            · -- PUT: mret unit + σ.put; evalD ret unit + dσ.put (readback arg).
              rw [if_neg hop, if_pos hop2] at h
              simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨Bang.CalcVM.SStore.put dσ n (readback (evalV ρ v)), dτ, dκ, ?_, ?_,
                hG.put_state hArgGood, ?_, by rintro n op mv ⟨⟩⟩
              · rw [hsubst]
                subst hop2
                simp only [Bang.CalcVM.evalD, hσD, if_neg hop, readbackTermS, readbackTerm, readback,
                  reduceIte]
              · exact ⟨by rw [hCσ]; exact (SStore.put_readback eσ n (evalV ρ v)).symm ▸ rfl, hCτ, hCκ⟩
              · rintro t ⟨rfl⟩; exact ⟨by simp only [MTerm.WF, MVal.WF, readback]; intro k; rfl,
                  by simp only [MTerm.WFClos, MVal.WFClos]⟩
            · -- other op on a state frame ⇒ RAISE.
              rw [if_neg hop, if_neg hop2] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨dσ, dτ, dκ, ?_, ⟨hCσ, hCτ, hCκ⟩, hG, by rintro t ⟨⟩, ?_⟩
              · rw [hsubst]
                simp only [Bang.CalcVM.evalD, hσD, hop, if_false, hop2, if_false, readbackTermS,
                  hrbarg]
              · rintro n' op' mv' ⟨rfl, rfl, rfl⟩; exact hArgGood
        | none =>
          rw [hσget] at h
          simp only at h
          have hσD : Bang.CalcVM.SStore.get? dσ n = none := by rw [hσeq, hσget]; rfl
          have hτeq : Bang.CalcVM.THeap.get? dτ n = (eτ.get? n).map (List.map readback) := by
            rw [hCτ]; exact THeap.get?_readback eτ n
          cases hτget : eτ.get? n with
          | some Θ =>
            rw [hτget] at h
            simp only at h
            have hτD : Bang.CalcVM.THeap.get? dτ n = some (Θ.map readback) := by rw [hτeq, hτget]; rfl
            -- Θ's cells are good (from StoresGood τ-clause).
            have hΘgood : ∀ mv ∈ Θ, MVal.WF mv ∧ MVal.WFClos mv := by
              intro mv hmv
              have hmem : (n, Θ) ∈ eτ := by
                simp only [ETHeap.get?, Option.map_eq_some_iff] at hτget
                obtain ⟨p, hf, hp⟩ := hτget
                have := List.mem_of_find?_eq_some hf
                have hp1 : p = (n, Θ) := by
                  obtain ⟨a, b⟩ := p; simp only at hp; rw [← hp]
                  have : a = n := by
                    have := List.find?_some hf; simp only [decide_eq_true_eq] at this; exact this
                  simp only [this]
                rw [hp1] at this; exact this
              exact hG.2.1 (n, Θ) hmem mv hmv
            by_cases hoptxn : Bang.CalcVM.isTxnOp op = true
            · -- TXN service.
              simp only [hoptxn, if_true] at h
              simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨dσ, Bang.CalcVM.THeap.put dτ n ((mtxnService op (evalV ρ v) Θ).2.map readback),
                dκ, ?_, ?_, hG.put_txn (mtxnService_good hArgGood hΘgood), ?_, by rintro n op mv ⟨⟩⟩
              · rw [hsubst]
                simp only [Bang.CalcVM.evalD, hσD, hτD, hoptxn, if_true]
                rw [mtxnService_readback op (evalV ρ v) Θ]
                simp only [readbackTermS, readbackTerm]
              · exact ⟨hCσ, by rw [hCτ]; exact (THeap.put_readback eτ n (mtxnService op (evalV ρ v) Θ).2).symm ▸ rfl, hCκ⟩
              · rintro t ⟨rfl⟩
                -- the returned value r is WFClos: it's a heap cell (readTVar), an index (newTVar), or unit.
                exact mtxnService_result_good hΘgood
            · -- non-txn op on a txn frame ⇒ RAISE.
              simp only [hoptxn, Bool.false_eq_true, if_false] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨dσ, dτ, dκ, ?_, ⟨hCσ, hCτ, hCκ⟩, hG, by rintro t ⟨⟩, ?_⟩
              · rw [hsubst]
                have hisTxn : Bang.CalcVM.isTxnOp op = false := Bool.not_eq_true _ |>.mp hoptxn
                simp only [Bang.CalcVM.evalD, hσD, hτD, hisTxn, Bool.false_eq_true, if_false,
                  readbackTermS, hrbarg]
              · rintro n' op' mv' ⟨rfl, rfl, rfl⟩; exact hArgGood
          | none =>
            rw [hτget] at h
            simp only at h
            have hτD : Bang.CalcVM.THeap.get? dτ n = none := by rw [hτeq, hτget]; rfl
            have hκeq : Bang.CalcVM.CStore.get? dκ n
                = (eκ.get? n).map (fun t => (readback t.1,
                    t.2.1.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv t.2.2) c.2)))) := by
              rw [hCκ]; exact CStore.get?_readback eκ n
            cases hκget : eκ.get? n with
            | some pcls =>
              obtain ⟨p, cls, ρ_inst⟩ := pcls
              rw [hκget] at h
              simp only at h
              have hκD : Bang.CalcVM.CStore.get? dκ n
                  = some (readback p, cls.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv ρ_inst) c.2))) := by
                rw [hκeq, hκget]; rfl
              obtain ⟨hpGood, hWFρinst, hWCρinst, hclsScope⟩ := hG.get_custom hκget
              cases hclsfind : cls.find? (·.1 == op) with
              | some clause =>
                rw [hclsfind] at h
                -- evalE runs clause.2 under (arg ∷ p ∷ ρ_inst); evalD runs its CLOSED image via the crux.
                have hclmem : clause ∈ cls := List.mem_of_find?_eq_some hclsfind
                obtain ⟨hclScope, hclHW⟩ := hclsScope clause hclmem
                obtain ⟨hWFp, hWCp⟩ := hpGood
                -- env agreement for the extended install-env.
                have hagN : EnvAgrees (evalV ρ v ∷ₑ p ∷ₑ ρ_inst)
                    (readback (evalV ρ v) :: readback p :: readbackEnv ρ_inst) := by
                  simp only [EnvAgrees, readbackEnv]
                have hWFN : MEnv.WF (evalV ρ v ∷ₑ p ∷ₑ ρ_inst) :=
                  MEnv.WF.cons hWFarg (MEnv.WF.cons hWFp hWFρinst)
                have hWCN : MEnv.WFClos (evalV ρ v ∷ₑ p ∷ₑ ρ_inst) :=
                  MEnv.WFClos.cons hWCarg (MEnv.WFClos.cons hWCp hWCρinst)
                have hScN : Comp.ScopedC (readback (evalV ρ v) :: readback p :: readbackEnv ρ_inst).length clause.2 := by
                  simpa only [List.length_cons] using hclScope
                have hHWN : Comp.HandlerWF (readback (evalV ρ v) :: readback p :: readbackEnv ρ_inst).length clause.2 := by
                  simpa only [List.length_cons] using hclHW
                obtain ⟨dσ', dτ', dκ', hdN, hC', hG', hWt', hRt'⟩ :=
                  ih (readback (evalV ρ v) :: readback p :: readbackEnv ρ_inst) clause.2 out
                    (evalV ρ v ∷ₑ p ∷ₑ ρ_inst) g g' eσ eσ' eτ eτ' eκ eκ'
                    dσ dτ dκ hagN hWFN hWCN hScN hHWN hG ⟨hCσ, hCτ, hCκ⟩ h
                refine ⟨dσ', dτ', dκ', ?_, hC', hG', hWt', hRt'⟩
                -- the crux: substEnv (arg :: p :: rbEnv ρ_inst) clause.2
                --   = subst (readback p) (subst (shift (readback arg)) (closeUnderBindersE 2 (rbEnv ρ_inst) clause.2)).
                have hγinst : ∀ u ∈ readbackEnv ρ_inst, Val.ClosedE u := hWFρinst
                have hcrux : substEnv (readback (evalV ρ v) :: readback p :: readbackEnv ρ_inst) clause.2
                    = Comp.subst (readback p) (Comp.subst (Val.shift (readback (evalV ρ v)))
                        (closeUnderBindersE 2 (readbackEnv ρ_inst) clause.2)) := by
                  rw [substEnv_cons2_subst hγinst hWFp hWFarg clause.2]; simp only [substEnv, Comp.subst]
                -- evalD find? on the CLOSED cls returns the closed clause.
                have hfindD : (cls.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv ρ_inst) c.2))).find? (·.1 == op)
                    = some (clause.1, closeUnderBindersE 2 (readbackEnv ρ_inst) clause.2) := by
                  rw [List.find?_map,
                    show ((fun x => x.1 == op) ∘ fun c => (c.1, closeUnderBindersE 2 (readbackEnv ρ_inst) c.2))
                      = (fun x : Bang.OpId × Comp => x.1 == op) from rfl, hclsfind]; rfl
                rw [hsubst]
                simp only [Bang.CalcVM.evalD, hσD, hτD, hκD, hfindD]
                rw [hcrux] at hdN
                exact hdN
              | none =>
                rw [hclsfind] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
                subst hout hgc hσ' hτ' hκ'
                refine ⟨dσ, dτ, dκ, ?_, ⟨hCσ, hCτ, hCκ⟩, hG, by rintro t ⟨⟩, ?_⟩
                · rw [hsubst]
                  have hfindD : (cls.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv ρ_inst) c.2))).find? (·.1 == op) = none := by
                    rw [List.find?_map,
                      show ((fun x => x.1 == op) ∘ fun c => (c.1, closeUnderBindersE 2 (readbackEnv ρ_inst) c.2))
                        = (fun x : Bang.OpId × Comp => x.1 == op) from rfl, hclsfind, Option.map_none]
                  simp only [Bang.CalcVM.evalD, hσD, hτD, hκD, hfindD, readbackTermS]
                · rintro n' op' mv' ⟨rfl, rfl, rfl⟩; exact hArgGood
            | none =>
              rw [hκget] at h
              simp only at h
              have hκD : Bang.CalcVM.CStore.get? dκ n = none := by rw [hκeq, hκget]; rfl
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨dσ, dτ, dκ, ?_, ⟨hCσ, hCτ, hCκ⟩, hG, by rintro t ⟨⟩, ?_⟩
              · rw [hsubst]
                simp only [Bang.CalcVM.evalD, hσD, hτD, hκD, readbackTermS, hrbarg]
              · rintro n' op' mv' ⟨rfl, rfl, rfl⟩; exact hArgGood
      | _ => rw [hw] at h; simp at h
    | handle hdl M =>
      -- HANDLE (envm3 resume — the last _gen case). Infra ALL landed + green:
      --   substEnv_handle · substEnvH_{state,transaction,custom,throws,label} · hSc.handle_inv ·
      --   the mint crux (substEnv_cons_subst with vcap ClosedE) · single-counter (mint keys g on both).
      -- SHAPE per kind (mirror the perform arm + the letC raise short-circuit):
      --   mint id:=g, extend ρ with mvcap g (label hdl), recurse at g+1 under the pushed store entry,
      --   then match the recursion outcome and POP (.tail) — .tail commutes with the readback-map so
      --   StoresCorr survives. The pushed entry relates by readback: state evalV ρ s ↔ substEnvV γ s
      --   (readback_evalV); txn Θ.map(evalV ρ) ↔ Θ (needs Θ cells CLOSED — kernel ADR-0030, add a
      --   handler-payload-scope premise or derive from hSc); custom (evalV ρ p, cls, ρ) ↔
      --   (readback p, closed-cls) — CStoreCorr by construction. throws: no push; CATCH mraised g
      --   "raise" ⟺ evalD raised g "raise" (if_neg/if_pos on n=g∧op="raise"). The recursion IH fires
      --   at fuel f (evalE/evalD both recurse at f). A first throws-arm attempt hit fiddly evalD
      --   reduction (the nested `show … from by` rewrites) — do the evalD side with a clean
      --   `rw [substEnv_handle]; simp only [Bang.CalcVM.evalD, Handler.label, substEnvH_*]` then bind
      --   the recursion via the IH `hdR`, mirroring perform, NOT nested `show`s.
      have hScM : Comp.ScopedC (γ.length + 1) M := hlen ▸ hSc.handle_inv
      -- the minted cap `vcap g (Handler.label hdl)` is ClosedE (shiftFrom is rfl on a vcap).
      have hCapClosed : Val.ClosedE (Val.vcap g (Handler.label hdl)) := by
        intro k; rfl
      -- the extended install-env `mvcap g ℓ ∷ₑ ρ` agrees with `vcap g ℓ :: γ` and is WF/WFClos.
      have hagN : EnvAgrees (MVal.mvcap g (Handler.label hdl) ∷ₑ ρ)
          (Val.vcap g (Handler.label hdl) :: γ) := by
        simp only [EnvAgrees, readbackEnv, readback]; rw [show readbackEnv ρ = γ from hag]
      have hWFcap : Val.ClosedE (readback (MVal.mvcap g (Handler.label hdl))) := by
        simp only [readback]; exact hCapClosed
      have hWFN : MEnv.WF (MVal.mvcap g (Handler.label hdl) ∷ₑ ρ) :=
        MEnv.WF.cons hWFcap hWF
      have hWCN : MEnv.WFClos (MVal.mvcap g (Handler.label hdl) ∷ₑ ρ) :=
        MEnv.WFClos.cons (by simp only [MVal.WFClos]) hP
      have hScN : Comp.ScopedC (Val.vcap g (Handler.label hdl) :: γ).length M := by
        simpa only [List.length_cons] using hScM
      have hHWM : Comp.HandlerWF (γ.length + 1) M := hlen ▸ hHWF.handle_body
      have hHWNbody : Comp.HandlerWF (Val.vcap g (Handler.label hdl) :: γ).length M := by
        simpa only [List.length_cons] using hHWM
      -- the mint crux: the extended-env substEnv IS the closed body with the cap substituted.
      have hcrux : substEnv (Val.vcap g (Handler.label hdl) :: γ) M
          = Comp.subst (Val.vcap g (Handler.label hdl)) (closeUnderBindersE 1 γ M) :=
        (substEnv_cons_subst hγ hCapClosed M).symm
      -- `.tail` of a StoresGood store stays StoresGood (membership in tail ⊆ membership in list).
      have hσtail : ∀ {eσ₀ : ESStore} {eτ₀ : ETHeap} {eκ₀ : ECStore},
          StoresGood eσ₀ eτ₀ eκ₀ → StoresGood eσ₀.tail eτ₀ eκ₀ := by
        rintro eσ₀ eτ₀ eκ₀ ⟨hs, ht, hk⟩
        exact ⟨fun p hp => hs p (List.mem_of_mem_tail hp), ht, hk⟩
      have hτtail : ∀ {eσ₀ : ESStore} {eτ₀ : ETHeap} {eκ₀ : ECStore},
          StoresGood eσ₀ eτ₀ eκ₀ → StoresGood eσ₀ eτ₀.tail eκ₀ := by
        rintro eσ₀ eτ₀ eκ₀ ⟨hs, ht, hk⟩
        exact ⟨hs, fun p hp => ht p (List.mem_of_mem_tail hp), hk⟩
      have hκtail : ∀ {eσ₀ : ESStore} {eτ₀ : ETHeap} {eκ₀ : ECStore},
          StoresGood eσ₀ eτ₀ eκ₀ → StoresGood eσ₀ eτ₀ eκ₀.tail := by
        rintro eσ₀ eτ₀ eκ₀ ⟨hs, ht, hk⟩
        exact ⟨hs, ht, fun p hp => hk p (List.mem_of_mem_tail hp)⟩
      obtain ⟨hCσ, hCτ, hCκ⟩ := hC
      cases hdl with
      | state ℓ s =>
        -- STATE mint: push (g, evalV ρ s) on σ; the pushed cell reads back to (g, readback (evalV ρ s)),
        -- and readback (evalV ρ s) = substEnvV γ s (the value correspondence). Recurse at g+1, POP with .tail.
        simp only [Handler.label] at hCapClosed hagN hWFcap hWFN hWCN hScN hHWNbody hcrux
        have hscs : Val.ScopedV γ.length s := hlen ▸ (by
          have := hSc; intro k hk
          have h1 := this k (by omega)
          simp only [Comp.shiftFrom, Handler.shiftFrom, Comp.handle.injEq] at h1
          have := h1.1; simp only [Handler.state.injEq] at this; exact this.2)
        have hWFs : MVal.WF (evalV ρ s) := evalV_WF hWF (hlen ▸ hscs)
        have hWCs : MVal.WFClos (evalV ρ s) :=
          evalV_WFClos hWF hP (hlen ▸ hscs) (hlen ▸ hHWF.handle_state)
        have hrbs : substEnvV γ s = readback (evalV ρ s) := by
          rw [show γ = readbackEnv ρ from hag.symm, readback_evalV hWF (hlen ▸ hscs)]
        simp only [evalE, Handler.label, Option.bind_eq_bind] at h
        -- the pushed evalE σ reads back to the pushed evalD σ (SStoreCorr on the cons).
        have hCσ' : SStoreCorr (⟨g, evalV ρ s⟩ :: eσ) (⟨g, readback (evalV ρ s)⟩ :: dσ) := by
          simp only [SStoreCorr, List.map_cons]; rw [show dσ = _ from hCσ]
        have hGpush : StoresGood (⟨g, evalV ρ s⟩ :: eσ) eτ eκ := by
          obtain ⟨hs0, ht0, hk0⟩ := hG
          refine ⟨fun p hp => ?_, ht0, hk0⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨hWFs, hWCs⟩
          · exact hs0 p hp
        cases hev : evalE f (g+1) (⟨g, evalV ρ s⟩ :: eσ) eτ eκ
            (MVal.mvcap g ℓ ∷ₑ ρ) M with
        | none => rw [hev] at h; simp only [Option.bind_none, reduceCtorEq] at h
        | some p =>
          rw [hev] at h
          obtain ⟨outR, gR, σR, τR, κR⟩ := p
          obtain ⟨dσR, dτR, dκR, hdR, hCR, hGR, hWtR, hRtR⟩ :=
            ih (Val.vcap g ℓ :: γ) M outR (MVal.mvcap g ℓ ∷ₑ ρ) (g+1) gR
              (⟨g, evalV ρ s⟩ :: eσ) σR eτ τR eκ κR
              (⟨g, readback (evalV ρ s)⟩ :: dσ) dτ dκ hagN hWFN hWCN hScN hHWNbody hGpush
              ⟨hCσ', hCτ, hCκ⟩ hev
          -- push the closed body into hdR so it lines up with the evalD state-mint focus.
          rw [hcrux] at hdR
          have hdR' : Bang.CalcVM.evalD f (g+1) (Bang.CalcVM.SStore.push dσ g (readback (evalV ρ s)))
              dτ dκ (Comp.subst (Val.vcap g ℓ) (closeUnderBindersE 1 γ M))
              = some (readbackTermS outR, gR, dσR, dτR, dκR) := hdR
          -- now split on the recursion outcome; POP with .tail on both sides.
          cases outR with
          | mterm tR => cases tR with
            | mret v =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                MOutcome.mterm.injEq, MTerm.mret.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              obtain ⟨hCσR, hCτR, hCκR⟩ := hCR
              refine ⟨dσR.tail, dτR, dκR, ?_, ?_, hσtail hGR, ?_, by rintro n op mv ⟨⟩⟩
              · rw [substEnv_handle]
                simp only [Bang.CalcVM.evalD, substEnvH_state, Handler.label, hrbs]
                rw [hdR']; simp only [readbackTermS, readbackTerm, Option.bind_some]
              · refine ⟨?_, hCτR, hCκR⟩
                simp only [SStoreCorr] at hCσR ⊢; rw [hCσR, ← List.map_tail]
              · rintro t ⟨rfl⟩; exact hWtR _ rfl
            | mlam _ _ =>
              simp only [Option.bind_some, reduceCtorEq] at h
          | mraised n op' w =>
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
            subst hout hgc hσ' hτ' hκ'
            obtain ⟨hCσR, hCτR, hCκR⟩ := hCR
            refine ⟨dσR.tail, dτR, dκR, ?_, ?_, hσtail hGR, by rintro t ⟨⟩, ?_⟩
            · rw [substEnv_handle]
              simp only [Bang.CalcVM.evalD, substEnvH_state, Handler.label, hrbs]
              rw [hdR']; simp only [readbackTermS, Option.bind_some]
            · refine ⟨?_, hCτR, hCκR⟩
              simp only [SStoreCorr] at hCσR ⊢; rw [hCσR, ← List.map_tail]
            · rintro n' op'' mv' ⟨rfl, rfl, rfl⟩; exact hRtR _ _ _ rfl
      | throws ℓ =>
        -- THROWS mint: NO push. Recurse at g+1; CATCH mraised g "raise" ⟺ evalD raised g "raise".
        simp only [Handler.label] at hCapClosed hagN hWFcap hWFN hWCN hScN hHWNbody hcrux
        simp only [evalE, Handler.label, Option.bind_eq_bind] at h
        cases hev : evalE f (g+1) eσ eτ eκ (MVal.mvcap g ℓ ∷ₑ ρ) M with
        | none => rw [hev] at h; simp only [Option.bind_none, reduceCtorEq] at h
        | some p =>
          rw [hev] at h
          obtain ⟨outR, gR, σR, τR, κR⟩ := p
          obtain ⟨dσR, dτR, dκR, hdR, hCR, hGR, hWtR, hRtR⟩ :=
            ih (Val.vcap g ℓ :: γ) M outR (MVal.mvcap g ℓ ∷ₑ ρ) (g+1) gR
              eσ σR eτ τR eκ κR dσ dτ dκ hagN hWFN hWCN hScN hHWNbody hG ⟨hCσ, hCτ, hCκ⟩ hev
          rw [hcrux] at hdR
          have hdR' : Bang.CalcVM.evalD f (g+1) dσ dτ dκ
              (Comp.subst (Val.vcap g ℓ) (closeUnderBindersE 1 γ M))
              = some (readbackTermS outR, gR, dσR, dτR, dκR) := hdR
          cases outR with
          | mterm tR => cases tR with
            | mret v =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                MOutcome.mterm.injEq, MTerm.mret.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨dσR, dτR, dκR, ?_, hCR, hGR, ?_, by rintro n op mv ⟨⟩⟩
              · rw [substEnv_handle]
                simp only [Bang.CalcVM.evalD, substEnvH_throws, Handler.label]
                rw [hdR']; simp only [readbackTermS, readbackTerm, Option.bind_some]
              · rintro t ⟨rfl⟩; exact hWtR _ rfl
            | mlam _ _ =>
              simp only [Option.bind_some, reduceCtorEq] at h
          | mraised n op' w =>
            simp only [Option.bind_some] at h
            by_cases hcatch : n = g ∧ op' = "raise"
            · -- CAUGHT: mret w ⟺ evalD ret w. KEEP the stores.
              rw [if_pos hcatch] at h
              simp only [Option.some.injEq, Prod.mk.injEq, MOutcome.mterm.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              obtain ⟨hWFw, hWCw⟩ := hRtR _ _ _ rfl
              refine ⟨dσR, dτR, dκR, ?_, hCR, hGR, ?_, by rintro n op mv ⟨⟩⟩
              · rw [substEnv_handle]
                simp only [Bang.CalcVM.evalD, substEnvH_throws, Handler.label]
                rw [hdR']; simp only [readbackTermS, Option.bind_some, hcatch.1, hcatch.2, and_self,
                  if_true, readbackTerm]
              · rintro t ⟨rfl⟩; exact ⟨hWFw, hWCw⟩
            · -- FORWARD: mraised n op' w ⟺ evalD raised n op' w.
              rw [if_neg hcatch] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              refine ⟨dσR, dτR, dκR, ?_, hCR, hGR, by rintro t ⟨⟩, ?_⟩
              · rw [substEnv_handle]
                simp only [Bang.CalcVM.evalD, substEnvH_throws, Handler.label]
                rw [hdR']; simp only [readbackTermS, Option.bind_some, if_neg hcatch]
              · rintro n' op'' mv' ⟨rfl, rfl, rfl⟩; exact hRtR _ _ _ rfl
      | transaction ℓ Θ =>
        -- TXN mint: push (g, Θ.map (evalV ρ)) on τ; evalD pushes the RAW Θ (substEnvH_transaction is id
        -- on Θ). THeapCorr on the pushed frames needs (Θ.map (evalV ρ)).map readback = Θ, i.e.
        -- readback (evalV ρ θ) = θ for each θ ∈ Θ — holds because θ is CLOSED (hHWF.handle_txn, the
        -- ADR-0030 heap-closed invariant). Recurse at g+1, POP with τ.tail.
        simp only [Handler.label] at hCapClosed hagN hWFcap hWFN hWCN hScN hHWNbody hcrux
        have hΘgood : ∀ θ ∈ Θ, Val.ClosedE θ ∧ ∀ m, Val.HandlerWF m θ := hHWF.handle_txn
        -- each pushed cell reads back to itself (closed) and is WF ∧ WFClos.
        have hcellId : ∀ θ ∈ Θ, readback (evalV ρ θ) = θ := by
          intro θ hθ
          have hcl := (hΘgood θ hθ).1
          rw [readback_evalV hWF (fun k _ => hcl k)]
          exact closeVE_closed hcl (readbackEnv ρ)
        have hΘmapGood : ∀ mv ∈ Θ.map (evalV ρ), MVal.WF mv ∧ MVal.WFClos mv := by
          intro mv hmv
          simp only [List.mem_map] at hmv
          obtain ⟨θ, hθ, rfl⟩ := hmv
          obtain ⟨hcl, hHWθ⟩ := hΘgood θ hθ
          refine ⟨?_, evalV_WFClos hWF hP (fun k _ => hcl k) (hHWθ _)⟩
          simp only [MVal.WF]; rw [hcellId θ hθ]; exact hcl
        -- THeapCorr on the pushed cons: evalD pushes RAW Θ; (Θ.map (evalV ρ)).map readback = Θ.
        have hΘrb : (Θ.map (evalV ρ)).map readback = Θ := by
          rw [List.map_map]
          conv_rhs => rw [← List.map_id Θ]
          exact List.map_congr_left (fun θ hθ => by simp only [Function.comp]; exact hcellId θ hθ)
        have hCτ' : THeapCorr (⟨g, Θ.map (evalV ρ)⟩ :: eτ) (⟨g, Θ⟩ :: dτ) := by
          simp only [THeapCorr, List.map_cons]; rw [show dτ = _ from hCτ, hΘrb]
        have hGpush : StoresGood eσ (⟨g, Θ.map (evalV ρ)⟩ :: eτ) eκ := by
          obtain ⟨hs0, ht0, hk0⟩ := hG
          refine ⟨hs0, fun p hp => ?_, hk0⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hΘmapGood
          · exact ht0 p hp
        simp only [evalE, Handler.label, Option.bind_eq_bind] at h
        cases hev : evalE f (g+1) eσ (⟨g, Θ.map (evalV ρ)⟩ :: eτ) eκ
            (MVal.mvcap g ℓ ∷ₑ ρ) M with
        | none => rw [hev] at h; simp only [Option.bind_none, reduceCtorEq] at h
        | some p =>
          rw [hev] at h
          obtain ⟨outR, gR, σR, τR, κR⟩ := p
          obtain ⟨dσR, dτR, dκR, hdR, hCR, hGR, hWtR, hRtR⟩ :=
            ih (Val.vcap g ℓ :: γ) M outR (MVal.mvcap g ℓ ∷ₑ ρ) (g+1) gR
              eσ σR (⟨g, Θ.map (evalV ρ)⟩ :: eτ) τR eκ κR
              dσ (⟨g, Θ⟩ :: dτ) dκ hagN hWFN hWCN hScN hHWNbody hGpush
              ⟨hCσ, hCτ', hCκ⟩ hev
          rw [hcrux] at hdR
          have hdR' : Bang.CalcVM.evalD f (g+1) dσ (Bang.CalcVM.THeap.push dτ g Θ) dκ
              (Comp.subst (Val.vcap g ℓ) (closeUnderBindersE 1 γ M))
              = some (readbackTermS outR, gR, dσR, dτR, dκR) := hdR
          cases outR with
          | mterm tR => cases tR with
            | mret v =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                MOutcome.mterm.injEq, MTerm.mret.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              obtain ⟨hCσR, hCτR, hCκR⟩ := hCR
              refine ⟨dσR, dτR.tail, dκR, ?_, ?_, hτtail hGR, ?_, by rintro n op mv ⟨⟩⟩
              · rw [substEnv_handle]
                simp only [Bang.CalcVM.evalD, substEnvH_transaction, Handler.label]
                rw [hdR']; simp only [readbackTermS, readbackTerm, Option.bind_some]
              · refine ⟨hCσR, ?_, hCκR⟩
                simp only [THeapCorr] at hCτR ⊢; rw [hCτR, ← List.map_tail]
              · rintro t ⟨rfl⟩; exact hWtR _ rfl
            | mlam _ _ =>
              simp only [Option.bind_some, reduceCtorEq] at h
          | mraised n op' w =>
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
            subst hout hgc hσ' hτ' hκ'
            obtain ⟨hCσR, hCτR, hCκR⟩ := hCR
            refine ⟨dσR, dτR.tail, dκR, ?_, ?_, hτtail hGR, by rintro t ⟨⟩, ?_⟩
            · rw [substEnv_handle]
              simp only [Bang.CalcVM.evalD, substEnvH_transaction, Handler.label]
              rw [hdR']; simp only [readbackTermS, Option.bind_some]
            · refine ⟨hCσR, ?_, hCκR⟩
              simp only [THeapCorr] at hCτR ⊢; rw [hCτR, ← List.map_tail]
            · rintro n' op'' mv' ⟨rfl, rfl, rfl⟩; exact hRtR _ _ _ rfl
      | custom ℓ p cls =>
        -- CUSTOM mint: push (g, (evalV ρ p, cls, ρ)) on κ; evalD pushes the RAW (p, cls) — `substEnvH_custom`
        -- is IDENTITY on the payload. CStoreCorr on the pushed frame needs `readback (evalV ρ p) = p`
        -- (p CLOSED, `ScopedV 0`) and `closeUnderBindersE 2 (readbackEnv ρ) c.2 = c.2` per clause (PAYLOAD-
        -- CLOSED `ScopedC 2` ⇒ close-is-identity), so the clause-map collapses to the RAW `cls`. Recurse at
        -- g+1, POP with κ.tail. Structural sibling of the state/txn mint. (ruling #6, task #11)
        simp only [Handler.label] at hCapClosed hagN hWFcap hWFN hWCN hScN hHWNbody hcrux
        obtain ⟨⟨hpClosed, hpHW⟩, hclsScope, hclsHW⟩ := hHWF.handle_custom
        have hpcl : Val.ClosedE p := hpClosed.closedE_zero
        -- the pushed param reads back to itself (closed) and is WF ∧ WFClos.
        have hpId : readback (evalV ρ p) = p := by
          rw [readback_evalV hWF (fun k _ => hpcl k)]; exact closeVE_closed hpcl (readbackEnv ρ)
        have hWFp : MVal.WF (evalV ρ p) := by
          simp only [MVal.WF]; rw [hpId]; exact hpcl
        have hWCp : MVal.WFClos (evalV ρ p) :=
          evalV_WFClos hWF hP (hpClosed.mono (Nat.zero_le _))
            (Val.HandlerWF.mono p 0 (readbackEnv ρ).length (Nat.zero_le _) hpHW)
        -- each clause is closed under `closeUnderBindersE 2 (readbackEnv ρ)` (payload-closed ⇒ identity).
        have hclsId : cls.map (fun c => (c.1, closeUnderBindersE 2 (readbackEnv ρ) c.2)) = cls := by
          conv_rhs => rw [← List.map_id cls]
          exact List.map_congr_left (fun c hc => by
            simp only [id, closeUnderBindersE_scoped_id (hclsScope c hc) (readbackEnv ρ)])
        -- the pushed frame is StoresGood: p WF/WFClos, ρ WF/WFClos, and each clause scoped/HandlerWF at
        -- the RELATIVE index `(readbackEnv ρ).length + 2` (lifted from the absolute `ScopedC 2`/`HandlerWF 2`).
        have hGpush : StoresGood eσ eτ (⟨g, (evalV ρ p, cls, ρ)⟩ :: eκ) := by
          obtain ⟨hs0, ht0, hk0⟩ := hG
          refine ⟨hs0, ht0, fun q hq => ?_⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨⟨hWFp, hWCp⟩, hWF, hP, fun c hc =>
              ⟨(hclsScope c hc).mono (by omega),
               Comp.HandlerWF.mono c.2 2 ((readbackEnv ρ).length + 2) (by omega) (hclsHW.get c hc)⟩⟩
          · exact hk0 q hq
        -- CStoreCorr on the pushed cons: evalD pushes RAW (p, cls); the readback-map collapses to it.
        have hCκ' : CStoreCorr (⟨g, (evalV ρ p, cls, ρ)⟩ :: eκ) (⟨g, (p, cls)⟩ :: dκ) := by
          simp only [CStoreCorr, List.map_cons]; rw [show dκ = _ from hCκ, hpId, hclsId]
        simp only [evalE, Handler.label, Option.bind_eq_bind] at h
        cases hev : evalE f (g+1) eσ eτ (⟨g, (evalV ρ p, cls, ρ)⟩ :: eκ)
            (MVal.mvcap g ℓ ∷ₑ ρ) M with
        | none => rw [hev] at h; simp only [Option.bind_none, reduceCtorEq] at h
        | some q =>
          rw [hev] at h
          obtain ⟨outR, gR, σR, τR, κR⟩ := q
          obtain ⟨dσR, dτR, dκR, hdR, hCR, hGR, hWtR, hRtR⟩ :=
            ih (Val.vcap g ℓ :: γ) M outR (MVal.mvcap g ℓ ∷ₑ ρ) (g+1) gR
              eσ σR eτ τR (⟨g, (evalV ρ p, cls, ρ)⟩ :: eκ) κR
              dσ dτ (⟨g, (p, cls)⟩ :: dκ) hagN hWFN hWCN hScN hHWNbody hGpush
              ⟨hCσ, hCτ, hCκ'⟩ hev
          rw [hcrux] at hdR
          have hdR' : Bang.CalcVM.evalD f (g+1) dσ dτ (Bang.CalcVM.CStore.push dκ g p cls)
              (Comp.subst (Val.vcap g ℓ) (closeUnderBindersE 1 γ M))
              = some (readbackTermS outR, gR, dσR, dτR, dκR) := hdR
          cases outR with
          | mterm tR => cases tR with
            | mret v =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                MOutcome.mterm.injEq, MTerm.mret.injEq] at h
              obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
              subst hout hgc hσ' hτ' hκ'
              obtain ⟨hCσR, hCτR, hCκR⟩ := hCR
              refine ⟨dσR, dτR, dκR.tail, ?_, ?_, hκtail hGR, ?_, by rintro n op mv ⟨⟩⟩
              · rw [substEnv_handle]
                simp only [Bang.CalcVM.evalD, substEnvH_custom, Handler.label]
                rw [hdR']; simp only [readbackTermS, readbackTerm, Option.bind_some]
              · refine ⟨hCσR, hCτR, ?_⟩
                simp only [CStoreCorr] at hCκR ⊢; rw [hCκR, ← List.map_tail]
              · rintro t ⟨rfl⟩; exact hWtR _ rfl
            | mlam _ _ =>
              simp only [Option.bind_some, reduceCtorEq] at h
          | mraised n op' w =>
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hout, hgc, hσ', hτ', hκ'⟩ := h
            subst hout hgc hσ' hτ' hκ'
            obtain ⟨hCσR, hCτR, hCκR⟩ := hCR
            refine ⟨dσR, dτR, dκR.tail, ?_, ?_, hκtail hGR, by rintro t ⟨⟩, ?_⟩
            · rw [substEnv_handle]
              simp only [Bang.CalcVM.evalD, substEnvH_custom, Handler.label]
              rw [hdR']; simp only [readbackTermS, Option.bind_some]
            · refine ⟨hCσR, hCτR, ?_⟩
              simp only [CStoreCorr] at hCκR ⊢; rw [hCκR, ← List.map_tail]
            · rintro n' op'' mv' ⟨rfl, rfl, rfl⟩; exact hRtR _ _ _ rfl
    | oom => simp [evalE] at h
    | wrong s => simp [evalE] at h

theorem evalE_agrees_evalD_effect :
    ∀ (f : Nat) (γ : List Val) (M : Comp) (t : MTerm) (ρ : MEnv) (g g' : Nat)
      (eσ eσ' : ESStore) (eτ eτ' : ETHeap) (eκ eκ' : ECStore)
      (dσ : Bang.CalcVM.SStore) (dτ : Bang.CalcVM.THeap) (dκ : Bang.CalcVM.CStore),
      EnvAgrees ρ γ → MEnv.WF ρ → MEnv.WFClos ρ → Comp.ScopedC γ.length M →
      Comp.HandlerWF γ.length M →
      StoresGood eσ eτ eκ → StoresCorr eσ eτ eκ dσ dτ dκ →
      evalE f g eσ eτ eκ ρ M = some (.mterm t, g', eσ', eτ', eκ') →
      ∃ (dσ' : Bang.CalcVM.SStore) (dτ' : Bang.CalcVM.THeap) (dκ' : Bang.CalcVM.CStore),
        Bang.CalcVM.evalD f g dσ dτ dκ (substEnv γ M)
            = some (readbackTerm t, g', dσ', dτ', dκ')
          ∧ StoresCorr eσ' eτ' eκ' dσ' dτ' dκ' ∧ MTerm.WF t ∧ MTerm.WFClos t := by
  intro f γ M t ρ g g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ hag hWF hP hSc hHWF hG hC h
  obtain ⟨dσ', dτ', dκ', hd, hC', _, hWt, _⟩ :=
    evalE_agrees_evalD_gen f γ M (.mterm t) ρ g g' eσ eσ' eτ eτ' eκ eκ' dσ dτ dκ
      hag hWF hP hSc hHWF hG hC h
  obtain ⟨hWFt, hPt⟩ := hWt t rfl
  exact ⟨dσ', dτ', dκ', by simpa only [readbackTermS] using hd, hC', hWFt, hPt⟩

/-- **The correspondence STATEMENT** (PLFA `γ≈ₑσ`; slice-3 proof).

If `evalE` runs `M` under `ρ` to a returner `mret mv`, and `ρ` agrees with a substitution
`σ`, then the substitution reference `evalD` (over the σ-substituted term) returns the
read-back value. Generalized from the empty env to an arbitrary `ρ`/`σ` per PLFA's warning
(the induction won't fire on the empty-env special case).

This is the top-of-machine corollary of `evalE_agrees_evalD_effect`: a whole-program run
(EMPTY input stores on BOTH sides) that returns `mret mv` under an agreeing env `ρ`/`σ` maps,
under `substEnv γ`, to an `evalD` run returning `ret (readback mv)`.

**Store-pinning (ruling #1, task #11):** the input stores are pinned to `[] [] []` on the `evalE`
side (matching `evalD`'s `[] [] []`). The earlier form left the `evalE` stores ARBITRARY while pinning
`evalD` to empty with no correspondence premise — that is UNSOUND (`headline_refutation_witness` below:
an `evalE` state cell `evalD`'s empty store can't resolve makes `evalE` return where `evalD` raises).
The empty-store pinning discharges `StoresGood`/`StoresCorr` trivially, and the `MEnv.WF`/`MEnv.WFClos`/
`Comp.ScopedC`/`Comp.HandlerWF` premises are the elaboration-guaranteed well-formedness the `_effect`
correspondence needs. Then the result is `evalE_agrees_evalD_effect` at empty stores, with
`readbackTerm (mret mv) = term (ret (readback mv))`. -/
theorem evalE_agrees_evalD (f : Nat) (γ : List Val) (M : Comp) (mv : MVal) (ρ : MEnv) (g' : Nat)
    (eσ' : ESStore) (eτ' : ETHeap) (eκ' : ECStore)
    (hagree : EnvAgrees ρ γ) (hWF : MEnv.WF ρ) (hP : MEnv.WFClos ρ)
    (hSc : Comp.ScopedC γ.length M) (hHWF : Comp.HandlerWF γ.length M)
    (h : evalE f 0 [] [] [] ρ M = some (.mterm (.mret mv), g', eσ', eτ', eκ')) :
    ∃ g'' σ' τ' κ',
      Bang.CalcVM.evalD f 0 [] [] [] (substEnv γ M)
        = some (.term (.ret (readback mv)), g'', σ', τ', κ') := by
  obtain ⟨dσ', dτ', dκ', hd, _, _, _⟩ :=
    evalE_agrees_evalD_effect f γ M (.mret mv) ρ 0 g' [] eσ' [] eτ' [] eκ' [] [] []
      hagree hWF hP hSc hHWF
      ⟨fun p hp => (List.not_mem_nil hp).elim, fun p hp => (List.not_mem_nil hp).elim,
        fun p hp => (List.not_mem_nil hp).elim⟩
      ⟨rfl, rfl, rfl⟩ h
  exact ⟨g', dσ', dτ', dκ', by simpa only [readbackTerm] using hd⟩

/-- **REFUTATION WITNESS (envm3, 2026-07-10) — the headline is FALSE for arbitrary evalE input stores.**
The headline (:1715) binds `eσ eτ eκ` as ARBITRARY inputs on the `evalE` side while pinning the `evalD`
side to `[] [] []`, with NO store-correspondence premise. That is unsound: an `evalE` store can hold a
state cell whose identity `evalD`'s empty store cannot resolve, so `evalE` RETURNS where `evalD` RAISES.

Concretely: `M = perform (vvar 0) "get" ()`, `γ = [vcap 7 0]`, `ρ = mvcap 7 0 ∷ₑ nil`,
`eσ = [(7, mvunit)]`. All headline hypotheses hold (`EnvAgrees ρ γ` by `readbackEnv ρ = γ`), and
`evalE` reads the cell ⇒ `mret mvunit`; but `substEnv γ M = perform (vcap 7 0) "get" ()` over
`[] [] []` misses all three stores ⇒ `raised n "get" vunit`, never a `ret`. So the ∃ conclusion is
unsatisfiable. This is INDEPENDENT of the in-file `sorry` (it takes the headline as a hypothesis `H`). -/
theorem headline_refutation_witness
    (H : ∀ (f : Nat) (γ : List Val) (M : Comp) (mv : MVal)
          (eσ : ESStore) (eτ : ETHeap) (eκ : ECStore) (ρ : MEnv) (g' : Nat)
          (eσ' : ESStore) (eτ' : ETHeap) (eκ' : ECStore),
          EnvAgrees ρ γ →
          evalE f 0 eσ eτ eκ ρ M = some (.mterm (.mret mv), g', eσ', eτ', eκ') →
          ∃ F g'' σ' τ' κ',
            Bang.CalcVM.evalD F 0 [] [] [] (substEnv γ M)
              = some (.term (.ret (readback mv)), g'', σ', τ', κ')) : False := by
  have heval : evalE 8 0 [(7, .mvunit)] [] [] (MVal.mvcap 7 0 ∷ₑ .nil)
      (.perform (.vvar 0) "get" .vunit)
      = some (.mterm (.mret .mvunit), 0, [(7, .mvunit)], [], []) := by
    simp only [evalE, evalV, MEnv.get, ESStore.get?, List.find?, decide_true, if_true,
      Option.map_some]
  obtain ⟨F, g'', σ', τ', κ', hd⟩ :=
    H 8 [Val.vcap 7 0] (.perform (.vvar 0) "get" .vunit) .mvunit
      [(7, .mvunit)] [] [] (MVal.mvcap 7 0 ∷ₑ .nil) 0 [(7, .mvunit)] [] []
      rfl heval
  cases F with
  | zero => simp only [Bang.CalcVM.evalD, reduceCtorEq] at hd
  | succ F =>
      simp only [substEnv, Comp.subst, Comp.substFrom, Val.substFrom, if_true, gt_iff_lt,
        Bang.CalcVM.evalD, Bang.CalcVM.SStore.get?, Bang.CalcVM.THeap.get?, Bang.CalcVM.CStore.get?,
        List.find?, Option.map_none, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hd
      exact hd.1

/-- **REFUTATION WITNESS #2 (envm3, 2026-07-10) — `_effect`'s `MTerm.PureV` conclusion is FALSE.**
The frozen `evalE_agrees_evalD_effect` (and my `_gen` engine) conclude `MTerm.PureV t` of the terminal.
For a returner `mret mv` that is `MVal.PureV mv`, i.e. every closure `mv` reaches has an `EffectFree`
body. But `M = ret (vthunk N)` with an EFFECTFUL `N` evaluates to `mret (mvclos N ρ)`, and
`MVal.PureV (mvclos N ρ) = EffectFree N ∧ …` is FALSE. NOTHING in `_effect`'s premises (WF/PureV env,
`ScopedC`, `StoresGood`, `StoresCorr`) forbids that input — so the `MTerm.PureV` conclusion is
unprovable AS STATED.

Concretely `N = handle (throws 0) (ret ())` (effectful — `EffectFree (handle _ _) = False` — and CLOSED,
so `ScopedC 0 M` holds), `γ = []`, `ρ = nil`, all stores empty. All `_effect` premises hold; evalE
returns `mret (mvclos N nil)`; the claimed `MTerm.PureV` = `EffectFree N` = `False`. Machine-checked
from `_effect` taken as hypothesis H, independent of the in-file sorry. -/
theorem effect_pureV_refutation_witness
    (H : ∀ (f : Nat) (γ : List Val) (M : Comp) (t : MTerm) (ρ : MEnv) (g G g' : Nat)
          (eσ eσ' : ESStore) (eτ eτ' : ETHeap) (eκ eκ' : ECStore)
          (dσ : Bang.CalcVM.SStore) (dτ : Bang.CalcVM.THeap) (dκ : Bang.CalcVM.CStore),
          EnvAgrees ρ γ → MEnv.WF ρ → MEnv.PureV ρ → Comp.ScopedC γ.length M →
          StoresGood eσ eτ eκ → StoresCorr eσ eτ eκ dσ dτ dκ →
          evalE f g eσ eτ eκ ρ M = some (.mterm t, g', eσ', eτ', eκ') →
          ∃ (G' : Nat) (dσ' : Bang.CalcVM.SStore) (dτ' : Bang.CalcVM.THeap) (dκ' : Bang.CalcVM.CStore),
            Bang.CalcVM.evalD f G dσ dτ dκ (substEnv γ M)
                = some (readbackTerm t, G', dσ', dτ', dκ')
              ∧ StoresCorr eσ' eτ' eκ' dσ' dτ' dκ' ∧ MTerm.WF t ∧ MTerm.PureV t) : False := by
  have hEA : EnvAgrees (MEnv.nil) ([] : List Val) := rfl
  have hWFnil : MEnv.WF (MEnv.nil) := by
    intro v hv; simp only [readbackEnv] at hv; exact (List.not_mem_nil hv).elim
  have hPnil : MEnv.PureV (MEnv.nil) := by simp only [MEnv.PureV]
  have hSc : Comp.ScopedC ([] : List Val).length
      (.ret (.vthunk (.handle (.throws 0) (.ret .vunit)))) := by
    intro k _
    simp only [Comp.shiftFrom, Val.shiftFrom, Bang.Handler.shiftFrom]
  have hSG : StoresGood ([] : ESStore) ([] : ETHeap) ([] : ECStore) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro p hp <;> simp only [List.not_mem_nil] at hp
  have hSC : StoresCorr ([] : ESStore) ([] : ETHeap) ([] : ECStore)
      ([] : Bang.CalcVM.SStore) ([] : Bang.CalcVM.THeap) ([] : Bang.CalcVM.CStore) :=
    ⟨rfl, rfl, rfl⟩
  have heval : evalE 4 0 [] [] [] MEnv.nil (.ret (.vthunk (.handle (.throws 0) (.ret .vunit))))
      = some (.mterm (.mret (.mvclos (.handle (.throws 0) (.ret .vunit)) MEnv.nil)), 0, [], [], []) := rfl
  obtain ⟨G', dσ', dτ', dκ', _hd, _hC, _hWF, hPt⟩ :=
    H 4 [] (.ret (.vthunk (.handle (.throws 0) (.ret .vunit))))
      (.mret (.mvclos (.handle (.throws 0) (.ret .vunit)) MEnv.nil)) MEnv.nil 0 0 0
      [] [] [] [] [] [] [] [] [] hEA hWFnil hPnil hSc hSG hSC heval
  -- MTerm.PureV (mret (mvclos (handle …) nil)) = EffectFree (handle …) ∧ … = False ∧ …
  simp only [MTerm.PureV, MVal.PureV, EffectFree] at hPt
  exact hPt.1

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
