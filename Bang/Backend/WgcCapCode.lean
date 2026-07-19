module

public import Bang.Core.IR

/-!
  WgcCapCode.lean — the first bounded, theorem-visible slice extracted from the
  concrete WasmGC emitter.

  This is deliberately NOT a semantics for Wasm text and NOT the full `wgcexec`
  machine. It contains only the fixed prelude declarations used by the concrete
  emitter's state-capability lifetime runtime (`$liveCaps`, `$nextId`, `$capMint`,
  `$capExit`, `$capGate`) and a calculated Lean machine for those helper calls plus
  one mutable state cell. `Bang.Backend.WasmEmit` renders `exactCapCode` directly;
  the retained scalar machine is only the refuted predecessor/counterexample.

  The scope is intentionally strong enough to expose the issue-134 kill shot and
  no stronger:

  * a live state cell can be read and updated;
  * the superseded scalar watermark rejects an immediately escaped state cap;
  * after a later handler mints a fresh id, that scalar watermark revives the old
    id, while the emitted exact live stack still rejects it;
  * an exit pops through its named frame, cleaning newer frames whose normal exits
    were skipped by exception/transaction unwinding.

  Therefore `id < liveTop` is NOT equivalent to `splitAtId K id ≠ none` in general.
  No theorem in this module claims closure adequacy, handler adequacy, a connection
  to `Source.eval`, or official Wasm semantics.
-/

namespace Bang.WgcCapCode

@[expose] public section

/-! ## Mechanical code extraction: the exact fixed helper text -/

/-- The live-stack node joins the emitter's recursive GC type group. The node is
not a source value: it is private runtime metadata linking a minted id to the
previous live handler frame. -/
def capFrameType : String :=
  "    (type $capframe (struct (field $id i64) (field $prev (ref null $capframe))))\n"

/-- The smallest instruction vocabulary extracted from `gcHelpers`: declarations
for exact live membership and its three ABI-frozen helper functions. -/
inductive Instr where
  | globals
  | mint
  | exit
  | gate
  deriving Repr, DecidableEq, Inhabited

abbrev Code := List Instr

/-- Per-instruction text image. These templates are the byte-for-byte strings that
previously lived inline at the head of `WasmEmit.gcHelpers`. -/
def renderInstr : Instr → String
  | .globals =>
      "  (global $liveCaps (mut (ref null $capframe)) (ref.null $capframe))\n" ++
      "  (global $nextId  (mut i64) (i64.const 0))\n"
  | .mint =>
      "  (func $capMint (result i64) (local $m i64)\n" ++
      "    (local.set $m (global.get $nextId))\n" ++
      "    (global.set $nextId (i64.add (global.get $nextId) (i64.const 1)))\n" ++
      "    (global.set $liveCaps (struct.new $capframe (local.get $m) (global.get $liveCaps)))\n" ++
      "    (local.get $m))\n"
  | .exit =>
      "  (func $capExit (param $m i64) (local $p (ref null $capframe))\n" ++
      "    (local.set $p (global.get $liveCaps))\n" ++
      "    (block $missing (loop $search\n" ++
      "      (br_if $missing (ref.is_null (local.get $p)))\n" ++
      "      (if (i64.eq (struct.get $capframe $id (ref.cast (ref $capframe) (local.get $p))) (local.get $m))\n" ++
      "        (then\n" ++
      "          (global.set $liveCaps (struct.get $capframe $prev (ref.cast (ref $capframe) (local.get $p))))\n" ++
      "          (return)))\n" ++
      "      (local.set $p (struct.get $capframe $prev (ref.cast (ref $capframe) (local.get $p))))\n" ++
      "      (br $search)))\n" ++
      "    (unreachable))\n"
  | .gate =>
      "  (func $capGate (param $id i64) (local $p (ref null $capframe))\n" ++
      "    (local.set $p (global.get $liveCaps))\n" ++
      "    (block $missing (loop $search\n" ++
      "      (br_if $missing (ref.is_null (local.get $p)))\n" ++
      "      (if (i64.eq (struct.get $capframe $id (ref.cast (ref $capframe) (local.get $p))) (local.get $id))\n" ++
      "        (then (return)))\n" ++
      "      (local.set $p (struct.get $capframe $prev (ref.cast (ref $capframe) (local.get $p))))\n" ++
      "      (br $search)))\n" ++
      "    (unreachable))\n"

def render (code : Code) : String :=
  code.foldl (fun out instr => out ++ renderInstr instr) ""

/-- The extracted code used by the current concrete emitter. -/
def exactCapCode : Code := [.globals, .mint, .exit, .gate]

/-! ## Calculated scalar helper machine -/

/-- Lean image of the two scalar Wasm globals. Natural numbers deliberately scope
this tracer below i64 overflow; the concrete witnesses mint only ids 0 and 1. -/
structure ScalarState where
  nextId : Nat := 0
  liveTop : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Image of `$capMint`: return the old globally-fresh id, advance the counter, and
raise the scalar high-water mark to the new counter. -/
def scalarMint (s : ScalarState) : Nat × ScalarState :=
  (s.nextId, { nextId := s.nextId + 1, liveTop := s.nextId + 1 })

/-- Image of `$capExit`: restore the scalar mark to this frame's minted id. -/
def scalarExit (id : Nat) (s : ScalarState) : ScalarState :=
  { s with liveTop := id }

/-- Image of the superseded scalar `$capGate`: allow iff `id < liveTop`. -/
def scalarGate (id : Nat) (s : ScalarState) : Bool :=
  id < s.liveTop

/-! ## Exact live-frame reference for this slice -/

/-- The reference lifetime state retains exact live identities, innermost first.
This is the finite-list image of asking whether `splitAtId K id` finds a frame. -/
structure ExactState where
  nextId : Nat := 0
  live : List Nat := []
  deriving Repr, DecidableEq, Inhabited

def exactMint (s : ExactState) : Nat × ExactState :=
  (s.nextId, { nextId := s.nextId + 1, live := s.nextId :: s.live })

/-- Remove `id` and every newer frame above it. This is deliberately pop-through,
not strict-pop: Wasm exception unwinding can skip an inner handler's normal
`$capExit`, while the enclosing exit must invalidate all lifetimes it leaves.
An absent id is rejected rather than silently manufacturing a live set. -/
def popThrough (id : Nat) : List Nat → Option (List Nat)
  | [] => none
  | top :: rest => if top = id then some rest else popThrough id rest

def exactExit (id : Nat) (s : ExactState) : Option ExactState :=
  (popThrough id s.live).map fun live => { s with live }

def exactGate (id : Nat) (s : ExactState) : Bool :=
  s.live.contains id

/-- Executable result of the emitted helper-level gate model. `trap` is the
bounded image of the helper's `unreachable`, not a theorem about Wasm traps. -/
inductive GateResult where
  | return
  | trap
  deriving Repr, DecidableEq, Inhabited

def runExactGate (id : Nat) (s : ExactState) : GateResult :=
  if exactGate id s then .return else .trap

/-! ## The smallest pure-result + mutable-state observations -/

structure StateBox where
  capId : Nat
  value : Int
  deriving Repr, DecidableEq, Inhabited

def scalarGet (s : ScalarState) (box : StateBox) : Option Int :=
  if scalarGate box.capId s then some box.value else none

def scalarPut (s : ScalarState) (box : StateBox) (value : Int) : Option StateBox :=
  if scalarGate box.capId s then some { box with value } else none

def exactGet (s : ExactState) (box : StateBox) : Option Int :=
  if exactGate box.capId s then some box.value else none

def exactPut (s : ExactState) (box : StateBox) (value : Int) : Option StateBox :=
  if exactGate box.capId s then some { box with value } else none

/-! ## Axiom-clean boundary theorems and the stale-reentry refutation -/

/-- Product preflight trace: an inner frame's normal exit is skipped, then the
middle frame exits. Pop-through removes both middle and inner while preserving
the older outer frame. This theorem fixes `$capExit`'s intended behavior before
the rendered helper is considered. -/
theorem exact_exit_pops_through_skipped_inner :
    let (outerId, outerLive) := exactMint {}
    let (middleId, middleLive) := exactMint outerLive
    let (_, innerLive) := exactMint middleLive
    exactExit middleId innerLive =
      some { nextId := 3, live := [outerId] } := by
  decide

/-- At the executable helper boundary, the gate returns exactly for list
membership. This does not interpret the rendered WAT or claim compiler adequacy. -/
theorem runExactGate_eq_live_membership (id : Nat) (s : ExactState) :
    runExactGate id s = if s.live.contains id then .return else .trap := by
  rfl

/-- Both models read a live state box. This is the positive floor, scoped only to
one freshly minted frame and one state cell. -/
theorem live_state_get_agrees :
    let (scalarId, scalar) := scalarMint {}
    let (exactId, exact) := exactMint {}
    scalarId = exactId ∧
      scalarGet scalar ⟨scalarId, 7⟩ = some 7 ∧
      exactGet exact ⟨exactId, 7⟩ = some 7 := by
  decide

/-- Both models update and read a live state box. -/
theorem live_state_put_get_agrees :
    let (scalarId, scalar) := scalarMint {}
    let (exactId, exact) := exactMint {}
    (scalarPut scalar ⟨scalarId, 7⟩ 9).bind (scalarGet scalar) = some 9 ∧
      (exactPut exact ⟨exactId, 7⟩ 9).bind (exactGet exact) = some 9 := by
  decide

/-- The scalar helper correctly rejects the original issue-134 shape when no later
handler has raised the watermark. -/
theorem scalar_rejects_immediate_escape :
    let (id, live) := scalarMint {}
    scalarGet (scalarExit id live) ⟨id, 7⟩ = none := by
  decide

/-- Exact live-frame membership also rejects the immediate escape. -/
theorem exact_rejects_immediate_escape :
    let (id, live) := exactMint {}
    (exactExit id live).bind (fun exited => exactGet exited ⟨id, 7⟩) = none := by
  decide

/-- The minimal stale-cap re-entry trace: mint state cap 0, pop it, mint a new
handler at id 1, then read the old box. The concrete scalar helper returns `7`.
This theorem is a refutation witness, not an adequacy claim. -/
theorem scalar_revives_stale_cap_after_reentry :
    let (oldId, firstLive) := scalarMint {}
    let afterExit := scalarExit oldId firstLive
    let (_, secondLive) := scalarMint afterExit
    scalarGet secondLive ⟨oldId, 7⟩ = some 7 := by
  decide

/-- The same well-bracketed trace under exact live-frame membership rejects the old
box. Together with `scalar_revives_stale_cap_after_reentry`, this disproves the
general `$liveTop ≡ splitAtId` equivalence assumed by the early-bank plan. -/
theorem exact_rejects_stale_cap_after_reentry :
    let (oldId, firstLive) := exactMint {}
    (exactExit oldId firstLive).bind (fun afterExit =>
      let (_, secondLive) := exactMint afterExit
      exactGet secondLive ⟨oldId, 7⟩) = none := by
  decide

end -- public section

/-! House witness gate: these bounded theorems must remain axiom-free. They are not
enrolled as `Bang/Audit.lean` headlines because none states general compiler adequacy. Each
`#guard_msgs` turns the observational axiom report into a build failure on dependency drift. -/
/-- info: 'Bang.WgcCapCode.live_state_get_agrees' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.live_state_get_agrees
/-- info: 'Bang.WgcCapCode.exact_exit_pops_through_skipped_inner' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.exact_exit_pops_through_skipped_inner
/-- info: 'Bang.WgcCapCode.runExactGate_eq_live_membership' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.runExactGate_eq_live_membership
/-- info: 'Bang.WgcCapCode.live_state_put_get_agrees' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.live_state_put_get_agrees
/-- info: 'Bang.WgcCapCode.scalar_rejects_immediate_escape' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.scalar_rejects_immediate_escape
/-- info: 'Bang.WgcCapCode.exact_rejects_immediate_escape' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.exact_rejects_immediate_escape
/-- info: 'Bang.WgcCapCode.scalar_revives_stale_cap_after_reentry' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.scalar_revives_stale_cap_after_reentry
/-- info: 'Bang.WgcCapCode.exact_rejects_stale_cap_after_reentry' does not depend on any axioms -/
#guard_msgs in
#print axioms Bang.WgcCapCode.exact_rejects_stale_cap_after_reentry

end Bang.WgcCapCode
