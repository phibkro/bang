module

public import Bang.Core.IR

/-!
  WgcCapCode.lean — the first bounded, theorem-visible slice extracted from the
  concrete WasmGC emitter.

  This is deliberately NOT a semantics for Wasm text and NOT the full `wgcexec`
  machine. It contains only the fixed prelude declarations used by the concrete
  emitter's state-capability lifetime runtime (`$liveTop`, `$nextId`, `$capMint`,
  `$capExit`, `$capGate`) and a calculated Lean machine for those helper calls plus
  one mutable state cell. `Bang.Backend.WasmEmit` renders `scalarCapCode` directly,
  so extracting this slice does not change emitted bytes.

  The scope is intentionally strong enough to expose the issue-134 kill shot and
  no stronger:

  * a live state cell can be read and updated;
  * the scalar watermark rejects an immediately escaped state cap;
  * after a later handler mints a fresh id, the scalar watermark revives the old
    id, while exact live-id membership still rejects it.

  Therefore `id < liveTop` is NOT equivalent to `splitAtId K id ≠ none` in general.
  No theorem in this module claims closure adequacy, handler adequacy, a connection
  to `Source.eval`, or official Wasm semantics.
-/

namespace Bang.WgcCapCode

@[expose] public section

/-! ## Mechanical code extraction: the exact fixed helper text -/

/-- The smallest instruction vocabulary extracted from `gcHelpers`: declarations
for the scalar watermark and its three helper functions. -/
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
      "  (global $liveTop (mut i64) (i64.const 0))\n" ++
      "  (global $nextId  (mut i64) (i64.const 0))\n"
  | .mint =>
      "  (func $capMint (result i64) (local $m i64)\n" ++
      "    (local.set $m (global.get $nextId))\n" ++
      "    (global.set $nextId (i64.add (global.get $nextId) (i64.const 1)))\n" ++
      "    (global.set $liveTop (global.get $nextId))\n" ++
      "    (local.get $m))\n"
  | .exit =>
      "  (func $capExit (param $m i64) (global.set $liveTop (local.get $m)))\n"
  | .gate =>
      "  (func $capGate (param $id i64)\n" ++
      "    (if (i64.ge_s (local.get $id) (global.get $liveTop)) (then (unreachable))))\n"

def render (code : Code) : String :=
  code.foldl (fun out instr => out ++ renderInstr instr) ""

/-- The extracted code used by the current concrete emitter. -/
def scalarCapCode : Code := [.globals, .mint, .exit, .gate]

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

/-- Image of `$capGate`: the concrete helper allows the operation iff `id < liveTop`. -/
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

/-- Pop a well-bracketed live frame. A mismatched exit is rejected rather than
silently manufacturing a live set. -/
def exactExit (id : Nat) (s : ExactState) : Option ExactState :=
  match s.live with
  | top :: rest =>
      if top = id then some { s with live := rest } else none
  | [] => none

def exactGate (id : Nat) (s : ExactState) : Bool :=
  s.live.contains id

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
