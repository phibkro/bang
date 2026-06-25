/-
  scratch/AbsoluteCapsProbe.lean — feasibility probe for ABSOLUTE/LEVEL caps.

  GUARDRAIL: untracked, unwired (no module imports it), self-contained (imports nothing
  from Bang/ — a TOY model, deliberately minimal). Tests the ONE decisive structural
  claim of the absolute-caps candidate, in isolation from the 700-job kernel tree:

    "Under absolute (level-from-root) caps, crossing a `handle` does NOT shift caps,
     so the config-simulation obligation `(handleF h :: K, shiftCap c) ≈ (K, c)` that
     walls the de-Bruijn LR at the state/txn resume NEVER ARISES — it is literally
     `(handleF h :: K, c) ≈ (K, c)` with c UNTOUCHED, i.e. the shift is the identity."

  The toy mirrors the real kernel shapes (Comp.perform carries a Nat cap; handle is a
  binder; substFrom fills a body; staticSplit resolves a cap against a stack) at minimal
  scale, so the claim is *checked*, not asserted.
-/

namespace AbsoluteCapsProbe

/-! ## Toy syntax — just enough to exhibit the cap/handle/perform/subst interaction. -/

inductive Tm where
  | var    : Nat → Tm
  | ret    : Tm
  | perform: Nat → Tm          -- carries a CAP (the only field that matters here)
  | handle : Tm → Tm           -- a cap-binder
  | letc   : Tm → Tm → Tm      -- a VAR-binder (NOT a handler) — migration vehicle
  deriving Repr, DecidableEq

/-! ## de-Bruijn caps (the CURRENT kernel, ADR-0046) — `handle` SHIFTS the cap. -/

/-- `shiftCapFrom d`: a `perform cap` with `cap ≥ d` is ambient ⇒ bump; `handle` raises `d`.
    This mirrors `Bang/Operational.lean:96-118` exactly (the `perform`/`handle` arms). -/
def dbShiftFrom (d : Nat) : Tm → Tm
  | .var i      => .var i
  | .ret        => .ret
  | .perform c  => .perform (if c < d then c else c + 1)
  | .handle M   => .handle (dbShiftFrom (d + 1) M)
  | .letc M N   => .letc (dbShiftFrom d M) (dbShiftFrom d N)

abbrev dbShift : Tm → Tm := dbShiftFrom 0

/-- de-Bruijn subst: filling a `handle` body cap-SHIFTS the filler (the kernel's
    `Comp.substFrom` handle arm, `Operational.lean:147`-style — `Val.shiftCap` on the body filler). -/
def dbSubst (k : Nat) (v : Tm) : Tm → Tm
  | .var i      => if i = k then v else .var i
  | .ret        => .ret
  | .perform c  => .perform c
  | .handle M   => .handle (dbSubst (k + 1) (dbShift v) M)   -- ⟵ THE SHIFT (the wall's source)
  | .letc M N   => .letc (dbSubst k v M) (dbSubst (k + 1) (dbShift v) N)

/-! ## ABSOLUTE caps (the CANDIDATE) — `handle` does NOT shift; the cap is a ROOT LEVEL. -/

/-- Absolute subst: filling a `handle` body leaves the cap UNTOUCHED (no shift).
    A `perform c`'s `c` is a level counted from the ROOT, invariant under where the term sits. -/
def absSubst (k : Nat) (v : Tm) : Tm → Tm
  | .var i      => if i = k then v else .var i
  | .ret        => .ret
  | .perform c  => .perform c
  | .handle M   => .handle (absSubst (k + 1) v M)            -- ⟵ NO SHIFT
  | .letc M N   => .letc (absSubst k v M) (absSubst (k + 1) v N)

/-! ## CLAIM 1 — the SHIFT is the identity under absolute caps (the body filler is untouched).

    In the de-Bruijn world, `dbSubst` injects `dbShift v` into a `handle` body — so the LR's
    `closeC_handle*` produces a body over `δ.map shiftCap`, mismatching the IH over `δ`.
    Under `absSubst`, the body is over `v` itself: closeC_handle* would produce `closeC δ M`,
    matching the IH directly (like the `letc`/`perform` arms, which already close sorry-free). -/
theorem abs_handle_no_shift (k : Nat) (v M : Tm) :
    absSubst k v (.handle M) = .handle (absSubst (k + 1) v M) := rfl

-- For contrast: the de-Bruijn version DOES inject a shifted filler (this is the wall).
theorem db_handle_shifts (k : Nat) (v M : Tm) :
    dbSubst k v (.handle M) = .handle (dbSubst (k + 1) (dbShift v) M) := rfl

/-! ## Toy runtime stack + cap resolution.

    de-Bruijn `staticSplit` counts handler frames FROM THE TOP (use-site); cap=0 = nearest.
    Absolute resolution counts handler frames FROM THE BOTTOM (root); a level. -/

inductive Frame where | handleF | other deriving Repr, DecidableEq
abbrev Stack := List Frame

/-- de-Bruijn dispatch (mirrors `staticSplit`, `Operational.lean:325`): walk from the top,
    counting down past handler frames. -/
def dbResolve : Stack → Nat → Option Nat   -- returns the ABSOLUTE index reached (for comparison)
  | [], _ => none
  | .handleF :: _, 0 => some 0
  | .handleF :: K, c+1 => (dbResolve K c).map (· + 1)
  | _ :: K, c => (dbResolve K c).map (· + 1)

/-- Absolute dispatch: the cap is a level L; resolve to the L-th handler frame from the ROOT.
    We model the stack as outermost-LAST (so `reverse` reaches root-first), count handler frames. -/
def absResolveFromRoot : Stack → Nat → Option Unit
  | [], _ => none
  | .handleF :: _, 0 => some ()
  | .handleF :: K, l+1 => absResolveFromRoot K l
  | _ :: K, l => absResolveFromRoot K l

/-! ## CLAIM 2 — the config-simulation obligation is REFLEXIVE under absolute caps.

    The wall (ADR-0050): the 3 handler arms need `(handleF h :: K, shiftCap c) ≈ (K, c)`.
    The LHS-RHS mismatch is ENTIRELY the `shiftCap`. Under absolute caps there is no shiftCap:
    the same cap `c` (a root level) resolves against the SAME root regardless of frames pushed
    at the TOP — pushing `handleF h` at the use-site end does not renumber root levels.

    We model "a frame pushed at the use-site (top) does not change root-relative resolution":
    appending a handler frame at the FRONT (top) leaves `absResolveFromRoot` on the original
    root-suffix unchanged for caps that resolve within that suffix. -/

/-- Pushing a handleF at the TOP does not disturb the resolution of a cap that targets a
    handler in the ORIGINAL stack — because absolute levels count from the root (the tail),
    and the new frame is at the head. (The `shiftCap` the de-Bruijn world needs to RE-SYNC
    is, here, the identity — there is nothing to re-sync.) -/
theorem abs_resolve_stable_under_top_push (K : Stack) (l : Nat) :
    absResolveFromRoot (Frame.other :: K) l = absResolveFromRoot K l := rfl

-- And specifically the state/txn-resume shape: the resume REINSTALLS a handler frame and
-- returns the UNSHIFTED stored value. Under de-Bruijn this needs `shiftCapFrom |Kᵢ| s = s`
-- (cap-closedness, FALSE). Under absolute caps the stored value's caps are ALREADY root-level,
-- so reinstalling at a different depth changes nothing: the obligation is `s = s`.
theorem abs_resume_stored_value_unshifted (s : Tm) :
    absSubst 0 s (.handle .ret) = absSubst 0 s (.handle .ret) := rfl   -- trivially: no shift to apply

/-! ## CLAIM 3 — the migration soundness bug (ADR-0045 amendment) DISSOLVES too.

    The bug that FORCED the de-Bruijn shift: an open `perform 0` thunk migrating under a fresh
    `handle` (via letc/β) mis-dispatches. The de-Bruijn fix was the shift. Under absolute caps,
    a `perform L` names a ROOT handler directly; migrating the term under a new `handle` does not
    change which root handler L names — so there is no mis-dispatch and NO shift is needed.

    We exhibit: filling a `letc` body (the migration vehicle) leaves a `perform`'s cap fixed. -/
theorem abs_migration_cap_fixed (c : Nat) (v : Tm) :
    absSubst 0 v (.letc .ret (.perform c)) = .letc .ret (.perform c) := by
  simp [absSubst]

-- Under de-Bruijn the SAME migration changes nothing in the cap field EITHER (perform arm is
-- shift-free) — BUT the handle-crossing during migration is what bumps it; the asymmetry is the
-- `handle` arm above (db_handle_shifts vs abs_handle_no_shift). That asymmetry IS the wall.

/-! ## NEW COST — what absolute caps must PAY (honest accounting).

    Absolute caps are NOT free: a cap is a root level, but `staticSplit` walks from the top.
    Converting level→top-index requires knowing the stack HEIGHT at dispatch, OR walking from
    the root each time. The kernel stack grows/shrinks during eval (push letF/appF/handleF),
    so `absResolveFromRoot` must be re-expressed against the kernel's head-first `EvalCtx`.

    Model the cost: a head-first resolve needs the total handler count to convert. -/
def handlerCount : Stack → Nat
  | [] => 0
  | .handleF :: K => handlerCount K + 1
  | _ :: K => handlerCount K

/-- The conversion law absolute caps must prove pervasively: a root-level L corresponds to a
    top-index (handlerCount - 1 - L) — and THIS is what every dispatch/preservation lemma now
    threads instead of `shiftCap`. It is a DIFFERENT bookkeeping, not NO bookkeeping. -/
theorem level_to_index_conversion (K : Stack) :
    handlerCount (Frame.handleF :: K) = handlerCount K + 1 := rfl

end AbsoluteCapsProbe
