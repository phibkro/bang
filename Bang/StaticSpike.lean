/-
SPIKE (task #13) — does a STATIC-LINK dispatch dissolve / relocate / or still need
typing for the ADR-0043 resume-through-a-wrap edge?

This is a SCRATCH model, NOT a kernel rewrite. It models the minimal static-link
dispatch shape (Effekt capability-passing / Lexa lexical resolution): a `perform`
carries a CAPABILITY identifying its handler frame DIRECTLY — dispatch goes to that
frame with NO outward search that walks PAST non-matching handlers.

The decisive question (build-grounded below): under static dispatch, does the
captured continuation `Kᵢ` (up to the directly-found handler) still contain a
NON-catching `handleF` whose answer type must be recovered — i.e. does the
`krelS_splitAt_decomp` handleF-MISS obstruction still arise?

We reuse the REAL kernel `Frame`/`Handler`/`EvalCtx` (Operational.lean) so the
model rides the actual defs, not a toy.
-/
import Bang.Operational

namespace Bang.StaticSpike

open Bang

/-! ## The dynamic search, recalled

`Bang.splitAt` (Operational:255) walks the stack testing each `handleF h` with
`handlesOp h ℓ op`. Its `:259` branch — `handlesOp h = false` ⇒ recurse, PREPEND
this non-catching `handleF h` to the inner prefix `Kᵢ` — is *exactly* the source
of the edge: it can put a non-catching `handleF` INSIDE `Kᵢ`. -/

/-- A CAPABILITY is a static link: a de-Bruijn-style count of how many `handleF`
frames sit between the `perform` site and ITS handler. A `perform` carries this;
it is fixed by elaboration (lexical resolution), never recomputed at runtime. -/
abbrev Cap := Nat

/-- STATIC dispatch: walk OUT `cap`-many `handleF` frames; the (cap+1)-th `handleF`
IS the handler — taken WITHOUT testing whether intervening handlers "match", because
the capability already named it. Non-`handleF` frames (letF/appF) are part of the
captured continuation and are skipped transparently (they are pure plumbing, not
dispatch candidates). Returns `(Kᵢ, h, Kₒ)` exactly like `splitAt`. -/
def staticSplit : EvalCtx → Cap → Option (EvalCtx × Handler × EvalCtx)
  | [], _ => none
  | (.handleF h :: K), 0 => some ([], h, K)              -- THIS handler: cap exhausted, take it
  | (.handleF h :: K), (c+1) =>                          -- skip one handler frame (cap counts down)
      (staticSplit K c).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ))
  | (fr :: K), c =>                                      -- non-handler frame: transparent, keep walking
      (staticSplit K c).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-! ## The decisive observation, MODELED and BUILD-GROUNDED

The dynamic edge is: `Kᵢ` (captured continuation up to the catcher) contains a
`handleF` frame whose answer type must be recovered. Under STATIC dispatch with
cap = 0 (the COMMON case: a perform resolves to its NEAREST enclosing handler,
which is what well-scoped capability-passing produces when handlers don't shadow),
`staticSplit K 0` takes the FIRST `handleF` it reaches.

Claim A (cap=0): the captured continuation `Kᵢ` returned by `staticSplit K 0`
contains NO `handleF` frame. (It is all letF/appF plumbing.) This is the structural
fact that makes the strip trivial — there is no nested non-catching handler to
strip, so no answer type to recover. -/

/-- A stack contains no `handleF` frame. -/
def NoHandleF : EvalCtx → Prop
  | [] => True
  | (.handleF _ :: _) => False
  | (_ :: K) => NoHandleF K

/-- **Claim A — BUILD-GROUNDED.** Under static dispatch to the NEAREST handler
(cap = 0), the captured inner continuation is handler-free: the strip never meets a
nested `handleF`. This is the static analogue of the obstruction's premise — and it
holds STRUCTURALLY, with no answer-type recovery. -/
theorem staticSplit_zero_inner_noHandleF :
    ∀ (K : EvalCtx) (Kᵢ Kₒ : EvalCtx) (h : Handler),
      staticSplit K 0 = some (Kᵢ, h, Kₒ) → NoHandleF Kᵢ := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hsp; simp [staticSplit] at hsp
  | cons fr K ih =>
      intro Kᵢ Kₒ h hsp
      cases fr with
      | handleF h' =>
          -- cap 0 at a handleF: take it, Kᵢ = [].
          simp only [staticSplit, Option.some.injEq, Prod.mk.injEq] at hsp
          obtain ⟨rfl, _, _⟩ := hsp
          exact True.intro
      | letF N =>
          simp only [staticSplit, Option.map_eq_some_iff] at hsp
          obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact ih Ki' Ko' hh hsp'
      | appF w =>
          simp only [staticSplit, Option.map_eq_some_iff] at hsp
          obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact ih Ki' Ko' hh hsp'

/-! ## The relocation, MODELED and BUILD-GROUNDED

For cap > 0 the capability deliberately reaches PAST `cap`-many enclosing handlers
(shadowing / resuming-into-an-outer-handler). Then `Kᵢ` DOES contain `handleF`
frames again — `staticSplit_succ_inner` below — so the SAME structural shape (a
non-catching `handleF` inside the captured continuation) reappears. The difference
from dynamic: WHICH handler is skipped is fixed STATICALLY by the cap, not decided
by a runtime `handlesOp` test.

This is the precise sense in which the edge RELOCATES rather than DISSOLVES in
general: it dissolves for cap=0 (nearest), and for cap>0 it becomes a count-driven
strip whose answer type is recoverable FROM THE CAP (each skipped handler's hole
type is a static, known quantity) — which is exactly the "typed makes it dissolve"
finding: the cap is a typed/static witness of the intermediate answer type. -/

/-- For cap = c+1 the inner prefix is `handleF h :: (inner of cap c)`: a non-catching
handler IS captured. The strip reappears — but indexed by the (static) cap. -/
theorem staticSplit_succ_inner {h : Handler} {K Kᵢ Kₒ : EvalCtx} {h' : Handler} {c : Nat}
    (hsp : staticSplit (Frame.handleF h :: K) (c+1) = some (Kᵢ, h', Kₒ)) :
    ∃ Kᵢ', Kᵢ = Frame.handleF h :: Kᵢ' ∧ staticSplit K c = some (Kᵢ', h', Kₒ) := by
  simp only [staticSplit, Option.map_eq_some_iff] at hsp
  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨Ki', rfl, hsp'⟩

end Bang.StaticSpike
