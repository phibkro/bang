module

-- `#guard Source.eval …` and the `capOccurs` evals run compiled code at the META phase, so the
-- instances they touch must be META-visible: `meta import` Semantics + Grade (as ReturnEscapeReach does).
meta import Bang.Core.Semantics
meta import Bang.Core.Grade
public import Bang.Core.Soundness
public import Bang.Core.Grade

/-! # ScopedCapWitness — the DISCRIMINATOR a scoped-cap type system must enforce (#134 post-v1).

These are the RUNNABLE witnesses backing `docs/notes/scoped-cap-types-design.md`. They pin, machine-
checkably, the one structural fact the whole design turns on:

  **the reachable cap-escape (ADR-0063) is a cap RETURNED (as a captured thunk) out of its handler;
  every corpus cap-use passes the cap DOWN and never returns it.**

That is exactly the "second-class capability" cut (Osvald/Rompf; Brachthäuser System C): caps may be
passed as arguments (down) but never returned/stored/thunked-out (up). This file gives the two poles of
that cut as build-checked terms, so the design note's central claim ("second-class rejects the escape and
keeps the corpus") is grounded on artifacts, not prose.

## The two poles

- `progEscape` — the ESCAPE (the ADR-0063 shape). A `state 1` handler RETURNS `ret (vthunk Mesc)` where
  `Mesc` captures the outer cap (`vvar 0`). The returned VALUE is a thunk that closes over a live `cap 1`
  — a cap escaping UPWARD. Behaviour: `.escapedCap` (fail-loud, ADR-0063). A scoped/second-class checker
  REJECTS `progEscape`.

- `progDown` — the CORPUS IDIOM (the `stage-swap`/`cap-param` shape). The handler body FORCES a thunk that
  performs on the handler-bound cap IN PLACE: `handle (force (thunk (perform (bound-cap) get))) with
  state`. The cap flows DOWN (into a forced-in-place computation), never up (never in the handler's answer
  value). Behaviour: `.done` (resolves). A second-class checker ACCEPTS `progDown`.

The structural predicate a checker enforces: **a handler's answer type must not carry a `cap` for the
label the handler binds** (`¬ capOccurs ℓ A`). `progEscape`'s answer thunk type carries `cap 1`;
`progDown`'s answer is `F 1 unit` (no `cap`). `capOccurs` SEPARATES them — that is the seal. -/

namespace Bang.ScopedCapWitness

open Bang
open Bang.EffectRow (Label EffRow)

/-- A `state`-style `EffSig` (label `1` has ops `get`/`put`, both `unit → unit`). Local copy of the
ReturnEscapeReach signature so this witness is self-contained. -/
@[reducible] def sigS : EffSig EffRow QTT where
  labelEff l := {l}
  opArg l op := if l = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  opRes l op := if l = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  labelEff_ne_bot l := Finset.singleton_ne_empty l
  labelEff_sep l l' φ h hne := by
    have hmem : l ∈ ({l'} : EffRow) ∪ φ := h (Finset.mem_singleton_self l)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hl | hφ
    · exact absurd (Finset.mem_singleton.1 hl) hne
    · exact hφ

attribute [local instance] sigS

/-! ## Pole 1 — the ESCAPE (`progEscape`, the ADR-0063 laundered-re-handle shape)

`progEscape = letC (handle (state 1) (ret (vthunk Mesc))) (force (vvar 0))`. The middle handler's answer
value is a THUNK `vthunk Mesc` whose body performs on the outer cap. That is a cap escaping UPWARD.
Behaviour = `.escapedCap` (ADR-0063 defined fail-loud). -/

/-- The captured-cap thunk body (in `[cap 1]`, `vvar 0` = the escaped outer cap): re-handle `state 1`,
then perform the outer cap with `get`. -/
def Mesc : Comp :=
  Comp.letC (Comp.ret (Val.vvar 0))
    (Comp.handle (Handler.state 1 Val.vunit) (Comp.perform (Val.vvar 1) "get" Val.vunit))

/-- The escape source: outer `state 1` binds the cap and RETURNS the laundered thunk; the outer `letC`
forces it AFTER the handler pops. -/
def progEscape : Comp :=
  Comp.letC (Comp.handle (Handler.state 1 Val.vunit) (Comp.ret (Val.vthunk Mesc)))
            (Comp.force (Val.vvar 0))

/-! The escape falls into the DEFINED capability-escape terminal (ADR-0063). Negative pole. -/
#guard (match Source.eval 300 progEscape with | .escapedCap => true | _ => false)

/-! ## Pole 2 — the CORPUS IDIOM (`progDown`, cap passed DOWN, performed in place)

The `stage-swap`/`cap-param` shape at the kernel level: bind the cap with a `state 1` handler, then FORCE
a thunk whose body performs on the handler-bound cap `vvar 0`. The cap is used INSIDE the handler's
dynamic extent — it never appears in the handler's returned value. This is what second-class PERMITS. -/

/-- `downBody` = `perform (vvar 0) "get" unit` — perform on the handler-bound cap, in place. -/
def downBody : Comp := Comp.perform (Val.vvar 0) "get" Val.vunit

/-- `progDown = handle (state 1) (force (vthunk downBody))`. The cap is performed on INSIDE the handler;
the answer is a plain `F 1 unit` — NO cap in the returned value. -/
def progDown : Comp :=
  Comp.handle (Handler.state 1 Val.vunit) (Comp.force (Val.vthunk downBody))

/-! The corpus cap idiom RESOLVES (`.done`). Positive pole. Cap used down, never returned. -/
#guard (match Source.eval 300 progDown with | .done _ => true | _ => false)

/-! ## The DISCRIMINATOR, stated structurally

`capOccurs ℓ A` — does the value type `A` mention `cap ℓ` (directly, or under a thunk/sum/prod/μ)? The
premise a scoped-cap / second-class checker adds to a handler binding label `ℓ` with answer type `A` is
`¬ capOccurs ℓ A`. It keys on the CAP former, not on the label-in-a-row (which the ADR-0063 laundering
defeats). -/

mutual
/-- Does value type `A` syntactically carry a `cap ℓ`? Descends thunk bodies, sums, products, μ. -/
def capOccurs (ℓ : Label) : VTy EffRow QTT → Bool
  | .cap ℓ' => ℓ = ℓ'
  | .U _ c => cCapOccurs ℓ c
  | .sum a b => capOccurs ℓ a || capOccurs ℓ b
  | .prod a b => capOccurs ℓ a || capOccurs ℓ b
  | .mu a => capOccurs ℓ a
  | _ => false
/-- Computation-type companion: does `C` carry a `cap ℓ` in its returned/argument value types? -/
def cCapOccurs (ℓ : Label) : CTy EffRow QTT → Bool
  | .F _ a => capOccurs ℓ a
  | .arr _ a c => capOccurs ℓ a || cCapOccurs ℓ c
end

/-! **THE SEAL, positive side.** ADR-0063's escape laundered label 1 out of the ROW (that is why the
answer-type B-occ, which keys on the LABEL, passes). Keying on the CAP former instead flags it: the
returned thunk's body still performs on the outer cap, so the answer a second-class checker inspects is a
cap-in-return-position `U _ (F 1 (cap 1))`. `capOccurs` FLAGS it where the label-keyed B-occ was blind —
exactly the gap ADR-0063 documented (B-occ guards the label, not the laundered cap). -/
#guard capOccurs 1 (VTy.U (⊥ : EffRow) (CTy.F 1 (VTy.cap 1))) = true

/-! **THE SEAL, negative side.** The corpus idiom's handler answer is `F 1 unit` — `capOccurs` does NOT
flag it. The discriminator SEPARATES escape (flagged) from corpus (clean). -/
#guard capOccurs 1 VTy.unit = false
#guard cCapOccurs 1 (CTy.F 1 VTy.unit) = false

/-! Reach through a returned PAIR — a cap hidden in a product is still flagged (the reach-capability gap
Xu/Boruch-Gruszecki's System Capless closes for generic containers). -/
#guard capOccurs 1 (VTy.U (⊥ : EffRow) (CTy.F 1 (VTy.prod VTy.int (VTy.cap 1)))) = true

/-! Per-label: a DIFFERENT handler's cap in the answer is not flagged for `ℓ = 1` (matching
dispatch-by-identity being per-handler-instance — the discipline is per-label). -/
#guard capOccurs 1 (VTy.U (⊥ : EffRow) (CTy.F 1 (VTy.cap 2))) = false

end Bang.ScopedCapWitness
