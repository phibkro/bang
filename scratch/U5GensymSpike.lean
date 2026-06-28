/-
U5 GENSYM-ALIGNMENT SPIKE (inc-6, the WASM-hop re-derivation) — refute-first de-risk.

Question under test (PATH §U5 design-first check b, the U2 refute-watch analog):
  does `wexec`'s new gensym `g` start/thread to MATCH `exec`'s minted handler ids,
  so that the route-B WASM machine simulates the route-B CalcVM `exec` in LOCKSTEP
  under `injHStack`?

The worry would be a NUMERIC alignment puzzle (the WASM mint counter drifting from
the CalcVM one). The spike answers it BUILD-GROUNDED on the HARDEST arm: HANDLE,
where the mint happens. We reuse the REAL route-B `CalcVM.exec`/`compile`/`Instr`/
`HFrame` (green at this sha) and define the route-B WASM machine as the 5-step plan
prescribes, then prove the HANDLE arm of `exec_wexec_sim_ok` re-keyed with `g`.

SPIKE scope: prove nil / RET / HANDLE / UNMARK (enough to exercise the IH through a
mint+pop). Other arms are `sorry` (this is a theorem-body spike, NOT the full grind).
Value rep is the IDENTITY injection (WStack = CalcVM.Stack) to strip compileV noise —
the gensym question is about HSTACK IDS, not value lowering.
-/
import Bang.CalcVM

namespace Bang.U5Spike
open Bang
open Bang.CalcVM

/-- route-B WASM instruction stream — mirror of `CalcVM.Instr`, with the handler
boundary DEFERRED (`wHANDLE` carries raw `(Handler, Comp, CalcVM.Code)`, mirroring
`bindS`), and `wOP`/`wTHROW` IDENTITY-keyed (`Nat`, not label). -/
inductive WInstr where
  | wRET    : Val → WInstr
  | wLAMI   : Comp → WInstr
  | wSUBST  : Comp → CalcVM.Code → WInstr
  | wAPP    : Val → CalcVM.Code → WInstr
  | wHANDLE : Handler → Comp → CalcVM.Code → WInstr   -- DEFER: mint id + recompile at exec
  | wUNMARK : WInstr
  | wTHROW  : Nat → Bang.OpId → Val → WInstr
  | wOP     : Nat → Bang.OpId → Val → WInstr
  | wCASE   : Val → Comp → Comp → CalcVM.Code → WInstr
  | wSPLIT  : Val → Comp → CalcVM.Code → WInstr
  deriving Inhabited

abbrev WCode := List WInstr
/-- Identity value rep for the spike (isolates the gensym/id question). -/
abbrev WStack := CalcVM.Stack

/-- route-B WASM handler frame — gains `id` (the mint), mirroring `CalcVM.HFrame`. -/
structure WHFrame where
  id         : Nat
  handler    : Handler
  savedCode  : WCode
  savedStack : WStack

abbrev WHStack := List WHFrame

/-- Step 1+4 of the 5-step plan: lower a route-B `CalcVM.Instr`+continuation. The
HANDLE arm DEFERS (carries the raw `h M` + the CalcVM continuation `c`), subsuming
the tail exactly as `bindS`/`SUBST`. -/
def lowerInstr (i : CalcVM.Instr) (c : CalcVM.Code) (rest : WCode) : WCode :=
  match i with
  | .RET v        => .wRET v :: rest
  | .LAMI M       => .wLAMI M :: rest
  | .SUBST N      => [.wSUBST N c]
  | .APP v        => [.wAPP v c]
  | .HANDLE h M   => [.wHANDLE h M c]              -- DEFER (subsumes tail; mirrors bindS)
  | .UNMARK       => .wUNMARK :: rest
  | .THROW n op v => .wTHROW n op v :: rest
  | .OP n op v    => .wOP n op v :: rest
  | .CASE w N₁ N₂ => [.wCASE w N₁ N₂ c]
  | .SPLIT w N    => [.wSPLIT w N c]

def lowerCode : CalcVM.Code → WCode
  | []     => []
  | i :: c => lowerInstr i c (lowerCode c)

/-- Step 2+3 of the plan: `wexec` gains the gensym `g`; the wHANDLE arm MINTS `id := g`
and RE-COMPILES the substituted body at `g+1`, pushing the frame keyed by `g` —
mirroring `CalcVM.exec`'s HANDLE arm EXACTLY (same mint, same `g+1`). -/
def wexec : Nat → Nat → WCode → WStack → WHStack → Option WStack
  | 0,          _, _,                  _, _  => none
  | Nat.succ _, _, [],                 s, _  => some s
  | Nat.succ f, g, .wRET v :: c,       s, hs => wexec f g c (.ret v :: s) hs
  | Nat.succ f, g, .wLAMI M :: c,      s, hs => wexec f g c (.lam M :: s) hs
  | Nat.succ f, g, .wSUBST N cc :: _,  s, hs =>
      match s with
      | .ret v :: s' => wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) cc)) s' hs
      | _            => none
  | Nat.succ f, g, .wAPP v cc :: _,    s, hs =>
      match s with
      | .lam N :: s' => wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) cc)) s' hs
      | _            => none
  -- ★ THE SPIKE TARGET — gensym mint, mirroring exec's HANDLE arm:
  | Nat.succ f, g, .wHANDLE h M cc :: _, s, hs =>
      let id := g
      wexec f (g+1)
        (lowerCode (CalcVM.compile (Comp.subst (.vcap id h.label) M) (CalcVM.Instr.UNMARK :: cc))) s
        ({ id := id, handler := h, savedCode := lowerCode cc, savedStack := s } :: hs)
  | Nat.succ f, g, .wUNMARK :: c,      s, hs =>
      match hs with
      | _ :: hs' => wexec f g c s hs'
      | []       => none
  | Nat.succ _, _, .wTHROW _ _ _ :: _, _, _  => none   -- (other arms: spike `sorry`s the proof, defs total)
  | Nat.succ _, _, .wOP _ _ _ :: _,    _, _  => none
  | Nat.succ _, _, .wCASE _ _ _ _ :: _, _, _ => none
  | Nat.succ _, _, .wSPLIT _ _ _ :: _,  _, _ => none

/-- Identity value injection; the HSTACK injection carries `fr.id` (step 4) and lowers
the saved code. THIS is the relating invariant the gensym alignment turns on. -/
def injHFrame (fr : CalcVM.HFrame) : WHFrame :=
  { id := fr.id, handler := fr.handler, savedCode := lowerCode fr.savedCode, savedStack := fr.savedStack }

def injHStack (hs : CalcVM.HStack) : WHStack := hs.map injHFrame

/-- ★ THE GENSYM-ALIGNMENT LOCKSTEP. Same `g` on both sides; the HANDLE arm is the
proof that the WASM mint threads identically to `exec`'s. Pure arms shown for the IH;
the effectful (OP/THROW/CASE/SPLIT/SUBST/APP/LAMI) arms are `sorry` — this is the
HANDLE-arm de-risk spike, not the full re-derivation. -/
theorem exec_wexec_sim_ok :
    ∀ (f g : Nat) (code : CalcVM.Code) (s s' : CalcVM.Stack) (hs : CalcVM.HStack),
      CalcVM.exec f g code s hs = some s' →
      wexec f g (lowerCode code) s (injHStack hs) = some s' := by
  intro f
  induction f with
  | zero => intro g code s s' hs h; simp [CalcVM.exec] at h
  | succ f ih =>
    intro g code s s' hs h
    cases code with
    | nil =>
        simp only [CalcVM.exec, Option.some.injEq] at h; subst h
        simp [lowerCode, wexec]
    | cons i c =>
        cases i with
        | RET v =>
            simp only [CalcVM.exec] at h
            simp only [lowerCode, lowerInstr, wexec]
            exact ih g c (.ret v :: s) s' hs h
        -- ★★ HANDLE: the mint. exec mints id:=g, recurses at g+1, pushes {id:=g,…}.
        -- wexec's wHANDLE arm does the IDENTICAL mint; injHStack of the pushed frame
        -- is DEFINITIONALLY the frame wexec pushes (injHFrame carries id := g). The IH
        -- at g+1 on the recompiled body closes — the SAME g threads both machines.
        | HANDLE hh M =>
            simp only [CalcVM.exec] at h
            simp only [lowerCode, lowerInstr, wexec]
            have key := ih (g+1)
              (CalcVM.compile (Comp.subst (.vcap g hh.label) M) (CalcVM.Instr.UNMARK :: c))
              s s' ({ id := g, handler := hh, savedCode := c, savedStack := s } :: hs) h
            simpa only [injHStack, injHFrame, List.map_cons] using key
        | UNMARK =>
            simp only [CalcVM.exec] at h
            cases hs with
            | nil => simp at h
            | cons fr hs' =>
                simp only [lowerCode, lowerInstr, wexec, injHStack, List.map_cons]
                exact ih g c s s' hs' h
        | LAMI M => sorry
        | SUBST N => sorry
        | APP v => sorry
        | THROW n op v => sorry
        | OP n op v => sorry
        | CASE w N₁ N₂ => sorry
        | SPLIT w N => sorry

end Bang.U5Spike
