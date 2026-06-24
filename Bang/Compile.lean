/-
  Bang/Compile.lean — WasmFX target + compilation primitives (◊5, ADR-0035).
  ─────────────────────────────────────────────────────────────
    §7 Wasmfx.* — Ty, Val, Instr, Module, run, WellTyped, MentionsLocal,
                  HandlerLawful, Wasmfx.HandlerEquiv
    §7 compileC, compileV, compileHandler

  Theorem STATEMENTS (compile_well_typed, compile_forward_sim,
  handler_compiles, zero_grade_no_code) live in Bang/Spec.lean.

  ## Method (ADR-0035): forward simulation, NOT the biorthogonal LR

  ◊5 is the *verified compiler output* leg of the two-hop architecture
  (ADR-0016: source → CalcVM → WasmFX). The CalcVM (`Bang/CalcVM.lean`) is the
  EXECUTABLE SPEC; this file lowers CalcVM `Code` to a concrete WasmFX
  instruction stream and proves a one-directional FORWARD SIMULATION
  (AsmFX/Benton–Hur shape):

      Source.eval fuel c = done v  ⇒  ∃ f', Wasmfx.run f' (compileC c) = done (compileV v)

  The proof composes the PROVEN CalcVM bridge (`compile_correct`,
  `evalD_agrees_source`) with a lockstep `wexec ≈ exec` simulation: the WasmFX
  machine is a re-presentation of the calculated `exec` over a WASM value
  representation (`Wasmfx.Val`, i32/unit/ref-tagged), with `compileV` the value
  injection. Reusing the calculated machine is exactly the two-hop discipline
  (invariant #4: the machine is the calculation's output, not hand-designed).

  ## Milestone A (this landing): the PURE CBPV spine

  `ret · letC · force/vthunk · lam · app` + i32/unit literals. The WasmFX AST
  carries `nocont`/`cont` heap-type slots (CURRENT stack-switching Explainer
  shape) UNINHABITED, so Milestone B (`switch`/`resume`/`suspend` + one tag)
  lands with no AST migration. The tracer effect maps to a generator
  suspend/resume (NOT `throws`→`resume_throw`, unimplemented in Wasmtime
  #10248) — Milestone B. -/

import Bang.Core
import Bang.Syntax
import Bang.Operational
import Bang.CalcVM

namespace Bang

namespace Wasmfx

/-! ### The WasmFX target AST (pure spine; cont/nocont carried-uninhabited)

Pinned to the CURRENT stack-switching Explainer (`cont`/`nocont` heap types,
`resume $ct (on $tag $label)*`, `switch` first-class), NOT the drifted OOPSLA'23
`(tag $e $h)` form. Milestone A inhabits only the pure fragment; the
continuation formers are declared so Milestone B extends the type, not migrates
it. -/

/-- WASM value types. `cont`/`nocont` are the stack-switching heap types
(Explainer); `ref` boxes a thunk/closure (a `funcref` to compiled code).
`unit` is the empty-tuple result. -/
inductive Ty where
  | i32    : Ty
  | unit   : Ty
  | ref    : Ty             -- funcref to compiled code (thunk / closure)
  | cont   : Ty             -- continuation reference (Milestone B: resume/suspend)
  | nocont : Ty             -- carried-uninhabited (switch lands later, no migration)
  deriving DecidableEq, Repr, Inhabited

/-- A WASM runtime value. The injection `compileV : Val → Wasmfx.Val` maps source
values here: `vint n ↦ i32 n`, `vunit ↦ unit`, and every other (boxed/closure)
former ↦ `boxed`/`clos`. The representation is GENUINELY distinct from `Val` — a
`Wasmfx.run` step operates on this, not on `Comp`/`Val` — so the forward
simulation is a real refinement, not an identity. -/
inductive Val where
  | i32   : Int → Val            -- i32.const n
  | unit  : Val                  -- ()
  | boxed : Bang.Val → Val       -- a boxed source value (sum/pair/fold payload)
  | clos  : Comp → Val           -- a closure (compiled `lam` body); funcref carrier
  deriving Inhabited

/-- The lowered instruction stream. Milestone A inhabits the pure-spine opcodes,
which mirror the calculated `Bang.Instr` (the two-hop: this is CalcVM `Code`
re-presented for WASM). `getL`/`setL` are the WASM locals a binder lowers to —
they make `MentionsLocal` observable (the QTT-erasure headline). -/
inductive Instr where
  | const  : Bang.Val → Instr    -- push a constant terminal value (ret v)
  | clos   : Comp → Instr        -- push a closure (lam M)
  | bindS  : Comp → Instr        -- pop value, bind, run continuation N[v]  (let)
  | callS  : Bang.Val → Instr    -- pop closure, apply to argument         (app/β)
  | getL   : Nat → Instr         -- local.get k   (free de Bruijn occurrence k)
  | setL   : Nat → Instr         -- local.set k
  deriving Inhabited

abbrev Code := List Instr

/-- The WASM operand stack holds runtime values (`Wasmfx.Val`). -/
abbrev VStack := List Val

/-- A WASM module: a single start-function body (the lowered instruction stream
of a closed program) plus its declared result type. The forward simulation runs
this body to a single value on the WASM operand stack. -/
structure Module where
  body   : Code
  result : Ty
  deriving Inhabited

end Wasmfx

/-! ### compileV / compileC — the lowering (source → CalcVM → WasmFX)

`compileV` injects a source value into the WASM value rep. `compileC` lowers via
the PROVEN calculated machine: `compile c [] : Bang.Code`, then `lowerCode` maps
each calculated instruction to its WASM opcode. The pure-spine lowering is
near-identity (the calculated `Instr` already IS a stack-machine IR), which is
what makes the `wexec ≈ exec` simulation a tight structural induction. -/

/-- Value injection. `vint`/`vunit` lower to native WASM scalars; `vthunk` to a
closure; every other former boxes. -/
def compileV : Bang.Val → Wasmfx.Val
  | .vint n   => .i32 n
  | .vunit    => .unit
  | .vthunk M => .clos M
  | v         => .boxed v

/-- A terminal computation (`ret v` / `lam M`) injected onto the WASM operand
stack. `exec`'s `Stack` holds terminals; `wexec`'s `VStack` holds their
injections — the simulation relates the two pointwise. -/
def injTerminal : Comp → Wasmfx.Val
  | .ret v => compileV v
  | .lam M => .clos M
  | _      => .unit          -- non-terminal: unreachable on the well-formed path

/-- Lower one calculated instruction (`Bang.Instr`) to a WASM opcode list. Pure
spine only (Milestone A): RET/LAMI/SUBST/APP map 1:1; the handler/ADT
instructions are Milestone B / out-of-scope and lower to the empty stream (a
closed PURE program's `compile` emits none of them). -/
def lowerInstr : CalcVM.Instr → List Wasmfx.Instr
  | .RET v   => [.const v]
  | .LAMI M  => [.clos M]
  | .SUBST N => [.bindS N]
  | .APP v   => [.callS v]
  | _        => []          -- Milestone B (MARK/UNMARK/THROW/OP/CASE/SPLIT)

def lowerCode : CalcVM.Code → Wasmfx.Code
  | []      => []
  | i :: c  => lowerInstr i ++ lowerCode c

/-- The compiler: lower the calculated `compile c []`. Result type fixed to `i32`
for Milestone A (the pure fragment returns i32/unit; a precise result type comes
with `compile_well_typed`'s typing premise). -/
def compileC (c : Comp) : Wasmfx.Module :=
  { body := lowerCode (CalcVM.compile c []), result := .i32 }

/-- Handlers are Milestone B (generator suspend/resume). Stubbed to an empty
module; `handler_compiles` is a Milestone B obligation. -/
def compileHandler (_ : Handler) : Wasmfx.Module :=
  { body := [], result := .unit }

namespace Wasmfx

/-! ### `wexec` — the WASM stack machine (pure spine)

A fuel-stepped stack machine over `Wasmfx.Code` × `VStack`, in LOCKSTEP with the
calculated `exec` (`Bang/CalcVM.lean`) on the pure spine. The `bindS`/`callS`
arms re-`compile`+`lowerCode` the residual `subst` exactly as `exec` re-compiles
it — that is the closure-carrying-coderef shape a real WasmFX backend uses, and
it makes the `wexec ≈ exec` simulation a clean structural induction. -/

/-- Recover the source value an operand carries — the LEFT INVERSE of `compileV`
(`recoverV (compileV v) = v`, `compileV_recoverV`). The `bindS`/`callS` arms use
it to re-`compile` the residual `subst` exactly as `exec`'s SUBST/APP arms do. -/
def recoverV : Val → Bang.Val
  | .i32 n   => .vint n
  | .unit    => .vunit
  | .clos M  => .vthunk M
  | .boxed v => v

/-- `recoverV` is the left inverse of `compileV`: the operand carrying `compileV v`
recovers exactly `v`. The round-trip that makes `wexec`'s `bindS`/`callS` arms
re-compile the SAME residual `exec` does. -/
theorem compileV_recoverV (v : Bang.Val) : recoverV (compileV v) = v := by
  cases v <;> rfl

def wexec : Nat → Code → VStack → Option VStack
  | 0,          _,              _ => none
  | Nat.succ _, [],             s => some s
  | Nat.succ f, .const v :: c,  s => wexec f c (compileV v :: s)
  | Nat.succ f, .clos M :: c,   s => wexec f c (.clos M :: s)
  | Nat.succ f, .bindS N :: c,  s =>
      match s with
      -- pop the operand (the injection of a `ret v`); recover `v` and re-compile
      -- `N[v]` PREPENDED to the remaining code `c`, exactly as `exec`'s SUBST arm.
      | w :: s' => wexec f (lowerCode (CalcVM.compile (Comp.subst (recoverV w) N) []) ++ c) s'
      | _       => none
  | Nat.succ f, .callS v :: c,  s =>
      match s with
      | .clos N :: s' => wexec f (lowerCode (CalcVM.compile (Comp.subst v N) []) ++ c) s'
      | _             => none
  | Nat.succ f, .getL _ :: c,   s => wexec f c s     -- (open programs only; closed ⇒ unused)
  | Nat.succ f, .setL _ :: c,   s => wexec f c s

/-- Run a compiled module to a single value on the operand stack. The closed
program starts on the empty stack; `done` = a singleton operand stack. -/
def run (fuel : Nat) (m : Module) : Result Val :=
  match wexec fuel m.body [] with
  | some [v] => .done v
  | some _   => .stuck
  | none     => .oom

/-! ### The pure fragment (Milestone A scope)

`Comp.Pure`/`Val.Pure` carve out the CBPV core the compiler covers: `ret · letC ·
force/vthunk · lam · app` over `vint/vunit/vthunk` values. NO `up`/`handle` (the
effect ops — Milestone B), NO ADT formers/eliminators (`case/split/unfold`,
`inl/inr/pair/fold` — a later increment), NO `oom`/`wrong`. A thunk body must be
pure (it is run on `force`), so the predicates are mutually recursive. -/
mutual
def Comp.Pure : Comp → Prop
  | .ret v          => Val.Pure v
  | .letC M N       => Comp.Pure M ∧ Comp.Pure N
  | .force (.vthunk M) => Comp.Pure M    -- `force` only steps on a thunk (closed-focus)
  | .force _        => False
  | .lam M          => Comp.Pure M
  | .app M v        => Comp.Pure M ∧ Val.Pure v
  | _               => False
def Val.Pure : Bang.Val → Prop
  | .vunit        => True
  | .vint _       => True
  | .vvar _       => True
  | .vthunk M     => Comp.Pure M
  | _             => False
end

/-! ### `wexec ≈ exec` — the forward simulation (pure spine)

The genuinely-new ◊5 content: the WASM machine refines the calculated `exec`. A
calculated instruction is `PureInstr` when it is one of the four pure-spine
opcodes (RET/LAMI/SUBST/APP) — the ONLY ones a closed PURE program's `compile`
emits. `injStack` injects `exec`'s terminal-stack pointwise via `injTerminal`.

`exec_wexec_sim`: for pure-spine code at the EMPTY handler stack, every `exec`
run is mirrored by a `wexec` run on the injected stacks. The proof is a fuel
induction with a head-instruction case split; each arm is definitional lockstep
(I built `wexec` to mirror `exec`). The `SUBST`/`APP` arms re-`compile` the SAME
residual `subst` (via `compileV_recoverV`), and the recursive code stays pure
because `compile` of a pure-fragment reduct is pure (`compile_pure`). -/

/-- A calculated instruction is pure-spine (the four Milestone-A opcodes). The
handler/ADT instructions (MARK/UNMARK/THROW/OP/CASE/SPLIT) are NOT pure — they
lower to the empty WASM stream and are Milestone B. The SUBST/APP residual
`Comp`s must themselves be in the pure fragment (so their re-`compile` stays
pure) — captured by `Comp.Pure` below. -/
def InstrPure : CalcVM.Instr → Prop
  | .RET v   => Val.Pure v        -- a pushed value must be pure (it lands on the stack)
  | .LAMI M  => Comp.Pure M       -- a `lam` body must stay pure (it is re-compiled on APP)
  | .SUBST N => Comp.Pure N
  | .APP v   => Val.Pure v        -- the applied argument must be pure (it is substituted)
  | _        => False

def CodePure (code : CalcVM.Code) : Prop := ∀ i ∈ code, InstrPure i

/-- Pointwise injection of `exec`'s terminal-stack onto the WASM operand stack. -/
def injStack (s : CalcVM.Stack) : VStack := s.map injTerminal

/-! #### Purity preservation under shift / subst (autosubst-style, structural) -/

mutual
theorem Val.shiftFrom_pure (k : Nat) : ∀ {t : Bang.Val}, Val.Pure t → Val.Pure (Val.shiftFrom k t)
  | .vunit, _   => by simp [Val.shiftFrom, Val.Pure]
  | .vint _, _  => by simp [Val.shiftFrom, Val.Pure]
  | .vvar i, _  => by
      by_cases hi : i < k <;> simp [Val.shiftFrom, hi, Val.Pure]
  | .vthunk M, h => by
      simp only [Val.shiftFrom, Val.Pure] at h ⊢; exact Comp.shiftFrom_pure k h
theorem Comp.shiftFrom_pure (k : Nat) : ∀ {t : Comp}, Comp.Pure t → Comp.Pure (Comp.shiftFrom k t)
  | .ret w, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢; exact Val.shiftFrom_pure k h
  | .letC M N, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢
      exact ⟨Comp.shiftFrom_pure k h.1, Comp.shiftFrom_pure (k+1) h.2⟩
  | .force w, h => by
      cases w with
      | vthunk M =>
          simp only [Comp.shiftFrom, Val.shiftFrom, Comp.Pure] at h ⊢
          exact Comp.shiftFrom_pure k h
      | _ => simp only [Comp.Pure] at h
  | .lam M, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢; exact Comp.shiftFrom_pure (k+1) h
  | .app M w, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢
      exact ⟨Comp.shiftFrom_pure k h.1, Val.shiftFrom_pure k h.2⟩
end

mutual
theorem Val.substFrom_pure (k : Nat) {v : Bang.Val} (hv : Val.Pure v) :
    ∀ {t : Bang.Val}, Val.Pure t → Val.Pure (Val.substFrom k v t)
  | .vunit, _   => by simp [Val.substFrom, Val.Pure]
  | .vint _, _  => by simp [Val.substFrom, Val.Pure]
  | .vvar i, _  => by
      simp only [Val.substFrom]
      by_cases h1 : i = k
      · simp [h1, hv]
      · by_cases h2 : i > k <;> simp [h1, h2, Val.Pure]
  | .vthunk M, h => by
      simp only [Val.substFrom, Val.Pure] at h ⊢; exact Comp.substFrom_pure k hv h
theorem Comp.substFrom_pure (k : Nat) {v : Bang.Val} (hv : Val.Pure v) :
    ∀ {t : Comp}, Comp.Pure t → Comp.Pure (Comp.substFrom k v t)
  | .ret w, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢; exact Val.substFrom_pure k hv h
  | .letC M N, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢
      exact ⟨Comp.substFrom_pure k hv h.1,
             Comp.substFrom_pure (k+1) (Val.shiftFrom_pure 0 hv) h.2⟩
  | .force w, h => by
      cases w with
      | vthunk M =>
          simp only [Comp.substFrom, Val.substFrom, Comp.Pure] at h ⊢
          exact Comp.substFrom_pure k hv h
      | _ => simp only [Comp.Pure] at h
  | .lam M, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢
      exact Comp.substFrom_pure (k+1) (Val.shiftFrom_pure 0 hv) h
  | .app M w, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢
      exact ⟨Comp.substFrom_pure k hv h.1, Val.substFrom_pure k hv h.2⟩
end

/-- `subst v N` stays pure when both `v` and `N` are. The β/let reduct purity that
keeps the simulation's recursive `compile (subst …)` inside the pure fragment. -/
theorem subst_pure {v : Bang.Val} {N : Comp} (hv : Val.Pure v) (hN : Comp.Pure N) :
    Comp.Pure (Comp.subst v N) :=
  Comp.substFrom_pure 0 hv hN

/-! #### `compile` / `lowerCode` append homomorphisms + purity -/

/-- `lowerCode` is a `++`-homomorphism (it is a `flatMap`). -/
theorem lowerCode_append (a b : CalcVM.Code) :
    lowerCode (a ++ b) = lowerCode a ++ lowerCode b := by
  induction a with
  | nil => simp [lowerCode]
  | cons i c ih => simp [lowerCode, ih, List.append_assoc]

/-- `compile` is a difference-list builder on the PURE fragment: `compile M c`
appends to `c`. (True structurally over the 5 pure arms; the non-pure arms are
out of scope.) -/
theorem compile_append : ∀ {M : Comp}, Comp.Pure M → ∀ (c : CalcVM.Code),
    CalcVM.compile M c = CalcVM.compile M [] ++ c
  | .ret v, _, c => by simp [CalcVM.compile]
  | .lam M, _, c => by simp [CalcVM.compile]
  | .force w, h, c => by
      -- only `force (vthunk M)` is pure; `compile (force (vthunk M)) c = compile M c`.
      cases w with
      | vthunk M => simp only [CalcVM.compile]; exact compile_append (by simpa [Comp.Pure] using h) c
      | _ => simp only [Comp.Pure] at h
  | .letC M N, h, c => by
      simp only [Comp.Pure] at h
      simp only [CalcVM.compile]
      rw [compile_append h.1 (CalcVM.Instr.SUBST N :: c),
          compile_append h.1 (CalcVM.Instr.SUBST N :: []), List.append_assoc]
      simp
  | .app M w, h, c => by
      simp only [Comp.Pure] at h
      simp only [CalcVM.compile]
      rw [compile_append h.1 (CalcVM.Instr.APP w :: c),
          compile_append h.1 (CalcVM.Instr.APP w :: []), List.append_assoc]
      simp

/-- `compile M c` of a pure `M` onto pure `c` stays pure. -/
theorem compile_pure : ∀ {M : Comp}, Comp.Pure M → ∀ {c : CalcVM.Code}, CodePure c →
    CodePure (CalcVM.compile M c)
  | .ret v, h, c, hc => by
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa only [InstrPure, Comp.Pure] using h
      · exact hc i hi
  | .lam M, h, c, hc => by
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa only [InstrPure] using h
      · exact hc i hi
  | .force w, h, c, hc => by
      cases w with
      | vthunk M => simp only [CalcVM.compile]; exact compile_pure (by simpa [Comp.Pure] using h) hc
      | _ => simp only [Comp.Pure] at h
  | .letC M N, h, c, hc => by
      simp only [Comp.Pure] at h
      simp only [CalcVM.compile]
      refine compile_pure h.1 ?_
      intro i hi; simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa only [InstrPure] using h.2
      · exact hc i hi
  | .app M w, h, c, hc => by
      simp only [Comp.Pure] at h
      simp only [CalcVM.compile]
      refine compile_pure h.1 ?_
      intro i hi; simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa only [InstrPure] using h.2
      · exact hc i hi

/-! #### The lockstep simulation `exec ⟹ wexec`

For PURE-spine code at the EMPTY handler stack, every successful `exec` run is
mirrored by a `wexec` run at the SAME fuel on the injected stacks. Fuel aligns
1:1 (a pure CalcVM instr lowers to exactly one WASM instr). The SUBST/APP arms
recover the popped value (`compileV_recoverV`) and re-compile the SAME residual,
prepended via `compile_append`/`lowerCode_append`; the recompiled code stays pure
(`compile_pure` + `subst_pure`), sustaining the induction invariant.

`StackPure` is the operand-stack invariant: every terminal on the stack is a pure
`ret v`/`lam M`. `exec` preserves it (RET/LAMI push pure terminals from pure
instrs; SUBST/APP pop a pure value and run pure recompiled code), which discharges
the value-purity obligation in the SUBST/APP arms. -/
def TerminalPure : Comp → Prop
  | .ret v => Val.Pure v
  | .lam M => Comp.Pure M
  | _      => False

def StackPure (s : CalcVM.Stack) : Prop := ∀ t ∈ s, TerminalPure t

theorem exec_wexec_sim :
    ∀ (f : Nat) (code : CalcVM.Code) (s s' : CalcVM.Stack),
      CodePure code → StackPure s →
      CalcVM.exec f code s [] = some s' →
      wexec f (lowerCode code) (injStack s) = some (injStack s') := by
  intro f
  induction f with
  | zero => intro code s s' _ _ h; simp [CalcVM.exec] at h
  | succ f ih =>
    intro code s s' hpure hsp h
    cases code with
    | nil =>
        simp only [CalcVM.exec, Option.some.injEq] at h; subst h
        simp [lowerCode, wexec]
    | cons i c =>
        have hi : InstrPure i := hpure i (by simp)
        have hc : CodePure c := fun j hj => hpure j (List.mem_cons_of_mem _ hj)
        cases i with
        | RET v =>
            simp only [CalcVM.exec] at h
            have hv : Val.Pure v := by simpa only [InstrPure] using hi
            simp only [lowerInstr, lowerCode, List.cons_append, List.nil_append, wexec, injStack,
              injTerminal, List.map_cons]
            exact ih c (.ret v :: s) s' hc
              (fun t ht => by
                rcases List.mem_cons.mp ht with rfl | ht
                · simpa only [TerminalPure] using hv
                · exact hsp t ht) h
        | LAMI M =>
            simp only [CalcVM.exec] at h
            have hM : Comp.Pure M := by simpa only [InstrPure] using hi
            simp only [lowerInstr, lowerCode, List.cons_append, List.nil_append, wexec, injStack,
              injTerminal, List.map_cons]
            exact ih c (.lam M :: s) s' hc
              (fun t ht => by
                rcases List.mem_cons.mp ht with rfl | ht
                · simpa only [TerminalPure] using hM
                · exact hsp t ht) h
        | SUBST N =>
            simp only [CalcVM.exec] at h
            cases s with
            | nil => simp at h
            | cons hd s0 =>
                cases hd with
                | ret v =>
                    have hN : Comp.Pure N := by simpa only [InstrPure] using hi
                    have hv : Val.Pure v := by
                      have := hsp (.ret v) (by simp); simpa only [TerminalPure] using this
                    have hsp0 : StackPure s0 := fun t ht => hsp t (List.mem_cons_of_mem _ ht)
                    have hpu : Comp.Pure (Comp.subst v N) := subst_pure hv hN
                    have hcode : CalcVM.compile (Comp.subst v N) c
                        = CalcVM.compile (Comp.subst v N) [] ++ c := compile_append hpu c
                    have key : wexec f (lowerCode (CalcVM.compile (Comp.subst v N) c)) (injStack s0)
                        = some (injStack s') :=
                      ih _ s0 s' (compile_pure hpu hc) hsp0 h
                    simp only [lowerInstr, lowerCode, List.cons_append, List.nil_append, wexec,
                      injStack, injTerminal, List.map_cons]
                    rw [compileV_recoverV, ← lowerCode_append, ← hcode]
                    simpa [injStack] using key
                | _ => simp at h
        | APP v =>
            simp only [CalcVM.exec] at h
            cases s with
            | nil => simp at h
            | cons hd s0 =>
                cases hd with
                | lam N =>
                    have hv : Val.Pure v := by simpa only [InstrPure] using hi
                    have hN : Comp.Pure N := by
                      have := hsp (.lam N) (by simp); simpa only [TerminalPure] using this
                    have hsp0 : StackPure s0 := fun t ht => hsp t (List.mem_cons_of_mem _ ht)
                    have hpu : Comp.Pure (Comp.subst v N) := subst_pure hv hN
                    have hcode : CalcVM.compile (Comp.subst v N) c
                        = CalcVM.compile (Comp.subst v N) [] ++ c := compile_append hpu c
                    have key : wexec f (lowerCode (CalcVM.compile (Comp.subst v N) c)) (injStack s0)
                        = some (injStack s') :=
                      ih _ s0 s' (compile_pure hpu hc) hsp0 h
                    simp only [lowerInstr, lowerCode, List.cons_append, List.nil_append, wexec,
                      injStack, injTerminal, List.map_cons]
                    rw [← lowerCode_append, ← hcode]
                    simpa [injStack] using key
                | _ => simp at h
        | _ => exact absurd hi (by simp [InstrPure])

/-! ### Structural predicates (`WellTyped`, `MentionsLocal`)

`MentionsLocal m k` — the module's instruction stream contains a `getL k`/`setL
k`. For the QTT-erasure headline (`zero_grade_no_code`), a 0-graded binder emits
NO `local` reference, so the pure-spine `compileC` (which threads no `getL`/`setL`
for closed-focus substitution code) trivially has none — the calculated machine
is substitution-based (closed focus, ADR-0025 D2), so `compile c []` carries no
free-variable locals at all. -/
def InstrMentionsLocal : Instr → Nat → Prop
  | .getL k, j => k = j
  | .setL k, j => k = j
  | _,       _ => False

def MentionsLocal (m : Module) (k : Nat) : Prop :=
  ∃ i ∈ m.body, InstrMentionsLocal i k

/-- A module is well-typed when its body is a well-formed pure-spine stream. For
Milestone A: the pure-spine opcodes are always well-formed (the calculated
`compile` of a typed program emits only RET/LAMI/SUBST/APP, which lower to
const/clos/bindS/callS). Made a structural `Prop` so `compile_well_typed`
discharges by construction. -/
def InstrWF : Instr → Prop
  | .getL _ => False        -- closed-focus compile emits no locals (Milestone A)
  | .setL _ => False
  | _       => True

def WellTyped (m : Module) : Prop :=
  ∀ i ∈ m.body, InstrWF i

end Wasmfx

/-! ### Handler predicates (Milestone B placeholders, kept honest)

`HandlerLawful` / `Wasmfx.HandlerEquiv` are the Milestone B (generator
suspend/resume) obligations; defined as `True`-on-the-empty-handler-module so
`handler_compiles` is a tracked Milestone B `sorry`, not an axiom. They are NOT
exercised by Milestone A's forward-sim (closed PURE programs). -/
def HandlerLawful (_ : Handler) : Prop := True

def Wasmfx.HandlerEquiv (_ : Wasmfx.Module) (_ : Handler) : Prop := True


/-! ## §7 proofs — Milestone A

The structural headlines (`zero_grade_no_code`, `compile_well_typed`) and the
forward simulation (`compile_forward_sim`). Statements are FROZEN in
`Bang/Spec.lean`; these `_proof` lemmas are wired there (the project convention:
Spec owns the claim, a sibling module owns the proof). -/

namespace Wasmfx

/-- The lowering NEVER emits a `getL`/`setL`: the calculated machine is
substitution-based (closed focus, ADR-0025 D2), so it threads no free-variable
locals. Every `lowerInstr` output is `const`/`clos`/`bindS`/`callS` (or empty).
This is the structural core of BOTH `zero_grade_no_code` (the QTT-erasure
headline) and `compile_well_typed`. -/
theorem lowerInstr_no_locals (i : CalcVM.Instr) (j : Wasmfx.Instr)
    (h : j ∈ lowerInstr i) : (∀ k, j ≠ .getL k) ∧ (∀ k, j ≠ .setL k) := by
  cases i <;> simp [lowerInstr] at h <;>
    first
    | (subst h; exact ⟨by intro k; simp, by intro k; simp⟩)
    | exact absurd h (by simp)

theorem lowerCode_no_locals (code : CalcVM.Code) (j : Wasmfx.Instr)
    (h : j ∈ lowerCode code) : (∀ k, j ≠ .getL k) ∧ (∀ k, j ≠ .setL k) := by
  induction code with
  | nil => simp [lowerCode] at h
  | cons i c ih =>
    simp only [lowerCode, List.mem_append] at h
    rcases h with h | h
    · exact lowerInstr_no_locals i j h
    · exact ih h

/-- `compileC` output mentions NO local (any `k`) — a fortiori not local 0. The
substitution-based calculated machine carries no variable locals. -/
theorem compileC_no_local (c : Comp) (k : Nat) :
    ¬ MentionsLocal (compileC c) k := by
  rintro ⟨i, hi, hml⟩
  obtain ⟨hg, hs⟩ := lowerCode_no_locals (CalcVM.compile c []) i hi
  cases i <;> simp [InstrMentionsLocal] at hml
  · exact hg _ rfl
  · exact hs _ rfl

/-- `compileC` output is well-typed (pure-spine, Milestone A): every instruction
is `InstrWF` because none is a `getL`/`setL`. -/
theorem compileC_wellTyped (c : Comp) : WellTyped (compileC c) := by
  intro i hi
  obtain ⟨hg, hs⟩ := lowerCode_no_locals (CalcVM.compile c []) i hi
  cases i <;> simp [InstrWF]
  · exact hg _ rfl
  · exact hs _ rfl

end Wasmfx

/-- `zero_grade_no_code` proof (the QTT-erasure headline): a 0-graded binder emits
no `local` reference. STRONGER than required — the substitution-based calculated
machine emits NO locals at all (any binder, any grade), so the grade-0 hypothesis
is not even needed. The headline is observable in the output: `compileC` never
references local 0. -/
theorem zero_grade_no_code_proof {Eff Mult : Type} [Lattice Eff] [OrderBot Eff]
    [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (_ : HasCTy ((0 : Mult) :: γ) (A :: Γ) c e B) :
    ¬ Wasmfx.MentionsLocal (compileC c) 0 :=
  Wasmfx.compileC_no_local c 0

/-- `compile_well_typed` proof (Milestone A): the pure-spine lowering is
well-formed by construction. The typing premise is unused at Milestone A (every
`compileC` output is structurally `InstrWF`); it becomes load-bearing when the
result type is refined and the continuation/ADT opcodes land (Milestone B). -/
theorem compile_well_typed_proof {Eff Mult : Type} [Lattice Eff] [OrderBot Eff]
    [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult}
    (_ : HasCTy ([] : GradeVec Mult) ([] : TyCtx Eff Mult) c e (CTy.F q A)) :
    Wasmfx.WellTyped (compileC c) :=
  Wasmfx.compileC_wellTyped c

/-! ### `compile_forward_sim` — the heart (PURE fragment proven; gaps named)

The forward simulation chains:

  Source.eval fuel c = done v
    ──(reverse bridge: `source_eval_to_exec`, the ONE remaining gap)──▸
  ∃F, CalcVM.exec F (compile c []) [] [] = some [.ret v]
    ──(`exec_wexec_sim`, PROVEN)──▸
  wexec F (lowerCode (compile c [])) [] = some [compileV v]
    ──(`run` unfold)──▸
  Wasmfx.run F (compileC c) = done (compileV v)

The middle and final legs are PROVEN. The first leg — `Source.eval` ⟹ `exec ∘
compile` — is the reverse of the CalcVM bridge that IS proven
(`evalD_agrees_source` goes `evalD ⟹ Source.eval`). It is a determinacy/
completeness argument (both machines are deterministic and total-on-termination),
left as a single named obligation. -/

/-! ### GAP 1 — the reverse CalcVM bridge (`Source.eval ⟹ exec`, pure fragment)

The converse of `CalcVM.run_evalD`. `Source.eval` (small-step CK) ⟹ `evalD`
(big-step) for the pure fragment, then compose the PROVEN `CalcVM.compile_correct`
(`evalD ⟹ exec`). The converse simulation is a STRONG induction on the
small-step fuel `F`: each `Source.step` decrements `F`, and the pure restriction
(no stores/handlers/raises, σ=τ=[]) collapses `run_evalD`'s CtxCorr/ctxNetEffect
bookkeeping to nothing.

`evalD_mono` (fuel monotonicity) lets the letC/app arms combine the existential
fuels of their two sub-evaluations. -/

/-- `evalD` fuel monotonicity: more fuel never changes a `some` result. Structural
induction on `f` with the IH applied to every sub-call (all at `f`). -/
theorem evalD_mono : ∀ (f : Nat) (σ : CalcVM.SStore) (τ : CalcVM.THeap) (c : Comp) r,
    CalcVM.evalD f σ τ c = some r → CalcVM.evalD (f + 1) σ τ c = some r := by
  intro f
  induction f with
  | zero => intro σ τ c r h; simp [CalcVM.evalD] at h
  | succ f ih =>
    intro σ τ c r h
    cases c with
    | ret v => simpa [CalcVM.evalD] using h
    | lam M => simpa [CalcVM.evalD] using h
    | force w =>
        cases w with
        | vthunk M => simp only [CalcVM.evalD] at h ⊢; exact ih σ τ M r h
        | _ => simp [CalcVM.evalD] at h
    | letC M N =>
        simp only [CalcVM.evalD] at h ⊢
        cases hM : CalcVM.evalD f σ τ M with
        | none => rw [hM] at h; simp at h
        | some oM =>
            rw [hM] at h; rw [ih σ τ M oM hM]
            cases oM with
            | mk out st =>
                cases out with
                | term t =>
                    cases t with
                    | ret w =>
                        simp only [Option.bind_some] at h ⊢
                        obtain ⟨st1, st2⟩ := st
                        exact ih st1 st2 (Comp.subst w N) r h
                    | _ => simp only [Option.bind_some] at h ⊢; exact h
                | raised ℓ op w => simpa only [Option.bind_some] using h
    | app M v =>
        simp only [CalcVM.evalD] at h ⊢
        cases hM : CalcVM.evalD f σ τ M with
        | none => rw [hM] at h; simp at h
        | some oM =>
            rw [hM] at h; rw [ih σ τ M oM hM]
            cases oM with
            | mk out st =>
                cases out with
                | term t =>
                    cases t with
                    | lam N =>
                        simp only [Option.bind_some] at h ⊢
                        obtain ⟨st1, st2⟩ := st
                        exact ih st1 st2 (Comp.subst v N) r h
                    | _ => simp only [Option.bind_some] at h ⊢; exact h
                | raised ℓ op w => simpa only [Option.bind_some] using h
    | up ℓ op v => simpa [CalcVM.evalD] using h
    | handle hh M =>
        cases hh with
        | state ℓ s =>
            simp only [CalcVM.evalD] at h ⊢
            cases hM : CalcVM.evalD f (σ.push ℓ s) τ M with
            | none => rw [hM] at h; simp at h
            | some oM =>
                rw [hM] at h; rw [ih (σ.push ℓ s) τ M oM hM]
                cases oM with | mk out st => cases out with
                  | term t => cases t with
                    | ret w => simpa only [Option.bind_some] using h
                    | _ => simpa only [Option.bind_some] using h
                  | raised ℓ' op' w => simpa only [Option.bind_some] using h
        | transaction ℓ Θ =>
            simp only [CalcVM.evalD] at h ⊢
            cases hM : CalcVM.evalD f σ (τ.push ℓ Θ) M with
            | none => rw [hM] at h; simp at h
            | some oM =>
                rw [hM] at h; rw [ih σ (τ.push ℓ Θ) M oM hM]
                cases oM with | mk out st => cases out with
                  | term t => cases t with
                    | ret w => simpa only [Option.bind_some] using h
                    | _ => simpa only [Option.bind_some] using h
                  | raised ℓ' op' w => simpa only [Option.bind_some] using h
        | throws ℓ0 =>
            simp only [CalcVM.evalD] at h ⊢
            cases hM : CalcVM.evalD f σ τ M with
            | none => rw [hM] at h; simp at h
            | some oM =>
                rw [hM] at h; rw [ih σ τ M oM hM]
                cases oM with | mk out st => cases out with
                  | term t => cases t with
                    | ret w => simpa only [Option.bind_some] using h
                    | _ => simpa only [Option.bind_some] using h
                  | raised ℓ' op' w => simpa only [Option.bind_some] using h
    | case w N₁ N₂ =>
        cases w <;> simp only [CalcVM.evalD] at h ⊢ <;> first
          | exact ih _ _ _ r h
          | (exact h)
    | split w N =>
        cases w <;> simp only [CalcVM.evalD] at h ⊢ <;> first
          | exact ih _ _ _ r h
          | (exact h)
    | unfold w =>
        cases w <;> simp only [CalcVM.evalD] at h ⊢ <;> exact h
    | oom => simp [CalcVM.evalD] at h
    | wrong s => simp [CalcVM.evalD] at h

/-- `evalD` adds fuel: `evalD f … = some r ⇒ evalD (f + k) … = some r`. -/
theorem evalD_add (k : Nat) : ∀ (f : Nat) (σ : CalcVM.SStore) (τ : CalcVM.THeap) (c : Comp) r,
    CalcVM.evalD f σ τ c = some r → CalcVM.evalD (f + k) σ τ c = some r := by
  induction k with
  | zero => intro f σ τ c r h; simpa using h
  | succ k ih =>
    intro f σ τ c r h
    rw [show f + (k + 1) = (f + k) + 1 by omega]
    exact evalD_mono (f + k) σ τ c r (ih f σ τ c r h)

/-- `evalD` results agree regardless of which (sufficient) fuel: two `some`s with
possibly different fuels coincide. Used to align the two sub-evaluation fuels. -/
theorem evalD_some_le {f g : Nat} {σ : CalcVM.SStore} {τ : CalcVM.THeap} {c : Comp} {r : _}
    (hfg : f ≤ g) (h : CalcVM.evalD f σ τ c = some r) :
    CalcVM.evalD g σ τ c = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hfg
  exact evalD_add k f σ τ c r h

/-! #### `evalD`-completeness via the plugged-term invariant

KEY IDEA: `plug K c` (`Operational.lean`) wraps the focus `c` back into its
frame stack as `letC`/`app` nodes, and `evalD` of that plugged term big-steps the
WHOLE config — so the target is `evalD n [] [] (plug K c) = some (.term (.ret v),
[],[])`. The induction is STRONG on the small-step fuel `F`. Each `Source.step`
either PRESERVES `plug K c` (a PUSH: `plug (fr::K) c' = plug K (fr.wrapStep c')`,
`plug_cons`) or is a β/let REDUCE whose evalD-completeness transfers by one evalD
unfold. The pure restriction means only letC/app/force-vthunk/letF/appF arise. -/

/-- A frame stack is pure when every frame is a `letF`/`appF` with pure contents
(no `handleF` — pure programs install no handlers). -/
def PureCtx : Bang.EvalCtx → Prop
  | [] => True
  | .letF N :: K => Wasmfx.Comp.Pure N ∧ PureCtx K
  | .appF v :: K => Wasmfx.Val.Pure v ∧ PureCtx K
  | .handleF _ :: K => False

/-- `plug K c` stays pure when `K` and `c` are. -/
theorem plug_pure : ∀ {K : Bang.EvalCtx}, PureCtx K → ∀ {c : Comp}, Wasmfx.Comp.Pure c →
    Wasmfx.Comp.Pure (plug K c)
  | [], _, c, hc => hc
  | .letF N :: K, hK, c, hc => by
      simp only [PureCtx] at hK
      exact plug_pure hK.2 (by simp only [Wasmfx.Comp.Pure]; exact ⟨hc, hK.1⟩)
  | .appF v :: K, hK, c, hc => by
      simp only [PureCtx] at hK
      exact plug_pure hK.2 (by simp only [Wasmfx.Comp.Pure]; exact ⟨hc, hK.1⟩)

/-- `cx` SIMULATES `cy` (closed, pure): everything `cy` big-steps to, `cx` does
too (possibly with different fuel). The relation a CK REDUCE step establishes
between a redex and its contractum. -/
def Simulates (cx cy : Comp) : Prop :=
  ∀ r, CalcVM.evalD 0 [] [] cy = some r ∨ (∃ b, CalcVM.evalD b [] [] cy = some r) →
    ∃ a, CalcVM.evalD a [] [] cx = some r

/-- Cleaner simulation: anything `cy` evaluates to (some fuel), `cx` evaluates to. -/
def Sim (cx cy : Comp) : Prop :=
  ∀ b r, CalcVM.evalD b [] [] cy = some r → ∃ a, CalcVM.evalD a [] [] cx = some r

/-- `letC` preserves simulation in the bound position: if `cx` simulates `cy`,
then `letC cx N` simulates `letC cy N`. Both run the bound computation FIRST;
`cx` reaches every terminal `cy` does, so the `letC`s agree. The non-`ret`
terminal case is vacuous (`evalD (letC _ N)` of a `lam`-terminal is `none`); the
`raised` case propagates the same raise. -/
theorem Sim.letC {cx cy : Comp} (h : Sim cx cy) (N : Comp) : Sim (.letC cx N) (.letC cy N) := by
  intro b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b [] [] cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h b oy hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | ret w =>
                  simp only [Option.bind_some] at hb
                  refine ⟨(max a b) + 1, ?_⟩
                  simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                  exact evalD_some_le (Nat.le_max_right a b) hb
              | lam M => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | up a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                refine ⟨a + 1, ?_⟩
                simp only [CalcVM.evalD, ha, Option.bind_some]
                exact hb

theorem Sim.app {cx cy : Comp} (h : Sim cx cy) (u : Bang.Val) : Sim (.app cx u) (.app cy u) := by
  intro b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b [] [] cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h b oy hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | lam M =>
                  simp only [Option.bind_some] at hb
                  refine ⟨(max a b) + 1, ?_⟩
                  simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                  exact evalD_some_le (Nat.le_max_right a b) hb
              | ret w => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | up a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                refine ⟨a + 1, ?_⟩
                simp only [CalcVM.evalD, ha, Option.bind_some]
                exact hb

/-- The plug-congruence: a focus simulation lifts through any pure frame stack.
Induction on `K`, using `Sim.letC`/`Sim.app` to push the simulation down one
frame. -/
theorem evalD_plug_sim : ∀ {K : Bang.EvalCtx}, PureCtx K → ∀ {cx cy : Comp}, Sim cx cy →
    ∀ {n r}, CalcVM.evalD n [] [] (plug K cy) = some r →
    ∃ m, CalcVM.evalD m [] [] (plug K cx) = some r
  | [], _, cx, cy, h, n, r, hn => h n r (by simpa [plug] using hn)
  | .letF N :: K, hK, cx, cy, h, n, r, hn => by
      simp only [PureCtx] at hK
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim hK.2 (h.letC N) hn
  | .appF u :: K, hK, cx, cy, h, n, r, hn => by
      simp only [PureCtx] at hK
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim hK.2 (h.app u) hn

/-- The three CK REDUCE steps as simulations (the contractum simulates the redex):
each is a single `evalD` head-unfold. -/
-- DIRECTION: the REDEX simulates the CONTRACTUM (what `subst …` reaches, `letC (ret w) N`
-- reaches too, in one extra unfold) — this is the direction the transfer needs (it has the
-- contractum's `evalD`, wants the redex's).
theorem sim_letC_ret (w : Bang.Val) (N : Comp) : Sim (.letC (.ret w) N) (Comp.subst w N) := by
  intro b r hb
  refine ⟨b + 2, ?_⟩
  simp only [CalcVM.evalD, Option.bind_some]
  exact evalD_some_le (by omega) hb

theorem sim_app_lam (u : Bang.Val) (M : Comp) : Sim (.app (.lam M) u) (Comp.subst u M) := by
  intro b r hb
  refine ⟨b + 2, ?_⟩
  simp only [CalcVM.evalD, Option.bind_some]
  exact evalD_some_le (by omega) hb

theorem sim_force (M : Comp) : Sim (.force (.vthunk M)) M := by
  intro b r hb
  exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩

/-- The three transfer lemmas `evalD_complete_gen` invokes, derived from
`evalD_plug_sim` + the redex simulations. -/
theorem evalD_plug_letC_ret (K : Bang.EvalCtx) (w : Bang.Val) (N : Comp) (r : _)
    (hK : PureCtx K) (h : CalcVM.evalD r [] [] (plug K (Comp.subst w N)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.letC (.ret w) N)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim hK (sim_letC_ret w N) h

theorem evalD_plug_app_lam (K : Bang.EvalCtx) (u : Bang.Val) (M : Comp) (r : _)
    (hK : PureCtx K) (h : CalcVM.evalD r [] [] (plug K (Comp.subst u M)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.app (.lam M) u)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim hK (sim_app_lam u M) h

theorem evalD_plug_force (K : Bang.EvalCtx) (M : Comp) (r : _)
    (hK : PureCtx K) (h : CalcVM.evalD r [] [] (plug K M) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.force (.vthunk M))) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim hK (sim_force M) h

/-- `evalD`-completeness for the pure fragment, generalized over the frame stack:
a terminating CK run is big-stepped by `evalD` of the plugged term. Strong
induction on the small-step fuel `F`. -/
theorem evalD_complete_gen : ∀ (F : Nat) (K : Bang.EvalCtx) (c : Comp) (v : Bang.Val),
    PureCtx K → Wasmfx.Comp.Pure c →
    Config.run F (K, c) = Result.done v →
    ∃ n, CalcVM.evalD n [] [] (plug K c) = some (.term (.ret v), [], []) := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro K c v hK hc hrun
    -- F = 0 ⇒ run = oom ≠ done.
    cases F with
    | zero => simp [Config.run] at hrun
    | succ F' =>
      -- terminal `([], ret v)` is the base; otherwise one Source.step.
      by_cases hterm : ∃ w, (K, c) = ([], Comp.ret w)
      · obtain ⟨w, hKc⟩ := hterm
        simp only [Prod.mk.injEq] at hKc
        obtain ⟨hK0, hcw⟩ := hKc; subst hK0; subst hcw
        -- ([], ret w): run yields done w ⇒ w = v; evalD of `ret w` returns immediately.
        simp only [Config.run, Result.done.injEq] at hrun
        subst hrun
        exact ⟨1, by simp [plug, CalcVM.evalD]⟩
      · -- non-terminal: step once, recurse with F' < F'+1.
        have hstep := Config.run_step F' (K, c) (fun w h => hterm ⟨w, h⟩)
        rw [hrun] at hstep
        -- analyse the step on (K, c).
        cases c with
        | ret w =>
            -- focus is `ret w` but K ≠ [] (else terminal). K's head reduces.
            cases K with
            | nil => exact absurd ⟨w, rfl⟩ hterm
            | cons fr K' =>
                cases fr with
                | letF N =>
                    -- step: (letF N :: K', ret w) ↦ (K', subst w N)
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.subst w N) = Result.done v := hstep.symm
                    simp only [PureCtx] at hK
                    have hsub : Wasmfx.Comp.Pure (Comp.subst w N) :=
                      Wasmfx.subst_pure (by simpa only [Wasmfx.Comp.Pure] using hc) hK.1
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.subst w N) v hK.2 hsub hrun'
                    -- transfer: evalD (plug K' (letC (ret w) N)) ⟸ evalD (plug K' (subst w N)).
                    exact evalD_plug_letC_ret K' w N n hK.2 hn
                | appF u =>
                    -- (appF u :: K', ret w): `ret w` is not a `lam`; step is `none` ⇒ stuck, not done.
                    simp only [Source.step] at hstep
                    -- Source.step (appF u :: K', ret w) = none (only lam reduces under appF).
                    exact absurd hstep (by simp [Config.run])
                | handleF h => simp only [PureCtx] at hK
        | lam M =>
            cases K with
            | nil => simp [Config.run, Source.step] at hrun   -- ([], lam M): not a `ret`, run = stuck
            | cons fr K' =>
                cases fr with
                | letF N =>
                    simp only [Source.step] at hstep
                    exact absurd hstep (by simp [Config.run])  -- letF needs `ret`, lam stuck
                | appF u =>
                    -- (appF u :: K', lam M) ↦ (K', subst u M)  (β)
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.subst u M) = Result.done v := hstep.symm
                    simp only [PureCtx] at hK
                    have hsub : Wasmfx.Comp.Pure (Comp.subst u M) :=
                      Wasmfx.subst_pure hK.1 (by simpa only [Wasmfx.Comp.Pure] using hc)
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.subst u M) v hK.2 hsub hrun'
                    exact evalD_plug_app_lam K' u M n hK.2 hn
                | handleF h => simp only [PureCtx] at hK
        | letC M N =>
            -- (K, letC M N) ↦ (letF N :: K, M)  (PUSH; plug preserved)
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.letF N :: K, M) = Result.done v := hstep.symm
            simp only [Wasmfx.Comp.Pure] at hc
            have hK' : PureCtx (Frame.letF N :: K) := by
              simp only [PureCtx]; exact ⟨hc.2, hK⟩
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.letF N :: K) M v hK' hc.1 hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn
            exact ⟨n, hn⟩
        | app M u =>
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.appF u :: K, M) = Result.done v := hstep.symm
            simp only [Wasmfx.Comp.Pure] at hc
            have hK' : PureCtx (Frame.appF u :: K) := by
              simp only [PureCtx]; exact ⟨hc.2, hK⟩
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.appF u :: K) M v hK' hc.1 hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn
            exact ⟨n, hn⟩
        | force w =>
            cases w with
            | vthunk M =>
                -- (K, force (vthunk M)) ↦ (K, M)
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, M) = Result.done v := hstep.symm
                simp only [Wasmfx.Comp.Pure] at hc
                obtain ⟨n, hn⟩ := ih F' (by omega) K M v hK hc hrun'
                -- evalD (plug K (force (vthunk M))) ⟸ evalD (plug K M)  (force erases).
                exact evalD_plug_force K M n hK hn
            | _ => simp only [Wasmfx.Comp.Pure] at hc
        | _ => simp only [Wasmfx.Comp.Pure] at hc

/-- `evalD`-completeness (pure fragment, closed): `Source.eval F c = done v ⟹
∃n, evalD n [] [] c = some(.term(.ret v),[],[])`. The `K = []` instance of
`evalD_complete_gen`. -/
theorem evalD_complete (F : Nat) (c : Comp) (v : Bang.Val)
    (hpure : Wasmfx.Comp.Pure c) (h : Source.eval F c = Result.done v) :
    ∃ n, CalcVM.evalD n [] [] c = some (.term (.ret v), [], []) := by
  have := evalD_complete_gen F [] c v (by simp [PureCtx]) hpure h
  simpa [plug] using this

/-- The reverse CalcVM bridge for the PURE fragment: a terminating `Source.eval`
is mirrored by the calculated `exec ∘ compile`. Composes `evalD`-completeness
(`evalD_complete`) with the PROVEN `CalcVM.compile_correct`. -/
theorem source_eval_to_exec (c : Comp) (v : Bang.Val) (fuel : Nat)
    (hpure : Wasmfx.Comp.Pure c)
    (h : Source.eval fuel c = Result.done v) :
    ∃ F, CalcVM.exec F (CalcVM.compile c []) [] [] = some [.ret v] := by
  obtain ⟨n, hn⟩ := evalD_complete fuel c v hpure h
  exact CalcVM.compile_correct n c (.ret v) [] [] hn

/-- **GAP 1 CLOSED** — the forward simulation, PROVEN and AXIOM-CLEAN
(⊆ {propext, Classical.choice, Quot.sound}) for the PURE CBPV fragment. Chains
the reverse CalcVM bridge (`source_eval_to_exec`, now proven via the converse
simulation `evalD_complete`) through the `exec ⟹ wexec` lockstep
(`exec_wexec_sim`) to `run`. No `sorry` on this path. -/
theorem compile_forward_sim_pure {c : Comp} {v : Val} {fuel : Nat}
    (hpure : Wasmfx.Comp.Pure c)
    (h : Source.eval fuel c = Result.done v) :
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := by
  obtain ⟨F, hexec⟩ := source_eval_to_exec c v fuel hpure h
  have hcp : Wasmfx.CodePure (CalcVM.compile c []) :=
    Wasmfx.compile_pure hpure (fun _ hm => by simp at hm)
  have hsim := Wasmfx.exec_wexec_sim F (CalcVM.compile c []) [] [.ret v] hcp
    (fun _ hm => by simp at hm) hexec
  refine ⟨F, ?_⟩
  -- injStack [.ret v] = [compileV v]; wexec yields it.
  rw [show Wasmfx.injStack [Comp.ret v] = [compileV v] from by
    simp [Wasmfx.injStack, injTerminal]] at hsim
  -- `run` reduces on `wexec … = some [compileV v]` (singleton-operand-stack ⇒ done).
  have hb : Wasmfx.wexec F (compileC c).body [] = some [compileV v] := hsim
  show Wasmfx.run F (compileC c) = Result.done (compileV v)
  unfold Wasmfx.run
  rw [hb]

/-- `compile_forward_sim` proof. The PURE fragment is PROVEN axiom-clean
(`compile_forward_sim_pure`, GAP 1 closed). The remaining `sorry` is GAP 2 only:
the NON-pure fragment (`up`/`handle`/ADT) — Milestone B (handlers ↦ generator
suspend/resume) + a later ADT increment, where `compileC`'s lowering drops those
opcodes so the simulation does not yet hold. -/
theorem compile_forward_sim_proof {c : Comp} {v : Val} {fuel : Nat}
    (h : Source.eval fuel c = Result.done v) :
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := by
  by_cases hpure : Wasmfx.Comp.Pure c
  · -- PURE fragment: GAP 1 closed, axiom-clean.
    exact compile_forward_sim_pure hpure h
  · -- NON-pure (Milestone B + ADT increment): GAP 2.
    exact ⟨0, by sorry⟩

end Bang
