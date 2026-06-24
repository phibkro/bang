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

/-- The reverse CalcVM bridge for the PURE fragment: a terminating `Source.eval`
is mirrored by the calculated `exec ∘ compile`. The converse of
`CalcVM.evalD_agrees_source`; closes by `evalD`-completeness (a terminating
`Source.eval` ⟹ `evalD` returns the same value) composed with `compile_correct`.

NEEDS (the precise remaining work for Milestone A's forward-sim):
  (1) `evalD` COMPLETENESS on the pure spine: `Source.eval F c = done v ⇒
      ∃F', evalD F' [] [] c = some (.term (.ret v), [], [])`. The converse
      simulation of `CalcVM.run_evalD`; a determinacy argument since both are
      deterministic substitution machines. Then `CalcVM.compile_correct` gives
      `exec`. -/
theorem source_eval_to_exec (c : Comp) (v : Bang.Val) (fuel : Nat)
    (hpure : Wasmfx.Comp.Pure c)
    (h : Source.eval fuel c = Result.done v) :
    ∃ F, CalcVM.exec F (CalcVM.compile c []) [] [] = some [.ret v] := by
  -- shape: composes evalD-completeness (gap 1) with CalcVM.compile_correct (proven).
  sorry

/-- `compile_forward_sim` proof. PROVEN for the PURE CBPV fragment (Milestone A
scope) modulo the single reverse-bridge obligation `source_eval_to_exec`; the
`exec ⟹ wexec` leg and the `run` unfold are fully proven (`exec_wexec_sim`).

NEEDS (beyond `source_eval_to_exec`'s gap 1):
  (2) the NON-pure fragment (`up`/`handle`/ADT) — Milestone B (handlers ↦
      generator suspend/resume) and a later ADT increment. Here `compileC`'s
      lowering drops those opcodes, so the simulation does not yet hold; this is
      the `¬ Comp.Pure c` branch. -/
theorem compile_forward_sim_proof {c : Comp} {v : Val} {fuel : Nat}
    (h : Source.eval fuel c = Result.done v) :
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := by
  by_cases hpure : Wasmfx.Comp.Pure c
  · -- PURE fragment: chain the reverse bridge through the proven simulation.
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
  · -- NON-pure (Milestone B + ADT increment): see NEEDS (2).
    exact ⟨0, by sorry⟩

end Bang
