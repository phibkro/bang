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
  -- RESIDUAL re-compile instructions (`bindS`/`callS`/`caseS`/`splitS`). Each subsumes the WHOLE
  -- tail: at runtime it re-`compile`s `subst …` THREADING the CalcVM continuation it carries, exactly
  -- as `exec`'s SUBST/APP/CASE/SPLIT arms run `compile (subst …) c`. The carried `CalcVM.Code` is the
  -- AsmFX "epilogue annotation" (Lindley et al. 2025 §1.3): the real outer continuation a re-compiled
  -- `handle` body must capture in its `markH` — WITHOUT it, a zero-shot abort resumes `[]` and stops
  -- early (the model defect this representation fixes). NOTHING runs after a residual instr in the
  -- stream; the recompile consumes the tail (mirrors `exec`, where `compile (subst v N) c` replaces
  -- the whole code). So `lowerCode (SUBST N :: c) = [bindS N c]`, NOT `bindS N :: lowerCode c`.
  | bindS  : Comp → CalcVM.Code → Instr        -- pop value, bind, run N[v] THREADING the CalcVM cont  (let)
  | callS  : Bang.Val → CalcVM.Code → Instr    -- pop closure, apply to arg THREADING the CalcVM cont  (app/β)
  | getL   : Nat → Instr         -- local.get k   (free de Bruijn occurrence k)
  | setL   : Nat → Instr         -- local.set k
  -- ADT eliminators (sub-step 1a): branch on a sum scrutinee / destructure a pair. Like `bindS`,
  -- carry the residual branch `Comp`s AND the CalcVM continuation (re-compiled+threaded at runtime);
  -- a real WASM backend lowers these to `br_table` over the boxed sum tag / a tuple projection.
  -- Scrutinee is in the instr (a closed value at runtime), matching CalcVM's `CASE`/`SPLIT`.
  | caseS  : Bang.Val → Comp → Comp → CalcVM.Code → Instr   -- sum elim: inl/inr ⇒ run matching branch threading cont
  | splitS : Bang.Val → Comp → CalcVM.Code → Instr          -- product elim: pair ⇒ run N[fst][snd] threading cont
  -- effect handlers (sub-step 1b). The CURRENT stack-switching Explainer shape:
  --   markH  = install a handler boundary = `(cont.new $ct)` capturing the OUTER continuation
  --            (resume target on a zero-shot abort), carrying the post-handle resume code.
  --   unmarkH = pop the boundary on a normal return (handler-return = identity, Q6).
  --   opH ℓ op v = perform op = `suspend $tag` for a RESUMPTIVE op (state get/put — `(on $tag
  --            $label)` resumes in place) OR a zero-shot unwind for a `throws` op. The tracer
  --            effect (ADR-0025 state) is the RESUMPTIVE path → plain suspend/resume (NOT
  --            resume_throw, unlanded in Wasmtime #10248).
  -- shape: logsem/iris-wasmfx opsem — `resume`/`suspend`/`cont.new` (stack-switching Explainer).
  -- route-B (ADR-0052): `markH` DEFERS, mirroring `bindS` — it carries the RAW handler + RAW body
  -- `Comp` + the CalcVM continuation `cc`, because the body's `perform` caps are unresolved `vvar`s
  -- until `wexec` mints the fresh identity `g` and substitutes `vcap g h.label`. At runtime `wexec`
  -- pushes the frame keyed by `g` and RE-COMPILES `subst (vcap g h.label) M` (the SUBST/APP pattern).
  | markH   : Handler → Comp → CalcVM.Code → Instr  -- DEFER: mint id + recompile the subst body
  | unmarkH : Instr                           -- pop the handler boundary (normal return)
  -- route-B: `opH` is IDENTITY-keyed (`Nat`, not label) — dispatch resolves the frame by capability
  -- identity `n` (mirroring `idDispatch`/`splitAtId`), matching the route-B CalcVM `OP n op v`.
  | opH     : Nat → Bang.OpId → Bang.Val → Instr  -- perform op (identity-keyed resume/unwind)
  deriving Inhabited

abbrev Code := List Instr

/-- The WASM operand stack holds runtime values (`Wasmfx.Val`). -/
abbrev VStack := List Val

/-- A saved handler boundary on the WASM handler-stack — the injection of CalcVM's
`HFrame` (`Bang/CalcVM.lean`): the handler + the OUTER continuation (WASM code ×
operand stack) to resume on a zero-shot abort. Mirrors the stack-switching
`cont`-reference captured at the handler boundary. -/
structure HFrame where
  id         : Nat          -- route-B: the minted generative identity; lookups resolve by it
  handler    : Handler
  savedCode  : Code
  savedStack : VStack

abbrev HStack := List HFrame

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

/- `lowerInstr`/`lowerCode`: lower a calculated `Bang.Code` to WASM opcodes.
RET/LAMI map 1:1; MARK/UNMARK/OP are the handler opcodes (sub-step 1b); THROW is
never compiled. The RESIDUAL opcodes SUBST/APP/CASE/SPLIT each CARRY the CalcVM
continuation `c` (the tail) so a re-compiled `handle` body captures the TRUE outer
continuation in its `markH` (the AsmFX epilogue annotation — Lindley et al. 2025
§1.3). Since the residual recompile consumes the whole tail (mirroring `exec`'s
`compile (subst …) c`), a residual `lowerInstr i c rest` SUBSUMES the tail
(`lowerInstr (SUBST N) c rest = [bindS N c]`, DROPPING `rest = lowerCode c`).

`lowerCode` recurses STRUCTURALLY on the list (`i :: c => lowerInstr i c (lowerCode
c)`); `lowerInstr` is a non-recursive constructor-match (its only `lowerCode` is on
the structurally-smaller MARK payload `cr`). BOTH reduce by `rfl` — the prior
single-function form, which matched the head constructor THROUGH the cons
(`.SUBST N :: c => …`), compiled to a non-reducing matcher and broke `rfl` on every
handler probe (the build caught it). Mutual because `MARK` lowers a nested `Code`. -/
mutual
def lowerInstr (i : CalcVM.Instr) (c : CalcVM.Code) (rest : Wasmfx.Code) : Wasmfx.Code :=
  match i with
  | .RET v        => .const v :: rest
  | .LAMI M       => .clos M :: rest
  | .SUBST N      => [.bindS N c]            -- subsumes the tail (re-compile threads `c`)
  | .APP v        => [.callS v c]
  | .CASE w N₁ N₂ => [.caseS w N₁ N₂ c]      -- sub-step 1a (ADT)
  | .SPLIT w N    => [.splitS w N c]
  -- route-B: HANDLE DEFERS like SUBST — subsume the tail, carry the raw body `M` + CalcVM cont `c`.
  | .HANDLE h M   => [.markH h M c]
  | .UNMARK       => .unmarkH :: rest
  | .OP n op v    => .opH n op v :: rest      -- identity-keyed
  | .THROW _ _ _  => rest                      -- never compiled (no-op)
def lowerCode : CalcVM.Code → Wasmfx.Code
  | []      => []
  | i :: c  => lowerInstr i c (lowerCode c)
end

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

/-! #### WASM handler-stack helpers (sub-step 1b) — mirror exec's exactly.

`wStateUpdate`/`wUnwindFind` are the WASM analogs of CalcVM's
`stateUpdate`/`unwindFind` (`Bang/CalcVM.lean`), operating on the WASM `HStack`.
They are STRUCTURALLY IDENTICAL (same recursion on the frame list, same handler
match) — only the saved code/stack carried in the kept/restored frames are WASM
rather than CalcVM. This 1:1 mirror is what keeps `exec_wexec_sim` a clean
lockstep: `injHStack` commutes with both (proven in the handler-commutation
lemmas). -/
def wStateUpdate : Nat → Bang.OpId → Bang.Val → HStack → Option (Bang.Val × HStack)
  | _, _, _, []       => none
  | n, op, v, fr :: hs =>
      match fr.handler with
      | .state ℓ0 s =>
          if fr.id = n then
            if op = "get" then some (s, fr :: hs)
            else if op = "put" then some (.vunit, { fr with handler := .state ℓ0 v } :: hs)
            else none
          else (wStateUpdate n op v hs).map (fun p => (p.1, fr :: p.2))
      | _ => (wStateUpdate n op v hs).map (fun p => (p.1, fr :: p.2))

/-- WASM analog of CalcVM's `txnUpdate` (ADR-0030 transaction resume): find the nearest
`transaction ℓ`-frame, service a txn op (`newTVar`/`readTVar`/`writeTVar`) via `txnService`
IN PLACE (thread the updated heap `Θ'`), and RESUME. STRUCTURALLY IDENTICAL to CalcVM's
`txnUpdate` (same recursion, same `txnService` on `Bang.Val`/`List Bang.Val`) — the WASM
HStack shares the `Handler`, so the frame's heap lives in the shared `transaction ℓ0 Θ`.
This is the OP-arm branch that closes the txn-resume gap (operator ruling: verify txn in
v1, headline ungated). -/
def wTxnUpdate : Nat → Bang.OpId → Bang.Val → HStack → Option (Bang.Val × HStack)
  | _, _, _, []       => none
  | n, op, v, fr :: hs =>
      match fr.handler with
      | .transaction ℓ0 Θ =>
          if fr.id = n then
            if CalcVM.isTxnOp op then
              let (r, Θ') := CalcVM.txnService op v Θ
              some (r, { fr with handler := .transaction ℓ0 Θ' } :: hs)
            else none
          else (wTxnUpdate n op v hs).map (fun p => (p.1, fr :: p.2))
      | _ => (wTxnUpdate n op v hs).map (fun p => (p.1, fr :: p.2))

/-- WASM analog of CalcVM's `unwindFind` (throws-only abort target): the nearest
`throws ℓ`-frame's saved OUTER continuation. -/
def wUnwindFind : Nat → Bang.OpId → HStack → Option (Code × VStack × HStack)
  | _, _, [] => none
  | n, op, fr :: hs =>
      match fr.handler with
      | .throws _ => if fr.id = n ∧ op = "raise" then some (fr.savedCode, fr.savedStack, hs)
                     else (wUnwindFind n op hs).map (fun p => (p.1, p.2.1, p.2.2))
      | _ => (wUnwindFind n op hs).map (fun p => (p.1, p.2.1, p.2.2))

def wexec : Nat → Nat → Code → VStack → HStack → Option VStack
  | 0,          _, _,              _, _ => none
  | Nat.succ _, _, [],             s, _ => some s
  | Nat.succ f, g, .const v :: c,  s, hs => wexec f g c (compileV v :: s) hs
  | Nat.succ f, g, .clos M :: c,   s, hs => wexec f g c (.clos M :: s) hs
  -- RESIDUAL arms: re-`compile` `subst …` THREADING the carried CalcVM continuation `cc`, then lower
  -- the WHOLE thing — exactly `exec`'s `compile (subst …) cc`. A re-compiled `handle` body's `markH`
  -- now captures the TRUE outer continuation `cc` (the model-soundness fix). The `:: _` tail is empty
  -- (`lowerCode` subsumes it into the instr), so nothing is stranded. `g` threads unchanged (pure).
  | Nat.succ f, g, .bindS N cc :: _,  s, hs =>
      match s with
      | w :: s' => wexec f g (lowerCode (CalcVM.compile (Comp.subst (recoverV w) N) cc)) s' hs
      | _       => none
  | Nat.succ f, g, .callS v cc :: _,  s, hs =>
      match s with
      | .clos N :: s' => wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) cc)) s' hs
      | _             => none
  | Nat.succ f, g, .getL _ :: c,   s, hs => wexec f g c s hs
  | Nat.succ f, g, .setL _ :: c,   s, hs => wexec f g c s hs
  -- ADT eliminators (sub-step 1a): scrutinee in the instr; re-compile the chosen branch (cont threaded).
  | Nat.succ f, g, .caseS w N₁ N₂ cc :: _, s, hs =>
      match w with
      | .inl v => wexec f g (lowerCode (CalcVM.compile (Comp.subst v N₁) cc)) s hs
      | .inr v => wexec f g (lowerCode (CalcVM.compile (Comp.subst v N₂) cc)) s hs
      | _      => none
  | Nat.succ f, g, .splitS w N cc :: _, s, hs =>
      match w with
      | .pair v u => wexec f g (lowerCode (CalcVM.compile (Comp.subst v (Comp.subst (Val.shift u) N)) cc)) s hs
      | _         => none
  -- effect handlers (sub-step 1b): mirror exec's HANDLE/UNMARK/OP arms (route-B, identity-keyed).
  -- HANDLE MINTS `id := g`, recurses at `g+1`, pushes the frame keyed by `g` (savedCode = `lowerCode cc`,
  -- the lowered abort target Kₒ), and RE-COMPILES `subst (vcap g h.label) M` before `UNMARK :: cc` —
  -- exactly `exec`'s HANDLE arm, lowered. The body's `perform`s resolve to identity-keyed `opH`s.
  | Nat.succ f, g, .markH h M cc :: _, s, hs =>
      let id := g
      wexec f (g+1)
        (lowerCode (CalcVM.compile (Comp.subst (.vcap id h.label) M) (CalcVM.Instr.UNMARK :: cc))) s
        ({ id := id, handler := h, savedCode := lowerCode cc, savedStack := s } :: hs)
  | Nat.succ f, g, .unmarkH :: c, s, hs =>
      match hs with
      | _ :: hs' => wexec f g c s hs'
      | []       => none
  | Nat.succ f, g, .opH n op v :: c, s, hs =>
      -- OP dispatch mirrors exec EXACTLY: stateUpdate → txnUpdate → unwindFind, by identity `n`.
      match wStateUpdate n op v hs with
      | some (r, hs') => wexec f g c (compileV r :: s) hs'         -- RESUME (state): continue c with ret r
      | none =>
          match wTxnUpdate n op v hs with
          | some (r, hs') => wexec f g c (compileV r :: s) hs'     -- RESUME (txn): continue c with ret r
          | none =>
              match wUnwindFind n op hs with
              | some (c', s', hs') => wexec f g c' (compileV v :: s') hs'  -- ABORT to (Kₒ, ret v)
              | none               => none

/-- Run a compiled module to a single value on the operand stack. The closed
program starts on the empty stack + empty handler stack; `done` = a singleton. -/
def run (fuel : Nat) (m : Module) : Result Val :=
  match wexec fuel 0 m.body [] [] with     -- route-B: the mint counter starts at 0 (mirrors `exec`/`evalD`)
  | some [v] => .done v
  | some _   => .stuck
  | none     => .oom

/-! ### The pure fragment (Milestone A scope)

`Comp.Pure`/`Val.Pure` carve out the EFFECT-FREE fragment the compiler covers:
the pure CBPV core (`ret · letC · force/vthunk · lam · app`) PLUS the ADT formers
(`inl/inr/pair/fold`) and eliminators (`case/split/unfold`, ADR-0029) — Milestone
B sub-step (1a). NO `up`/`handle` (the effect ops — sub-step 1b), NO `oom`/`wrong`.
A thunk body must be pure (run on `force`); the predicates are mutually recursive.
ADT scrutinees may be open (`vvar`, substituted before the eliminator steps), so
`Val.Pure` accepts variables. -/
mutual
def Comp.Pure : Comp → Prop
  | .ret v          => Val.Pure v
  | .letC M N       => Comp.Pure M ∧ Comp.Pure N
  | .force (.vthunk M) => Comp.Pure M    -- `force` only steps on a thunk (closed-focus)
  | .force _        => False
  | .lam M          => Comp.Pure M
  | .app M v        => Comp.Pure M ∧ Val.Pure v
  -- ADT eliminators (ADR-0029, sub-step 1a): scrutinee + each branch pure.
  | .case v N₁ N₂   => Val.Pure v ∧ Comp.Pure N₁ ∧ Comp.Pure N₂
  | .split v N      => Val.Pure v ∧ Comp.Pure N
  | .unfold v       => Val.Pure v
  | _               => False
def Val.Pure : Bang.Val → Prop
  | .vunit        => True
  | .vint _       => True
  | .vvar _       => True
  | .vthunk M     => Comp.Pure M
  -- ADT formers (ADR-0029, sub-step 1a): inert; purity threads into payloads.
  | .inl v        => Val.Pure v
  | .inr v        => Val.Pure v
  | .pair v w     => Val.Pure v ∧ Val.Pure w
  | .fold v       => Val.Pure v
  | .vcap _ _     => False        -- route-B: a capability is NOT in the pure (handler-free) fragment
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
  -- ADT eliminators (sub-step 1a): the residual branch(es) re-compiled at runtime must be pure.
  | .CASE w N₁ N₂ => Val.Pure w ∧ Comp.Pure N₁ ∧ Comp.Pure N₂
  | .SPLIT w N => Val.Pure w ∧ Comp.Pure N
  | _        => False

def CodePure (code : CalcVM.Code) : Prop := ∀ i ∈ code, InstrPure i

/-! #### Handler simulation invariant (`InstrOk`/`CodeOk`) — the FULL handler set

The handler simulation (`exec_wexec_sim_ok`, dropping `CodePure`) holds for the WHOLE
handler set — state · throws · transaction (operator ruling: verify txn in v1, headline
UNGATED). `wexec`'s OP arm now services `wStateUpdate → wTxnUpdate → wUnwindFind`,
exec-identical, so a txn op RESUMES (not aborts). With txn verified, the ONLY constraint
the simulation needs is `THROW`-freedom: `exec`'s `THROW` arm unwinds, but `compile` NEVER
emits `THROW` (it is an internal `exec` transition target — `lowerCode (THROW :: c)` drops
it), so any `compile`-output is `THROW`-free (`compile_ok`). No value/handler constraints
at all — all handlers + all values are in scope. `InstrOk i` = "`i` is not `THROW`" (with
`MARK`'s saved code recursively `THROW`-free); `CodeOk` = every instruction `InstrOk`. -/
-- route-B: the `.MARK _ cr => CodeOk cr` recursive obligation DISSOLVES — `HANDLE h M` carries a RAW
-- `Comp` body (not pre-compiled code), so there is no nested `Code` to constrain THROW-free; the body's
-- THROW-freedom comes from `compile_no_throw` when `wexec` re-compiles it. `InstrOk i` = "`i` is not THROW".
def InstrOk : CalcVM.Instr → Prop
  | .THROW _ _ _ => False          -- never compiled; resuming `[]`/dropping it would be unsound
  | _            => True
def CodeOk : CalcVM.Code → Prop
  | []     => True
  | i :: c => InstrOk i ∧ CodeOk c

theorem CodeOk_iff_forall (code : CalcVM.Code) : CodeOk code ↔ ∀ i ∈ code, InstrOk i := by
  induction code with
  | nil => simp [CodeOk]
  | cons i c ih => simp only [CodeOk, List.forall_mem_cons, ih]

/-- Pointwise injection of `exec`'s terminal-stack onto the WASM operand stack. -/
def injStack (s : CalcVM.Stack) : VStack := s.map injTerminal

/-- Injection of a CalcVM handler frame / handler stack onto the WASM ones: the
handler is shared, the saved code/stack are lowered/injected. The relating
invariant `whs = injHStack hs` is what makes `exec_wexec_sim`'s handler arms a
lockstep (the WASM helpers `wStateUpdate`/`wUnwindFind` commute with it). -/
def injHFrame (fr : CalcVM.HFrame) : HFrame :=
  { id := fr.id, handler := fr.handler, savedCode := lowerCode fr.savedCode, savedStack := injStack fr.savedStack }

def injHStack (hs : CalcVM.HStack) : HStack := hs.map injHFrame

/-! #### Handler-helper commutation: the WASM helpers mirror exec's under `injHStack`.

`wStateUpdate`/`wUnwindFind` are STRUCTURALLY IDENTICAL to CalcVM's
`stateUpdate`/`unwindFind`, so they commute with `injHStack` — the resume/abort
result value is the SAME `Bang.Val`, and the returned handler stack is the
injection of exec's. These are what make the `opH` simulation arm a lockstep. -/

theorem wStateUpdate_comm (n : Nat) (op : Bang.OpId) (v : Bang.Val) :
    ∀ {hs : CalcVM.HStack} {r hs'}, CalcVM.stateUpdate n op v hs = some (r, hs') →
      wStateUpdate n op v (injHStack hs) = some (r, injHStack hs') := by
  intro hs
  induction hs with
  | nil => intro r hs' h; simp [CalcVM.stateUpdate] at h
  | cons fr hs ih =>
      intro r hs' h
      simp only [injHStack, List.map_cons, wStateUpdate, injHFrame]
      simp only [CalcVM.stateUpdate] at h
      cases hfr : fr.handler with
      | state ℓ0 s =>
          rw [hfr] at h
          by_cases hid : fr.id = n
          · simp only [hid, if_pos rfl] at h
            by_cases hg : op = "get"
            · subst hg; simp only [if_pos rfl, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [wStateUpdate, injHStack, injHFrame, hfr, hid]
            · simp only [if_neg hg] at h
              by_cases hp : op = "put"
              · subst hp; simp only [if_pos rfl, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [wStateUpdate, injHStack, injHFrame, hfr, hid, hg]
              · simp only [if_neg hp] at h; simp at h
          · simp only [hid, if_neg hid] at h
            cases hrec : CalcVM.stateUpdate n op v hs with
            | none => rw [hrec] at h; simp at h
            | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp only [injHStack] at ih ⊢; rw [ih hrec]; simp [injHFrame, hfr, hid]
      | throws ℓ0 =>
          rw [hfr] at h
          cases hrec : CalcVM.stateUpdate n op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp only [injHStack] at ih ⊢; rw [ih hrec]; simp [injHFrame, hfr]
      | transaction ℓ0 Θ =>
          rw [hfr] at h
          cases hrec : CalcVM.stateUpdate n op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp only [injHStack] at ih ⊢; rw [ih hrec]; simp [injHFrame, hfr]

theorem wUnwindFind_comm (n : Nat) (op : Bang.OpId) :
    ∀ {hs : CalcVM.HStack} {c' s' hs'}, CalcVM.unwindFind n op hs = some (c', s', hs') →
      wUnwindFind n op (injHStack hs) = some (lowerCode c', injStack s', injHStack hs') := by
  intro hs
  induction hs with
  | nil => intro c' s' hs' h; simp [CalcVM.unwindFind] at h
  | cons fr hs ih =>
      intro c' s' hs' h
      simp only [injHStack, List.map_cons, wUnwindFind, injHFrame]
      simp only [CalcVM.unwindFind] at h
      cases hfr : fr.handler with
      | throws ℓ0 =>
          rw [hfr] at h
          by_cases hcond : fr.id = n ∧ op = "raise"
          · simp only [if_pos hcond] at h ⊢
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; simp [injHStack, injHFrame]
          · simp only [if_neg hcond] at h ⊢
            cases hrec : CalcVM.unwindFind n op hs with
            | none => rw [hrec] at h; simp at h
            | some p => obtain ⟨pc, ps, phs⟩ := p
                        rw [hrec] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        simp only [injHStack] at ih ⊢; rw [ih hrec]; simp
      | state ℓ0 s =>
          rw [hfr] at h
          cases hrec : CalcVM.unwindFind n op hs with
          | none => rw [hrec] at h; simp at h
          | some p => obtain ⟨pc, ps, phs⟩ := p
                      rw [hrec] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      simp only [injHStack] at ih ⊢; rw [ih hrec]; simp
      | transaction ℓ0 Θ =>
          rw [hfr] at h
          cases hrec : CalcVM.unwindFind n op hs with
          | none => rw [hrec] at h; simp at h
          | some p => obtain ⟨pc, ps, phs⟩ := p
                      rw [hrec] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      simp only [injHStack] at ih ⊢; rw [ih hrec]; simp

/-! #### Purity preservation under shift / subst (autosubst-style, structural) -/

mutual
theorem Val.shiftFrom_pure (k : Nat) : ∀ {t : Bang.Val}, Val.Pure t → Val.Pure (Val.shiftFrom k t)
  | .vunit, _   => by simp [Val.shiftFrom, Val.Pure]
  | .vint _, _  => by simp [Val.shiftFrom, Val.Pure]
  | .vvar i, _  => by
      by_cases hi : i < k <;> simp [Val.shiftFrom, hi, Val.Pure]
  | .vthunk M, h => by
      simp only [Val.shiftFrom, Val.Pure] at h ⊢; exact Comp.shiftFrom_pure k h
  | .inl w, h => by
      simp only [Val.shiftFrom, Val.Pure] at h ⊢; exact Val.shiftFrom_pure k h
  | .inr w, h => by
      simp only [Val.shiftFrom, Val.Pure] at h ⊢; exact Val.shiftFrom_pure k h
  | .pair w₁ w₂, h => by
      simp only [Val.shiftFrom, Val.Pure] at h ⊢
      exact ⟨Val.shiftFrom_pure k h.1, Val.shiftFrom_pure k h.2⟩
  | .fold w, h => by
      simp only [Val.shiftFrom, Val.Pure] at h ⊢; exact Val.shiftFrom_pure k h
  | .vcap _ _, h => by simp only [Val.Pure] at h   -- vacuous: a cap is not pure
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
  | .case w N₁ N₂, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢
      exact ⟨Val.shiftFrom_pure k h.1, Comp.shiftFrom_pure (k+1) h.2.1, Comp.shiftFrom_pure (k+1) h.2.2⟩
  | .split w N, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢
      exact ⟨Val.shiftFrom_pure k h.1, Comp.shiftFrom_pure (k+2) h.2⟩
  | .unfold w, h => by
      simp only [Comp.shiftFrom, Comp.Pure] at h ⊢; exact Val.shiftFrom_pure k h
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
  | .inl w, h => by
      simp only [Val.substFrom, Val.Pure] at h ⊢; exact Val.substFrom_pure k hv h
  | .inr w, h => by
      simp only [Val.substFrom, Val.Pure] at h ⊢; exact Val.substFrom_pure k hv h
  | .pair w₁ w₂, h => by
      simp only [Val.substFrom, Val.Pure] at h ⊢
      exact ⟨Val.substFrom_pure k hv h.1, Val.substFrom_pure k hv h.2⟩
  | .fold w, h => by
      simp only [Val.substFrom, Val.Pure] at h ⊢; exact Val.substFrom_pure k hv h
  | .vcap _ _, h => by simp only [Val.Pure] at h   -- vacuous: a cap is not pure
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
  | .case w N₁ N₂, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢
      exact ⟨Val.substFrom_pure k hv h.1,
             Comp.substFrom_pure (k+1) (Val.shiftFrom_pure 0 hv) h.2.1,
             Comp.substFrom_pure (k+1) (Val.shiftFrom_pure 0 hv) h.2.2⟩
  | .split w N, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢
      exact ⟨Val.substFrom_pure k hv h.1,
             Comp.substFrom_pure (k+2) (Val.shiftFrom_pure 0 (Val.shiftFrom_pure 0 hv)) h.2⟩
  | .unfold w, h => by
      simp only [Comp.substFrom, Comp.Pure] at h ⊢; exact Val.substFrom_pure k hv h
end

/-- `subst v N` stays pure when both `v` and `N` are. The β/let reduct purity that
keeps the simulation's recursive `compile (subst …)` inside the pure fragment. -/
theorem subst_pure {v : Bang.Val} {N : Comp} (hv : Val.Pure v) (hN : Comp.Pure N) :
    Comp.Pure (Comp.subst v N) :=
  Comp.substFrom_pure 0 hv hN

/-! #### `compile` purity (residual reducts stay pure)

NOTE: `lowerCode` is NO LONGER a `++`-homomorphism. The residual opcodes
(SUBST/APP/CASE/SPLIT) SUBSUME their tail into a single threaded-continuation
instr (`lowerCode (SUBST N :: c) = [bindS N c]`), so `lowerCode (a ++ b) ≠
lowerCode a ++ lowerCode b` when `a` ends in a residual opcode. The old
`lowerCode_append` lemma (and its `compile_append` companion in the residual
arms) was the workaround for `wexec`'s former `compile … [] ++ c` shape — that
shape is exactly the model defect; with the continuation threaded, the residual
`wexec`/`exec` equality is DEFINITIONAL and needs no append homomorphism. -/

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
  -- ADT eliminators (sub-step 1a): `case`/`split` cons ONE instruction (no recursion into
  -- branches — they re-compile at runtime); `unfold (fold v)` emits `RET v`, other `unfold`
  -- emits nothing. All trivially `x :: c = (x :: []) ++ c` (or `c = [] ++ c`).
  | .case w N₁ N₂, _, c => by simp [CalcVM.compile]
  | .split w N, _, c => by simp [CalcVM.compile]
  | .unfold w, _, c => by cases w <;> simp [CalcVM.compile]

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
  -- ADT eliminators: `case`/`split` cons their `CASE`/`SPLIT` instr (pure by `InstrPure`);
  -- `unfold (fold v)` conses `RET v` (pure since `v` is pure); other `unfold` emits nothing.
  | .case w N₁ N₂, h, c, hc => by
      simp only [Comp.Pure] at h
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa only [InstrPure] using h
      · exact hc i hi
  | .split w N, h, c, hc => by
      simp only [Comp.Pure] at h
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa only [InstrPure] using h
      · exact hc i hi
  | .unfold w, h, c, hc => by
      cases w with
      | fold v =>
          intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
          rcases hi with rfl | hi
          · simpa only [InstrPure, Comp.Pure] using h
          · exact hc i hi
      | _ => simp only [CalcVM.compile]; exact hc   -- emits nothing (open scrutinee)

/-! #### `compile_ok` — `compile`-output is `CodeOk` (THROW-free), for ANY source

With txn verified there is NO source constraint: `compile` NEVER emits `THROW`, and every
other opcode it emits is `InstrOk` (`MARK`'s saved code is the passed continuation, which
is `CodeOk` by recursion). So `compile M c` is `CodeOk` whenever `c` is — for any `M`.
Structural induction on `M` mirroring `compile`'s arms; the `handle` arm conses a `MARK h c`
(InstrOk = `CodeOk c`, from `hc`) and recurses on `compile M (UNMARK :: c)`. -/
theorem compile_ok_mem : ∀ (M : Comp) {c : CalcVM.Code}, (∀ i ∈ c, InstrOk i) →
    ∀ i ∈ CalcVM.compile M c, InstrOk i
  | .ret v, c, hc => by
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .lam M, c, hc => by
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .force w, c, hc => by
      cases w with
      | vthunk M => simp only [CalcVM.compile]; exact compile_ok_mem M hc
      | _ => simp only [CalcVM.compile]; exact hc
  | .letC M N, c, hc => by
      simp only [CalcVM.compile]
      refine compile_ok_mem M ?_
      intro i hi; simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .app M w, c, hc => by
      simp only [CalcVM.compile]
      refine compile_ok_mem M ?_
      intro i hi; simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .perform cap op v, c, hc => by
      -- route-B: `compile (perform (vcap n ℓ) op v) c = OP n op v :: c` (OP is InstrOk), else `= c`.
      intro i hi
      cases cap with
      | vcap m ℓ =>
          simp only [CalcVM.compile, List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact trivial
          · exact hc i hi
      | _ => exact hc i (by simpa only [CalcVM.compile] using hi)
  | .handle hh M, c, hc => by
      -- route-B: `compile (handle hh M) c = HANDLE hh M :: c` — DEFERS the raw body (no recursive
      -- compile of M), and `InstrOk (HANDLE …) = True`, so the arm is the same shape as `.perform`/`.case`.
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .case w N₁ N₂, c, hc => by
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .split w N, c, hc => by
      intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact trivial
      · exact hc i hi
  | .unfold w, c, hc => by
      cases w with
      | fold v =>
          intro i hi; simp only [CalcVM.compile, List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact trivial
          · exact hc i hi
      | _ => simp only [CalcVM.compile]; exact hc
  | .oom, c, hc => by simp only [CalcVM.compile]; exact hc
  | .wrong s, c, hc => by simp only [CalcVM.compile]; exact hc

/-- `compile M c` is `CodeOk` (THROW-free) whenever `c` is — for ANY source `M`. -/
theorem compile_ok (M : Comp) {c : CalcVM.Code} (hc : CodeOk c) :
    CodeOk (CalcVM.compile M c) :=
  (CodeOk_iff_forall _).mpr (compile_ok_mem M ((CodeOk_iff_forall c).mp hc))

/-- **The load-bearing premise, BUILD-ENFORCED:** `compile` NEVER emits a `THROW`. This is the
fact the whole `NoThrow`-is-total argument rests on (THROW is an internal `exec` transition
target, NOT a compile output — `compile`'s `up` arm emits `OP`, never `THROW`). Stated directly
+ legibly at `c = []` (a CLOSED program's compilation, exactly what `compileC` runs): NO top-level
instruction of `compile M []` is a `THROW`. Derived from `compile_ok` (so `CodeOk` is the witness):
if any `compile` arm could emit `THROW`, `compile_ok`/`compile_ok_mem` fails to build (since
`InstrOk (.THROW …) = False`), so `CodeOk`-of-compile-output — and the whole handler simulation's
totality — is GATED on this, not assumed. (`CodeOk` is the STRONGER nested form: it forbids `THROW`
inside `MARK` saved code too; this corollary is the legible headline of that fact.) -/
theorem compile_no_throw (M : Comp) :
    ∀ ℓ op v, CalcVM.Instr.THROW ℓ op v ∉ CalcVM.compile M [] := by
  intro ℓ op v hmem
  have hok : ∀ i ∈ CalcVM.compile M [], InstrOk i :=
    (CodeOk_iff_forall _).mp (compile_ok M (by simp [CodeOk]))
  exact (by simpa only [InstrOk] using hok _ hmem : False)

/-! #### The lockstep simulation `exec ⟹ wexec`

For PURE-spine code at the EMPTY handler stack, every successful `exec` run is
mirrored by a `wexec` run at the SAME fuel on the injected stacks. Fuel aligns
1:1 (a pure CalcVM instr lowers to exactly one WASM instr). The SUBST/APP arms
recover the popped value (`compileV_recoverV`) and re-compile the SAME residual,
THREADING the carried CalcVM continuation `c` (the threaded-cont rep) so the
`wexec`/`exec` recompiles coincide DEFINITIONALLY; the recompiled code stays pure
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

/-- A handler frame is pure when its saved continuation (code + stack) is — the
abort/UNMARK paths resume it, so the recursive simulation needs it pure. The
handler itself is `state`/`throws` (effect-free carriers; state's stored value is
pure for a well-typed closed program — threaded as part of the invariant). -/
def HFramePure (fr : CalcVM.HFrame) : Prop :=
  CodePure fr.savedCode ∧ StackPure fr.savedStack

def HStackPure (hs : CalcVM.HStack) : Prop := ∀ fr ∈ hs, HFramePure fr

/-! #### `HStackOk` — the handler-capable simulation's ONLY invariant (full handler set)

With txn verified, the simulation needs NO value/handler/stack constraint — only that
every saved handler frame's continuation is THROW-free (`CodeOk`), so an abort-resume
runs THROW-free code. No `TerminalOk`/`StackOk` (the operand stack is unconstrained),
no handler constraint (all handlers in scope). `HFrameOk fr = CodeOk fr.savedCode`. -/
def HFrameOk (fr : CalcVM.HFrame) : Prop := CodeOk fr.savedCode

def HStackOk (hs : CalcVM.HStack) : Prop := ∀ fr ∈ hs, HFrameOk fr

theorem exec_wexec_sim :
    ∀ (f g : Nat) (code : CalcVM.Code) (s s' : CalcVM.Stack) (hs : CalcVM.HStack),
      CodePure code → StackPure s → HStackPure hs →
      CalcVM.exec f g code s hs = some s' →
      wexec f g (lowerCode code) (injStack s) (injHStack hs) = some (injStack s') := by
  intro f
  induction f with
  | zero => intro g code s s' hs _ _ _ h; simp [CalcVM.exec] at h
  | succ f ih =>
    intro g code s s' hs hpure hsp hsph h
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
            simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
            exact ih g c (.ret v :: s) s' hs hc
              (fun t ht => by
                rcases List.mem_cons.mp ht with rfl | ht
                · simpa only [TerminalPure] using hv
                · exact hsp t ht) hsph h
        | LAMI M =>
            simp only [CalcVM.exec] at h
            have hM : Comp.Pure M := by simpa only [InstrPure] using hi
            simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
            exact ih g c (.lam M :: s) s' hs hc
              (fun t ht => by
                rcases List.mem_cons.mp ht with rfl | ht
                · simpa only [TerminalPure] using hM
                · exact hsp t ht) hsph h
        -- RESIDUAL arms: `wexec` now re-`compile`s THREADING the carried CalcVM continuation `c`,
        -- matching `exec`'s `compile (subst …) c` EXACTLY — no `compile_append`/`lowerCode_append`
        -- detour (those held only on the pure fragment; the threaded-cont rep makes the equality
        -- definitional, which is also what makes the model SOUND for handlers).
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
                    have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) c)) (injStack s0) (injHStack hs)
                        = some (injStack s') :=
                      ih g _ s0 s' hs (compile_pure hpu hc) hsp0 hsph h
                    simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
                    rw [compileV_recoverV]
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
                    have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) c)) (injStack s0) (injHStack hs)
                        = some (injStack s') :=
                      ih g _ s0 s' hs (compile_pure hpu hc) hsp0 hsph h
                    simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
                    simpa [injStack] using key
                | _ => simp at h
        | CASE w N₁ N₂ =>
            -- scrutinee in the instr; mirror exec's CASE (inl/inr ⇒ re-compile the branch).
            have hP : Val.Pure w ∧ Comp.Pure N₁ ∧ Comp.Pure N₂ := by simpa only [InstrPure] using hi
            simp only [CalcVM.exec] at h
            cases w with
            | inl v =>
                have hpu : Comp.Pure (Comp.subst v N₁) :=
                  subst_pure (by simpa only [Val.Pure] using hP.1) hP.2.1
                have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N₁) c)) (injStack s) (injHStack hs)
                    = some (injStack s') := ih g _ s s' hs (compile_pure hpu hc) hsp hsph h
                simp only [lowerCode, lowerInstr, wexec, injStack]
                simpa [injStack] using key
            | inr v =>
                have hpu : Comp.Pure (Comp.subst v N₂) :=
                  subst_pure (by simpa only [Val.Pure] using hP.1) hP.2.2
                have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N₂) c)) (injStack s) (injHStack hs)
                    = some (injStack s') := ih g _ s s' hs (compile_pure hpu hc) hsp hsph h
                simp only [lowerCode, lowerInstr, wexec, injStack]
                simpa [injStack] using key
            | _ => simp [CalcVM.exec] at h
        | SPLIT w N =>
            have hP : Val.Pure w ∧ Comp.Pure N := by simpa only [InstrPure] using hi
            simp only [CalcVM.exec] at h
            cases w with
            | pair v u =>
                have hpu : Comp.Pure (Comp.subst v (Comp.subst (Val.shift u) N)) := by
                  have hvw : Val.Pure v ∧ Val.Pure u := by simpa only [Val.Pure] using hP.1
                  exact subst_pure hvw.1 (subst_pure (Val.shiftFrom_pure 0 hvw.2) hP.2)
                have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v (Comp.subst (Val.shift u) N)) c)) (injStack s) (injHStack hs)
                    = some (injStack s') := ih g _ s s' hs (compile_pure hpu hc) hsp hsph h
                simp only [lowerCode, lowerInstr, wexec, injStack]
                simpa [injStack] using key
            | _ => simp [CalcVM.exec] at h
        | _ => exact absurd hi (by simp [InstrPure])

/-! #### OP-arm preservation lemmas — `HStackOk` (THROW-free saved continuations)
threaded through state-resume / txn-resume / abort, plus the `none`-commutations the
3-way OP dispatch needs. With txn verified there are NO value/handler obligations — only
`CodeOk fr.savedCode`, which all three update operations preserve (they keep frames /
update a frame's stored value or heap in place, leaving `savedCode` untouched). All
structural inductions on `hs` mirroring the `stateUpdate`/`txnUpdate`/`unwindFind` defs. -/

/-- `stateUpdate` preserves `HStackOk`: it keeps every frame, only swapping a `state` frame's
stored VALUE (not its `savedCode`), so `CodeOk fr.savedCode` is preserved frame-wise. -/
theorem stateUpdate_hstackOk :
    ∀ {hs : CalcVM.HStack} {r hs'}, HStackOk hs → CalcVM.stateUpdate ℓ op v hs = some (r, hs') →
      HStackOk hs' := by
  intro hs
  induction hs with
  | nil => intro r hs' _ h; simp [CalcVM.stateUpdate] at h
  | cons fr hs ih =>
      intro r hs' hsh h
      have hfr : HFrameOk fr := hsh fr (by simp)
      have hsh0 : HStackOk hs := fun fr2 hfr2 => hsh fr2 (List.mem_cons_of_mem _ hfr2)
      simp only [CalcVM.stateUpdate] at h
      cases hfrh : fr.handler with
      | state ℓ0 s =>
          rw [hfrh] at h
          by_cases hid : fr.id = ℓ
          · simp only [hid, if_pos rfl] at h
            by_cases hg : op = "get"
            · subst hg; simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h; exact hsh
            · simp only [if_neg hg] at h
              by_cases hp : op = "put"
              · subst hp; simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, rfl⟩ := h
                intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                · exact hfr   -- savedCode unchanged by a put (only the handler value swaps)
                · exact hsh0 fr2 hfr2
              · simp only [if_neg hp] at h; simp at h
          · simp only [hid, if_neg hid] at h
            cases hrec : CalcVM.stateUpdate ℓ op v hs with
            | none => rw [hrec] at h; simp at h
            | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                        · exact hfr
                        · exact ih hsh0 hrec fr2 hfr2
      | throws ℓ0 =>
          rw [hfrh] at h
          cases hrec : CalcVM.stateUpdate ℓ op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                      · exact hfr
                      · exact ih hsh0 hrec fr2 hfr2
      | transaction ℓ0 Θ =>
          rw [hfrh] at h
          cases hrec : CalcVM.stateUpdate ℓ op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                      · exact hfr
                      · exact ih hsh0 hrec fr2 hfr2

/-- `txnUpdate` preserves `HStackOk` (same shape as `stateUpdate`: it swaps a `transaction`
frame's stored HEAP, not its `savedCode`). -/
theorem txnUpdate_hstackOk :
    ∀ {hs : CalcVM.HStack} {r hs'}, HStackOk hs → CalcVM.txnUpdate ℓ op v hs = some (r, hs') →
      HStackOk hs' := by
  intro hs
  induction hs with
  | nil => intro r hs' _ h; simp [CalcVM.txnUpdate] at h
  | cons fr hs ih =>
      intro r hs' hsh h
      have hfr : HFrameOk fr := hsh fr (by simp)
      have hsh0 : HStackOk hs := fun fr2 hfr2 => hsh fr2 (List.mem_cons_of_mem _ hfr2)
      simp only [CalcVM.txnUpdate] at h
      cases hfrh : fr.handler with
      | transaction ℓ0 Θ =>
          rw [hfrh] at h
          by_cases hid : fr.id = ℓ
          · simp only [hid, if_pos rfl] at h
            by_cases ht : CalcVM.isTxnOp op
            · simp only [ht, if_true] at h
              obtain ⟨_, rfl⟩ := h
              intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
              · exact hfr   -- savedCode unchanged (only the txn heap Θ swaps)
              · exact hsh0 fr2 hfr2
            · simp only [ht, if_false] at h; simp at h
          · simp only [hid, if_neg hid] at h
            cases hrec : CalcVM.txnUpdate ℓ op v hs with
            | none => rw [hrec] at h; simp at h
            | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                        · exact hfr
                        · exact ih hsh0 hrec fr2 hfr2
      | state ℓ0 s =>
          rw [hfrh] at h
          cases hrec : CalcVM.txnUpdate ℓ op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                      · exact hfr
                      · exact ih hsh0 hrec fr2 hfr2
      | throws ℓ0 =>
          rw [hfrh] at h
          cases hrec : CalcVM.txnUpdate ℓ op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      intro fr2 hfr2; rcases List.mem_cons.mp hfr2 with rfl | hfr2
                      · exact hfr
                      · exact ih hsh0 hrec fr2 hfr2

/-- `wStateUpdate = none` whenever `stateUpdate = none` (structurally identical helpers). -/
theorem wStateUpdate_comm_none (n : Nat) (op : Bang.OpId) (v : Bang.Val) :
    ∀ {hs : CalcVM.HStack}, CalcVM.stateUpdate n op v hs = none →
      wStateUpdate n op v (injHStack hs) = none := by
  intro hs
  induction hs with
  | nil => intro _; rfl
  | cons fr hs ih =>
      intro h
      simp only [injHStack, List.map_cons, wStateUpdate, injHFrame]
      simp only [CalcVM.stateUpdate] at h
      cases hfr : fr.handler with
      | state ℓ0 s =>
          simp only [hfr] at h ⊢
          by_cases hid : fr.id = n
          · simp only [hid, if_pos rfl] at h ⊢
            by_cases hg : op = "get"
            · subst hg; simp at h
            · simp only [if_neg hg] at h ⊢
              by_cases hp : op = "put"
              · subst hp; simp at h
              · simp only [if_neg hp] at h ⊢; rfl
          · simp only [hid, if_neg hid] at h ⊢
            cases hrec : CalcVM.stateUpdate n op v hs with
            | none => simp only [injHStack] at ih ⊢; rw [ih hrec]; rfl
            | some p => rw [hrec] at h; simp at h
      | throws ℓ0 =>
          simp only [hfr] at h ⊢
          cases hrec : CalcVM.stateUpdate n op v hs with
          | none => simp only [injHStack] at ih ⊢; rw [ih hrec]; rfl
          | some p => rw [hrec] at h; simp at h
      | transaction ℓ0 Θ =>
          simp only [hfr] at h ⊢
          cases hrec : CalcVM.stateUpdate n op v hs with
          | none => simp only [injHStack] at ih ⊢; rw [ih hrec]; rfl
          | some p => rw [hrec] at h; simp at h

/-- `wTxnUpdate` mirrors `txnUpdate` under `injHStack` (the resume case): the serviced value
and the threaded-heap frame stack are the SAME, modulo injection. The `some`-commutation
the txn-resume OP arm rides. -/
theorem wTxnUpdate_comm (n : Nat) (op : Bang.OpId) (v : Bang.Val) :
    ∀ {hs : CalcVM.HStack} {r hs'}, CalcVM.txnUpdate n op v hs = some (r, hs') →
      wTxnUpdate n op v (injHStack hs) = some (r, injHStack hs') := by
  intro hs
  induction hs with
  | nil => intro r hs' h; simp [CalcVM.txnUpdate] at h
  | cons fr hs ih =>
      intro r hs' h
      simp only [injHStack, List.map_cons, wTxnUpdate, injHFrame]
      simp only [CalcVM.txnUpdate] at h
      cases hfr : fr.handler with
      | transaction ℓ0 Θ =>
          simp only [hfr] at h ⊢
          by_cases hid : fr.id = n
          · simp only [hid, if_pos rfl] at h ⊢
            by_cases ht : CalcVM.isTxnOp op
            · simp only [ht, if_true] at h ⊢
              obtain ⟨rfl, rfl⟩ := h
              simp [injHStack, injHFrame, hfr]
            · simp only [ht, if_false] at h; simp at h
          · simp only [hid, if_neg hid] at h ⊢
            cases hrec : CalcVM.txnUpdate n op v hs with
            | none => rw [hrec] at h; simp at h
            | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp only [injHStack] at ih ⊢; rw [ih hrec]; simp [injHFrame, hfr]
      | state ℓ0 s =>
          simp only [hfr] at h ⊢
          cases hrec : CalcVM.txnUpdate n op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp only [injHStack] at ih ⊢; rw [ih hrec]; simp [injHFrame, hfr]
      | throws ℓ0 =>
          simp only [hfr] at h ⊢
          cases hrec : CalcVM.txnUpdate n op v hs with
          | none => rw [hrec] at h; simp at h
          | some p => rw [hrec] at h; simp only [Option.map_some, Option.some.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp only [injHStack] at ih ⊢; rw [ih hrec]; simp [injHFrame, hfr]

/-- `wTxnUpdate = none` whenever `txnUpdate = none`. The `none`-commutation the dispatch needs
to fall through from txn to abort. -/
theorem wTxnUpdate_comm_none (n : Nat) (op : Bang.OpId) (v : Bang.Val) :
    ∀ {hs : CalcVM.HStack}, CalcVM.txnUpdate n op v hs = none →
      wTxnUpdate n op v (injHStack hs) = none := by
  intro hs
  induction hs with
  | nil => intro _; rfl
  | cons fr hs ih =>
      intro h
      simp only [injHStack, List.map_cons, wTxnUpdate, injHFrame]
      simp only [CalcVM.txnUpdate] at h
      cases hfr : fr.handler with
      | transaction ℓ0 Θ =>
          simp only [hfr] at h ⊢
          by_cases hid : fr.id = n
          · simp only [hid, if_pos rfl] at h ⊢
            by_cases ht : CalcVM.isTxnOp op
            · simp only [ht, if_true] at h; simp at h
            · simp only [ht, if_false] at h ⊢; rfl
          · simp only [hid, if_neg hid] at h ⊢
            cases hrec : CalcVM.txnUpdate n op v hs with
            | none => simp only [injHStack] at ih ⊢; rw [ih hrec]; rfl
            | some p => rw [hrec] at h; simp at h
      | state ℓ0 s =>
          simp only [hfr] at h ⊢
          cases hrec : CalcVM.txnUpdate n op v hs with
          | none => simp only [injHStack] at ih ⊢; rw [ih hrec]; rfl
          | some p => rw [hrec] at h; simp at h
      | throws ℓ0 =>
          simp only [hfr] at h ⊢
          cases hrec : CalcVM.txnUpdate n op v hs with
          | none => simp only [injHStack] at ih ⊢; rw [ih hrec]; rfl
          | some p => rw [hrec] at h; simp at h

/-- `unwindFind` returns a saved frame's `savedCode`, which is `CodeOk` (the frame was `HFrameOk`). -/
theorem unwindFind_savedCode_codeOk :
    ∀ {hs : CalcVM.HStack} {c' s' hs'}, HStackOk hs →
      CalcVM.unwindFind ℓ op hs = some (c', s', hs') → CodeOk c' := by
  intro hs
  induction hs with
  | nil => intro c' s' hs' _ h; simp [CalcVM.unwindFind] at h
  | cons fr hs ih =>
      intro c' s' hs' hsh h
      have hfr : HFrameOk fr := hsh fr (by simp)
      have hsh0 : HStackOk hs := fun fr2 hfr2 => hsh fr2 (List.mem_cons_of_mem _ hfr2)
      simp only [CalcVM.unwindFind] at h
      cases hfrh : fr.handler with
      | throws ℓ0 =>
          rw [hfrh] at h
          by_cases hcatch : fr.id = ℓ ∧ op = "raise"
          · simp only [if_pos hcatch, Option.some.injEq] at h
            obtain ⟨rfl, _, _⟩ := h; exact hfr
          · simp only [if_neg hcatch] at h; exact ih hsh0 h
      | state ℓ0 s => rw [hfrh] at h; exact ih hsh0 h
      | transaction ℓ0 Θ => rw [hfrh] at h; exact ih hsh0 h

theorem unwindFind_hstackOk :
    ∀ {hs : CalcVM.HStack} {c' s' hs'}, HStackOk hs →
      CalcVM.unwindFind ℓ op hs = some (c', s', hs') → HStackOk hs' := by
  intro hs
  induction hs with
  | nil => intro c' s' hs' _ h; simp [CalcVM.unwindFind] at h
  | cons fr hs ih =>
      intro c' s' hs' hsh h
      have hsh0 : HStackOk hs := fun fr2 hfr2 => hsh fr2 (List.mem_cons_of_mem _ hfr2)
      simp only [CalcVM.unwindFind] at h
      cases hfrh : fr.handler with
      | throws ℓ0 =>
          rw [hfrh] at h
          by_cases hcatch : fr.id = ℓ ∧ op = "raise"
          · simp only [if_pos hcatch, Option.some.injEq] at h
            obtain ⟨_, _, rfl⟩ := h; exact hsh0
          · simp only [if_neg hcatch] at h; exact ih hsh0 h
      | state ℓ0 s => rw [hfrh] at h; exact ih hsh0 h
      | transaction ℓ0 Θ => rw [hfrh] at h; exact ih hsh0 h

/-! #### The handler-capable simulation `exec ⟹ wexec` (Piece A — FULL handler set)

`exec_wexec_sim_ok` drops the `CodePure` gate of `exec_wexec_sim` and runs under just
`CodeOk`/`HStackOk` (= THROW-freedom of the code and of every saved continuation). It
covers the WHOLE handler set — state · throws · transaction (operator ruling: verify txn,
headline ungated). It ADDS the MARK/UNMARK/OP arms; the OP arm does the 3-way dispatch
state-resume / txn-resume / abort, EXEC-IDENTICAL, discharged via the commutation lemmas
`wStateUpdate_comm`/`wTxnUpdate_comm`/`wUnwindFind_comm` (+ their `none` companions) and
`injHStack`. No purity/value invariant — `wexec` mirrors `exec` arm-for-arm, so each arm
is a definitional lockstep under the injection. `THROW` is excluded by `InstrOk` (`compile`
never emits it). The operand stack is unconstrained (injected pointwise by `injStack`). -/
theorem exec_wexec_sim_ok :
    ∀ (f g : Nat) (code : CalcVM.Code) (s s' : CalcVM.Stack) (hs : CalcVM.HStack),
      CodeOk code → HStackOk hs →
      CalcVM.exec f g code s hs = some s' →
      wexec f g (lowerCode code) (injStack s) (injHStack hs) = some (injStack s') := by
  intro f
  induction f with
  | zero => intro g code s s' hs _ _ h; simp [CalcVM.exec] at h
  | succ f ih =>
    intro g code s s' hs hok hsh h
    cases code with
    | nil =>
        simp only [CalcVM.exec, Option.some.injEq] at h; subst h
        simp [lowerCode, wexec]
    | cons i c =>
        have hi : InstrOk i := ((CodeOk_iff_forall _).mp hok) i (by simp)
        have hc : CodeOk c := (CodeOk_iff_forall _).mpr
          (fun j hj => ((CodeOk_iff_forall _).mp hok) j (List.mem_cons_of_mem _ hj))
        cases i with
        | RET v =>
            simp only [CalcVM.exec] at h
            simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
            exact ih g c (.ret v :: s) s' hs hc hsh h
        | LAMI M =>
            simp only [CalcVM.exec] at h
            simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
            exact ih g c (.lam M :: s) s' hs hc hsh h
        | SUBST N =>
            simp only [CalcVM.exec] at h
            cases s with
            | nil => simp at h
            | cons hd s0 =>
                cases hd with
                | ret v =>
                    have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) c)) (injStack s0) (injHStack hs)
                        = some (injStack s') := ih g _ s0 s' hs (compile_ok _ hc) hsh h
                    simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
                    rw [compileV_recoverV]
                    simpa [injStack] using key
                | _ => simp at h
        | APP v =>
            simp only [CalcVM.exec] at h
            cases s with
            | nil => simp at h
            | cons hd s0 =>
                cases hd with
                | lam N =>
                    have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N) c)) (injStack s0) (injHStack hs)
                        = some (injStack s') := ih g _ s0 s' hs (compile_ok _ hc) hsh h
                    simp only [lowerCode, lowerInstr, wexec, injStack, injTerminal, List.map_cons]
                    simpa [injStack] using key
                | _ => simp at h
        | CASE w N₁ N₂ =>
            simp only [CalcVM.exec] at h
            cases w with
            | inl v =>
                have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N₁) c)) (injStack s) (injHStack hs)
                    = some (injStack s') := ih g _ s s' hs (compile_ok _ hc) hsh h
                simp only [lowerCode, lowerInstr, wexec, injStack]
                simpa [injStack] using key
            | inr v =>
                have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v N₂) c)) (injStack s) (injHStack hs)
                    = some (injStack s') := ih g _ s s' hs (compile_ok _ hc) hsh h
                simp only [lowerCode, lowerInstr, wexec, injStack]
                simpa [injStack] using key
            | _ => simp [CalcVM.exec] at h
        | SPLIT w N =>
            simp only [CalcVM.exec] at h
            cases w with
            | pair v u =>
                have key : wexec f g (lowerCode (CalcVM.compile (Comp.subst v (Comp.subst (Val.shift u) N)) c)) (injStack s) (injHStack hs)
                    = some (injStack s') := ih g _ s s' hs (compile_ok _ hc) hsh h
                simp only [lowerCode, lowerInstr, wexec, injStack]
                simpa [injStack] using key
            | _ => simp [CalcVM.exec] at h
        -- route-B HANDLE (the spike-proven mint arm): exec mints id:=g, recurses at g+1, pushes
        -- {id:=g,…}; wexec's markH arm does the IDENTICAL mint; injHFrame carries id:=g, so the pushed
        -- frame is DEFINITIONALLY injHStack-related and the IH at g+1 on the recompiled body closes.
        | HANDLE hh M =>
            simp only [CalcVM.exec] at h
            simp only [lowerCode, lowerInstr, wexec]
            have hcUnmark : CodeOk (CalcVM.Instr.UNMARK :: c) := ⟨trivial, hc⟩
            have hsh' : HStackOk ({ id := g, handler := hh, savedCode := c, savedStack := s } :: hs) := by
              intro fr hfr; rcases List.mem_cons.mp hfr with rfl | hfr
              · exact hc
              · exact hsh fr hfr
            have key := ih (g+1)
              (CalcVM.compile (Comp.subst (.vcap g hh.label) M) (CalcVM.Instr.UNMARK :: c))
              s s' ({ id := g, handler := hh, savedCode := c, savedStack := s } :: hs)
              (compile_ok _ hcUnmark) hsh' h
            simpa only [injHStack, injHFrame, List.map_cons] using key
        | UNMARK =>
            simp only [CalcVM.exec] at h
            cases hs with
            | nil => simp at h
            | cons fr hs' =>
                have hsh' : HStackOk hs' := fun fr2 hfr2 => hsh fr2 (List.mem_cons_of_mem _ hfr2)
                simp only [lowerCode, lowerInstr, wexec, injHStack, List.map_cons]
                exact ih g c s s' hs' hc hsh' h
        | OP n op v =>
            -- 3-way dispatch, EXEC-IDENTICAL: stateUpdate → txnUpdate → unwindFind, by identity n.
            simp only [CalcVM.exec] at h
            simp only [lowerCode, lowerInstr, wexec]
            cases hsu : CalcVM.stateUpdate n op v hs with
            | some p =>
                obtain ⟨r, hs'⟩ := p
                rw [hsu] at h; simp only at h
                rw [wStateUpdate_comm n op v hsu]
                have hsh' : HStackOk hs' := stateUpdate_hstackOk hsh hsu
                have key := ih g c (.ret r :: s) s' hs' hc hsh' h
                simpa only [injStack, injTerminal, List.map_cons] using key
            | none =>
                rw [hsu] at h
                rw [wStateUpdate_comm_none n op v hsu]
                cases htu : CalcVM.txnUpdate n op v hs with
                | some p =>
                    obtain ⟨r, hs'⟩ := p
                    rw [htu] at h; simp only at h
                    rw [wTxnUpdate_comm n op v htu]
                    have hsh' : HStackOk hs' := txnUpdate_hstackOk hsh htu
                    have key := ih g c (.ret r :: s) s' hs' hc hsh' h
                    simpa only [injStack, injTerminal, List.map_cons] using key
                | none =>
                    rw [htu] at h; simp only at h
                    rw [wTxnUpdate_comm_none n op v htu]
                    cases huf : CalcVM.unwindFind n op hs with
                    | some q =>
                        obtain ⟨c', s2, hs2⟩ := q
                        rw [huf] at h; simp only at h
                        rw [wUnwindFind_comm n op huf]
                        have hsh2 : HStackOk hs2 := unwindFind_hstackOk hsh huf
                        have hcok2 : CodeOk c' := unwindFind_savedCode_codeOk hsh huf
                        have key := ih g c' (.ret v :: s2) s' hs2 hcok2 hsh2 h
                        simpa only [injStack, injTerminal, List.map_cons] using key
                    | none =>
                        rw [huf] at h; simp at h
        | THROW n op v => exact absurd hi (by simp [InstrOk])

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
locals. Every emitted opcode is `const`/`clos`/`bindS`/`callS`/`caseS`/`splitS`/
`markH`/`unmarkH`/`opH` — none a local. This is the structural core of BOTH
`zero_grade_no_code` (the QTT-erasure headline) and `compile_well_typed`. The
residual arms (SUBST/APP/CASE/SPLIT) SUBSUME the tail into a single instr (the
threaded-continuation representation), so each cons-arm contributes exactly its
head opcode; induction on `Code` discharges every shape. -/
theorem lowerCode_no_locals (code : CalcVM.Code) (j : Wasmfx.Instr)
    (h : j ∈ lowerCode code) : (∀ k, j ≠ .getL k) ∧ (∀ k, j ≠ .setL k) := by
  induction code with
  | nil => simp [lowerCode] at h
  | cons i c ih =>
    cases i with
    -- head-cons-tail opcodes: head is not a local; tail by ih.
    | RET v   => simp only [lowerCode, lowerInstr, List.mem_cons] at h
                 rcases h with rfl | h; · exact ⟨by intro k; simp, by intro k; simp⟩
                 · exact ih h
    | LAMI M  => simp only [lowerCode, lowerInstr, List.mem_cons] at h
                 rcases h with rfl | h; · exact ⟨by intro k; simp, by intro k; simp⟩
                 · exact ih h
    | UNMARK  => simp only [lowerCode, lowerInstr, List.mem_cons] at h
                 rcases h with rfl | h; · exact ⟨by intro k; simp, by intro k; simp⟩
                 · exact ih h
    | OP n op v => simp only [lowerCode, lowerInstr, List.mem_cons] at h
                   rcases h with rfl | h; · exact ⟨by intro k; simp, by intro k; simp⟩
                   · exact ih h
    -- route-B HANDLE is a SUBSUMING singleton (`[markH h M c]`, the deferred-recompile rep) — not a local.
    | HANDLE h0 M => simp only [lowerCode, lowerInstr, List.mem_singleton] at h; subst h
                     exact ⟨by intro k; simp, by intro k; simp⟩
    -- residual opcodes: a SINGLE subsuming instr (threaded-cont rep) — not a local.
    | SUBST N => simp only [lowerCode, lowerInstr, List.mem_singleton] at h; subst h
                 exact ⟨by intro k; simp, by intro k; simp⟩
    | APP v   => simp only [lowerCode, lowerInstr, List.mem_singleton] at h; subst h
                 exact ⟨by intro k; simp, by intro k; simp⟩
    | CASE w N₁ N₂ => simp only [lowerCode, lowerInstr, List.mem_singleton] at h; subst h
                      exact ⟨by intro k; simp, by intro k; simp⟩
    | SPLIT w N => simp only [lowerCode, lowerInstr, List.mem_singleton] at h; subst h
                   exact ⟨by intro k; simp, by intro k; simp⟩
    -- THROW: lowers to nothing — `lowerCode c`; entirely the tail.
    | THROW ℓ op v => simp only [lowerCode, lowerInstr] at h; exact ih h

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

/-! ### `compile_forward_sim` — the heart (both legs proven)

The forward simulation chains:

  Source.eval fuel c = done v
    ──(reverse bridge: `source_eval_to_exec` / `evalD_complete_gen`, PROVEN)──▸
  ∃F, CalcVM.exec F (compile c []) [] [] = some [.ret v]
    ──(`exec_wexec_sim`, PROVEN)──▸
  wexec F (lowerCode (compile c [])) [] = some [compileV v]
    ──(`run` unfold)──▸
  Wasmfx.run F (compileC c) = done (compileV v)

All three legs are PROVEN. The first leg — `Source.eval` ⟹ `exec ∘ compile` — is the
reverse of the CalcVM bridge (`evalD_agrees_source` goes `evalD ⟹ Source.eval`); it is a
determinacy/completeness argument (both machines are deterministic and
total-on-termination), discharged via the converse simulation
`evalD_complete`/`evalD_complete_gen`. -/

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
    | perform _ ℓ op v => simpa [CalcVM.evalD] using h
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

/-- STORE-PARAMETRIC simulation: at ANY stores `σ τ`, anything `cy` evaluates to (some
fuel), `cx` evaluates to. The store parameter is what lets the simulation push UNDER a
`handle` (`Sim.handle`): a handle runs its body at PUSHED stores, so a `[] []`-only `Sim`
can't go under it — the reverse bridge needs the simulation at every store-context (every
`handleF` frame in `K` opens a new one). letC/app run the inner at the SAME stores, so their
congruences are store-agnostic (the σ/τ thread unchanged). -/
def Sim (cx cy : Comp) : Prop :=
  ∀ σ τ b r, CalcVM.evalD b σ τ cy = some r → ∃ a, CalcVM.evalD a σ τ cx = some r

/-- `letC` preserves simulation in the bound position: if `cx` simulates `cy`,
then `letC cx N` simulates `letC cy N`. Both run the bound computation FIRST;
`cx` reaches every terminal `cy` does, so the `letC`s agree. The non-`ret`
terminal case is vacuous (`evalD (letC _ N)` of a `lam`-terminal is `none`); the
`raised` case propagates the same raise. -/
theorem Sim.letC {cx cy : Comp} (h : Sim cx cy) (N : Comp) : Sim (.letC cx N) (.letC cy N) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b σ τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hy
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
              | perform _ a a' a'' => simp at hb
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
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b σ τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hy
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
              | perform _ a a' a'' => simp at hb
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

/-- `handle` preserves simulation: this is the NEW congruence the handler-fragment reverse
bridge needs (and the reason `Sim` is store-parametric). `evalD (handle h cy)` runs `cy` at
PUSHED stores and post-processes the body OUTCOME (pop / forward / catch) — a pure function of
that outcome. By `Sim cx cy` AT the pushed stores, `cx` reaches the SAME body outcome `oy`, so
the SAME post-processing yields the SAME `handle`-result. Case on the handler kind (state pushes
σ, transaction pushes τ, throws keeps both) — the body-fuel transfers, the post-step is identical. -/
theorem Sim.handle {cx cy : Comp} (h : Sim cx cy) (hh : Handler) :
    Sim (.handle hh cx) (.handle hh cy) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      cases hh with
      | state ℓ s =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b (σ.push ℓ s) τ cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h (σ.push ℓ s) τ b oy hy
              refine ⟨a + 1, ?_⟩
              simp only [CalcVM.evalD]; rw [ha]; exact hb
      | transaction ℓ Θ =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b σ (τ.push ℓ Θ) cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ (τ.push ℓ Θ) b oy hy
              refine ⟨a + 1, ?_⟩
              simp only [CalcVM.evalD]; rw [ha]; exact hb
      | throws ℓ0 =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b σ τ cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ τ b oy hy
              refine ⟨a + 1, ?_⟩
              simp only [CalcVM.evalD]; rw [ha]; exact hb

/-- The plug-congruence: a focus simulation lifts through ANY frame stack — including `handleF`
(via `Sim.handle`), now that `Sim` is store-parametric. Induction on `K`; the lift is
unconditional over `K` — no context-purity predicate needed. -/
theorem evalD_plug_sim : ∀ {K : Bang.EvalCtx} {cx cy : Comp}, Sim cx cy →
    ∀ {n r}, CalcVM.evalD n [] [] (plug K cy) = some r →
    ∃ m, CalcVM.evalD m [] [] (plug K cx) = some r
  | [], cx, cy, h, n, r, hn => h _ _ n r (by simpa [plug] using hn)
  | .letF N :: K, cx, cy, h, n, r, hn => by
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim (h.letC N) hn
  | .appF u :: K, cx, cy, h, n, r, hn => by
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim (h.app u) hn
  | .handleF hh :: K, cx, cy, h, n, r, hn => by
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim (h.handle hh) hn

/-- The three CK REDUCE steps as simulations (the contractum simulates the redex):
each is a single `evalD` head-unfold. -/
-- DIRECTION: the REDEX simulates the CONTRACTUM (what `subst …` reaches, `letC (ret w) N`
-- reaches too, in one extra unfold) — this is the direction the transfer needs (it has the
-- contractum's `evalD`, wants the redex's).
theorem sim_letC_ret (w : Bang.Val) (N : Comp) : Sim (.letC (.ret w) N) (Comp.subst w N) := by
  intro σ τ b r hb
  refine ⟨b + 2, ?_⟩
  simp only [CalcVM.evalD, Option.bind_some]
  exact evalD_some_le (by omega) hb

theorem sim_app_lam (u : Bang.Val) (M : Comp) : Sim (.app (.lam M) u) (Comp.subst u M) := by
  intro σ τ b r hb
  refine ⟨b + 2, ?_⟩
  simp only [CalcVM.evalD, Option.bind_some]
  exact evalD_some_le (by omega) hb

theorem sim_force (M : Comp) : Sim (.force (.vthunk M)) M := by
  intro σ τ b r hb
  exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩

/-- The three transfer lemmas `evalD_complete_gen` invokes, derived from
`evalD_plug_sim` + the redex simulations. -/
theorem evalD_plug_letC_ret (K : Bang.EvalCtx) (w : Bang.Val) (N : Comp) (r : _)
    (h : CalcVM.evalD r [] [] (plug K (Comp.subst w N)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.letC (.ret w) N)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_letC_ret w N) h

theorem evalD_plug_app_lam (K : Bang.EvalCtx) (u : Bang.Val) (M : Comp) (r : _)
    (h : CalcVM.evalD r [] [] (plug K (Comp.subst u M)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.app (.lam M) u)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_app_lam u M) h

theorem evalD_plug_force (K : Bang.EvalCtx) (M : Comp) (r : _)
    (h : CalcVM.evalD r [] [] (plug K M) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.force (.vthunk M))) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_force M) h

-- ADT redex simulations (sub-step 1a): the eliminator simulates its contractum (one evalD unfold).
theorem sim_case_inl (v : Bang.Val) (N₁ N₂ : Comp) :
    Sim (.case (.inl v) N₁ N₂) (Comp.subst v N₁) := by
  intro σ τ b r hb; exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩
theorem sim_case_inr (v : Bang.Val) (N₁ N₂ : Comp) :
    Sim (.case (.inr v) N₁ N₂) (Comp.subst v N₂) := by
  intro σ τ b r hb; exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩
theorem sim_split (v u : Bang.Val) (N : Comp) :
    Sim (.split (.pair v u) N) (Comp.subst v (Comp.subst (Val.shift u) N)) := by
  intro σ τ b r hb; exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩

theorem evalD_plug_case_inl (K : Bang.EvalCtx) (v : Bang.Val) (N₁ N₂ : Comp) (r : _)
    (h : CalcVM.evalD r [] [] (plug K (Comp.subst v N₁)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.case (.inl v) N₁ N₂)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_case_inl v N₁ N₂) h
theorem evalD_plug_case_inr (K : Bang.EvalCtx) (v : Bang.Val) (N₁ N₂ : Comp) (r : _)
    (h : CalcVM.evalD r [] [] (plug K (Comp.subst v N₂)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.case (.inr v) N₁ N₂)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_case_inr v N₁ N₂) h
theorem evalD_plug_split (K : Bang.EvalCtx) (v u : Bang.Val) (N : Comp) (r : _)
    (h : CalcVM.evalD r [] [] (plug K (Comp.subst v (Comp.subst (Val.shift u) N))) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.split (.pair v u) N)) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_split v u N) h

/-- `unfold (fold v)` reduces to `ret v` — a TERMINAL, not a focus-step. Under a pure
plug, `evalD (plug K (ret v))` ⟹ `evalD (plug K (unfold (fold v)))` (one unfold). -/
theorem sim_unfold (v : Bang.Val) : Sim (.unfold (.fold v)) (Comp.ret v) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      -- evalD (ret v) = some(.term(.ret v),σ,τ); evalD (unfold (fold v)) = the SAME.
      simp only [CalcVM.evalD] at hb
      exact ⟨1, by simp only [CalcVM.evalD]; exact hb⟩
theorem evalD_plug_unfold (K : Bang.EvalCtx) (v : Bang.Val) (r : _)
    (h : CalcVM.evalD r [] [] (plug K (Comp.ret v)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.unfold (.fold v))) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_unfold v) h

/-- HANDLER-RETURN (Q6 identity): `handle h (ret w)` evalD-EQUALS `ret w`. For state/transaction
the push/pop CANCEL on a terminal `ret`; for throws the body returns directly. So the redex
`handle h (ret w)` simulates its contractum `ret w` (one handle-unfold of fuel). The simulation
the `handleF`-return reverse-bridge arm needs. -/
theorem sim_handle_ret (h : Handler) (w : Bang.Val) : Sim (.handle h (.ret w)) (.ret w) := by
  intro σ τ b r hb
  -- evalD b (ret w) σ τ = some (.term (.ret w), σ, τ) (for b ≥ 1).
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hb
      -- run `handle h (ret w)` at b+2: pushes (state/txn) or not (throws), body `ret w` returns,
      -- pop cancels ⇒ same (.term (.ret w), σ, τ).
      refine ⟨b + 2, ?_⟩
      cases h <;> simp [CalcVM.evalD, CalcVM.SStore.push, CalcVM.THeap.push, List.tail]

theorem evalD_plug_handleF_ret (K : Bang.EvalCtx) (h : Handler) (w : Bang.Val) (r : _)
    (hn : CalcVM.evalD r [] [] (plug K (Comp.ret w)) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.handle h (.ret w))) = some (.term (.ret w'), [], []) :=
  evalD_plug_sim (sim_handle_ret h w) hn

/-! ### The dispatch reverse-bridge (◊5 GAP-2): store-restricted simulation lifted through `plug`.

The dispatch arm of `evalD_complete_gen` rewrites `up ℓ op v` to a handler-resume `focus` over a
RESTRUCTURED context `K'`. The focus-rewrite at the catching frame is a STORE-RESTRICTED simulation
(`SimOn P`): `Sim (up ℓ "get" v) (ret s)` is only valid when the threaded store has `get? σ ℓ = some s`
(a plain `Sim` is false). `evalD_plug_simon` lifts a `SimOn P` through any frame stack whose state
pushes preserve `P` — the reverse-direction analog of how `run_evalD` threads stores forward.
shape: the store-parametric `Sim`/`evalD_plug_sim` (above), conditioned on a store predicate. -/

def SimOn (P : CalcVM.SStore → Prop) (cx cy : Bang.Comp) : Prop :=
  ∀ σ τ b r, P σ → CalcVM.evalD b σ τ cy = some r → ∃ a, CalcVM.evalD a σ τ cx = some r

theorem SimOn.handle {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp} (h : SimOn P cx cy) (hh : Bang.Handler)
    (hsurv : ∀ σ, P σ → ∀ ℓ' s', hh = Bang.Handler.state ℓ' s' → P (σ.push ℓ' s')) :
    SimOn P (.handle hh cx) (.handle hh cy) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      cases hh with
      | state ℓ s =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b (σ.push ℓ s) τ cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h (σ.push ℓ s) τ b oy (hsurv σ hP ℓ s rfl) hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩
      | transaction ℓ Θ =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b σ (τ.push ℓ Θ) cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ (τ.push ℓ Θ) b oy hP hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩
      | throws ℓ0 =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b σ τ cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ τ b oy hP hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩

theorem SimOn.letC {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp} (h : SimOn P cx cy) (N : Bang.Comp) :
    SimOn P (.letC cx N) (.letC cy N) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b σ τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hP hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | ret w =>
                  simp only [Option.bind_some] at hb
                  exact ⟨(max a b) + 1, by
                    simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                    exact evalD_some_le (Nat.le_max_right a b) hb⟩
              | lam M => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | perform _ a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                exact ⟨a + 1, by simp only [CalcVM.evalD, ha, Option.bind_some]; exact hb⟩

theorem SimOn.app {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp} (h : SimOn P cx cy) (u : Bang.Val) :
    SimOn P (.app cx u) (.app cy u) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b σ τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hP hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | lam M =>
                  simp only [Option.bind_some] at hb
                  exact ⟨(max a b) + 1, by
                    simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                    exact evalD_some_le (Nat.le_max_right a b) hb⟩
              | ret w => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | perform _ a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                exact ⟨a + 1, by simp only [CalcVM.evalD, ha, Option.bind_some]; exact hb⟩

-- The plug-lift: structural recursion on K (mirrors evalD_plug_sim). The store-predicate P must
-- survive every state-push K does. We carry that as `hsurv`: P is preserved by any (ℓ',s')-push
-- where (ℓ',s') is a state frame of K. Stated as: for the HEAD handleF (state ℓ' s'), P survives.
theorem evalD_plug_simon {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp} (hsim : SimOn P cx cy) :
    ∀ {K : Bang.EvalCtx},
      (∀ σ, P σ → ∀ ℓ' s', Bang.Frame.handleF (Bang.Handler.state ℓ' s') ∈ K → P (σ.push ℓ' s')) →
    ∀ {σ τ n r}, P σ → CalcVM.evalD n σ τ (plug K cy) = some r →
      ∃ m, CalcVM.evalD m σ τ (plug K cx) = some r
  | [], _, σ, τ, n, r, hP, hn => hsim σ τ n r hP (by simpa [plug] using hn)
  | .letF N :: K, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      exact evalD_plug_simon (SimOn.letC hsim N) (fun σ' hP' ℓ' s' hmem => hsurv σ' hP' ℓ' s' (by simp [hmem])) hP hn
  | .appF u :: K, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      exact evalD_plug_simon (SimOn.app hsim u) (fun σ' hP' ℓ' s' hmem => hsurv σ' hP' ℓ' s' (by simp [hmem])) hP hn
  | .handleF hh :: K, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      refine evalD_plug_simon (SimOn.handle hsim hh ?_) (fun σ' hP' ℓ' s' hmem => hsurv σ' hP' ℓ' s' (by simp [hmem])) hP hn
      -- survival of the HEAD handle: if hh = state ℓ' s', it's a member of (handleF hh :: K).
      intro σ' hP' ℓ' s' hhe
      exact hsurv σ' hP' ℓ' s' (by rw [hhe]; simp)

-- ===== Redex SimOn lemmas (the focus-rewrite each dispatch sub-case performs) =====

theorem simon_get (cap : Nat) (ℓ : Bang.EffectRow.Label) (s v : Bang.Val) :
    SimOn (fun σ => CalcVM.SStore.get? σ ℓ = some s) (.perform cap ℓ "get" v) (.ret s) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      exact ⟨b+1, by simp only [CalcVM.evalD] at hb ⊢; rw [hP]; exact hb⟩


/-! ### put/txn store-threading: input-store-SHIFT simulation (`SimShift`).

put/txn CHANGE the output store, so they are NOT a plain `SimOn` (which demands identical output).
The fix: shift the change to the INPUT — `up l put v` at sigma (active frame l) produces the SAME
outcome as `ret unit` at `sigma.put l v`. `SimShift f P` captures cx at sigma == cy at (f sigma); it
lifts through `plug Ki` when f commutes with Ki's pushes (Ki has no state l frame). `sim_put_handle`
absorbs the shift via the catching handle's pop. -/

-- Input-store-shift simulation: cx at σ reaches every (out,σ',τ') that cy reaches at (f σ).
-- For put: cx = up ℓ put v at σ (ℓ=s), cy = ret unit at (σ.put ℓ v). Both give (term(ret unit), σ.put ℓ v, τ).
def SimShift (f : CalcVM.SStore → CalcVM.SStore) (P : CalcVM.SStore → Prop) (cx cy : Bang.Comp) : Prop :=
  ∀ σ τ b r, P σ → CalcVM.evalD b (f σ) τ cy = some r → ∃ a, CalcVM.evalD a σ τ cx = some r

-- put redex: f = (·.put ℓ v), P = (get? · ℓ = some s).
theorem simshift_put (cap : Nat) (ℓ : Bang.EffectRow.Label) (s v : Bang.Val) :
    SimShift (fun σ => CalcVM.SStore.put σ ℓ v) (fun σ => CalcVM.SStore.get? σ ℓ = some s)
      (.perform cap ℓ "put" v) (.ret .vunit) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      -- hb : evalD (b+1) (σ.put ℓ v) τ (ret unit) = some r, i.e. r = (term(ret unit), σ.put ℓ v, τ)
      simp only [CalcVM.evalD] at hb
      refine ⟨b+1, ?_⟩
      simp only [CalcVM.evalD, if_neg (by decide : ¬("put"="get")), hP, if_true]
      exact hb

-- put commutes with a non-ℓ cons (the stability the handle-lift needs).
theorem put_cons_ne (ℓ ℓ' : Bang.EffectRow.Label) (s' v : Bang.Val) (σ : CalcVM.SStore) (hne : ℓ' ≠ ℓ) :
    CalcVM.SStore.put ((ℓ', s') :: σ) ℓ v = (ℓ', s') :: CalcVM.SStore.put σ ℓ v := by
  simp only [CalcVM.SStore.put, if_neg hne]

-- SimShift congruences. f must be STABLE under the pushes (we pass that as hyp per-handle).
theorem SimShift.handle {f : CalcVM.SStore → CalcVM.SStore} {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp}
    (h : SimShift f P cx cy) (hh : Bang.Handler)
    (hstab : ∀ σ ℓ' s', hh = Bang.Handler.state ℓ' s' → f ((ℓ',s') :: σ) = (ℓ',s') :: f σ)
    (hsurv : ∀ σ, P σ → ∀ ℓ' s', hh = Bang.Handler.state ℓ' s' → P (σ.push ℓ' s')) :
    SimShift f P (.handle hh cx) (.handle hh cy) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      cases hh with
      | state ℓ0 s0 =>
          simp only [CalcVM.evalD] at hb
          -- hb runs cy at (f σ).push ℓ0 s0 = (ℓ0,s0)::(f σ); by hstab = f ((ℓ0,s0)::σ) = f (σ.push ℓ0 s0)
          rw [show (f σ).push ℓ0 s0 = f (σ.push ℓ0 s0) by
            simp only [CalcVM.SStore.push]; rw [hstab σ ℓ0 s0 rfl]] at hb
          cases hy : CalcVM.evalD b (f (σ.push ℓ0 s0)) τ cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h (σ.push ℓ0 s0) τ b oy (hsurv σ hP ℓ0 s0 rfl) hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩
      | transaction ℓ0 Θ0 =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b (f σ) (τ.push ℓ0 Θ0) cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ (τ.push ℓ0 Θ0) b oy hP hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩
      | throws ℓ0 =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b (f σ) τ cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ τ b oy hP hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩

theorem SimShift.letC {f : CalcVM.SStore → CalcVM.SStore} {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp}
    (h : SimShift f P cx cy) (N : Bang.Comp) : SimShift f P (.letC cx N) (.letC cy N) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b (f σ) τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hP hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | ret w =>
                  simp only [Option.bind_some] at hb
                  exact ⟨(max a b) + 1, by
                    simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                    exact evalD_some_le (Nat.le_max_right a b) hb⟩
              | lam M => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | perform _ a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                exact ⟨a + 1, by simp only [CalcVM.evalD, ha, Option.bind_some]; exact hb⟩

theorem SimShift.app {f : CalcVM.SStore → CalcVM.SStore} {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp}
    (h : SimShift f P cx cy) (u : Bang.Val) : SimShift f P (.app cx u) (.app cy u) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b (f σ) τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hP hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | lam M =>
                  simp only [Option.bind_some] at hb
                  exact ⟨(max a b) + 1, by
                    simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                    exact evalD_some_le (Nat.le_max_right a b) hb⟩
              | ret w => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | perform _ a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                exact ⟨a + 1, by simp only [CalcVM.evalD, ha, Option.bind_some]; exact hb⟩

theorem evalD_plug_simshift {f : CalcVM.SStore → CalcVM.SStore} {P : CalcVM.SStore → Prop} {cx cy : Bang.Comp}
    (hsim : SimShift f P cx cy) :
    ∀ {K : Bang.EvalCtx},
      (∀ σ ℓ' s', Bang.Frame.handleF (Bang.Handler.state ℓ' s') ∈ K → f ((ℓ',s') :: σ) = (ℓ',s') :: f σ) →
      (∀ σ, P σ → ∀ ℓ' s', Bang.Frame.handleF (Bang.Handler.state ℓ' s') ∈ K → P (σ.push ℓ' s')) →
    ∀ {σ τ n r}, P σ → CalcVM.evalD n (f σ) τ (plug K cy) = some r →
      ∃ m, CalcVM.evalD m σ τ (plug K cx) = some r
  | [], _, _, σ, τ, n, r, hP, hn => hsim σ τ n r hP (by simpa [plug] using hn)
  | .letF N :: K, hstab, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      exact evalD_plug_simshift (SimShift.letC hsim N)
        (fun σ' ℓ' s' hmem => hstab σ' ℓ' s' (by simp [hmem]))
        (fun σ' hP' ℓ' s' hmem => hsurv σ' hP' ℓ' s' (by simp [hmem])) hP hn
  | .appF u :: K, hstab, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      exact evalD_plug_simshift (SimShift.app hsim u)
        (fun σ' ℓ' s' hmem => hstab σ' ℓ' s' (by simp [hmem]))
        (fun σ' hP' ℓ' s' hmem => hsurv σ' hP' ℓ' s' (by simp [hmem])) hP hn
  | .handleF hh :: K, hstab, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      refine evalD_plug_simshift (SimShift.handle hsim hh ?_ ?_)
        (fun σ' ℓ' s' hmem => hstab σ' ℓ' s' (by simp [hmem]))
        (fun σ' hP' ℓ' s' hmem => hsurv σ' hP' ℓ' s' (by simp [hmem])) hP hn
      · intro σ' ℓ' s' hhe; exact hstab σ' ℓ' s' (by rw [hhe]; simp)
      · intro σ' hP' ℓ' s' hhe; exact hsurv σ' hP' ℓ' s' (by rw [hhe]; simp)

-- CalcVM.ctxStates none ⇒ no state ℓ frame ⇒ every state frame has a DIFFERENT label.
theorem state_mem_ne_of_ctxStates_none {ℓ : Bang.EffectRow.Label} :
    ∀ {Kᵢ : Bang.EvalCtx}, (CalcVM.ctxStates Kᵢ).get? ℓ = none →
      ∀ ℓ' s', Bang.Frame.handleF (Bang.Handler.state ℓ' s') ∈ Kᵢ → ℓ' ≠ ℓ := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro _ ℓ' s' hmem; simp at hmem
  | cons fr Kᵢ ih =>
      intro hnone ℓ' s' hmem
      cases fr with
      | handleF h0 =>
          cases h0 with
          | state ℓ0 s0 =>
              by_cases hc : ℓ0 = ℓ
              · subst hc
                simp only [CalcVM.ctxStates, CalcVM.SStore.get?, List.find?, decide_true, Option.map_some] at hnone
                exact absurd hnone (by simp)
              · simp only [CalcVM.ctxStates, CalcVM.SStore.get?, List.find?, hc, decide_false] at hnone
                rcases List.mem_cons.mp hmem with heq | htl
                · simp only [Bang.Frame.handleF.injEq, Bang.Handler.state.injEq] at heq; obtain ⟨h1, _⟩ := heq; subst h1; exact hc
                · exact ih (by simpa [CalcVM.SStore.get?] using hnone) ℓ' s' htl
          | throws ℓ0 =>
              simp only [CalcVM.ctxStates] at hnone
              rcases List.mem_cons.mp hmem with heq | htl
              · exact absurd heq (by simp)
              · exact ih hnone ℓ' s' htl
          | transaction ℓ0 Θ0 =>
              simp only [CalcVM.ctxStates] at hnone
              rcases List.mem_cons.mp hmem with heq | htl
              · exact absurd heq (by simp)
              · exact ih hnone ℓ' s' htl
      | letF N =>
          simp only [CalcVM.ctxStates] at hnone
          rcases List.mem_cons.mp hmem with heq | htl
          · exact absurd heq (by simp)
          · exact ih hnone ℓ' s' htl
      | appF u =>
          simp only [CalcVM.ctxStates] at hnone
          rcases List.mem_cons.mp hmem with heq | htl
          · exact absurd heq (by simp)
          · exact ih hnone ℓ' s' htl


-- get?-of-push helper
theorem get?_push_self2 (σ : CalcVM.SStore) (ℓ : Bang.EffectRow.Label) (s : Bang.Val) :
    CalcVM.SStore.get? ((ℓ, s) :: σ) ℓ = some s := by simp [CalcVM.SStore.get?, List.find?]

-- The handle-level put Sim: lifting through Kᵢ (no state ℓ in Kᵢ).
theorem sim_put_handle (cap : Nat) (ℓ : Bang.EffectRow.Label) (s w : Bang.Val) {Kᵢ : Bang.EvalCtx}
    (hnone : (CalcVM.ctxStates Kᵢ).get? ℓ = none) :
    Sim (.handle (.state ℓ s) (plug Kᵢ (.perform cap ℓ "put" w)))
        (.handle (.state ℓ w) (plug Kᵢ (.ret .vunit))) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      -- RHS: handle (state ℓ w): push (ℓ,w); run plug Kᵢ (ret unit) at (ℓ,w)::σ; pop tail.
      simp only [CalcVM.evalD, CalcVM.SStore.push] at hb
      -- note (ℓ,w)::σ = put ((ℓ,s)::σ) ℓ w = f ((ℓ,s)::σ) where f = put · ℓ w
      have hfeq : ((ℓ, w) :: σ : CalcVM.SStore) = CalcVM.SStore.put ((ℓ,s)::σ) ℓ w := by
        simp [CalcVM.SStore.put]
      rw [hfeq] at hb
      cases hy : CalcVM.evalD b (CalcVM.SStore.put ((ℓ,s)::σ) ℓ w) τ (plug Kᵢ (.ret .vunit)) with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          -- lift via SimShift through Kᵢ at inner store (ℓ,s)::σ
          have hne := state_mem_ne_of_ctxStates_none hnone
          obtain ⟨a, ha⟩ := evalD_plug_simshift (simshift_put cap ℓ s w)
            (K := Kᵢ)
            (fun σ' ℓ' s' hmem => put_cons_ne ℓ ℓ' s' w σ' (hne ℓ' s' hmem))
            (fun σ' hP' ℓ' s' hmem => by
              simp only [CalcVM.SStore.push, CalcVM.SStore.get?, List.find?, (hne ℓ' s' hmem), decide_false] at hP' ⊢
              exact hP')
            (σ := (ℓ,s)::σ) (τ := τ)
            (get?_push_self2 σ ℓ s) hy
          -- ha : evalD a ((ℓ,s)::σ) τ (plug Kᵢ (up ℓ put w)) = some oy
          refine ⟨a + 1, ?_⟩
          simp only [CalcVM.evalD, CalcVM.SStore.push]
          rw [ha]; exact hb

/-! ### abort (throws) case: raise-forwarding through the inner context.

A `throws`-routed `up ℓ "raise" v` produces `.raised ℓ "raise" v` and propagates through the inner
context Kᵢ (which catches nothing) to the throws handler, which catches → `ret v`. `Raises ℓ v cy`
captures "cy evalD-raises (ℓ,raise,v) at unchanged stores"; it forwards through letC/app and through
non-catching handles (push+pop restores the store). `evalD_plug_raises` lifts it through `plug Kᵢ`. -/

theorem evalD_perform_raise (cap : Nat) (ℓ : Bang.EffectRow.Label) (v : Bang.Val) (σ : CalcVM.SStore) (τ : CalcVM.THeap) (b : Nat) :
    CalcVM.evalD (b+1) σ τ (.perform cap ℓ "raise" v) = some (.raised ℓ "raise" v, σ, τ) := by
  simp only [CalcVM.evalD, if_neg (by decide : ¬("raise"="get")), if_neg (by decide : ¬("raise"="put")),
    (by decide : CalcVM.isTxnOp "raise" = false), Bool.false_eq_true, if_false]

-- A focus `cy` that evalD-RAISES (ℓ,raise,v) at σ τ unchanged simulates the same raise under one
-- frame wrap: letC forwards, app forwards, handle (non-catching) forwards+pops (store restored).
-- We carry the predicate "evalD-of-cy raises (ℓ,raise,v) leaving σ,τ" as `Raises cy`.
def Raises (ℓ : Bang.EffectRow.Label) (v : Bang.Val) (cy : Bang.Comp) : Prop :=
  ∀ σ τ, ∃ n, CalcVM.evalD n σ τ cy = some (.raised ℓ "raise" v, σ, τ)

theorem Raises.perform (cap : Nat) (ℓ : Bang.EffectRow.Label) (v : Bang.Val) : Raises ℓ v (.perform cap ℓ "raise" v) :=
  fun σ τ => ⟨1, evalD_perform_raise cap ℓ v σ τ 0⟩

theorem Raises.letC {ℓ v N} (h : Raises ℓ v cy) : Raises ℓ v (.letC cy N) := by
  intro σ τ; obtain ⟨n, hn⟩ := h σ τ
  exact ⟨n+1, by simp only [CalcVM.evalD, hn, Option.bind_some]⟩

theorem Raises.app {ℓ v u} (h : Raises ℓ v cy) : Raises ℓ v (.app cy u) := by
  intro σ τ; obtain ⟨n, hn⟩ := h σ τ
  exact ⟨n+1, by simp only [CalcVM.evalD, hn, Option.bind_some]⟩

theorem Raises.handle {ℓ v hh} (hnc : Bang.handlesOp hh ℓ "raise" = false) (h : Raises ℓ v cy) :
    Raises ℓ v (.handle hh cy) := by
  intro σ τ
  cases hh with
  | state ℓ0 s0 =>
      obtain ⟨n, hn⟩ := h (σ.push ℓ0 s0) τ
      refine ⟨n+1, ?_⟩
      simp only [CalcVM.SStore.push] at hn
      simp only [CalcVM.evalD, CalcVM.SStore.push, hn, Option.bind_some, List.tail_cons]
  | transaction ℓ0 Θ0 =>
      obtain ⟨n, hn⟩ := h σ (τ.push ℓ0 Θ0)
      refine ⟨n+1, ?_⟩
      simp only [CalcVM.THeap.push] at hn
      simp only [CalcVM.evalD, CalcVM.THeap.push, hn, Option.bind_some, List.tail_cons]
  | throws ℓ0 =>
      obtain ⟨n, hn⟩ := h σ τ
      refine ⟨n+1, ?_⟩
      have hne0 : ¬ (ℓ0 = ℓ) := by
        simp only [Bang.handlesOp, beq_self_eq_true, Bool.and_true, decide_eq_false_iff_not] at hnc
        exact hnc
      simp only [CalcVM.evalD, hn, Option.bind_some, if_neg (by tauto : ¬ (ℓ0 = ℓ ∧ True))]

-- The plug-lift of Raises (mirrors evalD_plug_sim): a raising focus lifts through any frame stack
-- that catches nothing. splitAt Kᵢ none ⇒ each handleF doesn't catch (handlesOp = false).
theorem evalD_plug_raises (ℓ : Bang.EffectRow.Label) (v : Bang.Val) :
    ∀ {Kᵢ : Bang.EvalCtx} {cy : Bang.Comp}, Bang.splitAt Kᵢ ℓ "raise" = none → Raises ℓ v cy →
      Raises ℓ v (plug Kᵢ cy)
  | [], cy, _, h => by simpa [plug] using h
  | .letF N :: Kᵢ, cy, hns, h => by
      rw [plug_cons, Bang.Frame.wrapStep]
      have hns' : Bang.splitAt Kᵢ ℓ "raise" = none := by
        simp only [Bang.splitAt, Option.map_eq_none_iff] at hns; exact hns
      exact evalD_plug_raises ℓ v hns' (Raises.letC h)
  | .appF u :: Kᵢ, cy, hns, h => by
      rw [plug_cons, Bang.Frame.wrapStep]
      have hns' : Bang.splitAt Kᵢ ℓ "raise" = none := by
        simp only [Bang.splitAt, Option.map_eq_none_iff] at hns; exact hns
      exact evalD_plug_raises ℓ v hns' (Raises.app h)
  | .handleF hh :: Kᵢ, cy, hns, h => by
      rw [plug_cons, Bang.Frame.wrapStep]
      -- splitAt (handleF hh :: Kᵢ) = none ⇒ hh doesn't catch (handlesOp false) AND splitAt Kᵢ = none.
      simp only [Bang.splitAt] at hns
      by_cases hc : Bang.handlesOp hh ℓ "raise" = true
      · rw [if_pos hc] at hns; exact absurd hns (by simp)
      · rw [if_neg hc] at hns
        rw [Option.map_eq_none_iff] at hns
        have hncf : Bang.handlesOp hh ℓ "raise" = false := by
          simpa using hc
        exact evalD_plug_raises ℓ v hns (Raises.handle hncf h)

/-! ### get/abort handle-Sims + the txn (transaction) store-shift mirror. -/

-- get handle-Sim: mirrors sim_put_handle but via SimOn (no store change). The handle pushes (ℓ,s),
-- establishing P = (get? · ℓ = some s); lift simon_get through Kᵢ.
theorem sim_get_handle (cap : Nat) (ℓ : Bang.EffectRow.Label) (s v : Bang.Val) {Kᵢ : Bang.EvalCtx}
    (hnone : (CalcVM.ctxStates Kᵢ).get? ℓ = none) :
    Sim (.handle (.state ℓ s) (plug Kᵢ (.perform cap ℓ "get" v)))
        (.handle (.state ℓ s) (plug Kᵢ (.ret s))) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD, CalcVM.SStore.push] at hb
      cases hy : CalcVM.evalD b ((ℓ,s)::σ) τ (plug Kᵢ (.ret s)) with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          have hne := state_mem_ne_of_ctxStates_none hnone
          obtain ⟨a, ha⟩ := evalD_plug_simon (simon_get cap ℓ s v) (K := Kᵢ)
            (fun σ' hP' ℓ' s' hmem => by
              simp only [CalcVM.SStore.push, CalcVM.SStore.get?, List.find?, (hne ℓ' s' hmem), decide_false] at hP' ⊢
              exact hP')
            (P := fun σ => CalcVM.SStore.get? σ ℓ = some s)
            (σ := (ℓ,s)::σ) (τ := τ)
            (get?_push_self2 σ ℓ s) hy
          refine ⟨a+1, ?_⟩
          simp only [CalcVM.evalD, CalcVM.SStore.push]
          rw [ha]; exact hb

-- abort handle-Sim: the inner raises (via evalD_plug_raises), the throws handler catches → ret v.
theorem sim_abort_handle (cap : Nat) (ℓ : Bang.EffectRow.Label) (v : Bang.Val) {Kᵢ : Bang.EvalCtx}
    (hnone : Bang.splitAt Kᵢ ℓ "raise" = none) :
    Sim (.handle (.throws ℓ) (plug Kᵢ (.perform cap ℓ "raise" v))) (.ret v) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      -- RHS: evalD (b+1) σ τ (ret v) = some (term (ret v), σ, τ) = r
      simp only [CalcVM.evalD] at hb
      -- inner raises at σ τ:
      obtain ⟨n, hn⟩ := evalD_plug_raises ℓ v hnone (Raises.perform cap ℓ v) σ τ
      refine ⟨n+1, ?_⟩
      simp only [CalcVM.evalD, hn, Option.bind_some, if_pos (by simp : (ℓ = ℓ ∧ "raise" = "raise"))]
      exact hb

-- CalcVM.THeap-shift simulation (txn analog of SimShift). cx at τ ≡ cy at (f τ); P on τ.
def SimShiftT (f : CalcVM.THeap → CalcVM.THeap) (P : CalcVM.THeap → Prop) (cx cy : Bang.Comp) : Prop :=
  ∀ σ τ b r, P τ → CalcVM.evalD b σ (f τ) cy = some r → ∃ a, CalcVM.evalD a σ τ cx = some r

-- txn redex: up ℓ op v at τ (active heap ℓ↦Θ) ≡ ret r at (τ.put ℓ Θ'), where (r,Θ')=txnService.
theorem simshiftT_txn (cap : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Bang.Val) (Θ : List Bang.Val)
    (hop : CalcVM.isTxnOp op = true) :
    SimShiftT (fun τ => CalcVM.THeap.put τ ℓ (CalcVM.txnService op v Θ).2)
      (fun τ => CalcVM.THeap.get? τ ℓ = some Θ)
      (.perform cap ℓ op v) (.ret (CalcVM.txnService op v Θ).1) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      refine ⟨b+1, ?_⟩
      have hng : ¬ (op = "get") := by rcases CalcVM.isTxnOp_iff.mp hop with rfl|rfl|rfl <;> decide
      have hnp : ¬ (op = "put") := by rcases CalcVM.isTxnOp_iff.mp hop with rfl|rfl|rfl <;> decide
      simp only [CalcVM.evalD, if_neg hng, if_neg hnp, hop, if_true, hP]
      exact hb

theorem put_consT_ne (ℓ ℓ' : Bang.EffectRow.Label) (Θ' Θx : List Bang.Val) (τ : CalcVM.THeap) (hne : ℓ' ≠ ℓ) :
    CalcVM.THeap.put ((ℓ', Θx) :: τ) ℓ Θ' = (ℓ', Θx) :: CalcVM.THeap.put τ ℓ Θ' := by
  simp only [CalcVM.THeap.put, if_neg hne]

theorem SimShiftT.handle {f : CalcVM.THeap → CalcVM.THeap} {P : CalcVM.THeap → Prop} {cx cy : Bang.Comp}
    (h : SimShiftT f P cx cy) (hh : Bang.Handler)
    (hstab : ∀ τ ℓ' Θ', hh = Bang.Handler.transaction ℓ' Θ' → f ((ℓ',Θ') :: τ) = (ℓ',Θ') :: f τ)
    (hsurv : ∀ τ, P τ → ∀ ℓ' Θ', hh = Bang.Handler.transaction ℓ' Θ' → P (τ.push ℓ' Θ')) :
    SimShiftT f P (.handle hh cx) (.handle hh cy) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      cases hh with
      | state ℓ0 s0 =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b (σ.push ℓ0 s0) (f τ) cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h (σ.push ℓ0 s0) τ b oy hP hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩
      | transaction ℓ0 Θ0 =>
          simp only [CalcVM.evalD] at hb
          rw [show (f τ).push ℓ0 Θ0 = f (τ.push ℓ0 Θ0) by
            simp only [CalcVM.THeap.push]; rw [hstab τ ℓ0 Θ0 rfl]] at hb
          cases hy : CalcVM.evalD b σ (f (τ.push ℓ0 Θ0)) cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ (τ.push ℓ0 Θ0) b oy (hsurv τ hP ℓ0 Θ0 rfl) hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩
      | throws ℓ0 =>
          simp only [CalcVM.evalD] at hb
          cases hy : CalcVM.evalD b σ (f τ) cy with
          | none => rw [hy] at hb; simp at hb
          | some oy =>
              rw [hy] at hb
              obtain ⟨a, ha⟩ := h σ τ b oy hP hy
              exact ⟨a + 1, by simp only [CalcVM.evalD]; rw [ha]; exact hb⟩

theorem SimShiftT.letC {f : CalcVM.THeap → CalcVM.THeap} {P : CalcVM.THeap → Prop} {cx cy : Bang.Comp}
    (h : SimShiftT f P cx cy) (N : Bang.Comp) : SimShiftT f P (.letC cx N) (.letC cy N) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b σ (f τ) cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hP hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | ret w =>
                  simp only [Option.bind_some] at hb
                  exact ⟨(max a b) + 1, by
                    simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                    exact evalD_some_le (Nat.le_max_right a b) hb⟩
              | lam M => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | perform _ a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                exact ⟨a + 1, by simp only [CalcVM.evalD, ha, Option.bind_some]; exact hb⟩

theorem SimShiftT.app {f : CalcVM.THeap → CalcVM.THeap} {P : CalcVM.THeap → Prop} {cx cy : Bang.Comp}
    (h : SimShiftT f P cx cy) (u : Bang.Val) : SimShiftT f P (.app cx u) (.app cy u) := by
  intro σ τ b r hP hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b σ (f τ) cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h σ τ b oy hP hy
          cases oy with | mk out st => cases st with | mk s1 s2 => cases out with
            | term t => cases t with
              | lam M =>
                  simp only [Option.bind_some] at hb
                  exact ⟨(max a b) + 1, by
                    simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                    exact evalD_some_le (Nat.le_max_right a b) hb⟩
              | ret w => simp at hb
              | force a => simp at hb
              | letC a a' => simp at hb
              | app a a' => simp at hb
              | perform _ a a' a'' => simp at hb
              | handle a a' => simp at hb
              | case a a' a'' => simp at hb
              | split a a' => simp at hb
              | unfold a => simp at hb
              | oom => simp at hb
              | wrong a => simp at hb
            | raised ℓ op w =>
                simp only [Option.bind_some] at hb
                exact ⟨a + 1, by simp only [CalcVM.evalD, ha, Option.bind_some]; exact hb⟩

theorem evalD_plug_simshiftT {f : CalcVM.THeap → CalcVM.THeap} {P : CalcVM.THeap → Prop} {cx cy : Bang.Comp}
    (hsim : SimShiftT f P cx cy) :
    ∀ {K : Bang.EvalCtx},
      (∀ τ ℓ' Θ', Bang.Frame.handleF (Bang.Handler.transaction ℓ' Θ') ∈ K → f ((ℓ',Θ') :: τ) = (ℓ',Θ') :: f τ) →
      (∀ τ, P τ → ∀ ℓ' Θ', Bang.Frame.handleF (Bang.Handler.transaction ℓ' Θ') ∈ K → P (τ.push ℓ' Θ')) →
    ∀ {σ τ n r}, P τ → CalcVM.evalD n σ (f τ) (plug K cy) = some r →
      ∃ m, CalcVM.evalD m σ τ (plug K cx) = some r
  | [], _, _, σ, τ, n, r, hP, hn => hsim σ τ n r hP (by simpa [plug] using hn)
  | .letF N :: K, hstab, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      exact evalD_plug_simshiftT (SimShiftT.letC hsim N)
        (fun τ' ℓ' Θ' hmem => hstab τ' ℓ' Θ' (by simp [hmem]))
        (fun τ' hP' ℓ' Θ' hmem => hsurv τ' hP' ℓ' Θ' (by simp [hmem])) hP hn
  | .appF u :: K, hstab, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      exact evalD_plug_simshiftT (SimShiftT.app hsim u)
        (fun τ' ℓ' Θ' hmem => hstab τ' ℓ' Θ' (by simp [hmem]))
        (fun τ' hP' ℓ' Θ' hmem => hsurv τ' hP' ℓ' Θ' (by simp [hmem])) hP hn
  | .handleF hh :: K, hstab, hsurv, σ, τ, n, r, hP, hn => by
      rw [plug_cons, Bang.Frame.wrapStep] at hn ⊢
      refine evalD_plug_simshiftT (SimShiftT.handle hsim hh ?_ ?_)
        (fun τ' ℓ' Θ' hmem => hstab τ' ℓ' Θ' (by simp [hmem]))
        (fun τ' hP' ℓ' Θ' hmem => hsurv τ' hP' ℓ' Θ' (by simp [hmem])) hP hn
      · intro τ' ℓ' Θ' hhe; exact hstab τ' ℓ' Θ' (by rw [hhe]; simp)
      · intro τ' hP' ℓ' Θ' hhe; exact hsurv τ' hP' ℓ' Θ' (by rw [hhe]; simp)

theorem txn_mem_ne_of_ctxTxns_none {ℓ : Bang.EffectRow.Label} :
    ∀ {Kᵢ : Bang.EvalCtx}, (CalcVM.ctxTxns Kᵢ).get? ℓ = none →
      ∀ ℓ' Θ', Bang.Frame.handleF (Bang.Handler.transaction ℓ' Θ') ∈ Kᵢ → ℓ' ≠ ℓ := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro _ ℓ' Θ' hmem; simp at hmem
  | cons fr Kᵢ ih =>
      intro hnone ℓ' Θ' hmem
      cases fr with
      | handleF h0 =>
          cases h0 with
          | transaction ℓ0 Θ0 =>
              by_cases hc : ℓ0 = ℓ
              · subst hc
                simp only [CalcVM.ctxTxns, CalcVM.THeap.get?, List.find?, decide_true, Option.map_some] at hnone
                exact absurd hnone (by simp)
              · simp only [CalcVM.ctxTxns, CalcVM.THeap.get?, List.find?, hc, decide_false] at hnone
                rcases List.mem_cons.mp hmem with heq | htl
                · simp only [Bang.Frame.handleF.injEq, Bang.Handler.transaction.injEq] at heq; obtain ⟨h1, _⟩ := heq; subst h1; exact hc
                · exact ih (by simpa [CalcVM.THeap.get?] using hnone) ℓ' Θ' htl
          | state ℓ0 s0 =>
              simp only [CalcVM.ctxTxns] at hnone
              rcases List.mem_cons.mp hmem with heq | htl
              · exact absurd heq (by simp)
              · exact ih hnone ℓ' Θ' htl
          | throws ℓ0 =>
              simp only [CalcVM.ctxTxns] at hnone
              rcases List.mem_cons.mp hmem with heq | htl
              · exact absurd heq (by simp)
              · exact ih hnone ℓ' Θ' htl
      | letF N =>
          simp only [CalcVM.ctxTxns] at hnone
          rcases List.mem_cons.mp hmem with heq | htl
          · exact absurd heq (by simp)
          · exact ih hnone ℓ' Θ' htl
      | appF u =>
          simp only [CalcVM.ctxTxns] at hnone
          rcases List.mem_cons.mp hmem with heq | htl
          · exact absurd heq (by simp)
          · exact ih hnone ℓ' Θ' htl

theorem get?T_push_self (τ : CalcVM.THeap) (ℓ : Bang.EffectRow.Label) (Θ : List Bang.Val) :
    CalcVM.THeap.get? ((ℓ, Θ) :: τ) ℓ = some Θ := by simp [CalcVM.THeap.get?, List.find?]

theorem sim_txn_handle (cap : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Bang.Val) (Θ : List Bang.Val)
    (hop : CalcVM.isTxnOp op = true) {Kᵢ : Bang.EvalCtx}
    (hnone : (CalcVM.ctxTxns Kᵢ).get? ℓ = none) :
    Sim (.handle (.transaction ℓ Θ) (plug Kᵢ (.perform cap ℓ op v)))
        (.handle (.transaction ℓ (CalcVM.txnService op v Θ).2) (plug Kᵢ (.ret (CalcVM.txnService op v Θ).1))) := by
  intro σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD, CalcVM.THeap.push] at hb
      have hfeq : ((ℓ, (CalcVM.txnService op v Θ).2) :: τ : CalcVM.THeap)
          = CalcVM.THeap.put ((ℓ,Θ)::τ) ℓ (CalcVM.txnService op v Θ).2 := by
        simp [CalcVM.THeap.put]
      rw [hfeq] at hb
      cases hy : CalcVM.evalD b σ (CalcVM.THeap.put ((ℓ,Θ)::τ) ℓ (CalcVM.txnService op v Θ).2)
          (plug Kᵢ (.ret (CalcVM.txnService op v Θ).1)) with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          have hne := txn_mem_ne_of_ctxTxns_none hnone
          obtain ⟨a, ha⟩ := evalD_plug_simshiftT (simshiftT_txn cap ℓ op v Θ hop) (K := Kᵢ)
            (fun τ' ℓ' Θ' hmem => put_consT_ne ℓ ℓ' (CalcVM.txnService op v Θ).2 Θ' τ' (hne ℓ' Θ' hmem))
            (fun τ' hP' ℓ' Θ' hmem => by
              simp only [CalcVM.THeap.push, CalcVM.THeap.get?, List.find?, (hne ℓ' Θ' hmem), decide_false] at hP' ⊢
              exact hP')
            (σ := σ) (τ := (ℓ,Θ)::τ)
            (get?T_push_self τ ℓ Θ) hy
          refine ⟨a+1, ?_⟩
          simp only [CalcVM.evalD, CalcVM.THeap.push]
          rw [ha]; exact hb

/-! ### Assembly: splitAt decomposition + the dispatch transfer lemma `evalD_plug_dispatch`. -/

theorem plug_append (A B : Bang.EvalCtx) (c : Bang.Comp) :
    plug (A ++ B) c = plug B (plug A c) := by
  induction A generalizing c with
  | nil => simp [plug]
  | cons fr A ih => rw [List.cons_append, plug_cons, plug_cons, ih]

-- The inner prefix Kᵢ from a splitAt catches NOTHING for (ℓ,op): induction on K.
theorem CalcVM.splitAt_inner_none {ℓ : Bang.EffectRow.Label} {op : Bang.OpId} :
    ∀ {K Kᵢ Kₒ : Bang.EvalCtx} {h : Bang.Handler},
      Bang.splitAt K ℓ op = some (Kᵢ, h, Kₒ) → Bang.splitAt Kᵢ ℓ op = none := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hs; simp [Bang.splitAt] at hs
  | cons fr K ih =>
      intro Kᵢ Kₒ h hs
      cases fr with
      | handleF h0 =>
          simp only [Bang.splitAt] at hs
          by_cases hc : Bang.handlesOp h0 ℓ op = true
          · rw [if_pos hc] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, _, _⟩ := hs; simp [Bang.splitAt]
          · rw [if_neg hc] at hs
            cases hsp : Bang.splitAt K ℓ op with
            | none => rw [hsp] at hs; simp at hs
            | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                        obtain ⟨rfl, rfl, rfl⟩ := hs
                        simp only [Bang.splitAt, if_neg hc, ih hsp, Option.map_none]
      | letF N =>
          simp only [Bang.splitAt] at hs
          cases hsp : Bang.splitAt K ℓ op with
          | none => rw [hsp] at hs; simp at hs
          | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                      obtain ⟨rfl, rfl, rfl⟩ := hs
                      simp only [Bang.splitAt, ih hsp, Option.map_none]
      | appF w =>
          simp only [Bang.splitAt] at hs
          cases hsp : Bang.splitAt K ℓ op with
          | none => rw [hsp] at hs; simp at hs
          | some t => obtain ⟨Ki, h', Ko⟩ := t; rw [hsp] at hs
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                      obtain ⟨rfl, rfl, rfl⟩ := hs
                      simp only [Bang.splitAt, ih hsp, Option.map_none]

-- splitAt none (for a get/put op) ⇒ no state ℓ frame ⇒ CalcVM.ctxStates get? none. Induction on Kᵢ.
theorem ctxStates_none_of_splitAt_none {ℓ : Bang.EffectRow.Label} {op : Bang.OpId}
    (hop : op = "get" ∨ op = "put") :
    ∀ {Kᵢ : Bang.EvalCtx}, Bang.splitAt Kᵢ ℓ op = none → (CalcVM.ctxStates Kᵢ).get? ℓ = none := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro _; simp [CalcVM.ctxStates, CalcVM.SStore.get?]
  | cons fr Kᵢ ih =>
      intro hns
      cases fr with
      | handleF h0 =>
          cases h0 with
          | state ℓ0 s0 =>
              by_cases hc : ℓ0 = ℓ
              · subst hc
                exfalso
                have hcatch : Bang.handlesOp (Bang.Handler.state ℓ0 s0) ℓ0 op = true := by
                  cases hop with | inl h => subst h; simp [Bang.handlesOp] | inr h => subst h; simp [Bang.handlesOp]
                simp only [Bang.splitAt, if_pos hcatch] at hns
                exact absurd hns (by simp)
              · simp only [Bang.splitAt, if_neg (by simp [Bang.handlesOp, hc] : ¬ Bang.handlesOp (Bang.Handler.state ℓ0 s0) ℓ op = true), Option.map_eq_none_iff] at hns
                simp only [CalcVM.ctxStates, CalcVM.SStore.get?, List.find?, hc, decide_false]
                simpa [CalcVM.SStore.get?] using ih hns
          | throws ℓ0 =>
              have hnt : ¬ Bang.handlesOp (Bang.Handler.throws ℓ0) ℓ op = true := by
                cases hop with | inl h => subst h; simp [Bang.handlesOp] | inr h => subst h; simp [Bang.handlesOp]
              simp only [Bang.splitAt, if_neg hnt, Option.map_eq_none_iff] at hns
              simp only [CalcVM.ctxStates]; exact ih hns
          | transaction ℓ0 Θ0 =>
              have hnt : ¬ Bang.handlesOp (Bang.Handler.transaction ℓ0 Θ0) ℓ op = true := by
                cases hop with | inl h => subst h; simp [Bang.handlesOp] | inr h => subst h; simp [Bang.handlesOp]
              simp only [Bang.splitAt, if_neg hnt, Option.map_eq_none_iff] at hns
              simp only [CalcVM.ctxStates]; exact ih hns
      | letF N =>
          simp only [Bang.splitAt, Option.map_eq_none_iff] at hns
          simp only [CalcVM.ctxStates]; exact ih hns
      | appF u =>
          simp only [Bang.splitAt, Option.map_eq_none_iff] at hns
          simp only [CalcVM.ctxStates]; exact ih hns

theorem ctxTxns_none_of_splitAt_none {ℓ : Bang.EffectRow.Label} {op : Bang.OpId}
    (hop : CalcVM.isTxnOp op = true) :
    ∀ {Kᵢ : Bang.EvalCtx}, Bang.splitAt Kᵢ ℓ op = none → (CalcVM.ctxTxns Kᵢ).get? ℓ = none := by
  intro Kᵢ
  induction Kᵢ with
  | nil => intro _; simp [CalcVM.ctxTxns, CalcVM.THeap.get?]
  | cons fr Kᵢ ih =>
      intro hns
      cases fr with
      | handleF h0 =>
          cases h0 with
          | transaction ℓ0 Θ0 =>
              by_cases hc : ℓ0 = ℓ
              · subst hc
                exfalso
                have hcatch : Bang.handlesOp (Bang.Handler.transaction ℓ0 Θ0) ℓ0 op = true := by
                  rcases CalcVM.isTxnOp_iff.mp hop with rfl|rfl|rfl <;> simp [Bang.handlesOp]
                simp only [Bang.splitAt, if_pos hcatch] at hns
                exact absurd hns (by simp)
              · simp only [Bang.splitAt, if_neg (by simp [Bang.handlesOp, hc] : ¬ Bang.handlesOp (Bang.Handler.transaction ℓ0 Θ0) ℓ op = true), Option.map_eq_none_iff] at hns
                simp only [CalcVM.ctxTxns, CalcVM.THeap.get?, List.find?, hc, decide_false]
                simpa [CalcVM.THeap.get?] using ih hns
          | state ℓ0 s0 =>
              have hnt : ¬ Bang.handlesOp (Bang.Handler.state ℓ0 s0) ℓ op = true := by
                rcases CalcVM.isTxnOp_iff.mp hop with rfl|rfl|rfl <;> simp [Bang.handlesOp]
              simp only [Bang.splitAt, if_neg hnt, Option.map_eq_none_iff] at hns
              simp only [CalcVM.ctxTxns]; exact ih hns
          | throws ℓ0 =>
              have hnt : ¬ Bang.handlesOp (Bang.Handler.throws ℓ0) ℓ op = true := by
                rcases CalcVM.isTxnOp_iff.mp hop with rfl|rfl|rfl <;> simp [Bang.handlesOp]
              simp only [Bang.splitAt, if_neg hnt, Option.map_eq_none_iff] at hns
              simp only [CalcVM.ctxTxns]; exact ih hns
      | letF N =>
          simp only [Bang.splitAt, Option.map_eq_none_iff] at hns
          simp only [CalcVM.ctxTxns]; exact ih hns
      | appF u =>
          simp only [Bang.splitAt, Option.map_eq_none_iff] at hns
          simp only [CalcVM.ctxTxns]; exact ih hns

-- dispatchOn for a txn op on a transaction frame: resumes Kᵢ ++ handleF (transaction ℓ Θ') :: Kₒ.
theorem dispatchOn_txn (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Bang.Val) (Θ : List Bang.Val)
    (Kᵢ Kₒ : Bang.EvalCtx) (hop : CalcVM.isTxnOp op = true) :
    Bang.dispatchOn op v (Kᵢ, Bang.Handler.transaction ℓ Θ, Kₒ)
      = some (Kᵢ ++ Bang.Frame.handleF (Bang.Handler.transaction ℓ (CalcVM.txnService op v Θ).2) :: Kₒ,
              .ret (CalcVM.txnService op v Θ).1) := by
  rcases CalcVM.isTxnOp_iff.mp hop with rfl | rfl | rfl
  · simp [Bang.dispatchOn, CalcVM.txnService]
  · simp [Bang.dispatchOn, CalcVM.txnService, (by decide : ("readTVar" == "newTVar") = false)]
  · simp only [Bang.dispatchOn, CalcVM.txnService, (by decide : ("writeTVar" == "newTVar") = false),
      (by decide : ("writeTVar" == "readTVar") = false), Bool.false_eq_true, if_false,
      if_neg (by decide : ¬ ("writeTVar" = "newTVar")), if_neg (by decide : ¬ ("writeTVar" = "readTVar"))]
    cases v with
    | pair iv w => simp
    | _ => simp

-- THE DISPATCH TRANSFER LEMMA. dispatch K = some (K', focus); evalD of plug K' focus reaches
-- (ret w',[],[]) ⇒ so does plug K (up ℓ op v). Case on splitAt + the handler kind.
theorem evalD_plug_dispatch (K : Bang.EvalCtx) (cap : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (v : Bang.Val)
    {K' : Bang.EvalCtx} {focus : Bang.Comp} {w' : Bang.Val} {n : Nat}
    (hd : Bang.dispatch K ℓ op v = some (K', focus))
    (hn : CalcVM.evalD n [] [] (plug K' focus) = some (.term (.ret w'), [], [])) :
    ∃ m, CalcVM.evalD m [] [] (plug K (.perform cap ℓ op v)) = some (.term (.ret w'), [], []) := by
  simp only [Bang.dispatch] at hd
  cases hsp : Bang.splitAt K ℓ op with
  | none => rw [hsp] at hd; simp at hd
  | some t =>
      obtain ⟨Kᵢ, h, Kₒ⟩ := t
      rw [hsp] at hd
      simp only [Option.bind_some] at hd
      have hrec : Kᵢ ++ Bang.Frame.handleF h :: Kₒ = K := CalcVM.splitAt_reconstruct hsp
      have hinner : Bang.splitAt Kᵢ ℓ op = none := CalcVM.splitAt_inner_none hsp
      -- plug K (up ℓ op v) = plug Kₒ (handle h (plug Kᵢ (up ℓ op v)))
      have hplugK : plug K (.perform cap ℓ op v) = plug Kₒ (.handle h (plug Kᵢ (.perform cap ℓ op v))) := by
        rw [← hrec, plug_append, plug_cons, Bang.Frame.wrapStep]
      -- common: from splitAt, handlesOp h ℓ op = true (h IS the catcher).
      have hcatch : Bang.handlesOp h ℓ op = true := CalcVM.splitAt_handles hsp
      cases h with
      | throws ℓ' =>
          -- handlesOp (throws ℓ') ℓ op = (ℓ'=ℓ)&&(op="raise") = true ⇒ ℓ'=ℓ, op="raise".
          simp only [Bang.handlesOp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcatch
          obtain ⟨rfl, rfl⟩ := hcatch
          simp only [Bang.dispatchOn] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd
          rw [hplugK]
          exact evalD_plug_sim (sim_abort_handle cap ℓ' v hinner) hn
      | state ℓ' s =>
          simp only [Bang.handlesOp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
            beq_iff_eq] at hcatch
          obtain ⟨rfl, hgp⟩ := hcatch
          have hns : (CalcVM.ctxStates Kᵢ).get? ℓ' = none :=
            ctxStates_none_of_splitAt_none hgp hinner
          rw [hplugK]
          rcases hgp with rfl | rfl
          · -- op = "get"
            simp only [Bang.dispatchOn, beq_self_eq_true, if_true] at hd
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd
            rw [plug_append, plug_cons, Bang.Frame.wrapStep] at hn
            exact evalD_plug_sim (sim_get_handle cap ℓ' s v hns) hn
          · -- op = "put"
            simp only [Bang.dispatchOn, if_neg (by decide : ¬ ("put" == "get") = true)] at hd
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd
            rw [plug_append, plug_cons, Bang.Frame.wrapStep] at hn
            exact evalD_plug_sim (sim_put_handle cap ℓ' s v hns) hn
      | transaction ℓ' Θ =>
          simp only [Bang.handlesOp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
            beq_iff_eq] at hcatch
          obtain ⟨rfl, hgp⟩ := hcatch
          have hopt : CalcVM.isTxnOp op = true := by
            rcases hgp with (rfl | rfl) | rfl
            · rfl
            · rfl
            · rfl
          have hns : (CalcVM.ctxTxns Kᵢ).get? ℓ' = none := ctxTxns_none_of_splitAt_none hopt hinner
          rw [hplugK]
          -- dispatchOn transaction: K' = Kᵢ ++ handleF (transaction ℓ' Θ') :: Kₒ, focus = ret r.
          have hres := dispatchOn_txn ℓ' op v Θ Kᵢ Kₒ hopt
          rw [hres] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd
          rw [plug_append, plug_cons, Bang.Frame.wrapStep] at hn
          exact evalD_plug_sim (sim_txn_handle cap ℓ' op v Θ hopt hns) hn

/-- `evalD`-completeness for the pure fragment, generalized over the frame stack:
a terminating CK run is big-stepped by `evalD` of the plugged term. Strong
induction on the small-step fuel `F`. -/
theorem evalD_complete_gen : ∀ (F : Nat) (K : Bang.EvalCtx) (c : Comp) (v : Bang.Val),
    Config.run F (K, c) = Result.done v →
    ∃ n, CalcVM.evalD n [] [] (plug K c) = some (.term (.ret v), [], []) := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro K c v hrun
    cases F with
    | zero => simp [Config.run] at hrun
    | succ F' =>
      by_cases hterm : ∃ w, (K, c) = ([], Comp.ret w)
      · obtain ⟨w, hKc⟩ := hterm
        simp only [Prod.mk.injEq] at hKc
        obtain ⟨hK0, hcw⟩ := hKc; subst hK0; subst hcw
        simp only [Config.run, Result.done.injEq] at hrun
        subst hrun
        exact ⟨1, by simp [plug, CalcVM.evalD]⟩
      · have hstep := Config.run_step F' (K, c) (fun w h => hterm ⟨w, h⟩)
        rw [hrun] at hstep
        cases c with
        | ret w =>
            cases K with
            | nil => exact absurd ⟨w, rfl⟩ hterm
            | cons fr K' =>
                cases fr with
                | letF N =>
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.subst w N) = Result.done v := hstep.symm
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.subst w N) v hrun'
                    exact evalD_plug_letC_ret K' w N n hn
                | appF u =>
                    simp only [Source.step] at hstep
                    exact absurd hstep (by simp [Config.run])
                | handleF h =>
                    -- handler RETURN (Q6 identity): (handleF h :: K', ret w) ↦ (K', ret w).
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.ret w) = Result.done v := hstep.symm
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.ret w) v hrun'
                    exact evalD_plug_handleF_ret K' h w n hn
        | lam M =>
            cases K with
            | nil => simp [Config.run, Source.step] at hrun
            | cons fr K' =>
                cases fr with
                | letF N =>
                    simp only [Source.step] at hstep
                    exact absurd hstep (by simp [Config.run])
                | appF u =>
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.subst u M) = Result.done v := hstep.symm
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.subst u M) v hrun'
                    exact evalD_plug_app_lam K' u M n hn
                | handleF h =>
                    -- (handleF h :: K', lam M): `lam` is not a `ret`; handler-return needs `ret` ⇒ stuck.
                    simp only [Source.step] at hstep
                    exact absurd hstep (by simp [Config.run])
        | letC M N =>
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.letF N :: K, M) = Result.done v := hstep.symm
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.letF N :: K) M v hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn
            exact ⟨n, hn⟩
        | app M u =>
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.appF u :: K, M) = Result.done v := hstep.symm
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.appF u :: K) M v hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn
            exact ⟨n, hn⟩
        | force w =>
            cases w with
            | vthunk M =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, M) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K M v hrun'
                exact evalD_plug_force K M n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | perform cap ℓ op v0 =>
            -- DISPATCH: (K, perform cap ℓ op v0) ↦ dispatch K ℓ op v0 (the reverse of run_evalD's raise-part).
            -- splitAt continuation-capture + state/txn-resume/throws-abort, discharged by the dispatch
            -- transfer lemma `evalD_plug_dispatch` (the get/put/txn handle-Sims + the abort Raises-fwd).
            simp only [Source.step] at hstep
            cases hdsp : Bang.dispatch K ℓ op v0 with
            | none => rw [hdsp] at hstep; exact absurd hstep.symm (by simp [Config.run])
            | some Kf =>
                obtain ⟨K', focus⟩ := Kf
                rw [hdsp] at hstep
                have hrun' : Config.run F' (K', focus) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K' focus v hrun'
                exact evalD_plug_dispatch K cap ℓ op v0 hdsp hn
        | handle h M =>
            -- PUSH: (K, handle h M) ↦ (handleF h :: K, M). plug (handleF h :: K) M = plug K (handle h M),
            -- so this closes DIRECTLY (like letC/app PUSH) — NO σ/τ threading at the reverse-bridge level
            -- (evalD's own handle arm threads the stores internally; the bridge runs at [] [] throughout).
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.handleF h :: K, M) = Result.done v := hstep.symm
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.handleF h :: K) M v hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn
            exact ⟨n, hn⟩
        | case w N₁ N₂ =>
            cases w with
            | inl vp =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.subst vp N₁) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.subst vp N₁) v hrun'
                exact evalD_plug_case_inl K vp N₁ N₂ n hn
            | inr vp =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.subst vp N₂) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.subst vp N₂) v hrun'
                exact evalD_plug_case_inr K vp N₁ N₂ n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | split w N =>
            cases w with
            | pair vp up =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.subst vp (Comp.subst (Val.shift up) N)) = Result.done v :=
                  hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.subst vp (Comp.subst (Val.shift up) N)) v hrun'
                exact evalD_plug_split K vp up N n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | unfold w =>
            cases w with
            | fold vp =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.ret vp) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.ret vp) v hrun'
                exact evalD_plug_unfold K vp n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | oom => exact absurd hstep (by simp [Source.step, Config.run])
        | wrong s => exact absurd hstep (by simp [Source.step, Config.run])

/-- The PURE-fragment reverse bridge (sorry-free), routing `compile_forward_sim_pure`. Same shape
as the total `evalD_complete_gen` but `PureCtx`/`Comp.Pure`-gated, so the `up`/`handle`/`handleF`
arms close by ABSURD (a pure program has no effect ops / handlers) — keeping the PURE headline
AXIOM-CLEAN (it never routes through the dispatch sorry). -/
theorem evalD_complete_gen_pure : ∀ (F : Nat) (K : Bang.EvalCtx) (c : Comp) (v : Bang.Val),
    PureCtx K → Wasmfx.Comp.Pure c →
    Config.run F (K, c) = Result.done v →
    ∃ n, CalcVM.evalD n [] [] (plug K c) = some (.term (.ret v), [], []) := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro K c v hK hc hrun
    cases F with
    | zero => simp [Config.run] at hrun
    | succ F' =>
      by_cases hterm : ∃ w, (K, c) = ([], Comp.ret w)
      · obtain ⟨w, hKc⟩ := hterm
        simp only [Prod.mk.injEq] at hKc
        obtain ⟨hK0, hcw⟩ := hKc; subst hK0; subst hcw
        simp only [Config.run, Result.done.injEq] at hrun
        subst hrun
        exact ⟨1, by simp [plug, CalcVM.evalD]⟩
      · have hstep := Config.run_step F' (K, c) (fun w h => hterm ⟨w, h⟩)
        rw [hrun] at hstep
        cases c with
        | ret w =>
            cases K with
            | nil => exact absurd ⟨w, rfl⟩ hterm
            | cons fr K' =>
                cases fr with
                | letF N =>
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.subst w N) = Result.done v := hstep.symm
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.subst w N) v hK.2
                      (Wasmfx.subst_pure (by simpa only [Wasmfx.Comp.Pure] using hc) (by simp only [PureCtx] at hK; exact hK.1)) hrun'
                    exact evalD_plug_letC_ret K' w N n hn
                | appF u =>
                    simp only [Source.step] at hstep
                    exact absurd hstep (by simp [Config.run])
                | handleF h => simp only [PureCtx] at hK
        | lam M =>
            cases K with
            | nil => simp [Config.run, Source.step] at hrun
            | cons fr K' =>
                cases fr with
                | letF N => simp only [Source.step] at hstep; exact absurd hstep (by simp [Config.run])
                | appF u =>
                    simp only [Source.step] at hstep
                    have hrun' : Config.run F' (K', Comp.subst u M) = Result.done v := hstep.symm
                    obtain ⟨n, hn⟩ := ih F' (by omega) K' (Comp.subst u M) v hK.2
                      (Wasmfx.subst_pure (by simp only [PureCtx] at hK; exact hK.1) (by simpa only [Wasmfx.Comp.Pure] using hc)) hrun'
                    exact evalD_plug_app_lam K' u M n hn
                | handleF h => simp only [PureCtx] at hK
        | letC M N =>
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.letF N :: K, M) = Result.done v := hstep.symm
            simp only [Wasmfx.Comp.Pure] at hc
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.letF N :: K) M v (by simp only [PureCtx]; exact ⟨hc.2, hK⟩) hc.1 hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn; exact ⟨n, hn⟩
        | app M u =>
            simp only [Source.step] at hstep
            have hrun' : Config.run F' (Frame.appF u :: K, M) = Result.done v := hstep.symm
            simp only [Wasmfx.Comp.Pure] at hc
            obtain ⟨n, hn⟩ := ih F' (by omega) (Frame.appF u :: K) M v (by simp only [PureCtx]; exact ⟨hc.2, hK⟩) hc.1 hrun'
            rw [plug_cons] at hn; simp only [Frame.wrapStep] at hn; exact ⟨n, hn⟩
        | force w =>
            cases w with
            | vthunk M =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, M) = Result.done v := hstep.symm
                simp only [Wasmfx.Comp.Pure] at hc
                obtain ⟨n, hn⟩ := ih F' (by omega) K M v hK hc hrun'
                exact evalD_plug_force K M n hn
            | _ => simp only [Wasmfx.Comp.Pure] at hc
        | perform _ ℓ op v0 => simp only [Wasmfx.Comp.Pure] at hc   -- pure ⇒ no `perform`
        | handle h M => simp only [Wasmfx.Comp.Pure] at hc   -- pure ⇒ no `handle`
        | case w N₁ N₂ =>
            simp only [Wasmfx.Comp.Pure] at hc
            cases w with
            | inl vp =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.subst vp N₁) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.subst vp N₁) v hK
                  (Wasmfx.subst_pure (by simpa only [Wasmfx.Val.Pure] using hc.1) hc.2.1) hrun'
                exact evalD_plug_case_inl K vp N₁ N₂ n hn
            | inr vp =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.subst vp N₂) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.subst vp N₂) v hK
                  (Wasmfx.subst_pure (by simpa only [Wasmfx.Val.Pure] using hc.1) hc.2.2) hrun'
                exact evalD_plug_case_inr K vp N₁ N₂ n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | split w N =>
            simp only [Wasmfx.Comp.Pure] at hc
            cases w with
            | pair vp up =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.subst vp (Comp.subst (Val.shift up) N)) = Result.done v := hstep.symm
                have hvu : Wasmfx.Val.Pure vp ∧ Wasmfx.Val.Pure up := by simpa only [Wasmfx.Val.Pure] using hc.1
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.subst vp (Comp.subst (Val.shift up) N)) v hK
                  (Wasmfx.subst_pure hvu.1 (Wasmfx.subst_pure (Wasmfx.Val.shiftFrom_pure 0 hvu.2) hc.2)) hrun'
                exact evalD_plug_split K vp up N n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | unfold w =>
            simp only [Wasmfx.Comp.Pure] at hc
            cases w with
            | fold vp =>
                simp only [Source.step] at hstep
                have hrun' : Config.run F' (K, Comp.ret vp) = Result.done v := hstep.symm
                obtain ⟨n, hn⟩ := ih F' (by omega) K (Comp.ret vp) v hK (by simpa only [Wasmfx.Comp.Pure, Wasmfx.Val.Pure] using hc) hrun'
                exact evalD_plug_unfold K vp n hn
            | _ => exact absurd hstep (by simp [Source.step, Config.run])
        | _ => simp only [Wasmfx.Comp.Pure] at hc

/-- `evalD`-completeness (pure fragment, closed): `Source.eval F c = done v ⟹
∃n, evalD n [] [] c = some(.term(.ret v),[],[])`. The `K = []` instance of
`evalD_complete_gen`. -/
theorem evalD_complete (F : Nat) (c : Comp) (v : Bang.Val)
    (hpure : Wasmfx.Comp.Pure c) (h : Source.eval F c = Result.done v) :
    ∃ n, CalcVM.evalD n [] [] c = some (.term (.ret v), [], []) := by
  -- routes through the PURE bridge (sorry-free) — keeps `compile_forward_sim_pure` axiom-clean.
  have := evalD_complete_gen_pure F [] c v (by simp [PureCtx]) hpure h
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
  have hsim := Wasmfx.exec_wexec_sim F (CalcVM.compile c []) [] [.ret v] [] hcp
    (fun _ hm => by simp at hm) (fun _ hm => by simp at hm) hexec
  refine ⟨F, ?_⟩
  -- injStack [.ret v] = [compileV v]; wexec yields it.
  rw [show Wasmfx.injStack [Comp.ret v] = [compileV v] from by
    simp [Wasmfx.injStack, injTerminal]] at hsim
  -- `run` reduces on `wexec … = some [compileV v]` (singleton-operand-stack ⇒ done).
  have hb : Wasmfx.wexec F (compileC c).body [] [] = some [compileV v] := hsim
  show Wasmfx.run F (compileC c) = Result.done (compileV v)
  unfold Wasmfx.run
  rw [hb]

/-- `compile_forward_sim` proof. BOTH branches are proven: the PURE fragment axiom-clean
(`compile_forward_sim_pure`, GAP 1 closed) and the NON-pure fragment (`up`/`handle`) via the
total reverse bridge `evalD_complete_gen` + `exec_wexec_sim_ok` (GAP 2 closed).

  MODEL STATUS: the WASM model is SOUND for handlers — `wexec` re-`compile`s residual
  `subst …` THREADING the CalcVM continuation, so a re-compiled `handle` body's `markH`
  captures the TRUE outer continuation (the former stop-early abort defect is FIXED; the §7b
  probes are the build-enforced witnesses, `wexec ≡ Source.eval` on handler programs incl. the
  ex-counterexample). -/
theorem compile_forward_sim_proof {c : Comp} {v : Val} {fuel : Nat}
    (h : Source.eval fuel c = Result.done v) :
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := by
  by_cases hpure : Wasmfx.Comp.Pure c
  · -- PURE fragment: GAP 1 closed, axiom-clean.
    exact compile_forward_sim_pure hpure h
  · -- NON-pure (handlers): GAP 2 CLOSED — re-wire of the now-TOTAL reverse bridge
    -- (`evalD_complete_gen`, the dispatch transfer closed it) through the HANDLER-COMPLETE
    -- WASM lowering (`exec_wexec_sim_ok`, drops `CodePure`, MARK/UNMARK/OP arms proven). Mirrors
    -- the pure arm with the `_ok`/total versions; `Source.eval = Config.run ([],·)` definitionally.
    have hrun : Config.run fuel ([], c) = Result.done v := h
    obtain ⟨n, hn⟩ := evalD_complete_gen fuel [] c v hrun
    rw [show plug [] c = c from rfl] at hn
    obtain ⟨F, hexec⟩ := CalcVM.compile_correct n c (.ret v) [] [] hn
    have hCodeOk : Wasmfx.CodeOk (CalcVM.compile c []) :=
      Wasmfx.compile_ok c ((Wasmfx.CodeOk_iff_forall []).mpr (by intro i hi; simp at hi))
    have hHsOk : Wasmfx.HStackOk ([] : CalcVM.HStack) := by intro fr hfr; simp at hfr
    have hsim := Wasmfx.exec_wexec_sim_ok F (CalcVM.compile c []) [] [.ret v] [] hCodeOk hHsOk hexec
    refine ⟨F, ?_⟩
    rw [show Wasmfx.injStack [Comp.ret v] = [compileV v] from by
      simp [Wasmfx.injStack, injTerminal]] at hsim
    have hb : Wasmfx.wexec F (compileC c).body [] [] = some [compileV v] := hsim
    show Wasmfx.run F (compileC c) = Result.done (compileV v)
    unfold Wasmfx.run
    rw [hb]

/-! ## §7b — HANDLER soundness probes (◊5 — wexec ≡ kernel, including the FORMER defect)

These probes pin `Wasmfx.run` (`wexec`) ≡ `Source.eval` (the kernel) on handler
programs. They include the case that USED to be a counterexample — the residual-arm
model defect — now AGREEING after the threaded-continuation fix.

THE FORMER DEFECT (fixed by the threaded-continuation representation): `wexec`'s SUBST/APP/CASE/SPLIT arms ran
`lowerCode (compile body []) ++ c`. When `body` contained a `handle`, `compile body
[]` baked the markH savedCode = `[]` (NOT the real outer continuation `c`); a zero-shot
ABORT then resumed `[]` and STOPPED early. THE FIX (Lindley et al. 2025 §1.3 epilogue
annotation): the residual WASM instrs (`bindS`/`callS`/`caseS`/`splitS`) now CARRY the
CalcVM continuation `c`, so the residual re-`compile (subst …) c` threads it WHOLE and
the markH captures the TRUE `c` — exactly as `exec`'s MARK does. The counterexample
below now returns the kernel's result (100), the build-enforced witness that the fix
landed. -/

-- state resume (no abort, savedCode unused): wexec ≡ kernel.
example : Source.eval 50 (.handle (.state 0 (.vint 42)) (.perform 0 0 "get" .vunit)) = Result.done (.vint 42) := by rfl
example : Wasmfx.run 50 (compileC (.handle (.state 0 (.vint 42)) (.perform 0 0 "get" .vunit)))
    = Result.done (.i32 42) := by rfl

-- abort, outer cont = identity-on-the-value: wexec ≡ kernel (7).
example : Source.eval 50
    (.letC (.handle (.throws 0) (.letC (.perform 0 0 "raise" (.vint 7)) (.ret (.vint 99)))) (.ret (.vvar 0)))
    = Result.done (.vint 7) := by rfl
example : Wasmfx.run 50
    (compileC (.letC (.handle (.throws 0) (.letC (.perform 0 0 "raise" (.vint 7)) (.ret (.vint 99)))) (.ret (.vvar 0))))
    = Result.done (.i32 7) := by rfl

-- ✓ THE FORMER COUNTEREXAMPLE — now AGREES. An APP β-residual produces a `handle` that
-- ABORTS; the outer let-cont IGNORES the aborted value (7) and returns 100. The kernel returns
-- 100, and `wexec` NOW returns 100 too (the threaded continuation reaches the outer cont, no
-- stop-early). This `rfl` is the build-enforced witness that the residual-arm fix is SOUND.
example : Source.eval 80
    (.letC (.app (.lam (.handle (.throws 0) (.letC (.perform 0 0 "raise" (.vint 7)) (.ret (.vint 99))))) .vunit)
           (.force (.vthunk (.ret (.vint 100)))))
    = Result.done (.vint 100) := by rfl
example : Wasmfx.run 80
    (compileC (.letC (.app (.lam (.handle (.throws 0) (.letC (.perform 0 0 "raise" (.vint 7)) (.ret (.vint 99))))) .vunit)
                     (.force (.vthunk (.ret (.vint 100))))))
    = Result.done (.i32 100)   -- ✓ SOUND: the threaded outer cont returns 100 (was i32 7 pre-fix)
    := by rfl

-- ✓ TRANSACTION RESUME — `wexec`'s new `wTxnUpdate` branch (operator ruling: verify txn). A
-- `transaction` handler services `newTVar 5` then `readTVar 0` IN PLACE (one-shot resume), reading
-- back 5. wexec ≡ kernel — the build-enforced witness that the txn OP-resume branch is sound (NOT
-- the old abort/fall-through that the missing branch would have produced).
example : Source.eval 50
    (.handle (.transaction 0 []) (.letC (.perform 0 0 "newTVar" (.vint 5)) (.perform 0 0 "readTVar" (.vint 0))))
    = Result.done (.vint 5) := by rfl
example : Wasmfx.run 50
    (compileC (.handle (.transaction 0 []) (.letC (.perform 0 0 "newTVar" (.vint 5)) (.perform 0 0 "readTVar" (.vint 0)))))
    = Result.done (.i32 5) := by rfl

end Bang
