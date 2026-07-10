/-
  WasmEmit.lean — the ◊5.5 EMISSION rung-1 SPIKE (pure ⊥-row arithmetic → real `.wat`).
  ─────────────────────────────────────────────────────────────────────────────────────
  STATUS: TESTED-stratum SPIKE (not proof-bearing). This is the first module that turns a
  bang `Comp` into BYTES a real engine runs (`wasmtime run out.wat`) — closing, for the
  smallest fragment, the model↔reality gap the ROADMAP's ◊5 honesty note names ("the engine
  round-trip never ran"). See `docs/notes/emission-rung1-probe.md` for the full design +
  verification story + the rung-2 wall.

  LEAF: imports `Bang.Backend.AbstractMachine` (for `Comp`/`Val`/`BinOp`), imported by NOTHING
  in `Bang/` (grep-check: no `import Bang.Backend.WasmEmit` outside this file). It rides the
  `Bang.+` build glob so `lake build` (the gate) compiles it — but it touches no proof-bearing
  definition and adds no axiom (self-tests are `by rfl`).

  WHY EMIT FROM THE TYPED `Comp`, NOT FROM `Code` (the design pivot — argued in the note):
  `compile`'s pure arithmetic image is DEGENERATE — every closed `binop` constant-FOLDS to a
  single `RET v` at compile time (`compile (binop add (vint 1) (vint 2)) c = RET (vint 3) :: c`,
  verified in `scratch/EmitProbe`). Emitting from `Code` would therefore emit a wasm module that
  returns a PRECOMPUTED constant — the interpreter's answer, not a compiled program; it would not
  exercise wasm arithmetic at all. Worse, `SUBST`/`APP` carry RESIDUAL `Comp`s that `exec`
  re-`compile`s AT RUNTIME under fuel — a static emitter can't consume them without BEING the
  interpreter. The honest rung-1 emitter is a STRUCTURAL recursion over the typed `Comp` that maps
  each pure former to native wasm (`binop add → i64.add`, `vint n → i64.const`, `letC → locals`),
  preserving arithmetic AS wasm computation. That matches ADR-0059 rung 1 ("pure → native Wasm,
  direct calls, native stack, engine codegen"). The oracle stays `Source.eval` (invariant #1).

  SCOPE (deliberately one fragment): closed ⊥-row INTEGER arithmetic + `let`-bindings — i.e.
  `vint`, `vvar`, `ret`, `binop {add,sub,mul,div}`, `letC`. Comparisons (`lt`/`eq`) return the
  sum-encoded `boolVal` (`inl unit`/`inr unit`), which needs a struct/memory rep — a rung-1.5 item
  named in the note, NOT emitted here. `app`/`lam`/`force` are the stretch (non-recursive call);
  the note maps them, the spike emits arithmetic only (ONE running program > five half-mapped).
-/
module

public import Bang.Backend.AbstractMachine

namespace Bang.WasmEmit

open Bang

-- Module reveal (Phase 1a idiom, mirrors Surface): the leaf runner exe `EmitMain` (outside the
-- `Bang.+` glob) and the differential harness consume `emitModule` + the sample `progN`, and the
-- `by decide`/`simp` self-tests need the equations exposed. `@[expose] public section` makes the
-- definitions visible + reducible across the plain `import` boundary.
@[expose] public section

/-- Result of an emission attempt: either the wasm expression text (an S-expr fragment that
leaves ONE i64 on the stack) or a reason this `Comp` is outside the rung-1 pure fragment.
Fail-LOUD (invariant #1 discipline): an unsupported former is a NAMED refusal, never a silent
wrong emission. -/
inductive Emit where
  | ok    : String → Emit
  | unsup : String → Emit
  deriving Repr, DecidableEq, Inhabited

/-- Did emission succeed? (used by the self-tests as a clean `Bool` regression guard). -/
def Emit.isOk : Emit → Bool
  | .ok _ => true
  | .unsup _ => false

/-- The wasm text for a `BinOp` on two i64 operands. Arithmetic only (rung-1 scope);
comparisons are refused (they'd need the sum-encoded bool rep — see the note). -/
def binOpWat : BinOp → Option String
  | .add => some "i64.add"
  | .sub => some "i64.sub"
  | .mul => some "i64.mul"
  | .div => some "i64.div_s"   -- signed (bang Int is signed); wasm div_s traps on /0, matching a
                               -- CHECKED div — bang's kernel `div` is total (a/0 = 0), so /0 is a
                               -- KNOWN rung-1 mismatch, flagged in the note (do not emit constant /0).
  | .lt | .eq => none          -- comparisons ⇒ sum-encoded bool ⇒ out of rung-1 (note: rung-1.5)

/-- Emit a `Val` as an i64-leaving wasm expression, given the current de-Bruijn depth→local
map `env` (env.get? i = the wasm local index bound to `vvar i`, innermost = env.head). -/
def emitVal (env : List Nat) : Val → Emit
  | .vint n => .ok s!"(i64.const {n})"
  | .vvar i =>
      match env[i]? with
      | some l => .ok s!"(local.get {l})"
      | none   => .unsup s!"free vvar {i} (open term — rung-1 emits closed programs only)"
  | .vunit  => .unsup "vunit (no i64 rep in rung-1)"
  | .vcap _ _ => .unsup "vcap (effect capability — not pure ⊥-row)"
  | .vthunk _ => .unsup "vthunk (needs force/closure — stretch, not rung-1 arithmetic)"
  | .inl _ | .inr _ | .pair _ _ | .fold _ =>
      .unsup "ADT value (sum/product/μ — needs struct rep, rung-1.5)"

/-- Emit a pure `Comp` as an i64-leaving wasm expression. `env` maps de-Bruijn depth to wasm
local index; `next` is the next-free local index (for `letC`'s freshly-bound local). Returns
the expression text AND the total number of locals used (so the caller can declare them).

`letC M N`: compute M, `local.set` it into local `next`, then emit N under the extended env
(`next :: env`) — the wasm-locals image of a de-Bruijn binder. Emitted as a `(block (result i64) …)`?
No — simpler and native: a wasm SEQUENCE `(local.set $k (…M…)) (…N…)`. We return the two-part text. -/
def emitComp (env : List Nat) (next : Nat) : Comp → Emit × Nat
  | .ret v => (emitVal env v, next)
  | .binop op a b =>
      match binOpWat op with
      | none => (.unsup s!"comparison binop (lt/eq) — sum-encoded bool, rung-1.5", next)
      | some w =>
          match emitVal env a, emitVal env b with
          | .ok ea, .ok eb => (.ok s!"({w} {ea} {eb})", next)
          | .unsup r, _ => (.unsup r, next)
          | _, .unsup r => (.unsup r, next)
  | .letC m n =>
      -- compute m into local `next`; run n with (next :: env), next local = next+1.
      let (em, _) := emitComp env next m
      match em with
      | .unsup r => (.unsup r, next)
      | .ok emS =>
          let (en, maxLocal) := emitComp (next :: env) (next + 1) n
          match en with
          | .unsup r => (.unsup r, next)
          | .ok enS =>
              -- (local.set $next em) then leave the value of n. A wasm `(block (result i64) ...)`
              -- would need `br`; simpler: emit `em` set + `en` as a two-statement sequence. The
              -- FUNCTION body wraps these; here we thread the SEQUENCE text with a marker split by \n.
              (.ok s!"(local.set {next} {emS})\n    {enS}", maxLocal)
  | .force _ => (.unsup "force (needs thunk/closure — stretch)", next)
  | .lam _ => (.unsup "lam (function value — stretch, non-recursive call)", next)
  | .app _ _ => (.unsup "app (call — stretch)", next)
  | .perform _ _ _ => (.unsup "perform (effect — not pure ⊥-row)", next)
  | .handle _ _ => (.unsup "handle (effect handler — not pure ⊥-row)", next)
  | .case _ _ _ => (.unsup "case (sum elim — rung-1.5)", next)
  | .split _ _ => (.unsup "split (product elim — rung-1.5)", next)
  | .unfold _ => (.unsup "unfold (μ elim — rung-1.5)", next)
  | .oom => (.unsup "oom", next)
  | .wrong s => (.unsup s!"wrong: {s}", next)

/-- Whole-module emission: wrap the pure-fragment body in a wasm module exporting `main : () → i64`,
declaring the `numLocals` i64 locals the `letC`s used. Returns the full `.wat` text or a refusal.

The module is CORE wasm 3.0 — no GC, no exceptions, no imports — so it runs on ANY engine
(`wasmtime run out.wat`), matching ADR-0059 rung 1 ("core wasm on ANY engine"). -/
def emitModule (M : Comp) : Emit :=
  let (body, numLocals) := emitComp [] 0 M
  match body with
  | .unsup r => .unsup r
  | .ok b =>
      let localDecls :=
        (List.range numLocals).foldl (fun acc _ => acc ++ " (local i64)") ""
      .ok s!"(module\n  (func $main (export \"main\") (result i64){localDecls}\n    {b})\n)"

-- ── SELF-TESTS (by rfl — axiom-clean; part of the `lake build` gate) ─────────────────────

-- Sample programs (mirror scratch/EmitProbe — the arithmetic that runs end-to-end).
/-- `1 + 2` -/
def prog0 : Comp := .binop .add (.vint 1) (.vint 2)
/-- `let x = 1 + 2 in x * 3`  ⇒ 9 -/
def prog1 : Comp := .letC (.binop .add (.vint 1) (.vint 2)) (.binop .mul (.vvar 0) (.vint 3))
/-- `let x = 5 in x + 10`  ⇒ 15 -/
def prog2 : Comp := .letC (.ret (.vint 5)) (.binop .add (.vvar 0) (.vint 10))
/-- `let x = 2 * 3 in let y = x + 4 in y - 1`  ⇒ 9  (nested lets) -/
def prog3 : Comp :=
  .letC (.binop .mul (.vint 2) (.vint 3))
        (.letC (.binop .add (.vvar 0) (.vint 4))
               (.binop .sub (.vvar 0) (.vint 1)))

-- The emitter produces `ok`, not a refusal, on every pure sample (structural regression guard).
-- `decide` (not `rfl`): the `s!"…"` interpolation in emitted text blocks definitional `rfl`, but
-- `Emit.isOk` (a constructor tag test) is decidable and evaluates — kernel-checked, no extra axiom.
-- Regression guards: `simp` rewrites through the emit equations (unfolding the sample `def` +
-- every emit function), landing on a constructor-tag test. Kernel-checked; no `native_decide`,
-- so no `Lean.ofReduceBool` enters the axiom set.
set_option linter.unusedSimpArgs false
example : (emitModule prog0).isOk = true := by
  simp [prog0, emitModule, emitComp, emitVal, binOpWat, Emit.isOk]
example : (emitModule prog1).isOk = true := by
  simp [prog1, emitModule, emitComp, emitVal, binOpWat, Emit.isOk]
example : (emitModule prog2).isOk = true := by
  simp [prog2, emitModule, emitComp, emitVal, binOpWat, Emit.isOk]
example : (emitModule prog3).isOk = true := by
  simp [prog3, emitModule, emitComp, emitVal, binOpWat, Emit.isOk]

-- Refusals are LOUD, not silent: an effectful/ADT former yields `unsup`, never a wrong `ok`.
example : (emitModule (.perform (.vcap 0 0) "op" .vunit)).isOk = false := by
  simp [emitModule, emitComp, Emit.isOk]
example : (emitModule (.ret .vunit)).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]

end -- public section

end Bang.WasmEmit
