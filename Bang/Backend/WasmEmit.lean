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

/-- The wasm text for a straight-line `BinOp` on two i64 operands (a single infix instruction).
`div` is NOT here — it needs a divisor-zero GUARD (`emitDiv`), and comparisons need the
sum-encoded bool rep + a `case` context (`emitCmpCase`). Both are handled in `emitComp`
directly, not through this table (rung-1.5). -/
def binOpWat : BinOp → Option String
  | .add => some "i64.add"
  | .sub => some "i64.sub"
  | .mul => some "i64.mul"
  | .div => none               -- guarded separately (emitDiv): kernel `a/0 = 0`, wasm div_s traps
  | .lt | .eq => none          -- comparisons ⇒ sum-encoded bool ⇒ need a `case` context (emitCmpCase)

/-- Guarded division — REVIEWER-RULED semantics (rung-1.5): the kernel's `div` is TOTAL,
`a / 0 = 0` (Lean `Int` division, `BinOp.eval div`, IR.lean:184). wasm's `i64.div_s` TRAPS on a
zero divisor, so a bare emission would diverge from `Source.eval` exactly at div-by-zero — and
the reference wins (invariant #1: proof rides the reference; invariant #7: the guard's extra
instructions are free, performance is second-class).

The guard tests `i64.eqz` of the divisor and yields `0` when it is zero, else `div_s`. The
operands `ea`/`eb` are pure `Val` expressions (`i64.const`/`local.get` — no side effects, no
traps), so duplicating `eb` in both the test and the divide is safe (no scratch local needed).

  (if (result i64) (i64.eqz <eb>)
    (then (i64.const 0))
    (else (i64.div_s <ea> <eb>)))

Known residual gap (NOT this slice): `i64.div_s` also traps on `INT64_MIN / -1` (signed
overflow). That is the pre-existing unbounded-`Int`→i64 edge (probe note §4.1, the bignum gap),
orthogonal to div-by-zero; the corpus stays within the i64-representable range. -/
def emitDiv (ea eb : String) : String :=
  s!"(if (result i64) (i64.eqz {eb})\n      (then (i64.const 0))\n      (else (i64.div_s {ea} {eb})))"

/-- The wasm comparison instruction for a comparison `BinOp` — used ONLY inside the fused
`letC cmp; case` if-then-else pattern (a comparison result has no standalone i64 rep). Each
leaves an i32 `0`/`1` on the stack, exactly what a wasm `if` condition consumes. Signed `lt_s`
(bang `Int` is signed); `eq` is sign-agnostic. Arithmetic ops return `none` (not comparisons). -/
def cmpWat : BinOp → Option String
  | .lt => some "i64.lt_s"
  | .eq => some "i64.eq"
  | .add | .sub | .mul | .div => none

/-- Emit a `Val` as an i64-leaving wasm expression, given the current de-Bruijn depth→local
map `env` (env[i]? = the wasm-local binding of `vvar i`, innermost = env.head).

Each slot is an `Option Nat`: `some l` = the de Bruijn var is bound to wasm local `l`;
`none` = bound-but-UNUSABLE (a `case`-on-bool payload — `boolVal` carries `vunit`, which has no
i64 rep, so a branch referencing its payload is out of the rung-1.5 fragment, `unsup` not a
wrong `local.get`). This models the de Bruijn binder even when no wasm local backs it. -/
def emitVal (env : List (Option Nat)) : Val → Emit
  | .vint n => .ok s!"(i64.const {n})"
  | .vvar i =>
      match env[i]? with
      | some (some l) => .ok s!"(local.get {l})"
      | some none     => .unsup s!"vvar {i} binds a unit `case`-payload (no i64 rep — rung-1.5)"
      | none          => .unsup s!"free vvar {i} (open term — rung-1 emits closed programs only)"
  | .vunit  => .unsup "vunit (no i64 rep in rung-1)"
  | .vcap _ _ => .unsup "vcap (effect capability — not pure ⊥-row)"
  | .vthunk _ => .unsup "vthunk (needs force/closure — stretch, not rung-1 arithmetic)"
  | .inl _ | .inr _ | .pair _ _ | .fold _ =>
      .unsup "ADT value (sum/product/μ — needs struct rep, rung-1.5)"

/-- Emit a pure `Comp` as an i64-leaving wasm expression. `env` maps de-Bruijn depth to wasm
local index; `next` is the next-free local index (for `letC`'s freshly-bound local). Returns
the expression text AND the total number of locals used (so the caller can declare them).

`letC M N`: compute M, `local.set` it into local `next`, then emit N under the extended env
(`some next :: env`) — the wasm-locals image of a de-Bruijn binder. Emitted as a `(block (result i64) …)`?
No — simpler and native: a wasm SEQUENCE `(local.set $k (…M…)) (…N…)`. We return the two-part text.

COMPARISON + case-on-bool (rung-1.5, the `if`-then-else pattern): the kernel expresses
`if a<b then E₂ else E₁` as `letC (binop cmp a b) (case (vvar 0) N₁ N₂)` — the comparison
reduces to `ret (boolVal c)` (`boolVal false = inl unit`, `boolVal true = inr unit`, IR.lean:173),
`letC` binds it to var 0, and `case (vvar 0)` eliminates: `inl → N₁` (left), `inr → N₂` (right,
`Eval.lean:96`). So a wasm `if` maps cleanly: the comparison leaves an i32 (`0`/`1`), and
`(if (result i64) <cmp> (then <N₂>) (else <N₁>))` — TRUE(1)=inr picks N₂(then),
FALSE(0)=inl picks N₁(else). The case binder (var 0) binds the `boolVal` unit payload, so both
branches emit under `none :: env` (bound-but-unusable, `emitVal` refuses a payload read). Any
comparison NOT in this immediate fused shape stays `unsup` (loud). -/
def emitComp (env : List (Option Nat)) (next : Nat) : Comp → Emit × Nat
  | .ret v => (emitVal env v, next)
  | .binop op a b =>
      match binOpWat op with
      | some w =>
          match emitVal env a, emitVal env b with
          | .ok ea, .ok eb => (.ok s!"({w} {ea} {eb})", next)
          | .unsup r, _ => (.unsup r, next)
          | _, .unsup r => (.unsup r, next)
      | none =>
          match op with
          | .div =>
              match emitVal env a, emitVal env b with
              | .ok ea, .ok eb => (.ok (emitDiv ea eb), next)
              | .unsup r, _ => (.unsup r, next)
              | _, .unsup r => (.unsup r, next)
          | _ =>
              -- a bare comparison (lt/eq) leaves a sum-encoded `boolVal` with no standalone i64
              -- rep — only meaningful when IMMEDIATELY eliminated by `case` (the fused letC arm).
              (.unsup s!"bare comparison binop (lt/eq) — only emittable when fused `letC cmp; case` (rung-1.5)", next)
  -- FUSED comparison + case-on-bool = wasm `if` (the `if`-then-else pattern; see the doc comment).
  | .letC (.binop cmpOp a b) (.case (.vvar 0) n1 n2) =>
      match cmpWat cmpOp with
      | none => (.unsup s!"letC binds a non-comparison then case (general sum-case is rung-2)", next)
      | some cw =>
          match emitVal env a, emitVal env b with
          | .unsup r, _ => (.unsup r, next)
          | _, .unsup r => (.unsup r, next)
          | .ok ea, .ok eb =>
              -- Inside each branch the de Bruijn context has TWO extra binders relative to the
              -- pre-`letC` scope: index 0 = the `case` unit payload, index 1 = the outer `letC`'s
              -- `boolVal` (the comparison result). Neither has an i64 wasm local (the comparison is
              -- consumed by the `if` condition; the payload is unit) — so the branch env is
              -- `none :: none :: env` (both unusable slots), and a branch reading either is `unsup`.
              let benv := none :: none :: env
              let (e1, m1) := emitComp benv next n1   -- inl branch (false)
              let (e2, m2) := emitComp benv next n2   -- inr branch (true)
              match e1, e2 with
              | .unsup r, _ => (.unsup r, next)
              | _, .unsup r => (.unsup r, next)
              | .ok e1S, .ok e2S =>
                  (.ok s!"(if (result i64) ({cw} {ea} {eb})\n      (then {e2S})\n      (else {e1S}))",
                   max m1 m2)
  | .letC m n =>
      -- compute m into local `next`; run n with (some next :: env), next local = next+1.
      let (em, _) := emitComp env next m
      match em with
      | .unsup r => (.unsup r, next)
      | .ok emS =>
          let (en, maxLocal) := emitComp (some next :: env) (next + 1) n
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

-- rung-1.5 arms: guarded div and the fused comparison + case-on-bool `if` emit `ok`.
/-- `10 / 2` — guarded division (`emitDiv`). -/
example : (emitModule (.binop .div (.vint 10) (.vint 2))).isOk = true := by
  simp [emitModule, emitComp, emitVal, binOpWat, emitDiv, Emit.isOk]
/-- `if 1<2 then 200 else 100` = `letC (lt 1 2) (case (vvar 0) 100 200)` — the fused `if`. -/
example :
    (emitModule (.letC (.binop .lt (.vint 1) (.vint 2))
      (.case (.vvar 0) (.ret (.vint 100)) (.ret (.vint 200))))).isOk = true := by
  simp [emitModule, emitComp, emitVal, cmpWat, Emit.isOk]

-- Refusals are LOUD, not silent: an effectful/ADT former yields `unsup`, never a wrong `ok`.
example : (emitModule (.perform (.vcap 0 0) "op" .vunit)).isOk = false := by
  simp [emitModule, emitComp, Emit.isOk]
example : (emitModule (.ret .vunit)).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- A BARE comparison (not immediately eliminated by `case`) is refused — no standalone bool i64 rep.
example : (emitModule (.binop .lt (.vint 1) (.vint 2))).isOk = false := by
  simp [emitModule, emitComp, emitVal, binOpWat, Emit.isOk]
-- A branch that READS the case unit-payload (index 0) or the boolVal (index 1) is refused (no i64 rep).
example :
    (emitModule (.letC (.binop .lt (.vint 1) (.vint 2))
      (.case (.vvar 0) (.ret (.vvar 0)) (.ret (.vint 0))))).isOk = false := by
  simp [emitModule, emitComp, emitVal, cmpWat, Emit.isOk]

end -- public section

end Bang.WasmEmit
