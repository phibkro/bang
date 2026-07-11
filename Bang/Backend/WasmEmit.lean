module

public import Bang.Backend.AbstractMachine

/-!
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

/-- What a de-Bruijn binder slot maps to (RUNG-2 generalization of the rung-1.5 `Option Nat`).
Both `letC` (value-binder) and `handle` (cap-binder, ADR-0054 — `handle h M` binds a capability
at index 0 in `M`, like `lam`) bind de-Bruijn index 0, so ONE unified environment must describe
what each slot is. Innermost binder = `env.head`.

  - `val l`   : the de-Bruijn var is a VALUE bound to wasm local `l` (a `letC` binder).
  - `cap t`   : the de-Bruijn var is a CAPABILITY naming the handle-frame whose wasm exception
                tag is `t` (a `handle (throws ℓ)` binder). A `perform (vvar i) "raise" v` with
                `env[i] = cap t` emits `throw $exn_t`. **This is the rung-2 handler-frame stack**:
                the de-Bruijn env IS the frame stack (a cap-slot per open `handle`), mirroring the
                kernel's `HStack`/`EvalCtx` — tag-minting rides the SAME recursion as the locals env.
  - `dead`    : bound-but-UNUSABLE (a `case`-on-bool unit payload — `boolVal` carries `vunit`, no
                i64 rep; reading it is out of fragment ⇒ `unsup`, not a wrong `local.get`).

Tag IDENTITY gives LEXICAL dispatch for free: each open `handle` mints a distinct tag, and
`try_table (catch $exn_t $h)` catches ONLY tag `t`, so a `throw $exn_t` unwinds to exactly the
lexically-enclosing handle that minted `t` — the wasm image of identity-keyed `idDispatch`. -/
inductive Slot where
  | val   : Nat → Slot     -- value-binder ⇒ wasm local
  | cap   : Nat → Slot     -- capability-binder (handle throws) ⇒ wasm exception tag
  -- RUNG-2b (state → in-place resume, ADR-0059's tail-call leg): the de-Bruijn var is the
  -- CAPABILITY naming a `handle (state ℓ s₀)` frame, whose single state cell is wasm LOCAL `l`.
  -- `perform (vvar i) "get" _` with `env[i] = state l` emits `(local.get l)` (read the cell,
  -- resume in place); `perform (vvar i) "put" v` emits `(local.set l ev)` (write, resume with
  -- unit). NO unwind, NO try_table — state RESUMES `Kᵢ` (`dispatchOn`'s state arm reinstalls the
  -- frame), unlike `throws`'s abort. The store is a mutable local threaded through the handled
  -- region; the handle's return delivers the body value (handler return = identity). ONE local per
  -- open `state` frame — the de-Bruijn env IS the store, exactly as `.cap` made it the handler stack.
  | state : Nat → Slot     -- state-cap-binder (handle state) ⇒ wasm local holding the store cell
  -- RUNG-3 (transaction → journal/snapshot over linear memory, ADR-0030). The de-Bruijn var is the
  -- CAPABILITY naming a `handle (transaction ℓ Θ)` frame — the MULTI-CELL generalization of `state`.
  -- The transaction heap is linear MEMORY (one i64 per cell at offset `8*idx`); `newTVar v` appends
  -- (bump `$heaplen` local, store `v`, return the old length as the TVar index), `readTVar (vint i)`
  -- loads cell `i`, `writeTVar (pair (vint i) w)` stores `w` at cell `i` (returns unit). Rollback is
  -- NOT free on wasm (mutation is destructive): the emitter SNAPSHOTS the heap at `handle` entry and
  -- RESTORES on the abort path (a `catch_all`-then-rethrow around the body — §rung-3). The Nat is the
  -- `$heaplen` LOCAL holding this transaction's live cell count (the index a `newTVar` allocates at).
  | txn   : Nat → Slot     -- transaction-cap-binder (handle transaction) ⇒ the `$heaplen` local
  | dead  : Slot           -- bound-but-unusable (case-on-bool payload / a `put`'s unit result)
  deriving Repr, DecidableEq, Inhabited

/-- Emit a `Val` as an i64-leaving wasm expression under the unified de-Bruijn `env`
(`env[i]?` = the binding of `vvar i`). Only VALUE slots yield an i64 expression; a `cap`/`dead`
slot has no i64 rep, so reading it is `unsup` (fail-loud — never a wrong `local.get`). -/
def emitVal (env : List Slot) : Val → Emit
  | .vint n => .ok s!"(i64.const {n})"
  | .vvar i =>
      match env[i]? with
      | some (.val l)   => .ok s!"(local.get {l})"
      | some (.cap _)   => .unsup s!"vvar {i} binds a CAPABILITY (no i64 rep — a cap is only usable as a `perform` target)"
      | some (.state _) => .unsup s!"vvar {i} binds a STATE capability (no i64 rep — usable only as a get/put `perform` target)"
      | some (.txn _)   => .unsup s!"vvar {i} binds a TRANSACTION capability (no i64 rep — usable only as a newTVar/readTVar/writeTVar `perform` target)"
      | some .dead      => .unsup s!"vvar {i} binds a unit `case`/`put`-payload (no i64 rep)"
      | none            => .unsup s!"free vvar {i} (open term — emits closed programs only)"
  | .vunit  => .unsup "vunit (no i64 rep in rung-1)"
  | .vcap _ _ => .unsup "vcap (runtime-minted capability — the static emitter routes caps by de-Bruijn binder, never a minted `vcap`)"
  | .vthunk _ => .unsup "vthunk (needs force/closure — stretch, not rung-1 arithmetic)"
  | .inl _ | .inr _ | .pair _ _ | .fold _ =>
      .unsup "ADT value (sum/product/μ — needs struct rep, rung-1.5)"

/-- Emit a `Comp` as an i64-leaving wasm expression under the unified de-Bruijn `env`.

Threaded state:
  - `next`    : next-free wasm LOCAL index (for `letC`'s bound value).
  - `nextTag` : next-free wasm exception-TAG index (for `handle (throws _)`'s minted tag).
Returned: `Emit × Nat × Nat` = `(text, maxLocal, maxTag)` — the caller declares that many
locals and tags at the module level.

`letC M N` (rung 1): compute M into local `next`, emit N under `.val next :: env`.

FUSED comparison + case-on-bool = wasm `if` (rung 1.5): `letC (binop cmp a b) (case (vvar 0) N₁ N₂)`.
The comparison reduces to `ret (boolVal c)` (`false = inl unit`, `true = inr unit`, IR.lean:173),
`letC` binds it at 0, `case (vvar 0)` eliminates: `inl → N₁` (else), `inr → N₂` (then). Both branch
bodies carry TWO extra binders (idx 0 = case unit payload, idx 1 = the boolVal) — both `.dead`.

`handle (throws ℓ) M` = wasm `try_table`/`throw` (RUNG 2 — abort → exceptions, ADR-0059). The
kernel (`Source.step`/`dispatchOn`, Eval.lean:83/Dispatch.lean:132) mints a fresh identity `g`,
substitutes `vcap g ℓ` for the body's index-0 cap-binder, and on a caught raise ABORTS: discards
the captured continuation `Kᵢ`, delivering the payload `w` to the outer stack (`ret w`); a body
that returns normally pops the handler frame (`ret v = ret v`). Both map to:

```wat
(block $h (result i64)
  (try_table (result i64) (catch $exn_t $h)
    <emit body under (.cap t :: env)>))   ;; raise → br $h WITH payload ; normal → body value out
```

The MINTED wasm tag `t = nextTag` is the static image of the runtime identity `g` — assigned by
descent (one tag per open `handle`), pushed onto the cap-frame stack as `.cap t`. A `perform
(vvar i) "raise" v` inside the body with `env[i] = .cap t` emits `throw $exn_t (emit v)`, which
wasm unwinds to exactly the `try_table` declaring `catch $exn_t` — the lexically-enclosing handle
that minted `t`, i.e. IDENTITY dispatch realized as tag identity. Nested handles get distinct tags,
so an inner raise to an OUTER handler (`vvar 1` skipping the inner cap-slot) throws the outer tag
and correctly unwinds past the inner `try_table`. Only `throws`/`"raise"` is in this fragment;
`state`/`transaction`/`custom` handlers, and any non-`raise` op, stay `unsup` (loud). -/
def emitComp (env : List Slot) (next : Nat) (nextTag : Nat) : Comp → Emit × Nat × Nat
  | .ret v => (emitVal env v, next, nextTag)
  | .binop op a b =>
      match binOpWat op with
      | some w =>
          match emitVal env a, emitVal env b with
          | .ok ea, .ok eb => (.ok s!"({w} {ea} {eb})", next, nextTag)
          | .unsup r, _ => (.unsup r, next, nextTag)
          | _, .unsup r => (.unsup r, next, nextTag)
      | none =>
          match op with
          | .div =>
              match emitVal env a, emitVal env b with
              | .ok ea, .ok eb => (.ok (emitDiv ea eb), next, nextTag)
              | .unsup r, _ => (.unsup r, next, nextTag)
              | _, .unsup r => (.unsup r, next, nextTag)
          | _ =>
              -- a bare comparison (lt/eq) leaves a sum-encoded `boolVal` with no standalone i64
              -- rep — only meaningful when IMMEDIATELY eliminated by `case` (the fused letC arm).
              (.unsup s!"bare comparison binop (lt/eq) — only emittable when fused `letC cmp; case` (rung-1.5)", next, nextTag)
  -- FUSED comparison + case-on-bool = wasm `if` (the `if`-then-else pattern; see the doc comment).
  | .letC (.binop cmpOp a b) (.case (.vvar 0) n1 n2) =>
      match cmpWat cmpOp with
      | none => (.unsup s!"letC binds a non-comparison then case (general sum-case is rung-2)", next, nextTag)
      | some cw =>
          match emitVal env a, emitVal env b with
          | .unsup r, _ => (.unsup r, next, nextTag)
          | _, .unsup r => (.unsup r, next, nextTag)
          | .ok ea, .ok eb =>
              -- Inside each branch the de Bruijn context has TWO extra binders relative to the
              -- pre-`letC` scope: index 0 = the `case` unit payload, index 1 = the outer `letC`'s
              -- `boolVal` (the comparison result). Neither has an i64 wasm local (the comparison is
              -- consumed by the `if` condition; the payload is unit) — so the branch env is
              -- `.dead :: .dead :: env` (both unusable slots), and a branch reading either is `unsup`.
              let benv := .dead :: .dead :: env
              let (e1, m1, t1) := emitComp benv next nextTag n1   -- inl branch (false)
              let (e2, m2, t2) := emitComp benv next nextTag n2   -- inr branch (true)
              match e1, e2 with
              | .unsup r, _ => (.unsup r, next, nextTag)
              | _, .unsup r => (.unsup r, next, nextTag)
              | .ok e1S, .ok e2S =>
                  (.ok s!"(if (result i64) ({cw} {ea} {eb})\n      (then {e2S})\n      (else {e1S}))",
                   max m1 m2, max t1 t2)
  -- RUNG 2: handle (throws ℓ) M  →  try_table/throw. Mint tag `nextTag`, push `.cap nextTag` for the
  -- body's index-0 cap-binder, wrap the body in `(block $h (try_table (catch $exn_t $h) <body>))`.
  | .handle (.throws _) M =>
      let t := nextTag
      let (eb, mLoc, mTag) := emitComp (.cap t :: env) next (nextTag + 1) M
      match eb with
      | .unsup r => (.unsup r, next, nextTag)
      | .ok bS =>
          (.ok s!"(block $h{t} (result i64)\n      (try_table (result i64) (catch $exn{t} $h{t})\n        {bS}))",
           mLoc, max mTag (t + 1))
  -- RUNG 2b: handle (state ℓ s₀) M  →  in-place resume (ADR-0059's tail-call leg). The kernel
  -- (`dispatchOn`'s `.state` arm, Dispatch.lean:133) RESUMES `Kᵢ` on both get (with `s`) and put
  -- (with `unit`, cell now `v`) — NO abort, NO unwind. So the store is one mutable wasm LOCAL `l`,
  -- initialized `(local.set l s₀)`, threaded through the handled region; `get`/`put` are straight-line
  -- reads/writes of `l`; the handle's value is the body value (handler return = identity, Eval.lean:65).
  -- Mint `l = next`, push `.state l` for M's index-0 cap-binder, prefix the init, deliver the body.
  | .handle (.state _ s₀) M =>
      let l := next
      match emitVal env s₀ with
      | .unsup r => (.unsup s!"state handler init value not i64-representable: {r}", next, nextTag)
      | .ok es₀ =>
          let (eb, mLoc, mTag) := emitComp (.state l :: env) (next + 1) nextTag M
          match eb with
          | .unsup r => (.unsup r, next, nextTag)
          | .ok bS =>
              -- (local.set l s₀) initializes the cell; then the body runs and leaves its i64 value.
              -- The cell local `l = next` counts toward maxLocal (`max mLoc (next+1)`).
              (.ok s!"(local.set {l} {es₀})\n    {bS}", max mLoc (next + 1), mTag)
  -- RUNG-3: handle (transaction ℓ Θ) M  →  journal/snapshot over linear MEMORY (ADR-0030).
  -- The transaction heap is linear memory (one i64 per cell, cell `i` at byte `8*i`). This slice
  -- takes the empty-heap start (`Θ = []`, the surface `atomically`), so `handle` resets the live
  -- length to 0. `$heaplen = next` counts cells; `$saved = next+1` snapshots it for rollback. The
  -- body runs under a `.txn next` slot; its i64 value flows out on the COMMIT (fall-through) path.
  -- ROLLBACK (the rung-3 novelty): wasm mutation is DESTRUCTIVE — the outer throws-unwind does NOT
  -- undo the `memory.store`s a `writeTVar` did (unlike the kernel, where the discarded frame takes
  -- `Θ'` with it). So the body is wrapped in `(try_table (catch_all_ref $ab) …)`: on ANY exception
  -- crossing this txn boundary, branch to `$ab`, RESTORE the heap length, then RETHROW (`throw_ref`)
  -- so the lexically-enclosing throws handler still catches. Empty-start restore is `$heaplen :=
  -- saved` (allocations dropped — cells that no longer exist are unreadable); a full snapshot COPY
  -- loop is the general form for pre-seeded heaps (§rung-3.2 of the design note).
  | .handle (.transaction _ Θ) M =>
      if Θ ≠ [] then
        (.unsup "transaction with a non-empty initial heap Θ (only `atomically`/empty-start is rung-3)", next, nextTag)
      else
        let hl := next          -- $heaplen local: live cell count (= next alloc index)
        let sv := next + 1      -- $saved local: snapshot of $heaplen for rollback
        let (eb, mLoc, mTag) := emitComp (.txn hl :: env) (next + 2) nextTag M
        match eb with
        | .unsup r => (.unsup s!"transaction body: {r}", next, nextTag)
        | .ok bS =>
            (.ok s!"(local.set {hl} (i64.const 0))\n    (local.set {sv} (local.get {hl}))\n    (block $txcommit{hl} (result i64)\n      (block $txab{hl} (result exnref)\n        (try_table (result i64) (catch_all_ref $txab{hl})\n          {bS})\n        (br $txcommit{hl}))\n      (local.set {hl} (local.get {sv}))\n      (throw_ref))",
             max mLoc (next + 2), mTag)
  -- RUNG-3 newTVar site (FUSED with its `letC` continuation): letC (perform (vvar i) "newTVar" v) N.
  -- `newTVar v` (dispatchOn: `ret (vint Θ.length)`, heap `Θ ++ [v]`) allocates: store `v` at the
  -- next free cell (`8 * $heaplen`), return the OLD length as the TVar index, bump `$heaplen`. The
  -- index is a VALUE (an i64), so it flows like an ordinary letC binder — N binds it at index 0 as a
  -- `.val` local. Emit: capture old len → local, store v, bump len, then N reads the index via it.
  | .letC (.perform (.vvar i) "newTVar" v) N =>
      match env[i]? with
      | some (.txn hl) =>
          match emitVal env v with
          | .unsup r => (.unsup s!"newTVar init value not i64-representable: {r}", next, nextTag)
          | .ok ev =>
              let idxLoc := next
              let (en, maxLocal, tn) := emitComp (.val idxLoc :: env) (next + 1) nextTag N
              match en with
              | .unsup r => (.unsup r, next, nextTag)
              | .ok enS =>
                  (.ok s!"(local.set {idxLoc} (local.get {hl}))\n    (i64.store (i32.wrap_i64 (i64.mul (local.get {idxLoc}) (i64.const 8))) {ev})\n    (local.set {hl} (i64.add (local.get {hl}) (i64.const 1)))\n    {enS}", maxLocal, tn)
      | some _ => (.unsup s!"newTVar target vvar {i} does not bind a transaction capability", next, nextTag)
      | none   => (.unsup s!"newTVar target vvar {i} is free (open term)", next, nextTag)
  -- RUNG-3 writeTVar site (FUSED with its `letC` continuation): letC (perform (vvar i) "writeTVar" (pair (vint j) w)) N.
  -- `writeTVar (pair (vint j) w)` (dispatchOn: storeSet Θ j w, `ret unit`) writes `w` to cell `j`,
  -- returns UNIT (no i64 rep) — a STATEMENT fused with its continuation, exactly like `put`. N binds
  -- the write-unit at index 0 (a `.dead` slot). The index `j` is a value expression (static `vint`).
  | .letC (.perform (.vvar i) "writeTVar" (.pair jv w)) N =>
      match env[i]? with
      | some (.txn _) =>
          match emitVal env jv, emitVal env w with
          | .ok ej, .ok ew =>
              let (en, maxLocal, tn) := emitComp (.dead :: env) next nextTag N
              match en with
              | .unsup r => (.unsup r, next, nextTag)
              | .ok enS =>
                  (.ok s!"(i64.store (i32.wrap_i64 (i64.mul {ej} (i64.const 8))) {ew})\n    {enS}", maxLocal, tn)
          | .unsup r, _ => (.unsup s!"writeTVar index not i64-representable: {r}", next, nextTag)
          | _, .unsup r => (.unsup s!"writeTVar value not i64-representable: {r}", next, nextTag)
      | some _ => (.unsup s!"writeTVar target vvar {i} does not bind a transaction capability", next, nextTag)
      | none   => (.unsup s!"writeTVar target vvar {i} is free (open term)", next, nextTag)
  -- RUNG 2b put site (FUSED with its `letC` continuation): letC (perform (vvar i) "put" v) N.
  -- `put` returns UNIT and resumes `Kᵢ` (`dispatchOn`: `ret .vunit`, cell now `v`) — unit has no i64
  -- rep, so put is a STATEMENT `(local.set l ev)`, then N runs. N binds the put-unit at index 0 (an
  -- unusable `.dead` slot, exactly the throws `letC`/case-payload pattern), so N reads env indices
  -- shifted by one (the cap that was `vvar i` is `vvar (i+1)` in N — verified against `Source.eval`).
  | .letC (.perform (.vvar i) "put" v) N =>
      match env[i]? with
      | some (.state l) =>
          match emitVal env v with
          | .unsup r => (.unsup s!"put payload not i64-representable: {r}", next, nextTag)
          | .ok ev =>
              let (en, maxLocal, tn) := emitComp (.dead :: env) next nextTag N
              match en with
              | .unsup r => (.unsup r, next, nextTag)
              | .ok enS =>
                  -- write the cell, then leave N's value — a wasm SEQUENCE (put resumes in place).
                  (.ok s!"(local.set {l} {ev})\n    {enS}", maxLocal, tn)
      | some (.cap _)  => (.unsup s!"put target vvar {i} binds a THROWS cap (put is a state op)", next, nextTag)
      | some (.txn _)  => (.unsup s!"put target vvar {i} binds a TRANSACTION cap (put is a state op — use writeTVar)", next, nextTag)
      | some (.val _)  => (.unsup s!"put target vvar {i} binds a VALUE, not a state capability", next, nextTag)
      | some .dead     => (.unsup s!"put target vvar {i} binds an unusable slot", next, nextTag)
      | none           => (.unsup s!"put target vvar {i} is free (open term)", next, nextTag)
  -- RUNG 2 raise site: perform (vvar i) "raise" v  →  throw $exn_t (emit v), where env[i] = .cap t.
  -- RUNG 2b get site: perform (vvar i) "get" _  →  (local.get l), where env[i] = .state l (read cell).
  -- Any non-`raise`/non-`get` op, a mismatched-kind target, or a non-i64 payload is out of fragment (loud).
  | .perform (.vvar i) op v =>
      if op = "raise" then
        match env[i]? with
        | some (.cap t) =>
            match emitVal env v with
            | .ok ev => (.ok s!"(throw $exn{t} {ev})", next, nextTag)
            | .unsup r => (.unsup s!"raise payload not i64-representable: {r}", next, nextTag)
        | some (.state _) => (.unsup s!"raise target vvar {i} binds a STATE cap (raise is a throws op)", next, nextTag)
        | some (.txn _)   => (.unsup s!"raise target vvar {i} binds a TRANSACTION cap (raise is a throws op)", next, nextTag)
        | some (.val _) => (.unsup s!"perform target vvar {i} binds a VALUE, not a capability", next, nextTag)
        | some .dead    => (.unsup s!"perform target vvar {i} binds an unusable slot", next, nextTag)
        | none          => (.unsup s!"perform target vvar {i} is free (open term)", next, nextTag)
      else if op = "get" then
        -- RUNG 2b: get reads the state cell (`dispatchOn`: `ret s`, resume in place). Payload ignored
        -- (the surface `get` carries `vunit`). env[i] must be a state cap ⇒ `(local.get l)`.
        match env[i]? with
        | some (.state l) => (.ok s!"(local.get {l})", next, nextTag)
        | some (.cap _)   => (.unsup s!"get target vvar {i} binds a THROWS cap (get is a state op)", next, nextTag)
        | some (.txn _)   => (.unsup s!"get target vvar {i} binds a TRANSACTION cap (get is a state op — use readTVar)", next, nextTag)
        | some (.val _)   => (.unsup s!"get target vvar {i} binds a VALUE, not a state capability", next, nextTag)
        | some .dead      => (.unsup s!"get target vvar {i} binds an unusable slot", next, nextTag)
        | none            => (.unsup s!"get target vvar {i} is free (open term)", next, nextTag)
      else if op = "readTVar" then
        -- RUNG 3: readTVar reads transaction heap cell `j` (`dispatchOn`: `ret Θ[j]`, resume in place).
        -- The payload `v` is the TVar index (a `vint j`), an i64 expression ⇒ `(i64.load (8*j))`.
        -- readTVar returns a VALUE (unlike write/new/put's unit), so it flows here as an i64-leaver.
        match env[i]? with
        | some (.txn _) =>
            match emitVal env v with
            | .ok ej   => (.ok s!"(i64.load (i32.wrap_i64 (i64.mul {ej} (i64.const 8))))", next, nextTag)
            | .unsup r => (.unsup s!"readTVar index not i64-representable: {r}", next, nextTag)
        | some _ => (.unsup s!"readTVar target vvar {i} does not bind a transaction capability", next, nextTag)
        | none   => (.unsup s!"readTVar target vvar {i} is free (open term)", next, nextTag)
      else
        -- `put`/`writeTVar`/`newTVar` are handled ONLY in the fused `letC (op) N` arms above (they
        -- return unit / a bound index — no i64 rep as a bare tail expression). Reaching here = bare.
        (.unsup s!"perform op {op} (rung-2/3: `raise`=throws, `get`/`readTVar`=read; `put`/`writeTVar`/`newTVar` need the fused `letC op; N`)", next, nextTag)
  | .letC m n =>
      -- compute m into local `next`; run n with (.val next :: env), next local = next+1.
      let (em, _, tm) := emitComp env next nextTag m
      match em with
      | .unsup r => (.unsup r, next, nextTag)
      | .ok emS =>
          let (en, maxLocal, tn) := emitComp (.val next :: env) (next + 1) tm n
          match en with
          | .unsup r => (.unsup r, next, nextTag)
          | .ok enS =>
              -- (local.set $next em) then leave the value of n — a wasm SEQUENCE (no `block`/`br`).
              (.ok s!"(local.set {next} {emS})\n    {enS}", maxLocal, tn)
  | .force _ => (.unsup "force (needs thunk/closure — stretch)", next, nextTag)
  | .lam _ => (.unsup "lam (function value — stretch, non-recursive call)", next, nextTag)
  | .app _ _ => (.unsup "app (call — stretch)", next, nextTag)
  | .perform _ _ _ => (.unsup "perform on a non-vvar target (runtime cap / malformed — out of the static throws fragment)", next, nextTag)
  | .handle _ _ => (.unsup "handle: `throws` (abort → exceptions) and `state` (in-place resume) are the rung-2/2b fragment; transaction/custom are rung-3", next, nextTag)
  | .case _ _ _ => (.unsup "case (sum elim — rung-1.5)", next, nextTag)
  | .split _ _ => (.unsup "split (product elim — rung-1.5)", next, nextTag)
  | .unfold _ => (.unsup "unfold (μ elim — rung-1.5)", next, nextTag)
  | .oom => (.unsup "oom", next, nextTag)
  | .wrong s => (.unsup s!"wrong: {s}", next, nextTag)

/-- Does this `Comp` contain a `handle (transaction …)` anywhere? Drives the `(memory 1)`
declaration in `emitModule` (rung-3 uses linear memory for the TVar heap). A pure/throws/state
program mints ZERO memory, so its module stays byte-identical to the earlier rungs (additive). -/
def usesTxn : Comp → Bool
  | .handle (.transaction _ _) _ => true
  | .handle _ M => usesTxn M
  | .letC m n => usesTxn m || usesTxn n
  | .case _ n1 n2 => usesTxn n1 || usesTxn n2
  | .split _ n => usesTxn n
  | _ => false

/-- Whole-module emission: wrap the fragment body in a wasm module exporting `main : () → i64`,
declaring the `numLocals` i64 locals the `letC`s used and the `numTags` exception tags the
`handle (throws _)`s minted. Returns the full `.wat` text or a refusal.

RUNG 1 (no `handle`): CORE wasm 3.0 — no GC, no exceptions, no imports — runs on ANY engine.
RUNG 2 (with `handle throws`): declares `(tag $exnT (param i64))` per minted tag and uses the
`try_table`/`throw` exception-handling proposal (Wasm 3.0 core; wasmtime needs `-W exceptions=y`,
see `tools/emit-rung1-diff.sh`). A pure/rung-1.5 program emits ZERO tags, so its module is
byte-identical to the rung-1 form (the tag block is empty) — the extension is purely additive.
RUNG 3 (with `handle transaction`): additionally declares `(memory 1)` for the TVar heap (one i64
per cell). The rollback path uses `catch_all_ref`/`throw_ref` (also under `-W exceptions=y`). -/
def emitModule (M : Comp) : Emit :=
  let (body, numLocals, numTags) := emitComp [] 0 0 M
  match body with
  | .unsup r => .unsup r
  | .ok b =>
      let localDecls :=
        (List.range numLocals).foldl (fun acc _ => acc ++ " (local i64)") ""
      -- One `(tag $exnT (param i64))` per minted throws-handler tag (each abort carries an i64 payload).
      let tagDecls :=
        (List.range numTags).foldl (fun acc t => acc ++ s!"\n  (tag $exn{t} (param i64))") ""
      -- One page of linear memory for the TVar heap, only when a transaction is present (additive).
      let memDecl := if usesTxn M then "\n  (memory 1)" else ""
      .ok s!"(module{tagDecls}{memDecl}\n  (func $main (export \"main\") (result i64){localDecls}\n    {b})\n)"

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

-- ── RUNG-2 arms (throws → try_table/throw) — structural regression guards ─────────────────
-- caught raise: handle (throws 0) (perform (vvar 0) "raise" 7)  ⇒ emits (7 delivered on catch).
example :
    (emitModule (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 7)))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- raise discards continuation: handle (throws 0) (letC (raise 7) (ret 99)) ⇒ emits.
example :
    (emitModule (.handle (.throws 0)
      (.letC (.perform (.vvar 0) "raise" (.vint 7)) (.ret (.vint 99))))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- normal return: handle (throws 0) (binop add 3 4) ⇒ body value flows out of try_table.
example :
    (emitModule (.handle (.throws 0) (.binop .add (.vint 3) (.vint 4)))).isOk = true := by
  simp [emitModule, emitComp, emitVal, binOpWat, Emit.isOk]
-- nested handles (distinct tags): inner catches its own raise.
example :
    (emitModule (.handle (.throws 0)
      (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 5))))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]

-- RUNG-2 refusals are LOUD: a KIND-mismatched op, a value-target perform, and an unsupported handler.
-- perform "get" on a THROWS cap (get is a state op — kind mismatch) → unsup (no wrong throw/read).
example :
    (emitModule (.handle (.throws 0) (.perform (.vvar 0) "get" .vunit))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- perform whose target binds a VALUE (letC-bound), not a cap → unsup (no wrong throw).
example :
    (emitModule (.handle (.throws 0)
      (.letC (.ret (.vint 5)) (.perform (.vvar 0) "raise" (.vint 1))))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]

-- ── RUNG-2b arms (state → in-place resume / tail-call) — structural regression guards ──────
-- get-only: handle (state 0 5) { get }  ⇒ emits (local.set l 5) then (local.get l).
example :
    (emitModule (.handle (.state 0 (.vint 5)) (.perform (.vvar 0) "get" .vunit))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- put-then-get: handle (state 0 0) { let _ = put 7 in get } — cap shifts to idx1 in the put's cont.
example :
    (emitModule (.handle (.state 0 (.vint 0))
      (.letC (.perform (.vvar 0) "put" (.vint 7)) (.perform (.vvar 1) "get" .vunit)))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- arithmetic around get: handle (state 0 10) { let x = get in x + 5 } — get flows the ordinary letC arm.
example :
    (emitModule (.handle (.state 0 (.vint 10))
      (.letC (.perform (.vvar 0) "get" .vunit) (.binop .add (.vvar 0) (.vint 5))))).isOk = true := by
  simp [emitModule, emitComp, emitVal, binOpWat, Emit.isOk]
-- normal return: handle (state 0 3) { 42 } — body value flows out (handler return = identity).
example :
    (emitModule (.handle (.state 0 (.vint 3)) (.ret (.vint 42)))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]

-- RUNG-2b refusals are LOUD: kind-mismatched raise on a state cap, a value-target get, a bare put.
-- raise on a STATE cap (raise is a throws op — kind mismatch) → unsup.
example :
    (emitModule (.handle (.state 0 (.vint 0)) (.perform (.vvar 0) "raise" (.vint 1)))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- get whose target binds a VALUE (letC-bound), not a state cap → unsup.
example :
    (emitModule (.handle (.state 0 (.vint 0))
      (.letC (.ret (.vint 5)) (.perform (.vvar 0) "get" .vunit)))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- a BARE put (unit tail, not fused with a `letC` continuation) → unsup (unit has no i64 tail rep).
example :
    (emitModule (.handle (.state 0 (.vint 0)) (.perform (.vvar 0) "put" (.vint 1)))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- ── RUNG-3 arms (transaction → journal/snapshot over linear memory) — structural guards ────
-- empty-start transaction, trivial body: emits (memory declared, heaplen reset).
example :
    (emitModule (.handle (.transaction 0 []) (.ret (.vint 1)))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- new;read: handle (txn) (let r = newTVar 9 in readTVar r) — alloc, read-back.
example :
    (emitModule (.handle (.transaction 2 [])
      (.letC (.perform (.vvar 0) "newTVar" (.vint 9)) (.perform (.vvar 1) "readTVar" (.vvar 0))))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- A11 abort/rollback: outer throws over a txn that writes then raises → emits (catch_all_ref restore).
example :
    (emitModule (.handle (.throws 0)
      (.handle (.transaction 2 [])
        (.letC (.perform (.vvar 0) "newTVar" (.vint 100))
          (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 70)))
            (.perform (.vvar 3) "raise" (.vint 100))))))).isOk = true := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- RUNG-3 refusals are LOUD: a non-empty initial heap is out of the empty-start fragment.
example :
    (emitModule (.handle (.transaction 0 [.vint 5]) (.ret (.vint 1)))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]
-- a `get` on a TRANSACTION cap (kind mismatch — txn uses readTVar) → unsup.
example :
    (emitModule (.handle (.transaction 0 []) (.perform (.vvar 0) "get" .vunit))).isOk = false := by
  simp [emitModule, emitComp, emitVal, Emit.isOk]

end -- public section

end Bang.WasmEmit
