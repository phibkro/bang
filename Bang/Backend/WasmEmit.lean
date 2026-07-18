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

/-- Guarded, EUCLIDEAN division — the kernel's `div` is TOTAL and EUCLIDEAN: `a / 0 = 0` and
`a / b = Int.ediv a b` (`BinOp.eval div`, IR.lean:188 — Lean core `Int./` is `Int.ediv`, whose
remainder is always `≥ 0`). This is NOT truncated-toward-zero: `(-7)/2 = -4`, `7/(-2) = -3`,
`(-7)/(-2) = 4` (pinned in `scratch/BignumOracleProbe.lean`). wasm's `i64.div_s` is TRUNCATED, so
a bare `div_s` diverges from `Source.eval` for EVERY negative-operand division — and the reference
wins (invariant #1). This was a latent compiled≠oracle gap (issue #132): the corpus never divided
with a negative operand, so it never fired.

The emitted sequence (witnessed on wasmtime 45, `scratch/euclid-div.wat`; the t→e fixup formula is
verified against the oracle across all sign quadrants in `scratch/EuclidDivProbe.lean`):

  (if (result i64) (i64.eqz <eb>)                              ;; b = 0  ⇒  0  (kernel a/0 = 0)
    (then (i64.const 0))
    (else                                                       ;; qt = a div_s b ; rt = a rem_s b
      (if (result i64) (i64.lt_s (i64.rem_s <ea> <eb>) 0)       ;; truncated remainder < 0 ?
        (then (if (result i64) (i64.gt_s <eb> 0)                ;; euclidean fixup: qt - sign(b)
          (then (i64.sub (i64.div_s <ea> <eb>) 1))
          (else (i64.add (i64.div_s <ea> <eb>) 1))))
        (else (i64.div_s <ea> <eb>)))))

The operands `ea`/`eb` are pure `Val` expressions (`i64.const`/`local.get` — no side effects, no
traps, `emitVal`), so duplicating them across the eqz/rem_s/div_s tests is safe (no scratch local).

Known residual gap (NOT this slice, the bignum lane): `i64.div_s` also traps on `INT64_MIN / -1`
(signed overflow) and any operand outside [−2⁶³, 2⁶³); the unbounded-`Int`→i64 edge closes when the
`$bigval` limb rep lands (`docs/notes/emission-bignum-design.md`). -/
def emitDiv (ea eb : String) : String :=
  s!"(if (result i64) (i64.eqz {eb})\n      (then (i64.const 0))\n      (else (if (result i64) (i64.lt_s (i64.rem_s {ea} {eb}) (i64.const 0))\n        (then (if (result i64) (i64.gt_s {eb} (i64.const 0))\n          (then (i64.sub (i64.div_s {ea} {eb}) (i64.const 1)))\n          (else (i64.add (i64.div_s {ea} {eb}) (i64.const 1)))))\n        (else (i64.div_s {ea} {eb})))))"

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

-- ═══════════════════════════════════════════════════════════════════════════════════════
-- RUNG 4 — closures + ADTs + recursion on WasmGC (the "nqueens compiles" rung)
-- ═══════════════════════════════════════════════════════════════════════════════════════
/-!
  The rung-1/2/3 emitter above is a STATIC inline structural recursion: every former is flattened
  into `$main`'s body with a compile-time de-Bruijn env of `Slot`s. That model CANNOT express
  recursion — the μ-knot (`let rec`, ADR-0073: `Rec = μX. Thunk(X → T)`, Landin's knot) applies
  itself under `force`/`unfold` an unbounded number of RUNTIME times; an inline emitter that
  unfolded it would not terminate at compile time (the wall the rung-1 note §4 named: "SUBST/APP
  carry residual Comps exec re-compiles at runtime — a static emitter can't consume them without
  BEING the interpreter").

  Rung 4 is the DERIVED answer (invariant #4 — the machine is an output of the calculation): the
  kernel reduces closures/ADTs by SUBSTITUTION into RESIDUAL Comps (`evalD`: `app (lam N) v ↦ N[v]`,
  `case (inl v) N₁ N₂ ↦ N₁[v]`, `force (vthunk M) ↦ M`, `unfold (fold v) ↦ ret v`,
  AbstractMachine.lean:263-357). The faithful WASM image of "reduce a residual Comp at runtime" is a
  REAL CALL: each `lam`/`vthunk` lambda-lifts to a top-level wasm function; `app`/`force` become
  `call_ref` through a closure GC-struct; recursion runs on the WASM CALL STACK, exactly as `exec`
  re-`compile`s under fuel (ADR-0059's `general → WasmGC-frame-chain runtime` slot).

  VALUE REP (`$val` = a uniform GC reference so lambdas are polymorphic — `List a` is generic):
    - `vint n`        → `(struct $ival (field i64))` — BOXED i64. Bang `Int` is unbounded ℤ; this
                        rung is i64-RANGE with a documented LOUD deviation (like guarded-div). Full
                        bignum is a NAMED rung-5 refusal (GC-array limb rep), NOT emitted here.
    - `inl v`/`inr v` → `(struct $sum (field $tag i32) (field $payload (ref null $val)))`, tag 0/1.
    - `pair a b`      → `(struct $pair (field (ref null $val)) (field (ref null $val)))`.
    - `fold v`        → ERASES (IR.lean:106): `fold v` = `v`'s bits, `unfold` = identity.
    - `vthunk M`/`lam M` → `(struct $clos (field $code (ref $fn)) (field $env (ref null $env)))`.

  ENVIRONMENT (`$env` = a cons-list of values, innermost binder first):
    `(struct $env (field $hd (ref null $val)) (field $tl (ref null $env)))`. Every binder PREPENDS
    its value into a FRESH env local (never a mutated shared local — branch bodies each set their
    own env local, so alternatives never leak binders); `vvar i` = `$lookup env i`. A lifted
    function receives its captured env as param 0 and prepends its argument; `$main` starts null.

  RECURSION FALLS OUT (no invented former): the μ-knot `letC (unfold (vvar 0)) (app (force (vvar 0))
    (fold (vvar 0)))` — `unfold`/`fold` erase, `force`/`app` are `call_ref`s. Emitting the four
    formers faithfully IS emitting recursion.

  LOCALS: one monotone counter per function; each fresh local records its wasm TYPE (`env`-ref or
  `val`-ref) in `localTys` so `emitModuleGC`/`renderFn` declare them in index order with the right
  type — no offset arithmetic, no index collisions. Indices 0,1 are the fixed params inside a lifted
  fn (env0, arg); `$main` has no params, so its locals start at 0.

  SEPARATE emitter (`emitModuleGC`), NOT a rewrite of the inline one (ADR-0059 grade-directed: the
  pure/effect fragment stays on rungs 1-3). Fail-loud preserved: `perform`/`handle` on the GC path
  are NAMED rung-5 refusals (effects lower on the inline path, rungs 2/3).
-/

/-- A rung-4 emission result: wasm text leaving one `(ref null $val)`, or a named refusal. -/
inductive EmitGC where
  | ok    : String → EmitGC
  | unsup : String → EmitGC
  deriving Repr, DecidableEq, Inhabited

def EmitGC.isOk : EmitGC → Bool
  | .ok _ => true
  | .unsup _ => false

/-- A lambda-lifted top-level function: its index, body text, and the per-index local TYPES it
declares (index 0 upward, EXCLUDING the two params — `localTys[k]` is the type of local `paramCount+k`). -/
structure LiftedFn where
  idx      : Nat
  body     : String
  localTys : List String
  deriving Repr, Inhabited

/-- State threaded through GC emission. `next` = the next fresh local index in the CURRENT function
(2 inside a lifted fn, past env0+arg; 0 in `$main`). `localTys` records the type of each local from
`base` upward, in claim order (reversed for O(1) prepend; reversed back at render). `base` = the
first non-param local index in the current function. -/
structure GCState where
  fns      : List LiftedFn := []
  nextFn   : Nat := 0
  base     : Nat := 0                 -- first non-param local index (0 in main, 2 in a lifted fn)
  next     : Nat := 0                 -- next fresh local index
  localTys : List String := []        -- types of locals [base..next), reversed
  nextTag  : Nat := 0                 -- RUNG 5 S2: next-free wasm exception TAG (per minted `handle throws`)
  tagCount : Nat := 0                 -- RUNG 5 S2: peak tag count minted (drives `(tag $exnT …)` decls)
  nextOpId : Nat := 0                 -- next module-local exact custom-operation identity
  opIds    : List (String × Nat) := [] -- interned op name → identity (collision-free within a module)
  deriving Inhabited

/-- Claim a fresh local of wasm type `ty`, returning its index and the updated state. -/
def GCState.fresh (st : GCState) (ty : String) : Nat × GCState :=
  (st.next, { st with next := st.next + 1, localTys := ty :: st.localTys })

/-- RUNG 5 S2: claim a fresh wasm exception-tag index (for a `handle (throws …)`). Tags accumulate
across the WHOLE module (each minted once), so `nextTag` bumps monotonically and `tagCount` records
the peak for the module-level `(tag $exnT (param (ref null $val)))` declarations. -/
def GCState.freshTag (st : GCState) : Nat × GCState :=
  (st.nextTag, { st with nextTag := st.nextTag + 1, tagCount := max st.tagCount (st.nextTag + 1) })

/-- Intern a custom operation name into a module-local exact identity. Both clause construction and
first-class perform emission use this table, so equal source names receive the same id and distinct
names cannot collide. The ids are an internal dispatch representation, never a source-level ABI. -/
def GCState.internOp (st : GCState) (op : String) : Nat × GCState :=
  match st.opIds.find? (fun entry => entry.1 == op) with
  | some (_, id) => (id, st)
  | none =>
      let id := st.nextOpId
      (id, { st with nextOpId := id + 1, opIds := (op, id) :: st.opIds })

#guard
  let st0 : GCState := {}
  let (inspectId, st1) := st0.internOp "inspect"
  let (advanceId, st2) := st1.internOp "advance"
  let (inspectAgain, _) := st2.internOp "inspect"
  inspectId == inspectAgain && inspectId != advanceId

/-- RUNG 5: a compile-time CAPABILITY slot in the de-Bruijn context threaded ALONGSIDE the runtime
`$env` cons-list (mirroring the inline emitter's `List Slot`). The `$env` carries VALUES at runtime;
`caps` carries the STATIC dispatch metadata a `perform` needs but a `$val` slot can't hold:
  - `none`        : an ordinary value binder (letC result, lam arg, case/split payload, state box).
  - `throwsTag t` : a `handle (throws)` cap-binder — a `raise` on it emits `throw $exn{t}` (tag
                    identity = lexical dispatch, exactly the inline `.cap t` Slot).
  - `custom`: a `handle (custom p cls)` cap-binder (RUNG 5 S4). The cap's runtime `$txbox`
              owns the clause closures and their shared mutable parameter environment.
Pushed identically to the `$env` at every binder so index `i` agrees between the two. -/
inductive CapSlot where
  | none      : CapSlot
  | throwsTag : Nat → CapSlot
  -- RUNG 5 S4: a `handle (custom p cls)` cap-binder. `clauses` maps each op NAME to its POSITION in the
  -- cap's clause-record list (a $env of `$clause` values built at the handle site, each carrying an
  -- exact operation id, update mode, and lam-style `$clos` capturing
  -- a shared mutable `p :: handlerEnv`, held in a $txbox stored in the cap's ENV slot — so a nested closure that
  -- performs the op reaches it via $lookup, NOT a compile-time local). A matching `perform op v`
  -- `call_ref`s the clause at that position with arg `v` ⇒ body env `(v :: p :: handlerEnv)` — the
  -- image of `subst p (subst (shift v) clause.2)`. Updating keys consume the returned pair and replace
  -- that shared environment's head before resuming. An unhandled op raises (kernel: no matching clause ⇒
  -- `.raised`), refused loudly here (v1 has no runtime raise-forward on the GC path).
  | custom    : List (Bang.ClauseKey × Nat) → CapSlot
  deriving Inhabited

/-- Wrap a statement-prefixed sequence (`local.set …`s followed by a value expression) in a
`(block (result (ref null $val)) …)` so it is a SINGLE value-producing expression, valid in
operand position. Every emitter arm that emits `local.set` statements before its value returns this
form — so nesting (an `app` whose callee is itself an `app`) composes without a void `local.set` in
value position (the wasm folded-form rule: a subexpression must produce exactly one value). -/
def seqBlock (body : String) : String :=
  s!"(block (result (ref null $val))\n    {body})"

/-- Arithmetic `BinOp` → the i64 wasm op used on the GC path. NONE remain — `add`/`sub`/`mul` all
route through `binopValHelper` (the bignum-safe runtime helpers), `div` is the B0 Euclidean path,
comparisons are `cmpValCond`. Kept as a (now-empty) hook for any future i64-only op. -/
def binopGCWat : BinOp → Option String
  | .add | .sub | .mul | .div | .lt | .eq => none

/-- `add`/`sub`/`mul` → the bignum-safe runtime helper (`$addVal`/`$subVal`/`$mulVal`) that operates
on BOXED `$val` operands (mixed `$ival`/`$bigval`) and returns an unbounded result (issue #132 /
bignum lane B2 add·sub, B3 mul). Comparisons and `div` are handled elsewhere. -/
def binopValHelper : BinOp → Option String
  | .add => some "$addVal"
  | .sub => some "$subVal"
  | .mul => some "$mulVal"
  | .div | .lt | .eq => none

/-- Comparison `BinOp` → the i64 wasm compare (i32 result), for the fused `if`. -/
def cmpGCWat : BinOp → Option String
  | .lt => some "i64.lt_s" | .eq => some "i64.eq" | _ => none

/-- BIGNUM-safe comparison condition (issue #132 / bignum lane B2): given two BOXED `$val` operand
expressions, produce the i32 boolean wasm condition via `$cmpVal` (which returns −1/0/1 on the mixed
`$ival`/`$bigval` rep). `lt` = `cmpVal < 0`, `eq` = `cmpVal == 0`. Operands are NOT unboxed (a
`$bigval` operand must not truncate to i64). -/
def cmpValCond : BinOp → Option (String → String → String)
  | .lt => some (fun ea eb => s!"(i32.lt_s (call $cmpVal {ea} {eb}) (i32.const 0))")
  | .eq => some (fun ea eb => s!"(i32.eqz (call $cmpVal {ea} {eb}))")
  | _ => none

def unboxI (e : String) : String := s!"(struct.get $ival 0 (ref.cast (ref $ival) {e}))"
def boxI (e : String) : String := s!"(struct.new $ival {e})"
/-- GC-path Euclidean guarded division — same semantics as `emitDiv` (kernel `div = Int.ediv`,
`a/0 = 0`): the truncated `div_s` fixed up to Euclidean when the truncated remainder is negative
(issue #132; witnessed `scratch/euclid-div.wat`, formula verified `scratch/EuclidDivProbe.lean`).
`ea`/`eb` here are UNBOXED i64 expressions (`unboxI` = a pure `struct.get $ival` — no side effect),
so duplicating them across the eqz/rem_s/div_s tests is safe. -/
def emitDivGCI (ea eb : String) : String :=
  s!"(if (result i64) (i64.eqz {eb}) (then (i64.const 0)) (else (if (result i64) (i64.lt_s (i64.rem_s {ea} {eb}) (i64.const 0)) (then (if (result i64) (i64.gt_s {eb} (i64.const 0)) (then (i64.sub (i64.div_s {ea} {eb}) (i64.const 1))) (else (i64.add (i64.div_s {ea} {eb}) (i64.const 1))))) (else (i64.div_s {ea} {eb})))))"
def lookupGC (envL i : Nat) : String := s!"(call $lookup (local.get {envL}) (i32.const {i}))"

/-- The base-10⁹ limb decomposition of a NON-NEGATIVE `Nat`, LEAST-significant limb first, with NO
leading (most-significant) zero limbs — the canonical `$bigval` magnitude. `0` yields `[0]` (a single
zero limb) so the array is never empty. Base 10⁹ = the readback-friendly base (each limb = 9 decimal
digits; `$emitBig` renders top-bare then `%09d`). Compile-time only (the literal `n : Int` is known);
runtime limb arithmetic (bignum lane B2/B3) lives in wasm. -/
partial def bigLimbs (m : Nat) : List Nat :=
  if m < 1000000000 then [m]
  else (m % 1000000000) :: bigLimbs (m / 1000000000)

/-- Whether an `Int` literal fits in a signed i64 (`$ival`) or needs the `$bigval` limb rep. The
boundary is exactly the kernel-vs-i64 gap: `[−2⁶³, 2⁶³)` is `$ival`; anything outside is `$bigval`. -/
def fitsI64 (n : Int) : Bool := (-9223372036854775808 : Int) ≤ n ∧ n < (9223372036854775808 : Int)

/-- Emit an out-of-i64-range `Int` LITERAL as a `$bigval` (issue #132 / bignum lane B1). Sign +
base-10⁹ limb array built with `array.new_fixed` (limbs LSB-first, matching `$emitBig`'s walk).
In-range literals never reach here (they stay `$ival`, `boxI`). Witnessed:
`scratch/bigval-literal-readback.wat`. -/
def emitBigLit (n : Int) : String :=
  let sign : Nat := if n < 0 then 1 else 0
  let mag  : Nat := n.natAbs
  let limbs := bigLimbs mag
  let limbStr := String.intercalate " " (limbs.map (fun l => s!"(i64.const {l})"))
  s!"(struct.new $bigval (i32.const {sign}) (array.new_fixed $limbs {limbs.length} {limbStr}))"

/-- Box an `Int` literal as a `$val`: `$ival` when it fits i64, else `$bigval` (bignum lane B1). -/
def boxInt (n : Int) : String :=
  if fitsI64 n then s!"(struct.new $ival (i64.const {n}))" else emitBigLit n

/-- wasm type strings for the two local roles. -/
def tyEnv : String := "(ref null $env)"
def tyVal : String := "(ref null $val)"

/-! A manifestly unused `letC` result needs no runtime `$env` cell. The occurrence test follows
`Comp.substFrom`'s binder structure exactly: handler parameters/heaps/clauses that substitution
treats as closed are ignored here too. This is intentionally a syntactic backend optimization;
the surface `use [0] x in ...` assertion is checked earlier and erased before lowering. -/
mutual
def usesBinderV (k : Nat) : Val → Bool
  | .vunit | .vint _ | .vcap _ _ => false
  | .vvar i => i == k
  | .vthunk m => usesBinderC k m
  | .inl v | .inr v | .fold v => usesBinderV k v
  | .pair a b => usesBinderV k a || usesBinderV k b
def usesBinderC (k : Nat) : Comp → Bool
  | .ret v | .force v | .unfold v => usesBinderV k v
  | .letC m n => usesBinderC k m || usesBinderC (k + 1) n
  | .lam m => usesBinderC (k + 1) m
  | .app m v => usesBinderC k m || usesBinderV k v
  | .perform cap _ arg => usesBinderV k cap || usesBinderV k arg
  | .handle h m => usesBinderH k h || usesBinderC (k + 1) m
  | .case v l r => usesBinderV k v || usesBinderC (k + 1) l || usesBinderC (k + 1) r
  | .split v n => usesBinderV k v || usesBinderC (k + 2) n
  | .binop _ a b => usesBinderV k a || usesBinderV k b
  | .oom | .wrong _ => false
def usesBinderH (k : Nat) : Handler → Bool
  | .state _ s => usesBinderV k s
  | .throws _ | .transaction _ _ | .custom _ _ _ => false
end

mutual
/-- Emit a `Val` as a `(ref null $val)` expression under env-local `envL`. `caps` is the compile-time
capability context (§`CapSlot`), threaded ALONGSIDE the runtime `$env` so a nested closure body knows
which de-Bruijn slots are handler caps. Threads `GCState`. -/
partial def emitValGC (envL : Nat) (caps : List CapSlot) (v : Val) (st : GCState) : EmitGC × GCState :=
  match v with
  | .vint n => (.ok (boxInt n), st)   -- $ival if it fits i64, else $bigval limbs (bignum lane B1)
  | .vvar i => (.ok (lookupGC envL i), st)
  | .vunit  => (.ok (boxI "(i64.const 0)"), st)
  | .inl w =>
      match emitValGC envL caps w st with
      | (.ok ew, st') => (.ok s!"(struct.new $sum (i32.const 0) {ew})", st')
      | (.unsup r, st') => (.unsup r, st')
  | .inr w =>
      match emitValGC envL caps w st with
      | (.ok ew, st') => (.ok s!"(struct.new $sum (i32.const 1) {ew})", st')
      | (.unsup r, st') => (.unsup r, st')
  | .pair a b =>
      match emitValGC envL caps a st with
      | (.unsup r, st') => (.unsup r, st')
      | (.ok ea, st1) =>
        match emitValGC envL caps b st1 with
        | (.unsup r, st') => (.unsup r, st')
        | (.ok eb, st2) => (.ok s!"(struct.new $pair {ea} {eb})", st2)
  | .fold w => emitValGC envL caps w st
  | .vthunk M => emitCloVal true envL caps M st       -- THUNK: no arg binder (force = run M as-is).
  | .vcap _ _ => (.unsup "vcap (runtime capability — no rung-4 GC value rep)", st)

/-- Lambda-lift `M` to a fresh top-level fn; emit the closure value capturing the CURRENT env.

`isThunk` distinguishes the two closure kinds — the kernel treats them differently (invariant #4,
AbstractMachine.lean:269 vs 263/270):
  - `lam M`:  `app (lam M) v ↦ M[v]` — M's index 0 IS the argument. The lifted fn PREPENDS its arg
              param to the captured env (body env = arg :: capturedEnv), so `vvar 0` = the arg.
  - `vthunk M`: `force (vthunk M) ↦ M` — a thunk introduces NO binder; M's `vvar 0` is the FIRST
              CAPTURED var. The lifted fn runs the body under the captured env DIRECTLY (the fn's arg
              param is a `force`-supplied dummy, ignored). Getting this wrong shifts every index by
              one inside every thunk — the μ-knot's `unfold`/`force`/`app` then cast a non-closure. -/
partial def emitCloVal (isThunk : Bool) (envL : Nat) (caps : List CapSlot) (M : Comp) (st : GCState) : EmitGC × GCState :=
  let fnIdx := st.nextFn
  -- lam: local 2 = arg :: env0, body under env-local 2. thunk: body under env-local 0 (the captured
  -- env param directly), no arg prepend. Fresh locals start at 3 (lam) or 1 (thunk).
  -- thunk: body env = the captured env param (local 0); fresh locals from 2 (past both params, so
  -- their declared types don't clash with the param types). lam: local 2 = arg::env0, fresh from 3.
  let (bodyEnvL, freshStart) := if isThunk then (0, 2) else (2, 3)
  -- Pre-declared locals past the two params: lam declares local 2 (arg::env0, tyEnv); thunk none.
  let preTys : List String := if isThunk then [] else [tyEnv]
  -- The body's compile-time cap context = the CAPTURED caps (a closure closes over its lexical caps,
  -- mirroring the $env capture). lam PREPENDS its arg as a non-cap (`none`) slot at index 0; thunk
  -- runs the captured context directly (its dummy arg is not bound). Tag counter stays in `GCState`
  -- (module-wide), so a raise inside a lifted body still throws its captured lexical tag.
  let bodyCaps : List CapSlot := if isThunk then caps else CapSlot.none :: caps
  let stInner : GCState :=
    { st with nextFn := st.nextFn + 1, base := freshStart, next := freshStart, localTys := preTys }
  match emitCompGC bodyEnvL bodyCaps M stInner with
  | (.unsup r, st') => (.unsup r, { st with fns := st'.fns, nextFn := st'.nextFn })
  | (.ok body, st2) =>
      let prefixArg := if isThunk then "" else s!"(local.set 2 (struct.new $env (local.get 1) (local.get 0)))\n    "
      let full := s!"{prefixArg}{body}"
      let lifted : LiftedFn := ⟨fnIdx, full, st2.localTys.reverse⟩
      (.ok s!"(struct.new $clos (ref.func $fn{fnIdx}) (local.get {envL}))",
       { st with fns := lifted :: st2.fns, nextFn := st2.nextFn })

/-- Emit a `Comp` as a `(ref null $val)` expression under env-local `envL`. `caps` = the compile-time
capability context (threaded with the runtime `$env`). Threads `GCState`. -/
partial def emitCompGC (envL : Nat) (caps : List CapSlot) (c : Comp) (st : GCState) : EmitGC × GCState :=
  match c with
  | .ret v => emitValGC envL caps v st
  | .binop op a b =>
      match binopValHelper op with
      | some h =>
          -- BIGNUM add/sub (issue #132 / bignum lane B2): operands stay BOXED $val; the runtime
          -- `$addVal`/`$subVal` picks the i64 fast path (both $ival, no overflow) or the sign-magnitude
          -- limb path (promotes to $bigval, demotes a small result). No unboxI — the result is unbounded.
          match emitValGC envL caps a st with
          | (.unsup r, st') => (.unsup r, st')
          | (.ok ea, st1) =>
            match emitValGC envL caps b st1 with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok eb, st2) => (.ok s!"(call {h} {ea} {eb})", st2)
      | none =>
      match binopGCWat op with
      | some w =>
          -- MUL (bignum lane B3, still i64-wrap): unbox, i64.mul, rebox as $ival. Overflows silently
          -- past 2⁶³ until B3 lands $mulVal; NAMED in docs/notes/emission-bignum-design.md.
          match emitValGC envL caps a st with
          | (.unsup r, st') => (.unsup r, st')
          | (.ok ea, st1) =>
            match emitValGC envL caps b st1 with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok eb, st2) => (.ok (boxI s!"({w} {unboxI ea} {unboxI eb})"), st2)
      | none =>
          match op with
          | .div =>
              match emitValGC envL caps a st with
              | (.unsup r, st') => (.unsup r, st')
              | (.ok ea, st1) =>
                match emitValGC envL caps b st1 with
                | (.unsup r, st') => (.unsup r, st')
                | (.ok eb, st2) => (.ok (boxI (emitDivGCI (unboxI ea) (unboxI eb))), st2)
          | _ =>
              -- COMPARISON: emit the sum-encoded boolVal directly (`true = inr unit` tag 1,
              -- `false = inl unit` tag 0, IR.lean:173). Unlike the inline emitter (no bare-bool
              -- i64 rep), the GC path HAS a sum rep, so no fusion is needed — a subsequent `case`
              -- eliminates it generically. `unit` payload = a boxed 0 (never inspected).
              match cmpValCond op with
              | none => (.unsup s!"binop {repr op} not emittable on the GC path", st)
              | some mkCond =>
                  match emitValGC envL caps a st with
                  | (.unsup r, st') => (.unsup r, st')
                  | (.ok ea, st1) =>
                    match emitValGC envL caps b st1 with
                    | (.unsup r, st') => (.unsup r, st')
                    | (.ok eb, st2) =>
                        let u := boxI "(i64.const 0)"
                        -- BIGNUM-safe comparison (issue #132 / bignum lane B2): $cmpVal returns −1/0/1
                        -- on the mixed $ival/$bigval rep; lt = (cmp < 0), eq = (cmp == 0). Operands
                        -- stay boxed $val (no unboxI — a big operand must not truncate to i64).
                        (.ok s!"(if (result (ref null $val)) {mkCond ea eb} (then (struct.new $sum (i32.const 1) {u})) (else (struct.new $sum (i32.const 0) {u})))", st2)
  -- RUNG 5 S1: a `put`/`get` fused with its `letC` continuation. The inline path MUST fuse (unit has
  -- no i64 rep); the GC path does NOT need to (unit is a boxed $val), but a bare `letC (put) N`
  -- prepends a `none` cap slot for the unit binder — so route through the ordinary letC arm, which
  -- already pushes `.none`. No special case needed: `put`/`get` are value-producing comps.
  | .letC m n => emitLetGC envL caps m n st
  | .force fv =>
      match emitValGC envL caps fv st with
      | (.unsup r, st') => (.unsup r, st')
      | (.ok efv, st1) =>
          let (clL, st2) := st1.fresh tyVal
          (.ok (callClosGC clL efv (boxI "(i64.const 0)")), st2)
  | .lam M => emitCloVal false envL caps M st         -- LAM: arg at index 0 (prepended by the fn).
  | .app M v =>
      match emitCompGC envL caps M st with
      | (.unsup r, st') => (.unsup r, st')
      | (.ok eM, st1) =>
        match emitValGC envL caps v st1 with
        | (.unsup r, st') => (.unsup r, st')
        | (.ok ev, st2) =>
            let (clL, st3) := st2.fresh tyVal
            (.ok (callClosGC clL eM ev), st3)
  | .case v n1 n2 =>
      match emitValGC envL caps v st with
      | (.unsup r, st') => (.unsup r, st')
      | (.ok ev, st1) =>
          let (scL, st1a) := st1.fresh tyVal
          let (e1L, st1b) := st1a.fresh tyEnv
          let (e2L, st2) := st1b.fresh tyEnv
          -- each branch binds the payload at index 0 (a value ⇒ `.none` cap slot).
          match emitCompGC e1L (CapSlot.none :: caps) n1 st2 with
          | (.unsup r, st') => (.unsup r, st')
          | (.ok b1, st3) =>
            match emitCompGC e2L (CapSlot.none :: caps) n2 st3 with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok b2, st4) =>
                let payload := s!"(struct.get $sum $payload (ref.cast (ref $sum) (local.get {scL})))"
                (.ok (seqBlock s!"(local.set {scL} {ev})\n    (if (result (ref null $val)) (i32.eqz (struct.get $sum $tag (ref.cast (ref $sum) (local.get {scL}))))\n      (then (local.set {e1L} (struct.new $env {payload} (local.get {envL}))) {b1})\n      (else (local.set {e2L} (struct.new $env {payload} (local.get {envL}))) {b2}))"), st4)
  | .split v n =>
      match emitValGC envL caps v st with
      | (.unsup r, st') => (.unsup r, st')
      | (.ok ev, st1) =>
          let (scL, st1a) := st1.fresh tyVal
          let (e1L, st1b) := st1a.fresh tyEnv
          let (e2L, st2) := st1b.fresh tyEnv
          -- split binds fst at index 1, snd at index 0 (snd::fst::env) ⇒ two `.none` cap slots.
          match emitCompGC e2L (CapSlot.none :: CapSlot.none :: caps) n st2 with
          | (.unsup r, st') => (.unsup r, st')
          | (.ok bn, st3) =>
              let fst := s!"(struct.get $pair 0 (ref.cast (ref $pair) (local.get {scL})))"
              let snd := s!"(struct.get $pair 1 (ref.cast (ref $pair) (local.get {scL})))"
              (.ok (seqBlock s!"(local.set {scL} {ev})\n    (local.set {e1L} (struct.new $env {fst} (local.get {envL})))\n    (local.set {e2L} (struct.new $env {snd} (local.get {e1L})))\n    {bn}"), st3)
  | .unfold v => emitValGC envL caps v st
  -- RUNG 5 S1-S4: a `perform (vvar i) op v` dispatches CAP-KIND-FIRST (the faithful image of the kernel's
  -- per-store, identity-keyed dispatch — AbstractMachine.lean:287-313). `caps[i]` decides:
  --   · `.custom clauseMap` : a user-effect op — `call_ref` the op's lifted clause closure with `v` (S4).
  --       (matches the kernel operator ruling: a custom frame keyed with a built-in-like name IS serviced
  --       by its clause, so the custom check precedes the built-in state/txn routing.)
  --   · `.throwsTag t`      : `raise` → `(throw $exn{t} v)` (S2, zero-shot abort).
  --   · `.none`             : a state/txn cap dispatched by its RUNTIME box (`get`/`put`, S1; the three
  --       stm ops, S3) — the box is looked up via `$lookup` and the op routed by name.
  | .perform (.vvar i) op v =>
      match caps[i]? with
      | some (.custom clauseMap) =>
          -- S4: user op. Find its clause POSITION; look up the cap's $txbox (env-reachable), walk its
          -- clause list to that position, and `call_ref` with the op-value v. An updating key consumes
          -- the returned `(resumeValue, nextParam)` pair and mutates the handler's shared parameter env.
          match clauseMap.find? (fun clause => clause.1.op == op) with
          | some (key, pos) =>
              match emitValGC envL caps v st with
              | (.unsup r, st') => (.unsup r, st')
              | (.ok ev, st1) =>
                  let (tmpL, st2) := st1.fresh tyVal
                  -- #134 ESCAPE STAMP: gate the custom cap's $txbox $id before dispatching its clause.
                  let capBox := s!"(ref.cast (ref $txbox) {lookupGC envL i})"
                  let clauseE := s!"(call $clauseat (struct.get $txbox $list {capBox}) (i64.const {pos}))"
                  let cloE := s!"(struct.get $clause $closure {clauseE})"
                  let gate := s!"(call $capGate (struct.get $txbox $id {capBox}))"
                  if key.updates then
                    let (resultL, st3) := st2.fresh tyVal
                    let pairE := s!"(ref.cast (ref $pair) (local.get {resultL}))"
                    let paramEnv := s!"(struct.get $txbox $param {capBox})"
                    (.ok (seqBlock s!"{gate}\n    (local.set {resultL} {callClosGC tmpL cloE ev})\n    (struct.set $env $hd {paramEnv} (struct.get $pair 1 {pairE}))\n    (struct.get $pair 0 {pairE})"), st3)
                  else
                    (.ok (seqBlock s!"{gate}\n    {callClosGC tmpL cloE ev}"), st2)
          | none => (.unsup s!"custom op {op} unhandled by the handler's clause list (kernel: raises; no GC raise-forward in v1)", st)
      | some (.throwsTag t) =>
          if op = "raise" then
            match emitValGC envL caps v st with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok ev, st1) => (.ok s!"(throw $exn{t} {ev})", st1)
          else (.unsup s!"op {op} on a throws cap (only `raise` is a throws op)", st)
      | some .none =>
          -- S1 state / S3 txn: the cap is a runtime box in the env; route by op name.
          -- #134 ESCAPE STAMP (C2): every op FIRST gates the cap's runtime id (`$capGate`) — a state
          -- `$ref` cap or a txn `$txbox` cap carries its minting handle's `$id`; if that handle has
          -- popped (`$id >= $liveTop`) the perform traps (= escapedCap), matching the kernel oracle.
          -- The gate is a statement prefixed into the op's seqBlock. Field indices shifted: $ref/$txbox
          -- field 0 = $id, field 1 = the box/list payload.
          let refGate := s!"(call $capGate (struct.get $ref $id (ref.cast (ref $ref) {lookupGC envL i})))"
          let txGate  := s!"(call $capGate (struct.get $txbox $id (ref.cast (ref $txbox) {lookupGC envL i})))"
          if op = "get" then
            (.ok (seqBlock s!"{refGate}\n    (struct.get $ref $box (ref.cast (ref $ref) {lookupGC envL i}))"), st)
          else if op = "put" then
            match emitValGC envL caps v st with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok ev, st1) =>
                (.ok (seqBlock s!"{refGate}\n    (struct.set $ref $box (ref.cast (ref $ref) {lookupGC envL i}) {ev})\n    {boxI "(i64.const 0)"}"), st1)
          else if op = "newTVar" then
            match emitValGC envL caps v st with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok ev, st1) =>
                let hbox := s!"(ref.cast (ref $txbox) {lookupGC envL i})"
                let hlist := s!"(struct.get $txbox $list {hbox})"
                -- boxed index = $txlen(list) BEFORE the prepend; then H := cons(new $ref v, list). The
                -- txn DATA cell's $id is inert (0) — only the $txbox cap is gated. Gate then allocate.
                (.ok (seqBlock s!"{txGate}\n    {boxI s!"(call $txlen {hlist})"}\n    (struct.set $txbox $list {hbox} (struct.new $env (struct.new $ref (i64.const 0) {ev}) {hlist}))"), st1)
          else if op = "readTVar" then
            match emitValGC envL caps v st with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok ev, st1) =>
                let hlist := s!"(struct.get $txbox $list (ref.cast (ref $txbox) {lookupGC envL i}))"
                (.ok (seqBlock s!"{txGate}\n    (struct.get $ref $box (call $txcell {hlist} {unboxI ev}))"), st1)
          else if op = "writeTVar" then
            match v with
            | .pair jv w =>
                match emitValGC envL caps jv st with
                | (.unsup r, st') => (.unsup r, st')
                | (.ok ej, st1) =>
                  match emitValGC envL caps w st1 with
                  | (.unsup r, st') => (.unsup r, st')
                  | (.ok ew, st2) =>
                      let hlist := s!"(struct.get $txbox $list (ref.cast (ref $txbox) {lookupGC envL i}))"
                      (.ok (seqBlock s!"{txGate}\n    (struct.set $ref $box (call $txcell {hlist} {unboxI ej}) {ew})\n    {boxI "(i64.const 0)"}"), st2)
            | _ => (.unsup s!"writeTVar payload not a (pair index value)", st)
          else
            -- #133 C0 — FIRST-CLASS CAP dispatch. The cap-binder at index `i` is `.none` (a value/arg
            -- slot), and the op is not a built-in state/txn op — so it is a CUSTOM op performed on a
            -- capability threaded as a runtime VALUE (a handler passed INTO a closure as an argument,
            -- `app (force performer) capArg`). The runtime slot holds the handler's `$txbox` cap
            -- (the SAME value the lexical custom path builds — §8, cap-gc-rep-design.md), so dispatch
            -- REUSES the lexical machinery, sourced from the runtime value instead of a compile-time
            -- CapSlot: gate the cap's `$id` (#134 stamp — an escaped first-class cap traps), then find
            -- the exact module-local operation id in that cap's clause records and `call_ref` its
            -- closure. Every record carries its own update bit, so a multi-operation capability
            -- preserves each clause's plain/updating mode instead of inheriting the first clause's.
            match emitValGC envL caps v st with
            | (.unsup r, st') => (.unsup r, st')
            | (.ok ev, st1) =>
                let (opId, st1a) := st1.internOp op
                let (clauseL, st2) := st1a.fresh "(ref $clause)"
                let (tmpL, st3) := st2.fresh tyVal
                let (resultL, st4) := st3.fresh tyVal
                let capBox := s!"(ref.cast (ref $txbox) {lookupGC envL i})"
                let hlist  := s!"(struct.get $txbox $list {capBox})"
                let gate := s!"(call $capGate (struct.get $txbox $id {capBox}))"
                let clauseE := s!"(call $clausefind {hlist} (i64.const {opId}))"
                let cloE := s!"(struct.get $clause $closure (local.get {clauseL}))"
                let pairE := s!"(ref.cast (ref $pair) (local.get {resultL}))"
                let paramEnv := s!"(struct.get $txbox $param {capBox})"
                let resume := s!"(if (result (ref null $val)) (struct.get $clause $updates (local.get {clauseL}))\n      (then (struct.set $env $hd {paramEnv} (struct.get $pair 1 {pairE})) (struct.get $pair 0 {pairE}))\n      (else (local.get {resultL})))"
                (.ok (seqBlock s!"{gate}\n    (local.set {clauseL} {clauseE})\n    (local.set {resultL} {callClosGC tmpL cloE ev})\n    {resume}"), st4)
      | none => (.unsup s!"perform target vvar {i} is free (open term) — no capability in scope", st)
  | .perform _ _ _ => (.unsup "perform on a non-vvar target (runtime cap / malformed — out of the GC-path fragment)", st)
  -- RUNG 5 S1: handle (state s₀) M on the GC path. Mint a $ref box holding s₀, PREPEND it as env slot
  -- 0 (so M's index-0 cap-binder resolves to the box via $lookup — exactly the inline `.state` Slot,
  -- now a heap box reachable by closures). The handle's value is M's value (handler return = identity,
  -- Eval.lean:65). Fuse the box construction into the env via a fresh env local, like `letC`. The
  -- state cap is NOT a compile-time throws tag ⇒ push `.none` (its dispatch is the runtime $ref box).
  | .handle (.state _ s₀) M =>
      match emitValGC envL caps s₀ st with
      | (.unsup r, st') => (.unsup s!"state init value: {r}", st')
      | (.ok es₀, st1) =>
          let (idL, st1a) := st1.fresh "i64"        -- #134: holds the minted handler id (for the exit).
          let (valL, st1b) := st1a.fresh tyVal       -- holds M's value across the $capExit restore.
          let (e2L, st2) := st1b.fresh tyEnv
          match emitCompGC e2L (CapSlot.none :: caps) M st2 with
          | (.unsup r, st') => (.unsup r, st')
          | (.ok bM, st3) =>
              -- #134 ESCAPE STAMP: mint id (bumps $liveTop), stamp the $ref cap with it, run M, then
              -- SAVE M's value, restore $liveTop ($capExit), yield the saved value. A {get} thunk that
              -- escaped in M's value carries the stamped $ref; forced past this exit its $id >= $liveTop
              -- ⇒ $capGate traps (= escapedCap). env slot 0 = a fresh stamped $ref box wrapping s₀.
              (.ok (seqBlock s!"(local.set {idL} (call $capMint))\n    (local.set {e2L} (struct.new $env (struct.new $ref (local.get {idL}) {es₀}) (local.get {envL})))\n    (local.set {valL} {bM})\n    (call $capExit (local.get {idL}))\n    (local.get {valL})"), st3)
  -- RUNG 5 S2: handle (throws ℓ) M on the GC path. Mint a fresh module-wide tag `t`, push `.throwsTag t`
  -- for M's index-0 cap-binder (compile-time), wrap the body in `(block $h{t} (try_table (catch
  -- $exn{t} $h{t}) <body>))`. The result type is `(ref null $val)` (the GC value rep), so both the
  -- normal exit AND the caught payload are $val refs. Rep-agnostic control flow (rung-5 design (a)):
  -- try_table/throw port verbatim from rung 2 — only the result TYPE changed from i64 to $val. M still
  -- needs a runtime $env slot for its cap-binder (indices line up); the box holds nothing meaningful
  -- (the cap is dispatched by the compile-time tag), so push a null-carrying $env slot.
  | .handle (.throws _) M =>
      let (t, st1) := st.freshTag
      let (idL, st1a) := st1.fresh "i64"          -- #134: the minted id (bumps $liveTop for nesting).
      let (valL, st1b) := st1a.fresh tyVal         -- M's value (normal OR caught), across $capExit.
      let (e2L, st2) := st1b.fresh tyEnv
      match emitCompGC e2L (CapSlot.throwsTag t :: caps) M st2 with
      | (.unsup r, st') => (.unsup r, st')
      | (.ok bM, st3) =>
          -- env slot 0 = a placeholder (the throws cap has no runtime value — dispatch is the tag);
          -- a boxed unit keeps the $env slot well-typed and the de-Bruijn depth aligned.
          -- #134 ESCAPE STAMP: a throws handle still bumps/restores $liveTop so a state/custom cap
          -- NESTED under it gets a correctly-ordered id (the watermark counts ALL open handlers). A
          -- `raise` on an ESCAPED throws cap throws a tag whose try_table has exited ⇒ wasm's uncaught
          -- throw traps (fail-loud) — no extra gate needed for throws itself. The block's value (normal
          -- exit OR the caught payload) is captured, $liveTop restored, then yielded.
          (.ok (seqBlock s!"(local.set {idL} (call $capMint))\n    (local.set {e2L} (struct.new $env {boxI "(i64.const 0)"} (local.get {envL})))\n    (local.set {valL} (block $h{t} (result (ref null $val))\n      (try_table (result (ref null $val)) (catch $exn{t} $h{t})\n        {bM})))\n    (call $capExit (local.get {idL}))\n    (local.get {valL})"), st3)
  -- RUNG 5 S3: handle (transaction Θ) M on the GC path. Empty-start only (Θ=[], all v1 STM surface,
  -- ADR-0030). Mint a fresh heap box H = (new $ref null) held in a local, push it as env slot 0. Run M
  -- under a `catch_all_ref`/`throw_ref` wrapper INSIDE any enclosing throws try_table: on ANY abort
  -- crossing the txn boundary, RESET H's list to null (rollback — the journal drops; empty-start
  -- restore, rung-3 §Q3) then re-raise the same exnref so the lexically-enclosing throws handler still
  -- catches. This restore is EXPLICIT and load-bearing (rung-3 key finding: wasm unwinds free but the
  -- heap mutation is not undone) — even though the txn-local cells are also GC-unreachable after unwind,
  -- resetting H matches `bang run`'s discard-Θ'-on-abort exactly. Commit (fall-through) keeps writes.
  | .handle (.transaction _ Θ) M =>
      if Θ ≠ [] then
        (.unsup "transaction with a non-empty initial heap Θ (only `atomically`/empty-start lowers)", st)
      else
        let (hL, st1) := st.fresh "(ref $txbox)"        -- the heap box, kept in a local for rollback
        let (idL, st1a) := st1.fresh "i64"              -- #134: the minted id (stamps the $txbox cap).
        let (e2L, st2) := st1a.fresh tyEnv
        match emitCompGC e2L (CapSlot.none :: caps) M st2 with
        | (.unsup r, st') => (.unsup r, st')
        | (.ok bM, st3) =>
            -- #134 ESCAPE STAMP: mint id (bumps $liveTop), stamp the $txbox with it. env slot 0 = H;
            -- body under a txcommit/txab rollback wrapper. On the COMMIT (fall-through) path, restore
            -- $liveTop after the block; on ABORT the throw_ref unwinds past here (an outer catcher's
            -- exit restores). The custom-only parameter field is null for a transaction box.
            (.ok (seqBlock s!"(local.set {idL} (call $capMint))\n    (local.set {hL} (struct.new $txbox (local.get {idL}) (ref.null $env) (ref.null $env)))\n    (local.set {e2L} (struct.new $env (local.get {hL}) (local.get {envL})))\n    (block $txc{hL} (result (ref null $val))\n      (block $txa{hL} (result exnref)\n        (try_table (result (ref null $val)) (catch_all_ref $txa{hL})\n          {bM})\n        (call $capExit (local.get {idL}))\n        (br $txc{hL}))\n      (struct.set $txbox $list (local.get {hL}) (ref.null $env))\n      (throw_ref))"), st3)
  -- RUNG 5 S4: handle (custom p cls) M on the GC path — user-defined effects (ADR-0085 Stage 4). A
  -- custom op runs `subst p (subst (shift v) clause.2)` INLINE (one-shot resume, no reified
  -- continuation, rung-5 design (c)). Image: build a shared mutable `pEnvL = (p ::
  -- handlerEnv)`, lambda-lift EACH clause body as a lam-style `$clos` capturing pEnvL (so the clause's
  -- index 0 = the op-arg the fn prepends, index 1 = p, index ≥2 = handlerEnv — exactly the subst
  -- order). A matching `perform op v` `call_ref`s that closure with `v`. The CapSlot.custom carries the
  -- op→closure-local map (compile-time dispatch). M's cap-binder gets a placeholder $env slot; the
  -- clause closures are built (local.set) in the prefix, before M runs.
  | .handle (.custom _ p cls) M =>
      match emitValGC envL caps p st with
      | (.unsup r, st') => (.unsup s!"custom handler param: {r}", st')
      | (.ok ep, st1) =>
          let (pEnvL, st2) := st1.fresh tyEnv
          -- Build the clause-closure list expression (clause 0 FRONTMOST) + the op→position map.
          match emitClauses pEnvL caps 0 cls st2 with
          | (.error r, _) => (.unsup r, st2)
          | (.ok (clauseMap, listExpr), st3) =>
              let (boxL, st3a) := st3.fresh "(ref $txbox)"    -- a $txbox holding the clause-closure list
              let (idL, st3b) := st3a.fresh "i64"             -- #134: the minted id (stamps the cap).
              let (valL, st3c) := st3b.fresh tyVal            -- M's value, across the $capExit restore.
              let (capL, st4) := st3c.fresh tyEnv
              match emitCompGC capL (CapSlot.custom clauseMap :: caps) M st4 with
              | (.unsup r, st') => (.unsup r, st')
              | (.ok bM, st5) =>
                  -- #134 ESCAPE STAMP: mint id (bumps $liveTop), stamp the clause-list $txbox with it.
                  -- pEnvL := (p :: handlerEnv); cap env slot := the box; run M; save its value; restore
                  -- $liveTop; yield. A closure escaping in M's value that performs the op carries the
                  -- stamped cap; forced past this exit its $id >= $liveTop ⇒ $capGate traps. $txbox
                  -- fields are id, clause-record list, and shared parameter env. Exact operation
                  -- identity and update mode live on each record, so first-class multi-op dispatch
                  -- needs no handler-wide shortcut.
                  (.ok (seqBlock s!"(local.set {pEnvL} (struct.new $env {ep} (local.get {envL})))\n    (local.set {idL} (call $capMint))\n    (local.set {boxL} (struct.new $txbox (local.get {idL}) {listExpr} (local.get {pEnvL})))\n    (local.set {capL} (struct.new $env (local.get {boxL}) (local.get {envL})))\n    (local.set {valL} {bM})\n    (call $capExit (local.get {idL}))\n    (local.get {valL})"), st5)
  | .oom => (.unsup "oom", st)
  | .wrong s => (.unsup s!"wrong: {s}", st)

/-- RUNG 5 S4: lambda-lift each custom clause body as a `$clos` capturing `pEnvL = (p :: handlerEnv)`,
wrap it in a `$clause` record, and BUILD an `$env` list with clause 0 FRONTMOST (so lexical
op-position `k` = `k` steps from the front). Returns the compile-time op→position map and runtime
record-list expression. `pos` counts the current clause's position. `Except String` on refusal. -/
partial def emitClauses (pEnvL : Nat) (caps : List CapSlot) (pos : Nat) :
    List (Bang.ClauseKey × Comp) → GCState →
      Except String (List (Bang.ClauseKey × Nat) × String) × GCState
  | [], st => (.ok ([], "(ref.null $env)"), st)
  | (op, body) :: rest, st =>
      let (opId, st0) := st.internOp op.op
      -- lam-style lift: the fn prepends its arg (the op-value v) at index 0; the captured env is
      -- (p :: handlerEnv), so index 1 = p, index ≥2 = handlerEnv (the subst (shift v)/subst p order).
      match emitCloVal false pEnvL (CapSlot.none :: caps) body st0 with
      | (.unsup r, st') => (.error r, st')
      | (.ok cloE, st1) =>
          match emitClauses pEnvL caps (pos + 1) rest st1 with
          | (.error r, st') => (.error r, st')
          | (.ok (restMap, restList), st2) =>
              -- Cons a runtime clause record: exact module-local op identity, its own update mode,
              -- and the lifted closure. Clause 0 remains frontmost for lexical position dispatch.
              let updateFlag : Nat := if op.updates then 1 else 0
              let record := s!"(struct.new $clause (i64.const {opId}) (i32.const {updateFlag}) {cloE})"
              (.ok ((op, pos) :: restMap, s!"(struct.new $env {record} {restList})"), st2)

/-- `letC m n`: compute m, bind its value at index 0 in a fresh env local, run n. n's index-0 binder
is a VALUE (m's result) ⇒ push `.none` in the cap context. When index 0 is absent, still evaluate
`m` (it may have effects), drop only its result, substitute away the dead binder to renumber outer
indices, and emit `n` under the original environment. -/
partial def emitLetGC (envL : Nat) (caps : List CapSlot) (m n : Comp) (st : GCState) : EmitGC × GCState :=
  match emitCompGC envL caps m st with
  | (.unsup r, st') => (.unsup r, st')
  | (.ok em, st1) =>
      if usesBinderC 0 n then
        let (e2L, st2) := st1.fresh tyEnv
        match emitCompGC e2L (CapSlot.none :: caps) n st2 with
        | (.unsup r, st') => (.unsup r, st')
        | (.ok en, st3) =>
            (.ok (seqBlock s!"(local.set {e2L} (struct.new $env {em} (local.get {envL})))\n    {en}"), st3)
      else
        match emitCompGC envL caps (Comp.subst .vunit n) st1 with
        | (.unsup r, st') => (.unsup r, st')
        | (.ok en, st2) => (.ok (seqBlock s!"(drop {em})\n    {en}"), st2)

/-- Call closure `cloE` with arg `argE` (both `(ref null $val)`): stash the cast closure in temp
local `clL`, dispatch `call_ref` on its `$code` with its captured `$env` + the arg. Wrapped in a
`seqBlock` so it is a single value expression (composes when `cloE`/`argE` are themselves calls). -/
partial def callClosGC (clL : Nat) (cloE argE : String) : String :=
  seqBlock s!"(local.set {clL} {cloE})\n    (call_ref $fn (struct.get $clos $env (ref.cast (ref $clos) (local.get {clL}))) {argE} (struct.get $clos $code (ref.cast (ref $clos) (local.get {clL}))))"
end

/-- The fixed WASM-GC recursive TYPE block (`$val` supertype + subtypes + `$env`/`$fn`/`$clos`). Split
from the helper funcs so the print module can interleave WASI imports between the two — wat requires
ALL imports precede ANY function definition. -/
def gcTypes : String :=
  "(rec\n" ++
  "    (type $val  (sub (struct)))\n" ++
  "    (type $ival (sub $val (struct (field i64))))\n" ++
  -- BIGNUM (issue #132 / bignum lane B1): a $bigval carries an unbounded ℤ as sign-magnitude —
  -- $sign (0 = non-negative, 1 = negative; zero is always sign 0) + $mag, a base-10⁹ limb array
  -- (LEAST-significant limb first, no leading zero limbs). Base 10⁹ makes decimal readback a
  -- zero-pad concat (`$emitBig`) and keeps limb·limb < 2⁶³ for schoolbook mul (bignum lane B2/B3).
  -- A LITERAL past [−2⁶³,2⁶³) emits as a $bigval (`emitBigLit`); in-range ints stay $ival. See
  -- `docs/notes/emission-bignum-design.md`.
  "    (type $limbs  (array (mut i64)))\n" ++
  "    (type $bigval (sub $val (struct (field $sign i32) (field $mag (ref $limbs)))))\n" ++
  "    (type $sum  (sub $val (struct (field $tag i32) (field $payload (ref null $val)))))\n" ++
  "    (type $pair (sub $val (struct (field (ref null $val)) (field (ref null $val)))))\n" ++
  -- RUNG 5: a $ref is a MUTABLE box holding a $val — the GC-path image of a state cell / TVar cell.
  -- A `handle (state s₀)` mints one and pushes it as an ordinary $env slot, so a captured closure
  -- reads/mutates it via the SAME $lookup rung 4 uses (get = struct.get, put = struct.set). This is
  -- the unified-rep move (rung-5 design (b) Candidate 1): the compile-time inline `.state` LOCAL
  -- becomes a runtime heap box, reachable through the env cons-list.
  -- #134 ESCAPE STAMP (C2): field $id = the generative handler identity (ADR-0055). For a STATE cap
  -- cell it is the minting handle's id; a `get`/`put` gates `$id < $liveTop` (the runtime image of
  -- `splitAtId K n ≠ none` / `WellCounted`'s `< g` bound) else traps = the defined `escapedCap`
  -- fail-loud (ADR-0063). For a TXN data cell (also a $ref) the id is inert (id 0) — txn cells are
  -- never performed on as caps; only the $txbox is the cap. `$box` (field 1) is the mutable payload.
  "    (type $ref  (sub $val (struct (field $id i64) (field $box (mut (ref null $val))))))\n" ++
  -- RUNG 5 S4: a runtime clause record carries exact module-local operation identity, that clause's
  -- own plain/updating mode, and its lifted closure. The identity is assigned by exact String
  -- interning during emission, so first-class dispatch has neither hashes nor collision risk.
  "    (type $clause (sub $val (struct (field $op i64) (field $updates i32) (field $closure (ref null $val)))))\n" ++
  -- RUNG 5 S3/S4: `$list` is the transaction journal or custom clause-record list. Custom boxes also
  -- point at the shared parameter environment; transaction boxes use null. `$env.$hd` is mutable
  -- solely so an updating clause can install nextParam while every clause closure keeps capturing
  -- the same environment object.
  "    (type $txbox (sub $val (struct (field $id i64) (field $list (mut (ref null $env))) (field $param (ref null $env)))))\n" ++
  "    (type $env  (struct (field $hd (mut (ref null $val))) (field $tl (ref null $env))))\n" ++
  "    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))\n" ++
  "    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env))))))"

/-- The fixed `$box`/`$lookup` helper functions, plus the RUNG 5 S3 transaction-heap helpers.

The TVar heap is the GC image of the kernel's `Θ : List Val` (rung-3 Q1 option B — a GC list of
`$ref` cells, the right rep once a TVar can hold a closure/ADT). A `handle (transaction)` mints a
`$ref` box `H` holding a `(ref null $env)` list of `$ref` CELLS, cells PREPENDED (newest at front).
`newTVar` returns `Θ.length` (the OLD length = the kernel index) and prepends a fresh cell; a cell
with kernel-index `i` sits at front-position `(length-1-i)`. `readTVar`/`writeTVar` walk to that cell
and `struct.get`/`struct.set` it — the SAME in-place resume as state (one-shot, ADR-0025). Rollback
= reset `H` to null (the journal drops; empty-start restore, rung-3 §Q3). -/
def gcHelpers : String :=
  -- #134 ESCAPE STAMP (C2): the runtime image of the kernel's global-fresh handler-identity counter
  -- (ADR-0055) + the live-frame chain (`splitAtId`). `$nextId` mints a fresh id per `handle`;
  -- `$liveTop` is the high-water mark = the count of currently-OPEN handlers. A `handle` bumps
  -- `$liveTop := ++$nextId` on entry and restores it to its own minted id on exit; a `perform` on a
  -- cap with id `n` gates `n < $liveTop` (its minting frame still live) else TRAPS = the defined
  -- `escapedCap` fail-loud (ADR-0063). This is EXACTLY `WellCounted`'s `< g` bound (Invariants.lean:31)
  -- made runtime: ids are monotone-fresh (never reused), so a popped handler's id is strictly below
  -- every later mint and can never be revived by a later frame's watermark (the ADR-0054 impostor
  -- collision the global counter kills). `$capMint` = mint+open; `$capExit` = restore; `$capGate`
  -- = the liveness check (traps on escape).
  "  (global $liveTop (mut i64) (i64.const 0))\n" ++
  "  (global $nextId  (mut i64) (i64.const 0))\n" ++
  -- mint a fresh id, OPEN the frame ($liveTop = ++$nextId), return the minted id (for the later exit).
  "  (func $capMint (result i64) (local $m i64)\n" ++
  "    (local.set $m (global.get $nextId))\n" ++
  "    (global.set $nextId (i64.add (global.get $nextId) (i64.const 1)))\n" ++
  "    (global.set $liveTop (global.get $nextId))\n" ++
  "    (local.get $m))\n" ++
  -- EXIT: the handle pops — restore $liveTop to the minting id (frames minted above it are now dead).
  "  (func $capExit (param $m i64) (global.set $liveTop (local.get $m)))\n" ++
  -- GATE: trap (= escapedCap) if the cap's id names a handler that has popped ($id >= $liveTop).
  "  (func $capGate (param $id i64)\n" ++
  "    (if (i64.ge_s (local.get $id) (global.get $liveTop)) (then (unreachable))))\n" ++
  "  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))\n" ++
  "  (func $lookup (param $e (ref null $env)) (param $n i32) (result (ref null $val))\n" ++
  "    (block $done (loop $l\n" ++
  "      (br_if $done (i32.eqz (local.get $n)))\n" ++
  "      (local.set $e (struct.get $env $tl (local.get $e)))\n" ++
  "      (local.set $n (i32.sub (local.get $n) (i32.const 1)))\n" ++
  "      (br $l)))\n" ++
  "    (struct.get $env $hd (local.get $e)))\n" ++
  -- $txlen: the current heap length = Θ.length (walk the cons-list). newTVar returns this as the index.
  "  (func $txlen (param $h (ref null $env)) (result i64) (local $n i64)\n" ++
  "    (local.set $n (i64.const 0))\n" ++
  "    (block $d (loop $l\n" ++
  "      (br_if $d (ref.is_null (local.get $h)))\n" ++
  "      (local.set $n (i64.add (local.get $n) (i64.const 1)))\n" ++
  "      (local.set $h (struct.get $env $tl (local.get $h)))\n" ++
  "      (br $l)))\n" ++
  "    (local.get $n))\n" ++
  -- $txcell: the $ref CELL for kernel-index `i` — at front-position (length-1-i), since cells are
  -- prepended (newest first). Walk that many $tl steps, cast the $hd to $ref.
  "  (func $txcell (param $h (ref null $env)) (param $i i64) (result (ref $ref)) (local $k i64)\n" ++
  "    (local.set $k (i64.sub (i64.sub (call $txlen (local.get $h)) (i64.const 1)) (local.get $i)))\n" ++
  "    (block $d (loop $l\n" ++
  "      (br_if $d (i64.eqz (local.get $k)))\n" ++
  "      (local.set $h (struct.get $env $tl (local.get $h)))\n" ++
  "      (local.set $k (i64.sub (local.get $k) (i64.const 1)))\n" ++
  "      (br $l)))\n" ++
  "    (ref.cast (ref $ref) (struct.get $env $hd (local.get $h))))\n" ++
  -- RUNG 5 S4: $clauseat walks `k` steps from the FRONT of a custom cap's clause-record list.
  -- Lexical dispatch already knows this position from CapSlot.custom and keeps that direct fast path.
  "  (func $clauseat (param $h (ref null $env)) (param $k i64) (result (ref $clause))\n" ++
  "    (block $d (loop $l\n" ++
  "      (br_if $d (i64.eqz (local.get $k)))\n" ++
  "      (local.set $h (struct.get $env $tl (local.get $h)))\n" ++
  "      (local.set $k (i64.sub (local.get $k) (i64.const 1)))\n" ++
  "      (br $l)))\n" ++
  "    (ref.cast (ref $clause) (struct.get $env $hd (local.get $h))))\n" ++
  -- A first-class perform has no CapSlot position, so $clausefind searches only the supplied cap's
  -- records for the exact interned operation id. Missing operations trap loudly instead of selecting
  -- another clause. The source type system prevents that case for well-typed programs.
  "  (func $clausefind (param $h (ref null $env)) (param $op i64) (result (ref $clause))\n" ++
  "    (block $missing\n" ++
  "      (loop $search\n" ++
  "        (br_if $missing (ref.is_null (local.get $h)))\n" ++
  "        (if (i64.eq (struct.get $clause $op (ref.cast (ref $clause) (struct.get $env $hd (local.get $h)))) (local.get $op))\n" ++
  "          (then (return (ref.cast (ref $clause) (struct.get $env $hd (local.get $h))))))\n" ++
  "        (local.set $h (struct.get $env $tl (local.get $h)))\n" ++
  "        (br $search)))\n" ++
  "    (unreachable))"

/-- BIGNUM runtime helpers (issue #132 / bignum lane B2): sign-magnitude arithmetic over the mixed
`$ival`/`$bigval` rep. Each `$addVal`/`$subVal` takes two `(ref null $val)` and returns one, with an
i64 FAST PATH (both `$ival`, no signed overflow ⇒ `$ival`) and a limb SLOW PATH (`$toBig` promote,
sign-magnitude `$addMag`/`$subMag` dispatched on signs via `$cmpMag`, `$normBig` demotes a small
result back to `$ival`). `$cmpVal` returns −1/0/1 (used by the `lt`/`eq` arms). Witnessed:
`scratch/bignum-addval-witness.wat` (all cases == hand oracle on wasmtime 45). Mul is bignum lane B3.
Every routine keeps the normalization invariant (no leading zero limbs; canonical zero). -/
def bignumHelpers : String :=
  "  (func $bIsBig (param $v (ref null $val)) (result i32) (ref.test (ref $bigval) (local.get $v)))\n" ++
  "  (func $bIsIval (param $v (ref null $val)) (result i32) (ref.test (ref $ival) (local.get $v)))\n" ++
  "  (func $bIvalN (param $v (ref null $val)) (result i64) (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))\n" ++
  "  (func $bLimbsOfU (param $m i64) (result (ref $limbs)) (local $n i32) (local $t i64) (local $r (ref $limbs)) (local $i i32)\n" ++
  "    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $m) (i64.const 1000000000)))\n" ++
  "    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))\n" ++
  "      (local.set $n (i32.add (local.get $n) (i32.const 1)))\n" ++
  "      (local.set $t (i64.div_u (local.get $t) (i64.const 1000000000))) (br $cl)))\n" ++
  "    (local.set $r (array.new_default $limbs (local.get $n))) (local.set $i (i32.const 0))\n" ++
  "    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $n)))\n" ++
  "      (array.set $limbs (local.get $r) (local.get $i) (i64.rem_u (local.get $m) (i64.const 1000000000)))\n" ++
  "      (local.set $m (i64.div_u (local.get $m) (i64.const 1000000000)))\n" ++
  "      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))\n" ++
  "    (local.get $r))\n" ++
  "  (func $bToBig (param $v (ref null $val)) (result (ref $bigval)) (local $n i64) (local $sign i32) (local $mag i64)\n" ++
  "    (if (result (ref $bigval)) (call $bIsBig (local.get $v))\n" ++
  "      (then (ref.cast (ref $bigval) (local.get $v)))\n" ++
  "      (else\n" ++
  "        (local.set $n (call $bIvalN (local.get $v)))\n" ++
  "        (if (i64.lt_s (local.get $n) (i64.const 0))\n" ++
  "          (then (local.set $sign (i32.const 1)) (local.set $mag (i64.sub (i64.const 0) (local.get $n))))\n" ++
  "          (else (local.set $sign (i32.const 0)) (local.set $mag (local.get $n))))\n" ++
  "        (struct.new $bigval (local.get $sign) (call $bLimbsOfU (local.get $mag))))))\n" ++
  "  (func $bAddMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))\n" ++
  "    (local $la i32) (local $lb i32) (local $n i32) (local $i i32) (local $carry i64) (local $sum i64) (local $r (ref $limbs)) (local $av i64) (local $bv i64)\n" ++
  "    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))\n" ++
  "    (local.set $n (i32.add (select (local.get $la) (local.get $lb) (i32.gt_u (local.get $la) (local.get $lb))) (i32.const 1)))\n" ++
  "    (local.set $r (array.new_default $limbs (local.get $n))) (local.set $i (i32.const 0)) (local.set $carry (i64.const 0))\n" ++
  "    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $n)))\n" ++
  "      (local.set $av (if (result i64) (i32.lt_u (local.get $i) (local.get $la)) (then (array.get $limbs (local.get $a) (local.get $i))) (else (i64.const 0))))\n" ++
  "      (local.set $bv (if (result i64) (i32.lt_u (local.get $i) (local.get $lb)) (then (array.get $limbs (local.get $b) (local.get $i))) (else (i64.const 0))))\n" ++
  "      (local.set $sum (i64.add (i64.add (local.get $av) (local.get $bv)) (local.get $carry)))\n" ++
  "      (local.set $carry (i64.div_u (local.get $sum) (i64.const 1000000000)))\n" ++
  "      (array.set $limbs (local.get $r) (local.get $i) (i64.rem_u (local.get $sum) (i64.const 1000000000)))\n" ++
  "      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))\n" ++
  "    (call $bTrim (local.get $r)))\n" ++
  "  (func $bCmpMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result i32)\n" ++
  "    (local $la i32) (local $lb i32) (local $i i32) (local $av i64) (local $bv i64)\n" ++
  "    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))\n" ++
  "    (if (i32.gt_u (local.get $la) (local.get $lb)) (then (return (i32.const 1))))\n" ++
  "    (if (i32.lt_u (local.get $la) (local.get $lb)) (then (return (i32.const -1))))\n" ++
  "    (local.set $i (i32.sub (local.get $la) (i32.const 1)))\n" ++
  "    (block $d (loop $l (br_if $d (i32.lt_s (local.get $i) (i32.const 0)))\n" ++
  "      (local.set $av (array.get $limbs (local.get $a) (local.get $i))) (local.set $bv (array.get $limbs (local.get $b) (local.get $i)))\n" ++
  "      (if (i64.gt_u (local.get $av) (local.get $bv)) (then (return (i32.const 1))))\n" ++
  "      (if (i64.lt_u (local.get $av) (local.get $bv)) (then (return (i32.const -1))))\n" ++
  "      (local.set $i (i32.sub (local.get $i) (i32.const 1))) (br $l)))\n" ++
  "    (i32.const 0))\n" ++
  "  (func $bTrim (param $r (ref $limbs)) (result (ref $limbs)) (local $top i32) (local $n i32) (local $i i32) (local $o (ref $limbs))\n" ++
  "    (local.set $top (i32.sub (array.len (local.get $r)) (i32.const 1)))\n" ++
  "    (block $td (loop $tl (br_if $td (i32.eqz (local.get $top)))\n" ++
  "      (br_if $td (i64.ne (array.get $limbs (local.get $r) (local.get $top)) (i64.const 0)))\n" ++
  "      (local.set $top (i32.sub (local.get $top) (i32.const 1))) (br $tl)))\n" ++
  "    (local.set $n (i32.add (local.get $top) (i32.const 1)))\n" ++
  "    (if (i32.eq (local.get $n) (array.len (local.get $r))) (then (return (local.get $r))))\n" ++
  "    (local.set $o (array.new_default $limbs (local.get $n))) (local.set $i (i32.const 0))\n" ++
  "    (block $cd (loop $cl (br_if $cd (i32.ge_u (local.get $i) (local.get $n)))\n" ++
  "      (array.set $limbs (local.get $o) (local.get $i) (array.get $limbs (local.get $r) (local.get $i)))\n" ++
  "      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $cl)))\n" ++
  "    (local.get $o))\n" ++
  "  (func $bSubMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))\n" ++
  "    (local $la i32) (local $lb i32) (local $i i32) (local $borrow i64) (local $av i64) (local $bv i64) (local $diff i64) (local $r (ref $limbs))\n" ++
  "    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))\n" ++
  "    (local.set $r (array.new_default $limbs (local.get $la))) (local.set $i (i32.const 0)) (local.set $borrow (i64.const 0))\n" ++
  "    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $la)))\n" ++
  "      (local.set $av (array.get $limbs (local.get $a) (local.get $i)))\n" ++
  "      (local.set $bv (if (result i64) (i32.lt_u (local.get $i) (local.get $lb)) (then (array.get $limbs (local.get $b) (local.get $i))) (else (i64.const 0))))\n" ++
  "      (local.set $diff (i64.sub (i64.sub (local.get $av) (local.get $bv)) (local.get $borrow)))\n" ++
  "      (if (i64.lt_s (local.get $diff) (i64.const 0))\n" ++
  "        (then (local.set $diff (i64.add (local.get $diff) (i64.const 1000000000))) (local.set $borrow (i64.const 1)))\n" ++
  "        (else (local.set $borrow (i64.const 0))))\n" ++
  "      (array.set $limbs (local.get $r) (local.get $i) (local.get $diff))\n" ++
  "      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))\n" ++
  "    (call $bTrim (local.get $r)))\n" ++
  "  (func $bNormBig (param $sign i32) (param $mag (ref $limbs)) (result (ref null $val)) (local $len i32) (local $v i64)\n" ++
  "    (local.set $len (array.len (local.get $mag)))\n" ++
  "    (if (i32.le_u (local.get $len) (i32.const 2))\n" ++
  "      (then\n" ++
  "        (local.set $v (array.get $limbs (local.get $mag) (i32.const 0)))\n" ++
  "        (if (i32.eq (local.get $len) (i32.const 2))\n" ++
  "          (then (local.set $v (i64.add (local.get $v) (i64.mul (array.get $limbs (local.get $mag) (i32.const 1)) (i64.const 1000000000))))))\n" ++
  "        (if (i32.eq (local.get $sign) (i32.const 1)) (then (local.set $v (i64.sub (i64.const 0) (local.get $v)))))\n" ++
  "        (return (struct.new $ival (local.get $v)))))\n" ++
  "    (struct.new $bigval (local.get $sign) (local.get $mag)))\n" ++
  "  (func $addVal (param $x (ref null $val)) (param $y (ref null $val)) (result (ref null $val))\n" ++
  "    (local $bx (ref $bigval)) (local $by (ref $bigval)) (local $sx i32) (local $sy i32) (local $mx (ref $limbs)) (local $my (ref $limbs)) (local $c i32) (local $a i64) (local $b i64) (local $s i64)\n" ++
  "    (if (i32.and (call $bIsIval (local.get $x)) (call $bIsIval (local.get $y)))\n" ++
  "      (then\n" ++
  "        (local.set $a (call $bIvalN (local.get $x))) (local.set $b (call $bIvalN (local.get $y)))\n" ++
  "        (local.set $s (i64.add (local.get $a) (local.get $b)))\n" ++
  "        (if (i64.ge_s (i64.and (i64.xor (local.get $a) (local.get $s)) (i64.xor (local.get $b) (local.get $s))) (i64.const 0))\n" ++
  "          (then (return (struct.new $ival (local.get $s)))))))\n" ++
  "    (local.set $bx (call $bToBig (local.get $x))) (local.set $by (call $bToBig (local.get $y)))\n" ++
  "    (local.set $sx (struct.get $bigval $sign (local.get $bx))) (local.set $sy (struct.get $bigval $sign (local.get $by)))\n" ++
  "    (local.set $mx (struct.get $bigval $mag (local.get $bx))) (local.set $my (struct.get $bigval $mag (local.get $by)))\n" ++
  "    (if (result (ref null $val)) (i32.eq (local.get $sx) (local.get $sy))\n" ++
  "      (then (call $bNormBig (local.get $sx) (call $bAddMag (local.get $mx) (local.get $my))))\n" ++
  "      (else\n" ++
  "        (local.set $c (call $bCmpMag (local.get $mx) (local.get $my)))\n" ++
  "        (if (result (ref null $val)) (i32.eqz (local.get $c))\n" ++
  "          (then (struct.new $ival (i64.const 0)))\n" ++
  "          (else (if (result (ref null $val)) (i32.eq (local.get $c) (i32.const 1))\n" ++
  "            (then (call $bNormBig (local.get $sx) (call $bSubMag (local.get $mx) (local.get $my))))\n" ++
  "            (else (call $bNormBig (local.get $sy) (call $bSubMag (local.get $my) (local.get $mx))))))))))\n" ++
  "  (func $bNeg (param $v (ref null $val)) (result (ref null $val)) (local $bg (ref $bigval)) (local $n i64)\n" ++
  "    (if (result (ref null $val)) (call $bIsIval (local.get $v))\n" ++
  "      (then\n" ++
  "        (local.set $n (call $bIvalN (local.get $v)))\n" ++
  "        (if (result (ref null $val)) (i64.eq (local.get $n) (i64.const -9223372036854775808))\n" ++
  "          (then (struct.new $bigval (i32.const 0) (call $bLimbsOfU (i64.const 9223372036854775808))))\n" ++
  "          (else (struct.new $ival (i64.sub (i64.const 0) (local.get $n))))))\n" ++
  "      (else\n" ++
  "        (local.set $bg (ref.cast (ref $bigval) (local.get $v)))\n" ++
  "        (if (result (ref null $val)) (i32.and (i32.eq (array.len (struct.get $bigval $mag (local.get $bg))) (i32.const 1)) (i64.eqz (array.get $limbs (struct.get $bigval $mag (local.get $bg)) (i32.const 0))))\n" ++
  "          (then (local.get $v))\n" ++
  "          (else (struct.new $bigval (i32.xor (struct.get $bigval $sign (local.get $bg)) (i32.const 1)) (struct.get $bigval $mag (local.get $bg))))))))\n" ++
  "  (func $subVal (param $x (ref null $val)) (param $y (ref null $val)) (result (ref null $val))\n" ++
  "    (call $addVal (local.get $x) (call $bNeg (local.get $y))))\n" ++
  "  (func $cmpVal (param $x (ref null $val)) (param $y (ref null $val)) (result i32)\n" ++
  "    (local $bx (ref $bigval)) (local $by (ref $bigval)) (local $sx i32) (local $sy i32) (local $c i32) (local $a i64) (local $b i64)\n" ++
  "    (if (i32.and (call $bIsIval (local.get $x)) (call $bIsIval (local.get $y)))\n" ++
  "      (then\n" ++
  "        (local.set $a (call $bIvalN (local.get $x))) (local.set $b (call $bIvalN (local.get $y)))\n" ++
  "        (if (i64.lt_s (local.get $a) (local.get $b)) (then (return (i32.const -1))))\n" ++
  "        (if (i64.gt_s (local.get $a) (local.get $b)) (then (return (i32.const 1))))\n" ++
  "        (return (i32.const 0))))\n" ++
  "    (local.set $bx (call $bToBig (local.get $x))) (local.set $by (call $bToBig (local.get $y)))\n" ++
  "    (local.set $sx (struct.get $bigval $sign (local.get $bx))) (local.set $sy (struct.get $bigval $sign (local.get $by)))\n" ++
  "    (if (i32.ne (local.get $sx) (local.get $sy)) (then (return (select (i32.const -1) (i32.const 1) (i32.eq (local.get $sx) (i32.const 1))))))\n" ++
  "    (local.set $c (call $bCmpMag (struct.get $bigval $mag (local.get $bx)) (struct.get $bigval $mag (local.get $by))))\n" ++
  "    (if (i32.eq (local.get $sx) (i32.const 1)) (then (return (i32.sub (i32.const 0) (local.get $c)))))\n" ++
  "    (local.get $c))\n" ++
  -- BIGNUM MUL (bignum lane B3): schoolbook $bMulMag (base 1e9, limb·limb < 1e18 < 2⁶³ so no
  -- 128-bit intermediate) + $mulVal with the i64 fast path (both $ival, no overflow via p/a==b AND
  -- not the INT64_MIN×-1 edge — wasm has no mul_high). Witnessed scratch/bignum-mulval-witness.wat.
  "  (func $bMulMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))\n" ++
  "    (local $la i32) (local $lb i32) (local $n i32) (local $i i32) (local $j i32) (local $r (ref $limbs)) (local $carry i64) (local $cur i64) (local $ai i64)\n" ++
  "    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))\n" ++
  "    (local.set $n (i32.add (local.get $la) (local.get $lb)))\n" ++
  "    (local.set $r (array.new_default $limbs (local.get $n))) (local.set $i (i32.const 0))\n" ++
  "    (block $od (loop $ol (br_if $od (i32.ge_u (local.get $i) (local.get $la)))\n" ++
  "      (local.set $ai (array.get $limbs (local.get $a) (local.get $i))) (local.set $carry (i64.const 0)) (local.set $j (i32.const 0))\n" ++
  "      (block $id (loop $il (br_if $id (i32.ge_u (local.get $j) (local.get $lb)))\n" ++
  "        (local.set $cur (i64.add (i64.add (array.get $limbs (local.get $r) (i32.add (local.get $i) (local.get $j))) (i64.mul (local.get $ai) (array.get $limbs (local.get $b) (local.get $j)))) (local.get $carry)))\n" ++
  "        (array.set $limbs (local.get $r) (i32.add (local.get $i) (local.get $j)) (i64.rem_u (local.get $cur) (i64.const 1000000000)))\n" ++
  "        (local.set $carry (i64.div_u (local.get $cur) (i64.const 1000000000)))\n" ++
  "        (local.set $j (i32.add (local.get $j) (i32.const 1))) (br $il)))\n" ++
  "      (array.set $limbs (local.get $r) (i32.add (local.get $i) (local.get $lb)) (i64.add (array.get $limbs (local.get $r) (i32.add (local.get $i) (local.get $lb))) (local.get $carry)))\n" ++
  "      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $ol)))\n" ++
  "    (call $bTrim (local.get $r)))\n" ++
  "  (func $bIsZeroVal (param $v (ref null $val)) (result i32)\n" ++
  "    (if (result i32) (call $bIsIval (local.get $v))\n" ++
  "      (then (i64.eqz (call $bIvalN (local.get $v))))\n" ++
  "      (else (i32.and (i32.eq (array.len (struct.get $bigval $mag (ref.cast (ref $bigval) (local.get $v)))) (i32.const 1)) (i64.eqz (array.get $limbs (struct.get $bigval $mag (ref.cast (ref $bigval) (local.get $v))) (i32.const 0)))))))\n" ++
  "  (func $mulVal (param $x (ref null $val)) (param $y (ref null $val)) (result (ref null $val))\n" ++
  "    (local $a i64) (local $b i64) (local $p i64) (local $bx (ref $bigval)) (local $by (ref $bigval)) (local $sx i32) (local $sy i32)\n" ++
  "    (if (i32.or (call $bIsZeroVal (local.get $x)) (call $bIsZeroVal (local.get $y))) (then (return (struct.new $ival (i64.const 0)))))\n" ++
  "    (if (i32.and (call $bIsIval (local.get $x)) (call $bIsIval (local.get $y)))\n" ++
  "      (then\n" ++
  "        (local.set $a (call $bIvalN (local.get $x))) (local.set $b (call $bIvalN (local.get $y)))\n" ++
  "        (local.set $p (i64.mul (local.get $a) (local.get $b)))\n" ++
  "        (if (i32.and (i64.eq (i64.div_s (local.get $p) (local.get $a)) (local.get $b)) (i32.eqz (i32.and (i64.eq (local.get $a) (i64.const -1)) (i64.eq (local.get $b) (i64.const -9223372036854775808)))))\n" ++
  "          (then (return (struct.new $ival (local.get $p)))))))\n" ++
  "    (local.set $bx (call $bToBig (local.get $x))) (local.set $by (call $bToBig (local.get $y)))\n" ++
  "    (local.set $sx (struct.get $bigval $sign (local.get $bx))) (local.set $sy (struct.get $bigval $sign (local.get $by)))\n" ++
  "    (struct.new $bigval (i32.xor (local.get $sx) (local.get $sy)) (call $bMulMag (struct.get $bigval $mag (local.get $bx)) (struct.get $bigval $mag (local.get $by)))))"

/-- The fixed WASM-GC type + helper preamble every rung-4 module shares (types then helper funcs). -/
def gcPreamble : String := gcTypes ++ "\n" ++ gcHelpers

/-- The module-header items the readback needs: the WASI `fd_write` import, one page of linear memory
(the render scratch buffer), the write cursor, and the literal pool. These MUST be emitted before any
function definition (wat's import-before-function rule), so they are separated from `renderFns`. -/
def renderImports : String :=
  "  (import \"wasi_snapshot_preview1\" \"fd_write\"\n" ++
  "    (func $fd_write (param i32 i32 i32 i32) (result i32)))\n" ++
  "  (memory (export \"memory\") 1)\n" ++
  "  (global $cur (mut i32) (i32.const 16))\n" ++
  "  (data (i32.const 0) \"()inl inr <thunk>\")"

/-- The readback FUNCTIONS: `$emitByte`/`$emitCp`/`$emitInt`/`$emitLit`/`$isStr`/`$emitStr`/`$render`/
`$flush` — the wasm image of `valPretty`/`asString`. Emitted AFTER all imports. -/
def renderFns : String :=
  "  (func $emitByte (param $b i32)\n" ++
  "    (i32.store8 (global.get $cur) (local.get $b))\n" ++
  "    (global.set $cur (i32.add (global.get $cur) (i32.const 1))))\n" ++
  "  (func $emitCp (param $cp i32)\n" ++
  "    (if (i32.lt_u (local.get $cp) (i32.const 0x80))\n" ++
  "      (then (call $emitByte (local.get $cp)))\n" ++
  "      (else (if (i32.lt_u (local.get $cp) (i32.const 0x800))\n" ++
  "        (then\n" ++
  "          (call $emitByte (i32.or (i32.const 0xC0) (i32.shr_u (local.get $cp) (i32.const 6))))\n" ++
  "          (call $emitByte (i32.or (i32.const 0x80) (i32.and (local.get $cp) (i32.const 0x3F)))))\n" ++
  "        (else (if (i32.lt_u (local.get $cp) (i32.const 0x10000))\n" ++
  "          (then\n" ++
  "            (call $emitByte (i32.or (i32.const 0xE0) (i32.shr_u (local.get $cp) (i32.const 12))))\n" ++
  "            (call $emitByte (i32.or (i32.const 0x80) (i32.and (i32.shr_u (local.get $cp) (i32.const 6)) (i32.const 0x3F))))\n" ++
  "            (call $emitByte (i32.or (i32.const 0x80) (i32.and (local.get $cp) (i32.const 0x3F)))))\n" ++
  "          (else\n" ++
  "            (call $emitByte (i32.or (i32.const 0xF0) (i32.shr_u (local.get $cp) (i32.const 18))))\n" ++
  "            (call $emitByte (i32.or (i32.const 0x80) (i32.and (i32.shr_u (local.get $cp) (i32.const 12)) (i32.const 0x3F))))\n" ++
  "            (call $emitByte (i32.or (i32.const 0x80) (i32.and (i32.shr_u (local.get $cp) (i32.const 6)) (i32.const 0x3F))))\n" ++
  "            (call $emitByte (i32.or (i32.const 0x80) (i32.and (local.get $cp) (i32.const 0x3F)))))))))))\n" ++
  "  (func $emitInt (param $n i64) (local $u i64) (local $start i32) (local $end i32) (local $t i32)\n" ++
  "    (if (i64.lt_s (local.get $n) (i64.const 0))\n" ++
  "      (then (call $emitByte (i32.const 45)) (local.set $u (i64.sub (i64.const 0) (local.get $n))))\n" ++
  "      (else (local.set $u (local.get $n))))\n" ++
  "    (local.set $start (global.get $cur))\n" ++
  "    (block $done (loop $l\n" ++
  "      (call $emitByte (i32.wrap_i64 (i64.add (i64.const 48) (i64.rem_u (local.get $u) (i64.const 10)))))\n" ++
  "      (local.set $u (i64.div_u (local.get $u) (i64.const 10)))\n" ++
  "      (br_if $l (i64.ne (local.get $u) (i64.const 0)))))\n" ++
  "    (local.set $end (i32.sub (global.get $cur) (i32.const 1)))\n" ++
  "    (block $rd (loop $rl\n" ++
  "      (br_if $rd (i32.ge_s (local.get $start) (local.get $end)))\n" ++
  "      (local.set $t (i32.load8_u (local.get $start)))\n" ++
  "      (i32.store8 (local.get $start) (i32.load8_u (local.get $end)))\n" ++
  "      (i32.store8 (local.get $end) (local.get $t))\n" ++
  "      (local.set $start (i32.add (local.get $start) (i32.const 1)))\n" ++
  "      (local.set $end (i32.sub (local.get $end) (i32.const 1)))\n" ++
  "      (br $rl))))\n" ++
  -- BIGNUM readback (issue #132 / bignum lane B1): render a $bigval to decimal. Base 10⁹ ⇒ the top
  -- limb prints BARE, every lower limb zero-padded to EXACTLY 9 digits, high→low; a '-' prefix when
  -- $sign=1. Byte-identical to `bang run`'s Lean-`Int` decimal (witnessed scratch/bigval-literal-readback.wat).
  -- $put9 writes 9 zero-padded digits of $v at [$cur,$cur+9); $putBare writes the bare decimal of $v.
  "  (func $put9 (param $v i64) (local $i i32) (local $start i32)\n" ++
  "    (local.set $start (global.get $cur))\n" ++
  "    (global.set $cur (i32.add (global.get $cur) (i32.const 9)))\n" ++
  "    (local.set $i (i32.const 8))\n" ++
  "    (block $done (loop $l\n" ++
  "      (i32.store8 (i32.add (local.get $start) (local.get $i))\n" ++
  "        (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))\n" ++
  "      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))\n" ++
  "      (br_if $done (i32.eqz (local.get $i)))\n" ++
  "      (local.set $i (i32.sub (local.get $i) (i32.const 1)))\n" ++
  "      (br $l))))\n" ++
  "  (func $putBare (param $v i64) (local $n i32) (local $t i64) (local $i i32) (local $start i32)\n" ++
  "    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $v) (i64.const 10)))\n" ++
  "    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))\n" ++
  "      (local.set $n (i32.add (local.get $n) (i32.const 1)))\n" ++
  "      (local.set $t (i64.div_u (local.get $t) (i64.const 10))) (br $cl)))\n" ++
  "    (local.set $start (global.get $cur))\n" ++
  "    (global.set $cur (i32.add (global.get $cur) (local.get $n)))\n" ++
  "    (local.set $i (i32.sub (local.get $n) (i32.const 1)))\n" ++
  "    (block $done (loop $l\n" ++
  "      (i32.store8 (i32.add (local.get $start) (local.get $i))\n" ++
  "        (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))\n" ++
  "      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))\n" ++
  "      (br_if $done (i32.eqz (local.get $i)))\n" ++
  "      (local.set $i (i32.sub (local.get $i) (i32.const 1)))\n" ++
  "      (br $l))))\n" ++
  "  (func $emitBig (param $b (ref $bigval)) (local $m (ref $limbs)) (local $i i32)\n" ++
  "    (if (i32.eq (struct.get $bigval $sign (local.get $b)) (i32.const 1))\n" ++
  "      (then (call $emitByte (i32.const 45))))\n" ++
  "    (local.set $m (struct.get $bigval $mag (local.get $b)))\n" ++
  "    (local.set $i (i32.sub (array.len (local.get $m)) (i32.const 1)))\n" ++
  "    (call $putBare (array.get $limbs (local.get $m) (local.get $i)))\n" ++
  "    (local.set $i (i32.sub (local.get $i) (i32.const 1)))\n" ++
  "    (block $d (loop $l\n" ++
  "      (br_if $d (i32.lt_s (local.get $i) (i32.const 0)))\n" ++
  "      (call $put9 (array.get $limbs (local.get $m) (local.get $i)))\n" ++
  "      (local.set $i (i32.sub (local.get $i) (i32.const 1)))\n" ++
  "      (br $l))))\n" ++
  "  (func $isBig (param $v (ref null $val)) (result i32) (ref.test (ref $bigval) (local.get $v)))\n" ++
  "  (func $emitLit (param $off i32) (param $len i32) (local $i i32)\n" ++
  "    (local.set $i (i32.const 0))\n" ++
  "    (block $d (loop $l\n" ++
  "      (br_if $d (i32.ge_u (local.get $i) (local.get $len)))\n" ++
  "      (call $emitByte (i32.load8_u (i32.add (local.get $off) (local.get $i))))\n" ++
  "      (local.set $i (i32.add (local.get $i) (i32.const 1)))\n" ++
  "      (br $l))))\n" ++
  "  (func $isSum (param $v (ref null $val)) (result i32) (ref.test (ref $sum) (local.get $v)))\n" ++
  "  (func $isPair (param $v (ref null $val)) (result i32) (ref.test (ref $pair) (local.get $v)))\n" ++
  "  (func $isIval (param $v (ref null $val)) (result i32) (ref.test (ref $ival) (local.get $v)))\n" ++
  "  (func $isStr (param $v (ref null $val)) (result i32)\n" ++
  "    (local $node (ref null $val)) (local $pr (ref null $val))\n" ++
  "    (local.set $node (local.get $v))\n" ++
  "    (if (i32.eqz (call $isSum (local.get $node))) (then (return (i32.const 0))))\n" ++
  "    (if (i32.ne (struct.get $sum $tag (ref.cast (ref $sum) (local.get $node))) (i32.const 1))\n" ++
  "      (then (return (i32.const 0))))\n" ++
  "    (block $done (loop $l\n" ++
  "      (local.set $pr (struct.get $sum $payload (ref.cast (ref $sum) (local.get $node))))\n" ++
  "      (if (i32.eqz (call $isPair (local.get $pr))) (then (return (i32.const 0))))\n" ++
  "      (if (i32.eqz (call $isIval (struct.get $pair 0 (ref.cast (ref $pair) (local.get $pr)))))\n" ++
  "        (then (return (i32.const 0))))\n" ++
  "      (local.set $node (struct.get $pair 1 (ref.cast (ref $pair) (local.get $pr))))\n" ++
  "      (if (i32.eqz (call $isSum (local.get $node))) (then (return (i32.const 0))))\n" ++
  "      (if (i32.eq (struct.get $sum $tag (ref.cast (ref $sum) (local.get $node))) (i32.const 0))\n" ++
  "        (then (return (i32.const 1))))\n" ++
  "      (br $l)))\n" ++
  "    (i32.const 1))\n" ++
  "  (func $emitStr (param $v (ref null $val)) (local $node (ref null $val)) (local $pr (ref null $val))\n" ++
  "    (local.set $node (local.get $v))\n" ++
  "    (block $done (loop $l\n" ++
  "      (if (i32.eqz (call $isSum (local.get $node))) (then (br $done)))\n" ++
  "      (if (i32.eq (struct.get $sum $tag (ref.cast (ref $sum) (local.get $node))) (i32.const 0))\n" ++
  "        (then (br $done)))\n" ++
  "      (local.set $pr (struct.get $sum $payload (ref.cast (ref $sum) (local.get $node))))\n" ++
  "      (call $emitCp (i32.wrap_i64 (struct.get $ival 0\n" ++
  "        (ref.cast (ref $ival) (struct.get $pair 0 (ref.cast (ref $pair) (local.get $pr)))))))\n" ++
  "      (local.set $node (struct.get $pair 1 (ref.cast (ref $pair) (local.get $pr))))\n" ++
  "      (br $l))))\n" ++
  "  (func $render (param $v (ref null $val))\n" ++
  "    (if (ref.is_null (local.get $v)) (then (call $emitLit (i32.const 0) (i32.const 2)) (return)))\n" ++
  "    (if (call $isBig (local.get $v))\n" ++
  "      (then (call $emitBig (ref.cast (ref $bigval) (local.get $v))) (return)))\n" ++
  "    (if (call $isIval (local.get $v))\n" ++
  "      (then (call $emitInt (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v)))) (return)))\n" ++
  "    (if (call $isPair (local.get $v))\n" ++
  "      (then\n" ++
  "        (call $emitByte (i32.const 40))\n" ++
  "        (call $render (struct.get $pair 0 (ref.cast (ref $pair) (local.get $v))))\n" ++
  "        (call $emitByte (i32.const 44)) (call $emitByte (i32.const 32))\n" ++
  "        (call $render (struct.get $pair 1 (ref.cast (ref $pair) (local.get $v))))\n" ++
  "        (call $emitByte (i32.const 41))\n" ++
  "        (return)))\n" ++
  "    (if (call $isSum (local.get $v))\n" ++
  "      (then\n" ++
  "        (if (call $isStr (local.get $v)) (then (call $emitStr (local.get $v)) (return)))\n" ++
  "        (if (i32.eq (struct.get $sum $tag (ref.cast (ref $sum) (local.get $v))) (i32.const 0))\n" ++
  "          (then (call $emitLit (i32.const 2) (i32.const 4)))\n" ++
  "          (else (call $emitLit (i32.const 6) (i32.const 4))))\n" ++
  "        (call $render (struct.get $sum $payload (ref.cast (ref $sum) (local.get $v))))\n" ++
  "        (return)))\n" ++
  "    (call $emitLit (i32.const 10) (i32.const 7)))\n" ++
  "  (func $flush\n" ++
  "    (i32.store (i32.const 4) (i32.const 16))\n" ++
  "    (i32.store (i32.const 8) (i32.sub (global.get $cur) (i32.const 16)))\n" ++
  "    (drop (call $fd_write (i32.const 1) (i32.const 4) (i32.const 1) (i32.const 12))))"

/-- The `$val` READBACK preamble (rung-5, Part 1): the WASI-command printer that walks the emitted
`$val` GC graph and renders the SAME text `Main.lean`'s `valPretty`/`asString` produce — the exact
bytes each `examples/<name>/expected.txt` carries (which IS `bang run`'s stdout). This closes rung-4's
non-Int gap (design §5.3): `caesar` returns a `Str`, not an `Int`, so `$unbox`-to-i64 gave a
meaningless answer; the printer emits its glyph string instead.

NOTE: `renderImports` (WASI import + memory + global + data pool) MUST precede any function, so a
consumer that also emits GC helper funcs must place `renderImports` BEFORE them and `renderFns` after
(this is why `emitModuleGCPrint` interleaves `gcTypes` · `renderImports` · `gcHelpers` · `renderFns`).

Correspondence to `valPretty` (Main.lean:130):
  - `vint n`   → decimal (`$emitInt`, two's-complement-safe negative handling)
  - `pair a b` → `(a, b)`
  - `inl v`/`inr v` → `inl `/`inr ` + payload   (a `$sum` that is NOT a non-empty Str)
  - a NON-EMPTY `Str` char-list → its glyphs (`asString`; `$isStr` detects the
    `SCons = $sum tag1 ($pair ($ival cp) rest)` spine, `SNil = $sum tag0` terminator)
  - `clos`/unknown → `<thunk>`  (matches `valPretty`'s `vthunk`/opaque arm)

ONE fidelity gap, honestly named: `fold` ERASES on the GC path (design §2 — no `$fold` struct), so a
bare non-Str `fold` and an EMPTY `Str` (`fold (inl ())`) — which `valPretty` prints with a `fold `
prefix — read back structurally as `inl ()` here. This never bites the corpus (every non-Int result
is a non-empty `Str`); a program returning a bare `fold` would mis-render, a documented rung-5
boundary of the erasing rep, not a silent wrong emission for the covered fragment. -/
def renderPreamble : String :=
  renderImports ++ "\n" ++ renderFns

/-- Declare locals from a per-index type list (index order). -/
def declLocalsFromTys (tys : List String) : String :=
  tys.foldl (fun acc t => acc ++ s!" (local {t})") ""

/-- Render one lifted function: two params (env0, arg) + its own locals + body. -/
def renderFn (f : LiftedFn) : String :=
  s!"(func $fn{f.idx} (type $fn) (param (ref null $env)) (param (ref null $val)) (result (ref null $val)){declLocalsFromTys f.localTys}\n    {f.body})"

/-- `(elem declare func $fn0 $fn1 …)` — every lifted fn must be declared for `ref.func`. -/
def elemDeclare (n : Nat) : String :=
  if n = 0 then "" else
    "\n  (elem declare func" ++ (List.range n).foldl (fun acc i => acc ++ s!" $fn{i}") "" ++ ")"

/-- RUNG 5 S2: `(tag $exn{t} (param (ref null $val)))` — one per minted `handle (throws)` tag. Each
throws handler carries a $val payload (unlike the inline path's i64-only tag). Emitted before any
function that `throw`s/`catch`es it. Empty when the program has no throws handler. -/
def tagDecls (n : Nat) : String :=
  (List.range n).foldl (fun acc t => acc ++ s!"\n  (tag $exn{t} (param (ref null $val)))") ""

/-- Whole-module GC emission: preamble + lifted fns + `$main`. `$main` runs the body under env-local
`base=0`, `next=1` (local 0 = the initial env, set to a null cons — `ref.null $env`). Returns full
`.wat` or a refusal. -/
def emitModuleGC (M : Comp) : EmitGC :=
  -- main: local 0 = env (starts null), fresh locals from 1. caps=[] (top-level, no open handler).
  let st0 : GCState := { base := 0, next := 1, localTys := [tyEnv] }
  match emitCompGC 0 [] M st0 with
  | (.unsup r, _) => .unsup r
  | (.ok body, stF) =>
          let fnsOrdered := stF.fns.reverse
          let fnCount := stF.nextFn
          let fnsText := (fnsOrdered.map renderFn).foldl (fun acc f => acc ++ "\n  " ++ f) ""
          let mainLocals := declLocalsFromTys stF.localTys.reverse
          let mainFn :=
            s!"(func $main (export \"main\") (result i64){mainLocals}\n    (local.set 0 (ref.null $env))\n    (call $unbox\n    {body}))"
          -- $unbox extracts the final i64 answer (main returns i64 for the harness diff).
          let unboxFn := "(func $unbox (param $v (ref null $val)) (result i64)\n    (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))"
          -- RUNG 5 S2: throws tags (if any) declared right after the type block, before any function.
          .ok s!"(module\n  {gcPreamble}\n  {bignumHelpers}{tagDecls stF.tagCount}\n  {unboxFn}{elemDeclare fnCount}{fnsText}\n  {mainFn}\n)"

/-- Whole-module GC emission with the `$val` READBACK (rung-5 Part 1): identical to `emitModuleGC`
except the entry is a WASI `_start` command that computes the body `$val`, walks it with `$render`
(the `valPretty` image, `renderPreamble`), appends a `\n` (matching `bang run`'s `IO.println`), and
`fd_write`s to stdout. This handles ANY result shape (Int / Str / sum / pair) uniformly — the printed
bytes ARE `examples/<name>/expected.txt`, so ONE readback gates the whole corpus (Int programs print
`valPretty (vint n) = toString n`, byte-identical to the old `$unbox` path). Run with plain
`wasmtime run <mod.wat>` (WASI command), NOT `--invoke main`. -/
def emitModuleGCPrint (M : Comp) : EmitGC :=
  let st0 : GCState := { base := 0, next := 1, localTys := [tyEnv] }
  match emitCompGC 0 [] M st0 with
  | (.unsup r, _) => .unsup r
  | (.ok body, stF) =>
          let fnsOrdered := stF.fns.reverse
          let fnCount := stF.nextFn
          let fnsText := (fnsOrdered.map renderFn).foldl (fun acc f => acc ++ "\n  " ++ f) ""
          let mainLocals := declLocalsFromTys stF.localTys.reverse
          -- `_start` renders the body value + a trailing newline, then flushes to stdout.
          let startFn :=
            s!"(func $_start (export \"_start\"){mainLocals}\n    (local.set 0 (ref.null $env))\n    (call $render\n    {body})\n    (call $emitByte (i32.const 10))\n    (call $flush))"
          -- Order matters (wat: imports before functions/tags): types · WASI imports · S2 throws tags ·
          -- GC helpers · readback fns · lifted fns · `_start`.
          .ok s!"(module\n  {gcTypes}\n  {renderImports}{tagDecls stF.tagCount}\n  {gcHelpers}\n  {bignumHelpers}\n  {renderFns}{elemDeclare fnCount}{fnsText}\n  {startFn}\n)"

end -- public section

end Bang.WasmEmit
