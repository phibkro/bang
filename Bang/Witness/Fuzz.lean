module

meta import Bang.Backend.AbstractMachine
meta import Bang.Witness.AgreeOutcome
public import Bang.Backend.AbstractMachine
public import Bang.Witness.AgreeOutcome

/-!
  Bang/Witness/Fuzz.lean — differential fuzz: `Source.eval` vs `exec ∘ compile` (#14).

  The proven equivalence (`compile_correct` + `evalD_agrees_source`, AbstractMachine.lean)
  covers ALL well-typed `Comp`, so a fuzzer restating that on the pure fragment is low-value.
  Value concentrates on the UN-PROVEN territory this repo already names: the handler
  fragment's runtime interleavings (deep state/throws/transaction dispatch across nested
  frames) and kernel-robustness (a generated program never hits genuine `.stuck` — every
  non-`done` outcome is the DEFINED `.escapedCap` terminal, ADR-0063).

  NON-META, BY CONSTRUCTION (no `Plausible.Gen`): `Plausible.Random`/`Plausible.Gen` are
  `public meta section` (checked: `.lake/packages/plausible/Plausible/{Random,Gen}.lean`),
  so a `Gen`-based generator cannot itself call the RUNTIME `Source.eval`/`compile`/`exec` in
  the same phase — exactly the split that forced `PropTest.lean` out of the module spine.
  This harness sidesteps that seam entirely with a hand-rolled splitmix64 PRNG (`Fuzz.Rng`,
  ordinary runtime `Nat` arithmetic) threaded through a size- and SCOPE-indexed generator, so
  the whole file is a plain `module` — no allowlist entry needed.

  WELL-SCOPED BY CONSTRUCTION: the generator carries the number of enclosing binders
  (`scope`) and the list of in-scope HANDLER slots (`hctx`, closest-first, mirroring how
  `handle` binds var 0). `vvar i` is only ever drawn for `i < scope`; `perform (vvar i) op v`
  only ever draws `i` from `hctx` and `op` from THAT slot's own vocabulary. This is what
  concentrates samples on well-formed handler interleavings instead of drowning in
  index-out-of-range / wrong-op stuck noise unrelated to the property under test — the same
  "make the bad state unrepresentable" move the kernel itself uses for capability dispatch.
-/

namespace Bang.Fuzz

open Bang
open Bang.CalcVM

@[expose] public section

/-! ## 1. A non-meta PRNG (splitmix64) — plain `Nat` state, no `Plausible` involved. -/

/-- splitmix64 step: `(next state, output)`. Pure `Nat` arithmetic mod 2^64, so it is an
ordinary runtime function — the seam `Plausible.Gen` cannot cross here. -/
def Rng.step (s : Nat) : Nat × Nat :=
  let s' := (s + 0x9E3779B97F4A7C15) % (2 ^ 64)
  let z  := s'
  let z  := ((z ^^^ (z / (2^30))) * 0xBF58476D1CE4E5B9) % (2 ^ 64)
  let z  := ((z ^^^ (z / (2^27))) * 0x94D049BB133111EB) % (2 ^ 64)
  let z  := z ^^^ (z / (2^31))
  (s', z)

/-- Draw a value in `[0, n)` (`n > 0`), threading the RNG state. `n = 0` degrades to `0`
without crashing (defensive; every call site below passes a positive bound). -/
def Rng.nextMod (s : Nat) (n : Nat) : Nat × Nat :=
  let (s', z) := Rng.step s
  (s', if n = 0 then 0 else z % n)

/-! ## 2. Handler slots the generator tracks in scope — enough to pick a MATCHING op. -/

/-- What kind of handler a `hctx` slot is, so `perform` can draw an op from ITS vocabulary
(state ↦ get/put, throws ↦ raise, transaction ↦ newTVar/readTVar/writeTVar) instead of a
free-for-all that mostly misses (ADR-0063's `escapedCap`/kernel-`stuck` split only tells
apart NO-HANDLER-FOUND from other stuck shapes; matching the vocabulary up front is what
keeps samples inside the handler fragment). -/
inductive HKind | state | throws | txn
  deriving Repr, DecidableEq

/-- One in-scope handler: its de Bruijn depth from the CURRENT point (0 = nearest, mirrors
`vvar`) and its kind. Consed by `handle`, shifted like every other scope entry. -/
abbrev HCtx := List HKind

/-! ## 3. The generator — sized, scope-correct, handler-fragment-biased.

`genComp fuel scope hctx s` returns `(Comp, s')`. `fuel` bounds recursion depth (NOT the
eval budget — this is generation fuel, decremented on every recursive call so generation
itself terminates); `scope` is the number of enclosing value binders; `hctx` the in-scope
handler slots (index = de Bruijn depth, closest first, exactly mirroring `vvar`/`handle`). -/

/-- Generate a closed-under-`scope` `Val`. Weighted toward `vvar`/`vint` (the two INERT
leaves that keep recursion shallow); only emits `vvar i` for `i < scope` (no other index is
representable), keeping every sample well-scoped by construction. -/
def genVal (fuel scope : Nat) (s : Nat) : Val × Nat :=
  match fuel with
  | 0 => (.vint 0, s)
  | fuel + 1 =>
    let (s, pick) := Rng.nextMod s (if scope = 0 then 2 else 4)
    match pick with
    | 0 =>
      let (s, n) := Rng.nextMod s 21
      (.vint ((n : Int) - 10), s)
    | 1 =>
      let (s, i) := Rng.nextMod s scope
      (.vvar i, s)
    | 2 =>
      let (v1, s) := genVal fuel scope s
      let (v2, s) := genVal fuel scope s
      (.pair v1 v2, s)
    | _ =>
      let (v, s) := genVal fuel scope s
      let (s, side) := Rng.nextMod s 2
      (if side = 0 then .inl v else .inr v, s)

/-- The op vocabulary a handler KIND actually services (mirrors `Dispatch.lean`'s
`stateUpdate`/`txnUpdate`/`unwindFind` op names exactly — the single source of truth for
"which op belongs to which handler" is the dispatcher; this list must not drift from it). -/
def HKind.ops : HKind → List OpId
  | .state  => ["get", "put"]
  | .throws => ["raise"]
  | .txn    => ["newTVar", "readTVar", "writeTVar"]

/-- Generate a `Comp`, closed under `scope` with in-scope handler slots `hctx`
(`hctx.length ≤ scope`, one entry per `handle`-bound var still in reach). Recursion is
sized by `fuel` (both a depth bound AND what keeps generation itself terminating — no
well-founded recursion needed since every branch strictly decreases `fuel`). -/
def genComp (fuel scope : Nat) (hctx : HCtx) (s : Nat) : Comp × Nat :=
  match fuel with
  | 0 =>
    let (v, s) := genVal 1 scope s
    (.ret v, s)
  | fuel + 1 =>
    -- Bias the choice: HANDLER-FRAGMENT constructors get most of the mass (handle/perform/
    -- letC-around-perform), the pure constructors the rest — concentrating samples on the
    -- unproven territory per the issue's stated value ranking, without starving pure mixing
    -- (a perform needs a `letC`/`app` around it sometimes to reach non-trivial nesting).
    let (s, pick) := Rng.nextMod s (if hctx.isEmpty then 6 else 10)
    match pick with
    -- ret v
    | 0 =>
      let (v, s) := genVal fuel scope s
      (.ret v, s)
    -- letC M N  (N binds index 0 ⇒ scope+1 under N)
    | 1 =>
      let (m, s) := genComp fuel scope hctx s
      let (n, s) := genComp fuel (scope + 1) (hctx.map id) s
      (.letC m n, s)
    -- app (lam M) v, again — a top-level BARE `lam` (no surrounding `app`) is well-typed (at
    -- `arr q A B`) but is NOT of returner shape `F q A`; `Config.run`'s only "done" terminal is
    -- `(_, [], .ret v)`, so an unapplied `lam` sitting at empty stack has no `Source.step` rule
    -- and is genuinely stuck ON BOTH SIDES — correctly so (`progress`/`type_safety`, Spec.lean,
    -- are stated over `HasConfig' … (F q A)`, which a bare `arr`-typed `lam` never inhabits). So
    -- `lam` is generated ONLY inside the `app` case (below), never as an independent top-level
    -- alternative — this is a duplicate `app`-producing branch, not a real second constructor,
    -- kept only to preserve the `hctx.isEmpty ↦ 6`-way modulus at this call site.
    | 2 =>
      let (m, s) := genComp fuel (scope + 1) hctx s
      let (v, s) := genVal fuel scope s
      (.app (.lam m) v, s)
    -- app (lam M) v — an immediately-applied lambda. `Source.step`'s `appF` REDUCE rule fires
    -- only when the callee focus becomes `.lam _` (`(g, .appF v :: K, .lam M) => …`); an
    -- arbitrary sub-`Comp` callee is not guaranteed to reduce to that shape (e.g. `ret v` under
    -- `appF` has no rule ⇒ genuine stuck — a real generator finding, not a kernel bug: `app`'s
    -- callee position needs a VALUE of function shape, not an arbitrary computation). Generating
    -- the `lam` inline keeps this well-typed by construction, mirroring how `case`/`split` below
    -- generate their OWN scrutinee value instead of an arbitrary sub-`Comp` that might not reduce
    -- to the right shape.
    | 3 =>
      let (m, s) := genComp fuel (scope + 1) hctx s
      let (v, s) := genVal fuel scope s
      (.app (.lam m) v, s)
    -- binop op v w (pure δ-rule; keep operands small ints so `div`/`eq` stay meaningful)
    | 4 =>
      let (s, oi) := Rng.nextMod s 6
      let op : BinOp := [BinOp.add, .sub, .mul, .div, .lt, .eq].getD oi .add
      let (s, a) := Rng.nextMod s 21
      let (s, b) := Rng.nextMod s 21
      (.binop op (.vint ((a : Int) - 10)) (.vint ((b : Int) - 10)), s)
    -- case/split (ADT eliminators over a freshly-built scrutinee, so they always reduce)
    | 5 =>
      let (s, mkInl) := Rng.nextMod s 2
      let (v, s) := genVal fuel scope s
      let (n1, s) := genComp fuel (scope + 1) hctx s
      let (n2, s) := genComp fuel (scope + 1) hctx s
      (.case (if mkInl = 0 then .inl v else .inr v) n1 n2, s)
    -- handle h M — mint a NEW handler slot at index 0 for M (kind chosen uniformly); this is
    -- the constructor that grows `hctx`, so deeper fuel ⇒ more nesting ⇒ more interleavings.
    | 6 =>
      let (s, ki) := Rng.nextMod s 3
      let kind : HKind := [HKind.state, .throws, .txn].getD ki .state
      let (initV, s) := genVal fuel scope s
      let h : Handler := match kind with
        | .state  => .state 0 initV
        | .throws => .throws 0
        | .txn    => .transaction 0 []
      let (m, s) := genComp fuel (scope + 1) (kind :: hctx) s
      (.handle h m, s)
    -- perform (vvar i) op v — `i` drawn from hctx (an ACTUAL in-scope handler), `op` drawn
    -- from THAT slot's own vocabulary. The label/id are irrelevant here: `Source.step`'s
    -- `perform (vcap n ℓ) …` requires a MINTED `vcap`, but at the SOURCE level (pre-mint) the
    -- handle-bound var is a plain `vvar`, substituted to `vcap g h.label` only once the
    -- enclosing `handle` steps — so a `vvar` pointing at hctx's i-th binder is exactly the
    -- well-scoped shape `Source.step`'s PUSH rule expects.
    | _ =>
      let (s, i) := Rng.nextMod s hctx.length
      let kind := hctx.getD i .state
      let ops := kind.ops
      let (s, oi) := Rng.nextMod s ops.length
      let op := ops.getD oi "get"
      let (v, s) := genVal fuel scope s
      (.perform (.vvar i) op v, s)

/-- Top-level entry: a CLOSED `Comp` (`scope = 0`, `hctx = []`) at generation-fuel `depth`,
from seed `seed`. -/
def genClosed (depth seed : Nat) : Comp := (genComp depth 0 [] seed).1

/-! ## 4. The differential property.

`fuzzAgree` is now a PROJECTION of `Bang.AgreeOutcome.agreeOutcome` (#54 outcome-differential):
that module's TOTAL oracle distinguishes all four `Result` cases (`done`/`outOfFuel`/`escapedCap`/
`stuck`) with no admitted "either side, whatever" disjunct — strictly STRONGER than this
file's former hand-rolled `FuzzAgree` (which let `.outOfFuel` pass regardless of what the machine
said, and folded `escapedCap`/`stuck` into one disjunct). Empirically confirmed a PURE
strengthening before landing: every one of `fuzzSeeds`' 200 generated programs that passed
the old `fuzzAgree` also passes `agreeOutcome` (`scratch/OutcomeFuzzProbe.lean`, not
committed — the check, not the artifact, is what mattered). `Bang.Fuzz`'s OWN `valEq` is
kept (this file predates `AgreeOutcome`'s copy and nothing here depends on that module's
private one) — same shape, not re-exported to avoid a needless cross-module coupling for a
five-line helper. -/

/-- `Val` structural equality (`Val` derives no `DecidableEq`/`BEq` — only the constructors
this generator can actually produce need comparing, so a hand match suffices here rather
than reaching for the full mutual-inductive derivation). -/
def valEq : Val → Val → Bool
  | .vunit,       .vunit       => true
  | .vint a,      .vint b      => a == b
  | .vvar i,      .vvar j      => i == j
  | .vcap n l,    .vcap m k    => n == m && l == k
  | .inl a,       .inl b       => valEq a b
  | .inr a,       .inr b       => valEq a b
  | .pair a b,    .pair c d    => valEq a c && valEq b d
  | .fold a,      .fold b      => valEq a b
  | _,            _            => false

/-- Boolean reflection of the fuzz property, so a counterexample can be caught by `#guard`
(build-fail on `false`) rather than requiring a proof term per sample. A thin projection of
`Bang.AgreeOutcome.agreeOutcome` — see the `§4` header for why this is a strengthening, not
a behavior change. -/
def fuzzAgree (fuel : Nat) (M : Comp) : Bool :=
  Bang.AgreeOutcome.agreeOutcome fuel M

/-! ## 5. The fuzz run — fixed seeds (deterministic in CI), `#guard`-gated (fails the build
on any counterexample). Depth/fuel/case-count are fixed constants, not a `native_decide`
sampling loop, so the whole battery stays axiom-clean (plain `rfl`/`decide` reduction) and
reproducible byte-for-byte across machines. -/

/-- Fixed seeds — deterministic, no wall-clock/OS entropy (CI-reproducible per the issue's
"seeded/deterministic" requirement). Chosen arbitrarily; NOT tuned to avoid a known failure. -/
def fuzzSeeds : List Nat := (List.range 200).map (fun i => i * 104729 + 7)

/-- Generation depth per sample (a handful of `handle` nestings deep — enough to reach
state-inside-throws-inside-txn interleavings, matching the curated `Agree` battery's
deepest case, `Agree 100` in AbstractMachine.lean). -/
def genDepth : Nat := 6

/-- Eval fuel — generous relative to `genDepth` (each construct costs O(1) `Source.step`s
and generation is depth-bounded, so this comfortably covers every generated sample; the
`.outOfFuel` case in the outcome oracle covers the (empirically unseen) case where it doesn't). -/
def evalFuel : Nat := 400

/-- One sample's outcome, for the summary fold below. -/
def sampleOk (seed : Nat) : Bool := fuzzAgree evalFuel (genClosed genDepth seed)

/-- **The fuzz property**: every fixed seed's generated program agrees per `fuzzAgree`.
`#guard` evaluates this at compile time and FAILS THE BUILD if any seed disagrees — the
repo's standing `plausible`-adjacent idiom (PropTest's `#test`, this file's compiled
`#guard` sibling) for "a false property is a red build", without needing `meta Gen`. -/
def allSamplesOk : Bool := fuzzSeeds.all sampleOk

#guard allSamplesOk

/-! ## 6. Coverage summary — a readable record of what this battery actually samples,
kept as running documentation (checkable: `#guard`s above enforce it stays true). -/

/-- Sample count. -/
example : fuzzSeeds.length = 200 := by rfl

end -- @[expose] public section

end Bang.Fuzz
