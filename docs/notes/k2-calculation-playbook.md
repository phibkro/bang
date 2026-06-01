# K2 calculation — proof playbook

> Hard-won technique for the Bahr–Hutton calculation in Lean. Read this before
> proving the **next** increment: the equality-sim shapes (K2 core → effects →
> compositions) re-run constantly, and the **K3 reification frontier** (ADR-0015,
> last section) is a *different* proof shape — read it before touching the
> resumption residual. Companion to **ADR-0009** (method/staging), **ADR-0010**
> (the higher-order proof) and **ADR-0015** (reification). Proven artifacts:
> `effectrow-oracle/oracle-lean/Bang/{Calc,CalcHO,CalcReify,CalcReifyRef,CalcReifySim}.lean`.

## The three transferable insights

### 1. Target a concrete `some r`, not `exec F c …` (the fuel-alignment key)

The textbook *total*-machine statement is

```
exec (compile e c) s = exec c (eval e :: s)        -- both sides run the continuation c
```

With a **fuel-bounded** `exec` this is unprovable as-is: the left side consumes
fuel running `compile e` *before* it reaches `c`, so the two sides hit `c` with
different fuel and the equality fails. Don't fight it. Restate forward, to a
concrete result:

```
eval fe env e = some v →
  ∀ c s F r, exec F c env (v :: s) = some r → ∃ F', exec F' (compile e c) env s = some r
```

Now the target is a fixed `some r`, and **fuel monotonicity** (`exec_mono`) lets
you bump every sub-fuel to a common value. The corollary (`compile_correct`) takes
`c = []`, `s = []`, `F = 1`, `r = [v]`. This single reframing is what unblocked
the whole higher-order proof.

### 2. Share the value representation → equality, not a logical relation

Higher-order compiler correctness is usually painful because the *denotational*
closure and the *machine* closure differ, forcing a step-indexed logical relation.
We sidestep it: `Value = vint Int | vclo Src Env` is **shared** by `eval` and the
machine (the closure stores the *source* body + env; `APP` compiles it on demand).
So `lam`/`app` correctness stays a plain **equality**. Keep this discipline as the
language grows — pick one value type both sides produce.

### 3. Structural recursion on fuel — drop `termination_by`

`eval`/`exec` recurse on `f` where the input is `f+1`, so they are **structurally
recursive on the fuel argument**. Writing an explicit `termination_by fuel` forces
WF-recursion, whose equation lemmas *don't* unfold under `simp`/`rw` (you'll see
"`simp` made no progress"). Omit `termination_by` → definitional unfolding →
`simp only [exec]` / `rw [exec]` work in proofs. Same behaviour, provable.

## Tactic patterns that worked

**Fuel monotonicity (`exec_succ`)** — the awkward case is `code = i :: c`, an
8-way instruction match with nested stack/option matches. The recipe:

```lean
simp only [exec] at h ⊢            -- both sides become `match i, env, s with …`
split at h <;>                     -- `split at h ⊢` is NOT supported; split h, scrutinees refine globally
  first
  | exact ih _ _ _ _ h             -- simple recursive arms (goal reduces by defeq)
  | simp at h                      -- stuck arms: h : none = some r
  | (split at h <;> first | exact ih _ _ _ _ h | simp at h)   -- nested match (LOOKUP on env[i]?)
  | skip                           -- leave the APP arm
all_goals (                        -- APP: the nested callee run
  rename_i va body cenv s'         -- name the pattern vars split introduced (count by the error)
  cases hb : exec f (compile body []) (va :: cenv) [] with
  | none => rw [hb] at h; simp at h
  | some bs => cases bs with
    | nil => rw [hb] at h; simp at h
    | cons rv rest => rw [hb] at h; rw [ih _ _ _ _ hb]; exact ih _ _ _ _ h)
```

Then `exec_mono` follows by `Nat.le.dest` + induction (`rw [Nat.add_succ]; exact
exec_succ …`).

**The simulation (`sim`)** — `induction fe` (eval fuel); `cases e`. Per case:
- `val`/`var`/`lam`: `⟨F+1, by simp only [compile, exec, …]; exact hr⟩`.
- `add`/`mul`/`letE`/`app`: destructure `h` by `cases hx : eval fe env x` down to
  the `vint`/`vclo` shape (stuck shapes close with `simp at h`); extract the value
  with `simp only [Option.some.injEq] at h; subst h`; then **chain the IH** on
  subterms right-to-left through the derived instructions, proving each
  instruction's step with `by simp only [exec]; exact …`.
- `app` specifically: run the callee to `[v]` via the IH, then `exec_mono` both the
  callee result and the continuation `hr` up to a common fuel `G + F` before the
  `APP` step; then IH on the argument, then the function.

## Mutual semantics → mutual simulation (the CBN/`force` pattern)

When `eval` is mutually recursive with a `forceV` (call-by-name: `force`/`binop`
operands/app-function reduce to WHNF), prove **one `sim` theorem that is a
conjunction**, by induction on the shared fuel:

```lean
theorem sim : ∀ fe,
  (∀ env e v, eval fe env e = some v → ∀ c s F r, exec F c env (v::s) = some r →
     ∃ F', exec F' (compile e c) env s = some r) ∧               -- eval-sim
  (∀ v w, forceV fe v = some w → ∀ env c s F r, exec F c env (w::s) = some r →
     ∃ F', exec F' (FORCE :: c) env (v::s) = some r) := by         -- forceV-sim
  intro fe; induction fe with
  | zero => exact ⟨fun _ _ _ h => by simp [eval] at h, fun _ _ h => by simp [forceV] at h⟩
  | succ fe ih => obtain ⟨ihe, ihf⟩ := ih; refine ⟨?_, ?_⟩ ...
```

`ihe`/`ihf` are both available at `fe`. The eval-sim's `force`/`app`/`binop` cases
call `ihf` to discharge a forcing; the forceV-sim's `FORCE`-on-`vthunk` case calls
`ihe` on the thunk body. Shared `vthunk`/`vclo` keep both equalities. This landed
`CalcCBN.compile_correct` (`Bang/CalcCBN.lean`) — BANG's full pure-core kernel,
proven. Worked the first build after fixing the lemma name + one copy-paste typo.

## Effects → a two-part (ret/exc) sim + handler stack (the K3 pattern)

Calculating an effect machine (`Bang/CalcEff.lean`, general handlers + Throws,
Hutton–Wright generalised to labels) added these beyond the closure proofs:

- **Total `eval`, fuel-bounded `exec`.** Exceptions short-circuit but don't
  diverge, so `eval : Env → Src → Outcome` (`ret │ exc`) is *total/structural* —
  the spec stays clean. Only the machine needs fuel (`THROW` jumps to recovery).
- **Keep the machine structurally recursive.** A `THROW` that unwinds the handler
  stack is tempting to write as `unwind (exec f) …` (passing `exec` as a
  higher-order arg) — but that forces `termination_by`, which makes `exec`
  WF-recursive and **breaks `simp [exec]` unfolding everywhere**. Instead split out
  a *pure* finder `unwindFind : Label → Int → HStack → (… ) ⊕ Result` and make the
  `THROW` arm a **direct** recursive call `exec f rec e' s' hs'`. Structural,
  clean unfolding, and no monotonicity lemma for the unwind.
- **Two-part `sim`** (one conjunction, induction on `e`): a *ret* part (as before)
  and an *exc* part `eval env e = exc ℓ p → ∀ F r, throwOutcome F ℓ p hs = some r →
  ∃ F', exec F' (compile e c) env s hs = some r`, where `throwOutcome` is the
  `THROW` arm factored out. The `handle` case is the crux: install/pop the frame
  (`MARK`/`UNMARK`); a *caught* exception links `eval`'s recovery run to the machine
  unwinding into that frame's recovery code; a *forwarded* effect skips the frame
  in both `eval` (`if l'=lab … else`) and `unwindFind` (`if fr.label=l …`).
- **`subst` direction is unpredictable** when both sides are local vars (`lx = l`).
  To extract a sub-evaluation's `exc lx px` against the goal's `exc l p`: prefer
  **`subst lx; subst px`** (name the *cases* var to eliminate) over
  `obtain ⟨rfl,rfl⟩`/`subst h`. When you must keep a specific name, rewrite the
  goal instead (`show throwOutcome F lab e hs = some r; rw [hl, hp]; exact hu`).

## Gotchas (cost real time — don't repeat)

- **`set` is a Mathlib tactic** — the `Calc*` modules import no Mathlib (core +
  Batteries only), so `set x := … with h` is "unknown tactic". Inline the term
  (anonymous constructor `⟨…⟩`), or `let`. Also **`rec` is a reserved keyword** —
  don't name a local `rec`.
- **`if`-condition symmetry**: `unwindFind`'s `fr.label = l` unfolds to `lab = l`,
  but `by_cases hc : l' = lab` (post-`subst`) gives `hc : l ≠ lab`. Use
  `rw [if_neg (Ne.symm hc)]` / `rw [if_pos hc.symm]`.
- To expose an `if` inside a reduced `match` for `rw [if_pos/neg]`, unfold the
  scrutinee with **`simp only [hb]`** (iota-reduces), not `rw [hb]` (leaves the
  match).

- **`::` binds tighter than `+`** (prec 67 vs 65): `n + m :: s` parses as
  `n + (m :: s)` → a `HAdd Int (List Int)` instance error. Write `(n + m) :: s`.
- `Option.bind_eq_some` is **`Option.bind_eq_some_iff`** in this pin
  (`x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b`) — used to split a
  `(eval …).bind (forceV …) = some v` hypothesis.
- `List.get?` is gone in this Lean/Mathlib pin → use `l[i]?` (`getElem?`).
- `Finset.toList` is **noncomputable** here; `Finset.sort` (Finset-first arg:
  `s.sort (· ≤ ·)`) is the computable extraction. `deriving Repr` on a
  `Finset`-containing structure fails (`Finset.instRepr` is `unsafe`).
- `split at h ⊢` (both targets) is unsupported — split `h`; the shared scrutinees
  refine globally so the goal follows.
- The Lean oracle **must flush stdout** after each reply or the long-lived harness
  starves over the pipe (block-buffering). One response per line, `stdout.flush`.

## Recipe for the next increment (thunk/`$`force + call-by-name)

1. Reuse `CalcHO`'s closure machinery; the change is the **argument convention** —
   CBV evaluates args eagerly, CBN passes them as *thunks* (descriptions) forced on
   demand. Expect a thunk value (`vthunk Src Env` or similar) and a `FORCE`
   instruction to fall out of the `$e` / application cases.
2. The `sim` statement and the monotonicity lemmas carry over almost verbatim —
   re-prove `sim` with the new cases; the fuel-alignment and shared-value tricks
   above still apply.
3. Diff-test against `Bang.Eval` (which *is* call-by-name) — so unlike CBV, CBN
   should now agree with the reference even on programs with unused/divergent
   arguments, a strictly better cross-check.

## K3 addendum — composing effects with the closure core (`CalcCBNEff`, ADR-0012)

Fusing Throws into `CalcCBN` (the real K3) re-runs the shapes above but surfaced a
few new, transferable gotchas. Read these before **State over the closure core**
(the next composition) — it will hit the same ones.

- **The simulation is a *four-part* mutual conjunction.** Composing a fuel-bounded
  CBN core (`eval`/`forceV` mutual) with an effect (`ret`/`exc` two-part) gives
  **eval-ret · eval-exc · forceV-ret · forceV-exc**, proven together by induction on
  fuel. `eval`/`forceV` returns `Option Outcome` (partiality ∘ exception). The new
  content vs the two parents is only the **nested-`uncaught` re-throw** (below).
- **The new semantic axis is "forcing can raise."** `forceV` returns an `Outcome`;
  every forcing point (`$e`, both `add` operands, the app function, a `perform`
  payload) is an effect-propagation point. This is where the bug hides — exercise it
  in goldens (force-a-thunk-that-raises, effect-escapes-a-call) *and* the fuzz.
- **Nested meta-runs use an *empty* handler stack `[]`, then re-throw at the
  boundary.** `APP`/`FORCE` run `exec f (compile b []) … [] []`; if that returns
  `uncaught ℓ p`, re-throw against the **outer** `hs` via `unwindFind`. Passing the
  live `hs` into the nested run is *wrong* (a frame's recovery belongs to the outer
  stream). This is **zero-shot-only** — State (resumable) won't compose this way;
  expect to flatten into a control stack (ADR-0012 "Revisit if").
- **A `| o => o` catch-all blocks `rw`-reduction.** With `eval` written as
  `match … with | some (.ret v) => B | o => o`, `rw [hx] at h` rewrites the scrutinee
  but does **not** iota-reduce the match, so the next *dependent* scrutinee
  (`forceV vx`, which uses the binder `vx`) stays shadowed and the next `rw`/`cases`
  fails. Fix: use **`simp only [hx] at h`** (rewrites *and* reduces) for every
  productive step, and `simp [hx] at h` for the contradiction leaves. (CalcEff got
  away with plain `rw` only because its operands were *independent*.)
- **Pin `f'` before `(by omega)` in `exec_mono`/`throwExec_mono`.** The expected type
  of a `have hX : exec (G+F) … := exec_mono _ _ … hG (by omega)` does **not**
  propagate to the `f'` metavar before the `omega` runs (it sees `G ≤ ?m`). Write
  `exec_mono _ (G + F) _ _ _ _ _ hG (by omega)` to pin it.
- **Don't put `intro …` on the `=>` line if the body wraps.** For a long arm header
  (`| handle lab onRaise body => intro …`), a continuation indented *less* than
  `intro` silently truncates the tactic block ("unsolved goals" / "alternative not
  provided"). Put `intro` on its own line and indent the body consistently.
- **Build defs first, fuzz, *then* prove.** The fuzz caught an eager-int-check
  divergence in `add` (a non-int operand made `eval` stuck *before* the other
  operand's effect ran, but the machine forces both first) before any proof effort —
  the "run the real journey" payoff. Fix the definition, re-fuzz, then prove.

### State over the closure core (`CalcCBNSt`, ADR-0013) — what carried over

The same shapes again, one part lighter, and it went through **first try** by
applying the bullets above from the start:

- **A tail-resumable effect threads cleanly; the sim is *two*-part** (eval-sim,
  forceV-sim — no `exc` part). State never raises, so there's no re-throw and no
  empty-nested trick: the register just threads `st → st'` through every step,
  *including* the nested meta-runs (`exec f (compile b …) … [] st` returns `st'`,
  the caller threads it forward). This is the structural reason State doesn't force a
  machine flatten — see the effect-shape map below.
- **Returning `Option (Value × State)` adds only pair-plumbing.** `cases hx : eval …
  with | some px => obtain ⟨vx, st1⟩ := px; simp only [hx] at h`, and finish value
  cases with `simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ :=
  h`. Everything else is `CalcCBN`'s proof with a state argument threaded.
- **`runState` (the scoped handler) reuses `CalcSt`'s `ENTER`/`LEAVE`** — the body is
  compiled *inline* (not via a nested meta-run), running on the main stack with the
  outer state boxed as a `vint` below it; the body-IH uses that stack and `LEAVE`
  restores. No new technique.

**Effect shape → composition mechanism** (the map these two increments established):

| effect shape | mechanism over the closure core | module |
|--------------|---------------------------------|--------|
| zero-shot (Throws) | nested run with empty handler stack, **re-throw** at the boundary | `CalcCBNEff` (ADR-0012) |
| one-shot tail (State) | **thread** the register through the nested runs; no re-throw | `CalcCBNSt` (ADR-0013) |
| **two at once** (Throws + State) | carry **both** apparatus; the nested run returns `(Result × State)`, re-throw *carries the state* | `CalcCBNEffSt` (ADR-0014) |
| non-tail / multi-shot | **flatten** to a control stack + **reify** the continuation | deferred (ADR-0011/0012/0013) |

**Two effects at once (`CalcCBNEffSt`) — what carried over.** The proof is exactly
`CalcCBNEff`'s **four-part** sim (eval/forceV × ret/exc) with `CalcCBNSt`'s state
register threaded through every step (the result type becomes `Outcome × State`;
`throwExec` gains the throw-time state). No new technique — the union of the two
parents' proofs. Two recurring fiddly bits worth flagging: (1) the `injEq` chain on a
pair-of-Outcome gives a **left-nested** `(l'=l ∧ p'=p) ∧ st1=st'`, so destructure
`⟨⟨rfl, rfl⟩, rfl⟩`, not `⟨rfl, rfl, rfl⟩`; (2) `rfl` there eliminates the **target**
`l p st'` (the older ∀-bound vars), leaving the *cased* names alive — so a propagate
case's IH call must reference the cased names (`l' p' st1`, `lx px2 st2`, …), or use
explicit `subst` of the cased vars to keep `l p st'`.

## K3 frontier — continuation **reification** (`CalcReify`, ADR-0015)

This is the deferred bottom row of the table above — **non-tail / multi-shot
handlers** — and it is a *genuinely different proof shape* than the eight equality
sims, so it earns its own section. The machine, its construction, and the proof
arc (built across one session) are all in `Bang/CalcReify*.lean`. Read this before
attempting the remaining residual (a *resuming* clause proved generally).

### Why this one is different (the wall, stated precisely)

A general handler hands its clause the **resumption** as a first-class value,
invocable 0/1/many times. The eight prior machines all dodged this (Throws is
zero-shot, State resumes only in tail position), and the dodge let the *reference*
`eval` return a plain `Value` — which is what made every prior sim a clean
**equality** (insight #2). Reification breaks the dodge:

- **A resumption can't be a `Value`.** `vcont : (Value → …) → Value` fails Lean's
  **strict positivity**. That failure is not an obstacle to route around — it is the
  *reason reification exists*: the continuation must be made **data**
  (defunctionalized). So the machine carries an explicit `Kont = List Frame` and a
  reified resumption is a captured *prefix* of it, held in a `vcont` constructor as
  data (ADR-0015 has the representation).
- **It forces the machine to flatten.** The closure machines reduce a subterm via a
  *nested meta-`exec`*; a resumption cannot be captured across that meta-boundary. So
  `CalcReify` is a **flat** machine — one `Code` stream + an explicit handler/return
  stack `K` — not an extension of the others. `exec`'s empty-code case *returns
  through* `K`; `PERFORM` captures a `vcont` and runs the clause; `RESUME` splices.

### The four-layer validation ladder (what to build, in order)

Reification's general theorem is research-grade, so we did **not** chase one monolith.
We built a ladder of increasingly strong evidence, each rung sorry-free and
independently valuable. This staging is the transferable method for any
"research-grade" correctness goal under the project's *never-fake* rule:

1. **`rfl` demonstrators** (`CalcReify.lean`). Seven closed programs — non-tail,
   multi-shot, zero-shot, re-handling, payload — each `run … = some … := by rfl`.
   Cheap, and they pin the *intended behaviour* before any proof.
2. **Fuel monotonicity** (`exec_succ`/`exec_mono`). The bedrock every sim needs;
   explicit per-instruction case analysis (the empty-code return-through, `PERFORM`,
   `RESUME` each decrease fuel). Same shape as the prior machines'.
3. **An independent cross-check** — *empirical*, then *in-Lean*:
   - **TS CPS interpreter** (`harness/src/reify-cps.ts`): a free-monad interpreter of
     the *same* `Src` where a resumption is a **real JS closure** `(w) => Comp` — the
     representation Lean positivity forbids, hence a genuinely independent oracle.
     2k random programs/CI run (20k locally), zero disagreements. This is the "run the
     real journey" rung: it finds bugs in the splicing logic before you waste proof
     effort, and it found two (mis-stated `want` goldens) immediately.
   - **In-Lean denotational reference** (`CalcReifyRef.lean`): the *same* free monad,
     now in Lean. The positivity escape is **CBPV + a free monad**: `Comp` is the free
     monad over `perform : Int ⇝ Int`, and the resumption `Int → Comp` sits in the
     **codomain** of `perf`'s argument — a *positive* occurrence — so `Comp` passes
     positivity where `Value` cannot. Resumptions live in the env as `Entry.ek`
     closures (CBPV values), never inside a `Comp` result. `bind`/`handleC`/`eval`
     all take **fuel** (a resumed `k w` is not a structural subterm). `rfl`-validated
     against the same seven demonstrators. This is the object the bisimulation is
     stated against — and proving it can be written at all turns ADR-0015's "a
     reference would be a second machine, no shortcut" prose into a checked artifact.
4. **The bisimulation itself** (`CalcReifySim.lean`) — `exec ∘ compile ≡ run` between
   the flat machine and the denotational reference. Proven for the pure fragment and
   the **first firing case**; the resuming case is the residual. Details next.

### The bisimulation, what's proven and the two ideas that unlocked firing

The statement reuses insight #1 (forward to a concrete `some r`, fuels aligned via
the existential `∃ F'`), but it is a **machine-vs-reference** sim, not machine-vs-its-
own-spec — the two sides are *different implementations* (defunctionalized `Kont`
vs real `Comp` closures). Layers, bottom-up:

- **Pure core** (`pure_sim`/`pure_correct`). The `val`/`add`/`var`/`let` fragment,
  with the handler stack `K` and data stack carried as **passengers** threaded
  unchanged. This is where the flat machine's new bits live (return-through-`K`,
  `BIND`/`UNBIND`). `RelVal`/`RelEnv` relate machine `Value`s to reference `Entry`s
  (int case only, so far).
- **Tie `pden` to the real reference** (`eval_pure`/`pure_correct_ref`). The
  structural denotation `pden` *is* the `ret`-fragment of `CalcReifyRef.eval`, so the
  pure core is a genuine two-implementation agreement (both `run`s yield `n`).
- **`handle` over a *pure body*** (`IsPure.handle`, `handleC_ret`). An **unfired
  handler is transparent**: a pure body never performs, so the clause is dead and
  both sides yield the body's value. This brings the `INSTALL` instruction and the
  return-through-a-handler-frame path into the proof *without* needing `vcont ↔ ek`.
- **The first ∀-quantified FIRING theorem** (`fire_agree`). For any pure payload `e`
  and any pure **non-resuming** `clause`, machine and reference agree on `handle
  clause (perform e)` — the clause genuinely runs with the captured continuation
  (zero-shot / payload-threading). **Two ideas made it provable, both transferable:**

  1. **An environment-independent structural fuel bound `fuelOf : Src → Nat`** (not an
     opaque `∃ F`). The reference's resumption closure *captures the ambient fuel*; an
     `∃ F` bound for the clause could then secretly depend on the resumption — a
     **circularity**. But the fuel a pure clause needs is a *structural number* of its
     term, independent of the environment. Restating `eval_pure` as `∀ f ≥ fuelOf e`
     breaks the loop. (General lesson: when a fuel witness must survive being placed
     under a fuel-capturing closure, make the witness *structural*, not existential.)
  2. **A *partial* value relation `RelEnv.consK`.** It relates an **opaque** machine
     `vcont` slot to a reference `ek` slot, asserting **nothing** about invoking
     them. Sound *because the clause is non-resuming* — it never reads the slot as an
     int (`relEnv_lookup` still holds: it only resolves `ev` entries; an `ek` can
     never match `some (ev n)`). This is the honest stub that the full step-indexed
     relation will replace. (General lesson: a logical relation can be introduced
     **partially** — relate-but-don't-constrain the slots a given theorem never
     observes — to land real results before the hard, fully-constrained version.)
- **In-Lean `Agree` on the *resuming* programs** `fire_agree` doesn't yet generalise.
  `run = some (vint k) ∧ CalcReifyRef.run = some k`, by `⟨rfl, rfl⟩`, for multi-shot
  (incl. triple), non-tail, re-handling. Both sides in-Lean — strictly stronger than
  the TS fuzz, covering exactly the firing behaviours the inductive proof can't reach.

- **The step-indexed relation is now *formalized* in Lean (definability greenlit).**
  The `consK` stub is replaced by a real `def RelV : Nat → Value → Entry → Prop`
  (with `RelEnvI`, `observe`, `RefK`) that carries the resumption agreement, all
  sorry-free (`CalcReifySim.lean`, the `Resuming` section). This converts ADR-0015's
  "the residual is the full step-indexed relation" *prose* into a checked artifact:
  the relation exists, Lean accepts it, and it integrates with the existing pure
  scaffolding (`relEnvI_lookup`, `bind_mono`, `relEnvI_forget`, `pure_sim_indexed`).
  What is *not* yet proven is `capture_relates` (that an actual PERFORM-capture
  *satisfies* `RelV`) and the firing theorem built on it. Four decisions made it
  definable, each a transferable lesson, each forced by a design-panel critique:
  1. **`def`, never `inductive`.** A resumption `g : Int → Comp` embedded in a
     *constructor* would sit negatively (positivity-rejected). A **`Prop`-valued
     `def`** carries no positivity obligation — `g` occurs only *applied* (`g w`),
     a positive use in a function body. (General lesson: a logical relation that
     quantifies over "continuations that themselves satisfy the relation" must be a
     recursive `def`, not an inductive — the Ahmed/Appel–McAllester step-indexed
     trick.)
  2. **Structural recursion on the index, not well-founded.** The `vcont↔ek` clause
     at `i+1` mentions `RelV` only at the *predecessor* `i` — so it is plain
     structural recursion on `Nat` (no `termination_by`/`decreasing_by`). The `∀ j ≤
     i` flavour the literature uses is recovered from the `i`-fact where needed; but
     see the downward-closure note below.
  3. **The base index keeps mismatches `False`.** Only `vcont↔ek` is vacuously `True`
     at budget `0`; `vint↔ev` stays `n=m` and every other shape stays `False` *at
     every index*. A blanket `| 0,_,_ => True` would let a `vcont` masquerade as an
     `ev n` slot at index 0 and **break `relEnv_lookup`**. (Lesson: in a step-indexed
     `def`, the budget-0 base must not collapse the *type-mismatch* cases, only the
     genuinely-recursive ones.)
  4. **`observe` is a pure head-match (no fuel).** The reference's
     `eval`/`handleC`/`bind` are *eager* and return a fully-formed `Comp` (only
     `perf`-binder bodies stay delayed, which a final observation never enters), so
     `g w = handleC fuel (k w) clause cEnv` is already a value — observing its head
     is exact. This kills the "CompObs reintroduces a fuel quantifier" objection for
     *this* reference. The RESUME splice config in `RelV` is copied **literally** from
     `CalcReify.lean:141-143` (`retEnv := <resume-site env>` in *both* spliced
     frames) — the single most-mis-quoted detail.

  Bonus simplification: with `RelV` carrying the agreement, the old *separate*
  `consK` constructor collapses into `cons` (one construct per problem) — `RelEnvI`
  is just `nil`/`cons`.

**Three ∀-quantified *resuming* firing theorems are now proven** (sorry-free, by
**direct inside-out construction** — they dodge the `RelV`-invocation crux because
the resumed continuation stays pure, so its result is an integer, index-free):
- **`fire_resume_tail`** — `handle (resume (var 1) v) (perform e)` ≡ `⟦v⟧` (tail
  resume, *empty* captured continuation). First ∀-quantified theorem where the
  resumption is genuinely invoked.
- **`fire_resume_nontail_body`** — `handle (resume (var 1) v) (add (perform e) rest)`
  ≡ `⟦v⟧ + ⟦rest⟧` (non-tail body, *non-empty* captured continuation `compile rest
  [ADD]` — the splice runs real captured code). The 1007 demonstrator, ∀-general.
- **`fire_multishot`** — `handle (add (resume@1 v1) (resume@1 v2)) (perform e)` ≡
  `⟦v1⟧ + ⟦v2⟧` (the resumption invoked **twice** — the signature reification
  capability; the demonstrator `7+20=27`). Enabled by the reusable
  `resume_empty_splice` helper (a RESUME of an empty-captured-continuation `vcont`
  hands the value to the post-RESUME code in 3 fuel steps); the first resume's pure
  frame carries the *second* resume as its continuation.

The reusable proof shapes: machine side built **inside-out** exactly like
`machine_fire` (halt → return-throughs → RESUME splice → LOOKUP/`pure_sim` v →
PERFORM → `pure_sim` e → INSTALL), with the captured `vcont`/frames as `let`s and
the recursive `clCode`-in-`kv` occurrence handled by a `rfl` head-rewrite
(`hcl_eq`) so `simp` never unfolds `clCode` *inside* `kv`. Reference side: a
`eval_*` reduction lemma (`eval_perform` / `eval_add_perform`) gives the body's
`perf p k` with a **clean** resumption (the `bind`/`eval` fuel-closures collapse
because the continuation is pure — `eval_add_perform` does this via plain `simp
[bind, eval_pure-as-rewrite]`, no `funext`), then `handleC`+clause unfolds mirror
`ref_fire`. Control eval-unfolding with `rfl`-`have`s for single steps — `simp only
[eval]` over-unfolds, but it's *safe* on a term whose `Src` argument is a variable
(it can't reduce an opaque `eval f env v`).

**The residual, stated sharply:** the cases the **direct construction does not yet
cover**, ordered by difficulty:
- **non-tail *clause*** (`add (resume@1 v) rest2`) and **multi-shot × non-empty
  captured continuation** (the full 2027: resume twice *and* each re-runs a `+rest`
  body) — still one-shot-of-pure-resumed leaves, provable by the *same* direct
  construction (longer chains: the RESUME pure-frame `retCode` carries the clause's
  own `+ rest2`; the captured continuation is `compile rest [ADD]` rather than `[]`,
  so `resume_empty_splice` is replaced by an explicit `pure_sim`-over-the-captured-
  continuation step as in `machine_fire_resume_nontail`).
- **deep / re-handling** (the resumed continuation *itself performs*) — the genuine
  frontier. **Correction to an earlier claim:** deep re-handling does *not*
  intrinsically require `RelV`. The distinction that actually matters:
  - **(A) fixed control-flow skeleton, ∀-general over pure subterms** — e.g.
    `handle (resume@1 v) (add (perform e1) (perform e2))` for *all* pure `e1,e2,v`.
    Because the language has **no recursion/loops/λ**, every closed program's
    *firing count is statically bounded by its skeleton*. So even a deep skeleton is
    **direct-constructible**: a longer inside-out chain with one fire→resume cycle
    *per* perform, the re-fire happening under the re-installed handler frame `frH`
    that the previous splice pushed. The reference mirrors this: `eval` of the body
    is a *nested* `perf` (`perf p1 (fun w⇒ perf p2 (fun w'⇒ ret (w+w')))`), and
    `handleC` fires once per `perf` layer, each `res` closure itself performing and
    re-firing `handleC`. **This is the deep mechanism, and it is reachable now.**
  - **(B) ∀-general over *all* `Src`** (the full `exec ∘ compile ≡ run` for every
    program) — *this* is what needs the inductive bisimulation and `RelV`'s
    agreement (`capture_relates`), because the skeleton is no longer fixed so the
    firing count is unbounded-in-the-quantifier. This is the research-grade core; the
    formalized `RelV` is built for it.

  Caveat for (A) — the clause is evaluated once **per fire**, in a *different* env
  each time (payload `p1` then `p2`), so a clause that reads the payload resumes with
  *different* values per fire: the result is `w1 + w2` (with `wᵢ = ⟦v⟧` under payload
  `pᵢ`), collapsing to `2⟦v⟧` only when `v` ignores the payload.

  Two findings still sharpen where **(B)**'s difficulty is:

- **The frozen-fuel crux only bites on a *performing* resumed continuation.** The
  reference's `res w = handleC fuel (k w) clause cEnv` captures the ambient `fuel`;
  the worry (critiques) is that no structural bound (à la `fuelOf`) controls it.
  But this only matters when `k w` *itself performs* (deep re-handling) — then
  raising fuel changes the `perf` continuation and you need reference *perf-outcome*
  monotonicity, which is itself bisimulation-shaped (the genuine paper-grade core).
  For the **one-shot / pure-resumed-body fragment** (incl. the headline non-tail
  `handle (add (resume@1 7) 100) (add (perform 5) 1000)`), `k w` is *pure*, so
  `res w = handleC f (ret …) clause = ret …` via `handleC_ret` — **no monotonicity
  needed**. So the right next milestone is that fragment: it exercises the splice +
  `RelK` + `observe` end-to-end while dodging the crux.
- **Naive `RelV` downward-closure (`j ≤ i → RelV i → RelV j`) is contravariantly
  blocked, and is *not needed*.** Lowering the outer index would require upgrading
  the contravariant `RelK` hypothesis from index `j` to `i` (i.e. `RelV j → RelV i`,
  the wrong direction). Don't chase it. The deep case instead uses the main
  induction's IH **at the predecessor index** directly, with the `RelK` hypothesis
  at the *matching* index — so the relation as-defined is sufficient without a
  monotonicity lemma.

### Reification gotchas (cost real time)

- **`rec` is a Lean keyword** — don't name a binder `rec` (rename `recov`). Structure
  literals `{ field := … }` can hit parse issues in some positions; `Frame.mk …` is a
  reliable fallback.
- **`DecidableEq` deriving fails on a `List Instr`-recursive constructor** (`INSTALL`
  holds `List Instr`). Don't derive it — use `by rfl` for `Decidable`-shaped goals on
  closed terms; `native_decide` is unavailable without the instance.
- **`let`-bound frames don't auto-unfold under `simp [exec]`.** A `let frN : Frame :=
  …` in a proof needs `simp [exec, frN]` (name the let) to reduce a return-through-`frN`
  step. Easy to miss — the goal stalls on `exec 1 frN.retCode …`.
- **A firing reduction is built inside-out.** `machine_fire` constructs the `exec`
  chain from the clause's halt outward: clause-halts-via-`pure_sim` → `PERFORM` fires
  (captures the `vcont`, prepends `[payload, kont]` to the env) → compile-`e`-via-
  `pure_sim` pushes the payload → `INSTALL` pushes the frame. Each step is a `have
  hX : exec (F+1) … = some r := by simp only [exec]; exact h_prev`.
- **Process note (environment, not Lean):** this arc hit a badly *lagged shell output
  buffer* — `lake build`/`git` results arrived several tool-calls late, and trusting a
  stale "success" led to committing a file that didn't compile (twice). The fix that
  restored reliability: **nonce-tagged, single-command verification** — `lake build
  > /tmp/x 2>&1; echo "NONCE-1234 RC=$? errs=$(grep -c error /tmp/x)"` — so each result
  is unambiguously from *this* run. Never commit a proof on a build result you can't
  tie to the current file state; a `sorry`-free claim demands a current-run RC=0.
