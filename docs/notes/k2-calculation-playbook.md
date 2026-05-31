# K2 calculation — proof playbook

> Hard-won technique for the Bahr–Hutton calculation in Lean. Read this before
> proving the **next** increment (thunk/`$`force + CBN → `if` → effects): each one
> re-runs the same shapes. Companion to **ADR-0009** (method/staging) and
> **ADR-0010** (the higher-order proof). The proven artifacts live in
> `effectrow-oracle/oracle-lean/Bang/{Calc,CalcHO}.lean`.

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
