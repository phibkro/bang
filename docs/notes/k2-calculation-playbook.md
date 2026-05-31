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

## Gotchas (cost real time — don't repeat)

- **`::` binds tighter than `+`** (prec 67 vs 65): `n + m :: s` parses as
  `n + (m :: s)` → a `HAdd Int (List Int)` instance error. Write `(n + m) :: s`.
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
