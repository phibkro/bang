import Bang.CalcReify
import Bang.CalcReifyRef

/-!
# Toward the reification bisimulation: the pure core

ADR-0015's open theorem is `exec ∘ compile ≡ run` for `CalcReify`, a
machine/interpreter **bisimulation** relating the flat machine's defunctionalized
`Kont` to the reference's real `Comp` continuations (`CalcReifyRef`). This file
starts that proof from the bottom: the **pure core** — the cases of the induction
that involve no effect (`val`/`add`/`var`/`let`). These are the base every
effect case rests on, and they already exercise the genuinely-new bits of *this*
machine vs the prior ones: a flat `Code` stream with the handler stack `K` carried
as a passenger, return-through-`K` on empty code, and `BIND`/`UNBIND` for `let`.

The statement is the continuation-passing simulation of Bahr–Hutton (cf.
`CalcCBN.sim`): if the continuation `c` succeeds with the value pushed, then
`compile e c` succeeds with the same result — with the handler stack `K` and the
rest of the data stack `s` universally quantified and threaded unchanged. We pin
the pure denotation with a structural evaluator `pden` (no fuel: pure terms are
strongly normalising); `eval_pure`/`pure_correct_ref` below prove `pden` is
exactly the `ret`-fragment of the real reference `CalcReifyRef.eval`, so the pure
core is a genuine machine-vs-reference agreement, not a parallel definition.

**Scope / honesty:** this file proves only the pure fragment. The effect cases
(`perform`/`handle`/`resume`) need the value relation `vcont ↔ ek` — a
step-indexed logical relation saying a defunctionalized resumption behaves like
the reference's `Int → Comp` closure — which is the research-grade residual and is
*not* attempted here. This file is `sorry`-free: it asserts only what it proves.
-/

namespace Bang.CalcReifySim

open Bang.CalcReify
open Bang.CalcReifyRef (Comp Entry REnv)

/-- The pure fragment of `Src`. -/
inductive IsPure : Src → Prop where
  | val  : IsPure (.val n)
  | var  : IsPure (.var i)
  | add  : IsPure a → IsPure b → IsPure (.add a b)
  | letE : IsPure e1 → IsPure e2 → IsPure (.letE e1 e2)

/-- Structural pure denotation: `none` on effects, unbound vars, or ill-typed
operands. On the pure fragment this is total (returns `some`). -/
def pden (renv : REnv) : Src → Option Int
  | .val n      => some n
  | .var i      => match renv[i]? with
                   | some (.ev n) => some n
                   | _            => none
  | .add a b    => match pden renv a, pden renv b with
                   | some x, some y => some (x + y)
                   | _,      _      => none
  | .letE e1 e2 => match pden renv e1 with
                   | some v => pden (.ev v :: renv) e2
                   | none   => none
  | _           => none

/-- Value relation (int case only — the `vcont ↔ ek` case is the open residual). -/
inductive RelVal : Value → Entry → Prop where
  | int (n : Int) : RelVal (.vint n) (.ev n)

/-- Environment relation: pointwise `RelVal`. -/
inductive RelEnv : Env → REnv → Prop where
  | nil  : RelEnv [] []
  | cons : RelVal v e → RelEnv vs es → RelEnv (v :: vs) (e :: es)

/-- A related lookup: if envs are related and the reference finds `ev n` at `i`,
the machine finds `vint n` at `i`. -/
theorem relEnv_lookup {env : Env} {renv : REnv} (h : RelEnv env renv) :
    ∀ {i : Nat} {n : Int}, renv[i]? = some (Entry.ev n) → env[i]? = some (Value.vint n) := by
  induction h with
  | nil => intro i n hi; simp at hi
  | cons hv _ ih =>
    intro i n hi
    cases i with
    | zero => cases hv with
      | int m => simpa using hi
    | succ j => simp only [List.getElem?_cons_succ] at hi ⊢; exact ih hi

/-- **The pure core of the bisimulation.** For a pure term whose structural
denotation is `n`, compiling it in front of any continuation `c` simulates pushing
`n` and running `c` — with the data stack `s` and handler stack `K` threaded
unchanged. Proven by structural induction on the term; the continuation-passing
form threads exact fuels through the existential. -/
theorem pure_sim : ∀ (e : Src), IsPure e → ∀ {renv : REnv} {env : Env}, RelEnv env renv →
    ∀ {n : Int}, pden renv e = some n →
    ∀ (c : Code) (s : Stack) (K : Kont) (F : Nat) (r : Value),
      exec F c env (.vint n :: s) K = some r →
      ∃ F', exec F' (compile e c) env s K = some r := by
  intro e
  induction e with
  | val m =>
    intro _ renv env _ n hp c s K F r hr
    simp only [pden] at hp; obtain rfl := Option.some.inj hp
    exact ⟨F + 1, by simp only [compile, exec]; exact hr⟩
  | var i =>
    intro _ renv env henv n hp c s K F r hr
    simp only [pden] at hp
    cases hri : renv[i]? with
    | none => rw [hri] at hp; simp at hp
    | some entry => cases entry with
      | ek f => rw [hri] at hp; simp at hp
      | ev m =>
        rw [hri] at hp; simp only [Option.some.injEq] at hp; subst hp
        have hlk : env[i]? = some (Value.vint m) := relEnv_lookup henv hri
        exact ⟨F + 1, by simp only [compile, exec, hlk]; exact hr⟩
  | add a b iha ihb =>
    intro hpure renv env henv n hp c s K F r hr
    cases hpure with
    | add hpa hpb =>
      simp only [pden] at hp
      cases ha : pden renv a with
      | none => rw [ha] at hp; simp at hp
      | some x => cases hb : pden renv b with
        | none => rw [ha, hb] at hp; simp at hp
        | some y =>
          rw [ha, hb] at hp; simp only [Option.some.injEq] at hp; subst hp
          have hadd : exec (F + 1) (Instr.ADD :: c) env (.vint y :: .vint x :: s) K = some r := by
            simp only [exec]; exact hr
          obtain ⟨Fb, hFb⟩ := ihb hpb henv hb (Instr.ADD :: c) (.vint x :: s) K (F + 1) r hadd
          obtain ⟨Fa, hFa⟩ := iha hpa henv ha (compile b (Instr.ADD :: c)) s K Fb r hFb
          exact ⟨Fa, by simpa only [compile] using hFa⟩
  | letE e1 e2 ih1 ih2 =>
    intro hpure renv env henv n hp c s K F r hr
    cases hpure with
    | letE hp1 hp2 =>
      simp only [pden] at hp
      cases h1 : pden renv e1 with
      | none => rw [h1] at hp; simp at hp
      | some v =>
        rw [h1] at hp
        have henv2 : RelEnv (.vint v :: env) (.ev v :: renv) := .cons (.int v) henv
        have hunbind : exec (F + 1) (Instr.UNBIND :: c) (.vint v :: env) (.vint n :: s) K = some r := by
          simp only [exec]; exact hr
        obtain ⟨F2, hF2⟩ := ih2 hp2 henv2 hp (Instr.UNBIND :: c) s K (F + 1) r hunbind
        have hbind : exec (F2 + 1) (Instr.BIND :: compile e2 (Instr.UNBIND :: c)) env (.vint v :: s) K = some r := by
          simp only [exec]; exact hF2
        obtain ⟨F1, hF1⟩ := ih1 hp1 henv h1 (Instr.BIND :: compile e2 (Instr.UNBIND :: c)) s K (F2 + 1) r hbind
        exact ⟨F1, by simpa only [compile] using hF1⟩
  | perform e1 _ => intro hpure _ _ _ _ _ _ _ _ _ _ _; cases hpure
  | handle cl bd _ _ => intro hpure _ _ _ _ _ _ _ _ _ _ _; cases hpure
  | resume k v _ _ => intro hpure _ _ _ _ _ _ _ _ _ _ _; cases hpure

/-- **Pure correctness corollary.** A closed pure program whose denotation is `n`
halts on the machine with `vint n`. -/
theorem pure_correct {e : Src} (hpure : IsPure e) {n : Int} (hp : pden [] e = some n) :
    ∃ F, run F e = some (.vint n) := by
  obtain ⟨F, hF⟩ := pure_sim e hpure (renv := []) (env := []) RelEnv.nil hp [] [] [] 1 (.vint n)
    (by simp [exec])
  exact ⟨F, hF⟩

/-! ## Tying `pden` to the real reference

`pden` is not an ad-hoc stand-in: on the pure fragment it is exactly what the
denotational reference `CalcReifyRef.eval` computes (a `ret`), so `pure_sim`/
`pure_correct` above are genuinely statements about the reference, not a parallel
definition. The proof is the standard fuel-monotone form (`∀ f ≥ F`), so the two
sides' fuels can always be aligned. -/

/-- `bind` consumes a `ret` in one step. -/
theorem bind_ret (k : Nat) (x : Int) (g : Int → Comp) :
    CalcReifyRef.bind (k + 1) (.ret x) g = g x := by
  simp [CalcReifyRef.bind]

/-- On a pure term, `CalcReifyRef.eval` returns `ret (pden …)` once it has enough
fuel — fuel-monotone in the standard `∀ f ≥ F` form. -/
theorem eval_pure : ∀ (e : Src), IsPure e → ∀ {renv : REnv} {n : Int}, pden renv e = some n →
    ∃ F, ∀ f, F ≤ f → CalcReifyRef.eval f renv e = .ret n := by
  intro e
  induction e with
  | val m =>
    intro _ renv n hp
    simp only [pden] at hp; obtain rfl := Option.some.inj hp
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    simp only [CalcReifyRef.eval]
  | var i =>
    intro _ renv n hp
    simp only [pden] at hp
    cases hri : renv[i]? with
    | none => rw [hri] at hp; simp at hp
    | some entry => cases entry with
      | ek f => rw [hri] at hp; simp at hp
      | ev m =>
        rw [hri] at hp; simp only [Option.some.injEq] at hp; subst hp
        refine ⟨1, fun f hf => ?_⟩
        obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
        simp only [CalcReifyRef.eval, hri]
  | add a b iha ihb =>
    intro hpure renv n hp
    cases hpure with
    | add hpa hpb =>
      simp only [pden] at hp
      cases ha : pden renv a with
      | none => rw [ha] at hp; simp at hp
      | some x => cases hb : pden renv b with
        | none => rw [ha, hb] at hp; simp at hp
        | some y =>
          rw [ha, hb] at hp; simp only [Option.some.injEq] at hp; subst hp
          obtain ⟨Fa, hFa⟩ := iha hpa ha
          obtain ⟨Fb, hFb⟩ := ihb hpb hb
          refine ⟨Fa + Fb + 2, fun f hf => ?_⟩
          obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
          have hfa : Fa ≤ f' := by omega
          have hfb : Fb ≤ f' := by omega
          obtain ⟨f'', rfl⟩ : ∃ k, f' = k + 1 := ⟨f' - 1, by omega⟩
          simp only [CalcReifyRef.eval, hFa _ hfa, hFb _ hfb, bind_ret]
  | letE e1 e2 ih1 ih2 =>
    intro hpure renv n hp
    cases hpure with
    | letE hp1 hp2 =>
      simp only [pden] at hp
      cases h1 : pden renv e1 with
      | none => rw [h1] at hp; simp at hp
      | some v =>
        rw [h1] at hp
        obtain ⟨F1, hF1⟩ := ih1 hp1 h1
        obtain ⟨F2, hF2⟩ := ih2 hp2 hp
        refine ⟨F1 + F2 + 2, fun f hf => ?_⟩
        obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
        have hf1 : F1 ≤ f' := by omega
        have hf2 : F2 ≤ f' := by omega
        obtain ⟨f'', rfl⟩ : ∃ k, f' = k + 1 := ⟨f' - 1, by omega⟩
        simp only [CalcReifyRef.eval, hF1 _ hf1, bind_ret]
        exact hF2 _ hf2
  | perform e1 _ => intro hpure _ _ _; cases hpure
  | handle cl bd _ _ => intro hpure _ _ _; cases hpure
  | resume k v _ _ => intro hpure _ _ _; cases hpure

/-- **The pure core, against the real reference.** For a closed pure program both
the machine (`CalcReify.run`) and the denotational reference (`CalcReifyRef.run`)
agree: each yields `n`. This is the pure spine of `exec ∘ compile ≡ run` as a
genuine two-implementation theorem. -/
theorem pure_correct_ref {e : Src} (hpure : IsPure e) {n : Int} (hp : pden [] e = some n) :
    (∃ F, run F e = some (.vint n)) ∧ (∃ G, CalcReifyRef.run G e = some n) := by
  refine ⟨pure_correct hpure hp, ?_⟩
  obtain ⟨G, hG⟩ := eval_pure e hpure (renv := []) hp
  exact ⟨G, by simp only [CalcReifyRef.run, hG G (Nat.le_refl G)]⟩

end Bang.CalcReifySim
