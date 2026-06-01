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

**Scope / honesty:** the inductive `pure_sim`/`eval_pure` cover the pure fragment
(now incl. `handle` over a pure body — an unfired handler is transparent). Beyond
that, `fire_agree` proves the **first ∀-quantified *firing* result**: for any pure
payload `e` and pure non-resuming `clause`, machine and reference agree on `handle
clause (perform e)` — the clause genuinely runs with the captured continuation.
The key was the *environment-independent* structural fuel bound `fuelOf`, which
breaks the circularity the reference's fuel-capturing resumption closure would
otherwise create; the partial `RelEnv.consK` constructor relates an opaque machine
`vcont` slot to a reference `ek` slot (sound here because the clause never reads
it). The remaining residual is a **resuming** clause — the full step-indexed
`vcont ↔ ek` relation, where the two resumptions must agree *when invoked*. This
file is `sorry`-free: it asserts only what it proves.
-/

namespace Bang.CalcReifySim

open Bang.CalcReify
open Bang.CalcReifyRef (Comp Entry REnv)

/-- The **effect-free** fragment of `Src` — meaning no effect is ever *triggered*,
not merely "no `perform` syntactically". A `handle clause body` with a pure body
is itself pure: the body never performs, so the handler never fires and the clause
(whatever it is) is dead — an *unfired handler is transparent*. This is the natural
stepping stone into the effect cases: it exercises the machine's `INSTALL`
instruction and the return-through-a-handler-frame path, without yet needing the
`vcont ↔ ek` relation (the handler is installed but its clause is never run). -/
inductive IsPure : Src → Prop where
  | val    : IsPure (.val n)
  | var    : IsPure (.var i)
  | add    : IsPure a → IsPure b → IsPure (.add a b)
  | letE   : IsPure e1 → IsPure e2 → IsPure (.letE e1 e2)
  | handle : IsPure body → IsPure (.handle clause body)

/-- Structural pure denotation: `none` on effects, unbound vars, or ill-typed
operands. On the pure fragment this is total (returns `some`). A `handle` over a
pure body denotes the body's value — the handler is never triggered. -/
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
  | .handle _ body => pden renv body
  | _           => none

/-- Value relation (int case only — the `vcont ↔ ek` case is the open residual). -/
inductive RelVal : Value → Entry → Prop where
  | int (n : Int) : RelVal (.vint n) (.ev n)

/-- Environment relation. `cons` relates `ev`/`vint` slots; **`consK`** relates a
**resumption slot** — an arbitrary machine value (a `vcont`) to a reference `ek`
closure. The latter is the partial `vcont ↔ ek` relation: it deliberately says
*nothing* about how the two resumptions behave when invoked (that is the open
step-indexed residual), only that the slot may be ignored. It is sound for the
present results precisely because the clauses we prove about are **non-resuming**
(`IsPure`): they never read the slot as an integer, so its contents are irrelevant.
`relEnv_lookup` still holds because it only ever resolves `ev` entries — an `ek`
slot can never match `some (ev n)`. -/
inductive RelEnv : Env → REnv → Prop where
  | nil   : RelEnv [] []
  | cons  : RelVal v e → RelEnv vs es → RelEnv (v :: vs) (e :: es)
  | consK : (mv : Value) → (g : Int → Comp) → RelEnv vs es → RelEnv (mv :: vs) (Entry.ek g :: es)

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
  | consK mv g _ ih =>
    intro i n hi
    cases i with
    | zero => simp at hi   -- some (ek g) = some (ev n) is impossible
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
  | handle clause body _ ihbody =>
    intro hpure renv env henv n hp c s K F r hr
    cases hpure with
    | handle hpb =>
      simp only [pden] at hp        -- hp : pden renv body = some n
      -- INSTALL pushes this handler frame; running the pure body never fires it.
      -- When the body returns `vint n`, the value flows THROUGH the frame to `c`.
      have hframe : exec (F + 1) [] env (.vint n :: s)
          ({ clause := some (compile clause [], env), retCode := c, retEnv := env, retStack := s } :: K)
            = some r := by
        simp only [exec]; exact hr
      obtain ⟨Gb, hGb⟩ := ihbody hpb henv hp [] s
        ({ clause := some (compile clause [], env), retCode := c, retEnv := env, retStack := s } :: K)
        (F + 1) r hframe
      have hinstall : exec (Gb + 1) (Instr.INSTALL (compile clause []) c :: compile body []) env s K
          = some r := by
        simp only [exec]; exact hGb
      exact ⟨Gb + 1, by simpa only [compile] using hinstall⟩
  | perform e1 _ => intro hpure _ _ _ _ _ _ _ _ _ _ _; cases hpure
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

/-- `handleC` over a `ret` value is transparent: an unfired handler returns the
body's value. (`handleC` matches on its computation argument; on `.ret` it ignores
the clause entirely.) -/
theorem handleC_ret (k : Nat) (x : Int) (clause : Src) (cEnv : REnv) :
    CalcReifyRef.handleC (k + 1) (.ret x) clause cEnv = .ret x := by
  simp [CalcReifyRef.handleC]

/-- A **term-structural** fuel bound: how much fuel `CalcReifyRef.eval` needs on a
pure term, computed from the term alone — *independent of the environment*. This
independence is the crux that lets the firing proof break a fuel circularity: the
reference's resumption closure captures the ambient fuel, but the fuel needed to
evaluate a pure clause under it is a fixed structural number, not a function of the
closure. -/
def fuelOf : Src → Nat
  | .val _        => 1
  | .var _        => 1
  | .add a b      => fuelOf a + fuelOf b + 2
  | .letE e1 e2   => fuelOf e1 + fuelOf e2 + 2
  | .handle _ body => fuelOf body + 2
  | _             => 1

/-- On a pure term, `CalcReifyRef.eval` returns `ret (pden …)` once it has at least
`fuelOf e` fuel — with the bound **independent of `renv`**. (The standard
fuel-monotone `∀ f ≥ F` form, but with the explicit structural `F = fuelOf e`.) -/
theorem eval_pure : ∀ (e : Src), IsPure e → ∀ {renv : REnv} {n : Int}, pden renv e = some n →
    ∀ f, fuelOf e ≤ f → CalcReifyRef.eval f renv e = .ret n := by
  intro e
  induction e with
  | val m =>
    intro _ renv n hp f hf
    simp only [pden] at hp; obtain rfl := Option.some.inj hp
    obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by simp only [fuelOf] at hf; omega⟩
    simp only [CalcReifyRef.eval]
  | var i =>
    intro _ renv n hp f hf
    simp only [pden] at hp
    cases hri : renv[i]? with
    | none => rw [hri] at hp; simp at hp
    | some entry => cases entry with
      | ek g => rw [hri] at hp; simp at hp
      | ev m =>
        rw [hri] at hp; simp only [Option.some.injEq] at hp; subst hp
        obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by simp only [fuelOf] at hf; omega⟩
        simp only [CalcReifyRef.eval, hri]
  | add a b iha ihb =>
    intro hpure renv n hp f hf
    cases hpure with
    | add hpa hpb =>
      simp only [pden] at hp
      cases ha : pden renv a with
      | none => rw [ha] at hp; simp at hp
      | some x => cases hb : pden renv b with
        | none => rw [ha, hb] at hp; simp at hp
        | some y =>
          rw [ha, hb] at hp; simp only [Option.some.injEq] at hp; subst hp
          simp only [fuelOf] at hf
          obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
          have hfa : fuelOf a ≤ f' := by omega
          have hfb : fuelOf b ≤ f' := by omega
          obtain ⟨f'', rfl⟩ : ∃ k, f' = k + 1 := ⟨f' - 1, by omega⟩
          simp only [CalcReifyRef.eval, iha hpa ha _ hfa, ihb hpb hb _ hfb, bind_ret]
  | letE e1 e2 ih1 ih2 =>
    intro hpure renv n hp f hf
    cases hpure with
    | letE hp1 hp2 =>
      simp only [pden] at hp
      cases h1 : pden renv e1 with
      | none => rw [h1] at hp; simp at hp
      | some v =>
        rw [h1] at hp
        simp only [fuelOf] at hf
        obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
        have hf1 : fuelOf e1 ≤ f' := by omega
        have hf2 : fuelOf e2 ≤ f' := by omega
        obtain ⟨f'', rfl⟩ : ∃ k, f' = k + 1 := ⟨f' - 1, by omega⟩
        simp only [CalcReifyRef.eval, ih1 hp1 h1 _ hf1, bind_ret]
        exact ih2 hp2 hp _ hf2
  | handle clause body _ ihbody =>
    intro hpure renv n hp f hf
    cases hpure with
    | handle hpb =>
      simp only [pden] at hp          -- hp : pden renv body = some n
      simp only [fuelOf] at hf
      obtain ⟨f', rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
      have hfb : fuelOf body ≤ f' := by omega
      -- eval (f'+1) (handle clause body) = handleC f' (eval f' body) clause renv
      --                                  = handleC f' (ret n) clause renv = ret n
      obtain ⟨f'', rfl⟩ : ∃ k, f' = k + 1 := ⟨f' - 1, by omega⟩
      simp only [CalcReifyRef.eval, ihbody hpb hp _ hfb, handleC_ret]
  | perform e1 _ => intro hpure _ _ _ _ _; cases hpure
  | resume k v _ _ => intro hpure _ _ _ _ _; cases hpure

/-! ## A first **firing** handler, proven generally (the `vcont ↔ ek` frontier)

The pure cases never trigger a clause. Here is the first *firing* result that is
**universally quantified over programs**, not just `rfl` on specific ones: a
`handle clause (perform e)` where `e` and `clause` are pure (the clause may read
the **payload**, but does not itself resume). The body performs once; the clause
runs with the payload; the (captured) resumption is discarded or used opaquely.

This is exactly where the `vcont ↔ ek` wall stands, and the proof shows *why* the
structural `fuelOf` was the key. The reference builds a resumption closure `res`
that **captures the ambient fuel**; naively, the fuel needed to evaluate the clause
*under* `res` could depend on `res`, a circularity. But `eval_pure`'s bound is
`fuelOf clause` — computed from the term alone, independent of the environment — so
`res` is irrelevant to how much fuel the clause needs. The clause's denotation is
likewise independent of the resumption slot (`pden` never reads inside an `ek`),
which we record by quantifying the clause hypothesis over **all** `g`. -/

/-- The reference evaluates `perform e` (pure `e`) to a `perf` node carrying the
payload and the identity resumption. -/
theorem eval_perform {e : Src} (he : IsPure e) {renv : REnv} {p : Int}
    (hpe : pden renv e = some p) :
    ∀ f, fuelOf e + 2 ≤ f → CalcReifyRef.eval f renv (.perform e) = .perf p (fun w => .ret w) := by
  intro f hf
  obtain ⟨s, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  have he' : CalcReifyRef.eval s renv e = .ret p := eval_pure e he hpe s (by omega)
  obtain ⟨s', rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  simp only [CalcReifyRef.eval, he', bind_ret]

/-- The reference's `handle`/`perform` reductions are definitional. -/
theorem eval_handle_def (fuel : Nat) (env : REnv) (clause body : Src) :
    CalcReifyRef.eval (fuel + 1) env (.handle clause body)
      = CalcReifyRef.handleC fuel (CalcReifyRef.eval fuel env body) clause env := rfl

/-- **Reference side of a firing zero-shot/payload handler.** `handle clause
(perform e)` evaluates to the clause's denotation `m` under the payload `p`. The
clause hypothesis is quantified over every resumption slot `g` — `pden` never reads
inside it, so this is no stronger than one instance, but it lets us instantiate at
the reference's actual (fuel-capturing) `res`. -/
theorem ref_fire {e clause : Src} (he : IsPure e) (hc : IsPure clause)
    {renv : REnv} {p m : Int}
    (hpe : pden renv e = some p)
    (hcl : ∀ (g : Int → Comp), pden (.ev p :: .ek g :: renv) clause = some m) :
    ∀ f, fuelOf e + fuelOf clause + 3 ≤ f →
      CalcReifyRef.eval f renv (.handle clause (.perform e)) = .ret m := by
  intro f hf
  obtain ⟨S2, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
  -- unfold the handle one step; the body `perform e` evaluates to a `perf` node
  rw [eval_handle_def, eval_perform he hpe (S2 + 1) (by omega)]
  -- handleC (S2+1) (perf p (fun w => ret w)) clause renv = eval S2 (ev p :: ek res :: renv) clause
  simp only [CalcReifyRef.handleC]
  -- the clause (pure, non-resuming) ignores the `ek res` slot: eval_pure closes it
  exact eval_pure clause hc (hcl _) S2 (by omega)

/-- **Machine side of a firing zero-shot/payload handler.** The flat machine runs
`handle clause (perform e)` by: INSTALL the handler frame; compile `e` then
PERFORM; PERFORM captures the continuation as a `vcont` and runs the clause with
`(payload, vcont)` prepended to the env. Since the clause is pure with denotation
`m` under the payload (for any resumption slot), `pure_sim` carries it to a halt on
`vint m`. -/
theorem machine_fire {e clause : Src} (he : IsPure e) (hc : IsPure clause)
    {p m : Int}
    (hpe : pden [] e = some p)
    (hcl : ∀ (g : Int → Comp), pden (.ev p :: .ek g :: []) clause = some m) :
    ∃ F, run F (.handle clause (.perform e)) = some (.vint m) := by
  -- Names for the machine objects the reduction produces.
  let clCode : Code := compile clause []
  -- the resumption captured by PERFORM (contents irrelevant — consK absorbs it).
  let kv : Value := .vcont [] [] [] clCode []
  -- the pure-return frame PERFORM leaves on K (carrying the clause's empty cont).
  let frN : Frame := { clause := none, retCode := [], retEnv := [], retStack := [] }
  -- Clause env on the machine, related to (ev p :: ek g :: []) via int + consK.
  have henvC : RelEnv [Value.vint p, kv] (.ev p :: .ek (fun _ => Comp.stuck) :: []) :=
    .cons (.int p) (.consK kv (fun _ => Comp.stuck) .nil)
  -- (1) the pure clause halts on `vint m`, returning through `frN`.
  obtain ⟨Fc, hFc⟩ := pure_sim clause hc henvC (hcl _) [] [] [frN] 2 (.vint m) (by simp [exec, frN])
  -- (2) PERFORM fires: it captures `kv` and runs the clause under `[vint p, kv]`.
  have hperf : exec (Fc + 1) [Instr.PERFORM] [] [Value.vint p]
      [{ clause := some (clCode, []), retCode := [], retEnv := [], retStack := [] }] = some (.vint m) := by
    simp only [exec]; exact hFc
  -- (3) compile `e` in front of PERFORM: pure_sim carries it from `[]` to push `p`.
  obtain ⟨Fe, hFe⟩ := pure_sim e he (.nil) hpe [Instr.PERFORM] [] _ (Fc + 1) (.vint m) hperf
  -- (4) INSTALL pushes the handler frame, then runs the body code.
  have hinstall : exec (Fe + 1)
      (Instr.INSTALL clCode [] :: compile e [Instr.PERFORM]) [] [] [] = some (.vint m) := by
    simp only [exec]; exact hFe
  exact ⟨Fe + 1, by simpa only [run, compile] using hinstall⟩

/-- **A firing-handler agreement, universally quantified over programs.** For any
pure payload-expression `e` and any pure non-resuming `clause`, the calculated
machine (`CalcReify.run`) and the denotational reference (`CalcReifyRef.run`) agree
on `handle clause (perform e)`: both yield the clause's denotation under the
payload. This is the **first non-`rfl`, ∀-quantified result that fires a handler**
— the clause is genuinely run with the captured continuation — closing the
zero-shot / payload-threading corner of the `vcont ↔ ek` frontier (the clause does
not itself resume; a *resuming* clause is the remaining residual). -/
theorem fire_agree {e clause : Src} (he : IsPure e) (hc : IsPure clause) {p m : Int}
    (hpe : pden [] e = some p)
    (hcl : ∀ (g : Int → Comp), pden (.ev p :: .ek g :: []) clause = some m) :
    (∃ F, run F (.handle clause (.perform e)) = some (.vint m)) ∧
    (∃ G, CalcReifyRef.run G (.handle clause (.perform e)) = some m) := by
  refine ⟨machine_fire he hc hpe hcl, ?_⟩
  exact ⟨fuelOf e + fuelOf clause + 3,
    by simp only [CalcReifyRef.run, ref_fire he hc hpe hcl _ (Nat.le_refl _)]⟩

/-- **The pure core, against the real reference.** For a closed pure program both
the machine (`CalcReify.run`) and the denotational reference (`CalcReifyRef.run`)
agree: each yields `n`. This is the pure spine of `exec ∘ compile ≡ run` as a
genuine two-implementation theorem. -/
theorem pure_correct_ref {e : Src} (hpure : IsPure e) {n : Int} (hp : pden [] e = some n) :
    (∃ F, run F e = some (.vint n)) ∧ (∃ G, CalcReifyRef.run G e = some n) := by
  refine ⟨pure_correct hpure hp, ?_⟩
  exact ⟨fuelOf e, by simp only [CalcReifyRef.run, eval_pure e hpure hp _ (Nat.le_refl _)]⟩

/-! ## A `handle`-over-pure-body demonstrator

`handle 999 (let x = 5 in x + 3)`: the body performs nothing, so the (zero-shot)
clause `999` is dead and an *unfired handler is transparent*. Both the machine and
the reference yield `8`. This is the `IsPure.handle` case end-to-end — the
`INSTALL` instruction and the return-through-a-handler-frame path, exercised and
proven against the real reference, with no `vcont ↔ ek` relation needed. -/
example :
    let prog : Src := .handle (.val 999) (.letE (.val 5) (.add (.var 0) (.val 3)))
    (∃ F, run F prog = some (.vint 8)) ∧ (∃ G, CalcReifyRef.run G prog = some 8) :=
  pure_correct_ref (.handle (.letE .val (.add .var .val))) (by rfl)

/-! ## A **firing** demonstrator via `fire_agree`

`handle (payload + 1) (perform 41)`: the body performs with payload `41`; the
clause reads the payload at index 0 and adds 1 → `42`, *discarding* the captured
resumption (zero-shot). `fire_agree` proves the machine and the reference both
yield `42` — for this instance, but through the universally-quantified firing
theorem, not a bare `rfl`. -/
example :
    let prog : Src := .handle (.add (.var 0) (.val 1)) (.perform (.val 41))
    (∃ F, run F prog = some (.vint 42)) ∧ (∃ G, CalcReifyRef.run G prog = some 42) :=
  fire_agree (e := .val 41) (clause := .add (.var 0) (.val 1))
    .val (.add .var .val) (by rfl) (fun _ => by rfl)

/-! ## In-Lean machine-vs-reference agreement on **firing** handlers

The inductive `pure_sim`/`eval_pure` above cannot yet reach a *firing* handler (a
`perform` that actually triggers its clause, possibly resuming): that needs the
`vcont ↔ ek` step-indexed logical relation, the open residual. But agreement on
any *specific* closed firing program is provable **right now**, because both
`CalcReify.run` (the flat machine) and `CalcReifyRef.run` (the free-monad
reference) reduce by computation: each side is a closed `rfl`. So `⟨rfl, rfl⟩`
proves the two *independent* implementations land on the same integer.

This is strictly stronger than the harness fuzz (`reify-cps.ts`): there the
cross-check is empirical and the reference is in TypeScript; here it is a
*machine-checked Lean proof* that the calculated machine and the in-Lean
denotational reference agree — on the genuinely-hard cases (non-tail, multi-shot,
re-handling) the general theorem still owes. It is program-specific, not the
universally-quantified bisimulation; but it is real, proven, and covers exactly
the firing behaviours `pure_sim` cannot. -/

section Firing
open Bang.CalcReify.Src

/-- Machine and reference agree (both yield `k`) on a closed program. -/
def Agree (prog : Src) (k : Int) : Prop :=
  run 1000 prog = some (.vint k) ∧ CalcReifyRef.run 1000 prog = some k

-- body `add (perform 5) 1000`: the captured continuation is "λr. r + 1000".
private def bodyP : Src := add (perform (val 5)) (val 1000)

-- one-shot, NON-TAIL: (7+1000)+100 = 1107
example : Agree (handle (add (resume (var 1) (val 7)) (val 100)) bodyP) 1107 := ⟨by rfl, by rfl⟩
-- one-shot, tail: 7+1000 = 1007
example : Agree (handle (resume (var 1) (val 7)) bodyP) 1007 := ⟨by rfl, by rfl⟩
-- MULTI-SHOT (resume twice): (7+1000)+(20+1000) = 2027
example : Agree (handle (add (resume (var 1) (val 7)) (resume (var 1) (val 20))) bodyP) 2027 :=
  ⟨by rfl, by rfl⟩
-- ZERO-shot (continuation discarded): 999
example : Agree (handle (val 999) bodyP) 999 := ⟨by rfl, by rfl⟩
-- re-handling (perform inside a resumption): 7+7 = 14
example : Agree (handle (resume (var 1) (val 7)) (add (perform (val 1)) (perform (val 2)))) 14 :=
  ⟨by rfl, by rfl⟩
-- payload reaches the clause: 5+3 = 8
example : Agree (letE (val 5) (handle (add (var 0) (resume (var 1) (val 3))) (perform (var 0)))) 8 :=
  ⟨by rfl, by rfl⟩
-- triple multi-shot: (1+1000)+(2+1000)+(3+1000) = 3006
example : Agree (handle (add (resume (var 1) (val 1))
    (add (resume (var 1) (val 2)) (resume (var 1) (val 3)))) bodyP) 3006 := ⟨by rfl, by rfl⟩

end Firing

end Bang.CalcReifySim
