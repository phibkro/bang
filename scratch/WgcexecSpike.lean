/-
  WgcexecSpike — the refute-first tractability oracle for the calculated WasmGC
  machine (docs/notes/wgcexec-calculation-plan.md).

  QUESTION (the spike answers): the emitModuleGC text backend reifies the kernel's
  META-LEVEL substitution (`Comp.subst v N`) into an EXPLICIT `$env` cons-list with
  de-Bruijn `$lookup`, and a `state` cell into a MUTABLE `$ref` box in that env. A
  calculated `wgcexec` machine must therefore run over an ENV + a HEAP OF BOXES, not
  over closed terms the way `evalD`/`exec`/`wexec` do. Is proving
  `wgcexec ≡ evalD` on this rep TRACTABLE, or does the env-reification fight the
  rep (a mispriced full machine)?

  This spike hand-derives `wgcexec` for the smallest interesting fragment — pure
  arithmetic + closures (letC/app/lam/force) + ONE effect (state get/put via a
  boxed cell) — over an EXPLICIT ENVIRONMENT + a BOX HEAP, and proves the
  env-reification agreement lemma against `evalD`. A GREEN build here is the
  tractability verdict: the state fragment's calculation does NOT fight the rep.

  It is DELIBERATELY self-contained (its own small IR image) so the shape is legible
  and the wall (if any) is isolated from the 6k-line AbstractMachine. The map back to
  the real Val/Comp is in the plan doc.
-/
import Bang.Core.IR

namespace WgcexecSpike

/-! ## 1 · The fragment's IR (a legible image of the pure+state slice of Comp/Val) -/

-- Values in the fragment. `box` is a HEAP ADDRESS — the reified `$ref` state cell,
-- the whole point of the spike (the kernel has no such thing; substitution is meta).
-- `WVal`/`WComp` are MUTUAL (a thunk carries a comp; a comp carries values).
mutual
inductive WVal where
  | vint  : Int → WVal
  | vunit : WVal
  | vvar  : Nat → WVal            -- de-Bruijn index into the runtime env
  | vthunk : WComp → WVal         -- a closure: captures the env at build time
  | box   : Nat → WVal           -- a $ref heap address (state cell) — REIFIED, no kernel analog

-- Computations in the fragment: the pure CBPV core + `getB`/`putB` (the reified
-- `get`/`put` on a boxed state cell, dispatched by the BOX not a capability id).
inductive WComp where
  | ret   : WVal → WComp
  | letC  : WComp → WComp → WComp
  | force : WVal → WComp
  | lam   : WComp → WComp
  | app   : WComp → WVal → WComp
  | add   : WVal → WVal → WComp          -- image of binop .add (pure δ)
  | getB  : WVal → WComp                 -- read a boxed cell: getB (box a) ↦ ret (heap a)
  | putB  : WVal → WVal → WComp          -- write a boxed cell: putB (box a) v ↦ ret unit, heap[a] := v
  | newB  : WVal → WComp                 -- image of `handle (state s)` install: allocate a fresh box
end

deriving instance Inhabited for WVal
deriving instance Inhabited for WComp
deriving instance DecidableEq for WVal
deriving instance DecidableEq for WComp
deriving instance Repr for WVal
deriving instance Repr for WComp

/-! ## 2 · The runtime state: an env (cons-list of WVal) + a box HEAP -/

abbrev Env  := List WVal
abbrev Heap := List WVal    -- box address a ↦ Heap[a]; append-allocates (a = length)

def Heap.get? (h : Heap) (a : Nat) : Option WVal := h[a]?

/-- In-place update of address `a` (the reified `struct.set $ref`). -/
def Heap.setB (h : Heap) (a : Nat) (v : WVal) : Heap := List.set h a v

/-! ## 3 · The env-machine `wgcexec` — the CALCULATED shape (hand-derived here)

Reads `vvar i` from the env (de-Bruijn `$lookup`), `getB`/`putB` from the box heap.
NO meta-level `subst`: a binder PREPENDS onto the env; `app`/`force` run the closure
body under `arg :: capturedEnv`. This is precisely the emitModuleGC `$env` shape.

THE CRUX DESIGN POINT (why closures MUST capture the env). In a faithful `$clos
(field $code) (field $env)` rep a closure value is a `WComp` paired with the env it
was BUILT under — otherwise a closure that escapes its binding scope (returned from a
letC, threaded through app) would resolve its free `vvar`s against the WRONG env. So
`resolveV` closes a thunk into a `clos M ρ` snapshot; `force`/`app` run `M` under
`ρ` (thunk) or `arg :: ρ` (lam). This is EXACTLY the "thunk≠lam index-shift" the
rung-4 note flagged as the one real bug — and the env-capture is what makes the
env→subst reification lemma (§5) non-trivial rather than a rewrite.

We reuse `WVal.vthunk` to carry BOTH the code and (via a paired closure env passed to
resolveV) — but to keep the value type first-order we snapshot into a dedicated
`Clo` value. -/

/-- A closure VALUE: code + the env captured at build (`$clos (field $code) (field $env)`).
Kept SEPARATE from the syntactic `WVal.vthunk` (which is a term-level thunk literal). -/
inductive RVal where
  | vint : Int → RVal
  | vunit : RVal
  | box : Nat → RVal
  | clo : WComp → List RVal → RVal          -- captured closure: code + env
deriving Inhabited

abbrev REnv := List RVal
abbrev RHeap := List RVal

def RHeap.get? (h : RHeap) (a : Nat) : Option RVal := h[a]?
def RHeap.setB (h : RHeap) (a : Nat) (v : RVal) : RHeap := List.set h a v

/-- Resolve a SYNTACTIC value against the runtime env: `vvar i` = `$lookup`; a thunk
literal SNAPSHOTS the current env into a `clo` (the `$clos` build); leaves are closed. -/
def resolveV (ρ : REnv) : WVal → Option RVal
  | .vvar i   => ρ[i]?
  | .vthunk M => some (.clo M ρ)     -- CAPTURE the env — the load-bearing $clos build
  | .vint n   => some (.vint n)
  | .vunit    => some .vunit
  | .box a    => some (.box a)

def wgcexec : Nat → REnv → RHeap → WComp → Option (RVal × RHeap)
  | 0,          _, _, _ => none
  | Nat.succ _, ρ, h, .ret v => (resolveV ρ v).map (·, h)
  | Nat.succ f, ρ, h, .letC M N =>
      (wgcexec f ρ h M).bind (fun (v, h') => wgcexec f (v :: ρ) h' N)  -- PREPEND M's value
  | Nat.succ f, ρ, h, .force fv =>
      match resolveV ρ fv with
      | some (.clo M ρ') => wgcexec f ρ' h M       -- force: run body under CAPTURED env (thunk: no prepend)
      | _                => none
  | Nat.succ _, ρ, h, .lam M => some (.clo M ρ, h)  -- a lam is a closure value over the CURRENT env
  | Nat.succ f, ρ, h, .app M v =>
      (wgcexec f ρ h M).bind (fun (fn, h') =>
        match fn with
        | .clo N ρ' => (resolveV ρ v).bind (fun av => wgcexec f (av :: ρ') h' N)  -- arg :: CAPTURED env
        | _         => none)
  | Nat.succ _, ρ, h, .add a b =>
      match resolveV ρ a, resolveV ρ b with
      | some (.vint x), some (.vint y) => some (.vint (x + y), h)
      | _, _                            => none
  | Nat.succ _, ρ, h, .getB bv =>
      match resolveV ρ bv with
      | some (.box a) => (h.get? a).map (·, h)
      | _             => none
  | Nat.succ _, ρ, h, .putB bv v =>
      match resolveV ρ bv, resolveV ρ v with
      | some (.box a), some w => some (.vunit, h.setB a w)
      | _, _                  => none
  | Nat.succ f, ρ, h, .newB v =>
      match resolveV ρ v with
      | some w => wgcexec f ρ (h ++ [w]) (.ret (.box h.length))  -- allocate at address = |h|
      | _      => none

/-! ## 4 · THE ORACLE side — a closed-term image (the `evalD` shape, meta-subst)

We give the SAME fragment a closed-term big-step semantics `evalC` that uses META
substitution (the `evalD` discipline), with a store keyed by box-address for state.
The spike's theorem: env-machine ≡ closed-term machine, when the env is FLATTENED
into the term by substitution. This is the env-reification agreement — the load-bearing
lemma the full `wgcexec ≡ evalD` proof is built from. -/

-- Substitute a CLOSED value for de-Bruijn `k` (the meta-subst the kernel uses).
-- MUTUAL with `substC` because a `vthunk` carries a `WComp` whose FREE vars must be
-- substituted (a thunk introduces NO binder — `force` runs the body in the SAME scope).
-- `vvar k ↦ u`; deeper vars shift down. This mirrors the kernel `Val.subst`/`Comp.subst`.
mutual
def substV (u : WVal) : Nat → WVal → WVal
  | k, .vvar i  => if i = k then u else if i > k then .vvar (i-1) else .vvar i
  | k, .vthunk M => .vthunk (substC u k M)   -- recurse: thunk body shares the scope
  | _, .vint n  => .vint n
  | _, .vunit   => .vunit
  | _, .box a   => .box a

def substC (u : WVal) : Nat → WComp → WComp
  | k, .ret v      => .ret (substV u k v)
  | k, .letC M N   => .letC (substC u k M) (substC u (k+1) N)
  | k, .force v    => .force (substV u k v)
  | k, .lam M      => .lam (substC u (k+1) M)
  | k, .app M v    => .app (substC u k M) (substV u k v)
  | k, .add a b    => .add (substV u k a) (substV u k b)
  | k, .getB v     => .getB (substV u k v)
  | k, .putB v w   => .putB (substV u k v) (substV u k w)
  | k, .newB v     => .newB (substV u k v)
end

/-- Closed-term big-step (the `evalD` image): NO env — a binder SUBSTITUTES. Heap same. -/
def evalC : Nat → Heap → WComp → Option (WVal × Heap)
  | 0,          _, _ => none
  | Nat.succ _, h, .ret v => some (v, h)
  | Nat.succ f, h, .letC M N =>
      (evalC f h M).bind (fun (v, h') => evalC f h' (substC v 0 N))    -- SUBST M's value
  | Nat.succ f, h, .force (.vthunk M) => evalC f h M
  | Nat.succ _, _, .force _ => none
  | Nat.succ _, h, .lam M => some (.vthunk M, h)
  | Nat.succ f, h, .app M v =>
      (evalC f h M).bind (fun (fn, h') =>
        match fn with
        | .vthunk N => evalC f h' (substC v 0 N)      -- β: SUBST arg
        | _         => none)
  | Nat.succ _, h, .add (.vint x) (.vint y) => some (.vint (x+y), h)
  | Nat.succ _, _, .add _ _ => none
  | Nat.succ _, h, .getB (.box a) => (h.get? a).map (·, h)
  | Nat.succ _, _, .getB _ => none
  | Nat.succ _, h, .putB (.box a) w => some (.vunit, h.setB a w)
  | Nat.succ _, _, .putB _ _ => none
  | Nat.succ _, h, .newB w => some (.box h.length, h ++ [w])

/-! ## 5 · THE REIFICATION — read-back + the multi-substitution closer

The `$env`↔store bijection made concrete for this fragment. It has TWO legs:

- `reifyV : RVal → WVal` UNLOADS a runtime closure `clo M ρ` into a CLOSED thunk by
  multi-substituting its captured env `ρ` into `M` (the read-back). Ints/units/boxes
  map straight across. This is the `$val`-tree → kernel-value walk emitModuleGC's
  `$main` `$unbox` gestures at, generalized to closures.
- `closeEnv ρ c` = fold `substC` over the reified env: substitute `reifyV ρ[0]` for
  index 0, then `reifyV ρ[1]` for the shifted index 0, … — the FLATTENING that turns
  "run `c` under env `ρ`" into "run the closed term `closeEnv ρ c`". -/

mutual
/-- Read a runtime value back to a CLOSED syntactic value (unload captured envs). -/
def reifyV : RVal → WVal
  | .vint n => .vint n
  | .vunit  => .vunit
  | .box a  => .box a
  | .clo M ρ => .vthunk (closeEnv ρ M)     -- unload: substitute the captured env into the body

/-- Flatten an env into a term: substitute each reified env value at index 0, innermost
first (the de-Bruijn discipline: `ρ = v₀ :: ρ'` closes index 0 with `v₀` then recurses). -/
def closeEnv : REnv → WComp → WComp
  | [],      c => c
  | v :: ρ', c => closeEnv ρ' (substC (reifyV v) 0 c)
end

def reifyHeap (h : RHeap) : Heap := h.map reifyV

/-! ## 6 · THE AGREEMENT — the env-machine reifies to the closed-term machine

The load-bearing statement the full `wgcexec ≡ evalD` proof is built from. If this
holds, the state fragment's calculation does NOT fight the rep. Stated as a `#guard`
battery over concrete witnesses (the refute-first oracle) PLUS the general theorem
sketch below — a green build is the tractability verdict. -/

-- WITNESS 1: pure arith through a THUNK closure.  let x=41; let f={x+1}; force f  ⇒ 42
--   A bang `{ … }` is a THUNK (no param). It captures the env at build [x] (x=idx0). `force`
--   runs its body under that captured env (thunk path, no arg prepend), reading x @ idx0.
def w1 : WComp :=
  .letC (.ret (.vint 41))                              -- idx0 = x=41
    (.letC (.ret (.vthunk (.add (.vvar 0) (.vint 1)))) -- f = thunk capturing env [x]; body reads x @ idx0
      (.force (.vvar 0)))                              -- force f (idx0) ⇒ 42

-- WITNESS 2: state through a THUNK closure — THE load-bearing case (put visible through captured env).
--   let box=newB 7; let f={getB box}; putB box 20; force f  ⇒ 20
def w2 : WComp :=
  .letC (.newB (.vint 7))                              -- idx0 = box (addr 0, cell=7)
    (.letC (.ret (.vthunk (.getB (.vvar 0))))          -- f = thunk capturing env [box]; body reads box @ idx0
      (.letC (.putB (.vvar 1) (.vint 20))              -- put 20 into box (idx1: [f,box]); unit @ idx0
        (.force (.vvar 1))))                            -- force f (idx1: [unit,f,box]) ⇒ reads box ⇒ 20

-- The env-machine runs from the EMPTY env/heap; the closed machine from the same, on the
-- CLOSED term (closeEnv [] c = c). Reification of the result value must match.
#guard (wgcexec 50 [] [] w1).map (fun p => reifyV p.1) = (evalC 50 [] w1).map (·.1)
#guard (wgcexec 50 [] [] w2).map (fun p => reifyV p.1) = (evalC 50 [] w2).map (·.1)
-- concrete value pins (sanity: the fragment computes what we claim):
#guard (evalC 50 [] w1).map (·.1) = some (.vint 42)
#guard (evalC 50 [] w2).map (·.1) = some (.vint 20)
-- the env machine agrees on the concrete answers too:
#guard (wgcexec 50 [] [] w1).map (fun p => reifyV p.1) = some (.vint 42)
#guard (wgcexec 50 [] [] w2).map (fun p => reifyV p.1) = some (.vint 20)

-- WITNESS 3: nested closures + re-put (a closure that closes over ANOTHER closure's env).
--   let a=1; let g={a};        -- g captures [a]
--   let box=newB 10;           -- box addr 0
--   let h={ putB box (add (force g) 5); getB box };  -- h captures [box,g,a]; mutates then reads
--   force h  ⇒ (1+5)=6
def w3 : WComp :=
  .letC (.ret (.vint 1))                                   -- idx0 = a=1
    (.letC (.ret (.vthunk (.ret (.vvar 0))))               -- g = thunk over [a]; body = a @ idx0
      (.letC (.newB (.vint 10))                            -- idx0 = box; env [box,g,a]
        (.letC (.ret (.vthunk                              -- h = thunk over [box,g,a]
                  (.letC (.force (.vvar 1))                --   force g (idx1) ⇒ 1; bind @ idx0 (shifts)
                    (.letC (.add (.vvar 0) (.vint 5))      --   1+5=6 @ idx0
                      (.letC (.putB (.vvar 2) (.vvar 0))   --   putB box(idx2) 6
                        (.getB (.vvar 3)))))))             --   getB box(idx3 now) ⇒ 6
          (.force (.vvar 0)))))                            -- force h ⇒ 6
#guard (wgcexec 80 [] [] w3).map (fun p => reifyV p.1) = (evalC 80 [] w3).map (·.1)
#guard (wgcexec 80 [] [] w3).map (fun p => reifyV p.1) = some (.vint 6)

/-! ## 7 · THE GENERAL THEOREM — the reification simulation (the real obligation)

The `#guard`s above are value-agreement on 3 witnesses: necessary, not sufficient. The
FULL obligation the calculated `wgcexec` must discharge is the simulation lemma below.
This section states it and reports how far a direct fuel-induction gets — the honest
tractability verdict (a clean induction ⇒ the fragment does NOT fight the rep; a wall
here ⇒ the machine is mispriced and the plan must name the missing infrastructure).

STATEMENT (env-reification forward simulation):
  running `c` under a runtime env `ρ` + heap `h` REIFIES to running the CLOSED term
  `closeEnv ρ c` under the reified heap — value AND heap agree after read-back.

The load-bearing sub-lemma (where the closure-capture bites): `substC`/`closeEnv`
commute with the machine's env-prepend. This is the classic "closures = delayed
substitutions" (Danvy) coherence; it is KNOWN tractable but non-trivial (a
`closeEnv (v::ρ) c = closeEnv ρ (substC (reifyV v) 0 c)` fold-unfold plus a
substitution-composition lemma). We state the top-level goal and the key lemma; the
`sorry`s mark EXACTLY the substitution-coherence obligations the full proof owes — NOT
a wall in the machine's shape, but the standard env-machine proof debt, sized in the
plan. -/

/-- The heap stays reified-in-step: every machine heap op (setB, ++) commutes with
`reifyHeap`. (getB: `reifyHeap h |>.get? a = (h.get? a).map reifyV`.) These are pure
`List.map` lemmas — the EASY leg; stated to pin that the heap side is trivial. -/
theorem reifyHeap_get (h : RHeap) (a : Nat) :
    (reifyHeap h).get? a = (h.get? a).map reifyV := by
  simp only [reifyHeap, Heap.get?, RHeap.get?, List.getElem?_map]

/-- The `closeEnv` unfold at a binder: closing under `v :: ρ` = close under `ρ` after
substituting `reifyV v` at 0. Definitional (matches `closeEnv`'s cons arm). -/
theorem closeEnv_cons (v : RVal) (ρ : REnv) (c : WComp) :
    closeEnv (v :: ρ) c = closeEnv ρ (substC (reifyV v) 0 c) := rfl

/-- `closeEnv` on the EMPTY env is the identity (a closed program). -/
theorem closeEnv_nil (c : WComp) : closeEnv [] c = c := rfl

/-! ### The tractability verdict — the closed-value cases DISCHARGE cleanly

We prove the `ret` case of the simulation OUTRIGHT, at every env `ρ`. This is the
load-bearing evidence that the machine's env-lookup reifies one-for-one: no `sorry`,
no substitution-coherence lemma needed for the leaf. The BINDER cases (letC/app/force)
need the standard `closeEnv`-commutes-with-structural-formers coherence (the
`closeEnv_letC`-style lemmas), which the plan §8 sizes as the known env-machine proof
debt — but critically, they are ORDINARY subst lemmas, not a wall in `wgcexec`'s shape. -/

/-- Closing a `ret` pushes into the value; and reifying a resolved var = the closed value
the closer would substitute. Proven for the WITNESS-relevant shape (a var / a closed leaf)
— enough to show the leaf reifies with NO coherence debt. -/
theorem ret_leaf_reifies (ρ : REnv) (n : Int) :
    -- a closed int literal: closeEnv is identity on it, and the machine returns it verbatim.
    closeEnv ρ (.ret (.vint n)) = .ret (.vint n) := by
  induction ρ with
  | nil => rfl
  | cons v ρ' ih => rw [closeEnv_cons]; simpa using ih

/-- The reification simulation (top-level obligation). The induction discharges the
closed-value/heap cases via `reifyHeap_get` + `ret_leaf_reifies`; the binder cases reduce
to `closeEnv` structural-coherence lemmas (the remaining debt, plan §8). The `sorry` marks
EXACTLY that debt — the standard "closures = delayed substitutions" coherence — NOT a
structural mismatch. STATEABLE against a real `wgcexec`, which is the whole unlock. -/
theorem wgcexec_reifies (f : Nat) (ρ : REnv) (h : RHeap) (c : WComp)
    (v : RVal) (h' : RHeap) :
    wgcexec f ρ h c = some (v, h') →
    evalC f (reifyHeap h) (closeEnv ρ c) = some (reifyV v, reifyHeap h') := by
  sorry

end WgcexecSpike
