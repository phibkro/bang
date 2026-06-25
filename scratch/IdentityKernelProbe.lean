/-
End-to-end de-risk of the identity representation (ADR-0054) — a standalone mini-kernel.
NO frozen-def edits; validates the chosen design BEFORE touching Core:
  • capability-passing: `handle` BINDS a capability var (index 0); `perform` references it as a VALUE
  • Fork (ii): the generative identity = `handlerCount`-at-install, substituted in as `cap n` (NO Config counter)
  • Fork (a): dispatch by label/identity MATCH (`splitAtId`), not by re-counting position

The witness is the exact program that breaks absolute caps (ADR-0053): a thunk that locally handles its
OWN state and reads it, FORCED under an unrelated outer `throws` (insert-below-the-target migration).
Target: BOTH the migrated and non-migrated forms read the thunk's own state = 7.
-/

namespace IdKernelProbe

mutual
inductive V where
  | unit | int (n : Int) | var (i : Nat) | thunk (c : C) | cap (n : Nat)
inductive C where
  | ret (v : V) | letC (m n : C) | force (v : V) | lam (m : C) | app (m : C) (v : V)
  | perform (c : V) (op : String) (arg : V) | handle (h : H) (m : C)
inductive H where
  | state (s : V) | throws
end

inductive F where
  | letF (n : C) | appF (v : V) | handleF (id : Nat) (h : H)
abbrev Stk := List F

-- de Bruijn shift (binders: lam · letC-cont · handle-cap all bind index 0)
mutual
def shiftV (c : Nat) : V → V
  | .unit => .unit | .int n => .int n | .cap n => .cap n
  | .var i => if i < c then .var i else .var (i + 1)
  | .thunk m => .thunk (shiftC c m)
def shiftC (c : Nat) : C → C
  | .ret v => .ret (shiftV c v) | .force v => .force (shiftV c v)
  | .letC m n => .letC (shiftC c m) (shiftC (c + 1) n)
  | .lam m => .lam (shiftC (c + 1) m)
  | .app m v => .app (shiftC c m) (shiftV c v)
  | .perform cp op a => .perform (shiftV c cp) op (shiftV c a)
  | .handle h m => .handle (shiftH c h) (shiftC (c + 1) m)
def shiftH (c : Nat) : H → H
  | .state s => .state (shiftV c s) | .throws => .throws
end

-- single substitution at level k (removes binder k; decrements free vars > k)
mutual
def substV (k : Nat) (f : V) : V → V
  | .unit => .unit | .int n => .int n | .cap n => .cap n
  | .var i => if i < k then .var i else if i = k then f else .var (i - 1)
  | .thunk m => .thunk (substC k f m)
def substC (k : Nat) (f : V) : C → C
  | .ret v => .ret (substV k f v) | .force v => .force (substV k f v)
  | .letC m n => .letC (substC k f m) (substC (k + 1) (shiftV 0 f) n)
  | .lam m => .lam (substC (k + 1) (shiftV 0 f) m)
  | .app m v => .app (substC k f m) (substV k f v)
  | .perform cp op a => .perform (substV k f cp) op (substV k f a)
  | .handle h m => .handle (substH k f h) (substC (k + 1) (shiftV 0 f) m)
def substH (k : Nat) (f : V) : H → H
  | .state s => .state (substV k f s) | .throws => .throws
end
abbrev subst0 (f : V) (m : C) : C := substC 0 f m

def hcount : Stk → Nat
  | [] => 0
  | .handleF _ _ :: K => hcount K + 1
  | _ :: K => hcount K

-- dispatch by IDENTITY match (Fork a): find the handleF whose id = n
def splitAtId : Stk → Nat → Option (Stk × H × Stk)
  | [], _ => none
  | .handleF m h :: K, n =>
      if m = n then some ([], h, K)
      else (splitAtId K n).map (fun x => (.handleF m h :: x.1, x.2.1, x.2.2))
  | fr :: K, n => (splitAtId K n).map (fun x => (fr :: x.1, x.2.1, x.2.2))

def step : Stk × C → Option (Stk × C)
  | (K, .letC m n)          => some (.letF n :: K, m)
  | (K, .app m v)           => some (.appF v :: K, m)
  | (K, .force (.thunk m))  => some (K, m)
  -- handle (ii): mint identity = hcount K, push, substitute `cap id` for the bound cap-var 0
  | (K, .handle h m)        => let id := hcount K; some (.handleF id h :: K, subst0 (.cap id) m)
  | (.letF n :: K, .ret v)  => some (K, subst0 v n)
  | (.appF v :: K, .lam m)  => some (K, subst0 v m)
  | (.handleF _ _ :: K, .ret v) => some (K, .ret v)        -- return clause = identity (state/throws)
  -- perform: identity dispatch; `get` reads the matched state and RESUMES (handler re-installed)
  | (K, .perform (.cap n) op _a) =>
      match splitAtId K n with
      | some (Ki, .state s, Ko) => if op = "get" then some (Ki ++ .handleF n (.state s) :: Ko, .ret s) else none
      | _ => none
  | _ => none

def run : Nat → Stk × C → Option V
  | 0, _ => none
  | _ + 1, ([], .ret v) => some v
  | f + 1, cfg => match step cfg with | some cfg' => run f cfg' | none => none

def evalInt (fuel : Nat) (c : C) : Option Int :=
  match run fuel ([], c) with | some (.int n) => some n | _ => none

-- WITNESS: a thunk that handles its OWN state and reads it; the cap is var 0 (the handle's binding)
def vFragile : V := .thunk (.handle (.state (.int 7)) (.perform (.var 0) "get" .unit))

def noMig : C := .force vFragile
-- migration: force vFragile UNDER a fresh outer throws (var 1 = the λ-arg, since handle binds var 0)
def migrate : C := .app (.lam (.handle .throws (.force (.var 1)))) vFragile

#guard evalInt 50 noMig   == some 7   -- reads its own state without migration
#guard evalInt 50 migrate == some 7   -- ★ THE FIX: still reads its OWN state = 7 after migration

end IdKernelProbe
