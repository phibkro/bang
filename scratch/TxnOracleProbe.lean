/-
  TxnOracleProbe.lean — refute-first oracle probe for the rung-3 transaction spike.
  Confirms Source.eval's value on the A11 abort witness + a commit witness + a nested
  handle-inside-txn case, BEFORE any emitter is written. Compiled #eval-via-IO (the
  fuel recursion is unreliable under `lake env lean` #eval — repo lesson).
-/
import Bang.Backend.AbstractMachine

open Bang

def oracleInt (M : Comp) : String :=
  match Source.eval 2000 M with
  | .done (.vint n) => toString n
  | .done _         => "NON-INT-VALUE"
  | .oom            => "OOM"
  | _               => "STUCK-OR-DIVERGE"

-- A11: handle (transaction) (new r=100; write r 70; raise 100) ⟹ 100 (abort, rollback)
def a11 : Comp :=
  .handle (.throws 0)
    (.handle (.transaction 2 [])
      (.letC (.perform (.vvar 0) "newTVar" (.vint 100))
        (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 70)))
          (.perform (.vvar 3) "raise" (.vint 100)))))

-- A10-shape COMMIT: transaction (new r=100; write r 70; read r) ⟹ 70
def commit : Comp :=
  .handle (.transaction 2 [])
    (.letC (.perform (.vvar 0) "newTVar" (.vint 100))
      (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 70)))
        (.perform (.vvar 2) "readTVar" (.vint 0))))

-- single-cell read after alloc (AgreeOutcome:162): new 9; read r ⟹ 9
def newread : Comp :=
  .handle (.transaction 2 [])
    (.letC (.perform (.vvar 0) "newTVar" (.vint 9)) (.perform (.vvar 1) "readTVar" (.vvar 0)))

-- two cells: new a=5; new b=10; write a 7; read a ⟹ 7  (allocation ordering)
def twocell : Comp :=
  .handle (.transaction 2 [])
    (.letC (.perform (.vvar 0) "newTVar" (.vint 5))
      (.letC (.perform (.vvar 1) "newTVar" (.vint 10))
        (.letC (.perform (.vvar 2) "writeTVar" (.pair (.vint 0) (.vint 7)))
          (.perform (.vvar 3) "readTVar" (.vint 0)))))

-- read the SECOND cell: new a=5; new b=10; read b ⟹ 10
def readsecond : Comp :=
  .handle (.transaction 2 [])
    (.letC (.perform (.vvar 0) "newTVar" (.vint 5))
      (.letC (.perform (.vvar 1) "newTVar" (.vint 10))
        (.perform (.vvar 2) "readTVar" (.vint 1))))

-- commit-then-observe-after-abort would need a shared handler; here just abort discards writes:
-- handle (txn (new a=5; write a 99; raise 42)) ⟹ 42 (write to a never observed)
def abort42 : Comp :=
  .handle (.throws 0)
    (.handle (.transaction 2 [])
      (.letC (.perform (.vvar 0) "newTVar" (.vint 5))
        (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 99)))
          (.perform (.vvar 3) "raise" (.vint 42)))))

def main : IO Unit := do
  IO.println s!"a11 (abort, rollback)     oracle = {oracleInt a11}   expect 100"
  IO.println s!"commit (new;write;read)   oracle = {oracleInt commit}   expect 70"
  IO.println s!"newread (new 9;read)      oracle = {oracleInt newread}   expect 9"
  IO.println s!"twocell (2 cells,write a) oracle = {oracleInt twocell}   expect 7"
  IO.println s!"readsecond (read cell 1)  oracle = {oracleInt readsecond}   expect 10"
  IO.println s!"abort42 (write then raise) oracle = {oracleInt abort42}   expect 42"
