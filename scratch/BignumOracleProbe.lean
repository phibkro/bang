import Bang.Core.IR

open Bang

/-! Refute-first probe (task: bignum rung). PIN the exact kernel Int semantics the
WasmGC emission must image. Compiled `#guard`s only — `lean env #eval` garbles nothing
here but the discipline is compiled anyway. -/

-- 1 · Which rounding does the kernel's `div` use? `BinOp.eval .div a b = vint (a / b)`.
--     CRITICAL FINDING: Lean core `Int./` = EUCLIDEAN division (`Int.ediv`) — NOT
--     truncated, NOT floored. The remainder is ALWAYS non-negative (0 ≤ a - b*(a/b) < |b|).
--     This is the exact differential-mismatch site. wasm i64 `div_s` is TRUNCATED-toward-
--     zero, so it DIFFERS from the kernel for every negative-dividend case:
--       kernel (ediv):   (-7)/2 = -4   7/(-2) = -3   (-7)/(-2) = 4
--       wasm div_s (t):  (-7)/2 = -3   7/(-2) = -3   (-7)/(-2) = 3
--     A correct emission must produce EUCLIDEAN results (both the i64 fast path AND the
--     limb routine): compute div_s, then correct by ±1 when the truncated remainder < 0.
#guard ((7 : Int) / 2) == 3
#guard ((-7 : Int) / 2) == -4        -- euclidean (tdiv -3, fdiv -4)
#guard ((7 : Int) / (-2)) == -3      -- euclidean (tdiv -3, fdiv -4)
#guard ((-7 : Int) / (-2)) == 4      -- euclidean (tdiv 3, fdiv 3)
#guard ((5 : Int) / 0) == 0          -- kernel: a / 0 = 0 (Lean total div)
#guard ((-5 : Int) / 0) == 0

-- Confirm `/` IS ediv (euclidean), distinct from BOTH tdiv and fdiv on the three cases.
#guard (((-7 : Int) / 2) == Int.ediv (-7) 2)
#guard (((7 : Int) / (-2)) == Int.ediv 7 (-2))
#guard (((-7 : Int) / (-2)) == Int.ediv (-7) (-2))
#guard (Int.ediv (-7) 2 == -4 ∧ Int.tdiv (-7) 2 == -3 ∧ Int.fdiv (-7) 2 == -4)
#guard (Int.ediv 7 (-2) == -3 ∧ Int.fdiv 7 (-2) == -4)   -- ediv ≠ fdiv here too

-- 2 · There is NO `mod`/`rem` binop (IR.BinOp = add|sub|mul|div|lt|eq). So div/mod
--     parity is NOT a v1 concern — only DIV. Remainder is derivable but unused.
--     (Val has no BEq; project the vint payload out.)
def vintOf : Val → Option Int | .vint n => some n | _ => none
#guard (vintOf (BinOp.eval .div (-7) 2) == some (-4))   -- euclidean, matches Int.ediv
#guard (vintOf (BinOp.eval .add 3 4) == some 7)
#guard (vintOf (BinOp.eval .mul (-3) 5) == some (-15))
#guard (vintOf (BinOp.eval .sub 3 10) == some (-7))

-- 3 · The i64 boundary the fast path must detect (2^63 - 1, -2^63).
#guard ((9223372036854775807 : Int) + 1 == 9223372036854775808)   -- overflows i64 max
#guard ((2 : Int) ^ 63 == 9223372036854775808)

def main : IO Unit := IO.println "BignumOracleProbe: all #guards compiled"
