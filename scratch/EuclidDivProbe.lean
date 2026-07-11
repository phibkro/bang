import Bang.Core.IR
open Bang

/-! B0 refute-first: verify the t→e (truncated→euclidean) correction formula that the wasm
emission will use, against the kernel oracle `BinOp.eval .div` (= Int.ediv) for ALL sign cases.

wasm `i64.div_s` gives truncated q_t and (via rem_s) r_t = a - b*q_t, where sign(r_t)=sign(a).
Euclidean requires r_e ≥ 0. Correction:
  if r_t < 0 then  (b > 0 ? q_t - 1 : q_t + 1)   -- i.e. q_t - sign(b)
  else q_t
Equivalently in wasm-emittable terms (no sign fn): compute q_t = a/b (div_s), r_t = a%b (rem_s);
if r_t < 0: if b > 0 then q_t-1 else q_t+1. Divisor 0 short-circuits to 0 (kernel a/0=0). -/

def tdivFixup (a b : Int) : Int :=
  if b == 0 then 0
  else
    let qt := Int.tdiv a b          -- truncated quotient (what wasm div_s gives)
    let rt := a - b * qt            -- truncated remainder (what wasm rem_s gives), sign = sign a
    if rt < 0 then (if b > 0 then qt - 1 else qt + 1) else qt

-- The fixup must equal the ORACLE (BinOp.eval .div, = Int.ediv) for every sign combination.
def oracleDiv (a b : Int) : Int := match BinOp.eval .div a b with | .vint n => n | _ => 999999

#guard tdivFixup 7 2      == oracleDiv 7 2       -- 3 == 3
#guard tdivFixup (-7) 2   == oracleDiv (-7) 2    -- -4 == -4
#guard tdivFixup 7 (-2)   == oracleDiv 7 (-2)    -- -3 == -3
#guard tdivFixup (-7) (-2) == oracleDiv (-7) (-2) -- 4 == 4
#guard tdivFixup 6 3      == oracleDiv 6 3       -- exact: 2 == 2 (no fixup)
#guard tdivFixup (-6) 3   == oracleDiv (-6) 3    -- exact: -2 == -2 (no fixup)
#guard tdivFixup 6 (-3)   == oracleDiv 6 (-3)    -- exact: -2 == -2
#guard tdivFixup (-6) (-3) == oracleDiv (-6) (-3) -- exact: 2 == 2
#guard tdivFixup 5 0      == oracleDiv 5 0       -- 0 == 0 (div by zero)
#guard tdivFixup (-5) 0   == oracleDiv (-5) 0    -- 0 == 0
#guard tdivFixup 0 7      == oracleDiv 0 7       -- 0 == 0
#guard tdivFixup 1 2      == oracleDiv 1 2       -- 0 == 0
#guard tdivFixup (-1) 2   == oracleDiv (-1) 2    -- ediv: -1 (tdiv 0, r_t -1 <0, b>0 ⇒ -1)
#guard tdivFixup 1 (-2)   == oracleDiv 1 (-2)    -- ediv: 0  (tdiv 0, r_t 1 ≥0 ⇒ 0)

-- Broad sweep: fixup ≡ oracle across a range including all sign quadrants.
#guard (List.range 21).all (fun ai =>
  (List.range 21).all (fun bi =>
    let a : Int := (ai : Int) - 10   -- -10..10
    let b : Int := (bi : Int) - 10   -- -10..10
    tdivFixup a b == oracleDiv a b))

def main : IO Unit := IO.println "EuclidDivProbe: t→e fixup ≡ oracle (all sign cases + sweep)"
