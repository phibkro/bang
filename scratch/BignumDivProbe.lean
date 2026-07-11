import Bang.Core.IR
open Bang

/-! Nail the EXACT value of Lean core `Int /` for all four sign combinations,
plus what the named div functions give. `#eval` prints; run compiled. -/

#eval s!"( 7)/( 2) = {(7:Int)/2}"
#eval s!"(-7)/( 2) = {(-7:Int)/2}"
#eval s!"( 7)/(-2) = {(7:Int)/(-2)}"
#eval s!"(-7)/(-2) = {(-7:Int)/(-2)}"
#eval s!"tdiv: (-7)/2={Int.tdiv (-7) 2}  7/(-2)={Int.tdiv 7 (-2)}  (-7)/(-2)={Int.tdiv (-7) (-2)}"
#eval s!"fdiv: (-7)/2={Int.fdiv (-7) 2}  7/(-2)={Int.fdiv 7 (-2)}  (-7)/(-2)={Int.fdiv (-7) (-2)}"
#eval s!"ediv: (-7)/2={Int.ediv (-7) 2}  7/(-2)={Int.ediv 7 (-2)}  (-7)/(-2)={Int.ediv (-7) (-2)}"
#eval s!"BinOp.eval div: (-7)/2={BinOp.eval .div (-7) 2}  7/(-2)={BinOp.eval .div 7 (-2)}"
