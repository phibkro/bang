import Bang.Backend.WasmEmit
open Bang Bang.WasmEmit
-- eyeball the emitted .wat for the caught-raise + normal + nested cases (pure string-building — #eval safe)
#eval match emitModule (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 7))) with | .ok s => IO.println s | .unsup r => IO.println s!"UNSUP: {r}"
#eval IO.println "----"
#eval match emitModule (.handle (.throws 0) (.letC (.perform (.vvar 0) "raise" (.vint 7)) (.ret (.vint 99)))) with | .ok s => IO.println s | .unsup r => IO.println s!"UNSUP: {r}"
#eval IO.println "----"
#eval match emitModule (.handle (.throws 0) (.binop .add (.vint 3) (.vint 4))) with | .ok s => IO.println s | .unsup r => IO.println s!"UNSUP: {r}"
#eval IO.println "----nested----"
#eval match emitModule (.handle (.throws 0) (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 5)))) with | .ok s => IO.println s | .unsup r => IO.println s!"UNSUP: {r}"
#eval IO.println "----nested outer----"
#eval match emitModule (.handle (.throws 0) (.handle (.throws 0) (.perform (.vvar 1) "raise" (.vint 8)))) with | .ok s => IO.println s | .unsup r => IO.println s!"UNSUP: {r}"
