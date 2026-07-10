import Bang.Backend.AbstractMachine
open Bang
-- Oracle values for the rung-2 throws fragment targets (compiled #guard — reliable).
-- caught raise: handle (throws 0) (perform (vvar 0) "raise" 7) ⇒ 7
#guard (match Source.eval 100 (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 7))) with | .done (.vint n) => n | _ => -999) == 7
-- raise discards continuation: handle (throws 0) (letC (raise 7) (ret 99)) ⇒ 7
#guard (match Source.eval 100 (.handle (.throws 0) (.letC (.perform (.vvar 0) "raise" (.vint 7)) (.ret (.vint 99)))) with | .done (.vint n) => n | _ => -999) == 7
-- normal return: handle (throws 0) (ret 42) ⇒ 42
#guard (match Source.eval 100 (.handle (.throws 0) (.ret (.vint 42))) with | .done (.vint n) => n | _ => -999) == 42
-- body computes then returns (no raise): handle (throws 0) (binop add 3 4) ⇒ 7
#guard (match Source.eval 100 (.handle (.throws 0) (.binop .add (.vint 3) (.vint 4))) with | .done (.vint n) => n | _ => -999) == 7
-- nested handles, inner raises to inner handler: handle(throws 0)(handle(throws 0)(raise@0 5)) ⇒ inner catches ⇒ ret 5 ⇒ outer normal ⇒ 5
#guard (match Source.eval 100 (.handle (.throws 0) (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 5)))) with | .done (.vint n) => n | _ => -999) == 5
-- nested, inner body raises to OUTER handler (vvar 1 skips inner cap): outer catches ⇒ 8
#guard (match Source.eval 100 (.handle (.throws 0) (.handle (.throws 0) (.perform (.vvar 1) "raise" (.vint 8)))) with | .done (.vint n) => n | _ => -999) == 8
