;; ADVERSARIAL WITNESS for cap-gc-rep-design.md: does a NAIVE $cap value (clause closures
;; carried directly) break ADR-0063 fail-loud on ESCAPE?
;;
;; Kernel capEscape (Bang/Examples.lean:258): a {get} thunk captures a state handler's cap,
;; is RETURNED out of the handler, then forced at top level where the handler has POPPED.
;; Kernel outcome = .escapedCap (a DEFINED fail-loud terminal, NOT a value).
;;
;; A naive $cap carries the handler's clause-closure/state-box DIRECTLY. After the handler
;; region exits, the GC keeps those closures ALIVE (reachable through the escaped $cap value).
;; So a perform on the escaped cap would SILENTLY SUCCEED — call the dead handler's get,
;; read the still-live box — instead of failing loud. THIS WITNESS DEMONSTRATES THE HAZARD:
;; it emits a value (42) where the kernel emits .escapedCap. A faithful design MUST NOT do this.
;;
;; Shape: handler mints a state cell (box=42), returns a thunk that performs get on the cap.
;; The thunk is forced AFTER the handler "region" (here: after $installHandler returns).
;; The naive rep has no liveness check ⇒ prints 42. Fail-loud would require a generation stamp.
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    (type $ref  (sub $val (struct (field (mut (ref null $val))))))
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env)))))
    ;; naive $cap: just the state box (the get clause reads it). No generation stamp.
    (type $cap  (sub $val (struct (field $box (ref $ref))))))

  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (func $unbox (param $v (ref null $val)) (result i64)
    (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))
  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; the escaped thunk: performs `get` on the captured cap (reads cap.$box).
  (elem declare func $getThunk)
  (func $getThunk (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    ;; env index 0 = the captured $cap.  get = struct.get its box.
    (struct.get $ref 0 (struct.get $cap $box
      (ref.cast (ref $cap) (struct.get $env $hd (local.get $env))))))

  ;; installHandler: mints a state cell = 42, builds the $cap, returns a thunk closure over it.
  ;; Models `handle (state 42) (ret {get})` — the thunk ESCAPES with the cap.
  (func $installHandler (result (ref $clos))
    (local $cell (ref $ref))
    (local $cap (ref $cap))
    (local.set $cell (struct.new $ref (call $box (i64.const 42))))
    (local.set $cap (struct.new $cap (local.get $cell)))
    ;; the returned thunk captures the $cap in its env (index 0)
    (struct.new $clos (ref.func $getThunk)
      (struct.new $env (local.get $cap) (ref.null $env))))

  (func $run (result i64)
    (local $thunk (ref $clos))
    ;; handler region EXITS here — $installHandler returned; the cell is off any "stack".
    (local.set $thunk (call $installHandler))
    ;; force the escaped thunk at top level — the naive rep happily reads the dead box.
    (call $unbox (call_ref $fn (struct.get $clos $env (local.get $thunk)) (call $box (i64.const 0)) (struct.get $clos $code (local.get $thunk)))))

  (func $_start (export "_start")
    (call $printInt (call $run)))
  (func $printInt (param $n i64) (local $i i32) (local $d i64)
    (local.set $i (i32.const 32))
    (if (i64.eqz (local.get $n))
      (then (local.set $i (i32.sub (local.get $i) (i32.const 1))) (i32.store8 (local.get $i) (i32.const 48)))
      (else (block $done (loop $l
        (br_if $done (i64.eqz (local.get $n)))
        (local.set $d (i64.rem_u (local.get $n) (i64.const 10)))
        (local.set $i (i32.sub (local.get $i) (i32.const 1)))
        (i32.store8 (local.get $i) (i32.add (i32.const 48) (i32.wrap_i64 (local.get $d))))
        (local.set $n (i64.div_u (local.get $n) (i64.const 10)))
        (br $l)))))
    (i32.store8 (i32.const 32) (i32.const 10))
    (i32.store (i32.const 40) (local.get $i))
    (i32.store (i32.const 44) (i32.sub (i32.const 33) (local.get $i)))
    (drop (call $fd_write (i32.const 1) (i32.const 40) (i32.const 1) (i32.const 48))))
)
