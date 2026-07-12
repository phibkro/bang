;; C2 DIFFERENTIAL: the stamp must NOT trap on a LEGITIMATE (non-escaping) perform. Mirrors
;;   state 5 in get   — get runs INSIDE the handler region (id < liveTop) ⇒ returns 5, no trap.
;; Same $ref/$liveTop machinery as structured-stamp-witness.wat; the ONLY difference is the perform
;; happens before the handle's restore (inside M), so the gate passes. Prints 5.
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    (type $ref  (sub $val (struct (field $id i64) (field (mut (ref null $val))))))
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env))))))
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (global $liveTop (mut i64) (i64.const 0))
  (global $nextId  (mut i64) (i64.const 0))
  (func $lookup (param $e (ref null $env)) (param $n i32) (result (ref null $val))
    (block $done (loop $l (br_if $done (i32.eqz (local.get $n)))
      (local.set $e (struct.get $env $tl (local.get $e)))
      (local.set $n (i32.sub (local.get $n) (i32.const 1))) (br $l)))
    (struct.get $env $hd (local.get $e)))
  (func $unbox (param $v (ref null $val)) (result i64) (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))
  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; the get performed INSIDE M — same gate, but liveTop still covers the cap (id < liveTop) ⇒ passes.
  (func $getInline (param $c (ref $ref)) (result (ref null $val))
    (if (i64.ge_s (struct.get $ref $id (local.get $c)) (global.get $liveTop)) (then (unreachable)))
    (struct.get $ref 1 (local.get $c)))

  (func $_start (export "_start") (local $env0 (ref null $env)) (local $e2 (ref null $env)) (local $myId i64) (local $r (ref null $val))
    (local.set $env0 (ref.null $env))
    (local.set $r (block (result (ref null $val))
      (local.set $myId (global.get $nextId))
      (global.set $nextId (i64.add (global.get $nextId) (i64.const 1)))
      (global.set $liveTop (global.get $nextId))
      (local.set $e2 (struct.new $env (struct.new $ref (local.get $myId) (call $box (i64.const 5))) (local.get $env0)))
      ;; M = get (INLINE, inside the region): gate passes (id < liveTop)
      (block (result (ref null $val))
        (local.set $r (call $getInline (ref.cast (ref $ref) (call $lookup (local.get $e2) (i32.const 0)))))
        (global.set $liveTop (local.get $myId))   ;; restore AFTER M
        (local.get $r))))
    (call $printInt (call $unbox (local.get $r))))

  (func $printInt (param $n i64) (local $i i32) (local $d i64)
    (local.set $i (i32.const 32))
    (if (i64.eqz (local.get $n)) (then (local.set $i (i32.sub (local.get $i) (i32.const 1))) (i32.store8 (local.get $i) (i32.const 48)))
      (else (block $done (loop $l (br_if $done (i64.eqz (local.get $n)))
        (local.set $d (i64.rem_u (local.get $n) (i64.const 10)))
        (local.set $i (i32.sub (local.get $i) (i32.const 1)))
        (i32.store8 (local.get $i) (i32.add (i32.const 48) (i32.wrap_i64 (local.get $d))))
        (local.set $n (i64.div_u (local.get $n) (i64.const 10))) (br $l)))))
    (i32.store8 (i32.const 32) (i32.const 10))
    (i32.store (i32.const 40) (local.get $i)) (i32.store (i32.const 44) (i32.sub (i32.const 33) (local.get $i)))
    (drop (call $fd_write (i32.const 1) (i32.const 40) (i32.const 1) (i32.const 48))))
)
