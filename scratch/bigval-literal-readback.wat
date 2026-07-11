;; B1 witness: a $bigval LITERAL round-trips to decimal via $emitBig (no arithmetic).
;; Value: 99999999999999999999 (> 2^63) — limbs base 1e9, LSB first: [999999999, 999999999, 99].
;;   check: 99*10^18 + 999999999*10^9 + 999999999 = 99999999999999999999. Sign 0 (non-negative).
;; The printer walks: top limb 99 bare, then 999999999 %09d, then 999999999 %09d ⇒
;;   "99" ++ "999999999" ++ "999999999" = "99999999999999999999". This is exactly the $emitBig
;; the emitter will inline; here we build the literal with array.new_fixed and render to mem.
(module
  (rec
    (type $val    (sub (struct)))
    (type $limbs  (array (mut i64)))
    (type $bigval (sub $val (struct (field $sign i32) (field $mag (ref $limbs))))))
  (memory (export "mem") 1)
  (global $cur (mut i32) (i32.const 0))

  (func $emitByte (param $b i32)
    (i32.store8 (global.get $cur) (local.get $b))
    (global.set $cur (i32.add (global.get $cur) (i32.const 1))))

  ;; write 9 zero-padded decimal digits of $v.
  (func $put9 (param $v i64) (local $i i32) (local $start i32)
    (local.set $start (global.get $cur))
    (global.set $cur (i32.add (global.get $cur) (i32.const 9)))
    (local.set $i (i32.const 8))
    (block $done (loop $l
      (i32.store8 (i32.add (local.get $start) (local.get $i))
        (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))
      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))
      (br_if $done (i32.eqz (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (br $l))))

  ;; write the bare (un-padded) decimal of $v (top limb).
  (func $putBare (param $v i64)
    (local $n i32) (local $t i64) (local $i i32) (local $start i32)
    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $v) (i64.const 10)))
    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (local.set $t (i64.div_u (local.get $t) (i64.const 10))) (br $cl)))
    (local.set $start (global.get $cur))
    (global.set $cur (i32.add (global.get $cur) (local.get $n)))
    (local.set $i (i32.sub (local.get $n) (i32.const 1)))
    (block $done (loop $l
      (i32.store8 (i32.add (local.get $start) (local.get $i))
        (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))
      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))
      (br_if $done (i32.eqz (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (br $l))))

  ;; $emitBig: render a $bigval to decimal at mem (sign prefix, top bare, rest %09d).
  (func $emitBig (param $b (ref $bigval))
    (local $m (ref $limbs)) (local $i i32)
    (if (i32.eq (struct.get $bigval $sign (local.get $b)) (i32.const 1))
      (then (call $emitByte (i32.const 45))))   ;; '-'
    (local.set $m (struct.get $bigval $mag (local.get $b)))
    ;; top limb bare
    (local.set $i (i32.sub (array.len (local.get $m)) (i32.const 1)))
    (call $putBare (array.get $limbs (local.get $m) (local.get $i)))
    ;; rest %09d, high→low
    (local.set $i (i32.sub (local.get $i) (i32.const 1)))
    (block $d (loop $l
      (br_if $d (i32.lt_s (local.get $i) (i32.const 0)))
      (call $put9 (array.get $limbs (local.get $m) (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (br $l))))

  ;; the LITERAL 99999999999999999999 as a $bigval (sign 0, mag [999999999,999999999,99]).
  (func $mkLit (result (ref $bigval))
    (struct.new $bigval (i32.const 0)
      (array.new_fixed $limbs 3 (i64.const 999999999) (i64.const 999999999) (i64.const 99))))

  (func $render (result i32)
    (global.set $cur (i32.const 0))
    (call $emitBig (call $mkLit))
    (global.get $cur))                          ;; total byte length (expect 20)
  (func (export "render") (result i32) (call $render))
  ;; each byte invocation renders fresh (module state resets between --invoke calls).
  (func (export "byte") (param $k i32) (result i32)
    (drop (call $render)) (i32.load8_u (local.get $k))))
