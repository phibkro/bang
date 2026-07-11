;; B3 witness: $mulVal on the mixed $ival/$bigval rep. i64 FAST PATH with overflow detection (no
;; mul_high in wasm) + sign-magnitude $mulMag fallback. Refute-first before wiring the mul arm.
;;
;; Overflow detection for signed i64 a*b (the classic no-widening check):
;;   p = a *(wrapping) b
;;   overflow iff  a != 0 AND (p / a != b  OR  (a == -1 AND b == INT64_MIN))
;;   (the a==-1 & b==MIN case: p/a == b arithmetically but the true product 2^63 is unrepresentable.)
;; If no overflow ⇒ $ival p. Else promote both to $bigval, $mulMag magnitudes, sign = sx xor sy.
;;
;; Cases (hand oracle):
;;   (A) 6 * 7 = 42                          (fast)
;;   (B) (10^10) * (10^10) = 10^20           (OVERFLOWS i64 ⇒ bignum)   check via readback below
;;   (C) (-6) * 7 = -42                      (fast, negative)
;;   (D) (3*10^9) * (4*10^9) = 1.2*10^19     (> 2^63 ⇒ bignum)
;;   (E) 0 * (big) = 0
(module
  (rec
    (type $val    (sub (struct)))
    (type $ival   (sub $val (struct (field i64))))
    (type $limbs  (array (mut i64)))
    (type $bigval (sub $val (struct (field $sign i32) (field $mag (ref $limbs))))))
  (global $BASE i64 (i64.const 1000000000))
  (memory (export "mem") 1)
  (global $cur (mut i32) (i32.const 0))

  (func $isBig (param $v (ref null $val)) (result i32) (ref.test (ref $bigval) (local.get $v)))
  (func $isIval (param $v (ref null $val)) (result i32) (ref.test (ref $ival) (local.get $v)))
  (func $ivalN (param $v (ref null $val)) (result i64) (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))

  (func $limbsOfU (param $m i64) (result (ref $limbs))
    (local $n i32) (local $t i64) (local $r (ref $limbs)) (local $i i32)
    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $m) (global.get $BASE)))
    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (local.set $t (i64.div_u (local.get $t) (global.get $BASE))) (br $cl)))
    (local.set $r (array.new_default $limbs (local.get $n))) (local.set $i (i32.const 0))
    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $n)))
      (array.set $limbs (local.get $r) (local.get $i) (i64.rem_u (local.get $m) (global.get $BASE)))
      (local.set $m (i64.div_u (local.get $m) (global.get $BASE)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))
    (local.get $r))

  (func $toBig (param $v (ref null $val)) (result (ref $bigval))
    (local $n i64) (local $sign i32) (local $mag i64)
    (if (result (ref $bigval)) (call $isBig (local.get $v))
      (then (ref.cast (ref $bigval) (local.get $v)))
      (else
        (local.set $n (call $ivalN (local.get $v)))
        (if (i64.lt_s (local.get $n) (i64.const 0))
          (then (local.set $sign (i32.const 1)) (local.set $mag (i64.sub (i64.const 0) (local.get $n))))
          (else (local.set $sign (i32.const 0)) (local.set $mag (local.get $n))))
        (struct.new $bigval (local.get $sign) (call $limbsOfU (local.get $mag))))))

  (func $trim (param $r (ref $limbs)) (result (ref $limbs))
    (local $top i32) (local $n i32) (local $i i32) (local $o (ref $limbs))
    (local.set $top (i32.sub (array.len (local.get $r)) (i32.const 1)))
    (block $td (loop $tl (br_if $td (i32.eqz (local.get $top)))
      (br_if $td (i64.ne (array.get $limbs (local.get $r) (local.get $top)) (i64.const 0)))
      (local.set $top (i32.sub (local.get $top) (i32.const 1))) (br $tl)))
    (local.set $n (i32.add (local.get $top) (i32.const 1)))
    (if (i32.eq (local.get $n) (array.len (local.get $r))) (then (return (local.get $r))))
    (local.set $o (array.new_default $limbs (local.get $n))) (local.set $i (i32.const 0))
    (block $cd (loop $cl (br_if $cd (i32.ge_u (local.get $i) (local.get $n)))
      (array.set $limbs (local.get $o) (local.get $i) (array.get $limbs (local.get $r) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $cl)))
    (local.get $o))

  ;; schoolbook $mulMag (base 1e9, limb·limb < 1e18 < 2^63).
  (func $mulMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))
    (local $la i32) (local $lb i32) (local $n i32) (local $i i32) (local $j i32)
    (local $r (ref $limbs)) (local $carry i64) (local $cur i64) (local $ai i64)
    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))
    (local.set $n (i32.add (local.get $la) (local.get $lb)))
    (local.set $r (array.new_default $limbs (local.get $n)))
    (local.set $i (i32.const 0))
    (block $od (loop $ol (br_if $od (i32.ge_u (local.get $i) (local.get $la)))
      (local.set $ai (array.get $limbs (local.get $a) (local.get $i)))
      (local.set $carry (i64.const 0)) (local.set $j (i32.const 0))
      (block $id (loop $il (br_if $id (i32.ge_u (local.get $j) (local.get $lb)))
        (local.set $cur (i64.add (i64.add
          (array.get $limbs (local.get $r) (i32.add (local.get $i) (local.get $j)))
          (i64.mul (local.get $ai) (array.get $limbs (local.get $b) (local.get $j))))
          (local.get $carry)))
        (array.set $limbs (local.get $r) (i32.add (local.get $i) (local.get $j)) (i64.rem_u (local.get $cur) (global.get $BASE)))
        (local.set $carry (i64.div_u (local.get $cur) (global.get $BASE)))
        (local.set $j (i32.add (local.get $j) (i32.const 1))) (br $il)))
      (array.set $limbs (local.get $r) (i32.add (local.get $i) (local.get $lb))
        (i64.add (array.get $limbs (local.get $r) (i32.add (local.get $i) (local.get $lb))) (local.get $carry)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $ol)))
    (call $trim (local.get $r)))

  (func $isZeroVal (param $v (ref null $val)) (result i32)
    (if (result i32) (call $isIval (local.get $v))
      (then (i64.eqz (call $ivalN (local.get $v))))
      (else (i32.and (i32.eq (array.len (struct.get $bigval $mag (ref.cast (ref $bigval) (local.get $v)))) (i32.const 1))
                     (i64.eqz (array.get $limbs (struct.get $bigval $mag (ref.cast (ref $bigval) (local.get $v))) (i32.const 0)))))))

  (func $mulVal (param $x (ref null $val)) (param $y (ref null $val)) (result (ref null $val))
    (local $a i64) (local $b i64) (local $p i64) (local $bx (ref $bigval)) (local $by (ref $bigval))
    (local $sx i32) (local $sy i32)
    ;; zero shortcut (keeps sign canonical)
    (if (i32.or (call $isZeroVal (local.get $x)) (call $isZeroVal (local.get $y)))
      (then (return (struct.new $ival (i64.const 0)))))
    ;; FAST PATH: both $ival, product doesn't overflow.
    (if (i32.and (call $isIval (local.get $x)) (call $isIval (local.get $y)))
      (then
        (local.set $a (call $ivalN (local.get $x))) (local.set $b (call $ivalN (local.get $y)))
        (local.set $p (i64.mul (local.get $a) (local.get $b)))
        ;; no overflow iff  p/a == b  AND NOT (a==-1 && b==INT64_MIN)
        (if (i32.and
              (i64.eq (i64.div_s (local.get $p) (local.get $a)) (local.get $b))
              (i32.eqz (i32.and (i64.eq (local.get $a) (i64.const -1)) (i64.eq (local.get $b) (i64.const -9223372036854775808)))))
          (then (return (struct.new $ival (local.get $p)))))))
    ;; SLOW PATH: promote, mulMag magnitudes, sign = sx xor sy.
    (local.set $bx (call $toBig (local.get $x))) (local.set $by (call $toBig (local.get $y)))
    (local.set $sx (struct.get $bigval $sign (local.get $bx))) (local.set $sy (struct.get $bigval $sign (local.get $by)))
    (struct.new $bigval (i32.xor (local.get $sx) (local.get $sy))
      (call $mulMag (struct.get $bigval $mag (local.get $bx)) (struct.get $bigval $mag (local.get $by)))))

  ;; --- decimal readback (for big results) + small reader (for fast-path results) ---
  (func $put9 (param $v i64) (local $i i32) (local $start i32)
    (local.set $start (global.get $cur)) (global.set $cur (i32.add (global.get $cur) (i32.const 9)))
    (local.set $i (i32.const 8))
    (block $done (loop $l
      (i32.store8 (i32.add (local.get $start) (local.get $i)) (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))
      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))
      (br_if $done (i32.eqz (local.get $i))) (local.set $i (i32.sub (local.get $i) (i32.const 1))) (br $l))))
  (func $putBare (param $v i64) (local $n i32) (local $t i64) (local $i i32) (local $start i32)
    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $v) (i64.const 10)))
    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))
      (local.set $n (i32.add (local.get $n) (i32.const 1))) (local.set $t (i64.div_u (local.get $t) (i64.const 10))) (br $cl)))
    (local.set $start (global.get $cur)) (global.set $cur (i32.add (global.get $cur) (local.get $n)))
    (local.set $i (i32.sub (local.get $n) (i32.const 1)))
    (block $done (loop $l
      (i32.store8 (i32.add (local.get $start) (local.get $i)) (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))
      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))
      (br_if $done (i32.eqz (local.get $i))) (local.set $i (i32.sub (local.get $i) (i32.const 1))) (br $l))))
  (func $emit (param $v (ref null $val)) (local $b (ref $bigval)) (local $m (ref $limbs)) (local $i i32) (local $n i64)
    (global.set $cur (i32.const 0))
    (if (call $isIval (local.get $v))
      (then
        (local.set $n (call $ivalN (local.get $v)))
        (if (i64.lt_s (local.get $n) (i64.const 0)) (then (i32.store8 (global.get $cur) (i32.const 45)) (global.set $cur (i32.add (global.get $cur) (i32.const 1))) (local.set $n (i64.sub (i64.const 0) (local.get $n)))))
        (call $putBare (local.get $n)) (return)))
    (local.set $b (ref.cast (ref $bigval) (local.get $v)))
    (if (i32.eq (struct.get $bigval $sign (local.get $b)) (i32.const 1)) (then (i32.store8 (global.get $cur) (i32.const 45)) (global.set $cur (i32.add (global.get $cur) (i32.const 1)))))
    (local.set $m (struct.get $bigval $mag (local.get $b)))
    (local.set $i (i32.sub (array.len (local.get $m)) (i32.const 1)))
    (call $putBare (array.get $limbs (local.get $m) (local.get $i)))
    (local.set $i (i32.sub (local.get $i) (i32.const 1)))
    (block $d (loop $l (br_if $d (i32.lt_s (local.get $i) (i32.const 0)))
      (call $put9 (array.get $limbs (local.get $m) (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1))) (br $l))))

  (func $mkI (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; render probes: each computes the product, renders to mem, returns length + bytes.
  (func $rA (result i32) (call $emit (call $mulVal (call $mkI (i64.const 6)) (call $mkI (i64.const 7)))) (global.get $cur))
  (func $rB (result i32) (call $emit (call $mulVal (call $mkI (i64.const 10000000000)) (call $mkI (i64.const 10000000000)))) (global.get $cur))
  (func $rC (result i32) (call $emit (call $mulVal (call $mkI (i64.const -6)) (call $mkI (i64.const 7)))) (global.get $cur))
  (func $rD (result i32) (call $emit (call $mulVal (call $mkI (i64.const 3000000000)) (call $mkI (i64.const 4000000000)))) (global.get $cur))
  (func (export "lenA") (result i32) (call $rA))
  (func (export "lenB") (result i32) (call $rB))
  (func (export "lenC") (result i32) (call $rC))
  (func (export "lenD") (result i32) (call $rD))
  (func (export "byteA") (param $k i32) (result i32) (drop (call $rA)) (i32.load8_u (local.get $k)))
  (func (export "byteB") (param $k i32) (result i32) (drop (call $rB)) (i32.load8_u (local.get $k)))
  (func (export "byteC") (param $k i32) (result i32) (drop (call $rC)) (i32.load8_u (local.get $k)))
  (func (export "byteD") (param $k i32) (result i32) (drop (call $rD)) (i32.load8_u (local.get $k))))
