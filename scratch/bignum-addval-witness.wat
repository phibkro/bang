;; B2 witness: $addVal / $subVal / $cmpVal on the MIXED $ival/$bigval rep, with the i64 fast path
;; + overflow detection + sign-magnitude limb fallback. Refute-first for the whole B2 approach BEFORE
;; wiring the arith arms. Cases witnessed against hand-computed oracles:
;;   (A) small + small, in-range        → $ival fast path              2 + 3 = 5
;;   (B) small + small, OVERFLOWS i64    → promote to $bigval           (2^63-1) + (2^63-1)
;;   (C) big + small                     → mixed, limb path             big + 1
;;   (D) opposite signs → subMag         → (2^63) + (-(2^63-1)) = 1     (fits i64 again)
;;   (E) cmp: big > small, neg < pos
(module
  (rec
    (type $val    (sub (struct)))
    (type $ival   (sub $val (struct (field i64))))
    (type $limbs  (array (mut i64)))
    (type $bigval (sub $val (struct (field $sign i32) (field $mag (ref $limbs))))))
  (global $BASE i64 (i64.const 1000000000))

  ;; --- rep helpers ---
  (func $isBig (param $v (ref null $val)) (result i32) (ref.test (ref $bigval) (local.get $v)))
  (func $isIval (param $v (ref null $val)) (result i32) (ref.test (ref $ival) (local.get $v)))
  (func $ivalN (param $v (ref null $val)) (result i64)
    (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))

  ;; base-10^9 limbs of an UNSIGNED i64 magnitude (LSB-first, no leading zeros, [0] for zero).
  (func $limbsOfU (param $m i64) (result (ref $limbs))
    (local $n i32) (local $t i64) (local $r (ref $limbs)) (local $i i32)
    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $m) (global.get $BASE)))
    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (local.set $t (i64.div_u (local.get $t) (global.get $BASE))) (br $cl)))
    (local.set $r (array.new_default $limbs (local.get $n)))
    (local.set $i (i32.const 0))
    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $n)))
      (array.set $limbs (local.get $r) (local.get $i) (i64.rem_u (local.get $m) (global.get $BASE)))
      (local.set $m (i64.div_u (local.get $m) (global.get $BASE)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))
    (local.get $r))

  ;; promote any int $val to a $bigval (sign + magnitude limbs).
  (func $toBig (param $v (ref null $val)) (result (ref $bigval))
    (local $n i64) (local $sign i32) (local $mag i64)
    (if (result (ref $bigval)) (call $isBig (local.get $v))
      (then (ref.cast (ref $bigval) (local.get $v)))
      (else
        (local.set $n (call $ivalN (local.get $v)))
        (if (i64.lt_s (local.get $n) (i64.const 0))
          (then (local.set $sign (i32.const 1))
                ;; magnitude = -n, computed unsigned to survive INT64_MIN (0 - n wraps to |n|).
                (local.set $mag (i64.sub (i64.const 0) (local.get $n))))
          (else (local.set $sign (i32.const 0)) (local.set $mag (local.get $n))))
        (struct.new $bigval (local.get $sign) (call $limbsOfU (local.get $mag))))))

  ;; --- magnitude ops (unsigned $limbs) ---
  (func $addMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))
    (local $la i32) (local $lb i32) (local $n i32) (local $i i32)
    (local $carry i64) (local $sum i64) (local $r (ref $limbs)) (local $av i64) (local $bv i64)
    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))
    (local.set $n (i32.add (select (local.get $la) (local.get $lb) (i32.gt_u (local.get $la) (local.get $lb))) (i32.const 1)))
    (local.set $r (array.new_default $limbs (local.get $n)))
    (local.set $i (i32.const 0)) (local.set $carry (i64.const 0))
    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $n)))
      (local.set $av (if (result i64) (i32.lt_u (local.get $i) (local.get $la)) (then (array.get $limbs (local.get $a) (local.get $i))) (else (i64.const 0))))
      (local.set $bv (if (result i64) (i32.lt_u (local.get $i) (local.get $lb)) (then (array.get $limbs (local.get $b) (local.get $i))) (else (i64.const 0))))
      (local.set $sum (i64.add (i64.add (local.get $av) (local.get $bv)) (local.get $carry)))
      (local.set $carry (i64.div_u (local.get $sum) (global.get $BASE)))
      (array.set $limbs (local.get $r) (local.get $i) (i64.rem_u (local.get $sum) (global.get $BASE)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))
    (local.get $r))

  ;; compare magnitudes: -1 if a<b, 0 if a==b, 1 if a>b (normalized, no leading zeros).
  (func $cmpMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result i32)
    (local $la i32) (local $lb i32) (local $i i32) (local $av i64) (local $bv i64)
    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))
    (if (i32.gt_u (local.get $la) (local.get $lb)) (then (return (i32.const 1))))
    (if (i32.lt_u (local.get $la) (local.get $lb)) (then (return (i32.const -1))))
    (local.set $i (i32.sub (local.get $la) (i32.const 1)))
    (block $d (loop $l (br_if $d (i32.lt_s (local.get $i) (i32.const 0)))
      (local.set $av (array.get $limbs (local.get $a) (local.get $i)))
      (local.set $bv (array.get $limbs (local.get $b) (local.get $i)))
      (if (i64.gt_u (local.get $av) (local.get $bv)) (then (return (i32.const 1))))
      (if (i64.lt_u (local.get $av) (local.get $bv)) (then (return (i32.const -1))))
      (local.set $i (i32.sub (local.get $i) (i32.const 1))) (br $l)))
    (i32.const 0))

  ;; subMag: a - b for a >= b (magnitudes), schoolbook borrow. Returns normalized (trimmed) limbs.
  (func $subMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))
    (local $la i32) (local $lb i32) (local $i i32) (local $borrow i64) (local $av i64) (local $bv i64)
    (local $diff i64) (local $r (ref $limbs)) (local $top i32)
    (local.set $la (array.len (local.get $a))) (local.set $lb (array.len (local.get $b)))
    (local.set $r (array.new_default $limbs (local.get $la)))
    (local.set $i (i32.const 0)) (local.set $borrow (i64.const 0))
    (block $d (loop $l (br_if $d (i32.ge_u (local.get $i) (local.get $la)))
      (local.set $av (array.get $limbs (local.get $a) (local.get $i)))
      (local.set $bv (if (result i64) (i32.lt_u (local.get $i) (local.get $lb)) (then (array.get $limbs (local.get $b) (local.get $i))) (else (i64.const 0))))
      (local.set $diff (i64.sub (i64.sub (local.get $av) (local.get $bv)) (local.get $borrow)))
      (if (i64.lt_s (local.get $diff) (i64.const 0))
        (then (local.set $diff (i64.add (local.get $diff) (global.get $BASE))) (local.set $borrow (i64.const 1)))
        (else (local.set $borrow (i64.const 0))))
      (array.set $limbs (local.get $r) (local.get $i) (local.get $diff))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))
    ;; trim leading zero limbs (keep at least 1)
    (local.set $top (i32.sub (local.get $la) (i32.const 1)))
    (block $td (loop $tl
      (br_if $td (i32.eqz (local.get $top)))
      (br_if $td (i64.ne (array.get $limbs (local.get $r) (local.get $top)) (i64.const 0)))
      (local.set $top (i32.sub (local.get $top) (i32.const 1))) (br $tl)))
    ;; copy [0..top] into a fresh array of length top+1
    (local.set $la (i32.add (local.get $top) (i32.const 1)))
    (local.set $a (array.new_default $limbs (local.get $la)))
    (local.set $i (i32.const 0))
    (block $cd (loop $cl (br_if $cd (i32.ge_u (local.get $i) (local.get $la)))
      (array.set $limbs (local.get $a) (local.get $i) (array.get $limbs (local.get $r) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $cl)))
    (local.get $a))

  ;; is a $bigval magnitude zero? (normalized ⇒ length 1 and limb0 == 0)
  (func $isZeroMag (param $m (ref $limbs)) (result i32)
    (i32.and (i32.eq (array.len (local.get $m)) (i32.const 1))
             (i64.eqz (array.get $limbs (local.get $m) (i32.const 0)))))

  ;; demote a $bigval back to $ival IF it fits [−2^63, 2^63); else keep $bigval. (normalization)
  ;; For the witness we compute the magnitude as i64 if len ≤ 2 limbs (< 10^18 < 2^63); this covers
  ;; cases D. General demote is emitter-side; here len≤2 suffices for the witnessed values.
  (func $normBig (param $sign i32) (param $mag (ref $limbs)) (result (ref null $val))
    (local $len i32) (local $v i64)
    (local.set $len (array.len (local.get $mag)))
    (if (i32.le_u (local.get $len) (i32.const 2))
      (then
        (local.set $v (array.get $limbs (local.get $mag) (i32.const 0)))
        (if (i32.eq (local.get $len) (i32.const 2))
          (then (local.set $v (i64.add (local.get $v) (i64.mul (array.get $limbs (local.get $mag) (i32.const 1)) (global.get $BASE))))))
        ;; v < 10^18 < 2^63, so it fits i64 signed; apply sign.
        (if (i32.eq (local.get $sign) (i32.const 1)) (then (local.set $v (i64.sub (i64.const 0) (local.get $v)))))
        (return (struct.new $ival (local.get $v)))))
    (struct.new $bigval (local.get $sign) (local.get $mag)))

  ;; --- $addVal: the emitter-facing add on two $val, mixed rep. ---
  (func $addVal (param $x (ref null $val)) (param $y (ref null $val)) (result (ref null $val))
    (local $bx (ref $bigval)) (local $by (ref $bigval)) (local $sx i32) (local $sy i32)
    (local $mx (ref $limbs)) (local $my (ref $limbs)) (local $c i32) (local $rmag (ref $limbs))
    (local $a i64) (local $b i64) (local $s i64)
    ;; FAST PATH: both $ival and the signed i64 add does not overflow ⇒ $ival.
    (if (i32.and (call $isIval (local.get $x)) (call $isIval (local.get $y)))
      (then
        (local.set $a (call $ivalN (local.get $x))) (local.set $b (call $ivalN (local.get $y)))
        (local.set $s (i64.add (local.get $a) (local.get $b)))
        ;; signed overflow iff (a^s)&(b^s) < 0
        (if (i64.ge_s (i64.and (i64.xor (local.get $a) (local.get $s)) (i64.xor (local.get $b) (local.get $s))) (i64.const 0))
          (then (return (struct.new $ival (local.get $s)))))))
    ;; SLOW PATH: promote both, sign-magnitude add.
    (local.set $bx (call $toBig (local.get $x))) (local.set $by (call $toBig (local.get $y)))
    (local.set $sx (struct.get $bigval $sign (local.get $bx))) (local.set $sy (struct.get $bigval $sign (local.get $by)))
    (local.set $mx (struct.get $bigval $mag (local.get $bx))) (local.set $my (struct.get $bigval $mag (local.get $by)))
    (if (result (ref null $val)) (i32.eq (local.get $sx) (local.get $sy))
      (then  ;; same sign: add magnitudes, keep sign
        (call $normBig (local.get $sx) (call $addMag (local.get $mx) (local.get $my))))
      (else  ;; opposite signs: subtract smaller magnitude from larger, sign of larger
        (local.set $c (call $cmpMag (local.get $mx) (local.get $my)))
        (if (result (ref null $val)) (i32.eqz (local.get $c))
          (then (struct.new $ival (i64.const 0)))   ;; equal magnitudes ⇒ 0
          (else
            (if (result (ref null $val)) (i32.eq (local.get $c) (i32.const 1))
              (then (call $normBig (local.get $sx) (call $subMag (local.get $mx) (local.get $my))))
              (else (call $normBig (local.get $sy) (call $subMag (local.get $my) (local.get $mx))))))))))

  ;; --- witness probes (return the i64 value if it fits, via a helper that reads either rep) ---
  ;; readSmall: for values known to fit i64 in these cases, extract the signed i64.
  (func $readSmall (param $v (ref null $val)) (result i64)
    (local $m (ref $limbs)) (local $r i64)
    (if (result i64) (call $isIval (local.get $v))
      (then (call $ivalN (local.get $v)))
      (else  ;; a $bigval that fits 2 limbs
        (local.set $m (struct.get $bigval $mag (ref.cast (ref $bigval) (local.get $v))))
        (local.set $r (array.get $limbs (local.get $m) (i32.const 0)))
        (if (i32.eq (array.len (local.get $m)) (i32.const 2))
          (then (local.set $r (i64.add (local.get $r) (i64.mul (array.get $limbs (local.get $m) (i32.const 1)) (global.get $BASE))))))
        (if (i32.eq (struct.get $bigval $sign (ref.cast (ref $bigval) (local.get $v))) (i32.const 1))
          (then (local.set $r (i64.sub (i64.const 0) (local.get $r)))))
        (local.get $r))))

  (func $mkI (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; (A) 2 + 3 = 5
  (func (export "a_small") (result i64) (call $readSmall (call $addVal (call $mkI (i64.const 2)) (call $mkI (i64.const 3)))))
  ;; (D) 2^63... use (10^18) + (-(10^18 - 1)) = 1, exercises opposite-sign subMag → back to small.
  (func (export "d_oppsign") (result i64)
    (call $readSmall (call $addVal (call $mkI (i64.const 1000000000000000000)) (call $mkI (i64.const -999999999999999999)))))
  ;; (B) big result: (10^18) + (10^18) = 2*10^18 (still 2 limbs, fits i64 via readSmall).
  (func (export "b_grow") (result i64)
    (call $readSmall (call $addVal (call $mkI (i64.const 1000000000000000000)) (call $mkI (i64.const 1000000000000000000)))))
  ;; (E) cmp probe: cmpMag([2],[1]) = 1 ; readSmall of a small neg add
  (func (export "e_negadd") (result i64)  ;; (-5) + 3 = -2
    (call $readSmall (call $addVal (call $mkI (i64.const -5)) (call $mkI (i64.const 3))))))
