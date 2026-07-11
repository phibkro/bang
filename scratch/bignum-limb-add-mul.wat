;; Bignum limb witness (task: bignum rung, PHASE 1 refute-first).
;; Goal: prove the CORE limb routines run on wasmtime 45 BEFORE committing to the design.
;;
;; REP DECISION being witnessed: sign-magnitude, magnitude = a WasmGC array of i64 LIMBS in
;;   base 10^9 (BASE = 1_000_000_000), LEAST-significant limb first. Two rationales:
;;     (1) base 10^9 makes DECIMAL READBACK trivial (each limb is 9 decimal digits) — the harness
;;         compares Lean-Int decimal BYTES, so decimal rendering is part of the rep, not an afterthought.
;;     (2) a product of two base-10^9 limbs is < 10^18 < 2^63, so limb*limb + carry fits in i64
;;         (u63 headroom) with NO 128-bit intermediate — schoolbook mul works in plain i64.
;;
;; This witness computes, with unsigned magnitude arrays (sign handled at the $val layer, not here):
;;   A = 9_999_999_999  (= [999999999, 9]   — just past 10^9, two limbs; also > 2^33)
;;   B = 1_000_000_001  (= [1, 1])
;;   A + B = 11_000_000_000              (limbs [0, 11, 0])  verified in Lean
;;   A * B = 9_999_999_999 * 1_000_000_001 = 10_000_000_008_999_999_999
;;         (> 2^63 = 9.22e18 — the real bignum witness; a plain i64 mul would WRAP here).
;;   Expected A*B limbs (base 1e9, LSB first): [999999999, 8, 10, 0]  (len 4, verified in Lean:
;;     limb0 = P%1e9 = 999999999 · limb1 = 8 · limb2 = 10 · limb3 = 0). The top limb is 0 (schoolbook
;;     over-allocates la+lb; a real emitter TRIMS trailing zero limbs — that trim is in the design note).
;;   We verify by returning individual limbs as i64s (wasmtime --invoke) AND by decimal readback below.

(module
  (rec
    (type $limbs (array (mut i64))))   ;; magnitude: i64 limbs, base 1e9, LSB first

  (global $BASE i64 (i64.const 1000000000))

  ;; --- limb ADD (unsigned magnitudes, schoolbook, result length = max(len)+1) ---
  ;; returns a fresh $limbs of length max(la,lb)+1 (top limb may be 0).
  (func $addMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))
    (local $la i32) (local $lb i32) (local $n i32) (local $i i32)
    (local $carry i64) (local $sum i64) (local $r (ref $limbs)) (local $av i64) (local $bv i64)
    (local.set $la (array.len (local.get $a)))
    (local.set $lb (array.len (local.get $b)))
    (local.set $n (select (local.get $la) (local.get $lb) (i32.gt_u (local.get $la) (local.get $lb))))
    (local.set $n (i32.add (local.get $n) (i32.const 1)))
    (local.set $r (array.new_default $limbs (local.get $n)))
    (local.set $i (i32.const 0))
    (local.set $carry (i64.const 0))
    (block $done (loop $l
      (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
      (local.set $av (if (result i64) (i32.lt_u (local.get $i) (local.get $la))
                        (then (array.get $limbs (local.get $a) (local.get $i)))
                        (else (i64.const 0))))
      (local.set $bv (if (result i64) (i32.lt_u (local.get $i) (local.get $lb))
                        (then (array.get $limbs (local.get $b) (local.get $i)))
                        (else (i64.const 0))))
      (local.set $sum (i64.add (i64.add (local.get $av) (local.get $bv)) (local.get $carry)))
      (local.set $carry (i64.div_u (local.get $sum) (global.get $BASE)))
      (array.set $limbs (local.get $r) (local.get $i)
        (i64.rem_u (local.get $sum) (global.get $BASE)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $r))

  ;; --- limb MUL (unsigned magnitudes, schoolbook O(la*lb), base 1e9 fits in i64) ---
  (func $mulMag (param $a (ref $limbs)) (param $b (ref $limbs)) (result (ref $limbs))
    (local $la i32) (local $lb i32) (local $n i32) (local $i i32) (local $j i32)
    (local $r (ref $limbs)) (local $carry i64) (local $cur i64) (local $ai i64)
    (local.set $la (array.len (local.get $a)))
    (local.set $lb (array.len (local.get $b)))
    (local.set $n (i32.add (local.get $la) (local.get $lb)))
    (local.set $r (array.new_default $limbs (local.get $n)))
    (local.set $i (i32.const 0))
    (block $outer_done (loop $outer
      (br_if $outer_done (i32.ge_u (local.get $i) (local.get $la)))
      (local.set $ai (array.get $limbs (local.get $a) (local.get $i)))
      (local.set $carry (i64.const 0))
      (local.set $j (i32.const 0))
      (block $inner_done (loop $inner
        (br_if $inner_done (i32.ge_u (local.get $j) (local.get $lb)))
        ;; cur = r[i+j] + ai*b[j] + carry.  ai,b[j] < 1e9 ⇒ product < 1e18 < 2^63; + r + carry (<1e9) safe.
        (local.set $cur
          (i64.add
            (i64.add
              (array.get $limbs (local.get $r) (i32.add (local.get $i) (local.get $j)))
              (i64.mul (local.get $ai) (array.get $limbs (local.get $b) (local.get $j))))
            (local.get $carry)))
        (array.set $limbs (local.get $r) (i32.add (local.get $i) (local.get $j))
          (i64.rem_u (local.get $cur) (global.get $BASE)))
        (local.set $carry (i64.div_u (local.get $cur) (global.get $BASE)))
        (local.set $j (i32.add (local.get $j) (i32.const 1)))
        (br $inner)))
      ;; propagate the final carry into r[i+lb]
      (array.set $limbs (local.get $r) (i32.add (local.get $i) (local.get $lb))
        (i64.add (array.get $limbs (local.get $r) (i32.add (local.get $i) (local.get $lb)))
                 (local.get $carry)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $outer)))
    (local.get $r))

  ;; --- helpers to build the two witness inputs ---
  (func $mkA (result (ref $limbs))   ;; 9_999_999_999 = [999999999, 9]
    (local $r (ref $limbs))
    (local.set $r (array.new_default $limbs (i32.const 2)))
    (array.set $limbs (local.get $r) (i32.const 0) (i64.const 999999999))
    (array.set $limbs (local.get $r) (i32.const 1) (i64.const 9))
    (local.get $r))
  (func $mkB (result (ref $limbs))   ;; 1_000_000_001 = [1, 1]
    (local $r (ref $limbs))
    (local.set $r (array.new_default $limbs (i32.const 2)))
    (array.set $limbs (local.get $r) (i32.const 0) (i64.const 1))
    (array.set $limbs (local.get $r) (i32.const 1) (i64.const 1))
    (local.get $r))

  ;; --- probes: return individual limbs of A+B and A*B so the harness can verify ---
  ;; A+B expected limbs: [0, 11, 0]  (len 3, top limb 0)
  (func (export "add_limb0") (result i64)
    (array.get $limbs (call $addMag (call $mkA) (call $mkB)) (i32.const 0)))
  (func (export "add_limb1") (result i64)
    (array.get $limbs (call $addMag (call $mkA) (call $mkB)) (i32.const 1)))

  ;; A*B expected limbs (LSB first): [999999999, 9, 999999999, 9999]  (len 4)
  (func (export "mul_limb0") (result i64)
    (array.get $limbs (call $mulMag (call $mkA) (call $mkB)) (i32.const 0)))
  (func (export "mul_limb1") (result i64)
    (array.get $limbs (call $mulMag (call $mkA) (call $mkB)) (i32.const 1)))
  (func (export "mul_limb2") (result i64)
    (array.get $limbs (call $mulMag (call $mkA) (call $mkB)) (i32.const 2)))
  (func (export "mul_limb3") (result i64)
    (array.get $limbs (call $mulMag (call $mkA) (call $mkB)) (i32.const 3)))
  (func (export "mul_len") (result i32)
    (array.len (call $mulMag (call $mkA) (call $mkB))))

  ;; --- DECIMAL READBACK witness (load-bearing: the harness compares Lean-Int decimal BYTES) ---
  ;; Base-1e9 makes readback trivial: find the top NON-ZERO limb, render it bare (no pad), then
  ;; render every lower limb zero-padded to EXACTLY 9 digits, concatenated. Here we write the
  ;; decimal ASCII of A*B into linear memory at offset 0 and export the byte length; a companion
  ;; probe returns a chosen byte so the harness can spot-check. Expected string:
  ;;   "10000000008999999999"  (20 bytes) — top limb 10 (2 digits) ++ "000000008" ++ "999999999".
  (memory (export "mem") 1)

  ;; write 9 zero-padded decimal digits of $v at mem[$off..$off+9); returns nothing.
  (func $put9 (param $v i64) (param $off i32)
    (local $i i32)
    (local.set $i (i32.const 8))
    (block $done (loop $l
      (i32.store8 (i32.add (local.get $off) (local.get $i))
        (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))
      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))
      (br_if $done (i32.eqz (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (br $l))))

  ;; write the bare (un-padded) decimal of $v at $off; returns the number of digits written.
  (func $putBare (param $v i64) (param $off i32) (result i32)
    (local $n i32) (local $t i64) (local $i i32)
    ;; count digits
    (local.set $n (i32.const 1)) (local.set $t (i64.div_u (local.get $v) (i64.const 10)))
    (block $cd (loop $cl (br_if $cd (i64.eqz (local.get $t)))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (local.set $t (i64.div_u (local.get $t) (i64.const 10))) (br $cl)))
    (local.set $i (i32.sub (local.get $n) (i32.const 1)))
    (block $done (loop $l
      (i32.store8 (i32.add (local.get $off) (local.get $i))
        (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $v) (i64.const 10)))))
      (local.set $v (i64.div_u (local.get $v) (i64.const 10)))
      (br_if $done (i32.eqz (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $n))

  ;; render A*B to decimal in mem@0; return total byte length (expect 20).
  (func $render (result i32)
    (local $m (ref $limbs)) (local $top i32) (local $off i32) (local $i i32)
    (local.set $m (call $mulMag (call $mkA) (call $mkB)))
    ;; find top non-zero limb index
    (local.set $top (i32.sub (array.len (local.get $m)) (i32.const 1)))
    (block $found (loop $fl
      (br_if $found (i64.ne (array.get $limbs (local.get $m) (local.get $top)) (i64.const 0)))
      (br_if $found (i32.eqz (local.get $top)))
      (local.set $top (i32.sub (local.get $top) (i32.const 1))) (br $fl)))
    ;; bare top limb
    (local.set $off (call $putBare (array.get $limbs (local.get $m) (local.get $top)) (i32.const 0)))
    ;; each lower limb, zero-padded to 9
    (local.set $i (i32.sub (local.get $top) (i32.const 1)))
    (block $ld (loop $ll
      (br_if $ld (i32.lt_s (local.get $i) (i32.const 0)))
      (call $put9 (array.get $limbs (local.get $m) (local.get $i)) (local.get $off))
      (local.set $off (i32.add (local.get $off) (i32.const 9)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1))) (br $ll)))
    (local.get $off))

  (func (export "dec_len") (result i32) (call $render))
  ;; return byte at index $k (after render) so the harness can read the string char-by-char
  (func (export "dec_byte") (param $k i32) (result i32)
    (drop (call $render)) (i32.load8_u (local.get $k))))

