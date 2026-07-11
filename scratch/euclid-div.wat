;; B0 witness: the Euclidean-division i64 sequence the emitter will produce.
;; Kernel div = Int.ediv (remainder ≥ 0); wasm div_s is truncated. Fixup (verified in
;; scratch/EuclidDivProbe.lean against the oracle):
;;   if b == 0: 0
;;   else: qt = a div_s b; rt = a rem_s b; if rt < 0 then (b>0 ? qt-1 : qt+1) else qt
;; This witness needs SCRATCH LOCALS for a and b (div_s + rem_s each consume operands), so the
;; emitted form uses two locals — NOT the current bare-inline emitDiv (which duplicated eb because
;; it only tested eqz once). The emitter change threads two fresh i64 locals per div site.
(module
  (func $ediv (param $a i64) (param $b i64) (result i64)
    (local $qt i64) (local $rt i64)
    (if (result i64) (i64.eqz (local.get $b))
      (then (i64.const 0))
      (else
        (local.set $qt (i64.div_s (local.get $a) (local.get $b)))
        (local.set $rt (i64.rem_s (local.get $a) (local.get $b)))
        (if (result i64) (i64.lt_s (local.get $rt) (i64.const 0))
          (then
            (if (result i64) (i64.gt_s (local.get $b) (i64.const 0))
              (then (i64.sub (local.get $qt) (i64.const 1)))
              (else (i64.add (local.get $qt) (i64.const 1)))))
          (else (local.get $qt))))))
  (func (export "d_7_2")    (result i64) (call $ediv (i64.const 7)  (i64.const 2)))    ;; 3
  (func (export "d_n7_2")   (result i64) (call $ediv (i64.const -7) (i64.const 2)))    ;; -4
  (func (export "d_7_n2")   (result i64) (call $ediv (i64.const 7)  (i64.const -2)))   ;; -3
  (func (export "d_n7_n2")  (result i64) (call $ediv (i64.const -7) (i64.const -2)))   ;; 4
  (func (export "d_5_0")    (result i64) (call $ediv (i64.const 5)  (i64.const 0)))    ;; 0
  (func (export "d_n1_2")   (result i64) (call $ediv (i64.const -1) (i64.const 2)))    ;; -1
  (func (export "d_1_n2")   (result i64) (call $ediv (i64.const 1)  (i64.const -2))))  ;; 0
