;; Minimal HAND-UNIFIED witness (rung-5 Part 2, deliverable (d)):
;; a CLOSURE that reads a STATE cell — the exact program the two disjoint lowerings refuse today
;; (inline rungs would want a compile-time .state Slot; GC rung 4 has no effect arm).
;;
;; Program (kernel shape):
;;   handle (state ℓ 7) {
;;     let f = { fun _ => get }          -- a CLOSURE capturing the state cap
;;     ($f ()) + 1                       -- force it, read the cell (7), add 1  ⇒  8
;;   }
;;
;; Unified rep decision demonstrated: the state cell is a GC $val SLOT in the env cons-list (NOT a
;; bare wasm local), so a closure capturing the env can read it via $lookup — the SAME env-list rung 4
;; uses for values. "get" = read the cell $val; "put" would overwrite the slot's contents. NO
;; try_table, NO reified continuation (one-shot in-place resume, ADR-0025 D1). The cell is a mutable
;; box ($ref) so put mutates in place while the closure holds the same reference.
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    (type $ref  (sub $val (struct (field (mut (ref null $val))))))   ;; a mutable state CELL as a $val
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env))))))

  (func $lookup (param $e (ref null $env)) (param $n i32) (result (ref null $val))
    (block $done (loop $l
      (br_if $done (i32.eqz (local.get $n)))
      (local.set $e (struct.get $env $tl (local.get $e)))
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br $l)))
    (struct.get $env $hd (local.get $e)))

  (elem declare func $fn0)

  ;; $fn0 = the closure { fun _ => get }.  Its captured env has the state CELL at index 0.
  ;; "get" reads the cell's current $val (resume in place — the cell IS the env slot, a $ref box).
  (func $fn0 (type $fn) (param $env0 (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    ;; This thunk-shaped closure ignores its arg; the state CELL is at captured-env index 0.
    (struct.get $ref 0 (ref.cast (ref $ref) (call $lookup (local.get $env0) (i32.const 0)))))

  (func $main (export "main") (result i64)
    (local $env (ref null $env))
    (local $cell (ref $ref))
    (local $clos (ref $clos))
    ;; handle (state 7): the cell is a $ref box holding (ival 7), pushed as env slot 0.
    (local.set $cell (struct.new $ref (struct.new $ival (i64.const 7))))
    (local.set $env (struct.new $env (local.get $cell) (ref.null $env)))
    ;; f = closure capturing this env
    (local.set $clos (struct.new $clos (ref.func $fn0) (local.get $env)))
    ;; ($f ()) + 1  — call_ref the closure with a dummy arg, read the returned ival, add 1
    (i64.add
      (struct.get $ival 0 (ref.cast (ref $ival)
        (call_ref $fn (struct.get $clos $env (local.get $clos))
                       (ref.null $val)
                       (struct.get $clos $code (local.get $clos)))))
      (i64.const 1)))
)
