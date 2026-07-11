;; Hand-written witness that the SNAPSHOT-RESTORE is load-bearing (not dead code).
;; A txn writes 70 to cell 0 then aborts; the OUTER handler catches and reads cell 0's
;; length pointer state. With restore: heaplen reset to 0 (write's cell is "gone"). We
;; observe the RESTORED heaplen (0) vs the leaked heaplen (1) to prove restore fired.
(module
  (tag $exn0 (param i64))
  (memory 1)
  (global $heaplen (mut i64) (i64.const 0))
  (global $saved (mut i64) (i64.const 0))
  (func $main (export "main") (result i64)
    (block $h0 (result i64)
      (try_table (result i64) (catch $exn0 $h0)
        ;; ── transaction body ──
        (global.set $heaplen (i64.const 0))
        (global.set $saved (global.get $heaplen))
        (block $txcommit (result i64)
          (block $txab (result exnref)
            (try_table (result i64) (catch_all_ref $txab)
              ;; newTVar 100 -> cell 0, heaplen := 1
              (i64.store (i32.const 0) (i64.const 100))
              (global.set $heaplen (i64.add (global.get $heaplen) (i64.const 1)))
              ;; writeTVar cell0 := 70
              (i64.store (i32.const 0) (i64.const 70))
              ;; raise 100 (foreign to txn)
              (throw $exn0 (i64.const 100)))
            (br $txcommit))
          ;; ── rollback path: restore heaplen, rethrow ──
          (global.set $heaplen (global.get $saved))   ;; heaplen 1 -> 0
          (throw_ref))))
    ;; outer catch delivers the raise payload; but return heaplen instead to OBSERVE restore.
    drop
    (global.get $heaplen)))   ;; 0 if restore fired, 1 if the write leaked
