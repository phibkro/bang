;; C2 STRUCTURED witness: does the $liveTop bump/restore work INLINE in the emitter's seqBlock
;; pattern (not the idealized function-per-handler shape)? Mirrors emitModuleGC's actual emission:
;; a `handle (state s0) M` is a seqBlock that (a) builds the env slot, (b) runs M inline, (c) the
;; handle's value IS M's value. The stamp must: mint id + bump $liveTop before M, restore after M's
;; value is computed, and the cap's env-slot value carries the id so a perform can gate on it.
;;
;; This replays capEscape STRUCTURALLY:
;;   letC (handle (state 0) (ret (vthunk (perform (vvar 0) get)))) (force (vvar 0))
;; The state handler returns a {get} thunk (a $clos capturing the STAMPED env). letC binds it, the
;; outer force runs it — at which point $liveTop has been RESTORED below the cap's id ⇒ the perform's
;; gate (id >= $liveTop) fires ⇒ trap (= escapedCap). Prints nothing / traps, NOT 0.
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    ;; a stamped state cell: id + the mutable box. (In the emitter, $ref gains an $id field.)
    (type $ref  (sub $val (struct (field $id i64) (field (mut (ref null $val))))))
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env))))))

  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (global $liveTop (mut i64) (i64.const 0))
  (global $nextId  (mut i64) (i64.const 0))
  (func $lookup (param $e (ref null $env)) (param $n i32) (result (ref null $val))
    (block $done (loop $l
      (br_if $done (i32.eqz (local.get $n)))
      (local.set $e (struct.get $env $tl (local.get $e)))
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br $l)))
    (struct.get $env $hd (local.get $e)))
  (func $unbox (param $v (ref null $val)) (result i64) (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))
  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; the {get} thunk (lifted $clos): body env index 0 = the STAMPED $ref cap. `get` gates on liveness.
  (elem declare func $getThunk)
  (func $getThunk (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (local $c (ref $ref))
    (local.set $c (ref.cast (ref $ref) (call $lookup (local.get $env) (i32.const 0))))
    ;; ESCAPE GATE: id >= liveTop ⇒ minting handle popped ⇒ trap (= escapedCap fail-loud).
    (if (i64.ge_s (struct.get $ref $id (local.get $c)) (global.get $liveTop))
      (then (unreachable)))
    (struct.get $ref 1 (local.get $c)))

  ;; $main body, emitted STRUCTURALLY (seqBlock shape). local 0 = env (null).
  (func $_start (export "_start") (local $env0 (ref null $env)) (local $e2 (ref null $env)) (local $leaked (ref null $val)) (local $myId i64)
    (local.set $env0 (ref.null $env))
    ;; --- handle (state 0) M : mint + bump, build stamped env slot, run M, RESTORE ---
    (local.set $leaked (block (result (ref null $val))
      ;; MINT id, OPEN: liveTop = ++nextId
      (local.set $myId (global.get $nextId))
      (global.set $nextId (i64.add (global.get $nextId) (i64.const 1)))
      (global.set $liveTop (global.get $nextId))
      ;; env slot 0 = stamped $ref (id=myId, box=0); M = ret (vthunk (perform vvar0 get))
      (local.set $e2 (struct.new $env (struct.new $ref (local.get $myId) (call $box (i64.const 0))) (local.get $env0)))
      ;; M's value = the {get} thunk closing over $e2 (the stamped env)
      (block (result (ref null $val))
        ;; RESTORE happens AFTER M's value is built but the value (a $clos) escapes with the stamped env.
        ;; In structured emission the restore is the LAST thing in the handle seqBlock, before the value
        ;; is yielded. Here: build the clos value, THEN restore liveTop, THEN yield the clos.
        (local.set $leaked (struct.new $clos (ref.func $getThunk) (local.get $e2)))
        (global.set $liveTop (local.get $myId))   ;; EXIT: handle pops
        (local.get $leaked))))
    ;; --- letC binds $leaked; outer force (vvar 0) runs it — liveTop now < the cap's id ⇒ gate fires ---
    (call $printInt (call $unbox
      (call_ref $fn (struct.get $clos $env (ref.cast (ref $clos) (local.get $leaked))) (call $box (i64.const 0)) (struct.get $clos $code (ref.cast (ref $clos) (local.get $leaked)))))))

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
