;; FIX WITNESS for cap-gc-rep-design.md: a GENERATION-STAMPED $cap restores ADR-0063 fail-loud.
;;
;; The naive $cap (escape-naive-cap.wat) printed 42 where the kernel says .escapedCap, because
;; carrying the clause closures directly loses the "is my handler still on the stack?" check that
;; the kernel's idDispatch/splitAtId performs by walking the live chain K.
;;
;; FIX: give each $cap an IDENTITY n (the kernel's generative id, ADR-0055) AND check it against a
;; LIVE-HANDLER REGISTRY at perform time — a global $liveTop watermark that a `handle` bumps on
;; entry and restores on exit. A perform whose cap identity n >= current $liveTop means the handler
;; that minted it has POPPED ⇒ trap (fail-loud, = .escapedCap). This is the runtime image of
;; splitAtId returning none. Here the escaping perform traps (unreachable) instead of reading 42.
;;
;; This is candidate (a) done FAITHFULLY: $cap = (identity n, clause list) + a live-frame check.
;; It reifies the ONE thing handlers-as-control-flow discarded: the frame's liveness.
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    (type $ref  (sub $val (struct (field (mut (ref null $val))))))
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env)))))
    ;; FAITHFUL $cap: identity n + the state box.  (A full rep also carries the clause list.)
    (type $cap  (sub $val (struct (field $id i64) (field $box (ref $ref))))))

  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  ;; the LIVE-HANDLER watermark: the count of currently-open handlers. A handle bumps it on entry,
  ;; restores on exit. A cap minted with id n is LIVE iff n < $liveTop (its frame not yet popped).
  ;; This is the runtime image of the kernel's live chain K (splitAtId walks it).
  (global $liveTop (mut i64) (i64.const 0))
  (global $nextId  (mut i64) (i64.const 0))

  (func $unbox (param $v (ref null $val)) (result i64)
    (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))
  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; perform get on a cap: FIRST check liveness (id < liveTop), trap if escaped (fail-loud).
  (elem declare func $getThunk)
  (func $getThunk (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (local $c (ref $cap))
    (local.set $c (ref.cast (ref $cap) (struct.get $env $hd (local.get $env))))
    ;; ESCAPE CHECK: id >= liveTop ⇒ the minting handler has popped ⇒ trap (= .escapedCap).
    (if (i64.ge_s (struct.get $cap $id (local.get $c)) (global.get $liveTop))
      (then (unreachable)))   ;; fail-loud; in the emitter this is a defined `escapedCap` trap
    (struct.get $ref 0 (struct.get $cap $box (local.get $c))))

  ;; handle (state 42) BODY: on entry bump liveTop (this handler is now open); run body; on exit
  ;; restore liveTop (handler popped). The body returns the escaping thunk (closes over the cap).
  (func $installHandler (result (ref $clos))
    (local $cell (ref $ref))
    (local $cap (ref $cap))
    (local $myId i64)
    ;; MINT: id = nextId++, then OPEN: liveTop = nextId (this frame + all below are live)
    (local.set $myId (global.get $nextId))
    (global.set $nextId (i64.add (global.get $nextId) (i64.const 1)))
    (global.set $liveTop (global.get $nextId))
    (local.set $cell (struct.new $ref (call $box (i64.const 42))))
    (local.set $cap (struct.new $cap (local.get $myId) (local.get $cell)))
    ;; body value = the thunk closing over the cap
    (global.set $liveTop (local.get $myId))   ;; EXIT: this handler pops (liveTop drops to myId)
    (struct.new $clos (ref.func $getThunk)
      (struct.new $env (local.get $cap) (ref.null $env))))

  (func $run (result i64)
    (local $thunk (ref $clos))
    (local.set $thunk (call $installHandler))
    ;; force the escaped thunk — the liveness check fires ⇒ trap (fail-loud), NOT 42.
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
