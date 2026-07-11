;; HAND-WITNESS for cap-gc-rep-design.md candidate (a): a first-class $cap GC value.
;; Mirrors examples/stage-swap (oracle = 30005): a `logic` closure takes `net : Cap Net`
;; as an ARGUMENT and performs net.fetch on it; two handlers (test = *10, prod = +1) apply
;; the SAME logic. The wall: today the emitter dispatches by compile-time CapSlot, so a cap
;; in an arg slot (CapSlot.none) refuses. This witness shows a $cap RUNTIME VALUE that:
;;   - carries the clause-closure list (the same $env-of-$clos the lexical path already builds)
;;   - is passed as an ordinary $val argument
;;   - a `perform op v` on it looks up the clause at the op's position and call_refs it.
;; For single-op Net, position 0. No compile-time CapSlot for the performer.
;;
;; logic  = fun net => net.fetch(1) + net.fetch(2)          -- net is an ARG ($cap value)
;; handlerTest: fetch(n) => n * 10  ;  handlerProd: fetch(n) => n + 1
;; result = (test logic)*1000 + (prod logic) = 30*1000 + 5 = 30005
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env)))))
    ;; THE NEW REP: a $cap is a runtime capability value. Field 0 = the clause-closure list
    ;; ($env of lam-style $clos, position k = k-from-front = the op at position k). This is
    ;; exactly the $txbox contents the lexical custom path already builds — lifted to a $val.
    (type $cap  (sub $val (struct (field $clauses (ref null $env))))))

  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  ;; $lookup: de Bruijn index into an $env.
  (func $lookup (param $e (ref null $env)) (param $n i32) (result (ref null $val))
    (block $done (loop $l
      (br_if $done (i32.eqz (local.get $n)))
      (local.set $e (struct.get $env $tl (local.get $e)))
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br $l)))
    (struct.get $env $hd (local.get $e)))
  ;; $clausecell: walk k steps into the clause-closure list (the op's position), return the $clos.
  (func $clausecell (param $h (ref null $env)) (param $k i64) (result (ref null $val))
    (block $d (loop $l
      (br_if $d (i64.eqz (local.get $k)))
      (local.set $h (struct.get $env $tl (local.get $h)))
      (local.set $k (i64.sub (local.get $k) (i64.const 1)))
      (br $l)))
    (struct.get $env $hd (local.get $h)))
  (func $unbox (param $v (ref null $val)) (result i64)
    (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))
  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))

  ;; ── the clause bodies (lam-style: arg n at index 0, then p::handlerEnv) ──
  ;; test's fetch clause: n * 10
  (elem declare func $clauseTest $clauseProd $logic)
  (func $clauseTest (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (call $box (i64.mul (call $unbox (local.get $arg)) (i64.const 10))))
  ;; prod's fetch clause: n + 1
  (func $clauseProd (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (call $box (i64.add (call $unbox (local.get $arg)) (i64.const 1))))

  ;; ── logic: fun net => net.fetch(1) + net.fetch(2) ──
  ;; net arrives as the ARG ($cap value) at $env index 0 (the fn prepends arg::capturedEnv).
  ;; A `perform fetch v` on net: extract net.$clauses, $clausecell at position 0 (fetch = op 0),
  ;; call_ref the clause with v. NO compile-time CapSlot — dispatch is off the runtime $cap value.
  (func $logic (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (local $body (ref null $env))
    (local $net (ref $cap))
    (local $cl0 (ref null $val))
    (local $cl1 (ref null $val))
    ;; body env = arg::captured
    (local.set $body (struct.new $env (local.get $arg) (local.get $env)))
    ;; net = the $cap arg (index 0)
    (local.set $net (ref.cast (ref $cap) (call $lookup (local.get $body) (i32.const 0))))
    ;; net.fetch(1): clausecell(net.$clauses, 0) call_ref 1
    (local.set $cl0 (call $clausecell (struct.get $cap $clauses (local.get $net)) (i64.const 0)))
    ;; net.fetch(2): same
    (local.set $cl1 (call $clausecell (struct.get $cap $clauses (local.get $net)) (i64.const 0)))
    (call $box (i64.add
      (call $unbox (call_ref $fn (struct.get $clos $env (ref.cast (ref $clos) (local.get $cl0))) (call $box (i64.const 1)) (struct.get $clos $code (ref.cast (ref $clos) (local.get $cl0)))))
      (call $unbox (call_ref $fn (struct.get $clos $env (ref.cast (ref $clos) (local.get $cl1))) (call $box (i64.const 2)) (struct.get $clos $code (ref.cast (ref $clos) (local.get $cl1))))))))

  ;; ── main: build two $cap values (test, prod), apply logic to each ──
  (func $run (result i64)
    (local $capTest (ref $cap))
    (local $capProd (ref $cap))
    ;; test cap: clause list = [clauseTest] (single op, position 0), empty captured env
    (local.set $capTest (struct.new $cap
      (struct.new $env (struct.new $clos (ref.func $clauseTest) (ref.null $env)) (ref.null $env))))
    (local.set $capProd (struct.new $cap
      (struct.new $env (struct.new $clos (ref.func $clauseProd) (ref.null $env)) (ref.null $env))))
    ;; (test logic) = logic applied with net := capTest  ⇒ 10 + 20 = 30
    ;; (prod logic) = logic applied with net := capProd  ⇒  2 +  3 =  5
    (i64.add
      (i64.mul
        (call $unbox (call $logic (ref.null $env) (local.get $capTest)))
        (i64.const 1000))
      (call $unbox (call $logic (ref.null $env) (local.get $capProd)))))

  (func $_start (export "_start")
    (call $printInt (call $run)))

  ;; minimal integer printer (decimal, positive) via WASI fd_write.
  (func $printInt (param $n i64) (local $i i32) (local $d i64)
    (local.set $i (i32.const 32))
    (if (i64.eqz (local.get $n))
      (then (local.set $i (i32.sub (local.get $i) (i32.const 1)))
            (i32.store8 (local.get $i) (i32.const 48)))
      (else
        (block $done (loop $l
          (br_if $done (i64.eqz (local.get $n)))
          (local.set $d (i64.rem_u (local.get $n) (i64.const 10)))
          (local.set $i (i32.sub (local.get $i) (i32.const 1)))
          (i32.store8 (local.get $i) (i32.add (i32.const 48) (i32.wrap_i64 (local.get $d))))
          (local.set $n (i64.div_u (local.get $n) (i64.const 10)))
          (br $l)))))
    ;; append newline
    (i32.store8 (i32.const 32) (i32.const 10))
    ;; iov: ptr=$i, len=(33-$i)
    (i32.store (i32.const 40) (local.get $i))
    (i32.store (i32.const 44) (i32.sub (i32.const 33) (local.get $i)))
    (drop (call $fd_write (i32.const 1) (i32.const 40) (i32.const 1) (i32.const 48))))
)
