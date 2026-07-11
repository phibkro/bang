;; ADR-0052 BACK-DOOR TEST for cap-gc-rep-design.md: does a first-class $cap value preserve
;; IDENTITY dispatch (not nearest-label) when TWO same-label caps are both live and BOTH threaded
;; as runtime values?
;;
;; examples/handle-custom-nested (oracle = 210): inner (fetch=n*10) + outer (fetch=n*100), then
;; inner.fetch(1) + outer.fetch(2) = 10 + 200 = 210. Nearest-label would give 10 + 20 = 30 (both
;; to inner). The correct answer 210 requires each perform to hit the SPECIFIC handler its cap
;; names — identity dispatch.
;;
;; HERE both caps are $cap VALUES held in locals (as if passed as args). Each perform call_refs
;; the clause carried by ITS OWN $cap value — inner via capInner, outer via capOuter. The identity
;; is the $cap value itself (its distinct clause closure), so there is no "nearest" search: the
;; performer holds a direct reference to the right handler's clause. Prints 210, NOT 30 ⇒ identity
;; dispatch survives first-class caps. (No global $liveTop lookup by label anywhere = no back door.)
(module
  (rec
    (type $val  (sub (struct)))
    (type $ival (sub $val (struct (field i64))))
    (type $env  (struct (field $hd (ref null $val)) (field $tl (ref null $env))))
    (type $fn   (func (param (ref null $env)) (param (ref null $val)) (result (ref null $val))))
    (type $clos (sub $val (struct (field $code (ref $fn)) (field $env (ref null $env)))))
    (type $cap  (sub $val (struct (field $id i64) (field $clauses (ref null $env))))))

  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (func $unbox (param $v (ref null $val)) (result i64)
    (struct.get $ival 0 (ref.cast (ref $ival) (local.get $v))))
  (func $box (param $n i64) (result (ref null $val)) (struct.new $ival (local.get $n)))
  (func $clausecell (param $h (ref null $env)) (param $k i64) (result (ref null $val))
    (block $d (loop $l
      (br_if $d (i64.eqz (local.get $k)))
      (local.set $h (struct.get $env $tl (local.get $h)))
      (local.set $k (i64.sub (local.get $k) (i64.const 1)))
      (br $l)))
    (struct.get $env $hd (local.get $h)))
  ;; perform op-0 on a $cap value: clausecell 0, call_ref with arg. Identity = the $cap itself.
  (func $performFetch (param $cap (ref $cap)) (param $arg (ref null $val)) (result (ref null $val))
    (local $cl (ref null $val))
    (local.set $cl (call $clausecell (struct.get $cap $clauses (local.get $cap)) (i64.const 0)))
    (call_ref $fn (struct.get $clos $env (ref.cast (ref $clos) (local.get $cl))) (local.get $arg) (struct.get $clos $code (ref.cast (ref $clos) (local.get $cl)))))

  (elem declare func $clauseInner $clauseOuter)
  (func $clauseInner (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (call $box (i64.mul (call $unbox (local.get $arg)) (i64.const 10))))
  (func $clauseOuter (type $fn) (param $env (ref null $env)) (param $arg (ref null $val)) (result (ref null $val))
    (call $box (i64.mul (call $unbox (local.get $arg)) (i64.const 100))))

  (func $run (result i64)
    (local $capInner (ref $cap))
    (local $capOuter (ref $cap))
    ;; two DISTINCT identities (0 = outer minted first, 1 = inner), each with its own clause.
    (local.set $capOuter (struct.new $cap (i64.const 0)
      (struct.new $env (struct.new $clos (ref.func $clauseOuter) (ref.null $env)) (ref.null $env))))
    (local.set $capInner (struct.new $cap (i64.const 1)
      (struct.new $env (struct.new $clos (ref.func $clauseInner) (ref.null $env)) (ref.null $env))))
    ;; inner.fetch(1) + outer.fetch(2) — each perform names ITS cap value ⇒ 10 + 200 = 210.
    (i64.add
      (call $unbox (call $performFetch (local.get $capInner) (call $box (i64.const 1))))
      (call $unbox (call $performFetch (local.get $capOuter) (call $box (i64.const 2))))))

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
