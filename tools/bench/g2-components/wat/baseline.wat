;; Baseline: NO canonical-ABI list crossing. Export `sum-internal: func(u32) -> u32`
;; that WRITES n u32s (0..n) into its own memory then sums them. Same compute
;; (write n + read n), same memory traffic, but the only boundary value is a
;; scalar u32 — so subtracting this from sum-list isolates the copy-in tax.
(component
  (core module $m
    (memory (export "mem") 1)
    (func $si (export "sum-internal") (param $n i32) (result i32)
      (local $i i32) (local $acc i32) (local $base i32) (local $need i32) (local $have i32)
      i32.const 1024
      local.set $base
      ;; grow memory for n u32s if needed
      local.get $base
      local.get $n
      i32.const 4
      i32.mul
      i32.add
      local.set $need
      memory.size i32.const 65536 i32.mul local.set $have
      (block $ok
        local.get $need local.get $have i32.le_u br_if $ok
        local.get $need local.get $have i32.sub i32.const 65535 i32.add
        i32.const 65536 i32.div_u memory.grow drop)
      ;; write 0..n
      (block $w1 (loop $l1
        local.get $i local.get $n i32.ge_u br_if $w1
        local.get $base local.get $i i32.const 4 i32.mul i32.add
        local.get $i i32.store
        local.get $i i32.const 1 i32.add local.set $i br $l1))
      ;; sum
      i32.const 0 local.set $i
      (block $w2 (loop $l2
        local.get $i local.get $n i32.ge_u br_if $w2
        local.get $acc
        local.get $base local.get $i i32.const 4 i32.mul i32.add i32.load
        i32.add local.set $acc
        local.get $i i32.const 1 i32.add local.set $i br $l2))
      local.get $acc))
  (core instance $i (instantiate $m))
  (func (export "sum-internal") (param "n" u32) (result u32)
    (canon lift (core func $i "sum-internal")))
)
