;; Component exporting `sum-list: func(list<u32>) -> u32`.
;; canon lift copies the caller's list INTO this component's memory (the
;; canonical-ABI copy under measurement); the core `sum` reads it back.
;; realloc grows memory as needed; post-return resets the bump allocator so
;; repeated calls don't leak (mirrors the canonical ABI's free-on-return).
(component
  (core module $m
    (memory (export "mem") 1)
    (global $base i32 (i32.const 1024))
    (global $bump (mut i32) (i32.const 1024))

    (func $realloc (export "realloc")
        (param $old i32) (param $oldsz i32) (param $align i32) (param $newsz i32)
        (result i32)
      (local $p i32) (local $need i32) (local $pages i32) (local $have i32)
      global.get $bump
      local.set $p
      ;; grow memory if bump+newsz exceeds current size
      local.get $p
      local.get $newsz
      i32.add
      local.set $need
      memory.size
      i32.const 65536
      i32.mul
      local.set $have
      (block $ok
        local.get $need
        local.get $have
        i32.le_u
        br_if $ok
        ;; grow by ceil((need-have)/65536) pages
        local.get $need
        local.get $have
        i32.sub
        i32.const 65535
        i32.add
        i32.const 65536
        i32.div_u
        memory.grow
        drop)
      global.get $bump
      local.get $newsz
      i32.add
      global.set $bump
      local.get $p)

    (func $sum (export "sum") (param $ptr i32) (param $len i32) (result i32)
      (local $i i32) (local $acc i32)
      (block $done
        (loop $loop
          local.get $i
          local.get $len
          i32.ge_u
          br_if $done
          local.get $acc
          local.get $ptr
          local.get $i
          i32.const 4
          i32.mul
          i32.add
          i32.load
          i32.add
          local.set $acc
          local.get $i
          i32.const 1
          i32.add
          local.set $i
          br $loop))
      local.get $acc)

    ;; called on post-return with the lifted result; reset the bump allocator
    (func $reset (export "reset") (param $ret i32)
      global.get $base
      global.set $bump))
  (core instance $i (instantiate $m))
  (func (export "sum-list") (param "xs" (list u32)) (result u32)
    (canon lift (core func $i "sum")
      (memory $i "mem")
      (realloc (func $i "realloc"))
      (post-return (func $i "reset"))))
)
