;; Pure copy-in: receive list<u32>, return only its length. The canon lift still
;; copies the whole list into memory (realloc'd), but the core func just returns
;; len — so this isolates the ABI copy cost from any per-element compute.
(component
  (core module $m
    (memory (export "mem") 1)
    (global $base i32 (i32.const 1024))
    (global $bump (mut i32) (i32.const 1024))
    (func $realloc (export "realloc")
        (param $old i32) (param $oldsz i32) (param $align i32) (param $newsz i32) (result i32)
      (local $p i32) (local $need i32) (local $have i32)
      global.get $bump local.set $p
      local.get $p local.get $newsz i32.add local.set $need
      memory.size i32.const 65536 i32.mul local.set $have
      (block $ok local.get $need local.get $have i32.le_u br_if $ok
        local.get $need local.get $have i32.sub i32.const 65535 i32.add
        i32.const 65536 i32.div_u memory.grow drop)
      global.get $bump local.get $newsz i32.add global.set $bump
      local.get $p)
    (func $len (export "len") (param $ptr i32) (param $len i32) (result i32)
      local.get $len)
    (func $reset (export "reset") (param $ret i32)
      global.get $base global.set $bump))
  (core instance $i (instantiate $m))
  (func (export "copy-only") (param "xs" (list u32)) (result u32)
    (canon lift (core func $i "len")
      (memory $i "mem") (realloc (func $i "realloc")) (post-return (func $i "reset"))))
)
