(component
  (core module $m
    (memory (export "mem") 1)
    (table 8 funcref)
    (global $g (mut i32) (i32.const 0))
    (func (export "run") (result i32)
      global.get $g
      i32.const 1
      i32.add
      global.set $g
      global.get $g))
  (core instance $i (instantiate $m))
  (func (export "run") (result u32)
    (canon lift (core func $i "run")))
)
