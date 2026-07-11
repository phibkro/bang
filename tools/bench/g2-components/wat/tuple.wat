(component
  (core module $m (func $r (export "r") (param $a i32) (param $b i32) (result i32)
    local.get $a local.get $b i32.add))
  (core instance $i (instantiate $m))
  (func (export "sum-tup") (param "x" (tuple u32 u32)) (result u32)
    (canon lift (core func $i "r")))
)
