(component
  (core module $m
    (func (export "run") (result i32) (i32.const 42)))
  (core instance $i (instantiate $m))
  (type $ft (func (result u32)))
  (func $lifted (type $ft) (canon lift (core func $i "run")))
  (export "run" (func $lifted))
)
