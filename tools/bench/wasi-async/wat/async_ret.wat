(component
  (type $ft (func async (result u32)))
  (core func $treturn (canon task.return (result u32)))
  (core module $m
    (import "" "task-return" (func $tr (param i32)))
    ;; initial: call task.return(42), then return callback-code EXIT=0
    (func (export "run") (result i32)
      (call $tr (i32.const 42))
      (i32.const 0))
    ;; callback: (ctx event payload) -> code ; never invoked since we EXIT initially
    (func (export "cb") (param i32 i32 i32) (result i32)
      (i32.const 0)))
  (core instance $i (instantiate $m
    (with "" (instance (export "task-return" (func $treturn))))))
  (func $lifted (type $ft)
    (canon lift (core func $i "run") async (callback (func $i "cb"))))
  (export "run" (func $lifted))
)
