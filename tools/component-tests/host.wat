;; The logging host of the component-test oracle (tools/component-tests/oracle.py).
;; Exports `f: func(x: u32)`, which appends the decimal digit `x` to a trace
;; (`trace := trace * 10 + x`) and counts the calls, and `trace`, `calls` to read them back.
(component
  (core module $M
    (global $t (mut i32) (i32.const 0))
    (global $n (mut i32) (i32.const 0))
    (func (export "f") (param i32)
      global.get $t i32.const 10 i32.mul local.get 0 i32.add global.set $t
      global.get $n i32.const 1 i32.add global.set $n)
    (func (export "trace") (result i32) global.get $t)
    (func (export "calls") (result i32) global.get $n))
  (core instance $m (instantiate $M))
  (func (export "f") (param "x" u32) (canon lift (core func $m "f")))
  (func (export "trace") (result u32) (canon lift (core func $m "trace")))
  (func (export "calls") (result u32) (canon lift (core func $m "calls"))))
