;; Round-robin scheduling policy: `pick` = step counter / quantum (the scheduler takes it
;; mod the number of threads). Quantum 3 instructions.
(module
  (global $k (mut i32) (i32.const 0))
  (func (export "pick") (result i32)
    (global.set $k (i32.add (global.get $k) (i32.const 1)))
    (i32.div_u (global.get $k) (i32.const 3))))
