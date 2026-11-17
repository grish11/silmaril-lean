;; Test environment memory for the RV64 simulators: implements the `mem.*`
;; imports of the simulator ABI over a 64 MiB guest window [0, 2^26). Any access outside
;; the window traps (= fault). Guest addresses are identity-mapped.
(module
  (memory (export "memory") 1024)
  (func $a (param $a i64) (result i32)
    (if (i64.ge_u (local.get $a) (i64.const 0x4000000)) (then (unreachable)))
    (i32.wrap_i64 (local.get $a)))
  (func (export "load8") (param $a i64) (result i64) (i64.load8_u (call $a (local.get $a))))
  (func (export "load16") (param $a i64) (result i64) (i64.load16_u (call $a (local.get $a))))
  (func (export "load32") (param $a i64) (result i64) (i64.load32_u (call $a (local.get $a))))
  (func (export "load64") (param $a i64) (result i64) (i64.load (call $a (local.get $a))))
  (func (export "store8") (param $a i64) (param $v i64) (i64.store8 (call $a (local.get $a)) (local.get $v)))
  (func (export "store16") (param $a i64) (param $v i64) (i64.store16 (call $a (local.get $a)) (local.get $v)))
  (func (export "store32") (param $a i64) (param $v i64) (i64.store32 (call $a (local.get $a)) (local.get $v)))
  (func (export "store64") (param $a i64) (param $v i64) (i64.store (call $a (local.get $a)) (local.get $v))))
