(module
  (global $count (mut i32) (i32.const 0))
  (func $sq (param $x i32) (result i32)
    ;; x * x, counting the calls in a global
    (global.set $count (i32.add (global.get $count) (i32.const 1)))
    (i32.mul (local.get $x) (local.get $x)))
  (func $quot (param $x i32) (param $y i32) (result i32)
    ;; traps when y is 0
    (i32.div_u (local.get $x) (local.get $y)))
  (func $sumsq (export "sumsq") (param $a i32) (param $b i32) (result i32)
    ;; a * a + b * b through two calls, and the call count
    (i32.add (i32.add (call $sq (local.get $a)) (call $sq (local.get $b))) (global.get $count)))
  (func $mean (export "mean") (param $a i32) (param $b i32) (result i32)
    ;; (a + b) / 2 through a call that may trap (it does not: the divisor is 2)
    (call $quot (i32.add (local.get $a) (local.get $b)) (i32.const 2)))
  (func $ratio (export "ratio") (param $a i32) (param $b i32) (result i32)
    ;; a / b + 1 through a call that traps when b is 0
    (i32.add (call $quot (local.get $a) (local.get $b)) (i32.const 1))))
