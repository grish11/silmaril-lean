(module
  (global $count (mut i32) (i32.const 0))
  (func $sumsq (export "sumsq") (param $a i32) (param $b i32) (result i32)
    ;; sumsq counting one call only
    (global.set $count (i32.add (global.get $count) (i32.const 1)))
    (i32.add (i32.add (i32.mul (local.get $a) (local.get $a)) (i32.mul (local.get $b) (local.get $b)))
      (global.get $count)))
  (func $mean (export "mean") (param $a i32) (param $b i32) (result i32)
    (i32.shr_s (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
  (func $ratio (export "ratio") (param $a i32) (param $b i32) (result i32)
    ;; does not trap when b is 0
    (i32.add (i32.div_u (local.get $a) (i32.or (local.get $b) (i32.const 1))) (i32.const 1))))
