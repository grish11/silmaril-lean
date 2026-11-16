(module
  (global $count (mut i32) (i32.const 0))
  (func $sumsq (export "sumsq") (param $a i32) (param $b i32) (result i32)
    ;; sumsq of calls.wat with both calls inlined by hand
    (global.set $count (i32.add (global.get $count) (i32.const 2)))
    (i32.add (i32.add (i32.mul (local.get $a) (local.get $a)) (i32.mul (local.get $b) (local.get $b)))
      (global.get $count)))
  (func $mean (export "mean") (param $a i32) (param $b i32) (result i32)
    (i32.shr_u (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
  (func $ratio (export "ratio") (param $a i32) (param $b i32) (result i32)
    (i32.add (i32.div_u (local.get $a) (local.get $b)) (i32.const 1))))
