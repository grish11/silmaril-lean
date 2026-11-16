(module
  (func $pow4 (export "pow4") (param $x i64) (result i64) (local $y i64)
    ;; x^4 as (x * x) * (x * x)
    (local.set $y (i64.mul (local.get $x) (local.get $x)))
    (i64.mul (local.get $y) (local.get $y))))
