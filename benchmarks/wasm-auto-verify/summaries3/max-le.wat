(module
 (func $max (export "max") (param $x i32) (param $y i32) (result i32)
  (if (result i32) (i32.le_s (local.get $x) (local.get $y))
   (then (local.get $y))
   (else (local.get $x)))))
