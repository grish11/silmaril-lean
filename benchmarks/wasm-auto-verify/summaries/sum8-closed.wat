(module
  (func $sum8 (export "sum8") (param $x i32) (result i32)
    ;; the closed form of sum8: x * (0 + 1 + ... + 7)
    (i32.mul (local.get $x) (i32.const 28))))
