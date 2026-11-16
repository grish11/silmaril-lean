(module
  (func $pow4 (export "pow4") (param $x i64) (result i64) (local $i i32) (local $acc i64)
    ;; x^4 by a loop of four multiplications
    (local.set $acc (i64.const 1))
    (loop $l
      (local.set $acc (i64.mul (local.get $acc) (local.get $x)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.ne (local.get $i) (i32.const 4))))
    (local.get $acc)))
