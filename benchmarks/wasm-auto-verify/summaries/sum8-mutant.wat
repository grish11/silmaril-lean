(module
  (func $sum8 (export "sum8") (param $x i32) (result i32) (local $i i32) (local $acc i32)
    ;; sum8 with one iteration missing (i < 7)
    (loop $l
      (local.set $acc (i32.add (local.get $acc) (i32.mul (local.get $x) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 7))))
    (local.get $acc)))
