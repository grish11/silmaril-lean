(module
  (func $divsum4 (export "divsum4") (param $x i32) (param $y i32) (result i32)
    (local $i i32) (local $acc i32)
    ;; acc = x / (y + 0) + x / (y + 1) + x / (y + 2) + x / (y + 3): traps when some y + i is 0
    (loop $l
      (local.set $acc
        (i32.add (local.get $acc) (i32.div_u (local.get $x) (i32.add (local.get $y) (local.get $i)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 4))))
    (local.get $acc)))
