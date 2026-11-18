(module
  (memory (export "memory") 1)
  (func $is_sorted (export "is_sorted") (param $p i32) (param $n i32) (result i32)
    (local $i i32)
    (local.set $i (i32.const 1))
    (block $done
      (loop $top
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (br_if $done (i32.gt_s
          (i32.load (i32.add (local.get $p)
            (i32.mul (i32.sub (local.get $i) (i32.const 1)) (i32.const 4))))
          (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4))))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $top)))
    (i32.ge_u (local.get $i) (local.get $n))))
