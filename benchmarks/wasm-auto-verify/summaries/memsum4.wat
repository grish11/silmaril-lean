(module
  (memory 1)
  (data (i32.const 0) "\01\02\03\04\05\06\07\08")
  (func $memsum4 (export "memsum4") (param $p i32) (result i32) (local $i i32) (local $acc i32)
    ;; the sum of the four bytes at p, p + 1, p + 2, p + 3 (each load traps out of bounds)
    (loop $l
      (local.set $acc
        (i32.add (local.get $acc) (i32.load8_u (i32.add (local.get $p) (local.get $i)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 4))))
    (local.get $acc)))
