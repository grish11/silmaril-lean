(module
  (memory (export "memory") 1)
  (func $insertion_sort (export "insertion_sort") (param $p i32) (param $n i32)
    (local $i i32) (local $j i32) (local $key i32)
    (local.set $i (i32.const 1))
    (block $done
      (loop $outer
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $key
          (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4)))))
        (local.set $j (local.get $i))
        (block $placed
          (loop $inner
            (br_if $placed (i32.eqz (local.get $j)))
            (br_if $placed (i32.le_s
              (i32.load (i32.add (local.get $p)
                (i32.mul (i32.sub (local.get $j) (i32.const 1)) (i32.const 4))))
              (local.get $key)))
            (i32.store (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))
              (i32.load (i32.add (local.get $p)
                (i32.mul (i32.sub (local.get $j) (i32.const 1)) (i32.const 4)))))
            (local.set $j (i32.sub (local.get $j) (i32.const 1)))
            (br $inner)))
        (i32.store (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))
          (local.get $key))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $outer)))))
