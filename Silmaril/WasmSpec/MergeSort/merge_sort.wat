(module
  (memory (export "memory") 1)
  (func $merge (export "merge") (param $p i32) (param $m i32) (param $n i32) (param $t i32)
    (local $i i32) (local $j i32) (local $k i32) (local $l i32)
    (local.set $j (local.get $m))
    (block $done
      (loop $step
        (br_if $done (i32.ge_u (local.get $k) (local.get $n)))
        (if (i32.ge_u (local.get $j) (local.get $n))
          (then (local.set $l (i32.const 1)))
          (else
            (if (i32.ge_u (local.get $i) (local.get $m))
              (then (local.set $l (i32.const 0)))
              (else
                (local.set $l (i32.le_s
                  (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4))))
                  (i32.load (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4))))))))))
        (if (local.get $l)
          (then
            (i32.store (i32.add (local.get $t) (i32.mul (local.get $k) (i32.const 4)))
              (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4)))))
            (local.set $i (i32.add (local.get $i) (i32.const 1))))
          (else
            (i32.store (i32.add (local.get $t) (i32.mul (local.get $k) (i32.const 4)))
              (i32.load (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))))
            (local.set $j (i32.add (local.get $j) (i32.const 1)))))
        (local.set $k (i32.add (local.get $k) (i32.const 1)))
        (br $step)))
    (local.set $k (i32.const 0))
    (block $copied
      (loop $copy
        (br_if $copied (i32.ge_u (local.get $k) (local.get $n)))
        (i32.store (i32.add (local.get $p) (i32.mul (local.get $k) (i32.const 4)))
          (i32.load (i32.add (local.get $t) (i32.mul (local.get $k) (i32.const 4)))))
        (local.set $k (i32.add (local.get $k) (i32.const 1)))
        (br $copy))))
  (func $merge_sort (export "merge_sort") (param $p i32) (param $n i32) (param $t i32)
    (local $m i32)
    (block $done
      (br_if $done (i32.lt_u (local.get $n) (i32.const 2)))
      (local.set $m (i32.shr_u (local.get $n) (i32.const 1)))
      (call $merge_sort (local.get $p) (local.get $m) (local.get $t))
      (call $merge_sort (i32.add (local.get $p) (i32.mul (local.get $m) (i32.const 4)))
        (i32.sub (local.get $n) (local.get $m)) (local.get $t))
      (call $merge (local.get $p) (local.get $m) (local.get $n) (local.get $t)))))
