(module
  (memory (export "memory") 1)
  (func $oba_get (export "oba_get") (param $x i32) (param $k i32) (result i32)
    (i32.load offset=4 (i32.add (local.get $x) (i32.mul (local.get $k) (i32.const 4)))))
  (func $oba_find (export "oba_find") (param $x i32) (param $e i32) (result i32)
    (local $i i32)
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $i) (i32.load (local.get $x))))
        (br_if $done (i32.ge_s
          (i32.load offset=4 (i32.add (local.get $x) (i32.mul (local.get $i) (i32.const 4))))
          (local.get $e)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (local.get $i))
  (func $btree_search (export "btree_search") (param $k i32) (result i32)
    (local $x i32) (local $i i32) (local $keys i32)
    (local.set $x (i32.load (i32.const 4)))
    (block $never
      (loop $descend
        (local.set $keys (i32.add (i32.mul (local.get $x) (i32.const 65536)) (i32.const 4)))
        (local.set $i (call $oba_find (local.get $keys) (local.get $k)))
        (if (i32.lt_u (local.get $i) (i32.load (local.get $keys)))
          (then
            (if (i32.eq (call $oba_get (local.get $keys) (local.get $i)) (local.get $k))
              (then (return (i32.const 1))))))
        (if (i32.load (i32.mul (local.get $x) (i32.const 65536)))
          (then (return (i32.const 0))))
        (local.set $x (call $oba_get
          (i32.add (i32.mul (local.get $x) (i32.const 65536)) (i32.const 32768)) (local.get $i)))
        (br $descend)))
    (i32.const 0)))
