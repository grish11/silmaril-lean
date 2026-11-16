(module
  ;; @requires true
  ;; @ensures (= result (ite (bvslt x #x00000000) (bvneg x) x))
  (func $abs (export "abs") (param $x i32) (result i32) (local $m i32)
    (local.set $m (i32.shr_s (local.get $x) (i32.const 31)))
    (i32.sub (i32.xor (local.get $x) (local.get $m)) (local.get $m))))
