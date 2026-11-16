(module
  ;; @requires true
  ;; @ensures (= result (ite (bvsgt x y) x y))
  (func $max (export "max") (param $x i32) (param $y i32) (result i32)
    (if (result i32) (i32.gt_s (local.get $x) (local.get $y))
      (then (local.get $x))
      (else (local.get $y)))))
