(module
  ;; @assume add (= result (bvadd x y))
  (import "env" "add" (func $add (param i32 i32) (result i32)))
  ;; @requires true
  ;; @ensures (= result (bvadd (bvadd x y) z))
  (func $add3 (export "add3") (param $x i32) (param $y i32) (param $z i32) (result i32)
    (call $add (call $add (local.get $x) (local.get $y)) (local.get $z))))
