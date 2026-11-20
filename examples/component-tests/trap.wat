;; Whole-instantiation failure (silmaril component tests, `trap`).
;; The first core instance's start function traps (`unreachable`); the second instance, whose
;; start function would call the imported `f` with 2, is never started, and the exported
;; `get` (which would return 7) is never available.
(component
  (import "f" (func $f (param "x" u32)))
  (core module $Trap
    (type (func))
    (type (func (result i32)))
    (func $s (type 0) unreachable)
    (func (export "get") (type 1) i32.const 7)
    (start $s))
  (core module $Call2
    (type (func (param i32)))
    (type (func))
    (import "env" "f" (func (type 0)))
    (func $s (type 1) i32.const 2 call 0)
    (start $s))
  (core func $fl (canon lower (func $f)))
  (core instance $env (export "f" (func $fl)))
  (core instance $t (instantiate $Trap))
  (core instance $c2 (instantiate $Call2 (with "env" (instance $env))))
  (func (export "get") (result u32) (canon lift (core func $t "get"))))
