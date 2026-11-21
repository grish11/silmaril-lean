;; Instantiation-time behaviour of a component (silmaril component tests, `starts`).
;; Three core instances, instantiated in order: the first two start functions call the
;; imported host function `f` with 1 and then 2; the third start function writes 42 into a
;; mutable global that the exported `get` returns (it is 0 before the start function runs).
(component
  (import "f" (func $f (param "x" u32)))
  (core module $Call1
    (type (func (param i32)))
    (type (func))
    (import "env" "f" (func (type 0)))
    (func $s (type 1) i32.const 1 call 0)
    (start $s))
  (core module $Call2
    (type (func (param i32)))
    (type (func))
    (import "env" "f" (func (type 0)))
    (func $s (type 1) i32.const 2 call 0)
    (start $s))
  (core module $Glob
    (type (func))
    (type (func (result i32)))
    (global (mut i32) (i32.const 0))
    (func $s (type 0) i32.const 42 global.set 0)
    (func (export "get") (type 1) global.get 0)
    (start $s))
  (core func $fl (canon lower (func $f)))
  (core instance $env (export "f" (func $fl)))
  (core instance $c1 (instantiate $Call1 (with "env" (instance $env))))
  (core instance $c2 (instantiate $Call2 (with "env" (instance $env))))
  (core instance $g (instantiate $Glob))
  (func (export "get") (result u32) (canon lift (core func $g "get"))))
