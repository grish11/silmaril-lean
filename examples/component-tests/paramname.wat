;; A parameter name the host does not have (silmaril component tests, `paramname`): `starts`
;; with the import `f` declared as `func(y: u32)` instead of `func(x: u32)`. Nothing else
;; differs. Component function types keep parameter names, so the binary differs from
;; `starts.wasm` in that name only; the IR reading drops parameter names and reads it exactly as
;; `starts.wasm`, while the reference machine checks the import against the host function
;; `f: func(x: u32)` by name and traps before any side effect.
(component
  (import "f" (func $f (param "y" u32)))
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
