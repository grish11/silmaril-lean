;; An exported instance (silmaril component tests, `instexport`). The component imports
;; `f: func(x: u32)` (unused, as in `starts` and `trap`); its core module returns 42 from `get`,
;; which is lifted and exported through an inline instance: the component's only export is the
;; instance `i`, whose function `get` is reachable by the export path `i`, `get`.
(component
  (import "f" (func $f (param "x" u32)))
  (core module $M
    (type (func (result i32)))
    (func (export "get") (type 0) i32.const 42))
  (core instance $m (instantiate $M))
  (func $get (result u32) (canon lift (core func $m "get")))
  (instance $i (export "get" (func $get)))
  (export "i" (instance $i)))
