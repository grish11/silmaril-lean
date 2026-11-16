;; Pseudo-random scheduling policy (xorshift32, fixed seed): one opaque scheduler choice
;; per step, i.e. one resolution of the scheduler nondeterminism.
(module
  (global $x (mut i32) (i32.const 2463534242))
  (func (export "pick") (result i32)
    (global.set $x (i32.xor (global.get $x) (i32.shl (global.get $x) (i32.const 13))))
    (global.set $x (i32.xor (global.get $x) (i32.shr_u (global.get $x) (i32.const 17))))
    (global.set $x (i32.xor (global.get $x) (i32.shl (global.get $x) (i32.const 5))))
    (i32.shr_u (global.get $x) (i32.const 8))))
