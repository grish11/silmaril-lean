;; ffi-none: no foreign library (every foreign call is unsupported, status 2).
(module
  (func (export "call") (param i64 i64 i64 i64 i64 i64 i64) (result i32) (i32.const 2))
  (func (export "ret") (result i64) (i64.const 0)))
