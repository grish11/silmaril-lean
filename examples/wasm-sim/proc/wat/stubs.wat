;; stubs: default environment pieces. `undef` answers every undefined location with 0
;; (one deterministic resolution of `nd.undef`); `call` reports every foreign call as
;; unsupported (status 2), i.e. a process without foreign code.
(module
  (func (export "undef") (param i32) (result i64) (i64.const 0))
  (func (export "call") (param i64) (result i32) (i32.const 2)))
