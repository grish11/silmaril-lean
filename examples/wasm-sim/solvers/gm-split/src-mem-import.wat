;; Memory as opaque imports (P-mem; the environment owns memory).
  (import "mem" "load8"  (func $load8  (param i64) (result i64)))
  (import "mem" "load16" (func $load16 (param i64) (result i64)))
  (import "mem" "load32" (func $load32 (param i64) (result i64)))
  (import "mem" "load64" (func $load64 (param i64) (result i64)))
  (import "mem" "store8"  (func $store8  (param i64 i64)))
  (import "mem" "store16" (func $store16 (param i64 i64)))
  (import "mem" "store32" (func $store32 (param i64 i64)))
  (import "mem" "store64" (func $store64 (param i64 i64)))
