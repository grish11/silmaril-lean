;; P-mem fetch: the instruction word is read through the `mem.load32` import,
;; like every data access (Silmaril.RiscV.Ext.fetch reads the current memory, so
;; stores to code are visible to later fetches).
(import "mem" "load32" (func $mem_load32 (param i64) (result i64)))
;;@body
(func $fetch (param $pc i64) (result i64) (call $mem_load32 (local.get $pc)))
