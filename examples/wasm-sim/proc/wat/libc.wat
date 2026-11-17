;; libc: a Wasm "foreign library" for dynamically linked x86-64 programs (`ffi` interface of
;; extrun). Foreign address EXT_BASE + 16*i is function i of the loader's table:
;;   0 puts(s)    -> writes s and "\n" to fd 1 (WASI fd_write); returns strlen(s) + 1
;;   1 strlen(s)  -> length
;;   2 putchar(c) -> writes the byte c; returns c & 255
;; `call(target, a1..a6) -> status` (0 ok, 2 unknown target); `ret()` = the last result (rax).
;; Strings are read through `mem.load8`. Its own memory is imported from `io` (bytes
;; [0x120000, 0x130100)) so that every WASI caller of a merged module shares one memory.
(module
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "mem" "load8" (func $ld8 (param i64) (result i64)))
  (import "io" "memory" (memory 33))
  (export "memory" (memory 0))
  (global $B i32 (i32.const 0x120000))
  (global $EXT_BASE i64 (i64.const 0x7f0000000000))
  (global $rax (mut i64) (i64.const 0))
  (func $out (param $n i32)
    (i32.store (global.get $B) (i32.add (global.get $B) (i32.const 64)))
    (i32.store offset=4 (global.get $B) (local.get $n))
    (drop (call $fd_write (i32.const 1) (global.get $B) (i32.const 1) (i32.add (global.get $B) (i32.const 8)))))
  ;; copy the C string at guest address $s to B+64.. (at most 65536 bytes); returns its length
  (func $fetch (param $s i64) (result i32)
    (local $n i32) (local $b i32)
    (block $o (loop $l
      (local.set $b (i32.wrap_i64 (call $ld8 (i64.add (local.get $s) (i64.extend_i32_u (local.get $n))))))
      (br_if $o (i32.or (i32.eqz (local.get $b)) (i32.ge_u (local.get $n) (i32.const 65536))))
      (i32.store8 offset=64 (i32.add (global.get $B) (local.get $n)) (local.get $b))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (br $l)))
    (local.get $n))
  (func (export "ret") (result i64) (global.get $rax))
  (func (export "call") (param $t i64) (param $a1 i64) (param $a2 i64) (param $a3 i64)
                        (param $a4 i64) (param $a5 i64) (param $a6 i64) (result i32)
    (local $i i64) (local $n i32)
    (local.set $i (i64.shr_u (i64.sub (local.get $t) (global.get $EXT_BASE)) (i64.const 4)))
    (if (i64.eqz (local.get $i))
      (then
        (local.set $n (call $fetch (local.get $a1)))
        (i32.store8 offset=64 (i32.add (global.get $B) (local.get $n)) (i32.const 10))
        (call $out (i32.add (local.get $n) (i32.const 1)))
        (global.set $rax (i64.extend_i32_u (i32.add (local.get $n) (i32.const 1))))
        (return (i32.const 0))))
    (if (i64.eq (local.get $i) (i64.const 1))
      (then (global.set $rax (i64.extend_i32_u (call $fetch (local.get $a1)))) (return (i32.const 0))))
    (if (i64.eq (local.get $i) (i64.const 2))
      (then
        (i32.store8 offset=64 (global.get $B) (i32.wrap_i64 (local.get $a1)))
        (call $out (i32.const 1))
        (global.set $rax (i64.and (local.get $a1) (i64.const 255)))
        (return (i32.const 0))))
    (i32.const 2))
)
