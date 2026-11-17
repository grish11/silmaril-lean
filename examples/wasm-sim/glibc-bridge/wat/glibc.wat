;; glibc-subset: WASI-backed Wasm implementations of the glibc functions a dynamically linked
;; x86-64 program imports (the `ffi` interface of extrun/glibcrun; WIT: wit/glibc.wit).
;; Foreign address EXT_BASE + 16*i is function i (the loader's table, build.sh):
;;   0 puts(s)        one fd_write(1, s ++ "\n"); returns |s| + 1 (glibc's value), EOF (-1)
;;                    if fd_write fails or writes fewer bytes (contract `putsC`, Lean
;;                    Silmaril.Sim.GlibcBridge)
;;   1 strlen(s)      2 putchar(c)
;;   3 __libc_start_main   handled by glibcrun (never reaches the library: status 2)
;;   4 exit(st)       proc_exit(st & 255) (no stdio buffers to flush: puts/write are unbuffered)
;;   5 write(fd,b,n)  one fd_write; returns the count, -1 on error
;;   6 memcpy(d,s,n)  7 memset(d,c,n)   (return d)
;; `call(target, a1..a6) -> status` (0 ok, 2 unknown target); `ret()` = the result (rax).
;; Guest memory through `mem.*`; its own memory is io.memory bytes [0x120000, 0x130100).
(module
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (import "mem" "load8" (func $ld8 (param i64) (result i64)))
  (import "mem" "store8" (func $st8 (param i64 i64)))
  (import "io" "memory" (memory 33))
  (export "memory" (memory 0))
  (global $B i32 (i32.const 0x120000))
  (global $EXT_BASE i64 (i64.const 0x7f0000000000))
  (global $rax (mut i64) (i64.const 0))
  ;; fd_write(fd, B+64, n); returns the count written, or -1 on error
  (func $out (param $fd i64) (param $n i32) (result i64)
    (i32.store (global.get $B) (i32.add (global.get $B) (i32.const 64)))
    (i32.store offset=4 (global.get $B) (local.get $n))
    (if (call $fd_write (i32.wrap_i64 (local.get $fd)) (global.get $B) (i32.const 1) (i32.add (global.get $B) (i32.const 8)))
      (then (return (i64.const -1))))
    (i64.extend_i32_u (i32.load offset=8 (global.get $B))))
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
  ;; copy n (<= 65536) guest bytes at $s to B+64..
  (func $fetchn (param $s i64) (param $n i32)
    (local $k i32)
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $k) (local.get $n)))
      (i32.store8 offset=64 (i32.add (global.get $B) (local.get $k))
        (i32.wrap_i64 (call $ld8 (i64.add (local.get $s) (i64.extend_i32_u (local.get $k))))))
      (local.set $k (i32.add (local.get $k) (i32.const 1)))
      (br $l))))
  (func (export "ret") (result i64) (global.get $rax))
  (func (export "call") (param $t i64) (param $a1 i64) (param $a2 i64) (param $a3 i64)
                        (param $a4 i64) (param $a5 i64) (param $a6 i64) (result i32)
    (local $i i64) (local $n i32) (local $w i64) (local $k i64)
    (local.set $i (i64.shr_u (i64.sub (local.get $t) (global.get $EXT_BASE)) (i64.const 4)))
    (block $done
      (if (i64.eqz (local.get $i))            ;; puts
        (then
          (local.set $n (call $fetch (local.get $a1)))
          (i32.store8 offset=64 (i32.add (global.get $B) (local.get $n)) (i32.const 10))
          (local.set $w (call $out (i64.const 1) (i32.add (local.get $n) (i32.const 1))))
          (global.set $rax (select (i64.extend_i32_u (i32.add (local.get $n) (i32.const 1))) (i64.const -1)
            (i64.eq (local.get $w) (i64.extend_i32_u (i32.add (local.get $n) (i32.const 1))))))
          (br $done)))
      (if (i64.eq (local.get $i) (i64.const 1))  ;; strlen
        (then (global.set $rax (i64.extend_i32_u (call $fetch (local.get $a1)))) (br $done)))
      (if (i64.eq (local.get $i) (i64.const 2))  ;; putchar
        (then
          (i32.store8 offset=64 (global.get $B) (i32.wrap_i64 (local.get $a1)))
          (local.set $w (call $out (i64.const 1) (i32.const 1)))
          (global.set $rax (select (i64.and (local.get $a1) (i64.const 255)) (i64.const -1) (i64.eq (local.get $w) (i64.const 1))))
          (br $done)))
      (if (i64.eq (local.get $i) (i64.const 4))  ;; exit
        (then (call $proc_exit (i32.wrap_i64 (i64.and (local.get $a1) (i64.const 255)))) (unreachable)))
      (if (i64.eq (local.get $i) (i64.const 5))  ;; write
        (then
          (local.set $n (i32.wrap_i64 (select (local.get $a3) (i64.const 65536) (i64.le_u (local.get $a3) (i64.const 65536)))))
          (call $fetchn (local.get $a2) (local.get $n))
          (global.set $rax (call $out (local.get $a1) (local.get $n)))
          (br $done)))
      (if (i64.eq (local.get $i) (i64.const 6))  ;; memcpy
        (then
          (block $o (loop $l
            (br_if $o (i64.ge_u (local.get $k) (local.get $a3)))
            (call $st8 (i64.add (local.get $a1) (local.get $k)) (call $ld8 (i64.add (local.get $a2) (local.get $k))))
            (local.set $k (i64.add (local.get $k) (i64.const 1)))
            (br $l)))
          (global.set $rax (local.get $a1)) (br $done)))
      (if (i64.eq (local.get $i) (i64.const 7))  ;; memset
        (then
          (block $o (loop $l
            (br_if $o (i64.ge_u (local.get $k) (local.get $a3)))
            (call $st8 (i64.add (local.get $a1) (local.get $k)) (i64.and (local.get $a2) (i64.const 255)))
            (local.set $k (i64.add (local.get $k) (i64.const 1)))
            (br $l)))
          (global.set $rax (local.get $a1)) (br $done)))
      (return (i32.const 2)))
    (i32.const 0))
)
