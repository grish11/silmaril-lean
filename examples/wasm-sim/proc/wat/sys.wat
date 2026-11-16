;; sys: the Linux syscall environment as a Wasm module over WASI preview 1 (provides
;; the simulator ABI's `sys.syscall`). Process memory is read through the `mem.*` module.
;;
;;   write(fd, buf, n)  (1)   -> copies up to 64 KiB through own memory, WASI fd_write; rax = count
;;   exit(code)        (60)   -> WASI proc_exit(code & 255)
;;   exit_group(code) (231)   -> WASI proc_exit(code & 255)
;;   brk(addr)         (12)   -> program break; grows by mapping pages with mem.map
;;   anything else            -> -ENOSYS (-38)
;; Correspondence with the Lean process model: see docs/wasm-sim-abi.md.
(module
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (import "mem" "load8" (func $ld8 (param i64) (result i64)))
  (import "mem" "load64" (func $ld64 (param i64) (result i64)))
  (import "mem" "map" (func $map (param i64 i64) (result i32)))
  (import "io" "memory" (memory 33))
  (export "memory" (memory 0))
  (global $B i32 (i32.const 0x100000))
  (global $brk (mut i64) (i64.const 0))
  (global $brk0 (mut i64) (i64.const 0))
  (func (export "set_brk") (param $a i64) (global.set $brk (local.get $a)) (global.set $brk0 (local.get $a)))

  (func $write (param $fd i64) (param $buf i64) (param $n i64) (result i64)
    (local $i i32) (local $k i32)
    (if (i64.gt_u (local.get $n) (i64.const 65536)) (then (local.set $n (i64.const 65536))))
    (local.set $k (i32.wrap_i64 (local.get $n)))
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $i) (local.get $k)))
      (i32.store8 offset=64 (i32.add (global.get $B) (local.get $i))
        (i32.wrap_i64 (call $ld8 (i64.add (local.get $buf) (i64.extend_i32_u (local.get $i))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (i32.store (global.get $B) (i32.add (global.get $B) (i32.const 64)))
    (i32.store offset=4 (global.get $B) (local.get $k))
    (if (call $fd_write (i32.wrap_i64 (local.get $fd)) (global.get $B) (i32.const 1) (i32.add (global.get $B) (i32.const 8)))
      (then (return (i64.const -9))))   ;; EBADF
    (i64.load32_u offset=8 (global.get $B)))

  (func (export "syscall") (param $nr i64) (param $a1 i64) (param $a2 i64) (param $a3 i64)
                           (param $a4 i64) (param $a5 i64) (param $a6 i64) (result i64)
    (local $top i64)
    (if (i64.eq (local.get $nr) (i64.const 1))
      (then (return (call $write (local.get $a1) (local.get $a2) (local.get $a3)))))
    (if (i32.or (i64.eq (local.get $nr) (i64.const 60)) (i64.eq (local.get $nr) (i64.const 231)))
      (then (call $proc_exit (i32.and (i32.wrap_i64 (local.get $a1)) (i32.const 255))) (unreachable)))
    (if (i64.eq (local.get $nr) (i64.const 12))
      (then
        (if (i64.gt_u (local.get $a1) (global.get $brk))
          (then
            (drop (call $map (global.get $brk) (i64.sub (local.get $a1) (global.get $brk))))
            (global.set $brk (local.get $a1)))
          (else (if (i64.ge_u (local.get $a1) (global.get $brk0))
            (then (global.set $brk (local.get $a1))))))
        (return (global.get $brk))))
    (i64.const -38))
)
