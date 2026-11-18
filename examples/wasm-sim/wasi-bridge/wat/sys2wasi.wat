;; sys2wasi: the syscall → WASI preview1 adapter (one layer of the ELF ≡ WASI stack).
;;
;; Exports the simulator ABI's `sys.syscall(nr, a1..a6) -> rax` for x86-64 Linux numbering and
;; implements it over `wasi_snapshot_preview1`. Process memory (the simulated address space) is
;; read and written through the `mem.*` module; the adapter's own WASI buffers live in the shared
;; `io.memory` at [0x100000, 0x110100) (WASI p1 reads iovecs from the caller's export "memory",
;; which all WASI-calling modules of the stack share).
;;
;; Syscall subset S₁ (signature, with its WASI image; anything else answers -ENOSYS = -38):
;;   read(fd, buf, n)    0   fd_read(fd, [n'])          rax = bytes read | -errno     (n' ≤ 64 KiB)
;;   write(fd, buf, n)   1   fd_write(fd, [buf[0..n')]) rax = bytes written | -errno  (n' ≤ 64 KiB)
;;   exit(code)         60   proc_exit(code & 255)      (does not return)
;;   exit_group(code)  231   proc_exit(code & 255)      (does not return)
;;   brk(addr)          12   — (memory-model local: mem.map; no WASI call)
;; errno: WASI p1 errno e ↦ -e' with e' the Linux errno of the same name for badf (8→9),
;; inval (28→22), io (29→5), others → -5 (EIO). Lean: Silmaril.Sim.WasiBridge (`SysName`, `toP1`).
(module
  (import "wasi_snapshot_preview1" "fd_read" (func $fd_read (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (import "mem" "load8" (func $ld8 (param i64) (result i64)))
  (import "mem" "store8" (func $st8 (param i64 i64)))
  (import "mem" "map" (func $map (param i64 i64) (result i32)))
  (import "io" "memory" (memory 33))
  (export "memory" (memory 0))
  (global $B i32 (i32.const 0x100000))   ;; iovec at B, nwritten at B+8, data at B+64
  (global $brk (mut i64) (i64.const 0))
  (global $brk0 (mut i64) (i64.const 0))
  (func (export "set_brk") (param $a i64) (global.set $brk (local.get $a)) (global.set $brk0 (local.get $a)))

  (func $errno (param $e i32) (result i64)
    (if (i32.eq (local.get $e) (i32.const 8)) (then (return (i64.const -9))))
    (if (i32.eq (local.get $e) (i32.const 28)) (then (return (i64.const -22))))
    (i64.const -5))

  (func $clamp (param $n i64) (result i32)
    (if (result i32) (i64.gt_u (local.get $n) (i64.const 65536)) (then (i32.const 65536))
      (else (i32.wrap_i64 (local.get $n)))))

  (func $write (param $fd i64) (param $buf i64) (param $n i64) (result i64)
    (local $i i32) (local $k i32) (local $e i32)
    (local.set $k (call $clamp (local.get $n)))
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $i) (local.get $k)))
      (i32.store8 offset=64 (i32.add (global.get $B) (local.get $i))
        (i32.wrap_i64 (call $ld8 (i64.add (local.get $buf) (i64.extend_i32_u (local.get $i))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (i32.store (global.get $B) (i32.add (global.get $B) (i32.const 64)))
    (i32.store offset=4 (global.get $B) (local.get $k))
    (local.set $e (call $fd_write (i32.wrap_i64 (local.get $fd)) (global.get $B) (i32.const 1) (i32.add (global.get $B) (i32.const 8))))
    (if (local.get $e) (then (return (call $errno (local.get $e)))))
    (i64.load32_u offset=8 (global.get $B)))

  (func $read (param $fd i64) (param $buf i64) (param $n i64) (result i64)
    (local $i i32) (local $k i32) (local $e i32) (local $got i32)
    (local.set $k (call $clamp (local.get $n)))
    (i32.store (global.get $B) (i32.add (global.get $B) (i32.const 64)))
    (i32.store offset=4 (global.get $B) (local.get $k))
    (local.set $e (call $fd_read (i32.wrap_i64 (local.get $fd)) (global.get $B) (i32.const 1) (i32.add (global.get $B) (i32.const 8))))
    (if (local.get $e) (then (return (call $errno (local.get $e)))))
    (local.set $got (i32.load offset=8 (global.get $B)))
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $i) (local.get $got)))
      (call $st8 (i64.add (local.get $buf) (i64.extend_i32_u (local.get $i)))
        (i64.load8_u offset=64 (i32.add (global.get $B) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (i64.extend_i32_u (local.get $got)))

  (func (export "syscall") (param $nr i64) (param $a1 i64) (param $a2 i64) (param $a3 i64)
                           (param $a4 i64) (param $a5 i64) (param $a6 i64) (result i64)
    (if (i64.eqz (local.get $nr))
      (then (return (call $read (local.get $a1) (local.get $a2) (local.get $a3)))))
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
