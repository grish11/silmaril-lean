;; cat: copy stdin to stdout in 64-byte chunks with fd_read/fd_write; proc_exit(0).
(module
  (import "wasi_snapshot_preview1" "fd_read" (func $fd_read (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (memory (export "memory") 1)
  (func (export "_start")
    (local $n i32)
    (loop $l
      (i32.store (i32.const 0) (i32.const 64)) (i32.store (i32.const 4) (i32.const 64))
      (drop (call $fd_read (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 8)))
      (local.set $n (i32.load (i32.const 8)))
      (if (i32.gt_s (local.get $n) (i32.const 0))
        (then
          (i32.store (i32.const 16) (i32.const 64)) (i32.store (i32.const 20) (local.get $n))
          (drop (call $fd_write (i32.const 1) (i32.const 16) (i32.const 1) (i32.const 24)))
          (br $l))))
    (call $proc_exit (i32.const 0))))
