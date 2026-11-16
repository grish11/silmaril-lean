;; wasi2sys: the WASI preview1 → syscall adapter (the reverse layer).
;;
;; Exports `wasi_snapshot_preview1` functions of the subset P₁ and implements each by x86-64
;; Linux syscalls through the import `sys.syscall`. The WASI program's linear memory is imported
;; as `app.appmem` (its `memory` export, renamed when linking), and is offered to the syscall layer as the process memory (`mem.*` exports:
;; process address a = linear-memory address a, a < 2^32). Linking needs the cycle
;; app → wasi2sys → (sys) → wasi2sys.mem / app.memory, so the stack is wasm-merge'd
;; (see check.sh), or run under an embedder that provides `sys.syscall` natively.
;;
;; P₁ and its syscall image (errno: -e ↦ WASI errno of the same name; badf 9→8, inval 22→28,
;; else io 29):
;;   fd_write(fd, iovs, n, nw)   one write(fd, iov.buf, iov.len) per iovec, stop on a short write
;;   fd_read(fd, iovs, n, nr)    one read(fd, iov.buf, iov.len) per iovec, stop on a short read
;;   proc_exit(code)             exit_group(code)
;;   args_sizes_get, environ_sizes_get   0, 0 (no syscall)   args_get, environ_get   no-ops
;; Everything else is not exported (linking fails: the subset is the signature).
(module
  (import "sys" "syscall" (func $sys (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "app" "appmem" (memory 1))

  ;; the process memory seen by the syscall layer = the WASI program's memory
  (func (export "load8") (param $a i64) (result i64) (i64.load8_u (i32.wrap_i64 (local.get $a))))
  (func (export "load16") (param $a i64) (result i64) (i64.load16_u (i32.wrap_i64 (local.get $a))))
  (func (export "load32") (param $a i64) (result i64) (i64.load32_u (i32.wrap_i64 (local.get $a))))
  (func (export "load64") (param $a i64) (result i64) (i64.load (i32.wrap_i64 (local.get $a))))
  (func (export "store8") (param $a i64) (param $v i64) (i64.store8 (i32.wrap_i64 (local.get $a)) (local.get $v)))
  (func (export "store16") (param $a i64) (param $v i64) (i64.store16 (i32.wrap_i64 (local.get $a)) (local.get $v)))
  (func (export "store32") (param $a i64) (param $v i64) (i64.store32 (i32.wrap_i64 (local.get $a)) (local.get $v)))
  (func (export "store64") (param $a i64) (param $v i64) (i64.store (i32.wrap_i64 (local.get $a)) (local.get $v)))
  (func (export "map") (param i64 i64) (result i32) (i32.const 0))

  (func $errno (param $r i64) (result i32)
    (if (i64.eq (local.get $r) (i64.const -9)) (then (return (i32.const 8))))
    (if (i64.eq (local.get $r) (i64.const -22)) (then (return (i32.const 28))))
    (i32.const 29))

  ;; one syscall per iovec (nr 0 read / 1 write)
  (func $rw (param $nr i64) (param $fd i32) (param $iovs i32) (param $n i32) (param $out i32) (result i32)
    (local $i i32) (local $total i32) (local $len i32) (local $r i64)
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $i) (local.get $n)))
      (local.set $len (i32.load offset=4 (i32.add (local.get $iovs) (i32.shl (local.get $i) (i32.const 3)))))
      (local.set $r (call $sys (local.get $nr) (i64.extend_i32_u (local.get $fd))
        (i64.extend_i32_u (i32.load (i32.add (local.get $iovs) (i32.shl (local.get $i) (i32.const 3)))))
        (i64.extend_i32_u (local.get $len)) (i64.const 0) (i64.const 0) (i64.const 0)))
      (if (i64.lt_s (local.get $r) (i64.const 0))
        (then (if (i32.eqz (local.get $total)) (then (return (call $errno (local.get $r))))) (br $o)))
      (local.set $total (i32.add (local.get $total) (i32.wrap_i64 (local.get $r))))
      (br_if $o (i64.lt_u (local.get $r) (i64.extend_i32_u (local.get $len))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (i32.store (local.get $out) (local.get $total))
    (i32.const 0))

  (func (export "fd_write") (param $fd i32) (param $iovs i32) (param $n i32) (param $nw i32) (result i32)
    (call $rw (i64.const 1) (local.get $fd) (local.get $iovs) (local.get $n) (local.get $nw)))
  (func (export "fd_read") (param $fd i32) (param $iovs i32) (param $n i32) (param $nr i32) (result i32)
    (call $rw (i64.const 0) (local.get $fd) (local.get $iovs) (local.get $n) (local.get $nr)))
  (func (export "proc_exit") (param $code i32)
    (drop (call $sys (i64.const 231) (i64.extend_i32_u (local.get $code)) (i64.const 0) (i64.const 0)
      (i64.const 0) (i64.const 0) (i64.const 0)))
    (unreachable))
  (func (export "args_sizes_get") (param $c i32) (param $s i32) (result i32)
    (i32.store (local.get $c) (i32.const 0)) (i32.store (local.get $s) (i32.const 0)) (i32.const 0))
  (func (export "environ_sizes_get") (param $c i32) (param $s i32) (result i32)
    (i32.store (local.get $c) (i32.const 0)) (i32.store (local.get $s) (i32.const 0)) (i32.const 0))
  (func (export "args_get") (param i32 i32) (result i32) (i32.const 0))
  (func (export "environ_get") (param i32 i32) (result i32) (i32.const 0))
)
