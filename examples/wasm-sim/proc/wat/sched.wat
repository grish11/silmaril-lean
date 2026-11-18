;; sched: threads and a scheduler around ANY simulator following docs/wasm-sim-abi.md (sketch).
;;
;; Thread states are kept in the M layout (Linux `struct user_regs_struct`, 27 x u64, flags
;; packed in `eflags`) at 256 * tid in this module's memory; the running thread's state lives
;; in the simulator. Before every step the scheduler asks the import `sched.pick() -> i32`
;; which thread steps (taken mod the number of threads) and context-switches through the
;; simulator's get/set (save 24 locations into the old block, load the new one).
;;
;; Thread creation is the `clone` system call (56), intercepted here before it reaches `sys`
;; (when rip points at `0f 05` and rax = 56): the child is a copy of the parent with
;; rax = 0, rsp = rsi, both past the syscall; the parent gets rax = child tid. Flags are
;; ignored (CLONE_VM | CLONE_THREAD semantics: one address space). At most 8 threads.
;;
;; Wraps a simulator imported as "core0"; exports get/set/modelled/step so that it can stand
;; in for the simulator under `extrun` (preload as "core").
(module
  (import "core0" "get" (func $get (param i32) (result i64)))
  (import "core0" "set" (func $set (param i32 i64)))
  (import "core0" "modelled" (func $modelled (param i32) (result i32)))
  (import "core0" "step" (func $step (result i32)))
  (import "sched" "pick" (func $pick (result i32)))
  (import "mem" "load16" (func $ld16 (param i64) (result i64)))
  (export "get" (func $get))
  (export "set" (func $set))
  (export "modelled" (func $modelled))
  (memory (export "threads") 1)
  ;; byte offset in user_regs_struct of locations 0..16 (rax .. r15, rip)
  (data (i32.const 4096) "\50\58\60\28\98\20\68\70\48\40\38\30\18\10\08\00\80")
  ;; eflags bit of locations 17..23 (CF PF AF ZF SF OF DF)
  (data (i32.const 4128) "\00\02\04\06\07\0b\0a")
  (global $n (mut i32) (i32.const 1))
  (global $cur (mut i32) (i32.const 0))
  (global $switches (mut i64) (i64.const 0))
  (func (export "switches") (result i64) (global.get $switches))
  (func (export "nthreads") (result i32) (global.get $n))

  ;; save the simulator state into block $t
  (func $save (param $t i32)
    (local $l i32) (local $b i32) (local $fl i64)
    (local.set $b (i32.shl (local.get $t) (i32.const 8)))
    (loop $r
      (i64.store (i32.add (local.get $b) (i32.load8_u offset=4096 (local.get $l))) (call $get (local.get $l)))
      (local.set $l (i32.add (local.get $l) (i32.const 1)))
      (br_if $r (i32.lt_u (local.get $l) (i32.const 17))))
    (local.set $fl (i64.const 0x202))
    (loop $f
      (local.set $fl (i64.or (local.get $fl)
        (i64.shl (i64.and (call $get (local.get $l)) (i64.const 1))
                 (i64.load8_u offset=4096 (i32.add (local.get $l) (i32.const 15))))))
      (local.set $l (i32.add (local.get $l) (i32.const 1)))
      (br_if $f (i32.lt_u (local.get $l) (i32.const 24))))
    (i64.store offset=144 (local.get $b) (local.get $fl)))

  ;; load block $t into the simulator
  (func $load (param $t i32)
    (local $l i32) (local $b i32) (local $fl i64)
    (local.set $b (i32.shl (local.get $t) (i32.const 8)))
    (loop $r
      (call $set (local.get $l) (i64.load (i32.add (local.get $b) (i32.load8_u offset=4096 (local.get $l)))))
      (local.set $l (i32.add (local.get $l) (i32.const 1)))
      (br_if $r (i32.lt_u (local.get $l) (i32.const 17))))
    (local.set $fl (i64.load offset=144 (local.get $b)))
    (loop $f
      (call $set (local.get $l) (i64.and (i64.shr_u (local.get $fl)
        (i64.load8_u offset=4096 (i32.add (local.get $l) (i32.const 15)))) (i64.const 1)))
      (local.set $l (i32.add (local.get $l) (i32.const 1)))
      (br_if $f (i32.lt_u (local.get $l) (i32.const 24)))))

  (func $clone
    (local $t i32) (local $rip i64)
    (if (i32.ge_u (global.get $n) (i32.const 8))
      (then (call $set (i32.const 0) (i64.const -11)) ;; EAGAIN
            (call $set (i32.const 16) (i64.add (call $get (i32.const 16)) (i64.const 2))) (return)))
    (local.set $t (global.get $n))
    (global.set $n (i32.add (global.get $n) (i32.const 1)))
    (local.set $rip (i64.add (call $get (i32.const 16)) (i64.const 2)))
    (call $set (i32.const 16) (local.get $rip))
    ;; child: copy of the parent with rax = 0, rsp = rsi
    (call $save (local.get $t))
    (i64.store offset=80 (i32.shl (local.get $t) (i32.const 8)) (i64.const 0))
    (i64.store offset=152 (i32.shl (local.get $t) (i32.const 8)) (call $get (i32.const 6)))
    ;; parent: rax = tid
    (call $set (i32.const 0) (i64.extend_i32_u (local.get $t))))

  (func (export "step") (result i32)
    (local $t i32) (local $rip i64)
    (local.set $t (i32.rem_u (call $pick) (global.get $n)))
    (if (i32.ne (local.get $t) (global.get $cur))
      (then (call $save (global.get $cur)) (call $load (local.get $t)) (global.set $cur (local.get $t))
            (global.set $switches (i64.add (global.get $switches) (i64.const 1)))))
    (local.set $rip (call $get (i32.const 16)))
    (if (i32.and (i64.eq (call $ld16 (local.get $rip)) (i64.const 0x050f))
                 (i64.eq (call $get (i32.const 0)) (i64.const 56)))
      (then (call $clone) (return (i32.const 0))))
    (call $step))
)
