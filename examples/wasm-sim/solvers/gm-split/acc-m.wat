;; GENERATED from src-state-m.wat (x86 simulator): the five state accessors of representation M.
(module
;; State representation M: Linux x86-64 `struct user_regs_struct` (27 x u64) at offset 0 of the
;; exported memory `state`: r15 r14 r13 r12 rbp rbx r11 r10 r9 r8 rax rcx rdx rsi rdi orig_rax
;; rip cs eflags rsp ss fs_base gs_base ds es fs gs; flags packed in eflags (offset 144).
;; Offset 216: u64 valid mask (bit loc = defined; all modelled locations, 0..23, are always
;; valid in this simulator). Offsets 256..272: loc -> byte offset table; 280..286: flag loc ->
;; eflags bit table. Provides $rget/$rset/$fget/$fset/$fset6 like state-g.wat.
  (memory $state (export "state") 1)
  (data (i32.const 144) "\02\02")
  (data (i32.const 216) "\ff\ff\ff\00\00\00\00\00")
  ;; rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 rip
  (data (i32.const 256) "\50\58\60\28\98\20\68\70\48\40\38\30\18\10\08\00\80")
  ;; CF PF AF ZF SF OF DF
  (data (i32.const 280) "\00\02\04\06\07\0b\0a")
  (func $rget (param $r i32) (result i64)
    (i64.load (i32.load8_u offset=256 (local.get $r))))
  (func $rset (param $r i32) (param $v i64)
    (i64.store (i32.load8_u offset=256 (local.get $r)) (local.get $v)))
  (func $fget (param $f i32) (result i32)
    (i32.and (i32.shr_u (i32.load offset=144 (i32.const 0))
                        (i32.load8_u offset=263 (local.get $f))) (i32.const 1)))
  (func $fset (param $f i32) (param $v i32)
    (local $b i32)
    (local.set $b (i32.load8_u offset=263 (local.get $f)))
    (i32.store offset=144 (i32.const 0)
      (i32.or (i32.and (i32.load offset=144 (i32.const 0))
                       (i32.xor (i32.shl (i32.const 1) (local.get $b)) (i32.const -1)))
              (i32.shl (i32.and (local.get $v) (i32.const 1)) (local.get $b)))))
  (func $fset6 (param $c i32) (param $p i32) (param $a i32) (param $z i32) (param $s i32) (param $o i32)
    (i32.store offset=144 (i32.const 0)
      (i32.or (i32.and (i32.load offset=144 (i32.const 0)) (i32.const 0xfffff72a))
        (i32.or (i32.or (i32.or (local.get $c) (i32.shl (local.get $p) (i32.const 2)))
                        (i32.or (i32.shl (local.get $a) (i32.const 4)) (i32.shl (local.get $z) (i32.const 6))))
                (i32.or (i32.shl (local.get $s) (i32.const 7)) (i32.shl (local.get $o) (i32.const 11)))))))
  (export "rget" (func $rget)) (export "rset" (func $rset)) (export "fget" (func $fget))
  (export "fset" (func $fset)) (export "fset6" (func $fset6))
)
