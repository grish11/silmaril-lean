;; Shared simulator for split problems: G state + methods; memory through mem.* imports.
;; x86-64 subset simulator: imports (environment), see docs/wasm-sim-abi.md.
;; Assembled by `wasm-sim gen-x86`: header ++ mem-import ++ state-{g,m} ++ core ++ decode ++ ")".
(module
  (import "sys" "syscall" (func $syscall (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "nd" "undef" (func $undef (param i32) (result i64)))
;; Memory as opaque imports (P-mem; the environment owns memory).
  (import "mem" "load8"  (func $load8  (param i64) (result i64)))
  (import "mem" "load16" (func $load16 (param i64) (result i64)))
  (import "mem" "load32" (func $load32 (param i64) (result i64)))
  (import "mem" "load64" (func $load64 (param i64) (result i64)))
  (import "mem" "store8"  (func $store8  (param i64 i64)))
  (import "mem" "store16" (func $store16 (param i64 i64)))
  (import "mem" "store32" (func $store32 (param i64 i64)))
  (import "mem" "store64" (func $store64 (param i64 i64)))
;; State representation G: one mutable global per location.
;; Provides $rget/$rset (loc 0..16: GPRs, rip), $fget/$fset (loc 17..23: flags, i32 0/1),
;; $fset6 (cf pf af zf sf of).
  (global $r0 (mut i64) (i64.const 0))
  (global $r1 (mut i64) (i64.const 0))
  (global $r2 (mut i64) (i64.const 0))
  (global $r3 (mut i64) (i64.const 0))
  (global $r4 (mut i64) (i64.const 0))
  (global $r5 (mut i64) (i64.const 0))
  (global $r6 (mut i64) (i64.const 0))
  (global $r7 (mut i64) (i64.const 0))
  (global $r8 (mut i64) (i64.const 0))
  (global $r9 (mut i64) (i64.const 0))
  (global $r10 (mut i64) (i64.const 0))
  (global $r11 (mut i64) (i64.const 0))
  (global $r12 (mut i64) (i64.const 0))
  (global $r13 (mut i64) (i64.const 0))
  (global $r14 (mut i64) (i64.const 0))
  (global $r15 (mut i64) (i64.const 0))
  (global $rip (mut i64) (i64.const 0))
  (global $cf (mut i32) (i32.const 0))
  (global $pf (mut i32) (i32.const 0))
  (global $af (mut i32) (i32.const 0))
  (global $zf (mut i32) (i32.const 0))
  (global $sf (mut i32) (i32.const 0))
  (global $of (mut i32) (i32.const 0))
  (global $df (mut i32) (i32.const 0))
  (func $rget (param $r i32) (result i64)
    (block $default
    (block $L16
    (block $L15
    (block $L14
    (block $L13
    (block $L12
    (block $L11
    (block $L10
    (block $L9
    (block $L8
    (block $L7
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $L7 $L8 $L9 $L10 $L11 $L12 $L13 $L14 $L15 $L16 $default (local.get $r)))
      (return (global.get $r0)))
      (return (global.get $r1)))
      (return (global.get $r2)))
      (return (global.get $r3)))
      (return (global.get $r4)))
      (return (global.get $r5)))
      (return (global.get $r6)))
      (return (global.get $r7)))
      (return (global.get $r8)))
      (return (global.get $r9)))
      (return (global.get $r10)))
      (return (global.get $r11)))
      (return (global.get $r12)))
      (return (global.get $r13)))
      (return (global.get $r14)))
      (return (global.get $r15)))
      (return (global.get $rip)))
    (unreachable))
  (func $rset (param $r i32) (param $v i64)
    (block $default
    (block $L16
    (block $L15
    (block $L14
    (block $L13
    (block $L12
    (block $L11
    (block $L10
    (block $L9
    (block $L8
    (block $L7
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $L7 $L8 $L9 $L10 $L11 $L12 $L13 $L14 $L15 $L16 $default (local.get $r)))
      (global.set $r0 (local.get $v)) (return))
      (global.set $r1 (local.get $v)) (return))
      (global.set $r2 (local.get $v)) (return))
      (global.set $r3 (local.get $v)) (return))
      (global.set $r4 (local.get $v)) (return))
      (global.set $r5 (local.get $v)) (return))
      (global.set $r6 (local.get $v)) (return))
      (global.set $r7 (local.get $v)) (return))
      (global.set $r8 (local.get $v)) (return))
      (global.set $r9 (local.get $v)) (return))
      (global.set $r10 (local.get $v)) (return))
      (global.set $r11 (local.get $v)) (return))
      (global.set $r12 (local.get $v)) (return))
      (global.set $r13 (local.get $v)) (return))
      (global.set $r14 (local.get $v)) (return))
      (global.set $r15 (local.get $v)) (return))
      (global.set $rip (local.get $v)) (return))
    (unreachable))
  (func $fget (param $f i32) (result i32)
    (block $default
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $default (i32.sub (local.get $f) (i32.const 17))))
      (return (global.get $cf)))
      (return (global.get $pf)))
      (return (global.get $af)))
      (return (global.get $zf)))
      (return (global.get $sf)))
      (return (global.get $of)))
      (return (global.get $df)))
    (unreachable))
  (func $fset (param $f i32) (param $v i32)
    (block $default
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $default (i32.sub (local.get $f) (i32.const 17))))
      (global.set $cf (local.get $v)) (return))
      (global.set $pf (local.get $v)) (return))
      (global.set $af (local.get $v)) (return))
      (global.set $zf (local.get $v)) (return))
      (global.set $sf (local.get $v)) (return))
      (global.set $of (local.get $v)) (return))
      (global.set $df (local.get $v)) (return))
    (unreachable))
  (func $fset6 (param $c i32) (param $p i32) (param $a i32) (param $z i32) (param $s i32) (param $o i32)
    (global.set $cf (local.get $c)) (global.set $pf (local.get $p)) (global.set $af (local.get $a))
    (global.set $zf (local.get $z)) (global.set $sf (local.get $s)) (global.set $of (local.get $o)))
;; x86-64 subset: instruction semantics, decoder (`step`, P-mem) and method API (`i_*`, P-calls).
;; Uses only $rget/$rset/$fget/$fset/$fset6 from the state fragment (G or M).
;; Operand size `w` is in bytes (1, 2, 4, 8). Register codes: 0..15 GPRs; for w = 1, codes
;; 16..19 are ah ch dh bh. Locations: 0..15 GPRs, 16 rip, 17 CF 18 PF 19 AF 20 ZF 21 SF 22 OF 23 DF.
;; Memory accesses happen before register/flag writes, so a faulting (trapping) access leaves
;; the state unchanged -- except read-modify-write forms, whose store (to an address just read)
;; follows the flag update.

  ;; ---------------------------------------------------------------- generic helpers
  (func $mask (param $w i32) (result i64)
    (if (result i64) (i32.eq (local.get $w) (i32.const 8))
      (then (i64.const -1))
      (else (i64.sub (i64.shl (i64.const 1) (i64.extend_i32_u (i32.shl (local.get $w) (i32.const 3))))
                     (i64.const 1)))))
  (func $sbit (param $w i32) (result i64)
    (i64.shl (i64.const 1) (i64.extend_i32_u (i32.sub (i32.shl (local.get $w) (i32.const 3)) (i32.const 1)))))
  ;; sign-extend the low w bytes
  (func $sext (param $w i32) (param $v i64) (result i64)
    (local $s i64)
    (local.set $s (i64.extend_i32_u (i32.sub (i32.const 64) (i32.shl (local.get $w) (i32.const 3)))))
    (i64.shr_s (i64.shl (local.get $v) (local.get $s)) (local.get $s)))
  ;; an undefined flag: low bit of nd.undef(loc)
  (func $u (param $loc i32) (result i32)
    (i32.and (i32.wrap_i64 (call $undef (local.get $loc))) (i32.const 1)))
  (func $parity (param $r i64) (result i32)
    (i32.eqz (i32.and (i32.popcnt (i32.and (i32.wrap_i64 (local.get $r)) (i32.const 0xff))) (i32.const 1))))
  ;; set all six status flags; PF/ZF/SF from the (masked) result r
  (func $fres (param $w i32) (param $r i64) (param $cf i32) (param $af i32) (param $of i32)
    (call $fset6 (local.get $cf) (call $parity (local.get $r)) (local.get $af)
      (i64.eqz (local.get $r))
      (i64.ne (i64.and (local.get $r) (call $sbit (local.get $w))) (i64.const 0))
      (local.get $of)))

  ;; register read/write with operand size
  (func $rd (param $w i32) (param $r i32) (result i64)
    (if (i32.ge_u (local.get $r) (i32.const 16))
      (then (return (i64.and (i64.shr_u (call $rget (i32.sub (local.get $r) (i32.const 16))) (i64.const 8))
                             (i64.const 0xff)))))
    (i64.and (call $rget (local.get $r)) (call $mask (local.get $w))))
  (func $wr (param $w i32) (param $r i32) (param $v i64)
    (local $m i64)
    (if (i32.ge_u (local.get $r) (i32.const 16))
      (then
        (local.set $r (i32.sub (local.get $r) (i32.const 16)))
        (call $rset (local.get $r)
          (i64.or (i64.and (call $rget (local.get $r)) (i64.const 0xffffffffffff00ff))
                  (i64.shl (i64.and (local.get $v) (i64.const 0xff)) (i64.const 8))))
        (return)))
    (if (i32.ge_u (local.get $w) (i32.const 4))
      (then (call $rset (local.get $r) (i64.and (local.get $v) (call $mask (local.get $w)))) (return)))
    (local.set $m (call $mask (local.get $w)))
    (call $rset (local.get $r)
      (i64.or (i64.and (call $rget (local.get $r)) (i64.xor (local.get $m) (i64.const -1)))
              (i64.and (local.get $v) (local.get $m)))))

  ;; memory with operand size
  (func $ld (param $w i32) (param $a i64) (result i64)
    (if (i32.eq (local.get $w) (i32.const 8)) (then (return (call $load64 (local.get $a)))))
    (if (i32.eq (local.get $w) (i32.const 4)) (then (return (call $load32 (local.get $a)))))
    (if (i32.eq (local.get $w) (i32.const 2)) (then (return (call $load16 (local.get $a)))))
    (call $load8 (local.get $a)))
  (func $st (param $w i32) (param $a i64) (param $v i64)
    (if (i32.eq (local.get $w) (i32.const 8)) (then (call $store64 (local.get $a) (local.get $v)) (return)))
    (if (i32.eq (local.get $w) (i32.const 4)) (then (call $store32 (local.get $a) (local.get $v)) (return)))
    (if (i32.eq (local.get $w) (i32.const 2)) (then (call $store16 (local.get $a) (local.get $v)) (return)))
    (call $store8 (local.get $a) (local.get $v)))

  ;; condition codes, Intel tttn order
  (func $cond (export "cond") (param $cc i32) (result i32)
    (local $b i32)
    (block $done
    (block $c7 (block $c6 (block $c5 (block $c4 (block $c3 (block $c2 (block $c1 (block $c0
      (br_table $c0 $c1 $c2 $c3 $c4 $c5 $c6 $c7
        (i32.and (i32.shr_u (local.get $cc) (i32.const 1)) (i32.const 7))))
      (local.set $b (call $fget (i32.const 22))) (br $done))                       ;; O
      (local.set $b (call $fget (i32.const 17))) (br $done))                       ;; B
      (local.set $b (call $fget (i32.const 20))) (br $done))                       ;; E
      (local.set $b (i32.or (call $fget (i32.const 17)) (call $fget (i32.const 20)))) (br $done)) ;; BE
      (local.set $b (call $fget (i32.const 21))) (br $done))                       ;; S
      (local.set $b (call $fget (i32.const 18))) (br $done))                       ;; P
      (local.set $b (i32.xor (call $fget (i32.const 21)) (call $fget (i32.const 22)))) (br $done)) ;; L
      (local.set $b (i32.or (call $fget (i32.const 20))
                            (i32.xor (call $fget (i32.const 21)) (call $fget (i32.const 22))))))  ;; LE
    (i32.xor (local.get $b) (i32.and (local.get $cc) (i32.const 1))))

  ;; packed rflags (bit 1 and IF set, as seen by user code)
  (func $eflags (result i64)
    (i64.extend_i32_u
      (i32.or (i32.const 0x202)
      (i32.or (i32.or (i32.or (call $fget (i32.const 17)) (i32.shl (call $fget (i32.const 18)) (i32.const 2)))
                      (i32.or (i32.shl (call $fget (i32.const 19)) (i32.const 4)) (i32.shl (call $fget (i32.const 20)) (i32.const 6))))
              (i32.or (i32.or (i32.shl (call $fget (i32.const 21)) (i32.const 7)) (i32.shl (call $fget (i32.const 22)) (i32.const 11)))
                      (i32.shl (call $fget (i32.const 23)) (i32.const 10)))))))

  ;; ---------------------------------------------------------------- semantics
  ;; ALU: op 0 add 1 or 2 adc 3 sbb 4 and 5 sub 6 xor 7 cmp 8 test; a, b masked; result masked
  (func $alu (param $op i32) (param $w i32) (param $a i64) (param $b i64) (result i64)
    (local $r i64) (local $m i64) (local $s i64) (local $c i64) (local $cf i32) (local $of i32)
    (local.set $m (call $mask (local.get $w)))
    (local.set $s (call $sbit (local.get $w)))
    (block $arith
    (block $logic
    (block $sub (block $xor (block $and (block $sbb (block $adc (block $or (block $add
      (br_table $add $or $adc $sbb $and $sub $xor $sub $and (local.get $op)))
      ;; add
      (local.set $r (i64.and (i64.add (local.get $a) (local.get $b)) (local.get $m)))
      (local.set $cf (i64.lt_u (local.get $r) (local.get $a)))
      (local.set $of (i64.ne (i64.and (i64.and (i64.xor (local.get $a) (local.get $r))
                                               (i64.xor (local.get $b) (local.get $r))) (local.get $s)) (i64.const 0)))
      (br $arith))
      ;; or
      (local.set $r (i64.or (local.get $a) (local.get $b))) (br $logic))
      ;; adc
      (local.set $c (i64.extend_i32_u (call $fget (i32.const 17))))
      (local.set $r (i64.and (i64.add (i64.add (local.get $a) (local.get $b)) (local.get $c)) (local.get $m)))
      (local.set $cf (i32.or (i64.lt_u (local.get $r) (local.get $a))
                             (i32.and (i32.wrap_i64 (local.get $c)) (i64.eq (local.get $r) (local.get $a)))))
      (local.set $of (i64.ne (i64.and (i64.and (i64.xor (local.get $a) (local.get $r))
                                               (i64.xor (local.get $b) (local.get $r))) (local.get $s)) (i64.const 0)))
      (br $arith))
      ;; sbb
      (local.set $c (i64.extend_i32_u (call $fget (i32.const 17))))
      (local.set $r (i64.and (i64.sub (i64.sub (local.get $a) (local.get $b)) (local.get $c)) (local.get $m)))
      (local.set $cf (i32.or (i64.lt_u (local.get $a) (local.get $b))
                             (i32.and (i32.wrap_i64 (local.get $c)) (i64.eq (local.get $a) (local.get $b)))))
      (local.set $of (i64.ne (i64.and (i64.and (i64.xor (local.get $a) (local.get $b))
                                               (i64.xor (local.get $a) (local.get $r))) (local.get $s)) (i64.const 0)))
      (br $arith))
      ;; and / test
      (local.set $r (i64.and (local.get $a) (local.get $b))) (br $logic))
      ;; xor
      (local.set $r (i64.xor (local.get $a) (local.get $b))) (br $logic))
      ;; sub / cmp
      (local.set $r (i64.and (i64.sub (local.get $a) (local.get $b)) (local.get $m)))
      (local.set $cf (i64.lt_u (local.get $a) (local.get $b)))
      (local.set $of (i64.ne (i64.and (i64.and (i64.xor (local.get $a) (local.get $b))
                                               (i64.xor (local.get $a) (local.get $r))) (local.get $s)) (i64.const 0)))
      (br $arith))
    ;; logic: CF = OF = 0, AF undefined
    (call $fres (local.get $w) (local.get $r) (i32.const 0) (call $u (i32.const 19)) (i32.const 0))
    (return (local.get $r)))
    ;; arith: AF = carry out of bit 3
    (call $fres (local.get $w) (local.get $r) (local.get $cf)
      (i32.wrap_i64 (i64.and (i64.shr_u (i64.xor (i64.xor (local.get $a) (local.get $b)) (local.get $r)) (i64.const 4)) (i64.const 1)))
      (local.get $of))
    (local.get $r))

  ;; unary: op 0 inc 1 dec 2 not 3 neg; a masked
  (func $unary (param $op i32) (param $w i32) (param $a i64) (result i64)
    (local $r i64) (local $s i64)
    (local.set $s (call $sbit (local.get $w)))
    (if (i32.eq (local.get $op) (i32.const 2))
      (then (return (i64.xor (local.get $a) (call $mask (local.get $w))))))
    (if (i32.eq (local.get $op) (i32.const 3))
      (then (return (call $alu (i32.const 5) (local.get $w) (i64.const 0) (local.get $a)))))
    (if (i32.eqz (local.get $op))
      (then (local.set $r (i64.and (i64.add (local.get $a) (i64.const 1)) (call $mask (local.get $w))))
            (call $fres (local.get $w) (local.get $r) (call $fget (i32.const 17))
              (i64.eqz (i64.and (local.get $r) (i64.const 15)))
              (i64.eq (local.get $r) (local.get $s))))
      (else (local.set $r (i64.and (i64.sub (local.get $a) (i64.const 1)) (call $mask (local.get $w))))
            (call $fres (local.get $w) (local.get $r) (call $fget (i32.const 17))
              (i64.eq (i64.and (local.get $r) (i64.const 15)) (i64.const 15))
              (i64.eq (local.get $a) (local.get $s)))))
    (local.get $r))

  ;; shifts and rotates (Intel /digit): op 0 rol 1 ror 4 shl 5 shr 7 sar; any w; a masked; cnt raw.
  ;; Count masked to 6 bits (w = 8) or 5 bits; masked count 0: no flag change. SHL/SHR with
  ;; count >= operand bits: result 0, CF undefined. OF defined only for count 1; AF undefined.
  ;; Rotates change only CF and OF.
  (func $shift (param $op i32) (param $w i32) (param $a i64) (param $cnt i32) (result i64)
    (local $n i64) (local $r i64) (local $cf i32) (local $of i32) (local $bits i64) (local $sa i64) (local $m i64) (local $rc i64)
    (local.set $bits (i64.extend_i32_u (i32.shl (local.get $w) (i32.const 3))))
    (local.set $m (call $mask (local.get $w)))
    (local.set $n (i64.extend_i32_u (i32.and (local.get $cnt)
      (select (i32.const 63) (i32.const 31) (i32.eq (local.get $w) (i32.const 8))))))
    (if (i64.eqz (local.get $n)) (then (return (local.get $a))))
    (if (i32.lt_u (local.get $op) (i32.const 2))
      (then
        (local.set $rc (i64.rem_u (local.get $n) (local.get $bits)))
        (local.set $r (local.get $a))
        (if (i64.ne (local.get $rc) (i64.const 0))
          (then
            (if (i32.eqz (local.get $op))
              (then (local.set $r (i64.and (i64.or (i64.shl (local.get $a) (local.get $rc))
                                                   (i64.shr_u (local.get $a) (i64.sub (local.get $bits) (local.get $rc))))
                                           (local.get $m))))
              (else (local.set $r (i64.and (i64.or (i64.shr_u (local.get $a) (local.get $rc))
                                                   (i64.shl (local.get $a) (i64.sub (local.get $bits) (local.get $rc))))
                                           (local.get $m)))))))
        (if (i32.eqz (local.get $op))
          (then (local.set $cf (i32.wrap_i64 (i64.and (local.get $r) (i64.const 1))))
                (local.set $of (i32.xor (local.get $cf)
                  (i64.ne (i64.and (local.get $r) (call $sbit (local.get $w))) (i64.const 0)))))
          (else (local.set $cf (i64.ne (i64.and (local.get $r) (call $sbit (local.get $w))) (i64.const 0)))
                (local.set $of (i32.xor (local.get $cf)
                  (i64.ne (i64.and (local.get $r) (i64.shr_u (call $sbit (local.get $w)) (i64.const 1))) (i64.const 0))))))
        (if (i64.ne (local.get $n) (i64.const 1)) (then (local.set $of (call $u (i32.const 22)))))
        (call $fset (i32.const 17) (local.get $cf))
        (call $fset (i32.const 22) (local.get $of))
        (return (local.get $r))))
    (if (i32.eq (local.get $op) (i32.const 4))
      (then
        (if (i64.lt_u (local.get $n) (local.get $bits))
          (then (local.set $r (i64.and (i64.shl (local.get $a) (local.get $n)) (local.get $m)))
                (local.set $cf (i32.wrap_i64 (i64.and (i64.shr_u (local.get $a) (i64.sub (local.get $bits) (local.get $n))) (i64.const 1)))))
          (else (local.set $r (i64.const 0)) (local.set $cf (call $u (i32.const 17)))))
        (local.set $of (i32.xor (local.get $cf)
          (i64.ne (i64.and (local.get $r) (call $sbit (local.get $w))) (i64.const 0))))))
    (if (i32.eq (local.get $op) (i32.const 5))
      (then
        (if (i64.lt_u (local.get $n) (local.get $bits))
          (then (local.set $r (i64.shr_u (local.get $a) (local.get $n)))
                (local.set $cf (i32.wrap_i64 (i64.and (i64.shr_u (local.get $a) (i64.sub (local.get $n) (i64.const 1))) (i64.const 1)))))
          (else (local.set $r (i64.const 0)) (local.set $cf (call $u (i32.const 17)))))
        (local.set $of (i64.ne (i64.and (local.get $a) (call $sbit (local.get $w))) (i64.const 0)))))
    (if (i32.eq (local.get $op) (i32.const 7))
      (then
        (local.set $sa (call $sext (local.get $w) (local.get $a)))
        (local.set $r (i64.and (i64.shr_s (local.get $sa) (local.get $n)) (local.get $m)))
        (local.set $cf (i32.wrap_i64 (i64.and (i64.shr_s (local.get $sa) (i64.sub (local.get $n) (i64.const 1))) (i64.const 1))))
        (local.set $of (i32.const 0))))
    (if (i64.ne (local.get $n) (i64.const 1)) (then (local.set $of (call $u (i32.const 22)))))
    (call $fres (local.get $w) (local.get $r) (local.get $cf) (call $u (i32.const 19)) (local.get $of))
    (local.get $r))

  ;; bit counting into register d: op 0 popcnt 1 tzcnt 2 lzcnt 3 bsf 4 bsr; s masked.
  ;; bsf/bsr with s = 0: ZF = 1 and the destination is undefined (whole register: nd.undef(d)).
  (func $bitop (param $op i32) (param $w i32) (param $d i32) (param $s i64)
    (local $r i64) (local $bits i64) (local $z i32)
    (local.set $bits (i64.extend_i32_u (i32.shl (local.get $w) (i32.const 3))))
    (local.set $z (i64.eqz (local.get $s)))
    (if (i32.eqz (local.get $op))
      (then (call $wr (local.get $w) (local.get $d) (i64.popcnt (local.get $s)))
            (call $fset6 (i32.const 0) (i32.const 0) (i32.const 0) (local.get $z) (i32.const 0) (i32.const 0))
            (return)))
    (if (i32.le_u (local.get $op) (i32.const 2))
      (then
        (local.set $r (if (result i64) (i32.eq (local.get $op) (i32.const 1))
          (then (select (local.get $bits) (i64.ctz (local.get $s)) (local.get $z)))
          (else (i64.sub (i64.clz (local.get $s)) (i64.sub (i64.const 64) (local.get $bits))))))
        (call $wr (local.get $w) (local.get $d) (local.get $r))
        (call $fset6 (local.get $z) (call $u (i32.const 18)) (call $u (i32.const 19)) (i64.eqz (local.get $r))
          (call $u (i32.const 21)) (call $u (i32.const 22)))
        (return)))
    (if (local.get $z)
      (then (call $rset (local.get $d) (call $undef (local.get $d))))
      (else (call $wr (local.get $w) (local.get $d)
              (if (result i64) (i32.eq (local.get $op) (i32.const 3))
                (then (i64.ctz (local.get $s)))
                (else (i64.sub (i64.const 63) (i64.clz (local.get $s))))))))
    (call $fset6 (call $u (i32.const 17)) (call $u (i32.const 18)) (call $u (i32.const 19)) (local.get $z)
      (call $u (i32.const 21)) (call $u (i32.const 22))))

  ;; high 64 bits of the unsigned / signed 128-bit product
  (func $umulh (param $a i64) (param $b i64) (result i64)
    (local $al i64) (local $ah i64) (local $bl i64) (local $bh i64) (local $t i64) (local $u i64) (local $v i64)
    (local.set $al (i64.and (local.get $a) (i64.const 0xffffffff)))
    (local.set $ah (i64.shr_u (local.get $a) (i64.const 32)))
    (local.set $bl (i64.and (local.get $b) (i64.const 0xffffffff)))
    (local.set $bh (i64.shr_u (local.get $b) (i64.const 32)))
    (local.set $t (i64.mul (local.get $al) (local.get $bl)))
    (local.set $u (i64.add (i64.mul (local.get $ah) (local.get $bl)) (i64.shr_u (local.get $t) (i64.const 32))))
    (local.set $v (i64.add (i64.mul (local.get $al) (local.get $bh)) (i64.and (local.get $u) (i64.const 0xffffffff))))
    (i64.add (i64.add (i64.mul (local.get $ah) (local.get $bh)) (i64.shr_u (local.get $u) (i64.const 32)))
             (i64.shr_u (local.get $v) (i64.const 32))))
  (func $smulh (param $a i64) (param $b i64) (result i64)
    (i64.sub (i64.sub (call $umulh (local.get $a) (local.get $b))
                      (select (local.get $b) (i64.const 0) (i64.lt_s (local.get $a) (i64.const 0))))
             (select (local.get $a) (i64.const 0) (i64.lt_s (local.get $b) (i64.const 0)))))

  ;; imul (2/3 operand), any w: CF = OF = truncation; SF ZF AF PF undefined
  (func $imul (param $w i32) (param $a i64) (param $b i64) (result i64)
    (local $r i64) (local $o i32) (local $full i64)
    (if (i32.eq (local.get $w) (i32.const 8))
      (then (local.set $r (i64.mul (local.get $a) (local.get $b)))
            (local.set $o (i64.ne (call $smulh (local.get $a) (local.get $b))
                                  (i64.shr_s (local.get $r) (i64.const 63)))))
      (else (local.set $full (i64.mul (call $sext (local.get $w) (local.get $a)) (call $sext (local.get $w) (local.get $b))))
            (local.set $r (i64.and (local.get $full) (call $mask (local.get $w))))
            (local.set $o (i64.ne (local.get $full) (call $sext (local.get $w) (local.get $full))))))
    (call $fset6 (local.get $o) (call $u (i32.const 18)) (call $u (i32.const 19))
      (call $u (i32.const 20)) (call $u (i32.const 21)) (local.get $o))
    (local.get $r))

  ;; unsigned 128/64 division, requires hi < d; quotient returned, remainder in $rem
  (global $rem (mut i64) (i64.const 0))
  (func $udiv128 (param $hi i64) (param $lo i64) (param $d i64) (result i64)
    (local $q i64) (local $i i32) (local $c i32)
    (if (i64.eqz (local.get $hi))
      (then (global.set $rem (i64.rem_u (local.get $lo) (local.get $d)))
            (return (i64.div_u (local.get $lo) (local.get $d)))))
    (local.set $i (i32.const 64))
    (loop $l
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (local.set $c (i64.ne (i64.shr_u (local.get $hi) (i64.const 63)) (i64.const 0)))
      (local.set $hi (i64.or (i64.shl (local.get $hi) (i64.const 1))
                             (i64.and (i64.shr_u (local.get $lo) (i64.extend_i32_u (local.get $i))) (i64.const 1))))
      (local.set $q (i64.shl (local.get $q) (i64.const 1)))
      (if (i32.or (local.get $c) (i64.ge_u (local.get $hi) (local.get $d)))
        (then (local.set $hi (i64.sub (local.get $hi) (local.get $d)))
              (local.set $q (i64.or (local.get $q) (i64.const 1)))))
      (br_if $l (local.get $i)))
    (global.set $rem (local.get $hi))
    (local.get $q))

  ;; one-operand mul/imul/div/idiv (op 4..7) on rdx:rax, w = 4 or 8, source value s (masked).
  ;; Returns 0, or 3 (#DE) leaving the state unchanged.
  (func $muldiv (param $op i32) (param $w i32) (param $s i64) (result i32)
    (local $a i64) (local $d i64) (local $lo i64) (local $hi i64) (local $o i32)
    (local $neg i32) (local $dn i32) (local $q i64) (local $r i64) (local $ad i64) (local $alo i64) (local $ahi i64)
    (local.set $a (call $rd (local.get $w) (i32.const 0)))
    (local.set $d (call $rd (local.get $w) (i32.const 2)))
    (if (i32.lt_u (local.get $op) (i32.const 6))
      (then
        (if (i32.eq (local.get $w) (i32.const 8))
          (then (local.set $lo (i64.mul (local.get $a) (local.get $s)))
                (if (i32.eq (local.get $op) (i32.const 4))
                  (then (local.set $hi (call $umulh (local.get $a) (local.get $s)))
                        (local.set $o (i64.ne (local.get $hi) (i64.const 0))))
                  (else (local.set $hi (call $smulh (local.get $a) (local.get $s)))
                        (local.set $o (i64.ne (local.get $hi) (i64.shr_s (local.get $lo) (i64.const 63)))))))
          (else
            (if (i32.eq (local.get $op) (i32.const 4))
              (then (local.set $lo (i64.mul (local.get $a) (local.get $s))))
              (else (local.set $lo (i64.mul (i64.extend32_s (local.get $a)) (i64.extend32_s (local.get $s))))))
            (local.set $o (if (result i32) (i32.eq (local.get $op) (i32.const 4))
              (then (i64.ne (i64.shr_u (local.get $lo) (i64.const 32)) (i64.const 0)))
              (else (i64.ne (local.get $lo) (i64.extend32_s (local.get $lo))))))
            (local.set $hi (i64.shr_u (local.get $lo) (i64.const 32)))))
        (call $wr (local.get $w) (i32.const 0) (local.get $lo))
        (call $wr (local.get $w) (i32.const 2) (local.get $hi))
        (call $fset6 (local.get $o) (call $u (i32.const 18)) (call $u (i32.const 19))
          (call $u (i32.const 20)) (call $u (i32.const 21)) (local.get $o))
        (return (i32.const 0))))
    (if (i64.eqz (local.get $s)) (then (return (i32.const 3))))
    (if (i32.eq (local.get $w) (i32.const 4))
      (then
        (local.set $lo (i64.or (i64.shl (local.get $d) (i64.const 32)) (local.get $a)))
        (if (i32.eq (local.get $op) (i32.const 6))
          (then (local.set $q (i64.div_u (local.get $lo) (local.get $s)))
                (local.set $r (i64.rem_u (local.get $lo) (local.get $s)))
                (if (i64.gt_u (local.get $q) (i64.const 0xffffffff)) (then (return (i32.const 3)))))
          (else (local.set $s (i64.extend32_s (local.get $s)))
                (if (i32.and (i64.eq (local.get $lo) (i64.const 0x8000000000000000))
                             (i64.eq (local.get $s) (i64.const -1))) (then (return (i32.const 3))))
                (local.set $q (i64.div_s (local.get $lo) (local.get $s)))
                (local.set $r (i64.rem_s (local.get $lo) (local.get $s)))
                (if (i64.ne (local.get $q) (i64.extend32_s (local.get $q))) (then (return (i32.const 3)))))))
      (else
        (if (i32.eq (local.get $op) (i32.const 6))
          (then (if (i64.ge_u (local.get $d) (local.get $s)) (then (return (i32.const 3))))
                (local.set $q (call $udiv128 (local.get $d) (local.get $a) (local.get $s)))
                (local.set $r (global.get $rem)))
          (else
            ;; |dividend|, |divisor|, unsigned divide, fix signs
            (local.set $neg (i64.lt_s (local.get $d) (i64.const 0)))
            (local.set $dn (i64.lt_s (local.get $s) (i64.const 0)))
            (local.set $alo (local.get $a)) (local.set $ahi (local.get $d))
            (if (local.get $neg)
              (then (local.set $alo (i64.sub (i64.const 0) (local.get $a)))
                    (local.set $ahi (i64.add (i64.xor (local.get $d) (i64.const -1))
                                             (i64.extend_i32_u (i64.eqz (local.get $a)))))))
            (local.set $ad (select (i64.sub (i64.const 0) (local.get $s)) (local.get $s) (local.get $dn)))
            (if (i64.ge_u (local.get $ahi) (local.get $ad)) (then (return (i32.const 3))))
            (local.set $q (call $udiv128 (local.get $ahi) (local.get $alo) (local.get $ad)))
            (local.set $r (global.get $rem))
            (if (i32.xor (local.get $neg) (local.get $dn))
              (then (if (i64.gt_u (local.get $q) (i64.const 0x8000000000000000)) (then (return (i32.const 3))))
                    (local.set $q (i64.sub (i64.const 0) (local.get $q))))
              (else (if (i64.ge_u (local.get $q) (i64.const 0x8000000000000000)) (then (return (i32.const 3))))))
            (if (local.get $neg) (then (local.set $r (i64.sub (i64.const 0) (local.get $r)))))))))
    (call $wr (local.get $w) (i32.const 0) (local.get $q))
    (call $wr (local.get $w) (i32.const 2) (local.get $r))
    (call $fset6 (call $u (i32.const 17)) (call $u (i32.const 18)) (call $u (i32.const 19))
      (call $u (i32.const 20)) (call $u (i32.const 21)) (call $u (i32.const 22)))
    (i32.const 0))

  (func $push (param $v i64)
    (local $sp i64)
    (local.set $sp (i64.sub (call $rget (i32.const 4)) (i64.const 8)))
    (call $store64 (local.get $sp) (local.get $v))
    (call $rset (i32.const 4) (local.get $sp)))
  (func $pop (result i64)
    (local $v i64)
    (local.set $v (call $load64 (call $rget (i32.const 4))))
    (call $rset (i32.const 4) (i64.add (call $rget (i32.const 4)) (i64.const 8)))
    (local.get $v))

  ;; syscall at next-rip `next`: rax <- sys(rax, rdi rsi rdx r10 r8 r9); rcx <- next; r11 <- rflags.
  ;; Status 1 (halted) after exit (60) / exit_group (231).
  (func $do_syscall (param $next i64) (result i32)
    (local $nr i64) (local $fl i64)
    (local.set $nr (call $rget (i32.const 0)))
    (local.set $fl (call $eflags))
    (call $rset (i32.const 0)
      (call $syscall (local.get $nr) (call $rget (i32.const 7)) (call $rget (i32.const 6)) (call $rget (i32.const 2))
                     (call $rget (i32.const 10)) (call $rget (i32.const 8)) (call $rget (i32.const 9))))
    (call $rset (i32.const 1) (local.get $next))
    (call $rset (i32.const 11) (local.get $fl))
    (call $rset (i32.const 16) (local.get $next))
    (if (i32.or (i64.eq (local.get $nr) (i64.const 60)) (i64.eq (local.get $nr) (i64.const 231)))
      (then (return (i32.const 1))))
    (i32.const 0))

  ;; ---------------------------------------------------------------- state API
  (func $get (export "get") (param $loc i32) (result i64)
    (if (i32.le_u (local.get $loc) (i32.const 16)) (then (return (call $rget (local.get $loc)))))
    (if (i32.le_u (local.get $loc) (i32.const 23)) (then (return (i64.extend_i32_u (call $fget (local.get $loc))))))
    (i64.const 0))
  (func $set (export "set") (param $loc i32) (param $v i64)
    (if (i32.le_u (local.get $loc) (i32.const 16)) (then (call $rset (local.get $loc) (local.get $v)) (return)))
    (if (i32.le_u (local.get $loc) (i32.const 23))
      (then (call $fset (local.get $loc) (i32.wrap_i64 (i64.and (local.get $v) (i64.const 1)))))))
  (func $modelled (export "modelled") (param $loc i32) (result i32)
    (i32.lt_u (local.get $loc) (i32.const 24)))

  ;; ---------------------------------------------------------------- method API (P-calls)
  ;; Methods do not advance rip, except control transfers; the program calls i_next(len) first
  ;; for call/jmp/jcc/syscall (rip must be the next instruction's address) and after others.
  (func $i_next (export "i_next") (param $len i32)
    (call $rset (i32.const 16) (i64.add (call $rget (i32.const 16)) (i64.extend_i32_u (local.get $len)))))
  ;; effective address; base/index -1 = none, scale = shift 0..3. (rip-relative: pass -1 and absolute disp)
  (func $ea (export "ea") (param $b i32) (param $i i32) (param $s i32) (param $d i64) (result i64)
    (if (i32.ge_s (local.get $b) (i32.const 0))
      (then (local.set $d (i64.add (local.get $d) (call $rget (local.get $b))))))
    (if (i32.ge_s (local.get $i) (i32.const 0))
      (then (local.set $d (i64.add (local.get $d)
              (i64.shl (call $rget (local.get $i)) (i64.extend_i32_u (local.get $s)))))))
    (local.get $d))
  (func $i_mov_rr (export "i_mov_rr") (param $w i32) (param $d i32) (param $s i32)
    (call $wr (local.get $w) (local.get $d) (call $rd (local.get $w) (local.get $s))))
  (func $i_mov_ri (export "i_mov_ri") (param $w i32) (param $d i32) (param $v i64)
    (call $wr (local.get $w) (local.get $d) (local.get $v)))
  (func $i_load (export "i_load") (param $w i32) (param $d i32) (param $a i64)
    (call $wr (local.get $w) (local.get $d) (call $ld (local.get $w) (local.get $a))))
  (func $i_store (export "i_store") (param $w i32) (param $a i64) (param $s i32)
    (call $st (local.get $w) (local.get $a) (call $rd (local.get $w) (local.get $s))))
  (func $i_store_i (export "i_store_i") (param $w i32) (param $a i64) (param $v i64)
    (call $st (local.get $w) (local.get $a) (local.get $v)))
  ;; movzx/movsx: sw = source size, sx = 1 for sign extension
  (func $i_movx_rr (export "i_movx_rr") (param $sx i32) (param $w i32) (param $sw i32) (param $d i32) (param $s i32)
    (local $v i64)
    (local.set $v (call $rd (local.get $sw) (local.get $s)))
    (if (local.get $sx) (then (local.set $v (call $sext (local.get $sw) (local.get $v)))))
    (call $wr (local.get $w) (local.get $d) (local.get $v)))
  (func $i_movx_rm (export "i_movx_rm") (param $sx i32) (param $w i32) (param $sw i32) (param $d i32) (param $a i64)
    (local $v i64)
    (local.set $v (call $ld (local.get $sw) (local.get $a)))
    (if (local.get $sx) (then (local.set $v (call $sext (local.get $sw) (local.get $v)))))
    (call $wr (local.get $w) (local.get $d) (local.get $v)))
  (func $i_lea (export "i_lea") (param $w i32) (param $d i32) (param $a i64)
    (call $wr (local.get $w) (local.get $d) (local.get $a)))
  (func $i_alu_rr (export "i_alu_rr") (param $op i32) (param $w i32) (param $d i32) (param $s i32)
    (local $r i64)
    (local.set $r (call $alu (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $d))
                                                    (call $rd (local.get $w) (local.get $s))))
    (if (i32.lt_u (local.get $op) (i32.const 7)) (then (call $wr (local.get $w) (local.get $d) (local.get $r)))))
  (func $i_alu_ri (export "i_alu_ri") (param $op i32) (param $w i32) (param $d i32) (param $v i64)
    (local $r i64)
    (local.set $r (call $alu (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $d))
                                                    (i64.and (local.get $v) (call $mask (local.get $w)))))
    (if (i32.lt_u (local.get $op) (i32.const 7)) (then (call $wr (local.get $w) (local.get $d) (local.get $r)))))
  (func $i_alu_rm (export "i_alu_rm") (param $op i32) (param $w i32) (param $d i32) (param $a i64)
    (local $r i64)
    (local.set $r (call $alu (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $d))
                                                    (call $ld (local.get $w) (local.get $a))))
    (if (i32.lt_u (local.get $op) (i32.const 7)) (then (call $wr (local.get $w) (local.get $d) (local.get $r)))))
  (func $i_alu_mr (export "i_alu_mr") (param $op i32) (param $w i32) (param $a i64) (param $s i32)
    (local $r i64)
    (local.set $r (call $alu (local.get $op) (local.get $w) (call $ld (local.get $w) (local.get $a))
                                                    (call $rd (local.get $w) (local.get $s))))
    (if (i32.lt_u (local.get $op) (i32.const 7)) (then (call $st (local.get $w) (local.get $a) (local.get $r)))))
  (func $i_alu_mi (export "i_alu_mi") (param $op i32) (param $w i32) (param $a i64) (param $v i64)
    (local $r i64)
    (local.set $r (call $alu (local.get $op) (local.get $w) (call $ld (local.get $w) (local.get $a))
                                                    (i64.and (local.get $v) (call $mask (local.get $w)))))
    (if (i32.lt_u (local.get $op) (i32.const 7)) (then (call $st (local.get $w) (local.get $a) (local.get $r)))))
  (func $i_unary_r (export "i_unary_r") (param $op i32) (param $w i32) (param $d i32)
    (call $wr (local.get $w) (local.get $d) (call $unary (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $d)))))
  (func $i_shift_ri (export "i_shift_ri") (param $op i32) (param $w i32) (param $d i32) (param $n i32)
    (call $wr (local.get $w) (local.get $d) (call $shift (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $d)) (local.get $n))))
  (func $i_shift_rcl (export "i_shift_rcl") (param $op i32) (param $w i32) (param $d i32)
    (call $wr (local.get $w) (local.get $d) (call $shift (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $d))
                                                (i32.wrap_i64 (call $rget (i32.const 1))))))
  (func $i_imul_rr (export "i_imul_rr") (param $w i32) (param $d i32) (param $s i32)
    (call $wr (local.get $w) (local.get $d) (call $imul (local.get $w) (call $rd (local.get $w) (local.get $d)) (call $rd (local.get $w) (local.get $s)))))
  (func $i_imul_rri (export "i_imul_rri") (param $w i32) (param $d i32) (param $s i32) (param $v i64)
    (call $wr (local.get $w) (local.get $d) (call $imul (local.get $w) (call $rd (local.get $w) (local.get $s)) (local.get $v))))
  (func $i_muldiv_r (export "i_muldiv_r") (param $op i32) (param $w i32) (param $s i32) (result i32)
    (call $muldiv (local.get $op) (local.get $w) (call $rd (local.get $w) (local.get $s))))
  ;; 0x98 (cdqe/cwde) and 0x99 (cqo/cdq)
  (func $i_cxx (export "i_cxx") (param $op i32) (param $w i32)
    (if (i32.eq (local.get $op) (i32.const 0x98))
      (then (call $wr (local.get $w) (i32.const 0)
              (call $sext (i32.shr_u (local.get $w) (i32.const 1)) (call $rget (i32.const 0)))))
      (else (call $wr (local.get $w) (i32.const 2)
              (i64.shr_s (call $sext (local.get $w) (call $rget (i32.const 0))) (i64.const 63))))))
  (func $i_push_r (export "i_push_r") (param $r i32) (call $push (call $rget (local.get $r))))
  (func $i_push_i (export "i_push_i") (param $v i64) (call $push (local.get $v)))
  (func $i_pop_r (export "i_pop_r") (param $r i32) (local $v i64) (local.set $v (call $pop)) (call $rset (local.get $r) (local.get $v)))
  (func $i_call (export "i_call") (param $t i64) (call $push (call $rget (i32.const 16))) (call $rset (i32.const 16) (local.get $t)))
  (func $i_ret (export "i_ret") (call $rset (i32.const 16) (call $pop)))
  (func $i_jmp (export "i_jmp") (param $t i64) (call $rset (i32.const 16) (local.get $t)))
  (func $i_cmov_rr (export "i_cmov_rr") (param $cc i32) (param $w i32) (param $d i32) (param $s i32)
    (call $wr (local.get $w) (local.get $d)
      (select (call $rd (local.get $w) (local.get $s)) (call $rd (local.get $w) (local.get $d)) (call $cond (local.get $cc)))))
  (func $i_cmov_rm (export "i_cmov_rm") (param $cc i32) (param $w i32) (param $d i32) (param $a i64)
    (local $v i64)
    (local.set $v (call $ld (local.get $w) (local.get $a)))
    (call $wr (local.get $w) (local.get $d)
      (select (local.get $v) (call $rd (local.get $w) (local.get $d)) (call $cond (local.get $cc)))))
  (func $i_setcc_r (export "i_setcc_r") (param $cc i32) (param $r i32)
    (call $wr (i32.const 1) (local.get $r) (i64.extend_i32_u (call $cond (local.get $cc)))))
  (func $i_setcc_m (export "i_setcc_m") (param $cc i32) (param $a i64)
    (call $st (i32.const 1) (local.get $a) (i64.extend_i32_u (call $cond (local.get $cc)))))
  (func $i_syscall (export "i_syscall") (result i32) (call $do_syscall (call $rget (i32.const 16))))
  (func $i_unary_m (export "i_unary_m") (param $op i32) (param $w i32) (param $a i64)
    (call $st (local.get $w) (local.get $a) (call $unary (local.get $op) (local.get $w) (call $ld (local.get $w) (local.get $a)))))
  (func $i_shift_mi (export "i_shift_mi") (param $op i32) (param $w i32) (param $a i64) (param $n i32)
    (call $st (local.get $w) (local.get $a) (call $shift (local.get $op) (local.get $w) (call $ld (local.get $w) (local.get $a)) (local.get $n))))
  (func $i_shift_mcl (export "i_shift_mcl") (param $op i32) (param $w i32) (param $a i64)
    (call $st (local.get $w) (local.get $a) (call $shift (local.get $op) (local.get $w) (call $ld (local.get $w) (local.get $a))
                                                (i32.wrap_i64 (call $rget (i32.const 1))))))
  (func $i_imul_rm (export "i_imul_rm") (param $w i32) (param $d i32) (param $a i64)
    (local $v i64)
    (local.set $v (call $ld (local.get $w) (local.get $a)))
    (call $wr (local.get $w) (local.get $d) (call $imul (local.get $w) (call $rd (local.get $w) (local.get $d)) (local.get $v))))
  (func $i_imul_rmi (export "i_imul_rmi") (param $w i32) (param $d i32) (param $a i64) (param $v i64)
    (call $wr (local.get $w) (local.get $d) (call $imul (local.get $w) (call $ld (local.get $w) (local.get $a)) (local.get $v))))
  (func $i_muldiv_m (export "i_muldiv_m") (param $op i32) (param $w i32) (param $a i64) (result i32)
    (call $muldiv (local.get $op) (local.get $w) (call $ld (local.get $w) (local.get $a))))
  (func $i_xchg_rr (export "i_xchg_rr") (param $w i32) (param $x i32) (param $y i32)
    (local $v i64)
    (local.set $v (call $rd (local.get $w) (local.get $x)))
    (call $wr (local.get $w) (local.get $x) (call $rd (local.get $w) (local.get $y)))
    (call $wr (local.get $w) (local.get $y) (local.get $v)))
  (func $i_xchg_rm (export "i_xchg_rm") (param $w i32) (param $r i32) (param $a i64)
    (local $v i64)
    (local.set $v (call $ld (local.get $w) (local.get $a)))
    (call $st (local.get $w) (local.get $a) (call $rd (local.get $w) (local.get $r)))
    (call $wr (local.get $w) (local.get $r) (local.get $v)))
  (func $i_bit_rr (export "i_bit_rr") (param $op i32) (param $w i32) (param $d i32) (param $s i32)
    (call $bitop (local.get $op) (local.get $w) (local.get $d) (call $rd (local.get $w) (local.get $s))))
  (func $i_bit_rm (export "i_bit_rm") (param $op i32) (param $w i32) (param $d i32) (param $a i64)
    (call $bitop (local.get $op) (local.get $w) (local.get $d) (call $ld (local.get $w) (local.get $a))))
  (func $i_push_m (export "i_push_m") (param $a i64) (call $push (call $load64 (local.get $a))))
)
