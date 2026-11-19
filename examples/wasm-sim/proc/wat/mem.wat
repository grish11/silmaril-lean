;; mem: the process memory model as a Wasm module (provides the simulator ABI's `mem.*` imports).
;;
;; A sparse 64-bit address space of 4 KiB pages. Page table: open-addressing hash table of
;; 4096 slots at [0, 64 KiB) (slot = 16 bytes: u64 vpage+1 (0 = empty), u32 frame offset).
;; Frames are allocated from 64 KiB upwards; the linear memory grows on demand.
;; Access to an unmapped page traps (`unreachable`) = fault. Permissions are not modelled.
;;
;; Exports: load8/16/32/64 (addr i64) -> i64 (zero-extended), store8/16/32/64 (addr, v),
;;          map (addr i64, len i64) -> i32 (pages newly mapped; zero-filled),
;;          mapped (addr i64) -> i32.
(module
  (memory (export "phys") 2)
  (global $next (mut i32) (i32.const 65536))   ;; next free frame
  (global $cpage (mut i64) (i64.const -1))     ;; one-entry TLB
  (global $cframe (mut i32) (i32.const 0))

  (func $slot (param $vp i64) (result i32)      ;; slot holding $vp, or the empty slot for it
    (local $h i32) (local $k i64)
    (local.set $h (i32.wrap_i64 (i64.shr_u (i64.mul (local.get $vp) (i64.const 0x9E3779B97F4A7C15)) (i64.const 52))))
    (loop $probe
      (local.set $k (i64.load (i32.shl (local.get $h) (i32.const 4))))
      (if (i32.or (i64.eqz (local.get $k)) (i64.eq (local.get $k) (i64.add (local.get $vp) (i64.const 1))))
        (then (return (i32.shl (local.get $h) (i32.const 4)))))
      (local.set $h (i32.and (i32.add (local.get $h) (i32.const 1)) (i32.const 4095)))
      (br $probe))
    (unreachable))

  (func $frame (param $vp i64) (result i32)     ;; frame offset, or -1
    (local $s i32)
    (local.set $s (call $slot (local.get $vp)))
    (if (result i32) (i64.eqz (i64.load (local.get $s)))
      (then (i32.const -1))
      (else (i32.load offset=8 (local.get $s)))))

  (func $tr (param $a i64) (result i32)
    (local $vp i64) (local $f i32)
    (local.set $vp (i64.shr_u (local.get $a) (i64.const 12)))
    (if (i64.ne (local.get $vp) (global.get $cpage))
      (then
        (local.set $f (call $frame (local.get $vp)))
        (if (i32.eq (local.get $f) (i32.const -1)) (then (unreachable)))
        (global.set $cpage (local.get $vp))
        (global.set $cframe (local.get $f))))
    (i32.add (global.get $cframe) (i32.wrap_i64 (i64.and (local.get $a) (i64.const 0xfff)))))

  (func $mapped (export "mapped") (param $a i64) (result i32)
    (i32.ne (call $frame (i64.shr_u (local.get $a) (i64.const 12))) (i32.const -1)))

  (func (export "map") (param $a i64) (param $len i64) (result i32)
    (local $vp i64) (local $end i64) (local $s i32) (local $n i32)
    (local.set $vp (i64.shr_u (local.get $a) (i64.const 12)))
    (local.set $end (i64.shr_u (i64.add (i64.add (local.get $a) (local.get $len)) (i64.const 4095)) (i64.const 12)))
    (block $out (loop $l
      (br_if $out (i64.ge_u (local.get $vp) (local.get $end)))
      (local.set $s (call $slot (local.get $vp)))
      (if (i64.eqz (i64.load (local.get $s)))
        (then
          (if (i32.ge_u (i32.add (global.get $next) (i32.const 4096)) (i32.shl (memory.size) (i32.const 16)))
            (then (if (i32.eq (memory.grow (i32.const 16)) (i32.const -1)) (then (unreachable)))))
          (i64.store (local.get $s) (i64.add (local.get $vp) (i64.const 1)))
          (i32.store offset=8 (local.get $s) (global.get $next))
          (global.set $next (i32.add (global.get $next) (i32.const 4096)))
          (local.set $n (i32.add (local.get $n) (i32.const 1)))))
      (local.set $vp (i64.add (local.get $vp) (i64.const 1)))
      (br $l)))
    (local.get $n))

  ;; byte-wise slow path for accesses crossing a page boundary
  (func $ldn (param $a i64) (param $n i32) (result i64)
    (local $v i64) (local $i i32)
    (loop $l
      (local.set $v (i64.or (local.get $v)
        (i64.shl (i64.load8_u (call $tr (i64.add (local.get $a) (i64.extend_i32_u (local.get $i)))))
                 (i64.extend_i32_u (i32.shl (local.get $i) (i32.const 3))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (local.get $n))))
    (local.get $v))
  (func $stn (param $a i64) (param $v i64) (param $n i32)
    (local $i i32)
    (loop $l
      (i64.store8 (call $tr (i64.add (local.get $a) (i64.extend_i32_u (local.get $i))))
        (i64.shr_u (local.get $v) (i64.extend_i32_u (i32.shl (local.get $i) (i32.const 3)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (local.get $n)))))
  (func $cross (param $a i64) (param $n i32) (result i32)
    (i64.gt_u (i64.and (local.get $a) (i64.const 0xfff)) (i64.extend_i32_u (i32.sub (i32.const 4096) (local.get $n)))))

  (func (export "load8") (param $a i64) (result i64) (i64.load8_u (call $tr (local.get $a))))
  (func (export "load16") (param $a i64) (result i64)
    (if (result i64) (call $cross (local.get $a) (i32.const 2)) (then (call $ldn (local.get $a) (i32.const 2)))
      (else (i64.load16_u (call $tr (local.get $a))))))
  (func (export "load32") (param $a i64) (result i64)
    (if (result i64) (call $cross (local.get $a) (i32.const 4)) (then (call $ldn (local.get $a) (i32.const 4)))
      (else (i64.load32_u (call $tr (local.get $a))))))
  (func (export "load64") (param $a i64) (result i64)
    (if (result i64) (call $cross (local.get $a) (i32.const 8)) (then (call $ldn (local.get $a) (i32.const 8)))
      (else (i64.load (call $tr (local.get $a))))))
  (func (export "store8") (param $a i64) (param $v i64) (i64.store8 (call $tr (local.get $a)) (local.get $v)))
  (func (export "store16") (param $a i64) (param $v i64)
    (if (call $cross (local.get $a) (i32.const 2)) (then (call $stn (local.get $a) (local.get $v) (i32.const 2)))
      (else (i64.store16 (call $tr (local.get $a)) (local.get $v)))))
  (func (export "store32") (param $a i64) (param $v i64)
    (if (call $cross (local.get $a) (i32.const 4)) (then (call $stn (local.get $a) (local.get $v) (i32.const 4)))
      (else (i64.store32 (call $tr (local.get $a)) (local.get $v)))))
  (func (export "store64") (param $a i64) (param $v i64)
    (if (call $cross (local.get $a) (i32.const 8)) (then (call $stn (local.get $a) (local.get $v) (i32.const 8)))
      (else (i64.store (call $tr (local.get $a)) (local.get $v)))))
)
