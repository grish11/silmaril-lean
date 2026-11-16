;; loader: an ELF loader and process launcher as a WASI command module.
;;
;;   wasmtime run --dir . --preload mem=mem.wasm --preload sys=sys.wasm --preload nd=stubs.wasm \
;;     ... loader.wasm PROG ARGS...   (see run-wasi.sh for the full --preload list)
;;
;; 1. reads the static (ET_EXEC) x86-64 ELF file PROG through WASI (preopened dir fd 3);
;; 2. maps every PT_LOAD with `mem.map`, copies p_filesz bytes, leaves the rest zero;
;;    the program break starts at the page-aligned end of the highest segment (`sys.set_brk`);
;; 3. if there is a PT_DYNAMIC: eager binding (BIND_NOW) of GLOB_DAT / JUMP_SLOT / 64 / RELATIVE
;;    relocations. Undefined symbols resolve to *foreign* addresses EXT_BASE + 16*i for the
;;    i-th name of the foreign library table below (`puts`, `strlen`, `putchar`), weak
;;    undefined ones to 0; the simulator (or extrun) gets `set_ext(EXT_BASE, EXT_BASE + 4096)`.
;; 4. builds the initial stack in the LPS layout (`Silmaril.Process.LPS.buildStackBytes`):
;;    argc, argv, NULL, (empty envp) NULL, auxv (AT_PHDR, AT_PHENT, AT_PHNUM, AT_HWCAP=0,
;;    AT_PAGESZ=4096, AT_UID=0, AT_EUID=0, AT_SECURE=0, AT_RANDOM, AT_NULL), strings, pad,
;;    16 AT_RANDOM bytes (fixed draw 1..16); rsp 16-byte aligned, other GPRs 0, rip = e_entry;
;; 5. runs the simulator. A process ends through
;;    `exit`/`exit_group` inside `sys` (WASI proc_exit). If the simulator stops otherwise, the
;;    loader prints the status and rip on stderr and exits with 100 + status.
(module
  (import "wasi_snapshot_preview1" "args_sizes_get" (func $args_sizes_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "args_get" (func $args_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_open"
    (func $path_open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_read" (func $fd_read (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (import "mem" "map" (func $map (param i64 i64) (result i32)))
  (import "mem" "load8" (func $ld8 (param i64) (result i64)))
  (import "mem" "load32" (func $ld32 (param i64) (result i64)))
  (import "mem" "load64" (func $ld64 (param i64) (result i64)))
  (import "mem" "store8" (func $st8 (param i64 i64)))
  (import "mem" "store64" (func $st64 (param i64 i64)))
  (import "sys" "set_brk" (func $set_brk (param i64)))
  (import "sim" "get" (func $sim_get (param i32) (result i64)))
  (import "sim" "set" (func $sim_set (param i32 i64)))
  (import "sim" "set_ext" (func $sim_set_ext (param i64 i64)))
  (import "sim" "run" (func $sim_run (param i64) (result i32)))

  (import "io" "memory" (memory 33))
  (export "memory" (memory 0))
  ;; memory = io.memory: 0..63 scratch, 64..1023 argv pointers, 1024..16383 argv strings,
  ;; 16384.. constants, 0x200000.. the ELF file
  (data (i32.const 16384) "puts\00strlen\00putchar\00\00")
  (data (i32.const 16448) "wsim-loader: stop status=0x")
  (data (i32.const 16480) " rip=0x")
  (data (i32.const 16496) "wsim-loader: error ")

  (global $EXT_BASE i64 (i64.const 0x7f0000000000))
  (global $STACK_TOP i64 (i64.const 0x7ffffffff000))
  (global $FILE i32 (i32.const 0x200000))

  (func $out (param $fd i32) (param $p i32) (param $n i32)
    (i32.store (i32.const 16) (local.get $p)) (i32.store (i32.const 20) (local.get $n))
    (drop (call $fd_write (local.get $fd) (i32.const 16) (i32.const 1) (i32.const 24))))
  (func $hex (param $v i64)
    (local $i i32) (local $d i32)
    (local.set $i (i32.const 0))
    (loop $l
      (local.set $d (i32.wrap_i64 (i64.and (i64.shr_u (local.get $v) (i64.extend_i32_u (i32.sub (i32.const 60) (i32.shl (local.get $i) (i32.const 2))))) (i64.const 15))))
      (i32.store8 offset=32 (local.get $i) (i32.add (local.get $d) (select (i32.const 48) (i32.const 87) (i32.lt_u (local.get $d) (i32.const 10)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 16))))
    (call $out (i32.const 2) (i32.const 32) (i32.const 16)))
  (func $die (param $code i32)
    (call $out (i32.const 2) (i32.const 16496) (i32.const 19))
    (call $hex (i64.extend_i32_u (local.get $code)))
    (i32.store8 (i32.const 48) (i32.const 10)) (call $out (i32.const 2) (i32.const 48) (i32.const 1))
    (call $proc_exit (local.get $code)) (unreachable))

  (func $f16 (param $o i64) (result i64) (i64.load16_u (i32.add (global.get $FILE) (i32.wrap_i64 (local.get $o)))))
  (func $f32 (param $o i64) (result i64) (i64.load32_u (i32.add (global.get $FILE) (i32.wrap_i64 (local.get $o)))))
  (func $f64 (param $o i64) (result i64) (i64.load (i32.add (global.get $FILE) (i32.wrap_i64 (local.get $o)))))

  (func $strlen (param $p i32) (result i32)
    (local $n i32)
    (block $o (loop $l (br_if $o (i32.eqz (i32.load8_u (i32.add (local.get $p) (local.get $n)))))
      (local.set $n (i32.add (local.get $n) (i32.const 1))) (br $l)))
    (local.get $n))

  ;; read the whole file into memory at $FILE; returns its size
  (func $read_file (param $path i32) (result i32)
    (local $size i32)
    (if (call $path_open (i32.const 3) (i32.const 1) (local.get $path) (call $strlen (local.get $path))
                         (i32.const 0) (i64.const 2) (i64.const 0) (i32.const 0) (i32.const 8))
      (then (call $die (i32.const 121))))
    (loop $l
      (if (i32.gt_u (i32.add (i32.add (global.get $FILE) (local.get $size)) (i32.const 65536)) (i32.shl (memory.size) (i32.const 16)))
        (then (drop (memory.grow (i32.const 1)))))
      (i32.store (i32.const 16) (i32.add (global.get $FILE) (local.get $size)))
      (i32.store (i32.const 20) (i32.const 65536))
      (if (call $fd_read (i32.load (i32.const 8)) (i32.const 16) (i32.const 1) (i32.const 12))
        (then (call $die (i32.const 121))))
      (local.set $size (i32.add (local.get $size) (i32.load (i32.const 12))))
      (br_if $l (i32.load (i32.const 12))))
    (local.get $size))

  ;; foreign symbol lookup by name (guest address of a NUL-terminated string); -1 if absent
  (func $foreign (param $name i64) (result i64)
    (local $p i32) (local $i i64) (local $k i32)
    (local.set $p (i32.const 16384))
    (block $notfound (loop $next
      (br_if $notfound (i32.eqz (i32.load8_u (local.get $p))))
      (local.set $k (i32.const 0))
      (block $mismatch (loop $cmp
        (br_if $mismatch (i64.ne (call $ld8 (i64.add (local.get $name) (i64.extend_i32_u (local.get $k))))
                                 (i64.load8_u (i32.add (local.get $p) (local.get $k)))))
        (if (i32.eqz (i32.load8_u (i32.add (local.get $p) (local.get $k))))
          (then (return (i64.add (global.get $EXT_BASE) (i64.shl (local.get $i) (i64.const 4))))))
        (local.set $k (i32.add (local.get $k) (i32.const 1)))
        (br $cmp)))
      (local.set $p (i32.add (i32.add (local.get $p) (call $strlen (local.get $p))) (i32.const 1)))
      (local.set $i (i64.add (local.get $i) (i64.const 1)))
      (br $next)))
    (i64.const -1))

  ;; apply `$n` bytes of Elf64_Rela at guest address $rela
  (func $relocate (param $rela i64) (param $sz i64) (param $symtab i64) (param $strtab i64)
    (local $end i64) (local $off i64) (local $info i64) (local $add i64) (local $ty i64)
    (local $sym i64) (local $v i64)
    (local.set $end (i64.add (local.get $rela) (local.get $sz)))
    (block $o (loop $l
      (br_if $o (i64.ge_u (local.get $rela) (local.get $end)))
      (local.set $off (call $ld64 (local.get $rela)))
      (local.set $info (call $ld64 (i64.add (local.get $rela) (i64.const 8))))
      (local.set $add (call $ld64 (i64.add (local.get $rela) (i64.const 16))))
      (local.set $ty (i64.and (local.get $info) (i64.const 0xffffffff)))
      (local.set $sym (i64.add (local.get $symtab) (i64.mul (i64.shr_u (local.get $info) (i64.const 32)) (i64.const 24))))
      (if (i64.eq (local.get $ty) (i64.const 8))       ;; R_X86_64_RELATIVE (base 0 for ET_EXEC)
        (then (local.set $v (local.get $add)))
      (else
        (if (i32.or (i32.or (i64.eq (local.get $ty) (i64.const 6)) (i64.eq (local.get $ty) (i64.const 7)))
                    (i64.eq (local.get $ty) (i64.const 1)))
          (then
            (if (i64.ne (i64.and (call $ld64 (i64.add (local.get $sym) (i64.const 4))) (i64.const 0xffff0000)) (i64.const 0))
              (then (local.set $v (call $ld64 (i64.add (local.get $sym) (i64.const 8)))))  ;; defined here
              (else
                (local.set $v (call $foreign (i64.add (local.get $strtab) (call $ld32 (local.get $sym)))))
                (if (i64.eq (local.get $v) (i64.const -1))
                  (then
                    (if (i64.eq (i64.shr_u (call $ld8 (i64.add (local.get $sym) (i64.const 4))) (i64.const 4)) (i64.const 2))
                      (then (local.set $v (i64.const 0)))               ;; weak undefined
                      (else (call $die (i32.const 123))))))))
            (if (i64.eq (local.get $ty) (i64.const 1)) (then (local.set $v (i64.add (local.get $v) (local.get $add))))))
          (else (call $die (i32.const 124))))))
      (call $st64 (local.get $off) (local.get $v))
      (local.set $rela (i64.add (local.get $rela) (i64.const 24)))
      (br $l))))

  (func $dynamic (param $dyn i64)
    (local $tag i64) (local $val i64) (local $strtab i64) (local $symtab i64)
    (local $rela i64) (local $relasz i64) (local $jmprel i64) (local $pltsz i64)
    (block $o (loop $l
      (local.set $tag (call $ld64 (local.get $dyn)))
      (local.set $val (call $ld64 (i64.add (local.get $dyn) (i64.const 8))))
      (br_if $o (i64.eqz (local.get $tag)))
      (if (i64.eq (local.get $tag) (i64.const 5)) (then (local.set $strtab (local.get $val))))
      (if (i64.eq (local.get $tag) (i64.const 6)) (then (local.set $symtab (local.get $val))))
      (if (i64.eq (local.get $tag) (i64.const 7)) (then (local.set $rela (local.get $val))))
      (if (i64.eq (local.get $tag) (i64.const 8)) (then (local.set $relasz (local.get $val))))
      (if (i64.eq (local.get $tag) (i64.const 23)) (then (local.set $jmprel (local.get $val))))
      (if (i64.eq (local.get $tag) (i64.const 2)) (then (local.set $pltsz (local.get $val))))
      (local.set $dyn (i64.add (local.get $dyn) (i64.const 16)))
      (br $l)))
    (call $relocate (local.get $rela) (local.get $relasz) (local.get $symtab) (local.get $strtab))
    (call $relocate (local.get $jmprel) (local.get $pltsz) (local.get $symtab) (local.get $strtab))
    (call $sim_set_ext (global.get $EXT_BASE) (i64.add (global.get $EXT_BASE) (i64.const 4096))))

  (func (export "_start")
    (local $argc i32) (local $size i32) (local $phoff i64) (local $phnum i64) (local $ph i64)
    (local $i i64) (local $ty i64) (local $va i64) (local $off i64) (local $fsz i64) (local $msz i64)
    (local $j i64) (local $end i64) (local $phdr i64) (local $dyn i64)
    (local $n i32) (local $k i32) (local $strs i32) (local $struct i32) (local $raw i32) (local $total i32)
    (local $sp i64) (local $sb i64) (local $a i64) (local $p i32) (local $len i32) (local $s i32)
    ;; arguments
    (drop (call $args_sizes_get (i32.const 0) (i32.const 4)))
    (local.set $argc (i32.load (i32.const 0)))
    (if (i32.or (i32.lt_u (local.get $argc) (i32.const 2))
                (i32.or (i32.gt_u (local.get $argc) (i32.const 200)) (i32.gt_u (i32.load (i32.const 4)) (i32.const 15000))))
      (then (call $die (i32.const 120))))
    (drop (call $args_get (i32.const 64) (i32.const 1024)))
    ;; ELF
    (local.set $size (call $read_file (i32.load (i32.const 68))))
    (if (i32.or (i32.lt_u (local.get $size) (i32.const 64))
          (i32.or (i32.ne (i32.load (global.get $FILE)) (i32.const 0x464c457f))
            (i32.or (i64.ne (call $f16 (i64.const 18)) (i64.const 62)) (i64.ne (call $f16 (i64.const 16)) (i64.const 2)))))
      (then (call $die (i32.const 122))))
    (local.set $phoff (call $f64 (i64.const 32)))
    (local.set $phnum (call $f16 (i64.const 56)))
    (local.set $phdr (i64.const 0))
    (loop $segs (if (i64.lt_u (local.get $i) (local.get $phnum)) (then
      (local.set $ph (i64.add (local.get $phoff) (i64.mul (local.get $i) (i64.const 56))))
      (local.set $ty (call $f32 (local.get $ph)))
      (local.set $off (call $f64 (i64.add (local.get $ph) (i64.const 8))))
      (local.set $va (call $f64 (i64.add (local.get $ph) (i64.const 16))))
      (local.set $fsz (call $f64 (i64.add (local.get $ph) (i64.const 32))))
      (local.set $msz (call $f64 (i64.add (local.get $ph) (i64.const 40))))
      (if (i64.eq (local.get $ty) (i64.const 6)) (then (local.set $phdr (local.get $va))))
      (if (i64.eq (local.get $ty) (i64.const 2)) (then (local.set $dyn (local.get $va))))
      (if (i64.eq (local.get $ty) (i64.const 1)) (then
        (drop (call $map (local.get $va) (local.get $msz)))
        (local.set $j (i64.const 0))
        (block $o (loop $cp
          (br_if $o (i64.ge_u (local.get $j) (local.get $fsz)))
          (call $st8 (i64.add (local.get $va) (local.get $j))
                     (i64.load8_u (i32.add (global.get $FILE) (i32.wrap_i64 (i64.add (local.get $off) (local.get $j))))))
          (local.set $j (i64.add (local.get $j) (i64.const 1)))
          (br $cp)))
        (if (i32.and (i64.eqz (local.get $phdr)) (i32.and (i64.le_u (local.get $off) (local.get $phoff))
               (i64.lt_u (local.get $phoff) (i64.add (local.get $off) (local.get $fsz)))))
          (then (local.set $phdr (i64.add (local.get $va) (i64.sub (local.get $phoff) (local.get $off))))))
        (if (i64.gt_u (i64.add (local.get $va) (local.get $msz)) (local.get $end))
          (then (local.set $end (i64.add (local.get $va) (local.get $msz)))))))
      (local.set $i (i64.add (local.get $i) (i64.const 1)))
      (br $segs))))
    (call $set_brk (i64.and (i64.add (local.get $end) (i64.const 4095)) (i64.const -4096)))
    (if (i64.ne (local.get $dyn) (i64.const 0)) (then (call $dynamic (local.get $dyn))))
    ;; initial stack (LPS layout)
    (drop (call $map (i64.sub (global.get $STACK_TOP) (i64.const 0x100000)) (i64.const 0x100000)))
    (local.set $n (i32.sub (local.get $argc) (i32.const 1)))
    (local.set $k (i32.const 0))
    (loop $sl (if (i32.lt_u (local.get $k) (local.get $n)) (then
      (local.set $strs (i32.add (local.get $strs)
        (i32.add (call $strlen (i32.load (i32.add (i32.const 68) (i32.shl (local.get $k) (i32.const 2))))) (i32.const 1))))
      (local.set $k (i32.add (local.get $k) (i32.const 1))) (br $sl))))
    (local.set $struct (i32.add (i32.add (i32.const 8) (i32.shl (i32.add (local.get $n) (i32.const 1)) (i32.const 3))) (i32.const 168)))
    (local.set $raw (i32.add (local.get $struct) (local.get $strs)))
    (local.set $total (i32.add (i32.and (i32.add (local.get $raw) (i32.const 7)) (i32.const -8)) (i32.const 16)))
    (local.set $sp (i64.and (i64.sub (i64.sub (global.get $STACK_TOP) (i64.const 4096)) (i64.extend_i32_u (local.get $total))) (i64.const -16)))
    (call $st64 (local.get $sp) (i64.extend_i32_u (local.get $n)))
    (local.set $sb (i64.add (local.get $sp) (i64.extend_i32_u (local.get $struct))))
    (local.set $a (local.get $sb))
    (local.set $k (i32.const 0))
    (loop $al (if (i32.lt_u (local.get $k) (local.get $n)) (then
      (call $st64 (i64.add (local.get $sp) (i64.extend_i32_u (i32.add (i32.const 8) (i32.shl (local.get $k) (i32.const 3))))) (local.get $a))
      (local.set $p (i32.load (i32.add (i32.const 68) (i32.shl (local.get $k) (i32.const 2)))))
      (local.set $len (i32.add (call $strlen (local.get $p)) (i32.const 1)))
      (local.set $s (i32.const 0))
      (loop $cs
        (call $st8 (i64.add (local.get $a) (i64.extend_i32_u (local.get $s))) (i64.load8_u (i32.add (local.get $p) (local.get $s))))
        (local.set $s (i32.add (local.get $s) (i32.const 1)))
        (br_if $cs (i32.lt_u (local.get $s) (local.get $len))))
      (local.set $a (i64.add (local.get $a) (i64.extend_i32_u (local.get $len))))
      (local.set $k (i32.add (local.get $k) (i32.const 1))) (br $al))))
    ;; argv NULL, envp NULL
    (local.set $a (i64.add (local.get $sp) (i64.extend_i32_u (i32.add (i32.const 8) (i32.shl (local.get $n) (i32.const 3))))))
    (call $st64 (local.get $a) (i64.const 0))
    (call $st64 (i64.add (local.get $a) (i64.const 8)) (i64.const 0))
    (local.set $a (i64.add (local.get $a) (i64.const 16)))
    ;; auxv
    (call $st64 (local.get $a) (i64.const 3))   (call $st64 (i64.add (local.get $a) (i64.const 8)) (local.get $phdr))
    (call $st64 (i64.add (local.get $a) (i64.const 16)) (i64.const 4))  (call $st64 (i64.add (local.get $a) (i64.const 24)) (i64.const 56))
    (call $st64 (i64.add (local.get $a) (i64.const 32)) (i64.const 5))  (call $st64 (i64.add (local.get $a) (i64.const 40)) (local.get $phnum))
    (call $st64 (i64.add (local.get $a) (i64.const 48)) (i64.const 16)) (call $st64 (i64.add (local.get $a) (i64.const 56)) (i64.const 0))
    (call $st64 (i64.add (local.get $a) (i64.const 64)) (i64.const 6))  (call $st64 (i64.add (local.get $a) (i64.const 72)) (i64.const 4096))
    (call $st64 (i64.add (local.get $a) (i64.const 80)) (i64.const 11)) (call $st64 (i64.add (local.get $a) (i64.const 88)) (i64.const 0))
    (call $st64 (i64.add (local.get $a) (i64.const 96)) (i64.const 12)) (call $st64 (i64.add (local.get $a) (i64.const 104)) (i64.const 0))
    (call $st64 (i64.add (local.get $a) (i64.const 112)) (i64.const 23)) (call $st64 (i64.add (local.get $a) (i64.const 120)) (i64.const 0))
    (call $st64 (i64.add (local.get $a) (i64.const 128)) (i64.const 25))
    (call $st64 (i64.add (local.get $a) (i64.const 136)) (i64.add (local.get $sp) (i64.extend_i32_u (i32.sub (local.get $total) (i32.const 16)))))
    (call $st64 (i64.add (local.get $a) (i64.const 144)) (i64.const 0)) (call $st64 (i64.add (local.get $a) (i64.const 152)) (i64.const 0))
    ;; AT_RANDOM bytes: fixed draw 1..16
    (local.set $a (i64.add (local.get $sp) (i64.extend_i32_u (i32.sub (local.get $total) (i32.const 16)))))
    (call $st64 (local.get $a) (i64.const 0x0807060504030201))
    (call $st64 (i64.add (local.get $a) (i64.const 8)) (i64.const 0x100f0e0d0c0b0a09))
    ;; registers
    (local.set $k (i32.const 0))
    (loop $rz (call $sim_set (local.get $k) (i64.const 0))
      (local.set $k (i32.add (local.get $k) (i32.const 1)))
      (br_if $rz (i32.lt_u (local.get $k) (i32.const 24))))
    (call $sim_set (i32.const 4) (local.get $sp))
    (call $sim_set (i32.const 16) (call $f64 (i64.const 24)))
    ;; run
    (local.set $k (call $sim_run (i64.const 0x7fffffffffffffff)))
    (call $out (i32.const 2) (i32.const 16448) (i32.const 27))
    (call $hex (i64.extend_i32_u (local.get $k)))
    (call $out (i32.const 2) (i32.const 16480) (i32.const 7))
    (call $hex (call $sim_get (i32.const 16)))
    (i32.store8 (i32.const 48) (i32.const 10)) (call $out (i32.const 2) (i32.const 48) (i32.const 1))
    (call $proc_exit (i32.add (i32.const 100) (local.get $k))))
)
