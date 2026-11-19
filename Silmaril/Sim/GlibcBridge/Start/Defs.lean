module

public import Silmaril.Sim.GlibcBridge.Bytes.Defs
public import Silmaril.Sim.GlibcBridge.Elf.Defs

/-!
# The start-up contract (header)

What the bridge's start-up provides at `main`'s entry, as one hypothesis `StartAtMain`.

**Ours** (`glibcrun.wat`'s `START`, after crt1's `_start` ran in the simulator: `endbr64; xor
%ebp,%ebp; mov %rdx,%r9; pop %rsi; mov %rsp,%rdx; and $-16,%rsp; push %rax; push %rsp; xor
%r8d,%r8d; xor %ecx,%ecx; mov $main,%rdi; call *GOT[__libc_start_main]`): at the foreign address
`__libc_start_main = EXT_BASE + 0x30` it sets `rip := rdi` (`main`), `rdi := argc`, `rsi := argv`,
`rdx := argv + 8 (argc + 1)`, and overwrites the return address slot `[rsp]` with `mainRet`;
`main`'s return to `mainRet` is `exit(rax)` (import 1, `exitC`). Nothing else.

**Real `__libc_start_main`** (glibc 2.39, `csu/libc-start.c`) additionally: `__libc_init_secure`,
TLS and the thread pointer (`__libc_setup_tls`, `arch_prctl`), stack protector and pointer guard
from `AT_RANDOM`, `_dl_relocate_static_pie`/IRELATIVE and `cpu_features` (in ld.so for a dynamic
executable), `__libc_init_first` (`__environ`, `__libc_argv`), `_dl_non_dynamic_init`, stdio and
locale defaults, `__cxa_atexit (rtld_fini)`, `init`/`DT_INIT_ARRAY` (`call_init`), `_setjmp` for
thread cancellation, and `exit (main (...))`, whose `exit` runs `atexit`/`DT_FINI_ARRAY` handlers
and flushes stdio (`_IO_cleanup`) before `_exit`. For the hello, `main` reads none of it (no
argument, no TLS, no locale), and `puts`'s output reaches WASI in the call itself, so only the
`exit(main())` part is observable.

**`StartAtMain s f mem W σ`**: the store encodes a core at `main` (`rip = 0x401050`) whose stack
holds `mainRet` at `rsp`, in GM's writable window with room for `main`'s frame (`rsp - 16`, no wrap).
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm.Execution.Core
open Silmaril.X86 (State Word)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G
open Silmaril.Sim.X86.GM

/-- **The start-up contract at `main`'s entry.** -/
structure StartAtMain {H : Type} (s : Store H) (f : Frame) (mem : Memory) (W : Win) (σ : State) :
    Prop where
  enc : Enc s f σ
  memEnc : MemEnc s f mem W
  /-- The window is writable (the stack). -/
  rw : W.rw = true
  rip : σ.rip = 0x401050#64
  ret : Silmaril.X86.Ext.loadN mem (σ.read .rsp) 8 = some mainRet
  win0 : W.Holds (σ.read .rsp)
  win16 : W.Holds (σ.read .rsp - 16#64)
  low : 16 ≤ (σ.read .rsp).toNat

end Silmaril.Sim.GlibcBridge
