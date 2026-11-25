module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Atomic9.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Machine.Execution

/-- Both byte sequences are inside the pinned versioned unlock symbol. -/
theorem code :
    CodeAt F 0xa1b7a selectBytes ∧ CodeAt F 0xa1ba0 clearBytes ∧
      MutexUnlock.entry.value ≤ 0xa1b7a ∧
      0xa1ba0 + clearBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath.code

/-- With bit 0x80 set in the loaded kind dword, the branch goes directly to
the EAX clear and the next RIP is the exchange. This route makes no flag-byte
read. The four-step cut preserves RDI and memory. -/
theorem shared_exchange {initial : MState} {kind : BitVec 32}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (clearLoaded : Loaded initial.memory 0xa1ba0 clearBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (shared : kind &&& 128#32 ≠ 0) :
    ∃ final, run Atomic9.step 4 initial = some final ∧ final.core.rip = 0xa1ba2 ∧
      final.core.read .rax = 0#64 ∧ final.core.read .rdi = initial.core.read .rdi ∧
      final.memory = initial.memory :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath.shared_exchange
    rip loaded clearLoaded kindRead shared

/-- With bit 0x80 clear and a readable zero byte at the RIP-relative flag
address, the six-step cut ends just before the exchange with full RAX zero.
It preserves RDI and memory. -/
theorem private_threaded_exchange {initial : MState} {kind : BitVec 32}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (clearLoaded : Loaded initial.memory 0xa1ba0 clearBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (privateKind : kind &&& 128#32 = 0)
    (threadRead : loadN initial.memory 0x20c040 1 = some 0#64) :
    ∃ final, run Atomic9.step 6 initial = some final ∧ final.core.rip = 0xa1ba2 ∧
      final.core.read .rax = 0#64 ∧ final.core.read .rdi = initial.core.read .rdi ∧
      final.memory = initial.memory :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath.private_threaded_exchange
    rip loaded clearLoaded kindRead privateKind threadRead

/-- When the kind bit is clear and the same byte is nonzero, the five-step
cut ends at the alternate instruction at 0xa1b8e. Memory is unchanged. -/
theorem private_single_thread_fallthrough {initial : MState} {kind : BitVec 32} {value : Byte}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (privateKind : kind &&& 128#32 = 0)
    (threadRead : loadN initial.memory 0x20c040 1 = some (value.setWidth 64))
    (singleThread : value ≠ 0) :
    ∃ final, run Atomic9.step 5 initial = some final ∧ final.core.rip = 0xa1b8e ∧
      final.memory = initial.memory :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath.private_single_thread_fallthrough
    rip loaded kindRead privateKind threadRead singleThread

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath
