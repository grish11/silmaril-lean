module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs

/-! Users-count and owner updates in the pinned Ubuntu glibc unlock symbol.
Addresses are link-time virtual addresses. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping

open Silmaril.X86 (Byte)

/-- The subtract at `0xa1b6f` and immediate store at `0xa1b73`. -/
def codeBytes : List Byte :=
  [0x83, 0x6f, 0x0c, 0x01, 0xc7, 0x47, 0x08, 0, 0, 0, 0]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping
