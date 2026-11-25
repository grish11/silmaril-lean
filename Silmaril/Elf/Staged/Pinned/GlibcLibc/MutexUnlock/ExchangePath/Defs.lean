module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs

/-! The branch from the kind load to the exchange in the pinned Ubuntu glibc
unlock symbol, at link-time virtual addresses. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath

open Silmaril.X86 (Byte)

def selectBytes : List Byte :=
  [0x8b, 0x77, 0x10, 0x81, 0xe6, 0x80, 0, 0, 0, 0x75, 0x1b,
    0x80, 0x3d, 0xb4, 0xa4, 0x16, 0, 0, 0x74, 0x12]

def clearBytes : List Byte := [0x31, 0xc0]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath
