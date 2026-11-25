module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs

/-! The recursive unlock's depth decrement and zero-flag branch in the pinned
Ubuntu glibc file, at link-time virtual addresses. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth

open Silmaril.X86 (Byte)

/-- `sub dword ptr [rdi+4], 1` followed by `je 0xa1b6f`, starting at `0xa1c06`. -/
def depthCode : List Byte :=
  [0x83, 0x6f, 0x04, 0x01, 0x0f, 0x84, 0x5f, 0xff, 0xff, 0xff]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth
