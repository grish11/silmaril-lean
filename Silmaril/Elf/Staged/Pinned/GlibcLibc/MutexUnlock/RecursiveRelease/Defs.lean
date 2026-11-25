module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath.Defs
public import Silmaril.X86.Ext.SymExec

/-! A reached depth-one decrement on the private threaded path of the pinned
Ubuntu glibc unlock symbol, at link-time virtual addresses. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease

open Silmaril.X86 (MState)
open Silmaril.X86.Ext (Loaded loadN)

/-- Loaded code spans and the readable and writable mutex fields at the reached cut.
The depth, owner and users dwords are separated from code and the flag byte. -/
structure Entry (initial : MState) (kind users : BitVec 32) : Prop where
  rip : initial.core.rip = 0xa1c06
  depthCode : Loaded initial.memory 0xa1c06 RecursiveDepth.depthCode
  updateCode : Loaded initial.memory 0xa1b6f Bookkeeping.codeBytes
  selectCode : Loaded initial.memory 0xa1b7a ExchangePath.selectBytes
  clearCode : Loaded initial.memory 0xa1ba0 ExchangePath.clearBytes
  exchangeCode : Loaded initial.memory 0xa1ba2 exchangeBytes
  depthOne : loadN initial.memory (initial.core.read .rdi + 4#64) 4 = some 1#64
  usersRead : loadN initial.memory (initial.core.read .rdi + 12#64) 4 = some (users.setWidth 64)
  kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 = some (kind.setWidth 64)
  depthWrite : initial.memory.Permitted .write (initial.core.read .rdi + 4#64).toNat 4
  ownerWrite : initial.memory.Permitted .write (initial.core.read .rdi + 8#64).toNat 4
  usersWrite : initial.memory.Permitted .write (initial.core.read .rdi + 12#64).toNat 4
  noWrap : (initial.core.read .rdi).toNat + 20 ≤ 2 ^ 64
  codeApart : (initial.core.read .rdi).toNat + 16 ≤ 0xa1b6f ∨
    0xa1c10 ≤ (initial.core.read .rdi).toNat + 4
  privateKind : kind &&& 128#32 = 0
  threadRead : loadN initial.memory 0x20c040 1 = some 0#64
  threadApart : (initial.core.read .rdi).toNat + 16 ≤ 0x20c040 ∨
    0x20c041 ≤ (initial.core.read .rdi).toNat + 4

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease
