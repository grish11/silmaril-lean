module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Atomic9.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockBookkeeping

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN storeN subFlagsN)

/-- The two instructions are inside the separately verified versioned unlock symbol. -/
theorem code : CodeAt F 0xa1b6f codeBytes ∧ MutexUnlock.entry.value ≤ 0xa1b6f ∧
    0xa1b6f + codeBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockBookkeeping.code

/-- The two steps decrement the users dword and clear the owner dword in order.
The write footprint is confined to these adjacent dwords. GPRs are preserved,
and the owner store retains the flags from the decrement. The theorem starts
at the reached users-count update and stops before the next instruction. -/
theorem steps {initial : MState} {users : BitVec 32}
    (rip : initial.core.rip = 0xa1b6f)
    (loaded : Loaded initial.memory 0xa1b6f#64 codeBytes)
    (read : loadN initial.memory (initial.core.read .rdi + 12#64) 4 = some (users.setWidth 64))
    (usersWritable : initial.memory.Permitted .write (initial.core.read .rdi + 12#64).toNat 4)
    (ownerWritable : initial.memory.Permitted .write (initial.core.read .rdi + 8#64).toNat 4)
    (noWrap : (initial.core.read .rdi).toNat + 16 ≤ 2 ^ 64)
    (disjoint : 0xa1b7a ≤ (initial.core.read .rdi).toNat + 8 ∨
      (initial.core.read .rdi).toNat + 16 ≤ 0xa1b6f) :
    ∃ mid final,
      Atomic9.step initial = some mid ∧ Atomic9.step mid = some final ∧
      final.core.rip = 0xa1b7a ∧ final.core.regs = initial.core.regs ∧
      final.core.flags = subFlagsN users 1 ∧
      storeN initial.memory (initial.core.read .rdi + 12#64) 4 ((users - 1#32).setWidth 64) = some mid.memory ∧
      storeN mid.memory (initial.core.read .rdi + 8#64) 4 0#64 = some final.memory ∧
      initial.memory.WritesOnly final.memory ((initial.core.read .rdi).toNat + 8) 8 :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockBookkeeping.steps
    rip loaded read usersWritable ownerWritable noWrap disjoint

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping
