module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Atomic9.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveDepth

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)

/-- The exact two instructions occupy ten bytes inside the versioned unlock
symbol whose lookup is checked by `MutexUnlock.lookup`. -/
theorem code :
    CodeAt F 0xa1c06 depthCode ∧ MutexUnlock.entry.value ≤ 0xa1c06 ∧
      0xa1c06 + depthCode.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveDepth.code

/-- Starting at the reached recursive-depth decrement, the two Atomic9 steps
write the decremented dword and take the release branch exactly for old depth
one. Other depths fall through, using the instruction's 32-bit arithmetic.
The hypotheses cover the effective address and keep the write off the two
fetched instructions. Reaching the decrement requires the earlier owner and
TLS checks. The release path and caller return are separate cuts. -/
theorem steps {initial : MState} {depth : BitVec 32}
    (rip : initial.core.rip = 0xa1c06)
    (loaded : Loaded initial.memory 0xa1c06 depthCode)
    (read : loadN initial.memory (initial.core.read .rdi + 4#64) 4 = some (depth.setWidth 64))
    (writable : initial.memory.Permitted .write (initial.core.read .rdi + 4#64).toNat 4)
    (disjoint : 0xa1c10 ≤ (initial.core.read .rdi + 4#64).toNat ∨
      (initial.core.read .rdi + 4#64).toNat + 4 ≤ 0xa1c06) :
    ∃ mid final, Atomic9.step initial = some mid ∧ Atomic9.step mid = some final ∧
      final.core.rip = (if depth = 1 then 0xa1b6f else 0xa1c10) ∧
      final.core.regs = initial.core.regs ∧
      loadN final.memory (initial.core.read .rdi + 4#64) 4 = some ((depth - 1#32).setWidth 64) ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rdi + 4#64).toNat 4 :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveDepth.steps
    rip loaded read writable disjoint

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth
