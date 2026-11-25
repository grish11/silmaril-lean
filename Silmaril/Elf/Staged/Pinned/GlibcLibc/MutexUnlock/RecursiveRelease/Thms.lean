module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Defs
public import Silmaril.Machine.Execution
public import Silmaril.X86.MemEvent.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveRelease

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease

open Silmaril.X86
open Silmaril.X86.Ext (loadN leBytes)
open Silmaril.Machine.Execution

/-- Ten SC steps reach the exchange with zero depth, full RAX zero,
preserved RDI and lock read, and the actual Atomic9 fetch. The depth, owner
and users dwords are the only bytes that can change. -/
theorem private_to_exchange {initial : MState} {kind users : BitVec 32}
    (entry : Entry initial kind users) :
    ∃ final, run Atomic9.step 10 initial = some final ∧
      final.core.rip = 0xa1ba2 ∧ final.core.read .rax = 0#64 ∧
      final.core.read .rdi = initial.core.read .rdi ∧
      loadN final.memory (initial.core.read .rdi + 4#64) 4 = some 0#64 ∧
      loadN final.memory (initial.core.read .rdi) 4 = loadN initial.memory (initial.core.read .rdi) 4 ∧
      MemEvent.atomic9Fetch final.memory final.core.rip.toNat = some (exchange, 2) ∧
      initial.memory.WritesOnly final.memory ((initial.core.read .rdi).toNat + 4) 12 :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveRelease.private_to_exchange
    entry

/-- With an aligned, readable and writable lock containing the dword one,
the eleven-step SC cut ends after the exchange with RAX one and four zero
lock bytes. The exact frame covers the lock, depth, owner and users dwords.
This proof starts at the reached decrement and ends before the wake test. -/
theorem private_through_exchange_sc {initial : MState} {kind users : BitVec 32}
    (entry : Entry initial kind users)
    (aligned : (initial.core.read .rdi).toNat % 4 = 0)
    (lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4) :
    ∃ final, run Atomic9.step 11 initial = some final ∧
      final.core.rip = 0xa1ba4 ∧ final.core.read .rax = 1#64 ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rdi).toNat 16 ∧
      ∀ address, (initial.core.read .rdi).toNat ≤ address →
        address < (initial.core.read .rdi).toNat + 4 →
        final.memory.bytes.get? address = some 0 :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveRelease.private_through_exchange_sc
    entry aligned lock writable

/-- The same eleven-step SC run, with exact bytes for each updated dword.
The lock, depth and owner dwords contain zero, and the users dword contains
the little-endian encoding of the decremented 32-bit count. -/
theorem private_through_exchange_sc_fields {initial : MState} {kind users : BitVec 32}
    (entry : Entry initial kind users)
    (aligned : (initial.core.read .rdi).toNat % 4 = 0)
    (lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4) :
    ∃ final, run Atomic9.step 11 initial = some final ∧
      final.core.rip = 0xa1ba4 ∧ final.core.read .rax = 1#64 ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rdi).toNat 16 ∧
      (∀ address, (initial.core.read .rdi).toNat ≤ address →
        address < (initial.core.read .rdi).toNat + 4 →
        final.memory.bytes.get? address = some 0) ∧
      ∀ offset, offset < 4 →
        let base := (initial.core.read .rdi).toNat
        final.memory.bytes.get? (base + 4 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 8 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 12 + offset) = (leBytes ((users - 1#32).setWidth 64) 4)[offset]? :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveRelease.private_through_exchange_sc_fields
    entry aligned lock writable


end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease
