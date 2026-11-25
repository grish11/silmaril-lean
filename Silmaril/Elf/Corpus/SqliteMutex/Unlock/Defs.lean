module

public import Silmaril.Elf.Corpus.SqliteMutex.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Defs

/-! The pinned x86-64 SQLite object's mutex-leave tail jumps, at link-time virtual
addresses. The runtime PLT step requires the unlock slot's value in memory. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteMutex.Unlock

open Silmaril.Elf.Link.DynElf
open Silmaril.X86 (Byte MState Word)

def callbackAddress : Word := 0x15560
def pltAddress : Word := 0xf5c0

def callbackBytes : List Byte := [0xe9, 0x5b, 0xa0, 0xff, 0xff]
def pltBytes : List Byte := [0xff, 0x25, 0x02, 0xfd, 0x0f, 0x00]

/-- The unlock PLT relocation, with type R_X86_64_JUMP_SLOT and zero addend. -/
def jumpSlot : Elf.Rela := ⟨0x10f2c8, 7, 41, 0⟩

def unlockRef : Elf.Ref :=
  ⟨"pthread_mutex_unlock".toUTF8.data.toList.map UInt8.toNat, false,
    some ⟨"GLIBC_2.2.5".toUTF8.data.toList.map UInt8.toNat, 157882997, false⟩⟩

/-- Read the 90th entry of DT_JMPREL and its referenced symbol and version. -/
def readUnlock : Rd (Elf.Rela × Elf.Ref) := do
  let dynamic ← Elf.dynInfo
  let offset ← Rd.ofOption (dynamic.tagOff Elf.DT_JMPREL)
  Rd.guard (89 < (dynamic.tag Elf.DT_PLTRELSZ).getD 0 / 24)
  let entry ← Elf.rela (offset + 24 * 89)
  let ref ← Elf.refOf dynamic entry.sym
  pure (entry, ref)

/-- Change the instruction pointer, preserving all other state. -/
def atRip (m : MState) (rip : Word) : MState :=
  ⟨{ m.core with rip }, m.memory⟩

end Silmaril.Elf.Corpus.SqliteMutex.Unlock
