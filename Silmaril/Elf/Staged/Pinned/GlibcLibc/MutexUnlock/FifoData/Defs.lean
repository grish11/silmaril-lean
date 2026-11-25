module

public import Silmaril.X86.Ext.Semantics
public import Silmaril.X86.MemoryModel.Tso.Defs

/-! A byte FIFO data schedule for the private threaded path of the pinned
glibc unlock. The two unlocked decrements each contribute a load and an
ordinary store. Branch selection and native instruction execution are
specified by the separate Atomic9 contracts. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData

open Silmaril.X86.Ext (leBytes)
open Silmaril.X86.MemoryModel.Tso

def zeroDword : List Byte := [0, 0, 0, 0]

def usersDword (users : BitVec 32) : List Byte :=
  leBytes ((users - 1#32).setWidth 64) 4

def stores (tid base : Nat) (users : BitVec 32) : List (XEvent Nat) :=
  [.store tid (base + 4) zeroDword,
    .store tid (base + 12) (usersDword users),
    .store tid (base + 8) zeroDword]

def committedStores (memory : Mem) (base : Nat) (users : BitVec 32) : Mem :=
  writeMem (writeMem (writeMem memory (base + 4) zeroDword)
    (base + 12) (usersDword users)) (base + 8) zeroDword

/-- The data events for the selected arm, in program order. The final event
is a locked dword exchange. -/
def dataEvents (tid base : Nat) (users kind : BitVec 32) : List (XEvent Nat) :=
  [.load tid (base + 4) [1, 0, 0, 0],
    .store tid (base + 4) zeroDword,
    .load tid (base + 12) (leBytes (users.setWidth 64) 4),
    .store tid (base + 12) (usersDword users),
    .store tid (base + 8) zeroDword,
    .load tid (base + 16) (leBytes (kind.setWidth 64) 4),
    .load tid 0x20c040 [0],
    .rmw tid base [1, 0, 0, 0] zeroDword]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData
