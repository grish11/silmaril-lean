module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockFifoData

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData

open Silmaril.X86.Ext (leBytes)
open Silmaril.X86.MemoryModel.Tso

/-- The issuer can buffer the three stores without changing shared memory.
Draining in FIFO order gives the same bytes as its forwarded view before
the drain. A locked exchange can then clear the unchanged lock dword.
This schedule leaves peer buffers untouched. -/
theorem buffer_and_release (initial : XState Nat) (tid base : Nat) (users : BitVec 32)
    (empty : initial.buffer tid = [])
    (lock : readMem initial.memory base 4 = some [1, 0, 0, 0]) :
    ∃ queued drained final,
      queued = enqueue (enqueue (enqueue initial tid (base + 4) zeroDword)
        tid (base + 12) (usersDword users)) tid (base + 8) zeroDword ∧
      Execution XStep initial (stores tid base users) queued ∧
      queued.buffer tid =
        [(base + 4, zeroDword), (base + 12, usersDword users), (base + 8, zeroDword)] ∧
      queued.memory = initial.memory ∧
      XFlushes queued drained ∧ drained.buffer tid = [] ∧
      viewMem queued tid = drained.memory ∧
      (∀ address, address < base + 4 ∨ base + 16 ≤ address →
        drained.memory address = initial.memory address) ∧
      XWeakStep queued (.rmw tid base [1, 0, 0, 0] zeroDword) final ∧
      final.memory = writeMem (committedStores initial.memory base users) base zeroDword ∧
      (∀ peer, peer ≠ tid → final.buffer peer = initial.buffer peer) :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockFifoData.buffer_and_release
    initial tid base users empty lock

/-- A finite FIFO execution of the eight data events. The three updates
remain buffered across the disjoint loads and drain before the exchange.
The final memory is the ordered four writes and the issuer ends drained. -/
theorem data_and_release (initial : XState Nat) (tid base : Nat) (users kind : BitVec 32)
    (empty : initial.buffer tid = [])
    (depth : readView initial tid (base + 4) 4 = some [1, 0, 0, 0])
    (count : readView initial tid (base + 12) 4 = some (leBytes (users.setWidth 64) 4))
    (kindRead : readView initial tid (base + 16) 4 = some (leBytes (kind.setWidth 64) 4))
    (flag : readView initial tid 0x20c040 1 = some [0])
    (flagApart : 0x20c041 ≤ base + 4 ∨ base + 16 ≤ 0x20c040)
    (lock : readMem initial.memory base 4 = some [1, 0, 0, 0]) :
    ∃ final, Execution XWeakStep initial (dataEvents tid base users kind) final ∧
      final.buffer tid = [] ∧
      final.memory = writeMem (committedStores initial.memory base users) base zeroDword ∧
      ∀ peer, peer ≠ tid → final.buffer peer = initial.buffer peer :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockFifoData.data_and_release
    initial tid base users kind empty depth count kindRead flag flagApart lock

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData
