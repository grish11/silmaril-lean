module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath.Thms
import Silmaril.X86.Atomic9.Converse.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Step.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveRelease

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Machine.Execution
open Silmaril.Process (Memory)

private def mutexWrites (base : Word) (address : Nat) : Prop :=
  base.toNat + 4 ≤ address ∧ address < base.toNat + 16

private theorem loaded_framed {before after : Memory} {base start : Word}
    {code : List Byte} (frame : before.WritesWithin after (mutexWrites base))
    (loaded : Loaded before start code)
    (apart : base.toNat + 16 ≤ start.toNat ∨ start.toNat + code.length ≤ base.toNat + 4) :
    Loaded after start code := by
  unfold Loaded at loaded ⊢
  rw [frame.fetchBytes]
  · exact loaded
  · intro offset fits
    unfold mutexWrites
    omega

private theorem load_framed {before after : Memory} {base address : Word} {length : Nat}
    (frame : before.WritesWithin after (mutexWrites base))
    (apart : base.toNat + 16 ≤ address.toNat ∨ address.toNat + length ≤ base.toNat + 4) :
    loadN after address length = loadN before address length := by
  unfold loadN
  rw [frame.readBytes]
  intro offset fits
  unfold mutexWrites
  omega

theorem private_to_exchange {initial : MState} {kind users : BitVec 32}
    (entry : Entry initial kind users) :
    ∃ final, run Atomic9.step 10 initial = some final ∧
      final.core.rip = 0xa1ba2 ∧ final.core.read .rax = 0#64 ∧
      final.core.read .rdi = initial.core.read .rdi ∧
      loadN final.memory (initial.core.read .rdi + 4#64) 4 = some 0#64 ∧
      loadN final.memory (initial.core.read .rdi) 4 = loadN initial.memory (initial.core.read .rdi) 4 ∧
      MemEvent.atomic9Fetch final.memory final.core.rip.toNat = some (exchange, 2) ∧
      initial.memory.WritesOnly final.memory ((initial.core.read .rdi).toNat + 4) 12 := by
  let base := initial.core.read .rdi
  have nowrap : base.toNat + 20 ≤ 2 ^ 64 := entry.noWrap
  have address (offset : Nat) (small : offset < 20) :
      (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have depthAddress : (base + 4#64).toNat = base.toNat + 4 := address 4 (by decide)
  have usersAddress : (base + 12#64).toNat = base.toNat + 12 := address 12 (by decide)
  have kindAddress : (base + 16#64).toNat = base.toNat + 16 := address 16 (by decide)
  have codeApart {address length : Nat} (start : 0xa1b6f ≤ address)
      (endBound : address + length ≤ 0xa1c10) :
      base.toNat + 16 ≤ address ∨ address + length ≤ base.toNat + 4 := by
    have h := entry.codeApart
    change base.toNat + 16 ≤ 0xa1b6f ∨ 0xa1c10 ≤ base.toNat + 4 at h
    omega
  have depthDisjoint : 0xa1c10 ≤ (base + 4#64).toNat ∨
      (base + 4#64).toNat + 4 ≤ 0xa1c06 := by
    rw [depthAddress]
    have := entry.codeApart
    change base.toNat + 16 ≤ 0xa1b6f ∨ 0xa1c10 ≤ base.toNat + 4 at this
    omega
  obtain ⟨dMid, depth, depthSub, depthBranch, depthRip, depthRegs, depthRead, depthFrame⟩ :=
    RecursiveDepth.steps (depth := 1#32) entry.rip entry.depthCode entry.depthOne entry.depthWrite depthDisjoint
  have depthRdi : depth.core.read .rdi = base := by
    unfold State.read
    rw [depthRegs]
    rfl
  have depthWritten : initial.memory.WritesWithin depth.memory (mutexWrites base) := by
    have small := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp depthFrame
    apply small.mono
    intro location inside
    change (base + 4#64).toNat ≤ location ∧ location < (base + 4#64).toNat + 4 at inside
    rw [depthAddress] at inside
    unfold mutexWrites
    omega
  have depthRuns : run Atomic9.step 2 initial = some depth := by
    simp [run_succ, depthSub, depthBranch]
  have usersRead : loadN depth.memory (depth.core.read .rdi + 12#64) 4 =
      some (users.setWidth 64) := by
    have apart : (base + 4#64).toNat + 4 ≤ (base + 12#64).toNat := by
      rw [depthAddress, usersAddress]
      omega
    rw [depthRdi, loadN, Memory.readBytes,
      Memory.readWith_writesOnly depthFrame .read _ _ (.inr apart)]
    exact entry.usersRead
  have usersWrite : depth.memory.Permitted .write (depth.core.read .rdi + 12#64).toNat 4 := by
    rw [depthRdi, depthWritten.permitted_iff]
    exact entry.usersWrite
  have ownerWrite : depth.memory.Permitted .write (depth.core.read .rdi + 8#64).toNat 4 := by
    rw [depthRdi, depthWritten.permitted_iff]
    exact entry.ownerWrite
  have updateLoaded : Loaded depth.memory 0xa1b6f Bookkeeping.codeBytes :=
    loaded_framed depthWritten entry.updateCode (codeApart (by decide) (by decide))
  have updateNoWrap : (depth.core.read .rdi).toNat + 16 ≤ 2 ^ 64 := by
    rw [depthRdi]
    omega
  have updateDisjoint : 0xa1b7a ≤ (depth.core.read .rdi).toNat + 8 ∨
      (depth.core.read .rdi).toNat + 16 ≤ 0xa1b6f := by
    rw [depthRdi]
    have := entry.codeApart
    change base.toNat + 16 ≤ 0xa1b6f ∨ 0xa1c10 ≤ base.toNat + 4 at this
    omega
  obtain ⟨uMid, updated, usersSub, ownerClear, updatedRip, updatedRegs, _, _, _, updateFrame⟩ :=
    Bookkeeping.steps (show depth.core.rip = 0xa1b6f from depthRip)
      updateLoaded usersRead usersWrite ownerWrite updateNoWrap updateDisjoint
  have updatedRdi : updated.core.read .rdi = base := by
    unfold State.read
    rw [updatedRegs, depthRegs]
    rfl
  have updateWritten : depth.memory.WritesWithin updated.memory (mutexWrites base) := by
    rw [depthRdi] at updateFrame
    have small := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp updateFrame
    apply small.mono
    intro location inside
    change base.toNat + 8 ≤ location ∧ location < base.toNat + 8 + 8 at inside
    unfold mutexWrites
    omega
  have total := depthWritten.trans updateWritten
  have updateRuns : run Atomic9.step 2 depth = some updated := by
    simp [run_succ, usersSub, ownerClear]
  have selectLoaded : Loaded updated.memory 0xa1b7a ExchangePath.selectBytes :=
    loaded_framed total entry.selectCode (codeApart (by decide) (by decide))
  have clearLoaded : Loaded updated.memory 0xa1ba0 ExchangePath.clearBytes :=
    loaded_framed total entry.clearCode (codeApart (by decide) (by decide))
  have kindRead : loadN updated.memory (updated.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64) := by
    rw [updatedRdi, load_framed total]
    · exact entry.kindRead
    · rw [kindAddress]
      exact .inl (Nat.le_refl _)
  have threadRead : loadN updated.memory 0x20c040 1 = some 0#64 := by
    rw [load_framed total]
    · exact entry.threadRead
    · exact entry.threadApart
  obtain ⟨final, selects, finalRip, finalRax, finalRdi, finalMemory⟩ :=
    ExchangePath.private_threaded_exchange updatedRip selectLoaded clearLoaded
      kindRead entry.privateKind threadRead
  refine ⟨final, ?_, finalRip, finalRax, finalRdi.trans updatedRdi, ?_, ?_, ?_, ?_⟩
  · change run Atomic9.step (2 + (2 + 6)) initial = some final
    rw [run_add, depthRuns]
    change run Atomic9.step (2 + 6) depth = some final
    rw [run_add, updateRuns]
    exact selects
  · rw [finalMemory]
    rw [depthRdi] at updateFrame
    have apart : (base + 4#64).toNat + 4 ≤ base.toNat + 8 := by
      rw [depthAddress]
    unfold loadN at depthRead ⊢
    rw [Memory.readBytes, Memory.readWith_writesOnly updateFrame .read _ _ (.inl apart)]
    exact depthRead
  · rw [finalMemory]
    exact load_framed total (.inr (Nat.le_refl _))
  · rw [finalMemory]
    have loaded : Loaded updated.memory 0xa1ba2 exchangeBytes :=
      loaded_framed total entry.exchangeCode (codeApart (by decide) (by decide))
    exact Atomic9.fetch_of_listed_new (o := 0) (l := 2) loaded finalRip
      (by decide +kernel) decode
  · rw [finalMemory]
    exact (Memory.writesOnly_iff_writesWithin _ _ _ _).mpr total

open Silmaril.X86.MemoryModel.Tso
open Silmaril.X86.Concurrency.Sqlite.Release

private theorem readBacking_eq_fifoRead (bytes : Silmaril.Process.ByteMemory) (start length : Nat) :
    Memory.readBacking bytes start length = readMem (fun address => bytes.get? address) start length := by
  induction length generalizing start with
  | zero => rfl
  | succ length previous =>
    simp only [Memory.readBacking, readMem, previous]
    cases bytes.get? start <;>
      cases readMem (fun address => bytes.get? address) (start + 1) length <;> rfl

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
        final.memory.bytes.get? address = some 0 := by
  obtain ⟨before, reached, rip, zero, rdi, _, _, fetched, prefixFrame⟩ := private_to_exchange entry
  let base := (initial.core.read .rdi).toNat
  have readLock : before.memory.readBytes base 4 = some [1, 0, 0, 0] := by
    unfold Memory.readBytes
    rw [Silmaril.X86.Memory.readWith_writesOnly prefixFrame .read base 4 (.inl (Nat.le_refl _))]
    exact lock
  have readable : before.memory.Permitted .read base 4 := Memory.readWith_permitted readLock
  have afterWritable : before.memory.Permitted .write base 4 := by
    unfold Memory.Permitted
    rw [Silmaril.X86.Memory.checkSpan_congr prefixFrame.1]
    exact writable
  let view : XState Nat := ⟨fun address => before.memory.bytes.get? address, fun _ => []⟩
  let written : XState Nat := {view with memory := writeMem view.memory base [0, 0, 0, 0]}
  have old : readMem view.memory (before.core.read .rdi).toNat 4 = some [1, 0, 0, 0] := by
    rw [rdi]
    unfold Memory.readBytes Memory.readWith at readLock
    rw [ite_eq_left (show before.memory.checkSpan .read base 4 = true from readable),
      readBacking_eq_fifoRead] at readLock
    exact readLock
  have confined : ∀ address, (before.core.read .rdi).toNat ≤ address →
      address < (before.core.read .rdi).toNat + 4 → BuffersAvoid view address := by
    intro address _ _ tid pending queued
    simp [view] at queued
  have alignAt : (before.core.read .rdi).toNat % 4 = 0 := by rw [rdi]; exact aligned
  have readAt : before.memory.Permitted .read (before.core.read .rdi).toNat 4 := by
    rw [rdi]
    exact readable
  have writeAt : before.memory.Permitted .write (before.core.read .rdi).toNat 4 := by
    rw [rdi]
    exact afterWritable
  have tail : XFlushes
      { view with memory := writeMem view.memory (before.core.read .rdi).toNat [0, 0, 0, 0] }
      written := by
    rw [rdi]
  obtain ⟨after, executes, exchangeFrame, _, byteView, cleared, _, _⟩ :=
    step_and_publication before.core before.memory view view written 0 fetched zero alignAt
      (fun _ => rfl) readAt writeAt .refl rfl old tail confined
  let final : MState := ⟨{before.core.write .rax 1 with rip := before.core.rip + 2}, after⟩
  refine ⟨final, ?_, ?_, rfl, ?_, ?_⟩
  · change run Atomic9.step (10 + 1) initial = some final
    rw [run_add, reached]
    change run Atomic9.step 1 before = some final
    rw [run_succ, executes]
    rfl
  · change before.core.rip + 2 = 0xa1ba4
    rw [rip]
    rfl
  · rw [rdi] at exchangeFrame
    refine ⟨exchangeFrame.1.trans prefixFrame.1, ?_⟩
    intro address outside
    change address < base ∨ base + 16 ≤ address at outside
    exact (exchangeFrame.2 address (by change address < base ∨ base + 4 ≤ address; omega)).trans
      (prefixFrame.2 address (by change address < base + 4 ∨ base + 4 + 12 ≤ address; omega))
  · intro address lo hi
    rw [rdi] at byteView cleared
    exact (byteView address).trans (cleared address lo hi)

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveRelease
