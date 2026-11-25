module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.Defs
public import Silmaril.Elf.Corpus.SqliteMutex.Thms
public import Silmaril.Elf.Staged.Reader.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteMutexUnlock

open Silmaril.Elf
open Silmaril.Elf.Corpus.SqliteMutex
open Silmaril.Elf.Corpus.SqliteMutex.Unlock
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Link.DynElf
open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.Ext.Wire

set_option maxRecDepth 4096

theorem code :
    CodeAt F callbackAddress.toNat callbackBytes ∧ CodeAt F pltAddress.toNat pltBytes :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
      (by decide +kernel) (by decide +kernel),
    codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
      (by decide +kernel) (by decide +kernel)⟩

theorem readsUnlock : readUnlock.run (blobRead F) = some (jumpSlot, unlockRef) :=
  (partIs_of_kbytes K.wf_true K.toByteArray_eq
    (ws := [⟨0, 568⟩, ⟨1109464, 464⟩, ⟨56032, 24⟩, ⟨4032, 24⟩,
      ⟨11352, 6523⟩, ⟨17876, 692⟩, ⟨18568, 96⟩])
    (p := readUnlock) (v := (jumpSlot, unlockRef)) (by decide +kernel)).run

private def callback : Decoded := ⟨.canonical (.jmp 0xffffa05b), callbackBytes⟩
private def slotMem : Silmaril.X86.Ext.Mem := ⟨.rip, none, 0x000ffd02, fun _ => rfl⟩
private def plt : Decoded := ⟨.jmpRM (.mem slotMem), pltBytes⟩

theorem callback_to_plt {platform : Platform} {caller : Word} {m : MState}
    (rip : m.core.rip = callbackAddress)
    (loaded : m.memory.fetchBytes callbackAddress.toNat callbackBytes.length = some callbackBytes) :
    step platform caller m = .retired (atRip m pltAddress) := by
  have addr : m.core.rip.toNat = callbackAddress.toNat := congrArg BitVec.toNat rip
  have read : m.memory.fetchBytes m.core.rip.toNat callback.length = some callbackBytes := by
    rw [addr, show callback.length = callbackBytes.length from rfl]
    exact loaded
  rw [step_of_fetch read (show decode callbackBytes = some callback by decide +kernel)]
  have executed : exec platform callback m.core m.memory = .ok (atRip m pltAddress).core m.memory := by
    simp only [exec, callback, execWithLength, Silmaril.X86.Ext.execWithLength,
      Silmaril.X86.Ext.exec, Decoded.length, callbackBytes, rip]
    rfl
  rw [executed]
  rfl

private theorem plt_slot_address {m : MState} (rip : m.core.rip = pltAddress) :
    slotMem.addr m.core (m.core.rip + BitVec.ofNat 64 plt.length) = BitVec.ofNat 64 jumpSlot.off := by
  rw [rip]
  change 0xf5c0#64 + 6#64 + 0#64 + (0x000ffd02#32).signExtend 64 = 0x10f2c8
  decide +kernel

private theorem plt_slot_read {m : MState} {target : Word}
    (rip : m.core.rip = pltAddress)
    (bound : loadN m.memory (BitVec.ofNat 64 jumpSlot.off) 8 = some target) :
    Silmaril.X86.Ext.readRM .q (.mem slotMem) m.core m.memory
      (m.core.rip + BitVec.ofNat 64 plt.length) = some target := by
  simp only [Silmaril.X86.Ext.readRM, plt_slot_address rip,
    show Silmaril.X86.Ext.Sz.q.bytes = 8 from rfl, bound, Option.map_some]
  exact congrArg some (BitVec.setWidth_eq target)

private theorem exec_indirect (platform : Platform) (src : Silmaril.X86.Ext.RM)
    (bytes : List Silmaril.X86.Byte) (core : Silmaril.X86.State)
    (memory : Silmaril.Process.Memory) (target : Word)
    (read : Silmaril.X86.Ext.readRM .q src core memory
      (core.rip + BitVec.ofNat 64 bytes.length) = some target) :
    exec platform ⟨.jmpRM src, bytes⟩ core memory =
      .ok {core with rip := target} memory := by
  change (match Silmaril.X86.Ext.readRM .q src core memory
      (core.rip + BitVec.ofNat 64 bytes.length) with
    | none => Silmaril.X86.Ext.Result.dataFault
    | some address => .ok {core with rip := address} memory) = _
  rw [read]

private theorem plt_exec {platform : Platform} {m : MState} {target : Word}
    (rip : m.core.rip = pltAddress)
    (bound : loadN m.memory (BitVec.ofNat 64 jumpSlot.off) 8 = some target) :
    exec platform plt m.core m.memory = .ok (atRip m target).core m.memory := by
  exact exec_indirect platform (.mem slotMem) pltBytes m.core m.memory target
    (plt_slot_read rip bound)

theorem plt_to_bound_target {platform : Platform} {caller target : Word} {m : MState}
    (rip : m.core.rip = pltAddress)
    (loaded : m.memory.fetchBytes pltAddress.toNat pltBytes.length = some pltBytes)
    (bound : loadN m.memory (BitVec.ofNat 64 jumpSlot.off) 8 = some target) :
    step platform caller m = .retired (atRip m target) := by
  have addr : m.core.rip.toNat = pltAddress.toNat := congrArg BitVec.toNat rip
  have read : m.memory.fetchBytes m.core.rip.toNat plt.length = some pltBytes := by
    rw [addr, show plt.length = pltBytes.length from rfl]
    exact loaded
  rw [step_of_fetch read (show decode pltBytes = some plt by decide +kernel)]
  have notReturn : ¬ (plt.instr = .canonical .ret ∧ (atRip m target).core.rip = caller) := by
    intro h
    have equal : Instr.jmpRM (.mem slotMem) = .canonical .ret := h.1
    cases equal
  simp only [plt_exec rip bound, ite_eq_right notReturn]
  rfl

theorem wrapper_through_plt {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller callbackAddress) (nonNull : initial.core.read .rdi ≠ 0)
    (callbackLoaded : initial.memory.fetchBytes callbackAddress.toNat callbackBytes.length = some callbackBytes)
    (pltLoaded : initial.memory.fetchBytes pltAddress.toNat pltBytes.length = some pltBytes)
    (bound : loadN initial.memory (BitVec.ofNat 64 jumpSlot.off) 8 = some target) :
    ∃ callbackState pltState targetState,
      run platform caller 3 initial = .handlerEntry callbackState ∧
      step platform caller callbackState = .retired pltState ∧
      step platform caller pltState = .retired targetState ∧
      targetState.core.rip = target ∧ targetState.core.regs = initial.core.regs ∧
      targetState.memory = initial.memory := by
  obtain ⟨cb, runs, rip, regs, sameMem⟩ := Silmaril.Elf.Corpus.SqliteMutex.run_dispatch entry nonNull
  refine ⟨cb, atRip cb pltAddress, atRip (atRip cb pltAddress) target, runs, ?_, ?_, rfl, regs, sameMem⟩
  · exact callback_to_plt rip (sameMem.symm ▸ callbackLoaded)
  · exact plt_to_bound_target rfl (sameMem.symm ▸ pltLoaded) (sameMem.symm ▸ bound)

end Silmaril.Proofs.Elf.Corpus.SqliteMutexUnlock
