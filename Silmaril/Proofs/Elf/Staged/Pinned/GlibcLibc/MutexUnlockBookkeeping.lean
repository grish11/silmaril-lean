module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Atomic9.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockBookkeeping

open Silmaril.Elf
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Bookkeeping
open Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.Process (Memory)

theorem code : CodeAt F 0xa1b6f codeBytes ∧ MutexUnlock.entry.value ≤ 0xa1b6f ∧
    0xa1b6f + codeBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel), by decide, by decide⟩

private def usersMem := Mem.ofReg .rdi none 12
private def ownerMem := Mem.ofReg .rdi none 8
private def subOp : Atomic9.Instr := .open9 (.ext8 (.base (.aluI8 .d .sub (.mem usersMem) 1)))
private def ownerOp : Atomic9.Instr := .open9 (.ext8 (.base (.movI .d (.mem ownerMem) 0)))

private theorem executeSub (core : State) (memory after : Memory) (users : BitVec 32)
    (rip : core.rip = 0xa1b6f)
    (read : loadN memory (core.read .rdi + 12#64) 4 = some (users.setWidth 64))
    (write : storeN memory (core.read .rdi + 12#64) 4 ((users - 1#32).setWidth 64) = some after) :
    Atomic9.exec subOp core memory 4 =
      .ok {core with rip := 0xa1b73, flags := subFlagsN users 1} after := by
  have address : ∀ next, usersMem.addr core next = core.read .rdi + 12#64 := by
    intro next
    change core.read .rdi + 0#64 + (12#32).signExtend 64 = core.read .rdi + 12#64
    rw [BitVec.add_zero]
    rfl
  have cast : (users.setWidth 64).setWidth 32 = users := by simp
  have loaded : readRM .d (.mem usersMem) core memory (core.rip + 4#64) = some users := by
    simp only [readRM, address, show Sz.d.bytes = 4 from rfl, read, Option.map_some]
    exact congrArg some cast
  have stored : writeRM .d (.mem usersMem) (users - 1#32) core memory (core.rip + 4#64) =
      some (core, after) := by
    simp only [writeRM, address, show Sz.d.bytes = 4 from rfl]
    exact congrArg (Option.map (fun updated => (core, updated))) write
  change retire (core.rip + 4#64)
    (aluStep .d .sub (.mem usersMem) 1#32 core memory (core.rip + 4#64)) = _
  unfold aluStep
  rw [loaded]
  simp only [show AluOp.sub ≠ AluOp.cmp by decide, ite_false, AluOp.resultN, AluOp.flagsN]
  erw [stored]
  simp only [retire, Option.map_some, rip]
  rfl

private theorem executeOwner (core : State) (memory after : Memory)
    (rip : core.rip = 0xa1b73)
    (write : storeN memory (core.read .rdi + 8#64) 4 0#64 = some after) :
    Atomic9.exec ownerOp core memory 7 = .ok {core with rip := 0xa1b7a} after := by
  have address : ∀ next, ownerMem.addr core next = core.read .rdi + 8#64 := by
    intro next
    change core.read .rdi + 0#64 + (8#32).signExtend 64 = core.read .rdi + 8#64
    rw [BitVec.add_zero]
    rfl
  have stored : writeRM .d (.mem ownerMem) 0#32 core memory (core.rip + 7#64) =
      some (core, after) := by
    simp only [writeRM, address, show Sz.d.bytes = 4 from rfl]
    exact congrArg (Option.map (fun updated => (core, updated))) write
  change retire (core.rip + 7#64)
    (writeRM .d (.mem ownerMem) 0#32 core memory (core.rip + 7#64)) = _
  rw [stored, rip]
  rfl

private theorem storeDword {memory : Memory} {address : Word} (value : Word)
    (writable : memory.Permitted .write address.toNat 4) :
    ∃ after, storeN memory address 4 value = some after := by
  refine ⟨⟨memory.regions, Memory.install memory.bytes address.toNat (leBytes value 4)⟩, ?_⟩
  unfold storeN Memory.writeBytes
  simp only [length_leBytes, show memory.checkSpan .write address.toNat 4 = true from writable,
    ite_true]

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
      initial.memory.WritesOnly final.memory ((initial.core.read .rdi).toNat + 8) 8 := by
  let base := initial.core.read .rdi
  have ownerNat : (base + 8#64).toNat = base.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (base.toNat + 8) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by change base.toNat + 16 ≤ 2 ^ 64 at noWrap; omega)
  have usersNat : (base + 12#64).toNat = base.toNat + 12 := by
    rw [BitVec.toNat_add]
    change (base.toNat + 12) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by change base.toNat + 16 ≤ 2 ^ 64 at noWrap; omega)
  obtain ⟨midMemory, usersStore⟩ := storeDword ((users - 1#32).setWidth 64) usersWritable
  have usersFrame := storeN_writesOnly usersStore
  have midWritable : midMemory.Permitted .write (base + 8#64).toNat 4 := by
    unfold Memory.Permitted
    rw [Silmaril.X86.Memory.checkSpan_congr usersFrame.1]
    exact ownerWritable
  obtain ⟨finalMemory, ownerStore⟩ := storeDword 0#64 midWritable
  have ownerFrame := storeN_writesOnly ownerStore
  have usersDisjoint : (0xa1b6f#64).toNat + codeBytes.length ≤ (base + 12#64).toNat ∨
      (base + 12#64).toNat + 4 ≤ (0xa1b6f#64).toNat := by
    rw [usersNat]
    change 0xa1b7a ≤ base.toNat + 12 ∨ base.toNat + 12 + 4 ≤ 0xa1b6f
    change 0xa1b7a ≤ base.toNat + 8 ∨ base.toNat + 16 ≤ 0xa1b6f at disjoint
    omega
  have midCode : Loaded midMemory 0xa1b6f#64 codeBytes := by
    unfold Loaded at loaded ⊢
    rw [Memory.fetchBytes, Silmaril.X86.Memory.readWith_writesOnly usersFrame .execute _ _ usersDisjoint]
    exact loaded
  let midCore : State := {initial.core with rip := 0xa1b73, flags := subFlagsN users 1}
  let finalCore : State := {midCore with rip := 0xa1b7a}
  refine ⟨⟨midCore, midMemory⟩, ⟨finalCore, finalMemory⟩, ?_, ?_, rfl, rfl, rfl,
    usersStore, ownerStore, ?_⟩
  · exact Atomic9.step_of_listed (o := 0) (l := 4) loaded rip
      (by decide +kernel) (by decide +kernel) (executeSub _ _ _ _ rip read usersStore)
  · exact Atomic9.step_of_listed (m := ⟨midCore, midMemory⟩) (o := 4) (l := 7)
      midCode rfl (by decide +kernel) (by decide +kernel) (executeOwner _ _ _ rfl ownerStore)
  · refine ⟨ownerFrame.1.trans usersFrame.1, ?_⟩
    intro location outside
    change location < base.toNat + 8 ∨ base.toNat + 8 + 8 ≤ location at outside
    have outsideOwner : location < (base + 8#64).toNat ∨ (base + 8#64).toNat + 4 ≤ location := by
      rw [ownerNat]
      omega
    have outsideUsers : location < (base + 12#64).toNat ∨ (base + 12#64).toNat + 4 ≤ location := by
      rw [usersNat]
      omega
    exact (ownerFrame.2 location outsideOwner).trans (usersFrame.2 location outsideUsers)

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockBookkeeping
