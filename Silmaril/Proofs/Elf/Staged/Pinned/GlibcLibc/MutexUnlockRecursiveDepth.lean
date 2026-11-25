module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Atomic9.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveDepth

open Silmaril.Elf
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDepth
open Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.Process (Memory)

theorem code :
    CodeAt F 0xa1c06 depthCode ∧ MutexUnlock.entry.value ≤ 0xa1c06 ∧
      0xa1c06 + depthCode.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel), by decide, by decide⟩

private def depthMem := Mem.ofReg .rdi none 4
private def subOp : Atomic9.Instr := .open9 (.ext8 (.base (.aluI8 .d .sub (.mem depthMem) 1)))
private def branchOp : Atomic9.Instr := .open9 (.ext8 (.base (.jcc .e 0xffffff5f)))

private theorem executeSub (core : State) (memory after : Memory) (depth : BitVec 32)
    (rip : core.rip = 0xa1c06)
    (read : loadN memory (core.read .rdi + 4#64) 4 = some (depth.setWidth 64))
    (write : storeN memory (core.read .rdi + 4#64) 4 ((depth - 1#32).setWidth 64) = some after) :
    Atomic9.exec subOp core memory 4 =
      .ok {core with rip := 0xa1c0a, flags := subFlagsN depth 1} after := by
  have address : ∀ next, depthMem.addr core next = core.read .rdi + 4#64 := by
    intro next
    change core.read .rdi + 0#64 + (4#32).signExtend 64 = core.read .rdi + 4#64
    rw [BitVec.add_zero]
    rfl
  have cast : (depth.setWidth 64).setWidth 32 = depth := by simp
  have loaded : readRM .d (.mem depthMem) core memory (core.rip + 4#64) = some depth := by
    simp only [readRM, address, show Sz.d.bytes = 4 from rfl, read, Option.map_some]
    exact congrArg some cast
  have stored : writeRM .d (.mem depthMem) (depth - 1#32) core memory (core.rip + 4#64) =
      some (core, after) := by
    simp only [writeRM, address, show Sz.d.bytes = 4 from rfl]
    exact congrArg (Option.map (fun updated => (core, updated))) write
  change retire (core.rip + 4#64)
    (aluStep .d .sub (.mem depthMem) 1#32 core memory (core.rip + 4#64)) = _
  unfold aluStep
  rw [loaded]
  simp only [show AluOp.sub ≠ AluOp.cmp by decide, ite_false, AluOp.resultN, AluOp.flagsN]
  erw [stored]
  simp only [retire, Option.map_some, rip]
  rfl

private theorem executeBranch (core : State) (memory : Memory) (depth : BitVec 32)
    (rip : core.rip = 0xa1c0a) (flags : core.flags = subFlagsN depth 1) :
    Atomic9.exec branchOp core memory 6 =
      .ok {core with rip := if depth = 1 then 0xa1b6f else 0xa1c10} memory := by
  have zero : (depth - 1#32 == 0#32) = (depth == 1) := by
    simp [BitVec.sub_eq_iff_eq_add]
  have cond : Cond.e.eval core.flags = some (depth == 1) := by
    rw [flags]
    exact congrArg some zero
  simp only [branchOp, Atomic9.exec, Ext9.exec, Ext8.exec, Ext.exec, cond, rip]
  by_cases last : depth = 1
  · simp only [last, beq_self_eq_true, ite_true]
    rfl
  · simp only [beq_eq_false_iff_ne.mpr last, ite_eq_right last]
    rfl

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
      initial.memory.WritesOnly final.memory (initial.core.read .rdi + 4#64).toNat 4 := by
  let address := initial.core.read .rdi + 4#64
  let value := (depth - 1#32).setWidth 64
  let after : Memory := {initial.memory with
    bytes := Memory.install initial.memory.bytes address.toNat (leBytes value 4)}
  have write : storeN initial.memory address 4 value = some after := by
    unfold storeN Memory.writeBytes
    simp only [length_leBytes, show initial.memory.checkSpan .write address.toNat 4 = true from writable,
      ite_true, after]
  have readable : initial.memory.Permitted .read address.toNat 4 := by
    unfold loadN at read
    change (initial.memory.readBytes address.toNat 4).map _ = some _ at read
    cases h : initial.memory.readBytes address.toNat 4 with
    | none => simp [h] at read
    | some bytes => exact Memory.readWith_permitted h
  have finalDepth : loadN after address 4 = some value := by
    have narrow : value.toNat < 2 ^ (8 * 4) := by
      change ((depth - 1#32).setWidth 64).toNat < 2 ^ 32
      rw [BitVec.toNat_setWidth]
      have fit := (depth - 1#32).isLt
      omega
    rw [loadN_storeN write readable, Nat.mod_eq_of_lt narrow, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  let midCore : State := {initial.core with rip := 0xa1c0a, flags := subFlagsN depth 1}
  let finalCore : State := {midCore with rip := if depth = 1 then 0xa1b6f else 0xa1c10}
  have frame := storeN_writesOnly write
  have afterCode : Loaded after 0xa1c06 depthCode := by
    unfold Loaded at loaded ⊢
    rw [Silmaril.Process.Memory.fetchBytes, Silmaril.X86.Memory.readWith_writesOnly frame .execute _ _ disjoint]
    exact loaded
  refine ⟨⟨midCore, after⟩, ⟨finalCore, after⟩, ?_, ?_, rfl, rfl, finalDepth, frame⟩
  · exact Atomic9.step_of_listed (o := 0) (l := 4) loaded rip
      (by decide +kernel) (by decide +kernel) (executeSub _ _ _ _ rip read write)
  · exact Atomic9.step_of_listed (m := ⟨midCore, after⟩) (o := 4) (l := 6)
      afterCode rfl (by decide +kernel) (by decide +kernel) (executeBranch _ _ _ rfl rfl)

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockRecursiveDepth
