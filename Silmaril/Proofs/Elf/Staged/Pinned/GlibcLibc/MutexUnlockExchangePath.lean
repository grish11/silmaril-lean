module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Atomic9.Thms
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath

open Silmaril.Elf
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ExchangePath
open Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution

theorem code :
    CodeAt F 0xa1b7a selectBytes ∧ CodeAt F 0xa1ba0 clearBytes ∧
      MutexUnlock.entry.value ≤ 0xa1b7a ∧
      0xa1ba0 + clearBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel),
   codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel), by decide, by decide⟩

private def wrap (instr : Ext.Instr) : Atomic9.Instr := .open9 (.ext8 (.base instr))
private def kindMem := Mem.ofReg .rdi none 16
private def threadMem : Ext.Mem := ⟨.rip, none, 0x0016a4b4, fun _ => rfl⟩

private def kindCore (core : State) (kind : BitVec 32) : State :=
  { Sz.d.write core .rsi kind with rip := 0xa1b7d }

private def maskCore (core : State) (kind : BitVec 32) : State :=
  { Sz.d.write (kindCore core kind) .rsi (kind &&& 128#32) with
    rip := 0xa1b83, flags := logicFlagsN (kind &&& 128#32) }

private def clearCore (core : State) : State :=
  { Sz.d.write core .rax 0#32 with rip := 0xa1ba2, flags := logicFlagsN 0#32 }

private theorem execKind (core : State) (memory : Memory) (kind : BitVec 32)
    (rip : core.rip = 0xa1b7a)
    (load : loadN memory (core.read .rdi + 16#64) 4 = some (kind.setWidth 64)) :
    Atomic9.exec (wrap (.load .d .rsi kindMem)) core memory 3 =
      .ok (kindCore core kind) memory := by
  have address : kindMem.addr core (core.rip + 3#64) = core.read .rdi + 16#64 := by
    change core.read .rdi + 0#64 + (16#32).signExtend 64 = core.read .rdi + 16#64
    rw [BitVec.add_zero]
    rfl
  have readKind : readRM .d (.mem kindMem) core memory (core.rip + 3#64) = some kind := by
    simp only [readRM, address, show Sz.d.bytes = 4 from rfl, load, Option.map_some]
    exact congrArg some (show (kind.setWidth 64).setWidth 32 = kind by simp)
  change retire (core.rip + 3#64)
    ((readRM .d (.mem kindMem) core memory (core.rip + 3#64)).map
      (fun value => (Sz.d.write core .rsi value, memory))) = _
  rw [readKind, rip]
  rfl

private theorem execMask (core : State) (memory : Memory) (kind : BitVec 32) :
    Atomic9.exec (wrap (.aluI .d .and (.reg .rsi) 128)) (kindCore core kind) memory 6 =
      .ok (maskCore core kind) memory := by
  have read : Sz.d.read (kindCore core kind) .rsi = kind := by
    simp [kindCore, Sz.read, Sz.write, State.read, State.write]
  change Ext.exec (.aluI .d .and (.reg .rsi) 128) (kindCore core kind) memory = _
  rw [exec_aluI_reg _ _ _ _ _ _ (by decide), read]
  rfl

private def destination (kind : BitVec 32) : Word :=
  if kind &&& 128#32 = 0 then 0xa1b85 else 0xa1ba0

private theorem execSelect (core : State) (memory : Memory) (kind : BitVec 32) :
    Atomic9.exec (wrap (.jcc8 .ne 0x1b)) (maskCore core kind) memory 2 =
      .ok {maskCore core kind with rip := destination kind} memory := by
  have cond : Cond.ne.eval (maskCore core kind).flags =
      some (!(kind &&& 128#32 == 0)) := rfl
  simp only [wrap, Atomic9.exec, Ext9.exec, Ext8.exec, Ext.exec, cond, destination]
  by_cases h : kind &&& 128#32 = 0
  · simp only [h, beq_self_eq_true, Bool.not_true, ite_true]
    rfl
  · simp only [beq_eq_false_iff_ne.mpr h, Bool.not_false, ite_eq_right h]
    rfl

private theorem execThread (core : State) (memory : Memory) (value : Byte)
    (rip : core.rip = 0xa1b85)
    (load : loadN memory 0x20c040 1 = some (value.setWidth 64)) :
    Atomic9.exec (wrap (.cmpI8 (.mem threadMem) 0)) core memory 7 =
      .ok {core with rip := 0xa1b8c, flags := subFlagsN value 0} memory := by
  have address : threadMem.addr core (core.rip + 7#64) = 0x20c040 := by
    rw [rip]
    change 0xa1b85#64 + 7#64 + 0#64 + (0x0016a4b4#32).signExtend 64 = 0x20c040
    decide +kernel
  have read : readNarrow .b (.mem threadMem) core memory (core.rip + 7#64) = some value := by
    simp only [readNarrow, address, show Narrow.b.bytes = 1 from rfl, load, Option.map_some]
    exact congrArg some (show (value.setWidth 64).setWidth 8 = value by simp)
  change retire (core.rip + 7#64)
    ((readNarrow .b (.mem threadMem) core memory (core.rip + 7#64)).map
      (fun observed => ({core with flags := subFlagsN observed 0}, memory))) = _
  rw [read, rip]
  rfl

private theorem execPrivateSelect (core : State) (memory : Memory) (value : Byte)
    (rip : core.rip = 0xa1b8c) (flags : core.flags = subFlagsN value 0) :
    Atomic9.exec (wrap (.jcc8 .e 0x12)) core memory 2 =
      .ok { core with rip := if value = 0 then 0xa1ba0 else 0xa1b8e } memory := by
  have cond : Cond.e.eval core.flags = some (value == 0) := by
    rw [flags]
    change some (value - 0#8 == 0#8) = _
    simp
  simp only [wrap, Atomic9.exec, Ext9.exec, Ext8.exec, Ext.exec, cond, rip]
  by_cases h : value = 0
  · simp only [h, beq_self_eq_true, ite_true]
    rfl
  · simp only [beq_eq_false_iff_ne.mpr h, ite_eq_right h]
    rfl

private theorem execClear (core : State) (memory : Memory) (rip : core.rip = 0xa1ba0) :
    Atomic9.exec (wrap (.alu .d .xor (.reg .rax) .rax)) core memory 2 =
      .ok (clearCore core) memory := by
  change Ext.exec (.alu .d .xor (.reg .rax) .rax) core memory = _
  rw [exec_alu_reg _ _ _ _ _ _ (by decide)]
  simp only [AluOp.resultN, AluOp.flagsN, BitVec.xor_self, rip]
  rfl

private theorem select_path {initial : MState} {kind : BitVec 32}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64)) :
    run Atomic9.step 3 initial =
      some ⟨{maskCore initial.core kind with rip := destination kind}, initial.memory⟩ := by
  let afterKind : MState := ⟨kindCore initial.core kind, initial.memory⟩
  let afterMask : MState := ⟨maskCore initial.core kind, initial.memory⟩
  have first : Atomic9.step initial = some afterKind :=
    Atomic9.step_of_listed (o := 0) (l := 3) loaded rip
      (by decide +kernel) (by decide +kernel) (execKind _ _ _ rip kindRead)
  have second : Atomic9.step afterKind = some afterMask :=
    Atomic9.step_of_listed (m := afterKind) (o := 3) (l := 6) loaded rfl
      (by decide +kernel) (by decide +kernel) (execMask _ _ _)
  have third : Atomic9.step afterMask =
      some ⟨{maskCore initial.core kind with rip := destination kind}, initial.memory⟩ :=
    Atomic9.step_of_listed (m := afterMask) (o := 9) (l := 2) loaded rfl
      (by decide +kernel) (by decide +kernel) (execSelect _ _ _)
  simp [run_succ, first, second, third]

private def threadResult (core : State) (value : Byte) : State :=
  { core with
    rip := if value = 0 then 0xa1ba0 else 0xa1b8e
    flags := subFlagsN value 0 }

private theorem private_branch {initial : MState} {value : Byte}
    (rip : initial.core.rip = 0xa1b85)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (read : loadN initial.memory 0x20c040 1 = some (value.setWidth 64)) :
    run Atomic9.step 2 initial =
      some ⟨threadResult initial.core value, initial.memory⟩ := by
  let afterTest : MState := ⟨{initial.core with rip := 0xa1b8c, flags := subFlagsN value 0},
    initial.memory⟩
  have first : Atomic9.step initial = some afterTest :=
    Atomic9.step_of_listed (o := 11) (l := 7) loaded rip
      (by decide +kernel) (by decide +kernel) (execThread _ _ _ rip read)
  have second : Atomic9.step afterTest =
      some ⟨threadResult initial.core value, initial.memory⟩ :=
    Atomic9.step_of_listed (m := afterTest) (o := 18) (l := 2) loaded rfl
      (by decide +kernel) (by decide +kernel) (execPrivateSelect _ _ _ rfl rfl)
  simp [run_succ, first, second]

private theorem clear_to_exchange {initial : MState}
    (rip : initial.core.rip = 0xa1ba0)
    (loaded : Loaded initial.memory 0xa1ba0 clearBytes) :
    Atomic9.step initial = some ⟨clearCore initial.core, initial.memory⟩ :=
  Atomic9.step_of_listed (o := 0) (l := 2) loaded rip
    (by decide +kernel) (by decide +kernel) (execClear _ _ rip)

theorem shared_exchange {initial : MState} {kind : BitVec 32}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (clearLoaded : Loaded initial.memory 0xa1ba0 clearBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (shared : kind &&& 128#32 ≠ 0) :
    ∃ final, run Atomic9.step 4 initial = some final ∧ final.core.rip = 0xa1ba2 ∧
      final.core.read .rax = 0#64 ∧ final.core.read .rdi = initial.core.read .rdi ∧
      final.memory = initial.memory := by
  let selected : MState := ⟨{maskCore initial.core kind with rip := 0xa1ba0}, initial.memory⟩
  let final : MState := ⟨clearCore selected.core, selected.memory⟩
  have picks : run Atomic9.step 3 initial = some selected := by
    simpa only [destination, ite_eq_right shared] using select_path rip loaded kindRead
  have clear : Atomic9.step selected = some final := clear_to_exchange rfl clearLoaded
  refine ⟨final, ?_, rfl, rfl, rfl, rfl⟩
  change run Atomic9.step (3 + 1) initial = some final
  rw [run_add, picks]
  change run Atomic9.step 1 selected = some final
  rw [run_succ, clear]
  rfl

private theorem private_select {initial : MState} {kind : BitVec 32} {value : Byte}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (privateKind : kind &&& 128#32 = 0)
    (threadRead : loadN initial.memory 0x20c040 1 = some (value.setWidth 64)) :
    run Atomic9.step 5 initial =
      some ⟨threadResult (maskCore initial.core kind) value, initial.memory⟩ := by
  let selected : MState := ⟨{maskCore initial.core kind with rip := 0xa1b85}, initial.memory⟩
  have picks : run Atomic9.step 3 initial = some selected := by
    simpa only [destination, privateKind, ite_true] using select_path rip loaded kindRead
  have branch := private_branch (initial := selected) rfl loaded threadRead
  change run Atomic9.step (3 + 2) initial = _
  rw [run_add, picks]
  exact branch

theorem private_threaded_exchange {initial : MState} {kind : BitVec 32}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (clearLoaded : Loaded initial.memory 0xa1ba0 clearBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (privateKind : kind &&& 128#32 = 0)
    (threadRead : loadN initial.memory 0x20c040 1 = some 0#64) :
    ∃ final, run Atomic9.step 6 initial = some final ∧ final.core.rip = 0xa1ba2 ∧
      final.core.read .rax = 0#64 ∧ final.core.read .rdi = initial.core.read .rdi ∧
      final.memory = initial.memory := by
  let selected : MState := ⟨threadResult (maskCore initial.core kind) 0#8, initial.memory⟩
  let final : MState := ⟨clearCore selected.core, selected.memory⟩
  have picks : run Atomic9.step 5 initial = some selected :=
    private_select rip loaded kindRead privateKind threadRead
  have clear : Atomic9.step selected = some final := clear_to_exchange rfl clearLoaded
  refine ⟨final, ?_, rfl, rfl, rfl, rfl⟩
  change run Atomic9.step (5 + 1) initial = some final
  rw [run_add, picks]
  change run Atomic9.step 1 selected = some final
  rw [run_succ, clear]
  rfl

theorem private_single_thread_fallthrough {initial : MState} {kind : BitVec 32} {value : Byte}
    (rip : initial.core.rip = 0xa1b7a)
    (loaded : Loaded initial.memory 0xa1b7a selectBytes)
    (kindRead : loadN initial.memory (initial.core.read .rdi + 16#64) 4 =
      some (kind.setWidth 64))
    (privateKind : kind &&& 128#32 = 0)
    (threadRead : loadN initial.memory 0x20c040 1 = some (value.setWidth 64))
    (singleThread : value ≠ 0) :
    ∃ final, run Atomic9.step 5 initial = some final ∧ final.core.rip = 0xa1b8e ∧
      final.memory = initial.memory := by
  refine ⟨⟨threadResult (maskCore initial.core kind) value, initial.memory⟩,
    private_select rip loaded kindRead privateKind threadRead, ?_, rfl⟩
  simp only [threadResult, ite_eq_right singleThread]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockExchangePath
