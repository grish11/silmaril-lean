module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Ext.Lemmas

@[expose] public section
namespace Silmaril.Proofs.Machine.Region.X86.SqliteStrLength.Clang

open Silmaril.Machine.Region.X86.SqliteStrLength
  (pointer field zeroExtendLength entryStore model ReturnSlot DataReady Register Operation)
open Silmaril.Machine.Region.X86.SqliteStrLength.Clang
open Silmaril.X86
open Silmaril.Process (Memory)
open Silmaril.SSA.LambdaRTL
open Silmaril.Machine.Execution (run)

private inductive Arm where
  | readLength | zero
  deriving DecidableEq

private def arm (entry : MState) : Arm := if pointer entry = 0 then .zero else .readLength

private def branchOffset : Arm → Word
  | .readLength => 5
  | .zero => 9

private def retOffset : Arm → Word
  | .readLength => 8
  | .zero => 11

private def branchLabel : Arm → Label
  | .readLength => .load
  | .zero => .zero

private def returnLabel : Arm → Label
  | .readLength => .returnLoaded
  | .zero => .returnZero

private def afterTest (entry : MState) : MState :=
  ⟨{ entry.core with rip := entry.core.rip + 3, flags := Ext.logicFlagsN (pointer entry) },
    entry.memory⟩

private def afterBranch (entry : MState) : MState :=
  ⟨{ (afterTest entry).core with rip := entry.core.rip + branchOffset (arm entry) },
    entry.memory⟩

private def afterRead (entry : MState) (value : Word) : MState :=
  ⟨{ (afterBranch entry).core.write .rax (zeroExtendLength value) with
      rip := entry.core.rip + 8 }, entry.memory⟩

private def afterZero (entry : MState) : MState :=
  ⟨{ (afterBranch entry).core.write .rax 0 with
      rip := entry.core.rip + 11
      flags := Ext.logicFlagsN (0 : BitVec 32) }, entry.memory⟩

private theorem stepTest {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    Open.step entry = some (afterTest entry) := by
  refine Open.step_of_listed (o := 0) (l := 3) (i := .base (.test .q (.reg .rdi) .rdi))
    loaded (by simp) (by decide) (by decide +kernel) ?_
  change Ext.exec (.test .q (.reg .rdi) .rdi) entry.core entry.memory = _
  rw [Ext.exec_test_reg, BitVec.and_self, Ext.Sz.read_q]
  rfl

private theorem stepBranch {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    Open.step (afterTest entry) = some (afterBranch entry) := by
  refine Open.step_of_listed (o := 3) (l := 2) (i := .base (.jcc8 .e 4))
    loaded rfl (by decide) (by decide +kernel) ?_
  change Ext.exec (.jcc8 .e 4) (afterTest entry).core entry.memory = _
  have flags : Ext.Cond.e.eval (afterTest entry).core.flags = some (decide (pointer entry = 0#64)) := rfl
  rw [Ext.exec_jcc8 _ _ .e 4 _ flags]
  have length : (Ext.Instr.jcc8 .e 4).length = 2 := by decide
  rw [length]
  by_cases zero : pointer entry = 0#64 <;>
    simp [afterTest, arm, branchOffset, zero, BitVec.add_assoc]

private theorem stepRead {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (nonnull : pointer entry ≠ 0#64) {value : Word} (read : field entry.memory (pointer entry) = some value) :
    Open.step (afterBranch entry) = some (afterRead entry value) := by
  let operand := Ext.Mem.ofReg .rdi none 24
  refine Open.step_of_listed (o := 5) (l := 3) (i := .base (.load .d .rax operand))
    loaded (by simp [afterBranch, arm, branchOffset, nonnull]) (by decide) (by decide +kernel) ?_
  change Ext.exec (.load .d .rax operand) (afterBranch entry).core entry.memory = _
  rw [Ext.exec_load]
  have length : (Ext.Instr.load .d .rax operand).length = 3 := by decide
  have address (next : Word) : operand.addr (afterBranch entry).core next = pointer entry + 24 := by
    simp [operand, Ext.Mem.addr, Ext.Mem.ofReg, afterBranch, afterTest, pointer]
  rw [length, address]
  change (match field entry.memory (pointer entry) with
    | some word => Ext.Result.ok _ _
    | none => Ext.Result.dataFault) = _
  rw [read]
  simp [afterBranch, arm, branchOffset, nonnull, Ext.Sz.write, zeroExtendLength, BitVec.add_assoc]

private theorem stepZero {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (null : pointer entry = 0#64) :
    Open.step (afterBranch entry) = some (afterZero entry) := by
  refine Open.step_of_listed (o := 9) (l := 2) (i := .base (.alu .d .xor (.reg .rax) .rax))
    loaded (by simp [afterBranch, arm, branchOffset, null]) (by decide) (by decide +kernel) ?_
  change Ext.exec (.alu .d .xor (.reg .rax) .rax) (afterBranch entry).core entry.memory = _
  rw [Ext.exec_alu_reg _ _ _ _ _ _ (by decide)]
  simp only [Ext.AluOp.flagsN, Ext.AluOp.resultN, BitVec.xor_self]
  have length : (Ext.Instr.alu .d .xor (.reg .rax) .rax).length = 2 := by decide
  simp [Ext.Sz.write, afterBranch, arm, branchOffset, null, length, BitVec.add_assoc]

private theorem notReturned {entry current : MState}
    (stack : current.core.read .rsp = entry.core.read .rsp) :
    ¬ FnContract.Returned Open.isa entry current := by
  intro returned
  have impossible : (0 : Word) = 8 := by
    simpa using congrArg (fun sp => sp - entry.core.read .rsp) (stack.symm.trans returned.2)
  contradiction

private theorem returnEffect {entry preRet : MState} (readable : ReturnSlot entry)
    (stack : preRet.core.read .rsp = entry.core.read .rsp) (mem : preRet.memory = entry.memory) :
    let returnPC := FnContract.retOf entry.core entry.memory
    let final : MState :=
      ⟨{ preRet.core.write .rsp (entry.core.read .rsp + 8) with rip := returnPC }, entry.memory⟩
    Ext.exec .ret preRet.core preRet.memory = .ok final.core final.memory := by
  have read : preRet.memory.readBytes (preRet.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [FnContract.retOf entry.core entry.memory]) := by
    rw [stack, mem]
    exact readable
  rw [Ext.exec_ret]
  simp only [Insn.exec, popWord_of_readBytes read]
  rw [stack, mem]
  rfl

private def Trace (entry final : MState) : Prop :=
  ∃ branch preRet,
    run Open.step 2 entry = some branch ∧
    branch.core.rip = entry.core.rip + branchOffset (arm entry) ∧
    branch.core.read .rdi = pointer entry ∧ branch.memory = entry.memory ∧
    Open.step branch = some preRet ∧
    preRet.core.rip = entry.core.rip + retOffset (arm entry) ∧ Open.step preRet = some final ∧
    final.core.read .rax = preRet.core.read .rax ∧ final.memory = entry.memory

private theorem firstReturn_trace {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (readable : ReturnSlot entry) (data : DataReady entry) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧ Trace entry final ∧
      some (final.core.read .rax) =
        (if pointer entry = 0 then some 0 else (field entry.memory (pointer entry)).map zeroExtendLength) := by
  let branch := afterBranch entry
  have prefixRun : run Open.step 2 entry = some branch := by simp [run, branch, stepTest loaded, stepBranch loaded]
  have branchStack : branch.core.read .rsp = entry.core.read .rsp := rfl
  have branchPtr : branch.core.read .rdi = pointer entry := rfl
  have notTested : ¬ FnContract.Returned Open.isa entry (afterTest entry) := notReturned rfl
  have prepend {preRet final : MState} (stepArm : Open.step branch = some preRet)
      (stepRet : Open.step preRet = some final) (stack : preRet.core.read .rsp = entry.core.read .rsp)
      (returned : FnContract.Returned Open.isa entry final) :
      FnContract.FirstReturn Open.isa entry final :=
    ⟨.step (notReturned rfl) (stepTest loaded) (.step notTested (stepBranch loaded)
      (.step (notReturned branchStack) stepArm (.step (notReturned stack) stepRet (.refl _)))), returned⟩
  let returnPC := FnContract.retOf entry.core entry.memory
  by_cases null : pointer entry = 0#64
  · let preRet := afterZero entry
    let final : MState := ⟨{ preRet.core.write .rsp (entry.core.read .rsp + 8) with rip := returnPC }, entry.memory⟩
    have stack : preRet.core.read .rsp = entry.core.read .rsp := by simp [preRet, afterZero, afterBranch, afterTest]
    have stepRet : Open.step preRet = some final :=
      Open.step_of_listed (o := 11) (l := 1) (i := .base .ret) loaded rfl (by decide) (by decide +kernel)
        (returnEffect readable stack rfl)
    have stepArm : Open.step branch = some preRet := stepZero loaded null
    refine ⟨final, prepend stepArm stepRet stack ⟨rfl, by simp [final]⟩,
      ⟨branch, preRet, prefixRun, rfl, branchPtr, rfl, stepArm, ?_, stepRet, by simp [final], rfl⟩, ?_⟩
    · simp [preRet, afterZero, arm, null, retOffset]
    · simp [final, preRet, afterZero, null]
  · obtain ⟨value, read⟩ := data null
    let preRet := afterRead entry value
    let final : MState := ⟨{ preRet.core.write .rsp (entry.core.read .rsp + 8) with rip := returnPC }, entry.memory⟩
    have stack : preRet.core.read .rsp = entry.core.read .rsp := by simp [preRet, afterRead, afterBranch, afterTest]
    have stepRet : Open.step preRet = some final :=
      Open.step_of_listed (o := 8) (l := 1) (i := .base .ret) loaded rfl (by decide) (by decide +kernel)
        (returnEffect readable stack rfl)
    have stepArm : Open.step branch = some preRet := stepRead loaded null read
    refine ⟨final, prepend stepArm stepRet stack ⟨rfl, by simp [final]⟩,
      ⟨branch, preRet, prefixRun, rfl, branchPtr, rfl, stepArm, ?_, stepRet, by simp [final], rfl⟩, ?_⟩
    · simp [preRet, afterRead, arm, null, retOffset]
    · simp [final, preRet, afterRead, null, read]

private theorem graph_selects (entry : MState) :
    graph.entry.exec (model entry.memory) (fun k _ _ => some k) (entryStore entry) =
      some (branchLabel (arm entry)) := by
  by_cases null : pointer entry = 0#64 <;>
    simp [graph, CFG.Body.exec, CFG.Term.exec, model, Op.eval, Val.eval, entryStore,
      arm, branchLabel, null]

private theorem graph_matches (entry : MState) :
    (obs <$> graph.run (model entry.memory) (entryStore entry)) =
      (fun v => (returnLabel (arm entry), v)) <$>
        (if pointer entry = 0 then some 0 else (field entry.memory (pointer entry)).map zeroExtendLength) := by
  by_cases null : pointer entry = 0#64
  · simp [CFG.run, graph, CFG.Body.exec, CFG.Term.exec, CFG.jump, model, Op.eval, Val.eval,
      entryStore, upd, obs, arm, returnLabel, null]
  · cases read : field entry.memory (pointer entry) <;>
      simp [CFG.run, graph, CFG.Body.exec, CFG.Term.exec, CFG.jump, model, Op.eval, Val.eval,
        entryStore, upd, obs, arm, returnLabel, null, read]

theorem bridge_exists {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (readable : ReturnSlot entry) (data : DataReady entry) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final := by
  obtain ⟨final, first, ⟨branch, preRet, prefixRun, branchPC, pointer, beforeMem, stepArm, preRetPC,
      stepRet, _, afterMem⟩, value⟩ := firstReturn_trace loaded readable data
  have branchOffset_eq : branchOffset (arm entry) = offset (branchLabel (arm entry)) := by
    cases arm entry <;> rfl
  have retOffset_eq : retOffset (arm entry) = offset (returnLabel (arm entry)) := by
    cases arm entry <;> rfl
  refine ⟨final, first, branchLabel (arm entry), returnLabel (arm entry), branch, preRet, graph_selects entry,
    prefixRun, branchPC.trans (congrArg (entry.core.rip + ·) branchOffset_eq), pointer, beforeMem, stepArm,
    preRetPC.trans (congrArg (entry.core.rip + ·) retOffset_eq), stepRet, ?_, afterMem⟩
  rw [graph_matches, ← value]
  rfl

theorem bridge_of_firstReturn {entry final : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (readable : ReturnSlot entry) (data : DataReady entry) (actual : FnContract.FirstReturn Open.isa entry final) :
    Bridge entry final := by
  obtain ⟨witness, first, trace⟩ := bridge_exists loaded readable data
  exact (FnContract.firstReturn_unique first actual) ▸ trace

private def stackBytes : List Byte := Silmaril.Machine.LittleEndian.encodeWords [0x9000]
private def lengthBytes : List Byte := [0x21, 0x43, 0x65, 0x87]

private def stackBacking : Silmaril.Process.ByteMemory := Memory.install ∅ 0x8008 stackBytes
private def fieldBytes (hasField : Bool) : List Byte := if hasField then lengthBytes else []

private def fieldBacking (hasField : Bool) : Silmaril.Process.ByteMemory :=
  Memory.install stackBacking 0x4018 (fieldBytes hasField)

private def fixtureMemory (hasField : Bool) : Silmaril.Process.Memory :=
  ⟨[⟨0x12e70, code.length, ⟨false, false, true⟩⟩, ⟨0x8008, 8, ⟨true, false, false⟩⟩] ++
      (if hasField then [⟨0x4018, 4, ⟨true, false, false⟩⟩] else []),
    Memory.install (fieldBacking hasField) 0x12e70 code⟩

private def fixture (argument : Word) (hasField : Bool) : MState :=
  ⟨{ regs := fun r => if r = .rsp then 0x8008 else if r = .rdi then argument else 0xdeadbeeffeed0000,
     rip := 0x12e70, flags := ⟨none, none, none, none, none, none⟩ }, fixtureMemory hasField⟩

private theorem fixture_code (argument : Word) (hasField : Bool) :
    Ext.Loaded (fixture argument hasField).memory (fixture argument hasField).core.rip code := by
  have permitted : (fixtureMemory hasField).Permitted .execute 0x12e70 code.length := by
    cases hasField <;> decide
  exact Memory.readWith_eq _ _ _ _ permitted (fun i hi => Memory.install_get _ _ _ i hi)

private theorem fixture_stack (hasField : Bool) :
    (fixtureMemory hasField).readBytes 0x8008 8 = some stackBytes := by
  have permitted : (fixtureMemory hasField).Permitted .read 0x8008 stackBytes.length := by
    cases hasField <;> decide
  change (fixtureMemory hasField).readWith .read 0x8008 stackBytes.length = some stackBytes
  refine Memory.readWith_eq _ _ _ _ permitted (fun i hi => ?_)
  have upper : i < 8 := hi
  have below : 0x8008 + i < 0x12e70 := by omega
  have above : 0x4018 + (fieldBytes hasField).length ≤ 0x8008 + i := by
    cases hasField <;> simp [fieldBytes, lengthBytes] <;> omega
  change (Memory.install (fieldBacking hasField) 0x12e70 code).get? (0x8008 + i) = _
  rw [Memory.install_outside _ _ _ _ (.inl below)]
  change (Memory.install stackBacking 0x4018 (fieldBytes hasField)).get? (0x8008 + i) = _
  rw [Memory.install_outside _ _ _ _ (.inr above)]
  exact Memory.install_get _ _ _ _ hi

private theorem fixture_saved (argument : Word) (hasField : Bool) : ReturnSlot (fixture argument hasField) := by
  have ret : FnContract.retOf (fixture argument hasField).core (fixtureMemory hasField) = 0x9000 := by
    change (((fixtureMemory hasField).readBytes 0x8008 8).bind wordOfBytes?).getD 0 = 0x9000
    rw [fixture_stack]
    rfl
  change (fixtureMemory hasField).readBytes 0x8008 8 = some (Silmaril.Machine.LittleEndian.encodeWords
    [FnContract.retOf (fixture argument hasField).core (fixtureMemory hasField)])
  rw [ret]
  exact fixture_stack hasField

private theorem fixture_length :
    field (fixture 0x4000#64 true).memory (pointer (fixture 0x4000#64 true)) = some 0x87654321 := by
  have read : (fixtureMemory true).readBytes 0x4018 4 = some lengthBytes := by
    change (fixtureMemory true).readWith .read 0x4018 lengthBytes.length = some lengthBytes
    refine Memory.readWith_eq _ _ _ _ (by decide) (fun i hi => ?_)
    have upper : i < 4 := hi
    have below : 0x4018 + i < 0x12e70 := by omega
    change (Memory.install (fieldBacking true) 0x12e70 code).get? (0x4018 + i) = _
    rw [Memory.install_outside _ _ _ _ (.inl below)]
    exact Memory.install_get _ _ _ _ hi
  change ((fixtureMemory true).readBytes 0x4018 4).map
    (fun bs => BitVec.ofNat 64 (Ext.leValue bs)) = _
  rw [read]
  rfl

private theorem fixture_null_field : field (fixture 0#64 false).memory 0 = none := by
  have denied : (fixtureMemory false).checkSpan .read 0x18 4 = false := by decide
  change ((fixtureMemory false).readBytes 0x18 4).map
    (fun bs => BitVec.ofNat 64 (Ext.leValue bs)) = none
  simp [Memory.readBytes, Memory.readWith, denied]

private theorem null_witness :
    ∃ final, field (fixture 0#64 false).memory 0 = none ∧
      FnContract.FirstReturn Open.isa (fixture 0#64 false) final ∧ Bridge (fixture 0#64 false) final ∧
      (obs <$> graph.run (model (fixture 0#64 false).memory) (entryStore (fixture 0#64 false))) =
        some (.returnZero, 0) ∧ final.core.read .rax = 0 := by
  have null : pointer (fixture 0#64 false) = 0#64 := rfl
  have data : DataReady (fixture 0#64 false) := fun nonnull => (nonnull null).elim
  obtain ⟨final, first, matched⟩ := bridge_exists (fixture_code 0 false) (fixture_saved 0 false) data
  have graphResult : (obs <$> graph.run (model (fixture 0#64 false).memory) (entryStore (fixture 0#64 false))) =
      some (.returnZero, 0) := by
    rw [graph_matches]
    simp [arm, returnLabel, null]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, observed, _⟩ := matched
  refine ⟨final, fixture_null_field, first, matched, graphResult, ?_⟩
  exact (congrArg Prod.snd (Option.some.inj (graphResult.symm.trans observed))).symm

private theorem bounded_witness :
    ∃ final, (pointer (fixture 0x4000#64 true)).toNat + 28 ≤ Silmaril.Process.addressLimit ∧
      FnContract.FirstReturn Open.isa (fixture 0x4000#64 true) final ∧ Bridge (fixture 0x4000#64 true) final ∧
      (obs <$> graph.run (model (fixture 0x4000#64 true).memory) (entryStore (fixture 0x4000#64 true))) =
        some (.returnLoaded, 0x87654321) ∧ final.core.read .rax = 0x87654321 := by
  have nonnull : pointer (fixture 0x4000#64 true) ≠ 0#64 := by decide
  have data : DataReady (fixture 0x4000#64 true) := fun _ => ⟨_, fixture_length⟩
  obtain ⟨final, first, matched⟩ := bridge_exists (fixture_code 0x4000 true) (fixture_saved 0x4000 true) data
  have graphResult : (obs <$> graph.run (model (fixture 0x4000#64 true).memory) (entryStore (fixture 0x4000#64 true))) =
      some (.returnLoaded, 0x87654321) := by
    rw [graph_matches]
    simp [arm, returnLabel, nonnull, fixture_length, zeroExtendLength]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, observed, _⟩ := matched
  refine ⟨final, by decide, first, matched, graphResult, ?_⟩
  exact (congrArg Prod.snd (Option.some.inj (graphResult.symm.trans observed))).symm

theorem viewed_run (entry : MState) :
    (fun out => (exitView out.1, out.2)) <$> graph.run (model entry.memory) (entryStore entry) =
      Silmaril.Machine.Region.X86.SqliteStrLength.graph.run (model entry.memory) (entryStore entry) := by
  by_cases null : pointer entry = 0#64
  · simp [CFG.run, graph, Silmaril.Machine.Region.X86.SqliteStrLength.graph, CFG.Body.exec, CFG.Term.exec, CFG.jump, model,
      Op.eval, Val.eval, entryStore, upd, exitView, null]
    funext register
    cases register <;> simp [upd, entryStore, null]
  · cases read : field entry.memory (pointer entry) <;>
      simp [CFG.run, graph, Silmaril.Machine.Region.X86.SqliteStrLength.graph, CFG.Body.exec, CFG.Term.exec, CFG.jump, model,
        Op.eval, Val.eval, entryStore, upd, exitView, null, read]
    funext register
    cases register <;> simp [upd]

end Silmaril.Proofs.Machine.Region.X86.SqliteStrLength.Clang
