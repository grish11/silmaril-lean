module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.Loops.IndexedHost.Examples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Examples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IfExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.BranchExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.FunctionBranchExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.BranchTableExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.SuffixLoopExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IndirectExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.GrowthExamples
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution (Admin Config Step Steps Store expression values)

private abbrev i32 := Value.int .i32
private def bytes (first : UInt8) : ByteArray := ⟨#[0xAA, 0xBB, 0xCC, first, 0, 0, 0, 0xDD]⟩
private def memory : MemInst := ⟨bytes 0x99, some 2⟩
private def sentinel : MemInst := ⟨⟨#[7, 8]⟩, none⟩
private def slot : MemAddr := ⟨1⟩
private def address : FuncAddr := ⟨0⟩
private def resultType : Option NumType := some (.int .i32)

private def region : List Op :=
  [.ranked (.numeric (.get ⟨1⟩)), .ranked (.numeric (.get ⟨0⟩)), .store 2,
    .ranked (.numeric (.get ⟨0⟩)), .ranked (.numeric (.get ⟨2⟩)), .ranked (.set ⟨0⟩),
    .ranked (.brIf ⟨0⟩ []), .ranked (.numeric (.get ⟨1⟩)), .load 2]

private def fn : Function :=
  ⟨⟨{ memories := [slot] }, ⟨0⟩, [.int .i32, .int .i32, .int .i32], [], [.int .i32]⟩,
    0, [i32 4], [.loop resultType region, .ranked (.numeric (.bin .i32 .sub))]⟩

private def program : Program := { functions := [some fn] }
private def base : Store Unit :=
  { memories := [sentinel, memory], funcs := [.wasm fn.declaration.type fn.declaration.module fn.v1Func] }
private theorem checked : program.checkV1 slot = true := rfl
private theorem layout : Layout program base slot memory where
  memory := rfl
  functions := by
    intro a target found
    rcases a with ⟨_ | n⟩ <;> simp [Program.lookup, program] at found
    subst target
    rfl

-- A scalar fallthrough result does not give the backedge an input.
example : Function.checkV1 { fn with
    code := [.loop resultType [.ranked (.numeric (.get ⟨0⟩)), .ranked (.br ⟨0⟩ [.int .i32])],
      .ranked (.numeric (.bin .i32 .sub))] } slot = false := rfl

example : Function.checkV1 { fn with
    code := [.loop resultType [.ranked (.numeric (.get ⟨1⟩)), .ranked (.numeric (.get ⟨0⟩)),
      .ranked (.brIf ⟨0⟩ [.int .i32])], .ranked (.numeric (.bin .i32 .sub))] } slot = false := rfl

example : Function.checkV1 { fn with
    code := [.loop resultType [], .ranked (.numeric (.bin .i32 .sub))] } slot = false := rfl

example : Function.checkV1 { fn with
    code := [.loop resultType [.ranked (.br ⟨0⟩ [])], .ranked (.numeric (.bin .i32 .sub))] } slot = true := rfl

private def flagBits (flag : Bool) : BitVec 32 := if flag then 1 else 0
private def flagByte (flag : Bool) : UInt8 := if flag then 1 else 0
private def args (flag : Bool) := [i32 (flagBits flag), i32 1, i32 0]
private def active (flag : Bool) := fn.declaration.frame (args flag)
private def caller : Frame := ⟨[i32 88], { funcs := [address] }⟩
private def input : State := ⟨memory.data, caller, values (args true) ++ [.source (.call ⟨0⟩)]⟩
private def live (first : UInt8) : Store Unit := storeWithBytes base slot memory (bytes first)
private def loop : Wasm.V1.Instr := .loop resultType (v1Code region)
private def suffix : List Admin := [.source (.intBinOp .i32 .sub)]
private def loadCode : List Admin := [.source (.localGet ⟨1⟩), .source ((Op.load 2).v1)]
private def selectCode : List Admin := [.source (.brIf ⟨0⟩)] ++ loadCode

private def underFunction (c : Config Unit) : Config Unit :=
  ⟨c.store, caller, [.frame 1 c.frame [.label 1 [] (values [i32 4] ++ c.code ++ suffix)]]⟩
private def underLoop (c : Config Unit) : Config Unit :=
  underFunction ⟨c.store, c.frame, [.label 0 [loop] c.code]⟩

private theorem functionStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (underFunction ⟨s, f, a⟩) (underFunction ⟨s', f', b⟩) :=
  .frame (.label (.context move [i32 4] suffix) 1 []) 1 caller

private theorem loopStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (underLoop ⟨s, f, a⟩) (underLoop ⟨s', f', b⟩) :=
  functionStep (.label move 0 [loop])

private def entered (first : UInt8) (flag : Bool) : Config Unit :=
  underLoop ⟨live first, active flag, expression (v1Code region)⟩

private theorem enterRoot :
    Steps CallFrame.v1NoHost ⟨base, caller, input.code⟩ (entered 0x99 true) := by
  apply Relation.ReflTransGen.head
    (b := ⟨base, caller, values (args true) ++ [.invoke address]⟩)
    (Step.context (.call _ _ ⟨0⟩ address rfl) (args true) [])
  refine Relation.ReflTransGen.head
    (layout.enter checked (address := address) (fn := fn) rfl layout.initial_shared
      (saved := []) (args := args true) (tail := []) rfl) ?_
  exact .single (functionStep (.pure _ _ (.loop resultType (v1Code region))))

private def afterWrite : List Admin :=
  [.source (.localGet ⟨0⟩), .source (.localGet ⟨2⟩), .source (.localSet ⟨0⟩)] ++ selectCode

private theorem writeFlag (old : UInt8) (flag : Bool) :
    Step CallFrame.v1NoHost
      ⟨live old, active flag, values [i32 1, i32 (flagBits flag)] ++ [.source ((Op.store 2).v1)] ++ afterWrite⟩
      ⟨live (flagByte flag), active flag, afterWrite⟩ := by
  cases flag <;>
    exact (MemoryWrite.v1_context_store_step_iff_at
      (immediate := immediate 2) (saved := []) (tail := afterWrite)
      (show Wasm.V1.Execution.frameMemory (live old) _ = some (slot, { memory with data := bytes old }) from rfl)).mpr
      ⟨.written _, MemoryWrite.fact_at (.write _ _ _ rfl), rfl⟩

private def atBranch (flag : Bool) : Config Unit :=
  underLoop ⟨live (flagByte flag), active false, values [i32 (flagBits flag)] ++ selectCode⟩

private theorem iteration (old : UInt8) (flag : Bool) :
    Steps CallFrame.v1NoHost (entered old flag) (atBranch flag) := by
  have start : Steps CallFrame.v1NoHost (entered old flag) (entered old flag) := .refl
  have pointer := start.tail (loopStep (.context (.localGet _ _ ⟨1⟩ (i32 1) rfl) []
    ([.source (.localGet ⟨0⟩), .source ((Op.store 2).v1)] ++ afterWrite)))
  have word := pointer.tail (loopStep (.context (.localGet _ _ ⟨0⟩ (i32 (flagBits flag)) rfl)
    [i32 1] ([.source ((Op.store 2).v1)] ++ afterWrite)))
  have written := word.tail (loopStep (writeFlag old flag))
  have prior := written.tail (loopStep (.context (.localGet _ _ ⟨0⟩ (i32 (flagBits flag)) rfl) []
    ([.source (.localGet ⟨2⟩), .source (.localSet ⟨0⟩)] ++ selectCode)))
  have zero := prior.tail (loopStep (.context (.localGet _ _ ⟨2⟩ (i32 0) rfl)
    [i32 (flagBits flag)] ([.source (.localSet ⟨0⟩)] ++ selectCode)))
  exact zero.tail (loopStep (.context (.localSet _ _ ⟨0⟩ (i32 0) (i32 (flagBits flag)) rfl)
    [i32 (flagBits flag)] selectCode))

private def selected : Config Unit :=
  underLoop ⟨live 1, active false, [.source (.br ⟨0⟩)] ++ loadCode⟩
private def pending : Config Unit :=
  underFunction ⟨live 1, active false, [.source loop]⟩

private theorem select : Step CallFrame.v1NoHost (atBranch true) selected :=
  loopStep (.context (.pure _ _ (.brIfNonzero ⟨0⟩ 1 (by decide))) [] loadCode)

private theorem restart : Step CallFrame.v1NoHost selected pending ∧
    Step CallFrame.v1NoHost pending (entered 1 false) := by
  have moves := v1_loop_restart (s := live 1) (f := active false) (result := resultType)
    (body := v1Code region) (saved := [i32 4]) (scratch := []) (branchTail := loadCode) (tail := suffix)
  exact ⟨.frame (.label moves.1 1 []) 1 caller, .frame (.label moves.2 1 []) 1 caller⟩

private theorem readback {dst : Config Unit} (path : Steps CallFrame.v1NoHost ⟨base, caller, input.code⟩ dst) :
    ∃ out, Runs program slot input out ∧ Ready program slot 1 memory.data.size out ∧
      dst = render base slot memory out :=
  (v1_call_run_iff (root := address) (fn := fn) (index := ⟨0⟩) (args := args true) (caller := caller)
    checked layout rfl rfl).mp path

-- The first iteration writes 1 and clears its flag. A finite prefix records
-- both the pending loop instruction and the re-entered label with those bytes.
example : ∃ taken restartPending reentered,
    Runs program slot input taken ∧ Edge program slot taken restartPending ∧
    Edge program slot restartPending reentered ∧ selected = render base slot memory taken ∧
    pending = render base slot memory restartPending ∧ entered 1 false = render base slot memory reentered := by
  obtain ⟨taken, trace, ready, eq⟩ := readback ((enterRoot.trans (iteration 0x99 true)).tail select)
  obtain ⟨restartPending, leave, nextReady, midEq⟩ := (v1_step_iff checked layout ready).mp (eq ▸ restart.1)
  obtain ⟨reentered, reenter, _, endEq⟩ := (v1_step_iff checked layout nextReady).mp (midEq ▸ restart.2)
  exact ⟨taken, restartPending, reentered, trace, leave, reenter, eq, midEq, endEq⟩

-- The second iteration writes zero and the untaken branch continues to the
-- load. Its scalar result is delivered above 4 via loop fallthrough.
example : ∃ out, Runs program slot input out ∧
    (⟨live 0, caller, values [i32 4]⟩ : Config Unit) = render base slot memory out := by
  have first := ((enterRoot.trans (iteration 0x99 true)).tail select).tail restart.1
  have second := (first.tail restart.2).trans (iteration 1 false)
  have zero := second.tail (loopStep (.context (.pure _ _ (.brIfZero ⟨0⟩)) [] loadCode))
  have pointer := zero.tail (loopStep (.context (.localGet _ _ ⟨1⟩ (i32 1) rfl) [] [.source ((Op.load 2).v1)]))
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2)
    (address := 1) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (live 0) (active false) = some (slot, { memory with data := bytes 0 }) from rfl)).mpr
    ⟨.value 0, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  have left := (pointer.tail (loopStep load)).tail (functionStep (.pure _ _ (.labelDone 0 [loop] [i32 0])))
  have sub := left.tail
    (Step.frame (Step.label (.pure _ _ (.intBinary .i32 .sub 4 0 4 rfl)) 1 []) 1 caller)
  have done := (sub.tail (.frame (.pure _ _ (.labelDone 1 [] [i32 4])) 1 caller)).tail
    (.pure _ _ (.frameDone 1 (active false) [i32 4] rfl))
  obtain ⟨out, trace, _, eq⟩ := readback done
  exact ⟨out, trace, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
