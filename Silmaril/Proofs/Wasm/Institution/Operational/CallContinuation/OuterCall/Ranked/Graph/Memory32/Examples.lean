module

import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.GrowthExamples
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.LoopExamples
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RecursiveExamples
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.TableExamples
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.V1.Execution.Properties
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution (Config Step Steps Store values)

private abbrev i32 := Value.int .i32
private def before : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 0, 0, 0, 0, 0xdd]⟩
private def after : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 0x44, 0x33, 0x22, 0x11, 0xdd]⟩
private def memory : MemInst := ⟨before, some 2⟩
private def untouched : MemInst := ⟨⟨#[3, 4]⟩, none⟩
private def slot : MemAddr := ⟨1⟩
private def childAddr : FuncAddr := ⟨0⟩
private def parentAddr : FuncAddr := ⟨1⟩

private def declaration (targets : List FuncAddr) (results : List NumType) : Declaration :=
  ⟨{ funcs := targets, memories := [slot] }, ⟨0⟩, [], [], results⟩

private def writer (traps : Bool) : Function :=
  ⟨declaration [] [], 0,
    (if traps then [i32 3, i32 0] else []) ++ [i32 1, i32 0x11223344],
    if traps then [.store 2, .store 2] else [.store 2]⟩
private def target (traps : Bool) : CallTarget := ⟨⟨0⟩, childAddr, (writer traps).declaration⟩
private def reader (traps : Bool) : Function :=
  ⟨{ declaration [childAddr] [.int .i32] with params := [.int .i64] }, 1, [i32 2], [.ranked (.call (target traps)), .load 1]⟩
private def program (traps : Bool) : Program := ⟨[some (writer traps), some (reader traps)]⟩

private theorem checked (traps : Bool) : (program traps).checkV1 slot = true := by cases traps <;> rfl

example : (program false).checkV1 ⟨0⟩ = false := rfl

example : (Program.mk [some (writer false), some { reader false with rank := 0 }]).checkV1 slot = false :=
  rfl

example : ({ writer false with initial := [Value.int .i64 1, i32 0] } : Function).checkV1 slot = false :=
  rfl

example : Function.checkV1 { writer false with code := [.ranked .unreachable, .ranked (.block none [])] }
    slot = false := rfl

example : Function.checkV1 { reader false with declaration := declaration [childAddr] [.int .i32, .int .i32] }
    slot = false := rfl

example : Function.checkV1 { reader false with initial := [Value.int .i64 2] } slot = false := rfl

private theorem resolves (traps : Bool) : (reader traps).declaration.module.funcs[0]? = some childAddr :=
  (Program.linked_target (checked traps) (address := parentAddr) (fn := reader traps) rfl (target := target traps)
    (by simp [reader, Function.targets, Op.targets, Graph.Op.targets])).choose_spec.2.1

private def base (traps : Bool) : Store Unit :=
  { memories := [untouched, memory], funcs := [writer traps, reader traps].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }

private theorem layout (traps : Bool) : Layout (program traps) (base traps) slot memory where
  memory := rfl
  functions := by
    intro a fn found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, program] at found
    all_goals subst fn; rfl

example : ¬ Layout (program false) { base false with memories := [] } slot memory := by
  intro missing
  cases missing.memory

private def caller (traps : Bool) : Frame :=
  Graph.currentFrame (reader traps).declaration [Value.int .i64 9]
private def callee (traps : Bool) : Frame := (writer traps).declaration.frame []
private def saved := [i32 2]
private def continuation : List Wasm.V1.Execution.Admin := [.source ((Op.load 1).v1)]
private def written (traps : Bool) := storeWithBytes (base traps) slot memory after
private def updated : MemInst := { memory with data := after }

private def armed (traps : Bool) : Config Unit :=
  ⟨base traps, caller traps, MemoryWrite.v1ActivationCode none (callee traps) saved continuation
    (Wasm.V1.Execution.expression (writer traps).v1Func.body)⟩
private def pending (traps : Bool) : Config Unit :=
  ⟨base traps, caller traps, values saved ++ .invoke childAddr :: continuation⟩

private def calling (traps : Bool) : Config Unit :=
  ⟨base traps, caller traps, values saved ++ .source (.call ⟨0⟩) :: continuation⟩

private theorem resolve (traps : Bool) : Step CallFrame.v1NoHost (calling traps) (pending traps) :=
  .context (.call _ _ ⟨0⟩ childAddr (resolves traps)) saved continuation

private theorem enter (traps : Bool) : Step CallFrame.v1NoHost (pending traps) (armed traps) :=
  (layout traps).enter (checked traps) (address := childAddr) (fn := writer traps) rfl
    (layout traps).initial_shared (saved := saved) (args := []) (tail := continuation) rfl

private theorem writing : MemoryWrite.EdgeAt before 2 (.store 1 0x11223344) (.written after) :=
  MemoryWrite.fact_at (.write _ _ _ (by decide))

private theorem didWrite : Step CallFrame.v1NoHost (armed false)
    ⟨written false, caller false, MemoryWrite.v1ActivationCode none (callee false) saved continuation []⟩ :=
  (MemoryWrite.v1_activation_store_step_iff_at (immediate := immediate 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (base false) (callee false) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩

example : SharedStore (base false) slot memory (written false) :=
  ((layout false).store_activation_shared (checked false) (address := childAddr) (fn := writer false) rfl
    (layout false).initial_shared (locals := []) (saved := []) (offset := 2)
    (callerSaved := saved) (callerTail := continuation) (tail := []) (ptr := 1) (word := 0x11223344) didWrite).1

-- Return to the parent's selected memory and observe the differently offset load.
private theorem returnedWrite : Steps CallFrame.v1NoHost (calling false)
    ⟨written false, caller false, values [i32 0x11223344]⟩ := by
  apply Relation.ReflTransGen.head (resolve false)
  apply Relation.ReflTransGen.head (enter false)
  apply Relation.ReflTransGen.head didWrite
  apply Relation.ReflTransGen.head
    (b := ⟨written false, caller false, values saved ++ [.frame 0 (callee false) []] ++ continuation⟩)
    (Step.context (.frame (.pure _ _ (.labelDone 0 [] [])) 0 _) saved continuation)
  apply Relation.ReflTransGen.head
    (b := ⟨written false, caller false, values saved ++ continuation⟩)
    (Step.context (.pure _ _ (.frameDone 0 (callee false) [] rfl)) saved continuation)
  have current := (layout false).frame_memory (checked false) (address := parentAddr) (fn := reader false)
    rfl [Value.int .i64 9] after
  exact .single ((MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1) (address := 2)
    (saved := []) (tail := []) current).mpr ⟨.value 0x11223344,
      MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩)

private def laterStore : List Wasm.V1.Execution.Admin :=
  [.source (.intConst .i32 3), .source (.intConst .i32 0), .source ((Op.store 2).v1)]
private def nextWrite : Config Unit :=
  ⟨written true, caller true, MemoryWrite.v1ActivationCode none (callee true) saved continuation laterStore⟩
private def firstTrap : Config Unit :=
  ⟨written true, caller true, MemoryWrite.v1ActivationCode none (callee true) saved continuation [.trap]⟩

private theorem writesBeforeTrap : Step CallFrame.v1NoHost (armed true) nextWrite :=
  (MemoryWrite.v1_activation_store_step_iff_at (immediate := immediate 2) (saved := [i32 3, i32 0])
    (tail := [.source ((Op.store 2).v1)])
    (show Wasm.V1.Execution.frameMemory (base true) (callee true) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩

private theorem trapsLater : Step CallFrame.v1NoHost nextWrite firstTrap :=
  (MemoryWrite.v1_activation_store_step_iff_at (immediate := immediate 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (written true) (callee true) = some (slot, updated) from rfl)).mpr
    ⟨.trap, MemoryWrite.store_trap_iff_at.mpr (by decide), rfl⟩

example : SharedStore (base true) slot memory firstTrap.store :=
  ((layout true).store_activation_shared (checked true) (address := childAddr) (fn := writer true) rfl
    (SharedStore.write rfl writing) (locals := []) (callerSaved := saved) (callerTail := continuation)
    (saved := []) (tail := []) (offset := 2) (ptr := 3) (word := 0) trapsLater).1

-- The later bounds failure preserves the first write through label and frame
-- unwind, including the native step that skips the parent's pending load.
private theorem trapRun : Steps CallFrame.v1NoHost (calling true) ⟨written true, caller true, [.trap]⟩ := by
  apply Relation.ReflTransGen.head (resolve true)
  apply Relation.ReflTransGen.head (enter true)
  apply Relation.ReflTransGen.head writesBeforeTrap
  apply Relation.ReflTransGen.head trapsLater
  apply Relation.ReflTransGen.head
    (b := ⟨written true, caller true, values saved ++ [.frame 0 (callee true) [.trap]] ++ continuation⟩)
    (Step.context (.frame (.pure _ _ (.labelTrap 0 [])) 0 _) saved continuation)
  apply Relation.ReflTransGen.head
    (b := ⟨written true, caller true, values saved ++ [.trap] ++ continuation⟩)
    (Step.context (.pure _ _ (.frameTrap 0 (callee true))) saved continuation)
  exact .single (.pure _ _ (.trapValues (i32 2) [] continuation))

example : (written true).memories = [untouched, updated] ∧ (written true).funcs = (base true).funcs :=
  ⟨rfl, rfl⟩

-- The ordinary outer call enters the reader with its i64 argument. The
-- reader's call then opens the writer inside that already-live activation.
private def outside : Frame := ⟨[i32 88], { funcs := [parentAddr] }⟩
private def rootArgs := [Value.int .i64 9]
private def rootInput : State := ⟨before, outside, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private def inReader (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] c.code]]⟩

example : Step CallFrame.v1NoHost (render (base false) slot memory rootInput)
    (render (base false) slot memory ⟨before, outside, values rootArgs ++ [.invoke parentAddr]⟩) := by
  have ready := call_ready (p := program false) (m := slot) (addr := parentAddr) (fn := reader false)
    (index := ⟨0⟩) (caller := outside) rfl rfl rootArgs before
  have move : Edge (program false) slot rootInput
      ⟨before, outside, values rootArgs ++ [.invoke parentAddr]⟩ :=
    .context (.resolve (i := ⟨0⟩) rfl) rootArgs []
  exact (v1_step_iff (checked false) (layout false) ready).mpr
    ⟨_, move, move.ready (checked false) ready, rfl⟩

private theorem rootEnter (traps : Bool) : Steps CallFrame.v1NoHost
    ⟨base traps, outside, rootInput.code⟩ (inReader (calling traps)) := by
  apply Relation.ReflTransGen.head
    (b := ⟨base traps, outside, values rootArgs ++ [.invoke parentAddr]⟩)
    (Step.context (.call _ _ ⟨0⟩ parentAddr rfl) rootArgs [])
  exact .single ((layout traps).enter (checked traps) (address := parentAddr) (fn := reader traps) rfl
    (layout traps).initial_shared (saved := []) (args := rootArgs) (tail := []) rfl)

private def returned : Config Unit := ⟨written false, outside, values [i32 0x11223344]⟩
private def unwound : Config Unit := ⟨written true, outside, [.trap]⟩

private theorem rootReturns : Steps CallFrame.v1NoHost ⟨base false, outside, rootInput.code⟩ returned := by
  have body := (returnedWrite.label 1 []).frame 1 outside
  have finishLabel : Step CallFrame.v1NoHost
      (inReader ⟨written false, caller false, values [i32 0x11223344]⟩)
      ⟨written false, outside, [.frame 1 (caller false) (values [i32 0x11223344])]⟩ :=
    .frame (.pure _ _ (.labelDone 1 [] [i32 0x11223344])) 1 _
  have finishFrame : Step CallFrame.v1NoHost
      ⟨written false, outside, [.frame 1 (caller false) (values [i32 0x11223344])]⟩ returned :=
    .pure _ _ (.frameDone 1 (caller false) [i32 0x11223344] rfl)
  exact (((rootEnter false).trans body).tail finishLabel).tail finishFrame

private theorem rootTraps : Steps CallFrame.v1NoHost ⟨base true, outside, rootInput.code⟩ unwound := by
  have body := (trapRun.label 1 []).frame 1 outside
  have finishLabel : Step CallFrame.v1NoHost (inReader ⟨written true, caller true, [.trap]⟩)
      ⟨written true, outside, [.frame 1 (caller true) [.trap]]⟩ :=
    .frame (.pure _ _ (.labelTrap 1 [])) 1 _
  have finishFrame : Step CallFrame.v1NoHost
      ⟨written true, outside, [.frame 1 (caller true) [.trap]]⟩ unwound :=
    .pure _ _ (.frameTrap 1 (caller true))
  exact (((rootEnter true).trans body).tail finishLabel).tail finishFrame

private theorem rootPrefix : Steps CallFrame.v1NoHost
    ⟨base true, outside, rootInput.code⟩ (inReader nextWrite) := by
  have body := ((Relation.ReflTransGen.single (resolve true)).tail (enter true)).tail writesBeforeTrap
  exact (rootEnter true).trans ((Wasm.V1.Execution.Steps.label body 1 []).frame 1 outside)

private theorem rootReadback {traps : Bool} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨base traps, outside, rootInput.code⟩ dst) :
    ∃ out, Runs (program traps) slot rootInput out ∧
      Ready (program traps) slot 2 before.size out ∧ dst = render (base traps) slot memory out :=
  (v1_call_run_iff (root := parentAddr) (fn := reader traps) (index := ⟨0⟩) (args := rootArgs) (caller := outside)
    (checked traps) (layout traps) rfl rfl).mp path

example : ∃ out, Runs (program false) slot rootInput out ∧ returned = render (base false) slot memory out := by
  obtain ⟨out, path, _, eq⟩ := rootReadback rootReturns
  exact ⟨out, path, eq⟩

example : ∃ out, Runs (program true) slot rootInput out ∧ unwound = render (base true) slot memory out ∧
    SharedStore (base true) slot memory unwound.store := by
  obtain ⟨out, path, ready, eq⟩ := rootReadback rootTraps
  exact ⟨out, path, eq, eq ▸ render_shared ready⟩

-- Stop after the nested write with both activations still live. Reflect the
-- very next bounds trap separately, with the written store still in place.
example : ∃ middle stopped,
    Runs (program true) slot rootInput middle ∧ Edge (program true) slot middle stopped ∧
      inReader nextWrite = render (base true) slot memory middle ∧
      inReader firstTrap = render (base true) slot memory stopped ∧ middle.bytes = stopped.bytes := by
  obtain ⟨middle, path, ready, endpoint⟩ := rootReadback rootPrefix
  have trapUnderReader := Step.frame (Step.label trapsLater 1 []) 1 outside
  have trapFromRender : Step CallFrame.v1NoHost (render (base true) slot memory middle) (inReader firstTrap) :=
    endpoint ▸ trapUnderReader
  obtain ⟨stopped, move, _, eq⟩ := (v1_step_iff (checked true) (layout true) ready).mp trapFromRender
  have storeBefore := congrArg (fun c : Config Unit => c.store) endpoint
  have storeAfter := congrArg (fun c : Config Unit => c.store) eq
  have sameStore := storeBefore.symm.trans storeAfter
  have sameCell := congrArg (fun s : Store Unit => s.memories[slot.value]?) sameStore
  have inBounds : slot.value < (base true).memories.length := by decide
  have cell : ({ memory with data := middle.bytes } : MemInst) =
      { memory with data := stopped.bytes } := by
    simpa [render, storeWithBytes, Wasm.V1.Execution.setMemory, List.getElem?_set, inBounds] using sameCell
  exact ⟨middle, stopped, path, move, endpoint, eq, congrArg MemInst.data cell⟩

-- The surrounding address stays below the condition and outside the arm.
-- The false arm skips the entire call, even when that callee would write and trap.
private def conditional (traps : Bool) : Function :=
  ⟨{ declaration [childAddr] [.int .i32] with params := [.int .i32] }, 1, [i32 2],
    [.ranked (.numeric (.get ⟨0⟩)), .if_ none [.ranked (.call (target traps))] [], .load 1]⟩

private def ifProgram (traps : Bool) : Program := ⟨[some (writer traps), some (conditional traps)]⟩
private def ifBase (traps : Bool) : Store Unit :=
  { memories := [untouched, memory], funcs := [writer traps, conditional traps].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }
private theorem ifChecked (traps : Bool) : (ifProgram traps).checkV1 slot = true := by
  cases traps <;> rfl
private theorem ifLayout (traps : Bool) : Layout (ifProgram traps) (ifBase traps) slot memory where
  memory := rfl
  functions := by
    intro a fn found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, ifProgram] at found
    all_goals subst fn; rfl

example : Function.checkV1 { conditional false with
    code := [.ranked (.numeric (.get ⟨0⟩)), .if_ none [] [.store 0], .load 1] } slot = false := rfl

example : Function.checkV1 { conditional false with
    declaration := { (conditional false).declaration with params := [.int .i64] } } slot = false := rfl

example : Function.checkV1 { conditional false with
    initial := []
    code := [.ranked (.numeric (.get ⟨0⟩)), .if_ (some (.int .i32))
      [.ranked (.numeric (.get ⟨0⟩))]
      [.if_ (some (.int .i32)) [] []]] } slot = false := rfl

-- The inner arm may return the function's i32 even though its label is void.
example : Function.checkV1 { conditional false with
    initial := []
    code := [.ranked (.numeric (.get ⟨0⟩)), .if_ (some (.int .i32))
      [.ranked (.numeric (.get ⟨0⟩)), .if_ none
        [.ranked (.numeric (.get ⟨0⟩)), .ranked .return_] [],
        .ranked (.numeric (.get ⟨0⟩))]
      [.ranked (.numeric (.get ⟨0⟩))]] } slot = true := rfl

example : (Program.mk [some (writer false), some { conditional false with rank := 0 }]).checkV1 slot =
    false := rfl

private def ifInput (condition : BitVec 32) : State :=
  ⟨before, outside, values [i32 condition] ++ [.source (.call ⟨0⟩)]⟩
private def ifFrame (traps : Bool) (condition : BitVec 32) : Frame :=
  (conditional traps).declaration.frame [i32 condition]
private def underReader (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] c.code]]⟩
private def selected (condition : BitVec 32) : Wasm.V1.Expr :=
  if condition = 0 then [] else [.call ⟨0⟩]
private def ifWritten (traps : Bool) := storeWithBytes (ifBase traps) slot memory after

-- Stop at the selected block, then account for the separate native label step.
private theorem ifSelect (traps : Bool) (condition : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput condition).code⟩
      (underReader ⟨ifBase traps, ifFrame traps condition,
        values saved ++ [.source (.block none (selected condition))] ++ continuation⟩) := by
  apply Relation.ReflTransGen.head
    (b := ⟨ifBase traps, outside, values [i32 condition] ++ [.invoke parentAddr]⟩)
    (Step.context (.call _ _ ⟨0⟩ parentAddr rfl) [i32 condition] [])
  have invoke := (ifLayout traps).enter (ifChecked traps) (address := parentAddr)
    (fn := conditional traps) rfl
    (ifLayout traps).initial_shared (caller := outside) (saved := []) (args := [i32 condition]) (tail := []) rfl
  refine Relation.ReflTransGen.head invoke ?_
  refine Relation.ReflTransGen.head
    (Step.frame (Step.label
      (Step.context (.localGet _ _ ⟨0⟩ (i32 condition) rfl) saved
        ([.source (.if_ none [.call ⟨0⟩] [])] ++ continuation)) 1 []) 1 outside) ?_
  exact .single (.frame (.label ((v1_if_select_iff (saved := saved)).mpr rfl) 1 []) 1 outside)

private theorem ifOpen (traps : Bool) (condition : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput condition).code⟩
      (underReader ⟨ifBase traps, ifFrame traps condition,
        values saved ++ [.label 0 [] (Wasm.V1.Execution.expression (selected condition))] ++ continuation⟩) :=
  (ifSelect traps condition).tail
    (.frame (.label (.context (.pure _ _ (.block none (selected condition))) saved continuation) 1 []) 1 outside)

private theorem ifReadback {traps : Bool} {condition : BitVec 32} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput condition).code⟩ dst) :
    ∃ out, Runs (ifProgram traps) slot (ifInput condition) out ∧
      Ready (ifProgram traps) slot 2 before.size out ∧ dst = render (ifBase traps) slot memory out :=
  (v1_call_run_iff (root := parentAddr) (fn := conditional traps) (index := ⟨0⟩)
    (args := [i32 condition]) (caller := outside) (ifChecked traps) (ifLayout traps) rfl rfl).mp path

example : ∃ out, Runs (ifProgram false) slot (ifInput 1) out ∧
    underReader ⟨ifBase false, ifFrame false 1,
      values saved ++ [.source (.block none [.call ⟨0⟩])] ++ continuation⟩ =
        render (ifBase false) slot memory out := by
  obtain ⟨out, path, _, eq⟩ := ifReadback (ifSelect false 1)
  exact ⟨out, path, eq⟩

private theorem ifFinish {traps : Bool} {condition word : BitVec 32} {s : Store Unit}
    (load : Step CallFrame.v1NoHost
      ⟨s, ifFrame traps condition, values saved ++ continuation⟩
      ⟨s, ifFrame traps condition, values [i32 word]⟩) :
    Steps CallFrame.v1NoHost
      (underReader ⟨s, ifFrame traps condition, values saved ++ [.label 0 [] []] ++ continuation⟩)
      ⟨s, outside, values [i32 word]⟩ := by
  apply Relation.ReflTransGen.head
    (Step.frame (Step.label (Step.context (.pure _ _ (.labelDone 0 [] [])) saved continuation) 1 []) 1 outside)
  apply Relation.ReflTransGen.head (Step.frame (Step.label load 1 []) 1 outside)
  apply Relation.ReflTransGen.head (Step.frame (.pure _ _ (.labelDone 1 [] [i32 word])) 1 outside)
  exact .single (.pure _ _ (.frameDone 1 (ifFrame traps condition) [i32 word] rfl))

example : ∃ out, Runs (ifProgram true) slot (ifInput 0) out ∧
    (⟨ifBase true, outside, values [i32 0]⟩ : Config Unit) = render (ifBase true) slot memory out := by
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 1) (address := 2)
    (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (ifBase true) (ifFrame true 0) = some (slot, memory) from rfl)).mpr
    ⟨.value 0, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  obtain ⟨out, path, _, eq⟩ := ifReadback ((ifOpen true 0).trans (ifFinish load))
  exact ⟨out, path, eq⟩

private def inIfArm (traps : Bool) (c : Config Unit) : Config Unit :=
  underReader ⟨c.store, ifFrame traps 1, values saved ++ [.label 0 [] c.code] ++ continuation⟩

private theorem inIfArm_steps {traps : Bool} {a b : Config Unit}
    (path : Steps CallFrame.v1NoHost a b) (frame : a.frame = ifFrame traps 1)
    (frame' : b.frame = ifFrame traps 1) :
    Steps CallFrame.v1NoHost (inIfArm traps a) (inIfArm traps b) := by
  simpa only [inIfArm, underReader, frame, frame'] using
    ((((path.label 0 []).context saved continuation).label 1 []).frame 1 outside)

private theorem ifInvoke (traps : Bool) :
    Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput 1).code⟩
      (inIfArm traps ⟨ifBase traps, ifFrame traps 1,
        MemoryWrite.v1ActivationCode none (callee traps) [] []
          (Wasm.V1.Execution.expression (writer traps).v1Func.body)⟩) := by
  apply (ifOpen traps 1).trans
  refine inIfArm_steps (traps := traps)
    (a := ⟨ifBase traps, ifFrame traps 1, [.source (.call ⟨0⟩)]⟩) ?_ rfl rfl
  apply Relation.ReflTransGen.head (Step.call _ _ ⟨0⟩ childAddr rfl)
  exact .single ((ifLayout traps).enter (ifChecked traps) (address := childAddr) (fn := writer traps) rfl
    (ifLayout traps).initial_shared (saved := []) (args := []) (tail := []) rfl)

example : ∃ out, Runs (ifProgram false) slot (ifInput 1) out ∧
    (⟨ifWritten false, outside, values [i32 0x11223344]⟩ : Config Unit) =
      render (ifBase false) slot memory out := by
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2) (callerSaved := []) (callerTail := []) (result := none)
    (caller := ifFrame false 1) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (ifBase false) (callee false) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have arm := ((Relation.ReflTransGen.single write).tail
    (Step.frame (.pure _ _ (.labelDone 0 [] [])) 0 (ifFrame false 1))).tail
    (Step.pure _ (ifFrame false 1) (.frameDone 0 (callee false) [] rfl))
  have resumed := (ifInvoke false).trans (inIfArm_steps arm rfl rfl)
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 1) (address := 2)
    (saved := []) (tail := [])
    ((ifLayout false).frame_memory (ifChecked false) (address := parentAddr) (fn := conditional false)
      rfl [i32 1] after)).mpr ⟨.value 0x11223344, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  obtain ⟨out, path, _, eq⟩ := ifReadback (resumed.trans (ifFinish load))
  exact ⟨out, path, eq⟩

example : ∃ out, Runs (ifProgram true) slot (ifInput 1) out ∧
    (⟨ifWritten true, outside, [.trap]⟩ : Config Unit) = render (ifBase true) slot memory out := by
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2)
    (caller := ifFrame true 1) (callerSaved := []) (callerTail := []) (result := none)
    (saved := [i32 3, i32 0]) (tail := [.source ((Op.store 2).v1)])
    (show Wasm.V1.Execution.frameMemory (ifBase true) (callee true) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have fail := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2) (callerSaved := []) (callerTail := []) (result := none)
    (caller := ifFrame true 1) (saved := []) (tail := []) (address := 3) (word := 0)
    (show Wasm.V1.Execution.frameMemory (ifWritten true) (callee true) = some (slot, updated) from rfl)).mpr
    ⟨.trap, MemoryWrite.store_trap_iff_at.mpr (by decide), rfl⟩
  have arm := (((Relation.ReflTransGen.single write).tail fail).tail
    (Step.frame (.pure _ _ (.labelTrap 0 [])) 0 (ifFrame true 1))).tail
    (Step.pure _ (ifFrame true 1) (.frameTrap 0 (callee true)))
  have branchTrap := ((ifInvoke true).trans (inIfArm_steps arm rfl rfl)).tail
    (Step.frame (Step.label (Step.context (.pure _ _ (.labelTrap 0 [])) saved continuation) 1 []) 1 outside)
  have discard := branchTrap.tail
    (Step.frame (Step.label (.pure _ _ (.trapValues (i32 2) [] continuation)) 1 []) 1 outside)
  have unwind := (discard.tail (Step.frame (.pure _ _ (.labelTrap 1 [])) 1 outside)).tail
    (Step.pure _ _ (.frameTrap 1 (ifFrame true 1)))
  obtain ⟨out, path, _, eq⟩ := ifReadback unwind
  exact ⟨out, path, eq⟩

-- The void inner block calls the writer. The outer block delivers the i32
-- local above a saved 4. The continuation subtracts it, then loads at 2 + 1.
private def blockReader (traps : Bool) : Function :=
  ⟨(conditional traps).declaration, 1, [i32 4],
    [.block (some (.int .i32)) [.block none [.ranked (.call (target traps))],
      .ranked (.numeric (.get ⟨0⟩))],
      .ranked (.numeric (.bin .i32 .sub)), .load 1]⟩

private def blockProgram (traps : Bool) : Program := ⟨[some (writer traps), some (blockReader traps)]⟩
private def blockBase (traps : Bool) : Store Unit :=
  { memories := [untouched, memory], funcs := [writer traps, blockReader traps].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }
private theorem blockChecked (traps : Bool) : (blockProgram traps).checkV1 slot = true := by
  cases traps <;> rfl
private theorem blockLayout (traps : Bool) : Layout (blockProgram traps) (blockBase traps) slot memory where
  memory := rfl
  functions := by
    intro a fn found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, blockProgram] at found
    all_goals subst fn; rfl

example : (Program.mk [some (writer false), some { blockReader false with rank := 0 }]).checkV1 slot =
    false := rfl

-- The body cannot use the enclosing address without producing its own.
example : Function.checkV1 { blockReader false with
    code := [.block (some (.int .i32)) [.load 1], .ranked (.numeric (.bin .i32 .sub))] } slot = false := rfl

example : Function.checkV1 { blockReader false with
    code := [.block (some (.int .i32)) [], .ranked (.numeric (.bin .i32 .sub))] } slot = false := rfl

-- Returning an i32 through a void block checks the enclosing function result.
example : Function.checkV1 { blockReader false with
    code := [.block (some (.int .i64)) [.block none [.ranked (.numeric (.get ⟨0⟩)), .ranked .return_],
      .ranked .unreachable], .ranked .unreachable] } slot = true := rfl

example : Function.checkV1 { blockReader false with
    code := [.block none [.ranked .return_], .load 1] } slot = false := rfl

private def blockInput := ifInput 2
private def blockFrame (traps : Bool) := (blockReader traps).declaration.frame [i32 2]
private def blockWritten (traps : Bool) := storeWithBytes (blockBase traps) slot memory after
private def pendingGet : List Wasm.V1.Execution.Admin := [.source (.localGet ⟨0⟩)]
private def blockTail : List Wasm.V1.Execution.Admin := [.source (.intBinOp .i32 .sub)] ++ continuation

private def inOuterBlock (c : Config Unit) : Config Unit :=
  underReader ⟨c.store, c.frame, values [i32 4] ++ [.label 1 [] c.code] ++ blockTail⟩

private def inNestedBlocks (c : Config Unit) : Config Unit :=
  inOuterBlock ⟨c.store, c.frame, [.label 0 [] c.code] ++ pendingGet⟩

private theorem inNestedBlocks_steps {a b : Config Unit} (path : Steps CallFrame.v1NoHost a b) :
    Steps CallFrame.v1NoHost (inNestedBlocks a) (inNestedBlocks b) :=
  let blocks := (((path.label 0 []).context [] pendingGet).label 1 []).context [i32 4] blockTail
  (blocks.label 1 []).frame 1 outside

private theorem outerBlockOpen (traps : Bool) :
    Steps CallFrame.v1NoHost ⟨blockBase traps, outside, blockInput.code⟩
      (inOuterBlock ⟨blockBase traps, blockFrame traps, [.source (.block none [.call ⟨0⟩])] ++ pendingGet⟩) := by
  apply Relation.ReflTransGen.head
    (b := ⟨blockBase traps, outside, values [i32 2] ++ [.invoke parentAddr]⟩)
    (Step.context (.call _ _ ⟨0⟩ parentAddr rfl) [i32 2] [])
  refine Relation.ReflTransGen.head
    ((blockLayout traps).enter (blockChecked traps) (address := parentAddr)
      (fn := blockReader traps) rfl (blockLayout traps).initial_shared (saved := []) (args := [i32 2])
      (tail := []) rfl) ?_
  exact .single (.frame (.label (.context
    (.pure _ _ (.block (some (.int .i32)) [.block none [.call ⟨0⟩], .localGet ⟨0⟩]))
    [i32 4] blockTail) 1 []) 1 outside)

private theorem innerBlockOpen (traps : Bool) :
    Step CallFrame.v1NoHost
      (inOuterBlock ⟨blockBase traps, blockFrame traps, [.source (.block none [.call ⟨0⟩])] ++ pendingGet⟩)
      (inNestedBlocks ⟨blockBase traps, blockFrame traps, [.source (.call ⟨0⟩)]⟩) :=
  .frame (.label (.context (.label (.context (.pure _ _ (.block none [.call ⟨0⟩])) [] pendingGet)
    1 []) [i32 4] blockTail) 1 []) 1 outside

private theorem blockReadback {traps : Bool} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨blockBase traps, outside, blockInput.code⟩ dst) :
    ∃ out, Runs (blockProgram traps) slot blockInput out ∧
      Ready (blockProgram traps) slot 2 before.size out ∧ dst = render (blockBase traps) slot memory out :=
  (v1_call_run_iff (root := parentAddr) (fn := blockReader traps) (index := ⟨0⟩)
    (args := [i32 2]) (caller := outside) (blockChecked traps) (blockLayout traps) rfl rfl).mp path

example : ∃ outer inner, Runs (blockProgram false) slot blockInput outer ∧ Edge (blockProgram false) slot outer inner ∧
    inOuterBlock ⟨blockBase false, blockFrame false, [.source (.block none [.call ⟨0⟩])] ++ pendingGet⟩ =
      render (blockBase false) slot memory outer ∧
    inNestedBlocks ⟨blockBase false, blockFrame false, [.source (.call ⟨0⟩)]⟩ =
      render (blockBase false) slot memory inner := by
  obtain ⟨outer, reaches, ready, eq⟩ := blockReadback (outerBlockOpen false)
  have next := eq ▸ innerBlockOpen false
  obtain ⟨inner, move, _, targetEq⟩ := (v1_step_iff (blockChecked false) (blockLayout false) ready).mp next
  exact ⟨outer, inner, reaches, move, eq, targetEq⟩

private theorem blockInvoke (traps : Bool) :
    Steps CallFrame.v1NoHost ⟨blockBase traps, outside, blockInput.code⟩
      (inNestedBlocks ⟨blockBase traps, blockFrame traps,
        MemoryWrite.v1ActivationCode none (callee traps) [] []
          (Wasm.V1.Execution.expression (writer traps).v1Func.body)⟩) := by
  apply ((outerBlockOpen traps).tail (innerBlockOpen traps)).trans
  apply inNestedBlocks_steps
  apply Relation.ReflTransGen.head (Step.call _ _ ⟨0⟩ childAddr rfl)
  exact .single ((blockLayout traps).enter (blockChecked traps) (address := childAddr)
    (fn := writer traps) rfl (blockLayout traps).initial_shared (saved := []) (args := []) (tail := []) rfl)

example : ∃ out, Runs (blockProgram false) slot blockInput out ∧
    (⟨blockWritten false, outside, values [i32 0x11223344]⟩ : Config Unit) =
      render (blockBase false) slot memory out := by
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 2) (caller := blockFrame false) (result := none)
    (callerSaved := []) (callerTail := []) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (blockBase false) (callee false) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have child := ((Relation.ReflTransGen.single write).tail
    (Step.frame (.pure _ _ (.labelDone 0 [] [])) 0 (blockFrame false))).tail
    (Step.pure _ (blockFrame false) (.frameDone 0 (callee false) [] rfl))
  have resumeInner := ((blockInvoke false).trans (inNestedBlocks_steps child)).tail
    (Step.frame (.label (.context (.label (.context (.pure _ _ (.labelDone 0 [] [])) [] pendingGet) 1 [])
      [i32 4] blockTail) 1 []) 1 outside)
  have get := resumeInner.tail
    (Step.frame (.label (.context (.label (.localGet _ _ ⟨0⟩ (i32 2) rfl) 1 [])
      [i32 4] blockTail) 1 []) 1 outside)
  have resumeOuter := get.tail
    (Step.frame (.label (.context (.pure _ _ (.labelDone 1 [] [i32 2])) [i32 4] blockTail) 1 []) 1 outside)
  have sub := resumeOuter.tail
    (Step.frame (.label (.context (.pure _ _ (.intBinary .i32 .sub 4 2 2 rfl)) [] continuation) 1 []) 1 outside)
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 1) (address := 2) (saved := []) (tail := [])
    ((blockLayout false).frame_memory (blockChecked false) (address := parentAddr) (fn := blockReader false)
      rfl [i32 2] after)).mpr ⟨.value 0x11223344, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  have result := ((sub.tail (Step.frame (Step.label load 1 []) 1 outside)).tail
    (Step.frame (.pure _ _ (.labelDone 1 [] [i32 0x11223344])) 1 outside)).tail
    (Step.pure _ _ (.frameDone 1 (blockFrame false) [i32 0x11223344] rfl))
  obtain ⟨out, reaches, _, eq⟩ := blockReadback result
  exact ⟨out, reaches, eq⟩

example : ∃ out, Runs (blockProgram true) slot blockInput out ∧
    (⟨blockWritten true, outside, [.trap]⟩ : Config Unit) = render (blockBase true) slot memory out := by
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 2) (caller := blockFrame true) (result := none)
    (callerSaved := []) (callerTail := []) (saved := [i32 3, i32 0]) (tail := [.source ((Op.store 2).v1)])
    (show Wasm.V1.Execution.frameMemory (blockBase true) (callee true) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have bounds := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 2) (caller := blockFrame true) (result := none)
    (callerSaved := []) (callerTail := []) (saved := []) (tail := []) (address := 3) (word := 0)
    (show Wasm.V1.Execution.frameMemory (blockWritten true) (callee true) = some (slot, updated) from rfl)).mpr
    ⟨.trap, MemoryWrite.store_trap_iff_at.mpr (by decide), rfl⟩
  have child := (((Relation.ReflTransGen.single write).tail bounds).tail
    (Step.frame (.pure _ _ (.labelTrap 0 [])) 0 (blockFrame true))).tail
    (Step.pure _ _ (.frameTrap 0 (callee true)))
  have popInner := ((blockInvoke true).trans (inNestedBlocks_steps child)).tail
    (Step.frame (.label (.context (.label (.context (.pure _ _ (.labelTrap 0 [])) [] pendingGet) 1 [])
      [i32 4] blockTail) 1 []) 1 outside)
  have skipGet := popInner.tail
    (Step.frame (.label (.context (.label (.pure _ _ (.trapTail (.source (.localGet ⟨0⟩)) [])) 1 [])
      [i32 4] blockTail) 1 []) 1 outside)
  have popOuter := skipGet.tail
    (Step.frame (.label (.context (.pure _ _ (.labelTrap 1 [])) [i32 4] blockTail) 1 []) 1 outside)
  have discard := popOuter.tail
    (Step.frame (.label (.pure _ _ (.trapValues (i32 4) [] blockTail)) 1 []) 1 outside)
  have unwind := (discard.tail (Step.frame (.pure _ _ (.labelTrap 1 [])) 1 outside)).tail
    (Step.pure _ _ (.frameTrap 1 (blockFrame true)))
  obtain ⟨out, reaches, _, eq⟩ := blockReadback unwind
  exact ⟨out, reaches, eq⟩

-- A callee writes before the branch. When the branch is untaken, the arm overwrites those
-- bytes using the two operands below the condition. Both paths deliver 2
-- above the saved 4, then subtract and read address 2 + 1.
private def branchDepth (toFunction : Bool) : LabelIdx := if toFunction then ⟨2⟩ else ⟨1⟩

private def branchArmSource (toFunction : Bool) : List Op :=
  [.ranked (.call (target false)), .ranked (.numeric (.get ⟨2⟩)), .ranked (.numeric (.get ⟨0⟩)),
    .ranked (.numeric (.get ⟨1⟩)), .ranked (.brIf (branchDepth toFunction) [.int .i32]), .store 2]

private def branching (toFunction : Bool := false) : Function :=
  ⟨{ declaration [childAddr] [.int .i32] with params := [.int .i32, .int .i32, .int .i32] }, 1, [i32 4],
    [.block (some (.int .i32)) [.ranked (.numeric (.get ⟨2⟩)), .if_ none (branchArmSource toFunction) [],
      .ranked (.numeric (.get ⟨0⟩)), .ranked (.br ⟨0⟩ [.int .i32])],
      .ranked (.numeric (.bin .i32 .sub)), .load 1]⟩

private def branchProgram (toFunction : Bool := false) : Program := ⟨[some (writer false), some (branching toFunction)]⟩
private def branchBase (toFunction : Bool := false) : Store Unit :=
  { memories := [untouched, memory], funcs := [writer false, branching toFunction].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }
private theorem branchChecked (toFunction : Bool := false) : (branchProgram toFunction).checkV1 slot = true := by
  cases toFunction <;> rfl
private theorem branchLayout (toFunction : Bool := false) : Layout (branchProgram toFunction) (branchBase toFunction) slot memory where
  memory := rfl
  functions := by
    intro a fn found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, branchProgram] at found
    all_goals subst fn; rfl

-- Under a single explicit block the function label is depth one.
example : Function.checkV1 { branching with initial := [], code := [.block (some (.int .i32))
    [.ranked (.numeric (.get ⟨0⟩)), .ranked (.br ⟨2⟩ [.int .i32])]] } slot = false := rfl

-- Zero still requires a valid depth, arity, and result annotation.
example : branching.checkRegion [.int .i32, .int .i32] [.int .i32]
    [.ranked (.brIf ⟨1⟩ [.int .i32])] [[.int .i32]] = false := rfl
example : branching.checkRegion [.int .i32, .int .i32] [.int .i32]
    [.ranked (.brIf ⟨0⟩ [])] [[.int .i32]] = false := rfl
example : branching.checkRegion [.int .i32, .int .i32] [.int .i32]
    [.ranked (.brIf ⟨0⟩ [.int .i64])] [[.int .i32]] = false := rfl

example : branching.checkRegion [.int .i32] []
    [.ranked (.brIf ⟨0⟩ [.int .i32])] [[.int .i32]] = false := rfl
example : branching.checkRegion [.int .i32, .int .i64] [.int .i64]
    [.ranked (.brIf ⟨0⟩ [.int .i32])] [[.int .i32]] = false := rfl
example : branching.checkRegion [.int .i64, .int .i32] [.int .i32]
    [.ranked (.brIf ⟨0⟩ [.int .i32])] [[.int .i32]] = false := rfl
example : branching.checkRegion [.int .i64] []
    [.ranked (.br ⟨0⟩ [.int .i32])] [[.int .i32]] = false := rfl

-- The whole-body guard still validates depths and signatures in skipped code.
example : Function.checkV1 { branching with initial := [], code := [.block (some (.int .i32))
    [.ranked (.numeric (.get ⟨0⟩)), .ranked .return_, .ranked (.br ⟨2⟩ [.int .i32])]] } slot = false := rfl
example : Function.checkV1 { branching with initial := [], code := [.block (some (.int .i32))
    [.ranked (.numeric (.get ⟨0⟩)), .ranked .return_, .ranked (.brIf ⟨1⟩ [.int .i64])]] } slot = false := rfl

private def branchArgs (condition : BitVec 32) := [i32 2, i32 condition, i32 1]
private def branchInput (condition : BitVec 32) : State :=
  ⟨before, outside, values (branchArgs condition) ++ [.source (.call ⟨0⟩)]⟩
private def branchFrame (condition : BitVec 32) := branching.declaration.frame (branchArgs condition)

private def branchWritten (toFunction : Bool := false) := storeWithBytes (branchBase toFunction) slot memory after
private def overwritten : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 2, 0, 0, 0, 0xdd]⟩
private def branchOverwritten := storeWithBytes branchBase slot memory overwritten

private def branchArmCode (toFunction : Bool) := v1Code (branchArmSource toFunction)
private def branchInnerTail : List Wasm.V1.Execution.Admin := [.source ((Op.store 2).v1)]
private def branchOperands (toFunction : Bool) : List Wasm.V1.Execution.Admin :=
  [.source (.localGet ⟨2⟩), .source (.localGet ⟨0⟩), .source (.localGet ⟨1⟩), .source (.brIf (branchDepth toFunction))] ++ branchInnerTail
private def branchOuterTail : List Wasm.V1.Execution.Admin := [.source (.localGet ⟨0⟩), .source (.br ⟨0⟩)]
private def branchPair := [i32 1, i32 2]

private def inBranchFunction (c : Config Unit) : Config Unit :=
  underReader ⟨c.store, c.frame, values [i32 4] ++ c.code ++ blockTail⟩

private def inBranchBlock (c : Config Unit) : Config Unit :=
  inBranchFunction ⟨c.store, c.frame, [.label 1 [] c.code]⟩

private def inBranchArm (c : Config Unit) : Config Unit :=
  inBranchBlock ⟨c.store, c.frame, [.label 0 [] c.code] ++ branchOuterTail⟩

private theorem branchFunctionStep {s s' : Store Unit} {f f' : Frame}
    {code code' : List Wasm.V1.Execution.Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    Step CallFrame.v1NoHost (inBranchFunction ⟨s, f, code⟩) (inBranchFunction ⟨s', f', code'⟩) :=
  .frame (.label (.context move [i32 4] blockTail) 1 []) 1 outside

private theorem branchBlockStep {s s' : Store Unit} {f f' : Frame}
    {code code' : List Wasm.V1.Execution.Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    Step CallFrame.v1NoHost (inBranchBlock ⟨s, f, code⟩) (inBranchBlock ⟨s', f', code'⟩) :=
  branchFunctionStep (.label move 1 [])

private theorem branchArmStep {s s' : Store Unit} {f f' : Frame}
    {code code' : List Wasm.V1.Execution.Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    Step CallFrame.v1NoHost (inBranchArm ⟨s, f, code⟩) (inBranchArm ⟨s', f', code'⟩) :=
  branchBlockStep (.context (.label move 0 []) [] branchOuterTail)

private theorem branchEntry (condition : BitVec 32) (toFunction : Bool := false) :
    Steps CallFrame.v1NoHost ⟨(branchBase toFunction), outside, (branchInput condition).code⟩
      (inBranchArm ⟨(branchBase toFunction), branchFrame condition, [.source (.call ⟨0⟩)] ++ (branchOperands toFunction)⟩) := by
  apply Relation.ReflTransGen.head
    (b := ⟨(branchBase toFunction), outside, values (branchArgs condition) ++ [.invoke parentAddr]⟩)
    (Step.context (.call _ _ ⟨0⟩ parentAddr rfl) (branchArgs condition) [])
  refine Relation.ReflTransGen.head
    ((branchLayout toFunction).enter (branchChecked toFunction) (address := parentAddr) (fn := branching toFunction) rfl (branchLayout toFunction).initial_shared
      (saved := []) (args := branchArgs condition) (tail := []) rfl) ?_
  refine Relation.ReflTransGen.head
    (branchFunctionStep (.pure _ _ (.block (some (.int .i32))
      [.localGet ⟨2⟩, .if_ none (branchArmCode toFunction) [], .localGet ⟨0⟩, .br ⟨0⟩]))) ?_
  refine Relation.ReflTransGen.head
    (branchBlockStep (.context (.localGet _ _ ⟨2⟩ (i32 1) rfl) []
      ([.source (.if_ none (branchArmCode toFunction) [])] ++ branchOuterTail))) ?_
  refine Relation.ReflTransGen.head
    (branchBlockStep (.context (.pure _ _ (.ifNonzero none (branchArmCode toFunction) [] 1 (by decide)))
      [] branchOuterTail)) ?_
  exact .single (branchBlockStep (.context (.pure _ _ (.block none (branchArmCode toFunction))) [] branchOuterTail))

private theorem branchCall (condition : BitVec 32) (toFunction : Bool := false) :
    Steps CallFrame.v1NoHost ⟨(branchBase toFunction), outside, (branchInput condition).code⟩
      (inBranchArm ⟨(branchWritten toFunction), branchFrame condition, (branchOperands toFunction)⟩) := by
  have resolved := (branchEntry condition toFunction).tail
    (branchArmStep (.context (.call _ _ ⟨0⟩ childAddr rfl) [] (branchOperands toFunction)))
  have entered := resolved.tail
    (branchArmStep ((branchLayout toFunction).enter (branchChecked toFunction) (address := childAddr) (fn := writer false)
      rfl (branchLayout toFunction).initial_shared (saved := []) (args := []) (tail := (branchOperands toFunction)) rfl))
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 2) (caller := branchFrame condition) (result := none)
    (callerSaved := []) (callerTail := (branchOperands toFunction)) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (branchBase toFunction) (callee false) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have labelExit := (entered.tail (branchArmStep write)).tail (branchArmStep
    (.context (.frame (.pure _ _ (.labelDone 0 [] [])) 0 _) [] (branchOperands toFunction)))
  exact labelExit.tail (branchArmStep
    (.context (.pure _ _ (.frameDone 0 (callee false) [] rfl)) [] (branchOperands toFunction)))

private def beforeBranch (condition : BitVec 32) (toFunction : Bool := false) : Config Unit :=
  inBranchArm ⟨(branchWritten toFunction), branchFrame condition,
    values (branchPair ++ [i32 condition]) ++ [.source (.brIf (branchDepth toFunction))] ++ branchInnerTail⟩

private theorem branchPrefix (condition : BitVec 32) (toFunction : Bool := false) :
    Steps CallFrame.v1NoHost ⟨(branchBase toFunction), outside, (branchInput condition).code⟩ (beforeBranch condition toFunction) := by
  have address := (branchCall condition toFunction).tail (branchArmStep
    (.context (.localGet _ _ ⟨2⟩ (i32 1) rfl) []
      ([.source (.localGet ⟨0⟩), .source (.localGet ⟨1⟩), .source (.brIf (branchDepth toFunction))] ++ branchInnerTail)))
  have payload := address.tail (branchArmStep
    (.context (.localGet _ _ ⟨0⟩ (i32 2) rfl) [i32 1]
      ([.source (.localGet ⟨1⟩), .source (.brIf (branchDepth toFunction))] ++ branchInnerTail)))
  exact payload.tail (branchArmStep
    (.context (.localGet _ _ ⟨1⟩ (i32 condition) rfl) branchPair ([.source (.brIf (branchDepth toFunction))] ++ branchInnerTail)))

private theorem branchReadback (toFunction : Bool) {condition : BitVec 32} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨(branchBase toFunction), outside, (branchInput condition).code⟩ dst) :
    ∃ out, Runs (branchProgram toFunction) slot (branchInput condition) out ∧ Ready (branchProgram toFunction) slot 2 before.size out ∧
      dst = render (branchBase toFunction) slot memory out :=
  (v1_call_run_iff (root := parentAddr) (fn := branching toFunction) (index := ⟨0⟩)
    (args := branchArgs condition) (caller := outside) (branchChecked toFunction) (branchLayout toFunction) rfl rfl).mp path

private def selectedBranch : Config Unit :=
  inBranchArm ⟨branchWritten, branchFrame 1, values branchPair ++ [.source (.br ⟨1⟩)] ++ branchInnerTail⟩
private def loweredBranch : Config Unit :=
  inBranchBlock ⟨branchWritten, branchFrame 1, values branchPair ++ [.source (.br ⟨0⟩)] ++ branchOuterTail⟩
private def deliveredBranch (condition : BitVec 32) (s : Store Unit) : Config Unit :=
  inBranchFunction ⟨s, branchFrame condition, values [i32 2]⟩
private def fallthroughBranch : Config Unit :=
  inBranchArm ⟨branchWritten, branchFrame 0, values branchPair ++ branchInnerTail⟩

private theorem selectBranch : Step CallFrame.v1NoHost (beforeBranch 1) selectedBranch :=
  branchArmStep (.context (.pure _ _ (.brIfNonzero ⟨1⟩ 1 (by decide))) branchPair branchInnerTail)
private theorem lowerBranch : Step CallFrame.v1NoHost selectedBranch loweredBranch :=
  branchBlockStep (.context (.pure _ _ (.labelBranchOuter 0 [] branchPair branchInnerTail ⟨1⟩ (by decide)))
    [] branchOuterTail)
private theorem deliverBranch : Step CallFrame.v1NoHost loweredBranch (deliveredBranch 1 branchWritten) :=
  branchFunctionStep (.pure _ _ (.labelBranch 1 [] [i32 1] [i32 2] branchOuterTail rfl))
private theorem skipBranch : Step CallFrame.v1NoHost (beforeBranch 0) fallthroughBranch :=
  branchArmStep (.context (.pure _ _ (.brIfZero ⟨1⟩)) branchPair branchInnerTail)

-- Each finite prefix keeps the previous write and reflects one native edge
-- for selection, transfer out of the arm, and exit of the targeted block.
example : ∃ src selected lowered delivered, Runs branchProgram slot (branchInput 1) src ∧
    Edge branchProgram slot src selected ∧ Edge branchProgram slot selected lowered ∧
    Edge branchProgram slot lowered delivered ∧
    beforeBranch 1 = render branchBase slot memory src ∧ selectedBranch = render branchBase slot memory selected ∧
    loweredBranch = render branchBase slot memory lowered ∧
    deliveredBranch 1 branchWritten = render branchBase slot memory delivered := by
  obtain ⟨src, reaches, ready, eq⟩ := branchReadback false (branchPrefix 1)
  obtain ⟨selected, select, selReady, selEq⟩ := (v1_step_iff branchChecked branchLayout ready).mp (eq ▸ selectBranch)
  obtain ⟨lowered, lower, lowReady, lowEq⟩ := (v1_step_iff branchChecked branchLayout selReady).mp (selEq ▸ lowerBranch)
  obtain ⟨delivered, deliver, _, endEq⟩ := (v1_step_iff branchChecked branchLayout lowReady).mp (lowEq ▸ deliverBranch)
  exact ⟨src, selected, lowered, delivered, reaches, select, lower, deliver, eq, selEq, lowEq, endEq⟩

example : ∃ src next, Runs branchProgram slot (branchInput 0) src ∧ Edge branchProgram slot src next ∧
    beforeBranch 0 = render branchBase slot memory src ∧ fallthroughBranch = render branchBase slot memory next := by
  obtain ⟨src, reaches, ready, eq⟩ := branchReadback false (branchPrefix 0)
  obtain ⟨next, step, _, nextEq⟩ := (v1_step_iff branchChecked branchLayout ready).mp (eq ▸ skipBranch)
  exact ⟨src, next, reaches, step, eq, nextEq⟩

private theorem branchFinish {condition word : BitVec 32} {s : Store Unit}
    (load : Step CallFrame.v1NoHost
      ⟨s, branchFrame condition, values [i32 2] ++ continuation⟩
      ⟨s, branchFrame condition, values [i32 word]⟩) :
    Steps CallFrame.v1NoHost (deliveredBranch condition s) ⟨s, outside, values [i32 word]⟩ := by
  apply Relation.ReflTransGen.head
    (Step.frame (Step.label (Step.context (.pure _ _ (.intBinary .i32 .sub 4 2 2 rfl)) [] continuation) 1 [])
      1 outside)
  apply Relation.ReflTransGen.head (Step.frame (Step.label load 1 []) 1 outside)
  apply Relation.ReflTransGen.head (Step.frame (.pure _ _ (.labelDone 1 [] [i32 word])) 1 outside)
  exact .single (.pure _ _ (.frameDone 1 (branchFrame condition) [i32 word] rfl))

example : ∃ out, Runs branchProgram slot (branchInput 1) out ∧
    (⟨branchWritten, outside, values [i32 0x11223344]⟩ : Config Unit) = render branchBase slot memory out := by
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 1) (address := 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory branchWritten (branchFrame 1) = some (slot, updated) from rfl)).mpr
    ⟨.value 0x11223344, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  have delivered := (((branchPrefix 1).tail selectBranch).tail lowerBranch).tail deliverBranch
  obtain ⟨out, run, _, eq⟩ := branchReadback false (delivered.trans (branchFinish load))
  exact ⟨out, run, eq⟩

example : ∃ out, Runs branchProgram slot (branchInput 0) out ∧
    (⟨branchOverwritten, outside, values [i32 2]⟩ : Config Unit) = render branchBase slot memory out := by
  have store := (MemoryWrite.v1_context_store_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 2) (address := 1) (word := 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory branchWritten (branchFrame 0) = some (slot, updated) from rfl)).mpr
    ⟨.written overwritten, MemoryWrite.fact_at (.write _ _ _ (by decide)), rfl⟩
  have wrote := ((branchPrefix 0).tail skipBranch).tail (branchArmStep store)
  have leaveArm := wrote.tail (branchBlockStep (.context (.pure _ _ (.labelDone 0 [] [])) [] branchOuterTail))
  have next := leaveArm.tail (branchBlockStep
    (.context (.localGet _ _ ⟨0⟩ (i32 2) rfl) [] [.source (.br ⟨0⟩)]))
  have delivered := next.tail (branchFunctionStep (.pure _ _ (.labelBranch 1 [] [] [i32 2] [] rfl)))
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 1) (address := 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory branchOverwritten (branchFrame 0) =
      some (slot, { memory with data := overwritten }) from rfl)).mpr
    ⟨.value 2, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  obtain ⟨out, run, _, eq⟩ := branchReadback false (delivered.trans (branchFinish load))
  exact ⟨out, run, eq⟩

example : Function.checkV1 { branching with
    initial := [i32 2]
    code := [.ranked (.br ⟨0⟩ [.int .i32])] } slot = true := rfl

example : Function.checkV1 { writer false with
    initial := [i32 2]
    code := [.ranked (.br ⟨0⟩ [])] } slot = true := rfl

example : Function.checkV1 { branching with
    initial := [Value.int .i64 2]
    code := [.ranked (.br ⟨0⟩ [.int .i32])] } slot = false := rfl

example : Function.checkV1 { branching with
    initial := [i32 2]
    code := [.ranked (.br ⟨0⟩ [])] } slot = false := rfl

private def functionSelected : Config Unit :=
  inBranchArm ⟨branchWritten true, branchFrame 1, values branchPair ++ [.source (.br ⟨2⟩)] ++ branchInnerTail⟩

private def functionLowered : Config Unit :=
  inBranchBlock ⟨branchWritten true, branchFrame 1, values branchPair ++ [.source (.br ⟨1⟩)] ++ branchOuterTail⟩

private def functionPending : Config Unit :=
  inBranchFunction ⟨branchWritten true, branchFrame 1, values branchPair ++ [.source (.br ⟨0⟩)]⟩

private def functionDelivered : Config Unit :=
  ⟨branchWritten true, outside, [.frame 1 (branchFrame 1) (values [i32 2])]⟩

private def functionDone : Config Unit :=
  ⟨branchWritten true, outside, values [i32 2]⟩

private theorem selectFunction : Step CallFrame.v1NoHost (beforeBranch 1 true) functionSelected :=
  branchArmStep (.context (.pure _ _ (.brIfNonzero ⟨2⟩ 1 (by decide))) branchPair branchInnerTail)

private theorem lowerArmForFunction : Step CallFrame.v1NoHost functionSelected functionLowered :=
  branchBlockStep (.context (.pure _ _ (.labelBranchOuter 0 [] branchPair branchInnerTail ⟨2⟩ (by decide)))
    [] branchOuterTail)

private theorem lowerBlockForFunction : Step CallFrame.v1NoHost functionLowered functionPending :=
  branchFunctionStep (.pure _ _ (.labelBranchOuter 1 [] branchPair branchOuterTail ⟨1⟩ (by decide)))

private theorem exitFunction : Step CallFrame.v1NoHost functionPending functionDelivered ∧
    Step CallFrame.v1NoHost functionDelivered functionDone :=
  v1_function_branch_exit (saved := []) (extra := [i32 4, i32 1]) (payload := [i32 2])
    (results := (branching true).declaration.results) (bodyTail := blockTail) (callerTail := []) rfl

-- The depth-two branch crosses the if arm and block before the implicit label
-- delivers 2. The inner store, outer local read, and function's subtract/load
-- are skipped. The first callee's write remains visible in all five successors.
example : ∃ start selected armExit blockExit delivered done,
    Runs (branchProgram true) slot (branchInput 1) start ∧
    Edge (branchProgram true) slot start selected ∧ Edge (branchProgram true) slot selected armExit ∧
    Edge (branchProgram true) slot armExit blockExit ∧ Edge (branchProgram true) slot blockExit delivered ∧
    Edge (branchProgram true) slot delivered done ∧
    beforeBranch 1 true = render (branchBase true) slot memory start ∧
    functionSelected = render (branchBase true) slot memory selected ∧
    functionLowered = render (branchBase true) slot memory armExit ∧
    functionPending = render (branchBase true) slot memory blockExit ∧
    functionDelivered = render (branchBase true) slot memory delivered ∧
    functionDone = render (branchBase true) slot memory done := by
  have step := fun {src} (ready : Ready (branchProgram true) slot 2 before.size src) {dst} =>
    (v1_step_iff (branchChecked true) (branchLayout true) (dst := dst) ready).mp
  obtain ⟨start, reaches, ready, eq⟩ := branchReadback true (branchPrefix 1 true)
  obtain ⟨selected, select, selReady, selEq⟩ := step ready (eq ▸ selectFunction)
  obtain ⟨armExit, lowerArm, armReady, armEq⟩ := step selReady (selEq ▸ lowerArmForFunction)
  obtain ⟨blockExit, lowerBlock, blockReady, blockEq⟩ := step armReady (armEq ▸ lowerBlockForFunction)
  obtain ⟨delivered, deliver, deliveredReady, deliveredEq⟩ := step blockReady (blockEq ▸ exitFunction.1)
  obtain ⟨done, complete, _, doneEq⟩ := step deliveredReady (deliveredEq ▸ exitFunction.2)
  exact ⟨start, selected, armExit, blockExit, delivered, done, reaches, select, lowerArm, lowerBlock, deliver,
    complete, eq, selEq, armEq, blockEq, deliveredEq, doneEq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
