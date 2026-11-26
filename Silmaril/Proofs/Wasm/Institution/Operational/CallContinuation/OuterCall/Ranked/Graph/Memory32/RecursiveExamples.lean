module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.V1.Execution.Properties

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private def word : BitVec 32 := 0x11223344
private def address : FuncAddr := ⟨0⟩
private def slot : MemAddr := ⟨0⟩
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def written : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def memory : MemInst := ⟨before, none⟩

private def decl : Declaration :=
  ⟨{ funcs := [address], memories := [slot] }, ⟨0⟩, [.int .i32, .int .i32], [.int .i32], [.int .i32]⟩

private def self : CallTarget := ⟨⟨0⟩, address, decl⟩
private def get (i : LocalIdx) : Op := .ranked (.numeric (.get i))
private def record : Op := .ranked (.set ⟨2⟩)
private def again : List Op := [get ⟨2⟩, get ⟨1⟩, .ranked (.call self), record]
private def write : List Op := [get ⟨0⟩, get ⟨1⟩, .store 1]
private def select : Op := .if_ none again write
private def fn : Function := ⟨decl, 0, [i32 0], [get ⟨0⟩, select, .load 1]⟩
private def graph : Program := ⟨[some fn]⟩
private def base : Store Unit :=
  { memories := [memory], funcs := [.wasm decl.type decl.module fn.v1Func] }
private def updated : Store Unit := storeWithBytes base slot memory written

private theorem checked : graph.checkV1 slot .fixed .recursive = true := rfl
private theorem layout : Layout graph base slot memory where
  memory := rfl
  functions := by
    intro a target found
    rcases a with ⟨_ | _⟩ <;> simp [Program.lookup, graph] at found
    subst target
    rfl

example : graph.checkV1 slot = false := rfl
example : graph.checkV1 ⟨1⟩ .fixed .recursive = false := rfl

private def withTarget (target : CallTarget) : Program :=
  ⟨[some { fn with initial := [], code := [get ⟨0⟩, get ⟨1⟩, .ranked (.call target)] }]⟩

example : (withTarget self).checkV1 slot .fixed .recursive = true := rfl

-- Wrong index, absent allocation in the graph, and a wrong claimed declaration
-- pass the body's stack check. Exact static linkage rejects all three.
example : (withTarget { self with index := ⟨1⟩ }).checkV1 slot .fixed .recursive = false := rfl
example : (withTarget { self with address := ⟨1⟩ }).checkV1 slot .fixed .recursive = false := rfl
example : (withTarget { self with declaration := { decl with locals := [] } }).checkV1 slot .fixed .recursive =
    false := rfl

private def outside : Frame := ⟨[i32 17], { funcs := [address] }⟩
private def args (flag : BitVec 32) : List Value := [i32 flag, i32 word]
private def active (flag : BitVec 32) : Frame := decl.frame (args flag)
private def saved : List Value := [i32 0]
private def loadTail : List Admin := [.source ((Op.load 1).v1)]
private def recordTail : List Admin := [.source record.v1]
private def root : State := ⟨before, outside, values (args 1) ++ [.source (.call ⟨0⟩)]⟩

private def inRoot (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] c.code]]⟩

-- In either activation, select the arm and open the zero-result label on a
-- separate step. The enclosing function's load keeps its saved address.
private theorem openArm (flag : BitVec 32) (arm : List Op)
    (choice : Step CallFrame.v1NoHost
      ⟨base, active flag, values [i32 flag] ++ [.source select.v1]⟩
      ⟨base, active flag, [.source (.block none (v1Code arm))]⟩) :
    Steps CallFrame.v1NoHost ⟨base, active flag, expression fn.v1Func.body⟩
      ⟨base, active flag, values saved ++ [.label 0 [] (expression (v1Code arm))] ++ loadTail⟩ := by
  have getFlag := Step.context (.localGet (host := CallFrame.v1NoHost) base (active flag) ⟨0⟩ (i32 flag) rfl)
    saved ([.source select.v1] ++ loadTail)
  exact ((Relation.ReflTransGen.single getFlag).tail (choice.context saved loadTail)).tail
    (.context (.pure _ _ (.block none (v1Code arm))) saved loadTail)

private theorem selectedAgain : Steps CallFrame.v1NoHost ⟨base, active 1, expression fn.v1Func.body⟩
    ⟨base, active 1, values saved ++ [.label 0 [] (expression (v1Code again))] ++ loadTail⟩ :=
  openArm 1 again (.pure _ _ (.ifNonzero none (v1Code again) (v1Code write) 1 (by decide)))

private theorem selectedWrite : Steps CallFrame.v1NoHost ⟨base, active 0, expression fn.v1Func.body⟩
    ⟨base, active 0, values saved ++ [.label 0 [] (expression (v1Code write))] ++ loadTail⟩ :=
  openArm 0 write (.pure _ _ (.ifZero none (v1Code again) (v1Code write)))

private def inArm (c : Config Unit) : Config Unit :=
  ⟨c.store, c.frame, values saved ++ [.label 0 [] c.code] ++ loadTail⟩

private theorem stepInArm {s t : Config Unit} (move : Step CallFrame.v1NoHost s t) :
    Step CallFrame.v1NoHost (inArm s) (inArm t) :=
  .context (.label move 0 []) saved loadTail

private def inSelf (c : Config Unit) : Config Unit :=
  inRoot (inArm ⟨c.store, active 1, [.frame 1 c.frame [.label 1 [] c.code]] ++ recordTail⟩)

private def enteredSelf : Config Unit := inSelf ⟨base, active 0, expression fn.v1Func.body⟩

private theorem enter {caller : Frame} (flag : BitVec 32) :
    Step CallFrame.v1NoHost ⟨base, caller, values (args flag) ++ [.invoke address]⟩
      ⟨base, caller, [.frame 1 (active flag) [.label 1 [] (expression fn.v1Func.body)]]⟩ := by
  have step := layout.enter_rendered (fn := fn) (address := address) rfl (by decide)
    (suspended := caller) (bytes := before) (args := args flag) rfl
  simp only [render, show storeWithBytes base slot memory before = base from layout.initial_store] at step
  exact step

private theorem reachSelf : Steps CallFrame.v1NoHost ⟨base, outside, root.code⟩ enteredSelf := by
  have resolveRoot : Step CallFrame.v1NoHost ⟨base, outside, root.code⟩
      ⟨base, outside, values (args 1) ++ [.invoke address]⟩ :=
    .context (.call _ _ ⟨0⟩ address rfl) (args 1) []
  have arg0 := stepInArm (.context (.localGet (host := CallFrame.v1NoHost) base (active 1) ⟨2⟩ (i32 0) rfl)
    [] (expression (v1Code [get ⟨1⟩, .ranked (.call self), record])))
  have arg1 := stepInArm (.context (.localGet (host := CallFrame.v1NoHost) base (active 1) ⟨1⟩ (i32 word) rfl)
    [i32 0] (expression (v1Code [.ranked (.call self), record])))
  have resolveSelf := stepInArm (.context (.call (host := CallFrame.v1NoHost) base (active 1) ⟨0⟩ address rfl)
    (args 0) recordTail)
  have enterSelf := stepInArm ((enter (caller := active 1) 0).context [] recordTail)
  have callerBody := ((selectedAgain.tail arg0).tail arg1).tail resolveSelf
  exact ((Relation.ReflTransGen.single resolveRoot).tail (enter 1)).trans
    (Steps.frame (Steps.label (callerBody.tail enterSelf) 1 []) 1 outside)

private theorem loadWritten {frame : Frame} (slotZero : frame.module.memories[0]? = some slot) :
    Step CallFrame.v1NoHost ⟨updated, frame, values saved ++ loadTail⟩ ⟨updated, frame, values [i32 word]⟩ := by
  have lookup : frameMemory updated frame = some (slot, { memory with data := written }) := by
    simp [frameMemory, slotZero, updated, storeWithBytes, setMemory, base, slot]
  exact (MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1)
    (address := 0) (saved := []) (tail := []) lookup).mpr
    ⟨.value word, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩

private theorem writeAndRead : Steps CallFrame.v1NoHost ⟨base, active 0, expression fn.v1Func.body⟩
    ⟨updated, active 0, values [i32 word]⟩ := by
  have getPointer := stepInArm (.context (.localGet (host := CallFrame.v1NoHost) base (active 0) ⟨0⟩ (i32 0) rfl)
    [] (expression (v1Code [get ⟨1⟩, .store 1])))
  have getWord := stepInArm (.context (.localGet (host := CallFrame.v1NoHost) base (active 0) ⟨1⟩ (i32 word) rfl)
    [i32 0] (expression (v1Code [.store 1])))
  have writeStep : Step CallFrame.v1NoHost
      ⟨base, active 0, values [i32 0, i32 word] ++ [.source ((Op.store 1).v1)]⟩ ⟨updated, active 0, []⟩ :=
    (MemoryWrite.v1_context_store_step_iff_at (immediate := immediate 1)
      (address := 0) (word := word) (saved := []) (tail := [])
      (show frameMemory base (active 0) = some (slot, memory) from rfl)).mpr
      ⟨.written written, MemoryWrite.fact_at (.write _ _ _ (by decide)), rfl⟩
  have closeArm : Step CallFrame.v1NoHost (inArm ⟨updated, active 0, []⟩)
      ⟨updated, active 0, values saved ++ loadTail⟩ :=
    .context (.pure _ _ (.labelDone 0 [] [])) saved loadTail
  exact ((((selectedWrite.tail getPointer).tail getWord).tail (stepInArm writeStep)).tail closeArm).tail
    (loadWritten rfl)

private def returnedToCaller : Config Unit := inRoot (inArm ⟨updated, active 1, values [i32 word] ++ recordTail⟩)

private theorem resume : Steps CallFrame.v1NoHost ⟨base, outside, root.code⟩ returnedToCaller := by
  have inChild := (((writeAndRead.label 1 []).frame 1 (active 1)).context [] recordTail).label 0 []
  have writes := reachSelf.trans (((inChild.context saved loadTail).label 1 []).frame 1 outside)
  have exit := v1_function_fallthrough (H := Unit) (s := updated) (caller := active 1)
    (callee := active 0) (saved := []) (payload := [i32 word]) (tail := recordTail) (arity := 1) rfl
  exact (writes.tail (.frame (.label (stepInArm exit.1) 1 []) 1 outside)).tail
    (.frame (.label (stepInArm exit.2) 1 []) 1 outside)

private theorem finish : Steps CallFrame.v1NoHost ⟨base, outside, root.code⟩ ⟨updated, outside, values [i32 word]⟩ := by
  let restored : Frame := { active 1 with locals := args 1 ++ [i32 word] }
  have recordWord : Step CallFrame.v1NoHost (inArm ⟨updated, active 1, values [i32 word] ++ recordTail⟩)
      (inArm ⟨updated, restored, []⟩) :=
    stepInArm (.localSet _ _ ⟨2⟩ (i32 word) (i32 0) rfl)
  have closeArm : Step CallFrame.v1NoHost (inArm ⟨updated, restored, []⟩)
      ⟨updated, restored, values saved ++ loadTail⟩ :=
    .context (.pure _ _ (.labelDone 0 [] [])) saved loadTail
  have callerBody := Steps.label (((Relation.ReflTransGen.single recordWord).tail closeArm).tail (loadWritten rfl)) 1 []
  have returned := resume.trans (callerBody.frame 1 outside)
  have exit := v1_function_fallthrough (H := Unit) (s := updated) (caller := outside)
    (callee := restored) (saved := []) (payload := [i32 word]) (tail := []) (arity := 1) rfl
  exact (returned.tail exit.1).tail exit.2

private theorem readback {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨base, outside, root.code⟩ dst) :
    ∃ out, Runs graph slot root out ∧ ReadyFor .fixed graph slot .recursive 1 before.size out ∧
      dst = render base slot memory out :=
  (v1_call_run_iff_at (root := address) (fn := fn) (index := ⟨0⟩) (args := args 1)
    (caller := outside) checked layout trivial rfl rfl rfl).mp path

-- Read back entry into a second activation of the same address, exact
-- resumption, and the outer return after the suspended caller loads the write.
example : ∃ out, Runs graph slot root out ∧ enteredSelf = render base slot memory out := by
  obtain ⟨out, path, _, eq⟩ := readback reachSelf
  exact ⟨out, path, eq⟩

example : ∃ out, Runs graph slot root out ∧ returnedToCaller = render base slot memory out := by
  obtain ⟨out, path, _, eq⟩ := readback resume
  exact ⟨out, path, eq⟩

example : ∃ out, Runs graph slot root out ∧
    (⟨updated, outside, values [i32 word]⟩ : Config Unit) = render base slot memory out := by
  obtain ⟨out, path, _, eq⟩ := readback finish
  exact ⟨out, path, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
