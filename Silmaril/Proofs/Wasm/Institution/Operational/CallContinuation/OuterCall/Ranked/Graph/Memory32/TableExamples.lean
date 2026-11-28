module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution (Admin Config Step Steps Store expression lowerLabel values)

private abbrev i32 := Value.int .i32
private def before : ByteArray := ⟨#[0xAA, 0xBB, 0xCC, 0, 0, 0, 0, 0xDD]⟩
private def after : ByteArray := ⟨#[0xAA, 0xBB, 0xCC, 0x44, 0x33, 0x22, 0x11, 0xDD]⟩
private def memory : MemInst := ⟨before, some 2⟩
private def sentinel : MemInst := ⟨⟨#[7, 8]⟩, none⟩
private def slot : MemAddr := ⟨1⟩
private def child : FuncAddr := ⟨0⟩
private def root : FuncAddr := ⟨1⟩

private def writer : Function :=
  ⟨⟨{ memories := [slot] }, ⟨0⟩, [], [], []⟩, 0, [i32 1, i32 0x11223344], [.store 2]⟩
private def target : CallTarget := ⟨⟨0⟩, child, writer.declaration⟩
private def depths : List LabelIdx := [⟨0⟩, ⟨1⟩, ⟨2⟩]
private def fallback : LabelIdx := ⟨3⟩

private def arm : List Op :=
  [.ranked (.call target), .ranked (.numeric (.get ⟨1⟩)), .ranked (.numeric (.get ⟨0⟩)),
    .ranked (.brTable depths fallback []), .ranked .unreachable]
private def body : List Op :=
  [.ranked (.numeric (.get ⟨1⟩)), .if_ none arm [], .ranked .unreachable]
private def fn : Function :=
  ⟨⟨{ funcs := [child], memories := [slot] }, ⟨0⟩, [.int .i32, .int .i32], [], []⟩, 1, [],
    [.block none [.loop none body, .ranked .unreachable], .ranked .unreachable]⟩
private def program : Program := { functions := [some writer, some fn] }
private def base : Store Unit :=
  { memories := [sentinel, memory], funcs := [writer, fn].map
      (fun f => .wasm f.declaration.type f.declaration.module f.v1Func) }
private theorem checked : program.checkV1 slot = true := rfl
private theorem layout : Layout program base slot memory where
  memory := rfl
  functions := by
    intro a callee found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, program] at found
    all_goals subst callee; rfl

-- These two rejections depend only on the listed and default depths in skipped code.
example : Function.checkV1 { fn with code := [.ranked .return_,
    .ranked (.brTable [⟨0⟩, ⟨1⟩] ⟨0⟩ [])] } slot = false := rfl
example : Function.checkV1 { fn with code := [.ranked .return_,
    .ranked (.brTable [⟨0⟩] ⟨1⟩ [])] } slot = false := rfl

-- Every reachable target must accept one common payload signature.
example : fn.checkRegion [.int .i32, .int .i32] []
    [.ranked (.brTable [⟨0⟩] ⟨1⟩ [.int .i32])] [[.int .i32], []] = false := rfl
example : fn.checkRegion [.int .i32, .int .i32] []
    [.ranked (.brTable [⟨1⟩] ⟨0⟩ [.int .i32])] [[.int .i32], [.int .i64]] = false := rfl
example : fn.checkRegion [.int .i32] []
    [.ranked (.brTable [] ⟨0⟩ [.int .i32])] [[.int .i32]] = false := rfl
example : fn.checkRegion [.int .i64] []
    [.ranked (.brTable [] ⟨0⟩ [])] [[]] = false := rfl
example : fn.checkRegion [.int .i32, .int .i32] []
    [.ranked (.brTable [⟨1⟩] ⟨0⟩ [.int .i32])] [[.int .i32], [.int .i32]] = true := rfl
example : fn.checkRegion [.int .i32] [] [.ranked (.brTable [] ⟨0⟩ [])] [[]] = true := rfl

private def args (selector : BitVec 32) := [i32 selector, i32 1]
private def active (selector : BitVec 32) := fn.declaration.frame (args selector)
private def caller : Frame := ⟨[i32 88], { funcs := [root] }⟩
private def input (selector : BitVec 32) : State :=
  ⟨before, caller, values (args selector) ++ [.source (.call ⟨0⟩)]⟩
private def live : Store Unit := storeWithBytes base slot memory after
private def loop : Wasm.V1.Instr := .loop none (v1Code body)
private def dead : List Admin := [.source .unreachable]
private def table : Admin := .source (.brTable depths fallback)
private def scratch := [i32 1]
private def operands : List Admin := [.source (.localGet ⟨1⟩), .source (.localGet ⟨0⟩), table] ++ dead

private def inFunction (c : Config Unit) : Config Unit :=
  ⟨c.store, caller, [.frame 0 c.frame [.label 0 [] c.code]]⟩
private def inBlock (c : Config Unit) : Config Unit :=
  inFunction ⟨c.store, c.frame, [.label 0 [] c.code] ++ dead⟩
private def inLoop (c : Config Unit) : Config Unit :=
  inBlock ⟨c.store, c.frame, [.label 0 [loop] c.code] ++ dead⟩
private def inArm (c : Config Unit) : Config Unit :=
  inLoop ⟨c.store, c.frame, [.label 0 [] c.code] ++ dead⟩

private theorem functionStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (inFunction ⟨s, f, a⟩) (inFunction ⟨s', f', b⟩) :=
  .frame (.label move 0 []) 0 caller

private theorem blockStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (inBlock ⟨s, f, a⟩) (inBlock ⟨s', f', b⟩) :=
  functionStep (.context (.label move 0 []) [] dead)

private theorem loopStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (inLoop ⟨s, f, a⟩) (inLoop ⟨s', f', b⟩) :=
  blockStep (.context (.label move 0 [loop]) [] dead)

private theorem armStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (inArm ⟨s, f, a⟩) (inArm ⟨s', f', b⟩) :=
  loopStep (.context (.label move 0 []) [] dead)

private theorem enterArm (selector : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨base, caller, (input selector).code⟩
      (inArm ⟨base, active selector, [.source (.call ⟨0⟩)] ++ operands⟩) := by
  have resolved : Step CallFrame.v1NoHost ⟨base, caller, (input selector).code⟩
      ⟨base, caller, values (args selector) ++ [.invoke root]⟩ :=
    .context (.call _ _ ⟨0⟩ root rfl) (args selector) []
  have entered := (Relation.ReflTransGen.single resolved).tail
    (layout.enter checked (address := root) (fn := fn) rfl layout.initial_shared
      (saved := []) (args := args selector) (tail := []) rfl)
  have openedBlock := entered.tail (functionStep (.context (.pure _ _
    (.block none [loop, .unreachable])) [] dead))
  have openedLoop := openedBlock.tail (blockStep (.context (.pure _ _ (.loop none (v1Code body))) [] dead))
  have condition := openedLoop.tail (loopStep (.context (.localGet _ _ ⟨1⟩ (i32 1) rfl) []
    ([.source (.if_ none (v1Code arm) [])] ++ dead)))
  have chosen := condition.tail (loopStep (.context (.pure _ _
    (.ifNonzero none (v1Code arm) [] 1 (by decide))) [] dead))
  exact chosen.tail (loopStep (.context (.pure _ _ (.block none (v1Code arm))) [] dead))

private def beforeTable (selector : BitVec 32) : Config Unit :=
  inArm ⟨live, active selector, values (scratch ++ [i32 selector]) ++ [table] ++ dead⟩

private theorem reachTable (selector : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨base, caller, (input selector).code⟩ (beforeTable selector) := by
  let callee := writer.declaration.frame []
  have resolved := (enterArm selector).tail (armStep (.context (.call _ _ ⟨0⟩ child rfl) [] operands))
  have entered := resolved.tail (armStep (layout.enter checked (address := child) (fn := writer)
    rfl layout.initial_shared (saved := []) (args := []) (tail := operands) rfl))
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost)
    (immediate := immediate 2) (address := 1) (word := 0x11223344) (caller := active selector) (result := none)
    (callerSaved := []) (callerTail := operands) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory base callee = some (slot, memory) from rfl)).mpr
    ⟨.written after, MemoryWrite.fact_at (.write _ _ _ rfl), rfl⟩
  have labelExit := (entered.tail (armStep write)).tail (armStep
    (.context (.frame (.pure _ _ (.labelDone 0 [] [])) 0 _) [] operands))
  have returned := labelExit.tail (armStep (.context (.pure _ _ (.frameDone 0 callee [] rfl)) [] operands))
  have saved := returned.tail (armStep (.context (.localGet _ _ ⟨1⟩ (i32 1) rfl) []
    ([.source (.localGet ⟨0⟩), table] ++ dead)))
  exact saved.tail (armStep (.context (.localGet _ _ ⟨0⟩ (i32 selector) rfl) scratch ([table] ++ dead)))

private def pending (depth : LabelIdx) : List Admin := values scratch ++ [.source (.br depth)] ++ dead
private def selected (selector : BitVec 32) (depth : LabelIdx) : Config Unit :=
  inArm ⟨live, active selector, pending depth⟩
private def inLoopBranch (selector : BitVec 32) (depth : LabelIdx) : Config Unit :=
  inLoop ⟨live, active selector, pending depth⟩
private def inBlockBranch (selector : BitVec 32) (depth : LabelIdx) : Config Unit :=
  inBlock ⟨live, active selector, pending depth⟩
private def inFunctionBranch (selector : BitVec 32) (depth : LabelIdx) : Config Unit :=
  inFunction ⟨live, active selector, pending depth⟩

private theorem select (selector : BitVec 32) :
    Step CallFrame.v1NoHost (beforeTable selector) (selected selector (depths[selector.toNat]?.getD fallback)) :=
  armStep ((v1_br_table_select_iff (saved := scratch) (tail := dead)).mpr rfl)

private theorem crossArm {selector : BitVec 32} {depth : LabelIdx} (h : depth.toNat ≠ 0) :
    Step CallFrame.v1NoHost (selected selector depth) (inLoopBranch selector (lowerLabel depth)) :=
  loopStep (.context (.pure _ _ (.labelBranchOuter 0 [] scratch dead depth h)) [] dead)
private theorem crossLoop {selector : BitVec 32} {depth : LabelIdx} (h : depth.toNat ≠ 0) :
    Step CallFrame.v1NoHost (inLoopBranch selector depth) (inBlockBranch selector (lowerLabel depth)) :=
  blockStep (.context (.pure _ _ (.labelBranchOuter 0 [loop] scratch dead depth h)) [] dead)
private theorem crossBlock {selector : BitVec 32} {depth : LabelIdx} (h : depth.toNat ≠ 0) :
    Step CallFrame.v1NoHost (inBlockBranch selector depth) (inFunctionBranch selector (lowerLabel depth)) :=
  functionStep (.context (.pure _ _ (.labelBranchOuter 0 [] scratch dead depth h)) [] dead)

private theorem readback {selector : BitVec 32} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨base, caller, (input selector).code⟩ dst) :
    ∃ out, Runs program slot (input selector) out ∧ Ready program slot 2 before.size out ∧
      dst = render base slot memory out :=
  (v1_call_run_iff (root := root) (fn := fn) (index := ⟨0⟩) (args := args selector) (caller := caller)
    checked layout rfl rfl).mp path

-- Selector zero reaches the if-arm exit and drops its scratch operand.
example : ∃ out, Runs program slot (input 0) out ∧
    inLoop ⟨live, active 0, dead⟩ = render base slot memory out := by
  have delivered : Step CallFrame.v1NoHost (selected 0 ⟨0⟩) (inLoop ⟨live, active 0, dead⟩) :=
    loopStep (.context (.pure _ _ (.labelBranch 0 [] scratch [] dead rfl)) [] dead)
  obtain ⟨out, trace, _, eq⟩ := readback (((reachTable 0).tail (select 0)).tail delivered)
  exact ⟨out, trace, eq⟩

private def waitingLoop : Config Unit := inBlock ⟨live, active 1, [.source loop] ++ dead⟩
private def nextLoop : Config Unit := inLoop ⟨live, active 1, expression (v1Code body)⟩

private theorem restartLoop : Step CallFrame.v1NoHost (inLoopBranch 1 ⟨0⟩) waitingLoop ∧
    Step CallFrame.v1NoHost waitingLoop nextLoop := by
  have steps := v1_loop_restart (s := live) (f := active 1) (result := none) (body := v1Code body)
    (saved := []) (scratch := scratch) (branchTail := dead) (tail := dead)
  exact ⟨blockStep steps.1, blockStep steps.2⟩

-- The indexed loop target has three distinct phases after selection. The
-- finite prefix stops just after re-entry, with the first callee's write.
example : ∃ chosen lowered waiting reentered,
    Runs program slot (input 1) chosen ∧ Edge program slot chosen lowered ∧
    Edge program slot lowered waiting ∧ Edge program slot waiting reentered ∧
    selected 1 ⟨1⟩ = render base slot memory chosen ∧
    inLoopBranch 1 ⟨0⟩ = render base slot memory lowered ∧
    waitingLoop = render base slot memory waiting ∧ nextLoop = render base slot memory reentered := by
  obtain ⟨chosen, trace, ready, eq⟩ := readback ((reachTable 1).tail (select 1))
  obtain ⟨lowered, crossed, lowReady, lowEq⟩ :=
    (v1_step_iff checked layout ready).mp (eq ▸ crossArm (selector := 1) (depth := ⟨1⟩) (by decide))
  obtain ⟨waiting, restart, waitReady, waitEq⟩ := (v1_step_iff checked layout lowReady).mp (lowEq ▸ restartLoop.1)
  obtain ⟨reentered, reenter, _, nextEq⟩ := (v1_step_iff checked layout waitReady).mp (waitEq ▸ restartLoop.2)
  exact ⟨chosen, lowered, waiting, reentered, trace, crossed, restart, reenter, eq, lowEq, waitEq, nextEq⟩

-- Index two exits the block and leaves the outer function tail in place.
example : ∃ out, Runs program slot (input 2) out ∧ inFunction ⟨live, active 2, dead⟩ = render base slot memory out := by
  have armExit := ((reachTable 2).tail (select 2)).tail (crossArm (depth := ⟨2⟩) (by decide))
  have loopExit := armExit.tail (crossLoop (depth := ⟨1⟩) (by decide))
  have delivered : Step CallFrame.v1NoHost (inBlockBranch 2 ⟨0⟩) (inFunction ⟨live, active 2, dead⟩) :=
    functionStep (.context (.pure _ _ (.labelBranch 0 [] scratch [] dead rfl)) [] dead)
  obtain ⟨out, trace, _, eq⟩ := readback (loopExit.tail delivered)
  exact ⟨out, trace, eq⟩

-- All one bits select the default under unsigned indexing. The function label
-- skips the outer tail and completes the frame with the callee's write intact.
example : ∃ out, Runs program slot (input 0xFFFFFFFF) out ∧
    (⟨live, caller, []⟩ : Config Unit) = render base slot memory out := by
  have armExit := ((reachTable 0xFFFFFFFF).tail (select 0xFFFFFFFF)).tail (crossArm (depth := ⟨3⟩) (by decide))
  have loopExit := armExit.tail (crossLoop (depth := ⟨2⟩) (by decide))
  have blockExit := loopExit.tail (crossBlock (depth := ⟨1⟩) (by decide))
  have exit := v1_function_branch_exit (s := live) (caller := caller) (callee := active 0xFFFFFFFF)
    (saved := []) (extra := scratch) (payload := []) (results := []) (bodyTail := dead) (callerTail := []) rfl
  obtain ⟨out, trace, _, eq⟩ := readback ((blockExit.tail exit.1).tail exit.2)
  exact ⟨out, trace, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
