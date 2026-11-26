module

import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.V1.Execution.Properties

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution
open CallContinuation.OuterCall.Ranked
open Graph.Memory32 (Function Op Program)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def expected : Wasm.V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩
private def wrongOrder : Wasm.V1.FuncType := ⟨expected.params.reverse, expected.results⟩
private def site : Site := ⟨⟨[some ⟨0⟩, none, some ⟨1⟩], some 3⟩, ⟨1⟩, expected⟩
private def memorySlot : MemAddr := ⟨0⟩
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def written : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def memory : MemInst := ⟨before, none⟩
private def word : BitVec 32 := 0x11223344
private def caller : Frame := ⟨[i32 99], { tables := [⟨0⟩], types := [wrongOrder, expected], memories := [memorySlot] }⟩
private def args := [i64 81, i32 word]
private def saved := [i32 0]
private def load : Admin := .source ((Op.load 1).v1)
private def tail : List Admin := [.source (.localSet ⟨0⟩), load]

private def writer : Function :=
  ⟨⟨{ memories := [memorySlot] }, ⟨0⟩, expected.params, [], expected.results⟩, 0, [i32 0],
    [.ranked (.numeric (.get ⟨1⟩)), .store 1, .ranked (.numeric (.get ⟨1⟩))]⟩
private def other : Function :=
  ⟨⟨{ memories := [memorySlot] }, ⟨0⟩, wrongOrder.params, [], wrongOrder.results⟩, 0, [],
    [.ranked (.numeric (.get ⟨0⟩))]⟩
private def program : Program := ⟨[some writer, some other]⟩
private def base : Store Unit :=
  { memories := [memory], tables := [site.table], funcs := [writer, other].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }

private theorem layout : Graph.Memory32.Layout program base memorySlot memory where
  memory := rfl
  functions := by
    intro addr fn found
    rcases addr with ⟨_ | _ | _⟩ <;> simp [Program.lookup, program] at found
    all_goals subst fn; rfl

private theorem checked : site.V1Checked program base caller where
  table := rfl
  signature := rfl
  targets := by
    intro a member
    simp [site] at member
    rcases member with rfl | rfl
    · exact ⟨writer, rfl⟩
    · exact ⟨other, rfl⟩

private theorem exact {index : TypeIdx} {selector : BitVec 32} {out : Outcome}
    (resolved : v1Resolve base caller index selector = some out) {dst : Config Unit} :
    Step CallFrame.v1NoHost (v1Source base caller index selector (saved ++ args) tail) dst ↔
      dst = v1Resolved base caller (saved ++ args) tail out := by
  rw [v1_step_iff]
  simp [resolved]

example : v1Resolve base caller site.typeIndex (-1) = some .bounds := rfl
example (dst : Config Unit) : Step CallFrame.v1NoHost
    (v1Source base caller site.typeIndex 0 (saved ++ args) tail) dst ↔
    dst = ⟨base, caller, values (saved ++ args) ++ .invoke ⟨0⟩ :: tail⟩ :=
  exact (out := .resolved ⟨0⟩) rfl

example (dst : Config Unit) := exact (dst := dst) (index := site.typeIndex) (selector := 1) (out := .null) rfl
example (dst : Config Unit) := exact (dst := dst) (index := site.typeIndex) (selector := 2) (out := .mismatch ⟨1⟩) rfl
example (dst : Config Unit) := exact (dst := dst) (index := site.typeIndex) (selector := -1) (out := .bounds) rfl

-- Bounds and null precede the type lookup, even with an absent type index.
example (dst : Config Unit) := exact (dst := dst) (index := ⟨2⟩) (selector := -1) (out := .bounds) rfl
example (dst : Config Unit) := exact (dst := dst) (index := ⟨2⟩) (selector := 1) (out := .null) rfl

private theorem stuck {s : Store Unit} {index : TypeIdx} {selector : BitVec 32} {dst : Config Unit}
    (failed : v1Resolve s caller index selector = none) :
    ¬ Step CallFrame.v1NoHost (v1Source s caller index selector (saved ++ args) tail) dst := by
  intro step
  obtain ⟨out, resolved, _⟩ := v1_step_iff.mp step
  rw [failed] at resolved
  cases resolved

example (dst : Config Unit) := stuck (dst := dst) (s := base) (index := ⟨2⟩) (selector := 0) rfl
example (dst : Config Unit) := stuck (dst := dst) (s := { base with funcs := [] }) (index := site.typeIndex) (selector := 0) rfl
example (dst : Config Unit) := stuck (dst := dst) (s := { base with tables := [] }) (index := site.typeIndex) (selector := 0) rfl

private def source : Config Unit := v1Source base caller site.typeIndex 0 (saved ++ args) tail
private def pending : Config Unit := v1Resolved base caller (saved ++ args) tail (.resolved ⟨0⟩)
private def callee : Frame := writer.declaration.frame args
private def updated : Store Unit := Graph.Memory32.storeWithBytes base memorySlot memory written
private def inCallee (s : Store Unit) (code : List Admin) : Config Unit :=
  v1Plug saved tail ⟨s, caller, [.frame 1 callee [.label 1 [] code]]⟩

private theorem entered : Step CallFrame.v1NoHost pending (inCallee base (expression writer.v1Func.body)) := by
  have move := layout.enter_rendered (address := ⟨0⟩) (fn := writer) rfl (by decide)
    (suspended := caller) (bytes := before) (args := args) rfl
  exact move.context saved tail

private theorem underFrame {s t : Store Unit} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, callee, a⟩ ⟨t, callee, b⟩) :
    Step CallFrame.v1NoHost (inCallee s a) (inCallee t b) :=
  .context (.frame (.label move 1 []) 1 caller) saved tail

private def afterWrite : Config Unit := inCallee updated [.source (.localGet ⟨1⟩)]
private theorem reachWrite : Steps CallFrame.v1NoHost source afterWrite := by
  have lookup : Step CallFrame.v1NoHost source pending := (exact (out := .resolved ⟨0⟩) rfl).mpr rfl
  have operands := underFrame
    (.context (.localGet base callee ⟨1⟩ (i32 word) rfl) [i32 0]
      [.source ((Op.store 1).v1), .source (.localGet ⟨1⟩)])
  have store : Step CallFrame.v1NoHost
      ⟨base, callee, values [i32 0, i32 word] ++ [.source ((Op.store 1).v1)]⟩ ⟨updated, callee, []⟩ :=
    (MemoryWrite.v1_context_store_step_iff_at (immediate := Graph.Memory32.immediate 1)
      (address := 0) (word := word) (saved := []) (tail := [])
      (show frameMemory base callee = some (memorySlot, memory) from rfl)).mpr
      ⟨.written written, MemoryWrite.fact_at (.write _ _ _ (by decide)), rfl⟩
  exact (((Relation.ReflTransGen.single lookup).tail entered).tail operands).tail
    (underFrame (.context store [] [.source (.localGet ⟨1⟩)]))

private def delivered : Config Unit := ⟨updated, caller, values (saved ++ [i32 word]) ++ tail⟩
private theorem deliver : Steps CallFrame.v1NoHost source delivered := by
  have result := underFrame (.localGet updated callee ⟨1⟩ (i32 word) rfl)
  have exit := Graph.Memory32.v1_function_fallthrough (s := updated) (caller := caller) (callee := callee)
    (saved := saved) (payload := [i32 word]) (tail := tail) (arity := 1) rfl
  exact ((reachWrite.tail result).tail exit.1).tail exit.2

private def resumed : Frame := { caller with locals := [i32 word] }
private def observed : Config Unit := ⟨updated, resumed, values [i32 word]⟩
private theorem observe : Steps CallFrame.v1NoHost source observed := by
  have record : Step CallFrame.v1NoHost delivered ⟨updated, resumed, values saved ++ [load]⟩ :=
    .context (.localSet updated caller ⟨0⟩ (i32 word) (i32 99) rfl) saved [load]
  have read : Step CallFrame.v1NoHost ⟨updated, resumed, values saved ++ [load]⟩ observed :=
    (MemoryWrite.v1_context_load_step_iff_at (immediate := Graph.Memory32.immediate 1)
      (address := 0) (saved := []) (tail := [])
      (show frameMemory updated resumed = some (memorySlot, { memory with data := written }) from rfl)).mpr
      ⟨.value word, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  exact (deliver.tail record).tail read

private def pendingState : Graph.Memory32.State := ⟨before, caller, values args ++ [.invoke ⟨0⟩]⟩

example : v1Resolve updated caller site.typeIndex 0 = some (.resolved ⟨0⟩) := rfl

example : ∃ out, Graph.Memory32.Edge program memorySlot pendingState out ∧
    inCallee base (expression writer.v1Func.body) =
      v1Plug saved tail (Graph.Memory32.render base memorySlot memory out) := by
  have ready := Graph.Memory32.invoke_ready (p := program) (m := memorySlot) (mode := .fixed)
    (calls := .ranked) (addr := ⟨0⟩) (fn := writer) (caller := caller) rfl args
    (show before.size = before.size from rfl)
  have rigid : Rigid base pendingState.code := .invoke ⟨_, rfl, rfl⟩
  have exactStep := v1_callee_step_iff (mode := .fixed) (calls := .ranked) (saved := saved) (tail := tail)
    (dst := inCallee base (expression writer.v1Func.body)) rfl layout trivial ready rigid
  obtain ⟨out, move, _, eq⟩ := exactStep.mp entered
  exact ⟨out, move, eq⟩

private theorem reflect (calls : Graph.Memory32.CallMode) {dst : Config Unit}
    (run : Steps CallFrame.v1NoHost source dst) (moved : dst ≠ source) :
    ∃ fn, program.lookup ⟨0⟩ = some fn ∧ ∃ out, Graph.Memory32.Runs program memorySlot pendingState out ∧
      Graph.Memory32.ReadyFor .fixed program memorySlot calls (fn.rank + 1) before.size out ∧
      v1CalleeEndpoint saved tail (Graph.Memory32.render base memorySlot memory out) dst := by
  have graph : program.checkV1 memorySlot .fixed calls = true := by cases calls <;> rfl
  have checkedRun := (site.v1_run_iff (dst := dst) (mode := .fixed) (bytes := before) graph layout trivial checked
    rfl (selector := 0) (address := ⟨0⟩) rfl (saved := saved) (args := args) (tail := tail) rfl).mp run
  exact checkedRun.resolve_left moved

-- Finite prefixes inside the callee and execution of the resumed native tail.
example (calls : Graph.Memory32.CallMode) := reflect calls reachWrite (by
  intro same
  have lengths := congrArg (fun cfg : Config Unit => cfg.code.length) same
  change 4 = 7 at lengths
  contradiction)

example (calls : Graph.Memory32.CallMode) := reflect calls observe (by
  intro same
  have lengths := congrArg (fun cfg : Config Unit => cfg.code.length) same
  change 1 = 7 at lengths
  contradiction)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
