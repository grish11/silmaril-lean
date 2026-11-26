module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.V1.Execution.Properties

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution
open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution (Admin Config Step Steps Store values)

private abbrev i32 := Value.int .i32
private def firstPage : ByteArray := ⟨Array.replicate Memory.pageSize 0x5a⟩
private def secondPage : ByteArray := ⟨Array.replicate Memory.pageSize 0⟩
private def grown : ByteArray := firstPage ++ secondPage
private def memory : MemInst := ⟨firstPage, some 2⟩
private def sentinel : MemInst := ⟨⟨#[7, 8]⟩, none⟩
private def slot : MemAddr := ⟨1⟩
private def address : FuncAddr := ⟨0⟩
private def firstOfSecond := i32 (BitVec.ofNat 32 Memory.pageSize)

private def reader : Function :=
  ⟨⟨{ memories := [slot] }, ⟨0⟩, [], [], [.int .i32]⟩, 0, [firstOfSecond], [.load 0]⟩
private def program : Program := ⟨[some reader]⟩
private def base : Store Unit :=
  { memories := [sentinel, memory], funcs := [.wasm reader.declaration.type reader.declaration.module reader.v1Func] }
private def caller : Frame := ⟨[Value.int .i64 7], { funcs := [address], memories := [slot] }⟩
private def live : Store Unit := storeWithBytes base slot memory grown
private def current : MemInst := { memory with data := grown }

private theorem checked : program.checkV1 slot = true := rfl
private theorem layout : Layout program base slot memory where
  memory := rfl
  functions := by
    intro a target found
    rcases a with ⟨_ | _⟩ <;> simp [Program.lookup, program] at found
    subst target
    rfl

private theorem firstSize : firstPage.size = Memory.pageSize := by
  change (Array.replicate Memory.pageSize (0x5a : UInt8)).size = _
  simp

private theorem oldPages : Memory.size memory.data = 1 := by
  simp [Memory.size, memory, firstSize, Memory.pageSize]

private theorem aligned : memory.data.size % Memory.pageSize = 0 := by
  simp only [memory, firstSize, Nat.mod_self]

private theorem permits : MemoryGrow.SizeAllows memory 1 := by
  refine ⟨aligned, ?_, Or.inr ?_⟩
  · rw [oldPages]; decide
  · rw [oldPages]; decide

private theorem growEdge : MemoryGrow.Edge memory (.request 1) (.grown grown) :=
  MemoryGrow.fact (.grow 1 _ (MemoryGrow.grow_eq_some_iff.mpr ⟨permits, rfl⟩))

private theorem newPages : Memory.size grown = 2 := by
  have pages := MemoryGrow.grown_pages growEdge
  rw [oldPages] at pages
  exact pages

private theorem initialExtent : GrowthExtent memory memory.data := by
  have extent : MemoryGrow.SizeAllows memory 0 := by
    refine ⟨aligned, ?_, Or.inr ?_⟩
    · rw [oldPages]; decide
    · rw [oldPages]; decide
  exact ⟨Nat.le_refl _, extent⟩

example : GrowingStore base slot memory live := by
  have shared := GrowingStore.grow (base := base) (a := slot) initialExtent growEdge
  simp only [layout.initial_store] at shared
  exact shared

example : live.memories = [sentinel, current] ∧ live.funcs = base.funcs := ⟨rfl, rfl⟩

private theorem found : Wasm.V1.Execution.frameMemory base caller = some (slot, memory) := rfl
private theorem foundLive : Wasm.V1.Execution.frameMemory live caller = some (slot, current) := rfl

-- The in-limit request also has a resource-failure successor.
example : Step CallFrame.v1NoHost (MemoryGrow.v1Config base caller slot memory (.request 1))
    (MemoryGrow.v1Config base caller slot memory .failed) :=
  (MemoryGrow.v1_request_cases_iff found).mpr (.inl rfl)

private theorem overLimit : ¬ MemoryGrow.SizeAllows memory 2 := by
  intro permits
  rcases permits.2.2 with unbounded | limited
  · cases unbounded
  · rw [oldPages] at limited
    have impossible : 3 ≤ 2 := limited
    omega

-- A request for two more pages reaches only the failure configuration.
example {dst : Config Unit}
    (step : Step CallFrame.v1NoHost (MemoryGrow.v1Config base caller slot memory (.request 2)) dst) :
    dst = MemoryGrow.v1Config base caller slot memory .failed := by
  rcases (MemoryGrow.v1_request_cases_iff found).mp step with failure | ⟨permitted, _⟩
  · exact failure
  · exact (overLimit permitted).elim

-- The first instruction returns the old page count. The next reads the same
-- live allocation at its new extent, with the old result still on the stack.
private theorem growThenSize : Steps CallFrame.v1NoHost
    ⟨base, caller, (MemoryGrow.v1Config base caller slot memory (.request 1)).code ++ [.source .memorySize]⟩
    ⟨live, caller, values [i32 1, i32 2]⟩ := by
  have grow := MemoryGrow.v1_sound (host := CallFrame.v1NoHost) found growEdge
  rw [show MemoryGrow.v1Config base caller slot memory (.grown grown) = ⟨live, caller, values [i32 1]⟩ by
    simp only [MemoryGrow.v1Config, oldPages]; rfl] at grow
  have size := (MemoryGrow.v1_size_cases_iff (host := CallFrame.v1NoHost) foundLive).mpr rfl
  change Step CallFrame.v1NoHost ⟨live, caller, [.source .memorySize]⟩
    ⟨live, caller, values [i32 (BitVec.ofNat 32 (Memory.size grown))]⟩ at size
  rw [newPages] at size
  exact (Relation.ReflTransGen.single (.context grow [] [.source .memorySize])).tail (.context size [i32 1] [])

private theorem zeros : Memory.load grown Memory.pageSize 4 = some 0 := by
  unfold Memory.load Memory.readBytes
  have secondSize : secondPage.size = Memory.pageSize := by
    change (Array.replicate Memory.pageSize (0 : UInt8)).size = _
    simp
  have extent : Memory.pageSize + 4 ≤ grown.size := by
    simp only [grown, ByteArray.size_append, firstSize, secondSize]
    decide
  rw [ite_eq_left extent]
  have slice : grown.extract Memory.pageSize (Memory.pageSize + 4) = secondPage.extract 0 4 := by
    simpa only [grown, Nat.add_zero] using ByteArray.extract_append_size_add' (b := secondPage)
      (i := 0) (j := 4) firstSize.symm
  rw [slice]
  have four : secondPage.extract 0 4 = ⟨#[0, 0, 0, 0]⟩ := by
    apply ByteArray.ext
    simp only [ByteArray.data_extract, secondPage, Array.extract_replicate, Nat.sub_zero]
    rw [Nat.min_eq_left (by decide : 4 ≤ Memory.pageSize)]
    rfl
  rw [four]
  rfl

private theorem grownCall :
    Steps CallFrame.v1NoHost ⟨live, caller, [.source (.call ⟨0⟩)]⟩ ⟨live, caller, values [i32 0]⟩ := by
  let callee := reader.declaration.frame []
  have resolved : Step CallFrame.v1NoHost ⟨live, caller, [.source (.call ⟨0⟩)]⟩
      ⟨live, caller, [.invoke address]⟩ :=
    .call _ _ ⟨0⟩ address rfl
  have entered := (Relation.ReflTransGen.single resolved).tail
    ((layout.with_bytes grown).enter checked (address := address) (fn := reader)
      rfl (layout.with_bytes grown).initial_shared (saved := []) (args := []) (tail := []) rfl)
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 0)
    (address := BitVec.ofNat 32 Memory.pageSize) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory live callee = some (slot, current) from rfl)).mpr
    ⟨.value 0, MemoryQuery.fact_at (.load _ _ zeros), rfl⟩
  have read := entered.tail (Step.frame (Step.label load 1 []) 1 caller)
  exact (read.tail (Step.frame (.pure _ _ (.labelDone 1 [] [i32 0])) 1 caller)).tail
    (.pure _ _ (.frameDone 1 callee [i32 0] rfl))

-- The external grow and size prefix composes with the checked invocation.
example : Steps CallFrame.v1NoHost
    ⟨base, caller, (MemoryGrow.v1Config base caller slot memory (.request 1)).code ++
      [.source .memorySize, .source (.call ⟨0⟩)]⟩
    ⟨live, caller, values [i32 1, i32 2, i32 0]⟩ :=
  (growThenSize.context [] [.source (.call ⟨0⟩)]).trans (grownCall.context [i32 1, i32 2] [])

-- After rebasing the fixed-extent layout on the new bytes, the ranked call
-- reads a zero word from the appended page and preserves all allocations.
example : ∃ out, Runs program slot ⟨grown, caller, [.source (.call ⟨0⟩)]⟩ out ∧
    (⟨live, caller, values [i32 0]⟩ : Config Unit) = render live slot current out := by
  obtain ⟨out, trace, _, eq⟩ := (v1_call_run_iff (root := address) (fn := reader) (index := ⟨0⟩)
    (args := []) (caller := caller) checked (layout.with_bytes grown) rfl rfl).mp grownCall
  exact ⟨out, trace, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
