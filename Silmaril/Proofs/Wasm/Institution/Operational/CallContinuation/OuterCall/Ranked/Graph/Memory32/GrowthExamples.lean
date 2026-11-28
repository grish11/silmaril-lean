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
private def program : Program := { functions := [some reader] }
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

private def mode := MemoryMode.growing memory.max
private def growerAddress : FuncAddr := ⟨1⟩
private def grower : Function :=
  ⟨⟨{ memories := [slot] }, ⟨0⟩, [.int .i32], [], [.int .i32]⟩,
    0, [], [.ranked (.numeric (.get ⟨0⟩)), .grow]⟩
private def growTarget : CallTarget := ⟨⟨0⟩, growerAddress, grower.declaration⟩
private def observer : Function :=
  ⟨⟨{ memories := [slot], funcs := [growerAddress] }, ⟨0⟩, [.int .i32], [.int .i32, .int .i32], [.int .i32]⟩,
    1, [firstOfSecond], [.ranked (.numeric (.get ⟨0⟩)), .ranked (.call growTarget),
      .ranked (.set ⟨1⟩), .size, .ranked (.set ⟨2⟩), .load 0]⟩
private def graph : Program := { functions := [some observer, some grower] }
private def graphBase : Store Unit :=
  { memories := [sentinel, memory], funcs := [observer, grower].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }
private def graphGrown := storeWithBytes graphBase slot memory grown
private theorem graphChecked : graph.checkV1 slot mode = true := rfl
private theorem graphLayout : Layout graph graphBase slot memory where
  memory := rfl
  functions := by
    intro a target found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, graph] at found
    all_goals subst target; rfl

example : graph.checkV1 slot = false := rfl
example : Function.checkV1 { grower with declaration := { grower.declaration with params := [.int .i64] } }
    slot mode = false := rfl
example : (Program.mk [some { observer with rank := 0 }, some grower] none).checkV1 slot mode = false := rfl
example : graph.checkV1 ⟨0⟩ mode = false := rfl

private def observerFrame (delta : BitVec 32) := observer.declaration.frame [i32 delta]
private def growerFrame (delta : BitVec 32) := grower.declaration.frame [i32 delta]
private def observedFrame (delta result : BitVec 32) : Frame :=
  { observerFrame delta with locals := [i32 delta, i32 result, i32 0] }
private def afterSize : List Admin := [.source (.localSet ⟨2⟩), .source ((Op.load 0).v1)]
private def afterCall : List Admin := [.source (.localSet ⟨1⟩), .source .memorySize] ++ afterSize

private def graphInput (delta : BitVec 32) : State :=
  ⟨memory.data, caller, values [i32 delta] ++ [.source (.call ⟨0⟩)]⟩

private def inObserver (c : Config Unit) : Config Unit :=
  ⟨c.store, caller, [.frame 1 c.frame [.label 1 [] c.code]]⟩
private def inGrower (delta : BitVec 32) (s : Store Unit) (code : List Admin) : Config Unit :=
  inObserver ⟨s, observerFrame delta,
    MemoryWrite.v1ActivationCode (some (.int .i32)) (growerFrame delta) [firstOfSecond] afterCall code⟩

private theorem observerStep {s s' : Store Unit} {f f' : Frame} {a b : List Admin}
    (step : Step CallFrame.v1NoHost ⟨s, f, a⟩ ⟨s', f', b⟩) :
    Step CallFrame.v1NoHost (inObserver ⟨s, f, a⟩) (inObserver ⟨s', f', b⟩) :=
  .frame (.label step 1 []) 1 caller

private theorem growerStep {delta : BitVec 32} {s s' : Store Unit} {a b : List Admin}
    (step : Step CallFrame.v1NoHost ⟨s, growerFrame delta, a⟩ ⟨s', growerFrame delta, b⟩) :
    Step CallFrame.v1NoHost (inGrower delta s a) (inGrower delta s' b) :=
  observerStep (.context (.frame (.label step 1 []) 1 (observerFrame delta)) [firstOfSecond] afterCall)

private def request (delta : BitVec 32) : Config Unit :=
  inGrower delta graphBase (values [i32 delta] ++ [.source .memoryGrow])

private theorem reachGrow (delta : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨graphBase, caller, (graphInput delta).code⟩ (request delta) := by
  have resolved : Step CallFrame.v1NoHost ⟨graphBase, caller, (graphInput delta).code⟩
      ⟨graphBase, caller, values [i32 delta] ++ [.invoke address]⟩ :=
    .context (.call _ _ ⟨0⟩ address rfl) [i32 delta] []
  have entered := (Relation.ReflTransGen.single resolved).tail
    (graphLayout.enter graphChecked (address := address) (fn := observer) rfl graphLayout.initial_shared
      (saved := []) (args := [i32 delta]) (tail := []) rfl)
  have arg := entered.tail (observerStep (.context (.localGet _ _ ⟨0⟩ (i32 delta) rfl)
    [firstOfSecond] ([.source (.call ⟨0⟩)] ++ afterCall)))
  have resolveChild := arg.tail (observerStep (.context (.call _ _ ⟨0⟩ growerAddress rfl)
    [firstOfSecond, i32 delta] afterCall))
  have enterChild := resolveChild.tail (observerStep (graphLayout.enter graphChecked
    (address := growerAddress) (fn := grower) rfl graphLayout.initial_shared
    (saved := [firstOfSecond]) (args := [i32 delta]) (tail := afterCall) rfl))
  exact enterChild.tail (growerStep (.context (.localGet _ _ ⟨0⟩ (i32 delta) rfl) [] [.source .memoryGrow]))

private theorem growSuccess :
    Step CallFrame.v1NoHost (request 1) (inGrower 1 graphGrown (values [i32 1])) := by
  have leaf := MemoryGrow.v1_sound (host := CallFrame.v1NoHost)
    (show Wasm.V1.Execution.frameMemory graphBase (growerFrame 1) = some (slot, memory) from rfl) growEdge
  simp only [MemoryGrow.v1Config, oldPages] at leaf
  exact growerStep leaf

private theorem growFailure (delta : BitVec 32) :
    Step CallFrame.v1NoHost (request delta) (inGrower delta graphBase (values [i32 (-1)])) :=
  growerStep (MemoryGrow.v1_sound
    (show Wasm.V1.Execution.frameMemory graphBase (growerFrame delta) = some (slot, memory) from rfl)
    (MemoryGrow.fact (.fail delta)))

private def sizeObserved (delta result pages : BitVec 32) (s : Store Unit) : Config Unit :=
  inObserver ⟨s, observedFrame delta result, values [firstOfSecond, i32 pages] ++ afterSize⟩

private theorem observeSize {delta result : BitVec 32} {s : Store Unit} {m : MemInst}
    (lookup : Wasm.V1.Execution.frameMemory s (observedFrame delta result) = some (slot, m)) :
    Steps CallFrame.v1NoHost (inGrower delta s (values [i32 result]))
      (sizeObserved delta result (BitVec.ofNat 32 (Memory.size m.data)) s) := by
  have leaveLabel := observerStep (.context (.frame (.pure (host := CallFrame.v1NoHost) s
    (growerFrame delta) (.labelDone 1 [] [i32 result])) 1 (observerFrame delta)) [firstOfSecond] afterCall)
  have leaveFrame := (Relation.ReflTransGen.single leaveLabel).tail (observerStep
    (.context (.pure _ _ (.frameDone 1 (growerFrame delta) [i32 result] rfl)) [firstOfSecond] afterCall))
  have recordResult := leaveFrame.tail (observerStep (.context (.localSet _ _ ⟨1⟩ (i32 result) (i32 0) rfl)
    [firstOfSecond] ([.source .memorySize] ++ afterSize)))
  exact recordResult.tail (observerStep
    (.context ((MemoryGrow.v1_size_cases_iff lookup).mpr rfl) [firstOfSecond] afterSize))

private theorem readGraph {delta : BitVec 32} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨graphBase, caller, (graphInput delta).code⟩ dst) :
    ∃ out, RunsAt mode graph slot (graphInput delta) out ∧ ReadyAt mode graph slot 2 memory.data.size out ∧
      dst = render graphBase slot memory out :=
  (v1_growing_call_run_iff (root := address) (fn := observer) (index := ⟨0⟩) (args := [i32 delta])
    (caller := caller) graphChecked graphLayout initialExtent.2 rfl rfl).mp path

-- Both call policies reflect both native allocations from the same pending
-- grow under a suspended caller.
example (calls : CallMode) : ∃ start success failure,
    RunsAt mode graph slot (graphInput 1) start ∧
    EdgeAt mode graph slot start success ∧ EdgeAt mode graph slot start failure ∧
    request 1 = render graphBase slot memory start ∧
    inGrower 1 graphGrown (values [i32 1]) = render graphBase slot memory success ∧
    inGrower 1 graphBase (values [i32 (-1)]) = render graphBase slot memory failure := by
  have checked : graph.checkV1 slot mode calls = true := by cases calls <;> rfl
  have fromEntry := v1_call_run_iff_at (dst := request 1) (root := address) (fn := observer) (index := ⟨0⟩) (args := [i32 1])
    (caller := caller) checked graphLayout rfl initialExtent rfl rfl
  obtain ⟨start, prefixRun, ready, eq⟩ := fromEntry.mp (reachGrow 1)
  have reflect := fun {dst : Config Unit} => (v1_step_iff_at (dst := dst) checked graphLayout rfl ready).mp
  obtain ⟨success, grows, _, grownEq⟩ := reflect (eq ▸ growSuccess)
  obtain ⟨failure, fails, _, failEq⟩ := reflect (eq ▸ growFailure 1)
  exact ⟨start, success, failure, prefixRun, grows, fails, eq, grownEq, failEq⟩

private theorem seesGrowth :
    Steps CallFrame.v1NoHost ⟨graphBase, caller, (graphInput 1).code⟩ (sizeObserved 1 1 2 graphGrown) := by
  have resumed := observeSize (delta := 1) (result := 1)
    (show Wasm.V1.Execution.frameMemory graphGrown (observedFrame 1 1) = some (slot, current) from rfl)
  change Steps CallFrame.v1NoHost _ (sizeObserved 1 1 (BitVec.ofNat 32 (Memory.size grown)) graphGrown) at resumed
  rw [newPages] at resumed
  exact ((reachGrow 1).tail growSuccess).trans resumed

example : ∃ out, RunsAt mode graph slot (graphInput 1) out ∧
    sizeObserved 1 1 2 graphGrown = render graphBase slot memory out := by
  obtain ⟨out, prefixRun, _, eq⟩ := readGraph seesGrowth
  exact ⟨out, prefixRun, eq⟩

example : ∃ out, RunsAt mode graph slot (graphInput 1) out ∧
    (⟨graphGrown, caller, values [i32 0]⟩ : Config Unit) = render graphBase slot memory out ∧
      GrowingStore graphBase slot memory graphGrown := by
  let updated := ({ observedFrame 1 1 with locals := [i32 1, i32 1, i32 2] } : Frame)
  have recordSize := seesGrowth.tail (observerStep (.context (.localSet _ _ ⟨2⟩ (i32 2) (i32 0) rfl)
    [firstOfSecond] [.source ((Op.load 0).v1)]))
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 0)
    (address := BitVec.ofNat 32 Memory.pageSize) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory graphGrown updated = some (slot, current) from rfl)).mpr
    ⟨.value 0, MemoryQuery.fact_at (.load _ _ zeros), rfl⟩
  have result := recordSize.tail (observerStep load)
  have done := (result.tail (.frame (.pure _ _ (.labelDone 1 [] [i32 0])) 1 caller)).tail
    (.pure _ _ (.frameDone 1 updated [i32 0] rfl))
  obtain ⟨out, trace, ready, eq⟩ := readGraph done
  have shared := render_growing (base := graphBase) ready
  rw [← eq] at shared
  exact ⟨out, trace, eq, shared⟩

-- Failure preserves the live bytes and the caller observes the old page count.
-- This prefix applies to both an in-limit failure and a limit failure.
example (delta : BitVec 32) : ∃ out, RunsAt mode graph slot (graphInput delta) out ∧
    sizeObserved delta (-1) 1 graphBase = render graphBase slot memory out := by
  have resumed := observeSize (delta := delta) (result := -1)
    (show Wasm.V1.Execution.frameMemory graphBase (observedFrame delta (-1)) = some (slot, memory) from rfl)
  rw [oldPages] at resumed
  obtain ⟨out, trace, _, eq⟩ := readGraph (((reachGrow delta).tail (growFailure delta)).trans resumed)
  exact ⟨out, trace, eq⟩

-- The callee at the limit-test site has only the native failure successor.
example {dst : Config Unit} (step : Step CallFrame.v1NoHost
    (MemoryGrow.v1Config graphBase (growerFrame 2) slot memory (.request 2)) dst) :
    dst = MemoryGrow.v1Config graphBase (growerFrame 2) slot memory .failed := by
  have found : Wasm.V1.Execution.frameMemory graphBase (growerFrame 2) = some (slot, memory) := rfl
  rcases (MemoryGrow.v1_request_cases_iff found).mp step with failure | ⟨permitted, _⟩
  · exact failure
  · exact (overLimit permitted).elim

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
