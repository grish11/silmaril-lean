module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IndirectExamples

open Execution.Runtime (Frame FuncInst MemInst TableInst Value)
open Wasm.Lime1.Execution
open Continuation (Label Op)
open CallContinuation.OuterCall (Declaration)
open CallContinuation.OuterCall.Ranked

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def expected : Wasm.Lime1.FuncType := ⟨[num64, num32], [num32, num64]⟩
private def wrong : Wasm.Lime1.FuncType := ⟨[num64, num32], [num64, num32]⟩
private def declaration : Declaration :=
  ⟨{types := [expected]}, ⟨0⟩, expected.params, [num64], expected.results⟩
private def wasmFn : Graph.Function := ⟨declaration, 0, [], [.numeric (.get ⟨1⟩), .numeric (.get ⟨0⟩)]⟩
private def trapFn : Graph.Function := ⟨declaration, 0, [], [.unreachable]⟩
private def wasmCallee : WasmTarget := ⟨⟨7⟩, wasmFn⟩
private def trapCallee : WasmTarget := ⟨⟨8⟩, trapFn⟩
private def graph : Graph.Program := ⟨[none, none, none, none, none, none, none, some wasmFn, some trapFn]⟩
private def table : TableInst := ⟨[some ⟨3⟩, none, some ⟨4⟩, some ⟨7⟩, some ⟨8⟩], none⟩
private def indirect : IndirectSite := ⟨⟨table, ⟨1⟩, expected⟩, graph, []⟩
private def prepare : Site Nat := ⟨⟨2⟩, ⟨[num64], [num64] ++ expected.params ++ [num32]⟩, 11⟩
private def target : Site Nat := ⟨⟨3⟩, expected, 12⟩
private def join : Site Nat := ⟨⟨5⟩, ⟨num64 :: expected.results, [num32]⟩, 14⟩
private def follow : Site Nat := ⟨⟨6⟩, ⟨[num64, num32], [num32]⟩, 15⟩
private def armTail : List (Op Nat) := [.call ⟨2⟩ join]
private def afterPrepare : List (Op Nat) := .callIndirect indirect :: armTail
private def arm : List (Op Nat) := .get ⟨0⟩ :: .call ⟨1⟩ prepare :: afterPrepare
private def afterArm : List (Op Nat) := [.call ⟨3⟩ follow]
private def label : Label Nat := ⟨.scalar num32, [i64 42], afterArm, none⟩

private def program : Program Nat where
  module := {
    types := [signature, expected]
    funcs := [⟨1⟩, ⟨2⟩, ⟨5⟩, ⟨6⟩]
    tables := [⟨0⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ (.scalar num32) arm arm :: afterArm
  saved := 42

private def base : Store Nat :=
  { memories := [initial], tables := [table], funcs :=
    [.wasm program.functionType program.module program.function, .host producerType 10,
      .host prepare.type prepare.code, .host expected 12, .host wrong 13,
      .host join.type join.code, .host follow.type follow.code,
      .wasm declaration.type declaration.module wasmFn.limeFunc,
      .wasm declaration.type declaration.module trapFn.limeFunc] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl, .fixed⟩
private def caller : Frame := ⟨[i32 9], {funcs := [⟨0⟩]}⟩
private abbrev Check := Continuation.Checked base program.module [num64]
private abbrev rootResults := [num32]

private theorem graphAllocated : graph.LimeAllocated base := by
  intro address fn found
  have bound : address.value < 9 := by
    by_contra outside
    have missing : graph.functions[address.value]? = none :=
      List.getElem?_eq_none (by change 9 ≤ address.value; omega)
    simp [Graph.Program.lookup, missing] at found
  have cases : address.value = 0 ∨ address.value = 1 ∨ address.value = 2 ∨
      address.value = 3 ∨ address.value = 4 ∨ address.value = 5 ∨ address.value = 6 ∨
      address.value = 7 ∨ address.value = 8 := by omega
  rcases cases with eq | eq | eq | eq | eq | eq | eq | eq | eq <;>
    simp [Graph.Program.lookup, graph, eq] at found
  all_goals
    subst fn
    change base.funcs[address.value]? = _
    rw [eq]
    rfl

private theorem linked : indirect.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, graphAllocated, ?_⟩
  intro address member
  simp [indirect, table] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨.host expected 12, rfl, fun _ => trivial⟩
  · exact ⟨.host wrong 13, rfl, fun _ => trivial⟩
  · exact ⟨.wasm declaration.type declaration.module wasmFn.limeFunc, rfl, fun _ => .inl ⟨wasmFn, rfl⟩⟩
  · exact ⟨.wasm declaration.type declaration.module trapFn.limeFunc, rfl, fun _ => .inl ⟨trapFn, rfl⟩⟩

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have afterLookup : Check [rootResults, rootResults] rootResults (num64 :: expected.results) armTail :=
    .call (site := join) (saved := []) rfl rfl .nil
  have atLookup : Check [rootResults, rootResults] rootResults
      (([num64] ++ expected.params) ++ [num32]) afterPrepare :=
    .callIndirect (site := indirect) (saved := [num64]) linked afterLookup
  have armChecked : Check [rootResults, rootResults] rootResults [] arm :=
    .get (type := num64) (stack := []) rfl (.call (site := prepare) (saved := []) rfl rfl atLookup)
  have tail : Check [rootResults] rootResults [num64, num32] afterArm :=
    .call (site := follow) (saved := []) rfl rfl .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl, .if_ (type := .scalar num32) (saved := [num64]) rfl armChecked armChecked tail,
    rfl, rfl⟩

private def saved : List Value := [i64 99]
private def args : List Value := [i64 71, i32 21]
private def returned : List Value := [i32 33, i64 77]

private def host : HostSemantics Nat := fun id store operands outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ operands = [i64 7] ∧
      outcome = .returned (memory.store (bytes 1)) (.values [i32 1, i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ operands = [i64 7] ∧ ∃ selector : BitVec 32,
      outcome = .returned (memory.store (bytes 2)) (.values ((saved ++ args) ++ [i32 selector]))
  | 12 => store = memory.store (bytes 2) ∧ operands = args ∧
      outcome = .returned (memory.store (bytes 3)) (.values returned)
  | 13 => store = memory.store (bytes 2) ∧ operands = args ∧
      outcome = .returned (memory.store (bytes 9)) (.values [i64 77, i32 33])
  | 14 => (store = memory.store (bytes 3) ∧ operands = saved ++ returned ∧
      outcome = .returned (memory.store (bytes 4)) (.values [i32 44])) ∨
      (store = memory.store (bytes 2) ∧ operands = saved ++ [i32 21, i64 71] ∧
        outcome = .returned (memory.store (bytes 6)) (.values [i32 45]))
  | 15 => (store = memory.store (bytes 4) ∧ operands = [i64 42, i32 44] ∧
      outcome = .returned (memory.store (bytes 5)) (.values [i32 55])) ∨
      (store = memory.store (bytes 6) ∧ operands = [i64 42, i32 45] ∧
        outcome = .returned (memory.store (bytes 7)) (.values [i32 56]))
  | _ => False

private theorem indirectContract : indirect.Contract memory host := by
  refine ⟨?_, fun callee found => ?_⟩
  swap
  · simp [IndirectSite.memoryLookup, indirect] at found
  intro address code member allocated
  simp [indirect, table] at member
  rcases member with rfl | rfl | rfl | rfl
  · change some (FuncInst.host expected 12 : FuncInst Wasm.Lime1.Func Nat) =
      some (.host expected code) at allocated
    have codeEq : 12 = code := (FuncInst.host.inj (Option.some.inj allocated)).2
    subst code
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 3, rfl, rfl, rfl⟩
  · change some (FuncInst.host wrong 13 : FuncInst Wasm.Lime1.Func Nat) =
      some (.host expected code) at allocated
    have bad : wrong = expected := congrArg FuncInst.type (Option.some.inj allocated)
    exact ((by decide : wrong ≠ expected) bad).elim

  · change some (FuncInst.wasm declaration.type declaration.module wasmFn.limeFunc : FuncInst Wasm.Lime1.Func Nat) =
      some (.host expected code) at allocated
    cases allocated
  · change some (FuncInst.wasm declaration.type declaration.module trapFn.limeFunc : FuncInst Wasm.Lime1.Func Nat) =
      some (.host expected code) at allocated
    cases allocated

private theorem contract : program.Contract memory host := by
  have prepareContract : prepare.Contract memory host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, selector, eq⟩ := answer
    cases eq
    exact ⟨bytes 2, rfl, rfl, rfl⟩
  have joinContract : join.Contract memory host := by
    intro _ _ _ _ _ _ answer
    rcases answer with ⟨_, _, eq⟩ | ⟨_, _, eq⟩
    · cases eq
      exact ⟨bytes 4, rfl, rfl, rfl⟩
    · cases eq
      exact ⟨bytes 6, rfl, rfl, rfl⟩
  have followContract : follow.Contract memory host := by
    intro _ _ _ _ _ _ answer
    rcases answer with ⟨_, _, eq⟩ | ⟨_, _, eq⟩
    · cases eq
      exact ⟨bytes 5, rfl, rfl, rfl⟩
    · cases eq
      exact ⟨bytes 7, rfl, rfl, rfl⟩
  have armContract : Continuation.Contract memory host arm :=
    .get (.call prepareContract (.callIndirect indirectContract (.call joinContract .nil)))
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 1, rfl, rfl, rfl⟩
  · exact .if_ armContract armContract (.call followContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) rootResults a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem atLookup (selector : BitVec 32) :
    BodyPath ⟨bytes 2, .source ((saved ++ args) ++ [i32 selector]) afterPrepare, [label]⟩ := by
  have producer : Path ⟨bytes 0, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨bytes 1, .source [i64 42, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have inside : BodyPath ⟨bytes 1, .source [] arm, [label]⟩ :=
    (exit.step (.if_ (saved := [i64 42]) (args := []) (guard := 1) rfl)).step (.block rfl)
  have preparing : BodyPath ⟨bytes 1, .invoke [] prepare [i64 7] afterPrepare, [label]⟩ :=
    (inside.step (.get rfl)).step (.resolve (saved := []) (args := [i64 7]) rfl)
  exact preparing.step (.returned (vs := (saved ++ args) ++ [i32 selector]) rfl rfl ⟨rfl, rfl, selector, rfl⟩)

private theorem dispatched : BodyPath ⟨bytes 2, .invoke saved target args armTail, [label]⟩ := by
  have found : indirect.Lookup base 0 (some (.host target)) :=
    .host (address := ⟨3⟩) (code := 12) rfl (show target.Allocated base from rfl)
  exact (atLookup 0).step (.callIndirect (saved := saved) (args := args) rfl found)

-- Lookup leaves a pending invocation under the live label and the same bytes.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 99), value (i64 71), value (i32 21),
      .invoke ⟨3⟩, .source (.call ⟨2⟩)], .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, dispatched, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, values [i32 55]⟩ := by
  have delivered : BodyPath ⟨bytes 3, .source (saved ++ returned) armTail, [label]⟩ :=
    dispatched.step (.returned (vs := returned) rfl rfl ⟨rfl, rfl, rfl⟩)
  have joined : BodyPath ⟨bytes 3, .invoke [] join (saved ++ returned) [], [label]⟩ :=
    delivered.step (.resolve (saved := []) (args := saved ++ returned) rfl)
  have result : BodyPath ⟨bytes 4, .source [i32 44] [], [label]⟩ :=
    joined.step (.returned (vs := [i32 44]) rfl rfl (.inl ⟨rfl, rfl, rfl⟩))
  have following : BodyPath ⟨bytes 4, .invoke [] follow [i64 42, i32 44] [], []⟩ :=
    (result.step .armResult).step (.resolve (saved := []) (args := [i64 42, i32 44]) rfl)
  have done : BodyPath ⟨bytes 5, .source [i32 55] [], []⟩ :=
    following.step (.returned (vs := [i32 55]) rfl rfl (.inl ⟨rfl, rfl, rfl⟩))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (done.step .labelResult).step .frameDone, rfl, rfl⟩

private theorem lookupTrap {selector : BitVec 32} (failure : indirect.Lookup base selector none) :
    BodyPath ⟨bytes 2, .trapped (saved ++ args) (Continuation.code armTail), [label]⟩ :=
  (atLookup selector).step (.callIndirect (saved := saved) (args := args) rfl failure)

-- Lookup failure consumes the selector and preserves the arguments and suffix
-- until native trap cleanup. The mismatched host's own outcome is irrelevant.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 99), value (i64 71), value (i32 21),
      .trap, .source (.call ⟨2⟩)], .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, lookupTrap (selector := 2) (.mismatch (fn := .host wrong 13) rfl rfl (by decide)), rfl, rfl⟩

example {dst : Config Nat} :
    Internal ⟨memory.store (bytes 2), program.active 7, values ((saved ++ args) ++ [i32 2]) ++
      .source (.callIndirect ⟨1⟩) :: Continuation.code armTail⟩ dst ↔
      dst = ⟨memory.store (bytes 2), program.active 7, values (saved ++ args) ++ .trap :: Continuation.code armTail⟩ :=
  IndirectSite.trap_iff (indirect := indirect) (selector := 2) linked (.mismatch (fn := .host wrong 13) rfl rfl (by decide))

private theorem unwind {stack : List Value}
    (trapped : BodyPath ⟨bytes 2, .trapped stack (Continuation.code armTail), [label]⟩) :
    Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ := by
  have inside : BodyPath ⟨bytes 2, .trapped [] [], [label]⟩ :=
    trapped.step (.erase (removed := stack) (cut := Continuation.code armTail)
      rfl rfl (.inr (by decide)))
  have outside : BodyPath ⟨bytes 2, .trapped [] [], []⟩ :=
    (inside.step .armTrap).step (.erase (removed := [i64 42]) (cut := Continuation.code afterArm)
      rfl rfl (.inl (by decide)))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (outside.step .labelTrap).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ :=
  unwind (lookupTrap (selector := (-1)) (.bounds rfl))

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ :=
  unwind (lookupTrap (selector := 1) (.null rfl))

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ :=
  unwind (lookupTrap (selector := 2) (.mismatch (fn := .host wrong 13) rfl rfl (by decide)))

private theorem BodyPath.wasmStep {callee : WasmTarget} {phase next : Graph.Phase}
    (path : BodyPath ⟨bytes 2, .wasm saved indirect callee phase armTail, [label]⟩)
    (found : graph.lookup callee.address = some callee.fn)
    (move : Graph.Layer callee.fn (fun target => graph.FrameEdge target.address) phase next) :
    BodyPath ⟨bytes 2, .afterWasm saved indirect callee armTail next, [label]⟩ :=
  path.step (.wasm ((graph.frameEdge_iff found).mpr move))

private theorem atWasm {selector : BitVec 32} {callee : WasmTarget}
    (found : indirect.Lookup base selector (some (.wasm callee))) :
    BodyPath ⟨bytes 2, .wasm saved indirect callee (.invoke args) armTail, [label]⟩ :=
  (atLookup selector).step (.callIndirect (saved := saved) (args := args) rfl found)

private def calleeFrame : Frame := declaration.frame args
private theorem normalEntered :
    BodyPath ⟨bytes 2, .wasm saved indirect wasmCallee (.label calleeFrame.locals (.running [] wasmFn.code))
      armTail, [label]⟩ := by
  have found : indirect.Lookup base 3 (some (.wasm wasmCallee)) :=
    .wasm rfl rfl (graphAllocated _ _ (show graph.lookup wasmCallee.address = some wasmFn from rfl)) rfl
  exact (atWasm found).wasmStep rfl (.enter args rfl)

-- Ordinary entry enters the actual selected Wasm function under the caller's
-- live label, with ordered arguments and its initialized local.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 99),
      .frame 2 calleeFrame [.label 2 [] [.source (.localGet ⟨1⟩), .source (.localGet ⟨0⟩)]],
      .source (.call ⟨2⟩)], .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, normalEntered, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 7), caller, values [i32 56]⟩ := by
  have readNarrow : BodyPath ⟨bytes 2, .wasm saved indirect wasmCallee
      (.label calleeFrame.locals (.running [i32 21] [.numeric (.get ⟨0⟩)])) armTail, [label]⟩ :=
    normalEntered.wasmStep rfl (.numeric (.get rfl))
  have completed : BodyPath ⟨bytes 2, .wasm saved indirect wasmCallee
      (.label calleeFrame.locals (.running [i32 21, i64 71] [])) armTail, [label]⟩ :=
    readNarrow.wasmStep rfl (.numeric (.get rfl))
  have popping : BodyPath ⟨bytes 2, .wasm saved indirect wasmCallee
      (.exit calleeFrame.locals (.values [i32 21, i64 71])) armTail, [label]⟩ :=
    completed.wasmStep rfl (.leaveValues _ _)
  have delivered : BodyPath ⟨bytes 2, .source (saved ++ [i32 21, i64 71]) armTail, [label]⟩ :=
    popping.wasmStep rfl (.leaveFrame _ _ rfl)
  have joined : BodyPath ⟨bytes 2, .invoke [] join (saved ++ [i32 21, i64 71]) [], [label]⟩ :=
    delivered.step (.resolve (saved := []) (args := saved ++ [i32 21, i64 71]) rfl)
  have result : BodyPath ⟨bytes 6, .source [i32 45] [], [label]⟩ :=
    joined.step (.returned (vs := [i32 45]) rfl rfl (.inr ⟨rfl, rfl, rfl⟩))
  have following : BodyPath ⟨bytes 6, .invoke [] follow [i64 42, i32 45] [], []⟩ :=
    (result.step .armResult).step (.resolve (saved := []) (args := [i64 42, i32 45]) rfl)
  have done : BodyPath ⟨bytes 7, .source [i32 56] [], []⟩ :=
    following.step (.returned (vs := [i32 56]) rfl rfl (.inr ⟨rfl, rfl, rfl⟩))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (done.step .labelResult).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ := by
  have found : indirect.Lookup base 4 (some (.wasm trapCallee)) :=
    .wasm rfl rfl (graphAllocated _ _ (show graph.lookup trapCallee.address = some trapFn from rfl)) rfl
  have entered : BodyPath ⟨bytes 2, .wasm saved indirect trapCallee
      (.label calleeFrame.locals (.running [] trapFn.code)) armTail, [label]⟩ :=
    (atWasm found).wasmStep rfl (.enter args rfl)
  have trapped : BodyPath ⟨bytes 2, .wasm saved indirect trapCallee
      (.label calleeFrame.locals (.trapped [] [])) armTail, [label]⟩ :=
    entered.wasmStep rfl (.unreachable _ [] [])
  have popping : BodyPath ⟨bytes 2, .wasm saved indirect trapCallee
      (.exit calleeFrame.locals .trap) armTail, [label]⟩ :=
    trapped.wasmStep rfl (.leaveTrap _)
  exact unwind (popping.wasmStep rfl (.leaveFrame _ .trap trivial))

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IndirectExamples
