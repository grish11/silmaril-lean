module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryFunctionBranchExamples

open Execution.Runtime (Frame FuncInst ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (Declaration)
open CallContinuation.OuterCall.Ranked
open IndexedLoop (Edge Program call_run_iff producerType)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private abbrev word : BitVec 32 := 0x04030201

private def empty : ByteArray := ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
private def written : ByteArray := ⟨#[0, 0, 0, 0, 0, 1, 2, 3, 4, 0]⟩
private def afterFallthrough : ByteArray := ⟨#[0, 1, 2, 3, 4, 1, 2, 3, 4, 0]⟩
private def signature : Wasm.Lime1.FuncType := ⟨[.int .i32, .int .i32], [.int .i32, .int .i32]⟩
private def calleeModule : ModuleInst := { types := [signature], memories := [⟨0⟩] }
private def decl : Declaration := ⟨calleeModule, ⟨0⟩, signature.params, [.int .i32], signature.results⟩
private def getMode : Graph.Memory32.Op := .ranked (.numeric (.get ⟨0⟩))
private def getGuard : Graph.Memory32.Op := .ranked (.numeric (.get ⟨1⟩))
private def getZero : Graph.Memory32.Op := .ranked (.numeric (.get ⟨2⟩))
private def payload : List Value := [i32 0, i32 word]
private def buildPayload : List Graph.Memory32.Op := [getZero, getZero, .load 5, getGuard]
private def branch (depth : LabelIdx) : Graph.Memory32.Op := .ranked (.brIf depth signature.results)
private def inner : List Graph.Memory32.Op := buildPayload ++ [branch ⟨1⟩, .store 1]
private def functionTail : List Graph.Memory32.Op := [.store 1, getZero, .load 5]
private def direct : List Graph.Memory32.Op := buildPayload ++ branch ⟨0⟩ :: functionTail
private def fn : Graph.Memory32.Function :=
  ⟨decl, 0, [i32 4, i32 0, i32 word], [.store 5, getMode, .if_ none inner []] ++ direct⟩
private def target : MemoryTarget := ⟨⟨0⟩, fn⟩
private def table : Execution.Runtime.TableInst := ⟨[some target.address], none⟩
private def site : IndirectSite := ⟨⟨table, ⟨1⟩, signature⟩, ⟨[]⟩, [some fn], .ranked⟩

example : MemoryTarget.supportedOp false (.if_ none (buildPayload ++ [branch ⟨2⟩, .store 1]) []) = false := by decide

-- The two operands are available, but the branch's declared result list is incompatible.
example : ¬ fn.WellTyped fn.initial
    ([.store 5, getMode, .if_ none inner []] ++ buildPayload ++
      .ranked (.brIf ⟨0⟩ [.int .i32]) :: functionTail) := by
  unfold Graph.Memory32.Function.WellTyped
  decide

private def keep : List Value := [i64 23]
private def prepare : Site Nat :=
  ⟨⟨3⟩, ⟨[.int .i64, .int .i32], [.int .i64, .int .i32, .int .i32, .int .i32]⟩, 1⟩
private def observe : Site Nat := ⟨⟨4⟩, ⟨[.int .i64] ++ signature.results, [.int .i32]⟩, 2⟩
private def observeTail : List (Continuation.Op Nat) := [.call ⟨2⟩ observe]
private def dispatch : List (Continuation.Op Nat) := .callIndirect site :: observeTail

private def program : Program Nat where
  module := {
    types := [IndexedLoop.signature, signature]
    funcs := [⟨2⟩, ⟨3⟩, ⟨4⟩]
    tables := [⟨0⟩], memories := [⟨0⟩] }
  rootAddress := ⟨1⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨2⟩
  producerCode := 0
  continuation := .call ⟨1⟩ prepare :: dispatch
  saved := 99

private def caller : Frame := ⟨[i32 17], { funcs := [program.rootAddress] }⟩
private def base : Store Nat :=
  { memories := [⟨empty, some 1⟩], tables := [table], funcs :=
    [.wasm signature calleeModule target.code, .wasm program.functionType program.module program.function,
      .host producerType 0, .host prepare.type 1, .host observe.type 2] }
private def mem : Memory32 base := ⟨⟨0⟩, ⟨empty, some 1⟩, rfl, .fixed⟩
private def prepResults (mode guard : BitVec 32) : List Value := keep ++ [i32 mode, i32 guard, i32 0]
private def host : HostSemantics Nat := fun code store operands outcome =>
  match code with
  | 0 => store = base ∧ operands = [i64 7] ∧ outcome = .returned base (.values [i32 1, i64 88, i32 0])
  | 1 => store = base ∧ operands = [i64 99, i32 1] ∧ ∃ mode guard : BitVec 32,
      outcome = .returned base (.values (prepResults mode guard))
  | 2 => (store = mem.store written ∧ operands = keep ++ payload ∧
        outcome = .returned (mem.store written) (.values [i32 42])) ∨
      (store = mem.store afterFallthrough ∧ operands = keep ++ [i32 4, i32 word] ∧
        outcome = .returned (mem.store afterFallthrough) (.values [i32 43]))
  | _ => False

private theorem registered {callee : MemoryTarget} (found : site.memoryLookup callee.address = some callee.fn) :
    callee = target := by
  rcases callee with ⟨⟨address⟩, entry⟩
  cases address <;> simp_all [IndirectSite.memoryLookup, site, target]

private theorem tableEntry {a : Execution.Runtime.FuncAddr} (entry : some a ∈ site.table.refs) :
    a = target.address := by simpa [site, table] using entry

private theorem linked : site.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro a entry found
    simp [site, Graph.Program.lookup] at found
  · intro a entry
    obtain rfl := tableEntry entry
    exact ⟨.wasm signature calleeModule target.code, rfl, fun _ => .inr ⟨fn, rfl, rfl⟩⟩

private theorem graphLinked : site.MemoryLinked mem host := by
  constructor
  · intro callee found
    obtain rfl := registered found
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro callee found call used
    obtain rfl := registered found
    simp [target, fn, inner, direct, buildPayload, branch, functionTail, getMode, getZero, getGuard,
      Graph.Memory32.Function.targets, Graph.Memory32.Op.targets, Graph.Memory32.codeTargets, Graph.Op.targets] at used
  · intro callee found index ty used
    obtain rfl := registered found
    simp [target, fn, inner, direct, buildPayload, branch, functionTail, getMode, getZero, getGuard,
      MemoryTarget.sourceOps, MemoryTarget.descendants] at used

private theorem programChecked : program.Checked mem caller ⟨0⟩ := by
  have observing : Continuation.Checked base program.module [.int .i64] [[.int .i32]]
      [.int .i32] observe.type.params observeTail :=
    .call (site := observe) (saved := []) rfl (show observe.Allocated base from rfl) .nil
  have calling : Continuation.Checked base program.module [.int .i64] [[.int .i32]]
      [.int .i32] prepare.type.results dispatch :=
    .callIndirect (saved := [.int .i64]) linked observing
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    .call (site := prepare) (saved := []) rfl (show prepare.Allocated base from rfl) calling, rfl, rfl⟩

private theorem programContract : program.Contract mem host := by
  have prepared : prepare.Contract mem host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, _, _, returned⟩ := answer
    cases returned
    exact ⟨empty, rfl, rfl, rfl⟩
  have observed : observe.Contract mem host := by
    intro _ _ _ _ _ _ answer
    rcases answer with ⟨_, _, returned⟩ | ⟨_, _, returned⟩ <;> cases returned
    · exact ⟨written, rfl, rfl, rfl⟩
    · exact ⟨afterFallthrough, rfl, rfl, rfl⟩
  have dispatched : site.Contract mem host := by
    refine ⟨?_, graphLinked⟩
    intro a code entry allocated
    obtain rfl := tableEntry entry
    cases (show some (.wasm signature calleeModule target.code : FuncInst Wasm.Lime1.Func Nat) =
      some (.host signature code) from allocated)
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨empty, rfl, rfl, rfl⟩
  · exact .call prepared (.callIndirect dispatched (.call observed .nil))

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program mem host 7) ⟨empty, .source⟩
private abbrev BodyPath (bytes : ByteArray) (phase : Continuation.Phase Nat) :=
  Path ⟨bytes, .continuation phase []⟩
private abbrev CalleePath (bytes : ByteArray) (phase : MemoryCallee.Phase Nat) :=
  BodyPath bytes (.memory keep site target phase observeTail)

private theorem CalleePath.step {bytes written : ByteArray} {p q : MemoryCallee.Phase Nat}
    (path : CalleePath bytes p) (step : MemoryCallee.Edge mem host site target bytes p written q) :
    BodyPath written (.afterMemory keep site target observeTail q) :=
  path.tail (.continuation (.memory step))

private def args (mode guard : BitVec 32) : List Value := [i32 mode, i32 guard]
private def scratch : List Value := [i32 4]

private theorem atSelect (mode guard : BitVec 32) :
    CalleePath written (.ifBlock (args mode guard) scratch none (MemoryCallee.selectArm mode inner []) direct) := by
  have producer : Path ⟨empty, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have answer : Edge program mem host 7 ⟨empty, .producerInvoke 7⟩ ⟨empty, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have loopDone : BodyPath empty (.source [i64 99, i32 1] program.continuation) :=
    (((producer.tail answer).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have preparing : BodyPath empty (.invoke [] prepare [i64 99, i32 1] dispatch) :=
    loopDone.tail (.continuation (.resolve (saved := []) (args := [i64 99, i32 1]) rfl))
  have atCall : BodyPath empty (.source (prepResults mode guard) dispatch) :=
    preparing.tail (.continuation (.returned (vs := prepResults mode guard) rfl rfl ⟨rfl, rfl, mode, guard, rfl⟩))
  have invoke : CalleePath empty (.invoke (args mode guard)) :=
    atCall.tail (.continuation (.callIndirect (saved := keep) (args := args mode guard) rfl
      (.memory (callee := target) rfl rfl (show target.Allocated base from rfl) rfl)))
  have entered : CalleePath empty (.body (args mode guard) fn.initial fn.code) := invoke.step .enter
  have stored : CalleePath written (.body (args mode guard) scratch (getMode :: .if_ none inner [] :: direct)) :=
    entered.step (.store (saved := scratch) (MemoryWrite.fact_at (.write 0 word written (by decide))))
  have test : CalleePath written (.body (args mode guard) (scratch ++ [i32 mode]) (.if_ none inner [] :: direct)) :=
    stored.step (.get (v := i32 mode) rfl)
  exact test.step .ifSelect

private theorem atDirect (guard : BitVec 32) :
    CalleePath written (.body (args 0 guard) (scratch ++ payload ++ [i32 guard]) (branch ⟨0⟩ :: functionTail)) := by
  have opened : CalleePath written (.arm (args 0 guard) scratch none (.body (args 0 guard) [] []) direct) :=
    (atSelect 0 guard).step .ifEnter
  have resumed : CalleePath written (.body (args 0 guard) scratch direct) := opened.step (.armStep rfl .labelDone)
  have first : CalleePath written (.body (args 0 guard) (scratch ++ [i32 0])
      (getZero :: .load 5 :: getGuard :: branch ⟨0⟩ :: functionTail)) :=
    resumed.step (.get (v := i32 0) rfl)
  have second : CalleePath written (.body (args 0 guard) ((scratch ++ [i32 0]) ++ [i32 0])
      (.load 5 :: getGuard :: branch ⟨0⟩ :: functionTail)) :=
    first.step (.get (v := i32 0) rfl)
  have loaded : CalleePath written (.body (args 0 guard) (scratch ++ payload)
      (getGuard :: branch ⟨0⟩ :: functionTail)) :=
    second.step (.load (saved := scratch ++ [i32 0]) (MemoryQuery.fact_at (.load 0 word (by decide))))
  exact loaded.step (.get (v := i32 guard) rfl)

private def inArm (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .arm (args 1 1) scratch none phase direct

private theorem pendingNested :
    CalleePath written (inArm (.branch (args 1 1) payload ⟨1⟩ signature.results [.store 1])) := by
  have opened : CalleePath written (inArm (.body (args 1 1) [] inner)) := (atSelect 1 1).step .ifEnter
  have first : CalleePath written (inArm (.body (args 1 1) [i32 0]
      [getZero, .load 5, getGuard, branch ⟨1⟩, .store 1])) :=
    opened.step (.armStep rfl (.get (v := i32 0) rfl))
  have second : CalleePath written (inArm (.body (args 1 1) [i32 0, i32 0] [.load 5, getGuard, branch ⟨1⟩, .store 1])) :=
    first.step (.armStep rfl (.get (v := i32 0) rfl))
  have loaded : CalleePath written (inArm (.body (args 1 1) payload [getGuard, branch ⟨1⟩, .store 1])) :=
    second.step (.armStep rfl (.load (saved := [i32 0]) (MemoryQuery.fact_at (.load 0 word (by decide)))))
  have test : CalleePath written (inArm (.body (args 1 1) (payload ++ [i32 1]) [branch ⟨1⟩, .store 1])) :=
    loaded.step (.armStep rfl (.get (v := i32 1) rfl))
  exact test.step (.armStep rfl (.brIf (stack := payload) (depth := ⟨1⟩)
    (result := signature.results) (rest := [.store 1]) (guard := 1)))

private theorem observeOnce {bytes : ByteArray} {vs : List Value} {n : BitVec 32}
    (resumed : BodyPath bytes (.source (keep ++ vs) observeTail))
    (typed : observe.Arguments (keep ++ vs)) (live : mem.Live bytes)
    (answer : host observe.code (mem.store bytes) (keep ++ vs) (.returned (mem.store bytes) (.values [i32 n]))) :
    Steps host launch ⟨mem.store bytes, caller, values [i32 n]⟩ := by
  have invoking : BodyPath bytes (.invoke [] observe (keep ++ vs) []) :=
    resumed.tail (.continuation (.resolve (saved := []) typed))
  have returned : BodyPath bytes (.source [i32 n] []) :=
    invoking.tail (.continuation (.returned live rfl answer))
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (returned.tail (.continuation .labelResult)).tail (.continuation .frameDone), live, rfl⟩

private theorem delivered {mode : BitVec 32} {rest : List Graph.Memory32.Op}
    (pending : CalleePath written (.branch (args mode 1) (scratch ++ payload) ⟨0⟩ signature.results rest)) :
    CalleePath written (.exit (args mode 1) (.values payload)) :=
  pending.step (.branchDone (scratch := scratch) (payload := payload) rfl)

private theorem directPending :
    CalleePath written (.branch (args 0 1) (scratch ++ payload) ⟨0⟩ signature.results functionTail) :=
  (atDirect 1).step (.brIf (stack := scratch ++ payload) (result := signature.results)
    (depth := ⟨0⟩) (rest := functionTail) (guard := 1))

private theorem loweredToFunction :
    CalleePath written (.branch (args 1 1) (scratch ++ payload) ⟨0⟩ signature.results direct) :=
  pendingNested.step (.armStep rfl (.branchLower (by decide)))

-- After one native lowering step, the implicit function label still has the pending branch and the function tail.
example : Steps host launch ⟨mem.store written, caller, program.functionCode 7
    (values keep ++ MemoryWrite.limeActivationCode 2 (decl.frame (args 1 1)) [] []
      (values (scratch ++ payload) ++ .source (.br ⟨0⟩) :: MemoryCallee.code direct) ++
      Continuation.code observeTail)⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, loweredToFunction, rfl, rfl⟩

-- Delivery discards the callee's scratch and instructions, leaving its frame in place.
example : Steps host launch ⟨mem.store written, caller, program.functionCode 7
    (values keep ++ [.frame 2 (decl.frame (args 1 1)) (values payload)] ++ Continuation.code observeTail)⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, delivered loweredToFunction, rfl, rfl⟩

-- Frame exit restores the saved caller operand and ordered payload with one copy of the source tail.
example : Steps host launch ⟨mem.store written, caller, program.functionCode 7
    (values (keep ++ payload) ++ Continuation.code observeTail)⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (delivered loweredToFunction).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨mem.store written, caller, values [i32 42]⟩ :=
  observeOnce ((delivered directPending).step .frameDone) rfl rfl (.inl ⟨rfl, rfl, rfl⟩)

example : Steps host launch ⟨mem.store written, caller, values [i32 42]⟩ :=
  observeOnce ((delivered loweredToFunction).step .frameDone) rfl rfl (.inl ⟨rfl, rfl, rfl⟩)

-- Zero preserves the operands for the store. The same continuation receives a different ordered result and store.
example : Steps host launch ⟨mem.store afterFallthrough, caller, values [i32 43]⟩ := by
  have fallthrough : CalleePath written (.body (args 0 0) (scratch ++ payload) functionTail) :=
    (atDirect 0).step (.brIf (stack := scratch ++ payload) (result := signature.results)
      (depth := ⟨0⟩) (rest := functionTail) (guard := 0))
  have stored : CalleePath afterFallthrough (.body (args 0 0) scratch [getZero, .load 5]) :=
    fallthrough.step (.store (saved := scratch) (MemoryWrite.fact_at (.write 0 word afterFallthrough (by decide))))
  have address : CalleePath afterFallthrough (.body (args 0 0) (scratch ++ [i32 0]) [.load 5]) :=
    stored.step (.get (v := i32 0) rfl)
  have loaded : CalleePath afterFallthrough (.body (args 0 0) [i32 4, i32 word] []) :=
    address.step (.load (saved := scratch) (MemoryQuery.fact_at (.load 0 word (by decide))))
  have label : CalleePath afterFallthrough (.exit (args 0 0) (.values [i32 4, i32 word])) := loaded.step .labelDone
  exact observeOnce (label.step .frameDone) rfl rfl (.inr ⟨rfl, rfl, rfl⟩)

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryFunctionBranchExamples
