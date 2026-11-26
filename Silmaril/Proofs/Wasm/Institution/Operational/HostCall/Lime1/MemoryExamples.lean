module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples

open Execution.Runtime (Frame MemInst ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (Declaration)
open CallContinuation.OuterCall.Ranked
open IndexedLoop (Program Edge call_run_iff producerType)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def arg : Wasm.V1.MemArg := Graph.Memory32.immediate 1
private abbrev word : BitVec 32 := 0x04030201

private def zero : ByteArray := ⟨#[0, 0, 0, 0, 0, 0]⟩
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def written : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 0xbb]⟩
private def initial : MemInst := ⟨zero, some 1⟩
private def signature : Wasm.Lime1.FuncType := ⟨[.int .i32], [.int .i64, .int .i32]⟩
private def hostType : Wasm.Lime1.FuncType := ⟨[.int .i32, .int .i64, .int .i32], [.int .i32]⟩
private def calleeModule : ModuleInst := { types := [signature], memories := [⟨1⟩] }
private def caller : Frame := ⟨[i64 111], { types := [signature], tables := [⟨0⟩], memories := [⟨1⟩] }⟩
private def callee (ptr : BitVec 32) : Frame := ⟨[i32 ptr], calleeModule⟩
private def callerSaved : List Value := [i32 23]
private def tail : List Admin := [.invoke ⟨1⟩]

private def fn : Graph.Memory32.Function where
  declaration := (⟨calleeModule, ⟨0⟩, signature.params, [], signature.results⟩ : Declaration)
  rank := 0
  initial := [i64 9, i32 0, i32 word]
  code := [.store 1, .ranked (.numeric (.get ⟨0⟩)), .load 1]

private def writeThenLoad : Wasm.Lime1.Func := fn.v1Func.toLime

-- Reuse the V1 graph's operator typing with Lime1's ordered result list.
example : fn.WellTyped fn.initial fn.code := by unfold Graph.Memory32.Function.WellTyped; decide
example : ¬ fn.WellTyped [i64 9, i64 0, i32 word] fn.code := by unfold Graph.Memory32.Function.WellTyped; decide

private def target : MemoryTarget := ⟨⟨0⟩, fn⟩
private def table : Execution.Runtime.TableInst := ⟨[some ⟨0⟩], none⟩
private def indirect : IndirectSite := ⟨⟨table, ⟨1⟩, signature⟩, ⟨[]⟩, [some fn]⟩
private def prepare : Site Nat := ⟨⟨4⟩, ⟨[.int .i64, .int .i32], [.int .i32, .int .i32, .int .i32]⟩, 9⟩
private def observe : Site Nat := ⟨⟨1⟩, hostType, 7⟩
private def afterLookup : List (Continuation.Op Nat) := [.call ⟨2⟩ observe]
private def lookupOps : List (Continuation.Op Nat) := .callIndirect indirect :: afterLookup

private def program : Program Nat where
  module := {
    types := [IndexedLoop.signature, signature]
    funcs := [⟨3⟩, ⟨4⟩, ⟨1⟩]
    tables := [⟨0⟩]
    memories := [⟨1⟩] }
  rootAddress := ⟨2⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨3⟩
  producerCode := 8
  continuation := .call ⟨1⟩ prepare :: lookupOps
  saved := 99

private def entryCaller : Frame := ⟨caller.locals, { caller.module with funcs := [⟨2⟩] }⟩

private def base : Store Nat :=
  { memories := [⟨⟨#[0xcc]⟩, none⟩, initial], tables := [table],
    funcs := [.wasm signature calleeModule writeThenLoad, .host hostType 7,
      .wasm program.functionType program.module program.function, .host producerType 8, .host prepare.type 9] }

private def mem : Memory32 base := ⟨⟨1⟩, initial, rfl, .fixed⟩
private def host : HostSemantics Nat := fun code store operands outcome =>
  code = 7 ∧ store = mem.store written ∧ operands = [i32 23, i64 9, i32 word] ∧
    outcome = .returned (mem.store written) (.values [i32 42])

private def launch (ptr : BitVec 32) : Config Nat :=
  ⟨mem.store before, caller, values (callerSaved ++ [i32 ptr, i32 0]) ++ [.source (.callIndirect ⟨0⟩)] ++ tail⟩

private def inCallee (ptr : BitVec 32) (bytes : ByteArray) (body : List Admin) : Config Nat :=
  ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode
    signature.results.length (callee ptr) callerSaved tail body⟩

private theorem atStore (ptr : BitVec 32) :
    Steps host (launch ptr) (inCallee ptr before (expression writeThenLoad.body)) := by
  have resolve : Step host (launch ptr)
      ⟨mem.store before, caller, values (callerSaved ++ [i32 ptr]) ++ [.invoke ⟨0⟩] ++ tail⟩ :=
    .context (.callIndirect _ _ ⟨0⟩ 0 _ ⟨0⟩ (.wasm signature calleeModule writeThenLoad)
      signature rfl rfl rfl rfl rfl) (callerSaved ++ [i32 ptr]) tail
  exact (Relation.ReflTransGen.single resolve).tail
    (.context (.invokeWasm _ caller ⟨0⟩ signature calleeModule writeThenLoad [i32 ptr] rfl rfl) callerSaved tail)

private def loadTail : List Admin := [.source (.localGet ⟨0⟩), .source (.intLoad .i32 none arg)]

private theorem writeStep (ptr : BitVec 32) :
    Step host (inCallee ptr before (expression writeThenLoad.body))
      (inCallee ptr written (values [i64 9] ++ loadTail)) := by
  have edge : MemoryWrite.EdgeAt before 1 (.store 0 word) (.written written) :=
    MemoryWrite.fact_at (.write 0 word written (by decide))
  exact (mem.activation_store_iff_at (bytes := before) (callee := callee ptr) (arg := arg) (ptr := 0) (word := word) (saved := [i64 9])
    (tail := loadTail) rfl rfl).mpr (.inl ⟨written, edge, rfl, rfl⟩)

private theorem atLoad (ptr : BitVec 32) :
    Steps host (launch ptr) (inCallee ptr written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load ptr))) :=
  ((atStore ptr).tail (writeStep ptr)).tail
    (.context (.frame (.label (.context (.localGet _ _ ⟨0⟩ (i32 ptr) rfl)
      [i64 9] [.source (.intLoad .i32 none arg)]) 2 []) 2 caller) callerSaved tail)

-- The first native prefix observes the callee's write before it loads a result.
example : Steps host (launch 0) (inCallee 0 written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load 0))) :=
  atLoad 0

example : Steps host (launch 0) ⟨mem.store written, caller, values [i32 42]⟩ := by
  have writtenPrefix := atLoad 0
  have loaded : Step host (inCallee 0 written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load 0)))
      (inCallee 0 written (values [i64 9, i32 word])) :=
    (MemoryWrite.lime_activation_load_step_iff_at (immediate := arg) (ptr := 0) (saved := [i64 9]) (tail := [])
      (mem.frameMemory_store (bytes := written) (active := callee 0) rfl)).mpr
      ⟨.value word, MemoryQuery.fact_at (.load 0 word (by decide)), rfl⟩
  have labelExited : Step host (inCallee 0 written (values [i64 9, i32 word]))
      ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee 0) (values [i64 9, i32 word])] ++ tail⟩ :=
    .context (.frame (.pure _ _ (.labelDone 2 [] [i64 9, i32 word])) 2 caller) callerSaved tail
  have calleeExited : Step host
      ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee 0) (values [i64 9, i32 word])] ++ tail⟩
      ⟨mem.store written, caller, values [i32 23, i64 9, i32 word] ++ tail⟩ :=
    .context (.pure _ _ (.frameDone 2 (callee 0) [i64 9, i32 word] rfl)) callerSaved tail
  have observed : Step host ⟨mem.store written, caller, values [i32 23, i64 9, i32 word] ++ tail⟩
      ⟨mem.store written, caller, values [i32 42]⟩ :=
    .invokeHost _ _ caller ⟨1⟩ hostType 7 [i32 23, i64 9, i32 word] (.values [i32 42])
      rfl rfl ⟨rfl, rfl, rfl, rfl⟩
  exact (((writtenPrefix.tail loaded).tail labelExited).tail calleeExited).tail observed

example : Steps host (launch (-1)) ⟨mem.store written, caller, [.trap]⟩ := by
  have writtenPrefix := atLoad (-1)
  have bounds : Step host (inCallee (-1) written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load (-1))))
      (inCallee (-1) written (values [i64 9] ++ [.trap])) :=
    (MemoryWrite.lime_activation_load_step_iff_at (immediate := arg) (ptr := -1) (saved := [i64 9]) (tail := [])
      (mem.frameMemory_store (bytes := written) (active := callee (-1)) rfl)).mpr
      ⟨.trap, MemoryQuery.load_trap_iff_at.mpr (by decide), rfl⟩
  have erased : Step host (inCallee (-1) written (values [i64 9] ++ [.trap])) (inCallee (-1) written [.trap]) :=
    .context (.frame (.label (.pure _ _ (.trapValues (i64 9) [] [])) 2 []) 2 caller) callerSaved tail
  have labelExited : Step host (inCallee (-1) written [.trap])
      ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee (-1)) [.trap]] ++ tail⟩ :=
    .context (.frame (.pure _ _ (.labelTrap 2 [])) 2 caller) callerSaved tail
  have calleeExited : Step host ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee (-1)) [.trap]] ++ tail⟩
      ⟨mem.store written, caller, values callerSaved ++ [.trap] ++ tail⟩ :=
    .context (.pure _ _ (.frameTrap 2 (callee (-1)))) callerSaved tail
  exact ((((writtenPrefix.tail bounds).tail erased).tail labelExited).tail calleeExited).tail
    (.pure _ _ (.trapValues (i32 23) [] tail))

/-! The same allocated callee runs in the checked mixed runner from ordinary
entry. The prepare host supplies a pointer choice without changing the bytes. -/

private def checkedHost : HostSemantics Nat := fun code store operands outcome =>
  match code with
  | 8 => store = mem.store zero ∧ operands = [i64 7] ∧
      outcome = .returned (mem.store before) (.values [i32 1, i64 88, i32 0])
  | 9 => store = mem.store before ∧ operands = [i64 99, i32 1] ∧ ∃ ptr : BitVec 32,
      outcome = .returned (mem.store before) (.values (callerSaved ++ [i32 ptr, i32 0]))
  | _ => host code store operands outcome

private theorem calleeChecked : target.Checked mem := ⟨rfl, rfl, rfl, rfl⟩

-- These guards reject a wrong address type and a function whose actual module
-- links a different memory, even though its ordered signature is unchanged.
example : ¬ ({ target with fn := { fn with initial := [i64 9, i64 0, i32 word] } } : MemoryTarget).Checked mem := by
  intro checked
  have wrong := checked.body
  change fn.checkCode (CallContinuation.OuterCall.Computed.Prefix.stackTypes [i64 9, i64 0, i32 word])
    fn.code = true at wrong
  contradiction

example : ¬ ({ target with fn := { fn with declaration :=
    { fn.declaration with module := { calleeModule with memories := [⟨0⟩] } } } } : MemoryTarget).Checked mem := by
  intro checked
  have slot := checked.slot
  change (some ⟨0⟩ : Option Execution.Runtime.MemAddr) = some ⟨1⟩ at slot
  contradiction

private theorem linked : indirect.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro address registered found
    simp [indirect, Graph.Program.lookup] at found
  · intro address member
    simp [indirect, table] at member
    subst address
    exact ⟨.wasm signature calleeModule writeThenLoad, rfl, fun _ => .inr ⟨fn, rfl, rfl⟩⟩

private theorem programChecked : program.Checked mem entryCaller ⟨0⟩ := by
  have suffix : Continuation.Checked base program.module [.int .i64] [[.int .i32]] [.int .i32]
      ([.int .i32] ++ signature.results) afterLookup :=
    .call (site := observe) (saved := []) rfl (show observe.Allocated base from rfl) .nil
  have lookup : Continuation.Checked base program.module [.int .i64] [[.int .i32]] [.int .i32]
      (([.int .i32] ++ signature.params) ++ [.int .i32]) lookupOps :=
    .callIndirect (saved := [.int .i32]) linked suffix
  exact ⟨rfl, rfl, rfl, rfl, rfl, .call (site := prepare) (saved := []) rfl (show prepare.Allocated base from rfl) lookup, rfl, rfl⟩

private theorem programContract : program.Contract mem checkedHost := by
  have prepared : prepare.Contract mem checkedHost := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, ptr, outcome⟩ := answer
    cases outcome
    exact ⟨before, rfl, rfl, rfl⟩
  have observed : observe.Contract mem checkedHost := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2.2
    exact ⟨written, rfl, rfl, rfl⟩
  have atSite : indirect.Contract mem checkedHost := by
    constructor
    · intro address code member allocated
      simp [indirect, table] at member
      subst address
      cases (show some (.wasm signature calleeModule writeThenLoad : Execution.Runtime.FuncInst Wasm.Lime1.Func Nat)
        = some (.host signature code) from allocated)
    · intro callee found
      rcases callee with ⟨address, registered⟩
      cases address with
      | mk address =>
        cases address with
        | zero =>
          change some fn = some registered at found
          cases found
          exact calleeChecked
        | succ => simp [IndirectSite.memoryLookup, indirect] at found
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨before, rfl, rfl, rfl⟩
  · exact .call prepared (.callIndirect atSite (.call observed .nil))

private def checkedLaunch : Config Nat :=
  ⟨base, entryCaller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩

private abbrev Path := Relation.ReflTransGen (Edge program mem checkedHost 7) ⟨zero, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge mem checkedHost (program.active 7) [.int .i32] a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem atCheckedLookup (ptr : BitVec 32) :
    BodyPath ⟨before, .source ((callerSaved ++ [i32 ptr]) ++ [i32 0]) lookupOps, []⟩ := by
  have producer : Path ⟨zero, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program mem checkedHost 7 ⟨zero, .producerInvoke 7⟩ ⟨before, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨before, .source [i64 99, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have preparing : BodyPath ⟨before, .invoke [] prepare [i64 99, i32 1] lookupOps, []⟩ :=
    exit.step (.resolve (saved := []) (args := [i64 99, i32 1]) rfl)
  exact preparing.step (.returned (vs := (callerSaved ++ [i32 ptr]) ++ [i32 0]) rfl rfl ⟨rfl, rfl, ptr, rfl⟩)

private theorem BodyPath.calleeStep {bytes next : ByteArray} {a b : MemoryCallee.Phase}
    (path : BodyPath ⟨bytes, .memory callerSaved target a afterLookup, []⟩)
    (move : MemoryCallee.Edge mem target bytes a next b) :
    BodyPath ⟨next, .afterMemory callerSaved target afterLookup b, []⟩ :=
  path.step (.memory move)

private theorem atCheckedLoad (ptr : BitVec 32) :
    BodyPath ⟨written, .memory callerSaved target (.body [i32 ptr] [i64 9, i32 ptr] [.load 1]) afterLookup, []⟩ := by
  have invoke : BodyPath ⟨before, .memory callerSaved target (.invoke [i32 ptr]) afterLookup, []⟩ :=
    (atCheckedLookup ptr).step (.callIndirect (saved := callerSaved) (args := [i32 ptr]) rfl
      (.memory (callee := target) rfl rfl (show target.Allocated base from rfl) rfl))
  have entered : BodyPath ⟨before, .memory callerSaved target (.body [i32 ptr] fn.initial fn.code) afterLookup, []⟩ :=
    invoke.calleeStep .enter
  have stored : BodyPath ⟨written, .memory callerSaved target
      (.body [i32 ptr] [i64 9] [.ranked (.numeric (.get ⟨0⟩)), .load 1]) afterLookup, []⟩ :=
    entered.calleeStep (.store (args := [i32 ptr]) (saved := [i64 9])
      (MemoryWrite.fact_at (.write 0 word written (by decide))))
  exact stored.calleeStep (.get (v := i32 ptr) rfl)

-- This endpoint is inside the callee, after the write and before the load.
example :
    Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller,
      program.functionCode 7 (MemoryWrite.limeActivationCode 2 (callee 0) callerSaved
        (Continuation.code afterLookup) (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load 0)))⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, atCheckedLoad 0, rfl, rfl⟩

example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, values [i32 42]⟩ := by
  have loaded : BodyPath ⟨written, .memory callerSaved target
      (.body [i32 0] [i64 9, i32 word] []) afterLookup, []⟩ :=
    (atCheckedLoad 0).calleeStep (.load (saved := [i64 9]) (MemoryQuery.fact_at (.load 0 word (by decide))))
  have poppedLabel : BodyPath ⟨written, .memory callerSaved target
      (.exit [i32 0] (.values [i64 9, i32 word])) afterLookup, []⟩ :=
    loaded.calleeStep .labelDone
  have resumed : BodyPath ⟨written, .source (callerSaved ++ [i64 9, i32 word]) afterLookup, []⟩ :=
    poppedLabel.calleeStep .frameDone
  have observed : BodyPath ⟨written, .invoke [] observe [i32 23, i64 9, i32 word] [], []⟩ :=
    resumed.step (.resolve (saved := []) (args := [i32 23, i64 9, i32 word]) rfl)
  have returned : BodyPath ⟨written, .source [i32 42] [], []⟩ :=
    observed.step (.returned (vs := [i32 42]) rfl rfl ⟨rfl, rfl, rfl, rfl⟩)
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (returned.step .labelResult).step .frameDone, rfl, rfl⟩

example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ := by
  have trapped : BodyPath ⟨written, .memory callerSaved target
      (.trapped [i32 (-1)] [i64 9] []) afterLookup, []⟩ :=
    (atCheckedLoad (-1)).calleeStep (.loadTrap (saved := [i64 9])
      (MemoryQuery.load_trap_iff_at.mpr (by decide)))
  have erased : BodyPath ⟨written, .memory callerSaved target
      (.trapped [i32 (-1)] [] []) afterLookup, []⟩ :=
    trapped.calleeStep (.erase (removed := [i64 9]) (cut := []) rfl rfl (.inl (by simp)))
  have poppedLabel : BodyPath ⟨written, .memory callerSaved target
      (.exit [i32 (-1)] .trap) afterLookup, []⟩ := erased.calleeStep .labelTrap
  have poppedFrame : BodyPath ⟨written, .trapped callerSaved (Continuation.code afterLookup), []⟩ :=
    poppedLabel.calleeStep .frameDone
  have discarded : BodyPath ⟨written, .trapped [] [], []⟩ :=
    poppedFrame.step (.erase (removed := callerSaved) (cut := Continuation.code afterLookup) rfl rfl
      (.inl (by simp [callerSaved])))
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (discarded.step .labelTrap).step .frameDone, rfl, rfl⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples
