module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples

open Execution.Runtime (Frame FuncInst MemInst ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Ranked
open IndexedLoop (Program Edge call_run_iff producerType)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def arg : Wasm.V1.MemArg := Graph.Memory32.immediate 1
private abbrev word : BitVec 32 := 0x04030201

private def zero : ByteArray := ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0, 0, 0, 0, 0xbb]⟩
private def written : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 0, 0, 0, 0, 0xbb]⟩
private abbrev nestedWord : BitVec 32 := 4
private def nestedWritten : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 4, 0, 0, 0, 0xbb]⟩
private def hostWritten : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 4, 0, 0, 0, 0xcc]⟩
private def hostTrapped : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 4, 0, 0, 0, 0xdd]⟩
private def directWritten : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 4, 0, 0, 0, 0xee]⟩
private def directTrapped : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 4, 0, 0, 0, 0xff]⟩
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
private def nestedHost : Site Nat := ⟨⟨8⟩, ⟨[.int .i64, .int .i32], signature.results⟩, 11⟩
private def hostOperands : List Value := [i64 17, i32 18]
private def hostCall : Graph.Memory32.Op :=
  .callIndirect ⟨1⟩ ⟨nestedHost.type.params, nestedHost.type.results⟩
private def nestedModule : ModuleInst :=
  { calleeModule with types := [signature, nestedHost.type], funcs := [nestedHost.address], tables := [⟨0⟩] }

private def directHost : CallTarget :=
  ⟨⟨0⟩, nestedHost.address, ⟨nestedModule, ⟨1⟩, nestedHost.type.params, [], nestedHost.type.results⟩⟩

private def hostTail : List Graph.Memory32.Op := [.ranked (.call directHost)]
private def hostOps : List Graph.Memory32.Op :=
  .ranked (.numeric (.get ⟨0⟩)) :: .load 5 :: hostCall :: hostTail
private def nestedFn : Graph.Memory32.Function :=
  { fn with
    declaration := { fn.declaration with module := nestedModule }
    initial := hostOperands ++ [i32 0, i32 nestedWord]
    code := .store 5 :: hostOps }
private def nestedTarget : MemoryTarget := ⟨⟨7⟩, nestedFn⟩
private def parentType : Wasm.Lime1.FuncType :=
  ⟨[.int .i32, .int .i32], [.int .i64] ++ signature.results ++ signature.results ++ [.int .i32]⟩

private def parentModule : ModuleInst :=
  { calleeModule with types := [parentType, signature], funcs := [⟨0⟩], tables := [⟨0⟩] }
private def direct : CallTarget := ⟨⟨0⟩, ⟨0⟩, fn.declaration⟩
private def reloadOps : List Graph.Memory32.Op := [.ranked (.numeric (.get ⟨0⟩)), .load 5]
private def nestedCall : Graph.Memory32.Op := .callIndirect ⟨1⟩ ⟨signature.params, signature.results⟩
private def nestedSite : List Graph.Memory32.Op := nestedCall :: reloadOps
private def afterDirect : List Graph.Memory32.Op :=
  [.ranked (.numeric (.get ⟨0⟩)), .ranked (.numeric (.get ⟨1⟩))] ++ nestedSite

private def parent : Graph.Memory32.Function where
  declaration := (⟨parentModule, ⟨0⟩, parentType.params, [], parentType.results⟩ : Declaration)
  rank := 1
  initial := [i64 13]
  code := .ranked (.numeric (.get ⟨0⟩)) :: .ranked (.call direct) :: afterDirect

private def parentTarget : MemoryTarget := ⟨⟨5⟩, parent⟩
private def table : Execution.Runtime.TableInst := ⟨[some ⟨0⟩, some ⟨5⟩, none, some ⟨7⟩, some ⟨8⟩], none⟩
private def indirect : IndirectSite :=
  ⟨⟨table, ⟨1⟩, parentType⟩, ⟨[]⟩, [some fn, none, none, none, none, some parent, none, some nestedFn], .ranked⟩
private def childResults : List Value := [i64 9, i32 word]
private def afterFirstChild : List Value := i64 13 :: childResults
private def indirectResults : List Value := [i64 19, i32 24]
private def nestedResults : List Value := [i64 29, i32 34]
private def afterSecondChild : List Value := afterFirstChild ++ nestedResults
private def observedStack : List Value := callerSaved ++ afterSecondChild ++ [i32 nestedWord]
private def prepare : Site Nat := ⟨⟨4⟩, ⟨[.int .i64, .int .i32], [.int .i32, .int .i32, .int .i32, .int .i32]⟩, 9⟩
private def observe : Site Nat := ⟨⟨6⟩, ⟨[.int .i32] ++ parentType.results, [.int .i32]⟩, 10⟩
private def afterLookup : List (Continuation.Op Nat) := [.call ⟨2⟩ observe]
private def lookupOps : List (Continuation.Op Nat) := .callIndirect indirect :: afterLookup

private def program : Program Nat where
  module := {
    types := [IndexedLoop.signature, parentType]
    funcs := [⟨3⟩, ⟨4⟩, ⟨6⟩]
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
      .wasm program.functionType program.module program.function, .host producerType 8, .host prepare.type 9,
      .wasm parentType parentModule parent.v1Func.toLime, .host observe.type 10, .wasm signature nestedModule nestedTarget.code, .host nestedHost.type nestedHost.code] }

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

/-! Ordinary entry selects the parent through the table. A direct child writes
first. A successful nested lookup runs a second child that writes another word,
then reaches the same host through an indirect site and a direct site.
Lookup failures retain the first child's write. -/

private def checkedHost : HostSemantics Nat := fun code store operands outcome =>
  match code with
  | 8 => store = mem.store zero ∧ operands = [i64 7] ∧
      outcome = .returned (mem.store before) (.values [i32 1, i64 88, i32 0])
  | 9 => store = mem.store before ∧ operands = [i64 99, i32 1] ∧ ∃ ptr selector : BitVec 32,
      outcome = .returned (mem.store before) (.values (callerSaved ++ [i32 ptr, i32 selector, i32 1]))
  | 10 => store = mem.store directWritten ∧ operands = observedStack ∧
      outcome = .returned (mem.store directWritten) (.values [i32 42])
  | 11 => (store = mem.store nestedWritten ∧ operands = hostOperands ∧
        (outcome = .returned (mem.store hostWritten) (.values indirectResults) ∨
          outcome = .returned (mem.store hostTrapped) .trap ∨ outcome = .diverged)) ∨
      (store = mem.store hostWritten ∧ operands = indirectResults ∧
        (outcome = .returned (mem.store directWritten) (.values nestedResults) ∨
          outcome = .returned (mem.store directTrapped) .trap))
  | _ => False

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

private theorem parentChecked : parentTarget.Checked mem := ⟨rfl, rfl, rfl, rfl⟩

private theorem directLinked : indirect.MemoryDirect (base := base) parentTarget direct target :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example : ¬ indirect.memoryCalls.permits 0 target.fn.rank := by decide

private theorem tableEntries {address : Execution.Runtime.FuncAddr}
    (member : some address ∈ indirect.table.refs) : address = ⟨0⟩ ∨ address = ⟨5⟩ ∨ address = ⟨7⟩ ∨ address = ⟨8⟩ := by
  simpa [indirect, table] using member

private theorem hostContract : nestedHost.Contract mem checkedHost := by
  intro _ _ _ _ _ _ answer
  rcases answer with indirectAnswer | directAnswer
  · rcases indirectAnswer.2.2 with returned | trapped | diverged
    · cases returned
      exact ⟨hostWritten, rfl, rfl, rfl⟩
    · cases trapped
      exact ⟨hostTrapped, rfl, rfl, trivial⟩
    · contradiction
  · rcases directAnswer.2.2 with returned | trapped
    · cases returned
      exact ⟨directWritten, rfl, rfl, rfl⟩
    · cases trapped
      exact ⟨directTrapped, rfl, rfl, trivial⟩

private theorem directHostLinked : MemoryDirectHost mem checkedHost nestedTarget directHost nestedHost.code :=
  ⟨rfl, rfl, hostContract⟩

-- The function index still resolves. The checked profile rejects the site's
-- incompatible declaration because neither allocation proof is possible.
private def wrongDirect : CallTarget :=
  { directHost with declaration := { directHost.declaration with params := signature.params } }

example : nestedModule.funcs[wrongDirect.index.toNat]? = some wrongDirect.address := rfl

example : ¬ ((∃ child, indirect.MemoryDirect (base := base) nestedTarget wrongDirect child) ∨
    ∃ code, MemoryDirectHost mem checkedHost nestedTarget wrongDirect code) := by
  rintro (⟨child, link⟩ | ⟨code, link⟩)
  · have allocated := link.allocated
    unfold MemoryTarget.Allocated at allocated
    rw [link.address] at allocated
    change some (.host nestedHost.type nestedHost.code : FuncInst Wasm.Lime1.Func Nat) = some (.wasm _ _ _)
      at allocated
    cases allocated
  · have allocated := link.allocated
    change some (.host nestedHost.type nestedHost.code : FuncInst Wasm.Lime1.Func Nat) =
      some (.host signature code) at allocated
    exact (show nestedHost.type ≠ signature from by decide) (congrArg FuncInst.type (Option.some.inj allocated))

private theorem nestedLinked :
    indirect.MemoryIndirect mem checkedHost parentTarget ⟨1⟩ ⟨signature.params, signature.results⟩ := by
  refine ⟨rfl, rfl, fun address member => ?_⟩
  rcases tableEntries member with rfl | rfl | rfl | rfl
  · exact ⟨.wasm signature calleeModule writeThenLoad, rfl, fun _ => ⟨fn, rfl, rfl, by decide⟩⟩
  · refine ⟨.wasm parentType parentModule parent.v1Func.toLime, rfl, fun wrong => ?_⟩
    change parentType = signature at wrong
    contradiction
  · exact ⟨.wasm signature nestedModule nestedTarget.code, rfl, fun _ => ⟨nestedFn, rfl, rfl, by decide⟩⟩

  · exact ⟨.host nestedHost.type nestedHost.code, rfl, fun wrong => by
      change nestedHost.type = signature at wrong
      contradiction⟩

private theorem hostLinked :
    indirect.MemoryIndirect mem checkedHost nestedTarget ⟨1⟩ ⟨nestedHost.type.params, nestedHost.type.results⟩ := by
  refine ⟨rfl, rfl, fun address member => ?_⟩
  rcases tableEntries member with rfl | rfl | rfl | rfl
  · exact ⟨.wasm signature calleeModule writeThenLoad, rfl, fun wrong => by
      change signature = nestedHost.type at wrong
      contradiction⟩
  · exact ⟨.wasm parentType parentModule parent.v1Func.toLime, rfl, fun wrong => by
      change parentType = nestedHost.type at wrong
      contradiction⟩
  · exact ⟨.wasm signature nestedModule nestedTarget.code, rfl, fun wrong => by
      change signature = nestedHost.type at wrong
      contradiction⟩
  · exact ⟨.host nestedHost.type nestedHost.code, rfl, fun _ => hostContract⟩

example : ¬ indirect.MemoryIndirect mem checkedHost
    { parentTarget with fn := { parent with rank := 0 } } ⟨1⟩ ⟨signature.params, signature.results⟩ := by
  intro link
  obtain ⟨allocated, seen, targetAt⟩ := link.entries ⟨0⟩ (by decide)
  change some (.wasm signature calleeModule writeThenLoad : FuncInst Wasm.Lime1.Func Nat) = some allocated at seen
  cases seen
  obtain ⟨_, _, _, smaller⟩ := targetAt rfl
  exact Nat.not_lt_zero _ smaller

private theorem linked : indirect.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro address registered found
    simp [indirect, Graph.Program.lookup] at found
  · intro address member
    rcases tableEntries member with rfl | rfl | rfl | rfl
    · exact ⟨.wasm signature calleeModule writeThenLoad, rfl, fun same => by
        change signature = parentType at same
        contradiction⟩
    · exact ⟨.wasm parentType parentModule parent.v1Func.toLime, rfl, fun _ => .inr ⟨parent, rfl, rfl⟩⟩
    · exact ⟨.wasm signature nestedModule nestedTarget.code, rfl, fun same => by
        change signature = parentType at same
        contradiction⟩
    · exact ⟨.host nestedHost.type nestedHost.code, rfl, fun _ => trivial⟩

private theorem registered {callee : MemoryTarget}
    (found : indirect.memoryLookup callee.address = some callee.fn) :
    callee = target ∨ callee = parentTarget ∨ callee = nestedTarget := by
  rcases callee with ⟨⟨address⟩, fnAt⟩
  rcases address with _ | _ | _ | _ | _ | _ | _ | _ | address <;>
    simp_all [IndirectSite.memoryLookup, indirect, target, parentTarget, nestedTarget]

private theorem programChecked : program.Checked mem entryCaller ⟨0⟩ := by
  have suffix : Continuation.Checked base program.module [.int .i64] [[.int .i32]] [.int .i32]
      ([.int .i32] ++ parentType.results) afterLookup :=
    .call (site := observe) (saved := []) rfl (show observe.Allocated base from rfl) .nil
  have lookup : Continuation.Checked base program.module [.int .i64] [[.int .i32]] [.int .i32]
      (([.int .i32] ++ parentType.params) ++ [.int .i32]) lookupOps :=
    .callIndirect (saved := [.int .i32]) linked suffix
  exact ⟨rfl, rfl, rfl, rfl, rfl, .call (site := prepare) (saved := []) rfl (show prepare.Allocated base from rfl) lookup, rfl, rfl⟩

private theorem programContract : program.Contract mem checkedHost := by
  have prepared : prepare.Contract mem checkedHost := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, _, _, outcome⟩ := answer
    cases outcome
    exact ⟨before, rfl, rfl, rfl⟩
  have observed : observe.Contract mem checkedHost := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨directWritten, rfl, rfl, rfl⟩
  have atSite : indirect.Contract mem checkedHost := by
    constructor
    · intro address code member allocated
      rcases tableEntries member with rfl | rfl | rfl | rfl
      · cases (show some (.wasm signature calleeModule writeThenLoad : Execution.Runtime.FuncInst Wasm.Lime1.Func Nat)
          = some (.host parentType code) from allocated)
      · cases (show some (.wasm parentType parentModule parent.v1Func.toLime : Execution.Runtime.FuncInst Wasm.Lime1.Func Nat)
          = some (.host parentType code) from allocated)
      · cases (show some (.wasm signature nestedModule nestedTarget.code : FuncInst Wasm.Lime1.Func Nat)
          = some (.host parentType code) from allocated)
      · have wrong := congrArg FuncInst.type (Option.some.inj (show
            some (.host nestedHost.type nestedHost.code : FuncInst Wasm.Lime1.Func Nat) =
              some (.host parentType code) from allocated))
        change nestedHost.type = parentType at wrong
        contradiction
    · refine ⟨?_, ?_, ?_⟩
      · intro callee found
        rcases registered found with rfl | rfl | rfl
        · exact calleeChecked
        · exact parentChecked
        · exact ⟨rfl, rfl, rfl, rfl⟩
      · intro callee found call used
        rcases registered found with rfl | rfl | rfl
        · simp [target, fn, Graph.Memory32.Function.targets, Graph.Memory32.Op.targets, Graph.Op.targets] at used
        · have same : call = direct := by
            simpa [parentTarget, parent, afterDirect, nestedSite, nestedCall, reloadOps, Graph.Memory32.Function.targets,
              Graph.Memory32.Op.targets, Graph.Op.targets] using used
          subst call
          exact .inl ⟨target, directLinked, by decide⟩
        · have same : call = directHost := by
            simpa [nestedTarget, nestedFn, hostOps, hostCall, hostTail, Graph.Memory32.Function.targets,
              Graph.Memory32.Op.targets, Graph.Op.targets] using used
          subst call
          exact .inr ⟨nestedHost.code, directHostLinked⟩
      · intro callee found index sig used
        rcases registered found with rfl | rfl | rfl
        · simp [target, fn, MemoryTarget.sourceOps, MemoryTarget.descendants] at used
        · have same : Graph.Memory32.Op.callIndirect index sig = nestedCall := by
            simpa [parentTarget, parent, afterDirect, nestedSite, nestedCall, reloadOps, MemoryTarget.sourceOps, MemoryTarget.descendants] using used
          change Graph.Memory32.Op.callIndirect index sig =
            .callIndirect ⟨1⟩ ⟨signature.params, signature.results⟩ at same
          have pair := Graph.Memory32.Op.callIndirect.inj same
          rcases pair with ⟨rfl, rfl⟩
          exact nestedLinked
        · have same : Graph.Memory32.Op.callIndirect index sig = hostCall := by
            simpa [nestedTarget, nestedFn, hostOps, hostCall, hostTail, MemoryTarget.sourceOps, MemoryTarget.descendants] using used
          change Graph.Memory32.Op.callIndirect index sig =
            .callIndirect ⟨1⟩ ⟨nestedHost.type.params, nestedHost.type.results⟩ at same
          obtain ⟨rfl, rfl⟩ := Graph.Memory32.Op.callIndirect.inj same
          exact hostLinked
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

private theorem atCheckedLookup (ptr selector : BitVec 32) :
    BodyPath ⟨before, .source ((callerSaved ++ [i32 ptr, i32 selector]) ++ [i32 1]) lookupOps, []⟩ := by
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
  exact preparing.step (.returned (vs := (callerSaved ++ [i32 ptr, i32 selector]) ++ [i32 1]) rfl rfl ⟨rfl, rfl, ptr, selector, rfl⟩)

private abbrev ParentPath (bytes : ByteArray) (phase : MemoryCallee.Phase Nat) :=
  BodyPath ⟨bytes, .memory callerSaved indirect parentTarget phase afterLookup, []⟩

private theorem BodyPath.calleeStep {bytes next : ByteArray} {a b : MemoryCallee.Phase Nat}
    (path : ParentPath bytes a) (move : MemoryCallee.Edge mem checkedHost indirect parentTarget bytes a next b) :
    BodyPath ⟨next, .afterMemory callerSaved indirect parentTarget afterLookup b, []⟩ :=
  path.step (.memory move)

private def suspended (ptr selector : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .child [i32 ptr, i32 selector] [i64 13] target phase afterDirect

private theorem BodyPath.childStep {bytes next : ByteArray} {args saved : List Value} {rest : List Graph.Memory32.Op}
    {child : MemoryTarget} {a b : MemoryCallee.Phase Nat}
    (path : ParentPath bytes (.child args saved child a rest))
    (move : MemoryCallee.Edge mem checkedHost indirect child bytes a next b) :
    ParentPath next (MemoryCallee.afterChild args saved child rest b) := by
  cases b with
  | done out => cases out <;> exact path.calleeStep (.child move)
  | _ => exact path.calleeStep (.child move)

private theorem atCheckedLoad (ptr selector : BitVec 32) :
    ParentPath written (suspended ptr selector (.body [i32 ptr] [i64 9, i32 ptr] [.load 1])) := by
  have invoke : ParentPath before (.invoke [i32 ptr, i32 selector]) :=
    (atCheckedLookup ptr selector).step (.callIndirect (saved := callerSaved) (args := [i32 ptr, i32 selector]) rfl
      (.memory (callee := parentTarget) rfl rfl (show parentTarget.Allocated base from rfl) rfl))
  have entered : ParentPath before (.body [i32 ptr, i32 selector] parent.initial parent.code) :=
    invoke.calleeStep .enter
  have pointer : ParentPath before
      (.body [i32 ptr, i32 selector] [i64 13, i32 ptr] (.ranked (.call direct) :: afterDirect)) :=
    entered.calleeStep (.get (v := i32 ptr) rfl)
  have called : ParentPath before (suspended ptr selector (.invoke [i32 ptr])) :=
    pointer.calleeStep (.call (saved := [i64 13]) (operands := [i32 ptr]) directLinked rfl)
  have childEntered : ParentPath before (suspended ptr selector (.body [i32 ptr] fn.initial fn.code)) :=
    called.childStep .enter
  have stored : ParentPath written
      (suspended ptr selector (.body [i32 ptr] [i64 9] [.ranked (.numeric (.get ⟨0⟩)), .load 1])) :=
    childEntered.childStep (.store (args := [i32 ptr]) (saved := [i64 9])
      (MemoryWrite.fact_at (.write 0 word written (by decide))))
  exact stored.childStep (.get (v := i32 ptr) rfl)

-- Both Wasm frames are still live after the direct child's write.
example :
    Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, program.functionCode 7
      (values callerSaved ++ MemoryCallee.render parentTarget
        (suspended 0 0 (.body [i32 0] [i64 9, i32 0] [.load 1])) ++ Continuation.code afterLookup)⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, atCheckedLoad 0 0, rfl, rfl⟩

private theorem readWord : MemoryQuery.EdgeAt written 1 (.load 0) (.value word) :=
  MemoryQuery.fact_at (.load 0 word (by decide))

private theorem atNestedLookup (selector : BitVec 32) :
    ParentPath written (.body [i32 0, i32 selector] ((afterFirstChild ++ [i32 0]) ++ [i32 selector]) nestedSite) := by
  have loaded : ParentPath written (suspended 0 selector (.body [i32 0] childResults [])) :=
    (atCheckedLoad 0 selector).childStep (.load (saved := [i64 9]) readWord)
  have childLabel : ParentPath written (suspended 0 selector (.exit [i32 0] (.values childResults))) :=
    loaded.childStep .labelDone
  have resumed : ParentPath written (.body [i32 0, i32 selector] afterFirstChild afterDirect) :=
    childLabel.childStep .frameDone
  have pointer : ParentPath written (.body [i32 0, i32 selector] (afterFirstChild ++ [i32 0])
      (.ranked (.numeric (.get ⟨1⟩)) :: nestedSite)) :=
    resumed.calleeStep (.get (v := i32 0) rfl)
  exact pointer.calleeStep (.get (v := i32 selector) rfl)

private abbrev resolvedSite := indirect.memorySite ⟨1⟩ ⟨signature.params, signature.results⟩

private theorem nestedInvoked :
    ParentPath written (.child [i32 0, i32 3] afterFirstChild nestedTarget (.invoke [i32 0]) reloadOps) :=
  (atNestedLookup 3).calleeStep (.callIndirect (child := nestedTarget) (.memory rfl rfl rfl rfl) rfl)

-- Resolution consumes only the selector and leaves a pending native invocation.
example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, program.functionCode 7
    (values callerSaved ++ MemoryWrite.limeActivationCode parentType.results.length
      (parent.declaration.frame [i32 0, i32 3]) [] []
      (values (afterFirstChild ++ [i32 0]) ++ [.invoke ⟨7⟩] ++ MemoryCallee.code reloadOps) ++
      Continuation.code afterLookup)⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, nestedInvoked, rfl, rfl⟩

private def inNestedChild (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .child [i32 0, i32 3] afterFirstChild nestedTarget phase reloadOps

private def pendingHost : MemoryCallee.Phase Nat := .hostInvoke [i32 0] [] nestedHost hostOperands hostTail

private theorem atNestedHost : ParentPath nestedWritten (inNestedChild pendingHost) := by
  have entered : ParentPath written (inNestedChild (.body [i32 0] nestedFn.initial nestedFn.code)) :=
    nestedInvoked.childStep .enter
  have stored : ParentPath nestedWritten (inNestedChild (.body [i32 0] hostOperands hostOps)) :=
    entered.childStep (.store (args := [i32 0]) (saved := hostOperands)
      (MemoryWrite.fact_at (.write 0 nestedWord nestedWritten (by decide))))
  have pointer : ParentPath nestedWritten
      (inNestedChild (.body [i32 0] (hostOperands ++ [i32 0]) (.load 5 :: hostCall :: hostTail))) :=
    stored.childStep (.get (v := i32 0) rfl)
  have selector : ParentPath nestedWritten
      (inNestedChild (.body [i32 0] (hostOperands ++ [i32 nestedWord]) (hostCall :: hostTail))) :=
    pointer.childStep (.load (saved := hostOperands) (MemoryQuery.fact_at (.load 0 nestedWord (by decide))))
  exact selector.childStep (.callIndirectHost (saved := []) (target := nestedHost) (.host rfl rfl) rfl)

private def atHostConfig : Config Nat :=
  ⟨mem.store nestedWritten, entryCaller, program.functionCode 7
    (values callerSaved ++ MemoryCallee.render parentTarget (inNestedChild pendingHost) ++ Continuation.code afterLookup)⟩

-- The pending host is reached from ordinary entry with the child and parent both live.
example : Steps checkedHost checkedLaunch atHostConfig :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, atNestedHost, rfl, rfl⟩

private def pendingDirectHost : MemoryCallee.Phase Nat :=
  .hostInvoke [i32 0] [] (Site.directTarget directHost nestedHost.code) indirectResults []

private theorem atDirectHost : ParentPath hostWritten (inNestedChild pendingDirectHost) := by
  have diverged : ParentPath nestedWritten (inNestedChild pendingHost) :=
    atNestedHost.childStep (.hostDiverged (.inl ⟨rfl, rfl, .inr (.inr rfl)⟩))
  have answered : ParentPath hostWritten (inNestedChild (.body [i32 0] indirectResults hostTail)) :=
    diverged.childStep (.hostReturned (written := hostWritten) (vs := indirectResults) rfl rfl
      (.inl ⟨rfl, rfl, .inl rfl⟩))
  exact answered.childStep (.callHost (saved := []) (operands := indirectResults) directHostLinked rfl)

-- The direct source call leaves the same native pending host invocation,
-- with the prior indirect outcome supplying both arguments and current memory.
example : Steps checkedHost checkedLaunch ⟨mem.store hostWritten, entryCaller, program.functionCode 7
    (values callerSaved ++ MemoryWrite.limeActivationCode parentType.results.length
      (parent.declaration.frame [i32 0, i32 3]) [] []
      (values afterFirstChild ++ MemoryWrite.limeActivationCode signature.results.length
        (nestedFn.declaration.frame [i32 0]) [] [] (values indirectResults ++ [.invoke nestedHost.address]) ++
        MemoryCallee.code reloadOps) ++ Continuation.code afterLookup)⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, atDirectHost, rfl, rfl⟩

example : Steps checkedHost checkedLaunch ⟨mem.store directWritten, entryCaller, values [i32 42]⟩ := by
  have answered : ParentPath directWritten (inNestedChild (.body [i32 0] nestedResults [])) :=
    atDirectHost.childStep (.hostReturned (written := directWritten) (vs := nestedResults) rfl rfl
      (.inr ⟨rfl, rfl, .inl rfl⟩))
  have childLabel : ParentPath directWritten (inNestedChild (.exit [i32 0] (.values nestedResults))) :=
    answered.childStep .labelDone
  have resumed : ParentPath directWritten (.body [i32 0, i32 3] afterSecondChild reloadOps) :=
    childLabel.childStep .frameDone
  have address : ParentPath directWritten (.body [i32 0, i32 3] (afterSecondChild ++ [i32 0]) [.load 5]) :=
    resumed.calleeStep (.get (v := i32 0) rfl)
  have reloaded : ParentPath directWritten (.body [i32 0, i32 3] (afterSecondChild ++ [i32 nestedWord]) []) :=
    address.calleeStep (.load (saved := afterSecondChild) (MemoryQuery.fact_at (.load 0 nestedWord (by decide))))
  have parentLabel : ParentPath directWritten (.exit [i32 0, i32 3] (.values (afterSecondChild ++ [i32 nestedWord]))) :=
    reloaded.calleeStep .labelDone
  have outer : BodyPath ⟨directWritten, .source observedStack afterLookup, []⟩ :=
    parentLabel.calleeStep .frameDone
  have observed : BodyPath ⟨directWritten, .invoke [] observe observedStack [], []⟩ :=
    outer.step (.resolve (saved := []) (args := observedStack) rfl)
  have returned : BodyPath ⟨directWritten, .source [i32 42] [], []⟩ :=
    observed.step (.returned (vs := [i32 42]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (returned.step .labelResult).step .frameDone, rfl, rfl⟩

private theorem finishTrap {bytes : ByteArray} {args stack : List Value} {rest : List Admin} (live : mem.Live bytes)
    (active : stack ≠ [] ∨ rest ≠ [])
    (trapped : ParentPath bytes (.trapped args stack rest)) :
    Steps checkedHost checkedLaunch ⟨mem.store bytes, entryCaller, [.trap]⟩ := by
  have parentErased : ParentPath bytes (.trapped args [] []) :=
    trapped.calleeStep (.erase (removed := stack) (cut := rest) (by simp) (by simp) active)
  have parentLabel : ParentPath bytes (.exit args .trap) := parentErased.calleeStep .labelTrap
  have outerTrap : BodyPath ⟨bytes, .trapped callerSaved (Continuation.code afterLookup), []⟩ :=
    parentLabel.calleeStep .frameDone
  have discarded : BodyPath ⟨bytes, .trapped [] [], []⟩ :=
    outerTrap.step (.erase (removed := callerSaved) (cut := Continuation.code afterLookup)
      rfl rfl (.inl (by simp [callerSaved])))
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (discarded.step .labelTrap).step .frameDone, live, rfl⟩

-- The original direct-child bounds trap bypasses the parent suffix entirely.
example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ := by
  have trapped : ParentPath written (suspended (-1) 0 (.trapped [i32 (-1)] [i64 9] [])) :=
    (atCheckedLoad (-1) 0).childStep (.loadTrap (saved := [i64 9])
      (MemoryQuery.load_trap_iff_at.mpr (by decide)))
  have childErased : ParentPath written (suspended (-1) 0 (.trapped [i32 (-1)] [] [])) :=
    trapped.childStep (.erase (removed := [i64 9]) (cut := []) rfl rfl (.inl (by simp)))
  have childLabel : ParentPath written (suspended (-1) 0 (.exit [i32 (-1)] .trap)) :=
    childErased.childStep .labelTrap
  have parentTrap : ParentPath written (.trapped [i32 (-1), i32 0] [i64 13] (MemoryCallee.code afterDirect)) :=
    childLabel.childStep .frameDone
  exact finishTrap rfl (.inl (by simp)) parentTrap

private theorem finishNestedTrap {bytes : ByteArray} (live : mem.Live bytes)
    (trapped : ParentPath bytes (inNestedChild (.trapped [i32 0] [] []))) :
    Steps checkedHost checkedLaunch ⟨mem.store bytes, entryCaller, [.trap]⟩ := by
  have childLabel : ParentPath bytes (inNestedChild (.exit [i32 0] .trap)) :=
    trapped.childStep .labelTrap
  have parentTrap : ParentPath bytes
      (.trapped [i32 0, i32 3] afterFirstChild (MemoryCallee.code reloadOps)) :=
    childLabel.childStep .frameDone
  exact finishTrap live (.inl (by simp [afterFirstChild])) parentTrap

-- A trap from the indirect host skips the pending direct source instruction.
example : Steps checkedHost checkedLaunch ⟨mem.store hostTrapped, entryCaller, [.trap]⟩ := by
  have trapped : ParentPath hostTrapped (inNestedChild (.trapped [i32 0] [] (MemoryCallee.code hostTail))) :=
    atNestedHost.childStep (.hostTrapped (written := hostTrapped) rfl (.inl ⟨rfl, rfl, .inr (.inl rfl)⟩))
  have discarded : ParentPath hostTrapped (inNestedChild (.trapped [i32 0] [] [])) :=
    trapped.childStep (.erase (removed := []) (cut := MemoryCallee.code hostTail)
      rfl rfl (.inr (by simp [hostTail, MemoryCallee.code, expression])))
  exact finishNestedTrap rfl discarded

-- A trap from the direct host preserves both earlier writes and its returned
-- bytes through the same native label and frame exits.
example : Steps checkedHost checkedLaunch ⟨mem.store directTrapped, entryCaller, [.trap]⟩ := by
  have trapped : ParentPath directTrapped (inNestedChild (.trapped [i32 0] [] [])) :=
    atDirectHost.childStep (.hostTrapped (written := directTrapped) rfl (.inr ⟨rfl, rfl, .inr rfl⟩))
  exact finishNestedTrap rfl trapped

private theorem failedLookup (selector : BitVec 32) (failure : resolvedSite.Lookup base selector none) :
    Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ := by
  have trapped : ParentPath written (.trapped [i32 0, i32 selector] (afterFirstChild ++ [i32 0])
      (MemoryCallee.code reloadOps)) :=
    (atNestedLookup selector).calleeStep (.indirectTrap failure)
  exact finishTrap rfl (.inl (by simp [afterFirstChild])) trapped

-- Bounds uses the unsigned representation of -1. Null and type mismatch
-- each leave the same prior write and skip both the reload and observing host.
example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ :=
  failedLookup (-1) (.bounds rfl)

example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ :=
  failedLookup 2 (.null rfl)

example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ :=
  failedLookup 1 (.mismatch (address := ⟨5⟩) rfl rfl (by decide))

-- The same allocated host is incompatible with the parent's Wasm signature.
example : Steps checkedHost checkedLaunch ⟨mem.store written, entryCaller, [.trap]⟩ :=
  failedLookup 4 (.mismatch (address := ⟨8⟩) rfl rfl (by decide))

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples
