module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.V1.Execution.Properties

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution
open CallResolution

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def root : FuncAddr := ⟨0⟩
private def writerAddress : FuncAddr := ⟨1⟩
private def otherAddress : FuncAddr := ⟨2⟩
private def slot : MemAddr := ⟨0⟩
private def typeIndex : TypeIdx := ⟨1⟩
private def i32Type : NumType := .int .i32
private def expected : Wasm.V1.FuncType := ⟨[.int .i64, i32Type], [i32Type]⟩
private def different : Wasm.V1.FuncType := ⟨expected.params.reverse, expected.results⟩
private def table : FixedTable :=
  ⟨⟨1⟩, ⟨[some writerAddress, none, some otherAddress], some 3⟩⟩
private def get (index : LocalIdx) : Op := .ranked (.numeric (.get index))
private def record : Op := .ranked (.set ⟨3⟩)
private def word : BitVec 32 := 0x11223344
private def earlier : BitVec 32 := 0x66778899
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def priorWrite : ByteArray := ⟨#[0xaa, 0x99, 0x88, 0x77, 0x66, 0xbb]⟩
private def calleeWrite : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def memory : MemInst := ⟨before, none⟩

private def writer : Function :=
  ⟨⟨{ memories := [slot] }, ⟨0⟩, expected.params, [], expected.results⟩, 0, [i32 0],
    [get ⟨1⟩, .store 1, get ⟨1⟩]⟩
private def wrong : Function :=
  ⟨⟨{ memories := [slot] }, ⟨0⟩, different.params, [], different.results⟩, 4, [], [get ⟨0⟩]⟩
private def indirect : Op := .callIndirect typeIndex expected
private def body : List Op := [get ⟨1⟩, get ⟨2⟩, get ⟨0⟩, indirect]
private def reader (rank : Nat) : Function :=
  ⟨⟨{ memories := [slot], tables := [table.address], types := [different, expected] }, ⟨0⟩,
      [i32Type, .int .i64, i32Type], [i32Type], [i32Type]⟩,
    rank, [i32 0, i32 0, i32 earlier], [.store 1, .block (some i32Type) body, record, .load 1]⟩
private def program (rank : Nat) : Program := ⟨[some (reader rank), some writer, some wrong], some table⟩

private def base : Store Unit :=
  { memories := [memory], tables := [⟨[], none⟩, table.table]
    funcs := [reader 1, writer, wrong].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }

private theorem layout (rank : Nat) : Layout (program rank) base slot memory where
  memory := rfl
  functions := by
    intro address fn found
    rcases address with ⟨_ | _ | _ | _⟩ <;> simp [Program.lookup, program] at found
    all_goals subst fn; rfl
  table := by
    intro fixed found
    change some table = some fixed at found
    cases found
    rfl

private def rankFor : CallMode → Nat
  | .ranked => 1
  | .recursive => 0
private theorem checked (calls : CallMode) : (program (rankFor calls)).checkV1 slot .fixed calls = true := by
  cases calls <;> rfl

-- A compatible equal-rank target is rejected. The mismatching higher-rank
-- entry is allowed in the ranked profile because it can only trap.
example : (program 0).checkV1 slot = false := rfl
example : (program 0).checkV1 slot .fixed .recursive = true := rfl
example : ({ program 1 with fixedTable := none } : Program).checkV1 slot = false := rfl
example : ({ program 1 with functions := [some (reader 1), some writer] } : Program).checkV1 slot = false := rfl
example : ¬ Layout (program 1) { base with tables := [] } slot memory := by
  intro missing
  cases missing.table table rfl

private def withReaderModule (mod : Execution.Runtime.ModuleInst) : Program :=
  { program 1 with functions := [some { reader 1 with declaration := { (reader 1).declaration with module := mod } },
    some writer, some wrong] }

example : (withReaderModule { (reader 1).declaration.module with tables := [⟨0⟩] }).checkV1 slot = false := rfl
example : (withReaderModule { (reader 1).declaration.module with types := [expected, different] }).checkV1 slot =
    false := rfl

example : ({ program 1 with functions := [some { reader 1 with code :=
      [.ranked .unreachable, .block none [.callIndirect ⟨2⟩ expected]] }, some writer, some wrong] } : Program).checkV1
    slot = false := rfl

example : (reader 1).checkRegion [.int .i64, i32Type, .int .i64] [i32Type]
    [indirect] [] = false := rfl
example : (reader 1).checkRegion [i32Type, .int .i64, i32Type] [i32Type]
    [indirect] [] = false := rfl

private def outside : Frame := ⟨[i32 91], { funcs := [root] }⟩
private def callArgs (selector : BitVec 32) : List Value := [i32 selector, i64 81, i32 word]
private def childArgs : List Value := [i64 81, i32 word]
private def active (selector : BitVec 32) : Frame := (reader 1).declaration.frame (callArgs selector)
private def child : Frame := writer.declaration.frame childArgs
private def input (selector : BitVec 32) : State :=
  ⟨before, outside, values (callArgs selector) ++ [.source (.call ⟨0⟩)]⟩
private def initial (selector : BitVec 32) : Config Unit := ⟨base, outside, (input selector).code⟩
private def saved : List Value := [i32 0]
private def tail : List Admin := [.source record.v1, .source ((Op.load 1).v1)]
private def afterPrior : Store Unit := storeWithBytes base slot memory priorWrite
private def afterChild : Store Unit := storeWithBytes base slot memory calleeWrite

private def inRoot (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] c.code]]⟩
private def inBlock (c : Config Unit) : Config Unit :=
  inRoot ⟨c.store, c.frame, values saved ++ [.label 1 [] c.code] ++ tail⟩

private theorem blockStep {s t : Config Unit} (move : Step CallFrame.v1NoHost s t) :
    Step CallFrame.v1NoHost (inBlock s) (inBlock t) :=
  .frame (.label (.context (.label move 1 []) saved tail) 1 []) 1 outside

private def site (selector : BitVec 32) : Config Unit :=
  Indirect.v1Source afterPrior (active selector) typeIndex selector childArgs []

private theorem storeAt {s t : Store Unit} {f : Frame} {mem : MemInst} {word : BitVec 32}
    {bytes : ByteArray} (found : frameMemory s f = some (slot, mem))
    (access : MemoryWrite.EdgeAt mem.data 1 (.store 0 word) (.written bytes))
    (next : setMemory s slot { mem with data := bytes } = t) :
    Step CallFrame.v1NoHost ⟨s, f, values [i32 0, i32 word] ++ [.source ((Op.store 1).v1)]⟩ ⟨t, f, []⟩ :=
  (MemoryWrite.v1_context_store_step_iff_at (immediate := immediate 1) (saved := []) (tail := []) found).mpr
    ⟨.written bytes, access, by cases next; rfl⟩

private theorem reachLookup (selector : BitVec 32) : Steps CallFrame.v1NoHost (initial selector) (inBlock (site selector)) := by
  have resolved : Step CallFrame.v1NoHost (initial selector)
      ⟨base, outside, values (callArgs selector) ++ [.invoke root]⟩ :=
    .context (.call _ _ ⟨0⟩ root rfl) (callArgs selector) []
  have entered := (layout 1).enter_rendered (address := root) (fn := reader 1) rfl (by decide)
    (suspended := outside) (bytes := before) (args := callArgs selector) rfl
  have write := storeAt (s := base) (t := afterPrior) (f := active selector) (word := earlier)
    (show frameMemory base (active selector) = some (slot, memory) from rfl)
    (MemoryWrite.fact_at (.write _ _ _ (by decide))) rfl
  have writeInRoot : Step CallFrame.v1NoHost (inRoot ⟨base, active selector, expression (reader 1).v1Func.body⟩)
      (inRoot ⟨afterPrior, active selector, values saved ++ [.source (.block (some i32Type) (v1Code body))] ++ tail⟩) :=
    .frame (.label (.context write saved (([.source (.block (some i32Type) (v1Code body))] : List Admin) ++ tail))
      1 []) 1 outside
  have openBlock :
      Step CallFrame.v1NoHost (inRoot ⟨afterPrior, active selector, values saved ++
        [.source (.block (some i32Type) (v1Code body))] ++ tail⟩)
        (inBlock ⟨afterPrior, active selector, expression (v1Code body)⟩) :=
    .frame (.label (.context (.pure _ _ (.block (some i32Type) (v1Code body))) saved tail) 1 []) 1 outside
  have first := blockStep (.context (.localGet afterPrior (active selector) ⟨1⟩ (i64 81) rfl)
    [] (expression (v1Code [get ⟨2⟩, get ⟨0⟩, indirect])))
  have second := blockStep (.context (.localGet afterPrior (active selector) ⟨2⟩ (i32 word) rfl)
    [i64 81] (expression (v1Code [get ⟨0⟩, indirect])))
  have select := blockStep (.context (.localGet afterPrior (active selector) ⟨0⟩ (i32 selector) rfl)
    childArgs [.source indirect.v1])
  exact ((((((Relation.ReflTransGen.single resolved).tail entered).tail writeInRoot).tail openBlock).tail first).tail second).tail select

private theorem lookup {selector : BitVec 32} {out : Indirect.Outcome}
    (result : Indirect.v1Resolve afterPrior (active selector) typeIndex selector = some out) :
    Step CallFrame.v1NoHost (inBlock (site selector))
      (inBlock (Indirect.v1Resolved afterPrior (active selector) childArgs [] out)) :=
  blockStep (Indirect.v1_step_iff.mpr ⟨out, result, rfl⟩)

private def inChild (s : Store Unit) (code : List Admin) : Config Unit :=
  inBlock ⟨s, active 0, [.frame 1 child [.label 1 [] code]]⟩

private theorem childStep {s t : Store Unit} {a b : List Admin}
    (move : Step CallFrame.v1NoHost ⟨s, child, a⟩ ⟨t, child, b⟩) :
    Step CallFrame.v1NoHost (inChild s a) (inChild t b) :=
  blockStep (.frame (.label move 1 []) 1 (active 0))

private def afterWrite : Config Unit := inChild afterChild [.source (.localGet ⟨1⟩)]

private theorem reachChildWrite : Steps CallFrame.v1NoHost (initial 0) afterWrite := by
  have dispatch := lookup (selector := 0) (out := .resolved writerAddress) rfl
  have enter := (layout 1).enter_rendered (address := writerAddress) (fn := writer) rfl (by decide)
    (suspended := active 0) (bytes := priorWrite) (args := childArgs) rfl
  have operands := childStep (.context (.localGet afterPrior child ⟨1⟩ (i32 word) rfl)
    [i32 0] [.source ((Op.store 1).v1), .source (.localGet ⟨1⟩)])
  have write := storeAt (s := afterPrior) (t := afterChild) (f := child) (word := word)
    (show frameMemory afterPrior child = some (slot, { memory with data := priorWrite }) from rfl)
    (MemoryWrite.fact_at (.write _ _ _ (by decide))) rfl
  exact ((((reachLookup 0).tail dispatch).tail (blockStep enter)).tail operands).tail
    (childStep (.context write [] [.source (.localGet ⟨1⟩)]))

private def resuming : Config Unit :=
  inRoot ⟨afterChild, active 0, values saved ++ values [i32 word] ++ tail⟩
private theorem resume : Steps CallFrame.v1NoHost (initial 0) resuming := by
  have result := childStep (.localGet afterChild child ⟨1⟩ (i32 word) rfl)
  have exit := v1_function_fallthrough (s := afterChild) (caller := active 0) (callee := child)
    (saved := []) (payload := [i32 word]) (tail := []) (arity := 1) rfl
  have closeBlock : Step CallFrame.v1NoHost (inBlock ⟨afterChild, active 0, values [i32 word]⟩) resuming :=
    .frame (.label (.context (.pure _ _ (.labelDone 1 [] [i32 word])) saved tail) 1 []) 1 outside
  exact (((reachChildWrite.tail result).tail (blockStep exit.1)).tail (blockStep exit.2)).tail closeBlock

private def returned : Config Unit := ⟨afterChild, outside, values [i32 word]⟩
private theorem observe : Steps CallFrame.v1NoHost (initial 0) returned := by
  let resumed : Frame := { active 0 with locals := callArgs 0 ++ [i32 word] }
  have recordWord : Step CallFrame.v1NoHost resuming
      (inRoot ⟨afterChild, resumed, values saved ++ [.source ((Op.load 1).v1)]⟩) :=
    .frame (.label (.context (.localSet afterChild (active 0) ⟨3⟩ (i32 word) (i32 0) rfl)
      saved [.source ((Op.load 1).v1)]) 1 []) 1 outside
  have read : Step CallFrame.v1NoHost ⟨afterChild, resumed, values saved ++ [.source ((Op.load 1).v1)]⟩
      ⟨afterChild, resumed, values [i32 word]⟩ :=
    (MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1) (address := 0)
      (saved := []) (tail := [])
      (show frameMemory afterChild resumed = some (slot, { memory with data := calleeWrite }) from rfl)).mpr
      ⟨.value word, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  have exit := v1_function_fallthrough (s := afterChild) (caller := outside) (callee := resumed)
    (saved := []) (payload := [i32 word]) (tail := []) (arity := 1) rfl
  exact (((resume.tail recordWord).tail (.frame (.label read 1 []) 1 outside)).tail exit.1).tail exit.2

private def trapped : Config Unit := ⟨afterPrior, outside, [.trap]⟩

-- The first trap leaves the argument operands pending. Native label and
-- frame reductions discard them and the caller tail in separate steps.
private theorem unwind {selector : BitVec 32} :
    Steps CallFrame.v1NoHost
      (inBlock ⟨afterPrior, active selector, values childArgs ++ [.trap]⟩) trapped := by
  have dropArgs := blockStep (.pure (host := CallFrame.v1NoHost) afterPrior (active selector)
    (.trapValues (i64 81) [i32 word] []))
  have closeBlock : Step CallFrame.v1NoHost (inBlock ⟨afterPrior, active selector, [.trap]⟩)
      (inRoot ⟨afterPrior, active selector, values saved ++ [.trap] ++ tail⟩) :=
    .frame (.label (.context (.pure _ _ (.labelTrap 1 [])) saved tail) 1 []) 1 outside
  have discard := Step.frame (.label (.pure (host := CallFrame.v1NoHost) afterPrior (active selector)
    (.trapValues (i32 0) [] tail)) 1 []) 1 outside
  have closeFunction := Step.frame (.pure (host := CallFrame.v1NoHost) afterPrior (active selector)
    (.labelTrap 1 [])) 1 outside
  exact ((((Relation.ReflTransGen.single dropArgs).tail closeBlock).tail discard).tail closeFunction).tail
    (.pure _ _ (.frameTrap 1 (active selector)))

private theorem readback (calls : CallMode) {selector : BitVec 32} {dst : Config Unit}
    (native : Steps CallFrame.v1NoHost (initial selector) dst) :
    ∃ out, Runs (program (rankFor calls)) slot (input selector) out ∧
      ReadyFor .fixed (program (rankFor calls)) slot calls (rankFor calls + 1) before.size out ∧
      dst = render base slot memory out :=
  (v1_call_run_iff_at (root := root) (fn := reader (rankFor calls)) (index := ⟨0⟩)
    (args := callArgs selector) (caller := outside) (checked calls) (layout (rankFor calls)) trivial rfl rfl rfl).mp native

private theorem exactLookup (calls : CallMode) {selector : BitVec 32} {out : Indirect.Outcome}
    (result : Indirect.v1Resolve afterPrior (active selector) typeIndex selector = some out) :
    ∃ start next, Runs (program (rankFor calls)) slot (input selector) start ∧
      Edge (program (rankFor calls)) slot start next ∧
      inBlock (site selector) = render base slot memory start ∧
      inBlock (Indirect.v1Resolved afterPrior (active selector) childArgs [] out) = render base slot memory next := by
  obtain ⟨start, trace, ready, eq⟩ := readback calls (reachLookup selector)
  obtain ⟨next, edge, _, outEq⟩ := (v1_step_iff_at (checked calls) (layout (rankFor calls)) trivial ready).mp
    (eq ▸ lookup result)
  exact ⟨start, next, trace, edge, eq, outEq⟩

private theorem lookupTrap {selector : BitVec 32} {out : Indirect.Outcome}
    (result : Indirect.v1Resolve afterPrior (active selector) typeIndex selector = some out)
    (traps : out.v1Head = .trap) : Steps CallFrame.v1NoHost (initial selector) trapped := by
  have move := lookup result
  simp only [Indirect.v1Resolved, traps] at move
  exact ((reachLookup selector).tail move).trans unwind

example (calls : CallMode) := exactLookup calls (selector := 0) (out := .resolved writerAddress) rfl
example (calls : CallMode) := exactLookup calls (selector := 1) (out := .null) rfl
example (calls : CallMode) := exactLookup calls (selector := 2) (out := .mismatch otherAddress) rfl
example (calls : CallMode) := exactLookup calls (selector := -1) (out := .bounds) rfl

example (calls : CallMode) := readback calls reachChildWrite
example (calls : CallMode) := readback calls resume
example (calls : CallMode) := readback calls observe
example (calls : CallMode) := readback calls (lookupTrap (selector := 1) (out := .null) rfl rfl)
example (calls : CallMode) := readback calls (lookupTrap (selector := 2) (out := .mismatch otherAddress) rfl rfl)
example (calls : CallMode) := readback calls (lookupTrap (selector := -1) (out := .bounds) rfl rfl)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
