module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.ControlExamples

open Execution.Runtime (Frame HostOutcome MemAddr MemInst ModuleInst Value)
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private def slot : MemAddr := ⟨0⟩
private def hostType : Wasm.V1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def site : HostCall.V1.Site Nat := ⟨⟨0⟩, ⟨0⟩, hostType, 17⟩
private def alternateSite : HostCall.V1.Site Nat := ⟨⟨1⟩, ⟨1⟩, hostType, 18⟩
private def mod : ModuleInst := { funcs := [site.address, alternateSite.address], memories := [slot] }
private def fn : Function :=
  ⟨⟨mod, ⟨0⟩, [.int .i32, .int .i32], [.int .i32], [.int .i32]⟩, 0, [i32 0], []⟩
private def root : HostEntry Nat := ⟨⟨0⟩, ⟨2⟩, fn, [.get ⟨1⟩], site⟩
private def seq : Sequence Nat := ⟨root, []⟩
private def graph : Program := ⟨[], none⟩
private def block : PathBlock := ⟨none, [.load 1]⟩
private def branch : PathBlock := ⟨some (.int .i32), [.ranked (.set ⟨2⟩)]⟩
private def choice : PathChoice := ⟨⟨0⟩, [.ranked (.numeric (.get ⟨1⟩))]⟩
private def branchNode : PathNode := ⟨branch, some choice⟩
private def path : List PathNode := [⟨block, none⟩, branchNode]
private def nested : PathBlock := ⟨branch.result, []⟩
private def alternate : Source Nat :=
  .block nested (.hosts ⟨[.get ⟨0⟩], alternateSite⟩ [])

private def right (enabled : Bool) : Source Nat := if enabled then alternate else .plain choice.alternate

private def body : Bool → Source Nat
  | false => Source.ofPath path
  | true => .block block (.if_ branch choice.condition .root alternate)
private def saved : List Value := [i32 0]
private def outerLabel : OpenLabel Nat := .block saved block.result (.plain block.tail)
private def innerLabel : OpenLabel Nat := .block [] branch.result (.plain branch.tail)
private def nestedLabel : OpenLabel Nat := .block [] nested.result (.plain nested.tail)
private def caller : Frame := ⟨[i32 44], { funcs := [root.address] }⟩
private def params (condition : BitVec 32) : List Value := [i32 condition, i32 9]
private def active (condition : BitVec 32) := fn.declaration.frame (params condition)
private def initial : MemInst := ⟨⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩, none⟩
private def written : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def alternateBytes : ByteArray := ⟨#[0xaa, 0x88, 0x77, 0x66, 0x55, 0xbb]⟩
private def base (enabled : Bool) : Store Nat :=
  { funcs := [.host hostType 17, .host hostType 18, .wasm fn.declaration.type mod (seq.v1FuncFor (body enabled))],
    memories := [initial] }
private def live (enabled : Bool) := storeWithBytes (base enabled) slot initial initial.data
private def changed (enabled : Bool) := storeWithBytes (base enabled) slot initial written
private def rightStore (enabled : Bool) := storeWithBytes (base enabled) slot initial alternateBytes

private theorem guarded (enabled : Bool) : Source.Allowed .fixed graph slot .ranked fn (body enabled) := by
  have load : CodeAllowed graph slot fn.rank fn.declaration.module (expression (v1Code block.tail)) := by
    intro instr member
    obtain rfl := List.mem_singleton.mp member
    exact .source (.load 1 rfl)
  have set : CodeAllowed graph slot fn.rank fn.declaration.module (expression (v1Code branch.tail)) := by
    intro instr member
    obtain rfl := List.mem_singleton.mp member
    exact .source (.set ⟨2⟩)
  cases enabled
  · refine ⟨load, set, trivial, ?_⟩
    intro instr member
    obtain rfl := List.mem_singleton.mp member
    exact .source (.get ⟨1⟩)
  · refine ⟨load, set, trivial, ?_, trivial⟩
    intro _ member
    cases member

private theorem isSite {enabled : Bool} {found : HostCall.V1.Site Nat}
    (used : found ∈ seq.sourceSites (body enabled)) : found = site ∨ found = alternateSite := by
  cases enabled
  · exact .inl (List.mem_singleton.mp used)
  · have members : found ∈ [site, alternateSite] := used
    simpa using members

private theorem checked (enabled : Bool) (condition : BitVec 32) :
    seq.Checked .fixed graph slot .ranked (base enabled) caller (params condition) (body enabled) where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro found used
    rcases isSite used with rfl | rfl <;> exact ⟨rfl, rfl, by decide⟩
  typedBody := by cases enabled <;> rfl
  guardedBody := guarded enabled
  supportedTail := rfl
  linkedTail := by intro _ h; cases h

private theorem layout (enabled : Bool) : Layout graph (base enabled) slot initial where
  memory := rfl
  functions := by intro _ _ h; simp [graph, Program.lookup] at h

private inductive Outcome (enabled : Bool) : HostOutcome Wasm.V1.Func Nat → Prop
  | ok : Outcome enabled (.returned (changed enabled) (.values [i32 7]))
  | trap : Outcome enabled (.returned (changed enabled) .trap)

private def host (enabled : Bool) : HostSemantics Nat :=
  fun id store args answer => store = live enabled ∧
    ((id = 17 ∧ args = [i32 9] ∧ Outcome enabled answer) ∨
      (id = 18 ∧ args = [i32 0] ∧ answer = .returned (rightStore enabled) (.values [i32 8])))

private theorem contract (enabled : Bool) : seq.Contract (host enabled) .fixed slot initial (base enabled) (body enabled) := by
  intro target used _ _ _ _ _ result outcome
  have signature : target.signature = hostType := by rcases isSite used with rfl | rfl <;> rfl
  obtain ⟨store, ⟨_, _, returned⟩ | ⟨_, _, right⟩⟩ := outcome
  · rw [store, signature]
    cases returned
    · exact ⟨rfl, initial.data, written, rfl, rfl, rfl⟩
    · exact ⟨trivial, initial.data, written, rfl, rfl, rfl⟩
  · cases right
    rw [store, signature]
    exact ⟨rfl, initial.data, alternateBytes, rfl, rfl, rfl⟩

private abbrev Phase := Sequence.Phase Nat
private abbrev Ready (enabled : Bool) (phase : Phase) := seq.Ready .fixed graph slot .ranked initial phase (body enabled)
private abbrev Runs (enabled : Bool) (condition : BitVec 32) :=
  seq.Runs (host enabled) .fixed graph slot (base enabled) initial initial.data caller (params condition)
private abbrev cfg (enabled : Bool) (condition : BitVec 32) :=
  seq.render (base enabled) slot initial initial.data caller (params condition)
private def source (enabled : Bool) (condition : BitVec 32) : Config Nat :=
  ⟨live enabled, caller, values (params condition) ++ [.source (.call ⟨0⟩)]⟩

private theorem correspondence (enabled : Bool) (condition : BitVec 32) {dst : Config Nat} :
    Steps (host enabled) (source enabled condition) dst ↔
      ∃ phase, Runs enabled condition (.call (body enabled)) phase ∧ Ready enabled phase ∧ dst = cfg enabled condition phase :=
  Sequence.v1_call_run_iff rfl (checked enabled condition) (layout enabled) trivial rfl (contract enabled)

private theorem native {enabled : Bool} {condition : BitVec 32} {phase : Phase}
    (run : Runs enabled condition (.call (body enabled)) phase) :
    Steps (host enabled) (source enabled condition) (cfg enabled condition phase) := by
  have ready : Ready enabled phase := by
    induction run with
    | refl => rfl
    | tail _ move ih =>
      exact move.ready rfl (checked enabled condition) (layout enabled) rfl (contract enabled) ih
  exact (correspondence enabled condition).mpr ⟨phase, run, ready, rfl⟩

private theorem tested (enabled : Bool) (condition : BitVec 32) : Runs enabled condition (.call (body enabled))
    (.test initial.data [] branch.result choice.condition .root (right enabled) (.plain branch.tail) condition [outerLabel]) := by
  have entered : Runs enabled condition (.call (body enabled))
      (seq.beginBody caller (params condition) initial.data saved [] (body enabled)) :=
    (Relation.ReflTransGen.single .resolve).tail .enter
  have outer : Runs enabled condition (.call (body enabled)) (.if_ initial.data [] branch.result choice.condition .root (right enabled) (.plain branch.tail) [outerLabel]) := by
    cases enabled <;> exact entered.tail .openBlock
  exact outer.tail (.readCondition rfl)

private def pending : Phase := .pending initial.data [] [i32 9] site [] [innerLabel, outerLabel]
private theorem pendingRun (enabled : Bool) : Runs enabled 1 (.call (body enabled)) pending := by
  have selected : Runs enabled 1 (.call (body enabled)) (.block initial.data [] branch.result .root (.plain branch.tail) [outerLabel]) :=
    (tested enabled 1).tail .select
  have entered : Runs enabled 1 (.call (body enabled)) (.computing initial.data [] root.operands site [] [innerLabel, outerLabel]) :=
    selected.tail .openBlock
  exact (entered.tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private def rightPending : Phase :=
  .pending initial.data [] [i32 0] alternateSite [] [nestedLabel, innerLabel, outerLabel]
private theorem rightRun : Runs true 0 (.call (body true)) rightPending := by
  have selected : Runs true 0 (.call (body true)) (.block initial.data [] branch.result alternate (.plain branch.tail) [outerLabel]) :=
    (tested true 0).tail .select
  have entered : Runs true 0 (.call (body true))
      (.computing initial.data [] [.get ⟨0⟩] alternateSite [] [nestedLabel, innerLabel, outerLabel]) :=
    (selected.tail .openBlock).tail .openBlock
  exact (entered.tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private def framed (bytes : ByteArray) (f : Frame) (code : List Admin) : State :=
  ⟨bytes, caller, [.frame 1 f [.label 1 [] code]]⟩
private def load : Admin := .source ((Op.load 1).v1)
private def setLocal : Admin := .source (.localSet ⟨2⟩)
private def inOuter (code : List Admin) : List Admin := values saved ++ [.label 0 [] code, load]
private def payloadState (condition : BitVec 32) (bytes : ByteArray) (v : Value) : State :=
  framed bytes (active condition) (inOuter [.label 1 [] (values [v]), setLocal])

-- The dynamically reached pending host really sits beneath two distinct
-- labels, with its argument inside and the saved address outside.
example : Steps (host true) (source true 1)
    ⟨live true, caller, [.frame 1 (active 1) [.label 1 [] (inOuter [.label 1 [] (values [i32 9] ++ [.invoke site.address]), setLocal])]]⟩ :=
  native (pendingRun true)

private theorem finish (condition : BitVec 32) (bytes : ByteArray) (payload : Value) (word : BitVec 32)
    (read : MemoryQuery.EdgeAt bytes 1 (.load 0) (.value word)) :
    Memory32.Runs graph slot (payloadState condition bytes payload)
      ⟨bytes, caller, values [i32 word]⟩ := by
  let f := active condition
  let recorded : Frame := { f with locals := (params condition) ++ [payload] }
  have delivered : Memory32.Edge graph slot (payloadState condition bytes payload)
      (framed bytes f (inOuter (values [payload] ++ [setLocal]))) :=
    .frame (.label (.context (.label (.context (.pure (.labelDone 1 [] [payload])) [] [setLocal]) 0) saved [load]) 1) 1 caller
  have record : Memory32.Edge graph slot (framed bytes f (inOuter (values [payload] ++ [setLocal])))
      (framed bytes recorded (inOuter [])) :=
    .frame (.label (.context (.label (.set (old := i32 0) rfl) 0) saved [load]) 1) 1 caller
  have outerDone : Memory32.Edge graph slot (framed bytes recorded (inOuter []))
      (framed bytes recorded (values saved ++ [load])) :=
    .frame (.label (.context (.pure (.labelDone 0 [] [])) saved [load]) 1) 1 caller
  have readMemory : Memory32.Edge graph slot (framed bytes recorded (values saved ++ [load]))
      (framed bytes recorded (values [i32 word])) :=
    .frame (.label (.load (arg := immediate 1) rfl read) 1) 1 caller
  exact ((((Relation.ReflTransGen.single delivered).tail record).tail outerDone).tail readMemory
    |>.tail (.frame (.pure (.labelDone 1 [] [i32 word])) 1 caller))
    |>.tail (.pure (.frameDone 1 recorded [i32 word] rfl))

private theorem graphRuns {enabled : Bool} {condition : BitVec 32} {before after : State}
    (pathRun : Runs enabled condition (.call (body enabled)) (.graph before)) (tail : Memory32.Runs graph slot before after) :
    Runs enabled condition (.call (body enabled)) (.graph after) := by
  induction tail with
  | refl => exact pathRun
  | tail _ move ih => exact ih.tail (.graph move)

-- Positive selection resumes through the scalar if label, consumes its
-- result in the void block's tail, and then reads the shared returned store.
example (enabled : Bool) : Steps (host enabled) (source enabled 1) ⟨changed enabled, caller, values [i32 0x11223344]⟩ := by
  have returned : host enabled site.target (live enabled) [i32 9] (.returned (changed enabled) (.values [i32 7])) :=
    ⟨rfl, .inl ⟨rfl, rfl, .ok⟩⟩
  have resumed : Runs enabled 1 (.call (body enabled)) (.graph (payloadState 1 written (i32 7))) :=
    (pendingRun enabled).tail (.returned returned rfl)
  exact native (graphRuns resumed (finish 1 written (i32 7) 0x11223344 (MemoryQuery.fact_at (.load _ _ (by decide)))))

-- The zero arm enters another scalar block before reaching a different
-- allocated host. Its result flows through both scalar labels and the void block.
example : Steps (host true) (source true 0)
    ⟨live true, caller, [.frame 1 (active 0) [.label 1 [] (inOuter
      [.label 1 [] [.label 1 [] (values [i32 0] ++ [.invoke alternateSite.address])], setLocal])]]⟩ :=
  native rightRun

example : Steps (host true) (source true 0) ⟨rightStore true, caller, values [i32 0x55667788]⟩ := by
  have returned : host true alternateSite.target (live true) [i32 0]
      (.returned (rightStore true) (.values [i32 8])) :=
    ⟨rfl, .inr ⟨rfl, rfl, rfl⟩⟩
  let f := active 0
  let inside := framed alternateBytes f (inOuter [.label 1 [] [.label 1 [] (values [i32 8])], setLocal])
  have delivered : Runs true 0 (.call (body true)) (.graph inside) :=
    rightRun.tail (.returned returned rfl)
  have exits : Memory32.Edge graph slot inside (payloadState 0 alternateBytes (i32 8)) :=
    .frame (.label (.context (.label (.context (.label (.pure (.labelDone 1 [] [i32 8])) 1) [] [setLocal]) 0)
      saved [load]) 1) 1 caller
  have finishes := finish 0 alternateBytes (i32 8) 0x55667788 (MemoryQuery.fact_at (.load _ _ (by decide)))
  exact native (graphRuns delivered (finishes.head exits))

-- Zero selects the alternate block. Its result uses the same enclosing
-- labels and continuation, while its memory is the original allocation.
example : Steps (host false) (source false 0) ⟨live false, caller, values [i32 0]⟩ := by
  have selected : Runs false 0 (.call (body false)) (.block initial.data [] branch.result (.plain choice.alternate) (.plain branch.tail) [outerLabel]) :=
    (tested false 0).tail .select
  have alternate : Runs false 0 (.call (body false)) (.graph
      (framed initial.data (active 0) (inOuter [.label 1 [] [.source (.localGet ⟨1⟩)], setLocal]))) :=
    selected.tail .openBlock
  have reads : Memory32.Edge graph slot
      (framed initial.data (active 0) (inOuter [.label 1 [] [.source (.localGet ⟨1⟩)], setLocal]))
      (payloadState 0 initial.data (i32 9)) :=
    .frame (.label (.context (.label (.context (.label (.get rfl) 1) [] [setLocal]) 0) saved [load]) 1) 1 caller
  have finishes := finish 0 initial.data (i32 9) 0 (MemoryQuery.fact_at (.load _ _ (by decide)))
  exact native (graphRuns alternate (finishes.head reads))

-- The host trap removes the inner label first. Its returned bytes survive
-- both enclosing tail discards, the outer label exits and frame unwind.
example (enabled : Bool) : Steps (host enabled) (source enabled 1) ⟨changed enabled, caller, [.trap]⟩ := by
  have trapped : host enabled site.target (live enabled) [i32 9] (.returned (changed enabled) .trap) :=
    ⟨rfl, .inl ⟨rfl, rfl, .trap⟩⟩
  have delivered : Runs enabled 1 (.call (body enabled)) (.trapped written [] [] [innerLabel, outerLabel]) :=
    (pendingRun enabled).tail (.returned trapped rfl)
  let f := active 1
  have close : Runs enabled 1 (.call (body enabled)) (.graph (framed written f (inOuter [.trap, setLocal]))) :=
    delivered.tail .closeTrap
  have discardInner : Memory32.Edge graph slot (framed written f (inOuter [.trap, setLocal]))
      (framed written f (inOuter [.trap])) :=
    .frame (.label (.context (.label (.pure (.trapTail setLocal [])) 0) saved [load]) 1) 1 caller
  have closeOuter : Memory32.Edge graph slot (framed written f (inOuter [.trap]))
      (framed written f (values saved ++ [.trap, load])) :=
    .frame (.label (.context (.pure (.labelTrap 0 [])) saved [load]) 1) 1 caller
  have discardOuter : Memory32.Edge graph slot (framed written f (values saved ++ [.trap, load]))
      (framed written f [.trap]) :=
    .frame (.label (.pure (.trapValues (i32 0) [] [load])) 1) 1 caller
  have cleanup : Memory32.Runs graph slot (framed written f (inOuter [.trap, setLocal]))
      ⟨written, caller, [.trap]⟩ :=
    (((Relation.ReflTransGen.single discardInner).tail closeOuter).tail discardOuter
      |>.tail (.frame (.pure (.labelTrap 1 [])) 1 caller))
      |>.tail (.pure (.frameTrap 1 f))
  exact native (graphRuns close cleanup)

-- Once the selected arm has trapped, even the allocated host in the
-- other arm is excluded from every subsequent checked phase.
example (run : Runs true 1 (.trapped written [] [] [innerLabel, outerLabel]) rightPending) : False := by
  rcases Sequence.trapped_run run with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩
  · cases impossible
  · cases impossible

-- Both arms must satisfy the declared scalar result.
example : seq.checkPath (Computed.Prefix.stackTypes fn.initial) fn.declaration.results fn.entryLabels
    [⟨block, none⟩, ⟨branch, some { choice with alternate := [] }⟩] = false := rfl

-- A host-enabled arm is checked even if this invocation would select the
-- other arm.
example : seq.checkSource (Computed.Prefix.stackTypes fn.initial) fn.declaration.results fn.entryLabels
    (.block block (.if_ branch choice.condition .root
      (.hosts ⟨[.get ⟨0⟩], { alternateSite with signature := ⟨[.int .i64], [.int .i32]⟩ }⟩ []))) = false := rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.ControlExamples
