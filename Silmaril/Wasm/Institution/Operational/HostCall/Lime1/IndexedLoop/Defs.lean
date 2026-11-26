module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
public import Silmaril.Wasm.Institution.Operational.Loops.Indexed.Defs

/-!
# Direct hosts in a checked Lime1 indexed loop

The profile contains one allocated Wasm function, a producer host in the
indexed loop, and a checked normal continuation.
Its root reads the original i64 argument from local zero, enters the loop
with that input, and keeps one saved i64 below the label. The loop calls
its first host and tests the i32 at the top of the returned stack. Restart
uses the new i64 and discards the i32 below it. Fallthrough drops the i64
and delivers the i32 result to the continuation above the saved operand.
The function's separately resolved result list governs its implicit label
and frame. The root and loop share the one-i64 parameter profile.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop

open Execution.Runtime (EvalCtx Frame FuncAddr ModuleInst Value)
open Wasm.Lime1.Execution

abbrev i32 (bits : BitVec 32) : Value := Value.int .i32 bits
abbrev i64 (bits : BitVec 64) : Value := Value.int .i64 bits

/-- The indexed loop signature, also the default root function signature. -/
def signature : Wasm.Lime1.FuncType := ⟨[.int .i64], [.int .i32]⟩
def producerType : Wasm.Lime1.FuncType := ⟨[.int .i64], [.int .i32, .int .i64, .int .i32]⟩

structure Program (H : Type) where
  module : ModuleInst
  rootAddress : FuncAddr
  loopIndex : TypeIdx
  producerIndex : FuncIdx
  producerAddress : FuncAddr
  producerCode : H
  continuation : List (Continuation.Op H)
  saved : BitVec 64
  functionIndex : TypeIdx := loopIndex
  functionResults : List NumType := signature.results

namespace Program

variable {H : Type}

def producer (p : Program H) : Site H := ⟨p.producerAddress, producerType, p.producerCode⟩

def loop (p : Program H) : Loops.LimeIndexedLoop :=
  ⟨p.loopIndex, signature, [.call p.producerIndex, .brIf ⟨0⟩, .drop]⟩

def functionType (p : Program H) : Wasm.Lime1.FuncType := ⟨signature.params, p.functionResults⟩

def function (p : Program H) : Wasm.Lime1.Func :=
  ⟨p.functionIndex, [], [.intConst .i64 p.saved, .localGet ⟨0⟩, p.loop.instr] ++
    Continuation.expr p.continuation⟩

def active (p : Program H) (arg : BitVec 64) : Frame := ⟨[i64 arg], p.module⟩

/-- Source entry links the allocated root and producer and resolves the loop
and function signatures in the active module. The root result list is the
outermost branch target in the checked suffix. The function consults a single
Memory32. -/
structure Checked (p : Program H) {base : Store H} (memory : Memory32 base)
    (caller : Frame) (index : FuncIdx) : Prop where
  rootIndex : caller.module.funcs[index.toNat]? = some p.rootAddress
  root : base.funcs[p.rootAddress.value]? = some (.wasm p.functionType p.module p.function)
  loopIndex : p.module.types[p.loopIndex.toNat]? = some signature
  producerIndex : p.module.funcs[p.producerIndex.toNat]? = some p.producerAddress
  producer : p.producer.Allocated base
  continuation : Continuation.Checked base p.module [.int .i64] [p.functionResults] p.functionResults
    [.int .i64, .int .i32] p.continuation
  memorySlot : p.module.memories = [memory.address]
  functionIndex : p.module.types[p.functionIndex.toNat]? = some p.functionType

def Contract (p : Program H) {base : Store H} (memory : Memory32 base)
    (host : HostSemantics H) : Prop :=
  p.producer.Contract memory host ∧ Continuation.Contract memory host p.continuation

end Program

/-- Each control change here corresponds to its own native step. The trapped
phases retain pending code while native contexts erase it. -/
inductive Phase (H : Type) where
  | source | invoke | localGet
  | enterLoop (input : BitVec 64)
  | producerCall (input : BitVec 64)
  | producerInvoke (input : BitVec 64)
  | test (res : BitVec 32) (next : BitVec 64) (condition : BitVec 32)
  | restart (scratch : BitVec 32) (next : BitVec 64)
  | dropInput (res : BitVec 32) (input : BitVec 64)
  | loopResult (res : BitVec 32)
  | loopTrap (tail : List Admin)
  | continuation (phase : Continuation.Phase H) (labels : List (Continuation.Label H))

structure State (H : Type) where
  bytes : ByteArray
  phase : Phase H

namespace Program

variable {H : Type} (p : Program H)

def afterProducer : List Admin := [.source (.brIf ⟨0⟩), .source .drop]
def afterLoop : List Admin := Continuation.code p.continuation
def loopCode (inner : List Admin) : List Admin :=
  value (i64 p.saved) :: .label 1 [p.loop.instr] inner :: p.afterLoop

def functionCode (arg : BitVec 64) (code : List Admin) : List Admin :=
  Continuation.entered p.functionResults.length (p.active arg) code

def functionContext (arg : BitVec 64) : EvalCtx Wasm.Lime1.Instr :=
  .frame p.functionResults.length (p.active arg) (.label p.functionResults.length [] .hole)

def producerContext (arg : BitVec 64) : EvalCtx Wasm.Lime1.Instr :=
  (p.functionContext arg).comp
    (.seq [i64 p.saved] (.label 1 [p.loop.instr] (.seq [] .hole Program.afterProducer)) p.afterLoop)

def code (index : FuncIdx) (arg : BitVec 64) : Phase H → List Admin
  | .source => values [i64 arg] ++ [.source (.call index)]
  | .invoke => values [i64 arg] ++ [.invoke p.rootAddress]
  | .localGet => p.functionCode arg (expression p.function.body)
  | .enterLoop input => p.functionCode arg (values [i64 p.saved, i64 input] ++ .source p.loop.instr :: p.afterLoop)
  | .producerCall input => p.functionCode arg (p.loopCode (values [i64 input] ++ expression p.loop.body))
  | .producerInvoke input => (p.producerContext arg).plug value (values [i64 input] ++ [.invoke p.producerAddress])
  | .test res next condition => p.functionCode arg
      (p.loopCode (values [i32 res, i64 next, i32 condition] ++ Program.afterProducer))
  | .restart scratch next => p.functionCode arg
      (p.loopCode (values [i32 scratch, i64 next] ++ [.source (.br ⟨0⟩), .source .drop]))
  | .dropInput res input => p.functionCode arg (p.loopCode (values [i32 res, i64 input] ++ [.source .drop]))
  | .loopResult res => p.functionCode arg (p.loopCode (values [i32 res]))
  | .loopTrap tail => p.functionCode arg (p.loopCode (.trap :: tail))
  | .continuation phase labels => phase.renderCode p.functionResults (p.active arg) labels

def render {base : Store H} (memory : Memory32 base) (caller : Frame)
    (index : FuncIdx) (arg : BitVec 64) (state : State H) : Config H :=
  ⟨memory.store state.bytes, caller, p.code index arg state.phase⟩

def Ready {base : Store H} (mem : Memory32 base) (host : HostSemantics H) (arg : BitVec 64) : Phase H → Prop
  | .continuation phase labels => Continuation.Ready mem host (p.active arg) p.functionResults phase labels
  | _ => True

end Program

/-- Steps before the handoff to the checked continuation preserve the live store. -/
inductive Control {H : Type} (arg saved : BitVec 64) (ops : List (Continuation.Op H)) :
    Phase H → Phase H → Prop where
  | resolve : Control arg saved ops .source .invoke
  | enter : Control arg saved ops .invoke .localGet
  | readLocal : Control arg saved ops .localGet (.enterLoop arg)
  | openLoop (input : BitVec 64) : Control arg saved ops (.enterLoop input) (.producerCall input)
  | resolveProducer (input : BitVec 64) : Control arg saved ops (.producerCall input) (.producerInvoke input)
  | test (res : BitVec 32) (next : BitVec 64) (condition : BitVec 32) :
      Control arg saved ops (.test res next condition) (if condition = 0 then .dropInput res next else .restart res next)
  | restart (scratch : BitVec 32) (next : BitVec 64) : Control arg saved ops (.restart scratch next) (.enterLoop next)
  | dropInput (res : BitVec 32) (input : BitVec 64) : Control arg saved ops (.dropInput res input) (.loopResult res)
  | loopResult (res : BitVec 32) :
      Control arg saved ops (.loopResult res) (.continuation (.source [i64 saved, i32 res] ops) [])
  | eraseLoop {before cut tail : List Admin} (split : before = cut ++ tail) (active : cut ≠ []) :
      Control arg saved ops (.loopTrap before) (.loopTrap tail)
  | exitLoop : Control arg saved ops (.loopTrap [])
      (.continuation (.trapped [i64 saved] (Continuation.code ops)) [])

inductive Edge {H : Type} (p : Program H) {base : Store H} (memory : Memory32 base)
    (host : HostSemantics H) (arg : BitVec 64) : State H → State H → Prop where
  | control {bytes a b} (move : Control arg p.saved p.continuation a b) :
      Edge p memory host arg ⟨bytes, a⟩ ⟨bytes, b⟩
  | producerReturns {bytes next input res param condition} (live : memory.Live next)
      (answer : host p.producerCode (memory.store bytes) [i64 input]
        (.returned (memory.store next) (.values [i32 res, i64 param, i32 condition]))) :
      Edge p memory host arg ⟨bytes, .producerInvoke input⟩ ⟨next, .test res param condition⟩
  | producerTraps {bytes next input} (live : memory.Live next)
      (answer : host p.producerCode (memory.store bytes) [i64 input] (.returned (memory.store next) .trap)) :
      Edge p memory host arg ⟨bytes, .producerInvoke input⟩ ⟨next, .loopTrap Program.afterProducer⟩
  | producerDiverges {bytes input} (answer : host p.producerCode (memory.store bytes) [i64 input] .diverged) :
      Edge p memory host arg ⟨bytes, .producerInvoke input⟩ ⟨bytes, .producerInvoke input⟩
  | continuation {bytes next a b labels rest}
      (move : Continuation.Edge memory host (p.active arg) p.functionResults ⟨bytes, a, labels⟩ ⟨next, b, rest⟩) :
      Edge p memory host arg ⟨bytes, .continuation a labels⟩ ⟨next, .continuation b rest⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop
