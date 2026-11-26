module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
public import Silmaril.Wasm.Institution.Operational.Loops.Indexed.Defs

/-!
# Direct hosts in a checked Lime1 indexed loop

The profile contains one allocated Wasm function and two direct host sites.
Its root reads the original i64 argument from local zero, enters the loop
with that input, and keeps one saved i64 below the label. The loop calls
its first host and tests the i32 at the top of the returned stack. Restart
uses the new i64 and discards the i32 below it. Fallthrough drops the i64
and leaves the i32 result for the second site above the saved operand.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop

open Execution.Runtime (EvalCtx Frame FuncAddr ModuleInst Value)
open Wasm.Lime1.Execution

abbrev i32 (bits : BitVec 32) : Value := Value.int .i32 bits
abbrev i64 (bits : BitVec 64) : Value := Value.int .i64 bits

def signature : Wasm.Lime1.FuncType := ⟨[.int .i64], [.int .i32]⟩
def producerType : Wasm.Lime1.FuncType := ⟨[.int .i64], [.int .i32, .int .i64, .int .i32]⟩
def laterType : Wasm.Lime1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩

structure Program (H : Type) where
  module : ModuleInst
  rootAddress : FuncAddr
  loopIndex : TypeIdx
  producerIndex : FuncIdx
  producerAddress : FuncAddr
  producerCode : H
  laterIndex : FuncIdx
  laterAddress : FuncAddr
  laterCode : H
  saved : BitVec 64

namespace Program

variable {H : Type}

def producer (p : Program H) : Site H := ⟨p.producerAddress, producerType, p.producerCode⟩
def later (p : Program H) : Site H := ⟨p.laterAddress, laterType, p.laterCode⟩

def loop (p : Program H) : Loops.LimeIndexedLoop :=
  ⟨p.loopIndex, signature, [.call p.producerIndex, .brIf ⟨0⟩, .drop]⟩

def function (p : Program H) : Wasm.Lime1.Func :=
  ⟨p.loopIndex, [], [.intConst .i64 p.saved, .localGet ⟨0⟩, p.loop.instr, .call p.laterIndex]⟩

def active (p : Program H) (arg : BitVec 64) : Frame := ⟨[i64 arg], p.module⟩

/-- Source entry links the active type table and both ordered host signatures
to their allocated declarations. The function consults a single Memory32. -/
structure Checked (p : Program H) {base : Store H} (memory : Memory32 base)
    (caller : Frame) (index : FuncIdx) : Prop where
  rootIndex : caller.module.funcs[index.toNat]? = some p.rootAddress
  root : base.funcs[p.rootAddress.value]? = some (.wasm signature p.module p.function)
  loopIndex : p.module.types[p.loopIndex.toNat]? = some signature
  producerIndex : p.module.funcs[p.producerIndex.toNat]? = some p.producerAddress
  producer : p.producer.Allocated base
  laterIndex : p.module.funcs[p.laterIndex.toNat]? = some p.laterAddress
  later : p.later.Allocated base
  memorySlot : p.module.memories = [memory.address]

def Contract (p : Program H) {base : Store H} (memory : Memory32 base)
    (host : HostSemantics H) : Prop :=
  p.producer.Contract memory host ∧ p.later.Contract memory host

end Program

/-- Each control change here corresponds to its own native step. The trapped
phases retain pending code while native contexts erase it. -/
inductive Phase where
  | source | invoke | localGet
  | enterLoop (input : BitVec 64)
  | producerCall (input : BitVec 64)
  | producerInvoke (input : BitVec 64)
  | test (res : BitVec 32) (next : BitVec 64) (condition : BitVec 32)
  | restart (scratch : BitVec 32) (next : BitVec 64)
  | dropInput (res : BitVec 32) (input : BitVec 64)
  | loopResult (res : BitVec 32)
  | laterCall (res : BitVec 32)
  | laterInvoke (res : BitVec 32)
  | loopTrap (tail : List Admin)
  | bodyTrap (saved : List Value) (tail : List Admin)
  | bodyResult (res : BitVec 32)
  | frameResult (res : Option (BitVec 32))
  | done (res : Option (BitVec 32))

structure State where
  bytes : ByteArray
  phase : Phase

def resultCode : Option (BitVec 32) → List Admin
  | none => [.trap]
  | some n => values [i32 n]

namespace Program

variable {H : Type} (p : Program H)

def afterProducer : List Admin := [.source (.brIf ⟨0⟩), .source .drop]
def afterLoop : List Admin := [.source (.call p.laterIndex)]
def loopCode (inner : List Admin) : List Admin :=
  value (i64 p.saved) :: .label 1 [p.loop.instr] inner :: p.afterLoop

def functionCode (arg : BitVec 64) (code : List Admin) : List Admin :=
  [.frame 1 (p.active arg) [.label 1 [] code]]

def functionContext (arg : BitVec 64) : EvalCtx Wasm.Lime1.Instr :=
  .frame 1 (p.active arg) (.label 1 [] .hole)

def producerContext (arg : BitVec 64) : EvalCtx Wasm.Lime1.Instr :=
  (p.functionContext arg).comp
    (.seq [i64 p.saved] (.label 1 [p.loop.instr] (.seq [] .hole Program.afterProducer)) p.afterLoop)

def code (index : FuncIdx) (arg : BitVec 64) : Phase → List Admin
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
  | .laterCall res => p.functionCode arg (values [i64 p.saved, i32 res] ++ p.afterLoop)
  | .laterInvoke res => (p.functionContext arg).plug value (values [i64 p.saved, i32 res] ++ [.invoke p.laterAddress])
  | .loopTrap tail => p.functionCode arg (p.loopCode (.trap :: tail))
  | .bodyTrap saved tail => p.functionCode arg (values saved ++ .trap :: tail)
  | .bodyResult res => p.functionCode arg (resultCode (some res))
  | .frameResult res => [.frame 1 (p.active arg) (resultCode res)]
  | .done res => resultCode res

def render {base : Store H} (memory : Memory32 base) (caller : Frame)
    (index : FuncIdx) (arg : BitVec 64) (state : State) : Config H :=
  ⟨memory.store state.bytes, caller, p.code index arg state.phase⟩

end Program

/-- Pure graph phases preserve the single live store. Trap erasure may discard
a suffix of the saved operands or a prefix of the skipped instructions. -/
inductive Control (arg saved : BitVec 64) (afterLoop : List Admin) : Phase → Phase → Prop where
  | resolve : Control arg saved afterLoop .source .invoke
  | enter : Control arg saved afterLoop .invoke .localGet
  | readLocal : Control arg saved afterLoop .localGet (.enterLoop arg)
  | openLoop (input : BitVec 64) : Control arg saved afterLoop (.enterLoop input) (.producerCall input)
  | resolveProducer (input : BitVec 64) : Control arg saved afterLoop (.producerCall input) (.producerInvoke input)
  | test (res : BitVec 32) (next : BitVec 64) (condition : BitVec 32) :
      Control arg saved afterLoop (.test res next condition) (if condition = 0 then .dropInput res next else .restart res next)
  | restart (scratch : BitVec 32) (next : BitVec 64) : Control arg saved afterLoop (.restart scratch next) (.enterLoop next)
  | dropInput (res : BitVec 32) (input : BitVec 64) : Control arg saved afterLoop (.dropInput res input) (.loopResult res)
  | loopResult (res : BitVec 32) : Control arg saved afterLoop (.loopResult res) (.laterCall res)
  | resolveLater (res : BitVec 32) : Control arg saved afterLoop (.laterCall res) (.laterInvoke res)
  | eraseLoop {before cut tail : List Admin} (split : before = cut ++ tail) (active : cut ≠ []) :
      Control arg saved afterLoop (.loopTrap before) (.loopTrap tail)
  | exitLoop : Control arg saved afterLoop (.loopTrap []) (.bodyTrap [i64 saved] afterLoop)
  | eraseBody {stack kept removed : List Value} {before cut tail : List Admin}
      (split : stack = kept ++ removed) (suffix : before = cut ++ tail) (active : removed ≠ [] ∨ cut ≠ []) :
      Control arg saved afterLoop (.bodyTrap stack before) (.bodyTrap kept tail)
  | exitTrap : Control arg saved afterLoop (.bodyTrap [] []) (.frameResult none)
  | exitResult (res : BitVec 32) : Control arg saved afterLoop (.bodyResult res) (.frameResult (some res))
  | finish (res : Option (BitVec 32)) : Control arg saved afterLoop (.frameResult res) (.done res)

inductive Edge {H : Type} (p : Program H) {base : Store H} (memory : Memory32 base)
    (host : HostSemantics H) (arg : BitVec 64) : State → State → Prop where
  | control {bytes a b} (move : Control arg p.saved p.afterLoop a b) :
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
  | laterReturns {bytes next input res} (live : memory.Live next)
      (answer : host p.laterCode (memory.store bytes) [i64 p.saved, i32 input]
        (.returned (memory.store next) (.values [i32 res]))) :
      Edge p memory host arg ⟨bytes, .laterInvoke input⟩ ⟨next, .bodyResult res⟩
  | laterTraps {bytes next input} (live : memory.Live next)
      (answer : host p.laterCode (memory.store bytes) [i64 p.saved, i32 input] (.returned (memory.store next) .trap)) :
      Edge p memory host arg ⟨bytes, .laterInvoke input⟩ ⟨next, .bodyTrap [] []⟩
  | laterDiverges {bytes input} (answer : host p.laterCode (memory.store bytes) [i64 p.saved, i32 input] .diverged) :
      Edge p memory host arg ⟨bytes, .laterInvoke input⟩ ⟨bytes, .laterInvoke input⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop
