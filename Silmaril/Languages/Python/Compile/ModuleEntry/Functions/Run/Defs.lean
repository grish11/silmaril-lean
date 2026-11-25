module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Defs
public import Silmaril.Languages.Python.Compile.Closure.Run.Defs
public import Silmaril.Languages.Python.Core.Module.Functions.Defs

/-! # Run lowered module bindings and calls -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

open Source (Scope)
open Compile.Closure (frameLayout)
open Core.Closure (Value RuntimeError Heap)
open Core.Closure.Executor (CodeTable Event)
open Core.Module.Functions (Invocation Session TopFunction)

inductive Instruction (scope : Scope) where
  | scalar (action : ModuleEntry.Action scope)
  | publish (name : String) (function : TopFunction)
  | call (destination : Core.Module.Functions.Destination) (name : String) (operands : List Core.Module.Functions.Operand)

inductive CompileError where
  | source (error : Functions.Error)
  | incomingCaptures (path : Source.BlockPath)
  | functionBody (error : Compile.Closure.Run.Error)
  | callOperand
  deriving Repr

def callOperand? {scope : Scope} : Operand scope → Option Core.Module.Functions.Operand
  | .integer value => some (.literal (.int value))
  | .boolean value => some (.literal (.bool value))
  | .read name _ => some (.readGlobal name)
  | .binary .. => none

def destination {scope : Scope} : Functions.Destination scope → Core.Module.Functions.Destination
  | .discard => .discard
  | .store name _ => .bindGlobal name

def lowerInstructions {scope : Scope} (next : Nat) : List (Functions.Action scope) →
    Except CompileError (List (Instruction scope) × List Compile.Closure.Link.Block)
  | [] => .ok ([], [])
  | .scalar action :: rest => do
    let (instructions, blocks) ← lowerInstructions next rest
    return (.scalar action :: instructions, blocks)
  | .call target name _ operands :: rest => do
    let some arguments := operands.mapM callOperand? | throw .callOperand
    let (instructions, blocks) ← lowerInstructions next rest
    return (.call (destination target) name arguments :: instructions, blocks)
  | .define name _ child parameters code :: rest => do
    let layout := frameLayout child.scope
    if captures : layout.captures = 0 then
      let nested := Compile.Closure.Link.linkBody (next + 1) code
      let (instructions, blocks) ← lowerInstructions (next + 1 + nested.children.length) rest
      let root : Compile.Closure.Link.Block := ⟨child.scope.context.path, ⟨layout, ⟨parameters, nested.code⟩⟩⟩
      return (.publish name ⟨⟨next, layout⟩, captures⟩ :: instructions, root :: (nested.children ++ blocks))
    else throw (.incomingCaptures child.scope.context.path)

structure Compiled (source : Source.Module) where
  checked : Functions.Checked source
  instructions : List (Instruction checked.tree.scope)
  linked : List Compile.Closure.Link.Block
  entries : List Compile.Closure.Run.ExecutorEntry
  lowered : Compile.Closure.Run.TableTranslation linked entries

def Compiled.table {source : Source.Module} (compiled : Compiled source) : CodeTable :=
  fun key => compiled.entries[key]?

def compile (source : Source.Module) : Except CompileError (Compiled source) := do
  let checked ← (Functions.check source).mapError .source
  let (instructions, linked) ← lowerInstructions 0 checked.actions
  let table ← (Compile.Closure.Run.lowerTable linked).mapError .functionBody
  return ⟨checked, instructions, linked, table.val, table.property⟩

def embed : Core.Module.Value → Value
  | .int value => .int value
  | .bool value => .bool value

def seed (globals : Core.Module.Globals) (heap : Heap := .empty) : Session :=
  ⟨fun name => (globals.lookup name).map embed, heap⟩

inductive Completion where
  | normal
  | raised (error : RuntimeError)
  | assertionError
  | codeFault (error : Core.Closure.Dispatch.Failure)
  | executorFault (error : Core.Closure.Executor.Fault)
  | scalarProfile
  deriving DecidableEq, Repr

def scalar? : Value → Option Core.Module.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .function _ => none

def evaluate {scope : Scope} (session : Session) : Operand scope → Except Completion Value
  | .integer value => .ok (.int value)
  | .boolean value => .ok (.bool value)
  | .read name _ =>
    match session.globals name with
    | some value => .ok value
    | none => .error (.raised (.nameError name))
  | .binary op lhs rhs => do
    let first ← evaluate session lhs
    let second ← evaluate session rhs
    let some left := scalar? first | throw .scalarProfile
    let some right := scalar? second | throw .scalarProfile
    match (ModuleEntry.Run.operator op).eval left right with
    | .ok value => .ok (embed value)
    | .error (.arithmetic error) => .error (.raised (.arithmetic error))
    | .error (.nameError name) => .error (.raised (.nameError name))
    | .error .assertionError => .error .assertionError

inductive State (scope : Scope) where
  | ready (session : Session) (instructions : List (Instruction scope))
  | calling (invocation : Invocation) (remaining : List (Instruction scope))
  | finished (session : Session) (completion : Completion)

def advance {scope : Scope} (table : CodeTable) : State scope → List Event × State scope
  | .finished session completion => ([], .finished session completion)
  | .ready session [] => ([], .finished session .normal)
  | .ready session (instruction :: rest) =>
    match instruction with
    | .scalar (.assign name _ operand) => ([], match evaluate session operand with
      | .ok value => .ready (session.bindGlobal name value) rest
      | .error error => .finished session error)
    | .scalar (.assertion operand) => ([], match evaluate session operand with
      | .ok value =>
        if Core.Module.Functions.truth value then .ready session rest else .finished session .assertionError
      | .error error => .finished session error)
    | .publish name function => ([], match session.publish table name function with
      | .ok updated => .ready updated rest
      | .error fault => .finished session (.codeFault fault))
    | .call destination name arguments => ([], .calling (session.prepareCall destination (.readGlobal name) arguments) rest)
  | .calling invocation rest =>
    let (log, residual) := invocation.runPrefix table 1
    (log, match residual.finish? with
      | none => .calling residual rest
      | some observation => match observation.completion with
        | .returned _ => .ready observation.residual rest
        | .raised error => .finished observation.residual (.raised error)
        | .assertionError => .finished observation.residual .assertionError
        | .fault fault => .finished observation.residual (.executorFault fault))

def runPrefix {scope : Scope} (table : CodeTable) : Nat → State scope → List Event × State scope
  | 0, state => ([], state)
  | _ + 1, .finished session completion => ([], .finished session completion)
  | fuel + 1, state =>
    let (log, next) := advance table state
    let (tail, residual) := runPrefix table fuel next
    (log ++ tail, residual)

def Compiled.start {source : Source.Module} (compiled : Compiled source)
    (globals : Core.Module.Globals := .empty) : State compiled.checked.tree.scope :=
  .ready (seed globals) compiled.instructions

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run
