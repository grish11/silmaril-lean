module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs
public import Silmaril.Languages.Python.Core.Closure.Executor.Defs

/-! # Compile a Python closure program to the fixed-positional executor

Executor operands are integer literals and name reads. An assigned call
makes its destination explicit. A nested definition stores a closure using
its resolved code reference and ordered captures.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Run

open Core.Closure (CodeRef Heap Layout Value)
open Core.Closure.Dispatch (Entry)
open Core.Closure.Executor (Operand State Event)

inductive OperandTranslation {layout : Layout} : Body.Expr layout → Operand layout → Prop where
  | integer (value : Int) : OperandTranslation (.integer value) (.literal (.int value))
  | read (slot : Core.Closure.Slot layout) : OperandTranslation (.read slot) (.read slot)
  | globalName (name : Source.Name) : OperandTranslation (.globalName name) (.readGlobal name)

def operand? {layout : Layout} : (source : Body.Expr layout) →
    Option {target // OperandTranslation source target}
  | .integer value => some ⟨.literal (.int value), .integer value⟩
  | .read slot => some ⟨.read slot, .read slot⟩
  | .globalName name => some ⟨.readGlobal name, .globalName name⟩
  | _ => none

inductive ArgumentsTranslation {layout : Layout} : List (Body.Expr layout) → List (Operand layout) → Prop where
  | nil : ArgumentsTranslation [] []
  | cons {source target sources targets}
      (first : OperandTranslation source target) (rest : ArgumentsTranslation sources targets) :
      ArgumentsTranslation (source :: sources) (target :: targets)

def arguments? {layout : Layout} : (sources : List (Body.Expr layout)) →
    Option {targets // ArgumentsTranslation sources targets}
  | [] => some ⟨[], .nil⟩
  | source :: rest => do
    let argument ← operand? source
    let tail ← arguments? rest
    return ⟨argument.val :: tail.val, .cons argument.property tail.property⟩

inductive Translation {layout : Layout} :
    Link.Code layout → Core.Closure.Executor.Body layout → Prop where
  | ret {source target} (value : OperandTranslation source target) :
      Translation (.ret source) (.ret target)
  | assign {slot source target rest next}
      (value : OperandTranslation source target) (tail : Translation rest next) :
      Translation (.assign slot source rest) (.store slot target next)
  | call {slot callee arguments function operands rest next}
      (calleeTranslation : OperandTranslation callee function)
      (argumentTranslation : ArgumentsTranslation arguments operands) (tail : Translation rest next) :
      Translation (.assign slot (.call callee arguments) rest) (.call slot function operands next)
  | closure {slot path ref captures rest next} (tail : Translation rest next) :
      Translation (.closure slot path ref captures rest) (.store slot (.closure ref captures) next)

def lowerCode {layout : Layout} : (code : Link.Code layout) →
    Option {target // Translation code target}
  | .ret expression => do
    let operand ← operand? expression
    return ⟨.ret operand.val, .ret operand.property⟩
  | .assign slot (.call callee arguments) rest => do
    let function ← operand? callee
    let operands ← arguments? arguments
    let tail ← lowerCode rest
    return ⟨.call slot function.val operands.val tail.val, .call function.property operands.property tail.property⟩
  | .assign slot expression rest => do
    let operand ← operand? expression
    let tail ← lowerCode rest
    return ⟨.store slot operand.val tail.val, .assign operand.property tail.property⟩
  | .closure slot _ ref captures rest => do
    let tail ← lowerCode rest
    return ⟨.store slot (.closure ref captures) tail.val, .closure tail.property⟩

inductive Error where
  | frontend (failure : Body.Error)
  | bodyProfile (path : Source.BlockPath)
  | entryCaptures
  deriving Repr

abbrev ExecutorEntry := Entry Core.Closure.Executor.Body

inductive TableTranslation : List Link.Block → List ExecutorEntry → Prop where
  | nil : TableTranslation [] []
  | cons {block : Link.Block} {body : Core.Closure.Executor.Body block.entry.layout}
      {blocks entries} (head : Translation block.entry.definition.body body)
      (tail : TableTranslation blocks entries) :
      TableTranslation (block :: blocks) (⟨block.entry.layout, ⟨block.entry.definition.parameters, body⟩⟩ :: entries)

def lowerTable : (blocks : List Link.Block) → Except Error {entries // TableTranslation blocks entries}
  | [] => .ok ⟨[], .nil⟩
  | block :: rest => do
    let some body := lowerCode block.entry.definition.body | throw (.bodyProfile block.path)
    let tail ← lowerTable rest
    let entry : ExecutorEntry := ⟨block.entry.layout, ⟨block.entry.definition.parameters, body.val⟩⟩
    return ⟨entry :: tail.val, .cons body.property tail.property⟩

structure Compiled (source : Source.Module) where
  sourceBody : Body.Compiled source
  entries : List ExecutorEntry
  lowered : TableTranslation (Link.link sourceBody).blocks entries
  entryCapturesEmpty : (Link.link sourceBody).entry.layout.captures = 0

def Compiled.entry {source : Source.Module} (compiled : Compiled source) : CodeRef :=
  (Link.link compiled.sourceBody).entry

def Compiled.table {source : Source.Module} (compiled : Compiled source) : Core.Closure.Executor.CodeTable :=
  fun key => compiled.entries[key]?

def compile (source : Source.Module) : Except Error (Compiled source) := do
  let body ← (Body.compile source).mapError .frontend
  let program := Link.link body
  if emptyCaptures : program.entry.layout.captures = 0 then
    let table ← lowerTable program.blocks
    return ⟨body, table.val, table.property, emptyCaptures⟩
  else throw .entryCaptures

inductive StartError where
  | resolve (failure : Core.Closure.Dispatch.Failure)
  | bind (failure : Core.Closure.Failure)
  deriving Repr

def start {source : Source.Module} (compiled : Compiled source) (arguments : List Value) :
    Except StartError State := do
  let definition ← (Core.Closure.Dispatch.resolve compiled.table compiled.entry).mapError .resolve
  let heap := Heap.empty
  let (heap, frame) := Core.Closure.Frame.fresh (layout := compiled.entry.layout) heap
    (fun index => Fin.elim0 (Fin.cast compiled.entryCapturesEmpty index))
  let environment ← (Core.Closure.Call.bindPositional definition.parameters arguments (heap, frame)).mapError .bind
  return .running environment.1 environment.2 definition.body []

def run {source : Source.Module} (compiled : Compiled source) (arguments : List Value) (fuel : Nat) :
    Except StartError (List Event × State) := do
  let state ← start compiled arguments
  return Core.Closure.Executor.runPrefix compiled.table fuel state

end Silmaril.Languages.Python.Compile.Closure.Run
