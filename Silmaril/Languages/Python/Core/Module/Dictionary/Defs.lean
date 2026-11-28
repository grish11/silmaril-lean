module

public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs

/-! # Read-only Python dictionaries built from exact displays -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.Dictionary

abbrev Atom := TupleDispatch.Element
abbrev Entry := Atom × Atom

/-- Replacing an equal key keeps its original tag and position. -/
def insert (entry : Entry) : List Entry → List Entry
  | [] => [entry]
  | first :: rest =>
    if first.1.equal entry.1 then (first.1, entry.2) :: rest
    else first :: insert entry rest

def build (display : List Entry) : List Entry :=
  display.foldl (fun entries entry => insert entry entries) []

def Entry.equal (left right : Entry) : Bool :=
  left.1.equal right.1 && left.2.equal right.2

/-- Exact dictionaries have one value for each key. Compare the pairs in
both directions so their insertion orders play no role. -/
def equalContents (left right : List Entry) : Bool :=
  left.all (fun entry => right.any (entry.equal ·)) &&
    right.all (fun entry => left.any (entry.equal ·))

structure Object where
  address : Nat
  deriving DecidableEq, Repr

inductive Argument where
  | literal (value : Atom)
  | global (name : String)

structure Clear where
  receiver : String
  arguments : List Argument

structure Get where
  receiver : String
  key : Argument
  fallback : Argument

inductive ReadValue where
  | atom (value : Atom)
  | object (value : Object)
  | unsupported

inductive Failure where
  | missingName (name : String)
  | clearArity (actual : Nat)
  | unsupported

def readName (globals : String → Option ReadValue) (name : String) :
    Except Failure ReadValue :=
  (globals name).elim (.error (.missingName name)) .ok

def Argument.read (globals : String → Option ReadValue) : Argument → Except Failure ReadValue
  | .literal value => .ok (.atom value)
  | .global name => readName globals name

/-- Resolve the stock method before preparing arguments. Positional arguments
are read in order even when their count will fail the stock arity check. -/
def Clear.prepare (call : Clear) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) : Except Failure Object := do
  let .object object ← readName globals call.receiver | throw .unsupported
  let some _ := resolve object | throw .unsupported
  let arguments ← call.arguments.mapM (Argument.read globals)
  match arguments with
  | [] => return object
  | _ :: _ => throw (.clearArity arguments.length)

/-- The live receiver selects the stock method before argument preparation.
Even on a hit the default is read before lookup. The object table validates
the handle and supplies the contents used by the lookup. -/
def Get.eval (test : Get) (globals : String → Option ReadValue) (resolve : Object → Option (List Entry)) :
    Except Failure Atom := do
  let .object object ← readName globals test.receiver | throw .unsupported
  let some entries := resolve object | throw .unsupported
  let key ← test.key.read globals
  let fallback ← test.fallback.read globals
  let .atom needle := key | throw .unsupported
  let .atom defaultValue := fallback | throw .unsupported
  return Core.Module.dictionaryGet TupleDispatch.Element.equal entries needle defaultValue

end Silmaril.Languages.Python.Core.Module.Dictionary
