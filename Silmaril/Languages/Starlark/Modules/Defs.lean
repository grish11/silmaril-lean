module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
public import Silmaril.Languages.Starlark.Lists.Freeze.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Modules

open Functions
open Lists

def globalSlot (name : String) : Binding := ⟨.global, name⟩
def fileSlot (name : String) : Binding := ⟨.local, name⟩

/-- Top-level executable commands lack the function-only control constructs. -/
inductive TopCode where
  | atomic (code : Lists.Stmt)
  | define (name : String) (id : DeclarationId)
  | call (target : Option Binding) (callee : Lists.Expr) (arguments : Arguments)

def TopCode.body : TopCode → Body
  | .atomic code => .total (.atomic code)
  | .define name id => .define (globalSlot name) id
  | .call target callee arguments => .call target callee arguments

structure Import where
  exportedName : String
  localName : String

inductive Command where
  | exec (code : TopCode)
  | load (label : String) (imports : List Import)

structure Source where
  globals : List String
  temporaryNames : List String := []
  commands : List Command

def Source.fileNames (source : Source) : List String :=
  source.temporaryNames ++ (source.commands.flatMap fun
    | .load _ imports => imports.map Import.localName
    | _ => [])

structure Published where
  exports : List (String × Lists.Value)

/-- The host supplies a requester-specific interpretation of labels and
looks up previously published modules in the same linked heap. -/
abbrev Catalog := String → Option Published

inductive Error where
  | syntax (error : CallStaticError)
  | bindingCollision (name : String)
  | privateImport (name : String)
  | unavailableModule (label : String)
  | missingExport (label name : String)
  | runtime (error : Lists.Error)
  deriving DecidableEq, Repr

abbrev Result := EStateM.Result Error State

def isPublic (name : String) : Bool := !name.startsWith "_"

def Command.validate : Command → Except Error Unit
  | .exec code => code.body.validateCalls.mapError .syntax
  | .load _ imports =>
    match imports.find? (fun item => !isPublic item.exportedName) with
    | none => .ok ()
    | some item => .error (.privateImport item.exportedName)

def validateSource (program : Program) (source : Source) : Except Error Unit := do
  if let some collision := firstDuplicate (source.globals ++ source.fileNames) then
    throw (.bindingCollision collision)
  (Functions.validate program (.total (.atomic .pass))).mapError .syntax
  for command in source.commands do
    command.validate

def importsFrom (host : Catalog) (label : String) (imports : List Import) :
    Except Error (List (Binding × Lists.Value)) := do
  let some published := host label | throw (.unavailableModule label)
  imports.mapM fun item => do
    if !isPublic item.exportedName then
      throw (.privateImport item.exportedName)
    let some value := List.lookup item.exportedName published.exports |
      throw (.missingExport label item.exportedName)
    return (fileSlot item.localName, value)

def loadFrom (host : Catalog) (label : String) (imports : List Import) (state : State) :
    Result Unit :=
  match importsFrom host label imports with
  | .error error => .error error state
  | .ok entries => .ok () (entries.foldl (fun s (slot, value) => s.write slot value) state)

def afterCode : Outcome Iteration.Flow → Result Unit
  | .ok _ state => .ok () state
  | .error error state => .error (.runtime error) state

def runCommand (program : Program) (host : Catalog) (command : Command) (state : State) :
    Result Unit :=
  match command with
  | .exec code => afterCode (Functions.run program code.body state)
  | .load label imports => loadFrom host label imports state

def runCommands (program : Program) (host : Catalog) : List Command → State → Result Unit
  | [], state => .ok () state
  | command :: rest, state =>
    match runCommand program host command state with
    | .error error next => .error error next
    | .ok () next => runCommands program host rest next

/-- Begin a module thread with fresh scopes and no active iterator context. -/
def enter (source : Source) (state : State) : State :=
  let fresh := { state with bindings := fun _ => none, slots := fun _ => none, iterators := [] }
  (source.globals.map globalSlot ++ source.fileNames.map fileSlot).foldl State.allocateSlot fresh

def globalValues (source : Source) (state : State) : List (String × Lists.Value) :=
  source.globals.filterMap fun name =>
    (state.bindingValue (globalSlot name)).toOption.map fun value => (name, value)

def restoreThread (caller state : State) : State :=
  { restoreCaller caller state with iterators := caller.iterators }

/-- Freeze all global values on successful publication, including private
ones. File-local names never become exports. -/
def finish (source : Source) (caller : State) : Result Unit → Result Published
  | .error error state => .error error (restoreThread caller state)
  | .ok () state =>
    let globals := globalValues source state
    let frozen := state.freeze (globals.map Prod.snd)
    .ok ⟨globals.filter (fun (name, _) => isPublic name)⟩ (restoreThread caller frozen)

def initializeModule (program : Program) (host : Catalog) (source : Source) (caller : State) :
    Result Published :=
  match validateSource program source with
  | .error error => .error error caller
  | .ok () => finish source caller (runCommands program host source.commands (enter source caller))

end Silmaril.Languages.Starlark.Modules
