module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
public import Silmaril.Languages.Starlark.Modules.Loader.Defs

/-! # UTF-8 entry points for the finite Starlark loader -/

public section

namespace Silmaril.Languages.Starlark.Frontend.Module.Loader

open Modules (Published)

/-- Array position gives the module ID. The caller supplies each entry's label table. -/
structure TextEntry where
  source : ByteArray
  labels : List (String × Modules.Loader.ModuleId) := []

structure Prepared where
  program : Functions.Program := #[]
  manifest : Modules.Loader.Manifest := #[]
  sources : Array ParsedModule := #[]

inductive Error where
  | intake (id : Modules.Loader.ModuleId) (error : IntakeError)
  deriving DecidableEq, Repr

/-- Parse and resolve in input order, appending declarations to one linked table.
The manifest and the spanned source commands have the same array indices. -/
def prepare (sources : Array TextEntry) : Except Error Prepared :=
  sources.foldlM (fun prepared entry => do
    let id := prepared.manifest.size
    let parsed ← (parseUtf8 entry.source).mapError (fun error => .intake id (.frontend error))
    let resolved ← (Modules.Resolve.resolve parsed.toCommands prepared.program).mapError
      (fun error => .intake id (.validation error))
    return ⟨resolved.program, prepared.manifest.push ⟨resolved.source, entry.labels⟩,
      prepared.sources.push parsed⟩) {}

/-- Reuse a session with this same prepared graph and linked table. -/
@[expose] def Prepared.load (prepared : Prepared) (id : Modules.Loader.ModuleId)
    (session : Modules.Loader.Session := {}) : Modules.Loader.Result Published :=
  Modules.Loader.load prepared.program prepared.manifest id session

/-- Prepare the supplied bytes and start a cold load. Runtime errors retain the
loader's session, including any dependencies already published. -/
def loadUtf8 (sources : Array TextEntry) (id : Modules.Loader.ModuleId) :
    Except Error (Modules.Loader.Result Published) := do
  let prepared ← prepare sources
  return prepared.load id

end Silmaril.Languages.Starlark.Frontend.Module.Loader
