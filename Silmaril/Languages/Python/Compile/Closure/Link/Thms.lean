module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs
public import Silmaril.Languages.Python.Compile.Closure.Body.Thms
public import Silmaril.Languages.Python.Core.Closure.Dispatch.Thms
import Silmaril.Proofs.Languages.Python.Compile.Closure.Link.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.Closure.Link

open Core.Closure (CodeRef)
open Core.Closure.Dispatch (Definition resolve)

theorem paths {source : Source.Module} (compiled : Body.Compiled source) :
    (link compiled).blocks.map Block.path = compiled.paths :=
  Proofs.Languages.Python.Compile.Closure.Link.paths compiled

theorem distinctPaths {source : Source.Module} (compiled : Body.Compiled source) :
    ((link compiled).blocks.map Block.path).Nodup :=
  paths compiled ▸ compiled.paths_distinct

theorem resolve_entry {source : Source.Module} (compiled : Body.Compiled source) :
    resolve (link compiled).table (link compiled).entry =
      .ok { parameters := compiled.parameters
            body := (linkBody 1 compiled.moduleTree compiled.code).code
            freevars := (link compiled).entryFreeVars
            cellvars := (link compiled).entryCellVars
            codeNames := (link compiled).entryCodeNames } :=
  Core.Closure.Dispatch.resolve_iff.mpr rfl

theorem resolve_reference {source : Source.Module} (compiled : Body.Compiled source)
    {path : Source.BlockPath} {ref : CodeRef} (emitted : (path, ref) ∈ (link compiled).references) :
    ∃ definition : Definition Code ref.layout,
      (link compiled).blocks[ref.key]? = some ⟨path, ⟨ref.layout, definition⟩⟩ ∧
      resolve (link compiled).table ref = .ok definition :=
  Proofs.Languages.Python.Compile.Closure.Link.resolve_reference compiled emitted

end Silmaril.Languages.Python.Compile.Closure.Link
