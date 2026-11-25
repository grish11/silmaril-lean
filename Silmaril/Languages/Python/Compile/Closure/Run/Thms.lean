module

public import Silmaril.Languages.Python.Compile.Closure.Run.Defs
public import Silmaril.Languages.Python.Core.Closure.Executor.Thms
import Silmaril.Proofs.Languages.Python.Compile.Closure.Run.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.Closure.Run

open Core.Closure (CodeRef Layout Value)
open Core.Closure.Dispatch (Definition resolve)
open Core.Closure.Executor (Event State labelled runPrefix)

theorem lower_complete {layout : Layout} {source : Link.Code layout}
    {target : Core.Closure.Executor.Body layout} (translated : Translation source target) :
    lowerCode source = some ⟨target, translated⟩ :=
  Proofs.Languages.Python.Compile.Closure.Run.lower_complete translated

theorem lower_rejected_iff {layout : Layout} (source : Link.Code layout) :
    lowerCode source = none ↔ ¬∃ target, Translation source target :=
  Proofs.Languages.Python.Compile.Closure.Run.lower_rejected_iff source

theorem Compiled.resolve_entry {source : Source.Module} (compiled : Compiled source) :
    ∃ target : Core.Closure.Executor.Body compiled.entry.layout,
      Translation (Link.linkBody 1 compiled.sourceBody.code).code target ∧
      resolve compiled.table compiled.entry = .ok ⟨compiled.sourceBody.parameters, target⟩ :=
  Proofs.Languages.Python.Compile.Closure.Run.resolve_entry compiled

theorem Compiled.resolve_reference {source : Source.Module} (compiled : Compiled source)
    {path : Source.BlockPath} {ref : CodeRef}
    (emitted : (path, ref) ∈ (Link.link compiled.sourceBody).references) :
    ∃ (definition : Definition Link.Code ref.layout) (target : Core.Closure.Executor.Body ref.layout),
      resolve (Link.link compiled.sourceBody).table ref = .ok definition ∧
      Translation definition.body target ∧
      resolve compiled.table ref = .ok ⟨definition.parameters, target⟩ :=
  Proofs.Languages.Python.Compile.Closure.Run.resolve_reference compiled emitted

theorem run_path {source : Source.Module} {compiled : Compiled source} {arguments : List Value}
    {fuel : Nat} {initial residual : State} {events : List Event}
    (started : start compiled arguments = .ok initial)
    (observed : run compiled arguments fuel = .ok (events, residual)) :
    (labelled compiled.table).Path initial events residual := by
  have exactRun : runPrefix compiled.table fuel initial = (events, residual) := by
    simpa [run, started] using observed
  simpa only [exactRun] using Core.Closure.Executor.run_path compiled.table fuel initial

end Silmaril.Languages.Python.Compile.Closure.Run
