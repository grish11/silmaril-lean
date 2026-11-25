module

public import Silmaril.Languages.Python.Compile.Closed.Defs
public import Silmaril.Languages.Python.Core.Thms
import Silmaril.Proofs.Languages.Python.Compile.Closed.Thms
import Silmaril.Proofs.Languages.Python.Compile.Closed.Rejection

public section
namespace Silmaril.Languages.Python.Compile.Closed

theorem compile_iff (source : Source.Module) (target : Core.Body) :
    compile source = .ok target ↔
      (∃ scope, Source.analyze source = .ok scope) ∧ Translation source target :=
  Proofs.Languages.Python.Compile.Closed.compile_iff source target

theorem rejects_iff (source : Source.Module) (error : Error) :
    compile source = .error error ↔ Rejection source error :=
  Proofs.Languages.Python.Compile.Closed.rejects_iff source error

theorem returns_exists {source : Source.Module} {target : Core.Body}
    (accepted : compile source = .ok target) : ∃ result, Returns source result :=
  Proofs.Languages.Python.Compile.Closed.returns_exists ((compile_iff _ _).mp accepted).2

theorem initial {source : Source.Module} {target : Core.Body}
    (accepted : compile source = .ok target) :
    (Core.model .addition).initial target target.start := by
  cases ((compile_iff _ _).mp accepted).2 with
  | function _ translated => exact ⟨Proofs.Languages.Python.Compile.Closed.supports translated, rfl⟩

theorem observes_iff {source : Source.Module} {target : Core.Body} {result : Int}
    (accepted : compile source = .ok target) :
    (Core.model .addition).May target (.returned (.ok result)) ↔ Returns source result :=
  Proofs.Languages.Python.Compile.Closed.observes ((compile_iff _ _).mp accepted).2

theorem run_exact {source : Source.Module} {target : Core.Body} {result : Int} {fuel : Nat}
    (accepted : compile source = .ok target) (evaluated : Returns source result)
    (enough : target.start.budget ≤ fuel) :
    Core.run .addition target fuel =
      some (.stop (.finished (.ok result)) (.observed (.returned (.ok result)))) :=
  Proofs.Languages.Python.Compile.Closed.run_exact ((compile_iff _ _).mp accepted).2 evaluated enough

end Silmaril.Languages.Python.Compile.Closed
