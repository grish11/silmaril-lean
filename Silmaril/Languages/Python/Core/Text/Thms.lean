module

public import Silmaril.Languages.Python.Core.Text.Defs

public section
namespace Silmaril.Languages.Python.Core

theorem Text.singletons_points (value : Text) :
    value.singletons.map Text.points = value.points.map (fun point => [point]) := by
  simpa only [Text.singletons, List.map_map, Function.comp_def] using
    (List.attach_map_val (l := value.points) (f := fun point => [point]))

theorem Text.singletons_length (value : Text) :
    value.singletons.length = value.points.length := by
  simpa only [List.length_map] using congrArg List.length value.singletons_points

theorem Text.singletons_empty {value : Text} (empty : value.points = []) :
    value.singletons = [] := by
  simp [Text.singletons, empty]

end Silmaril.Languages.Python.Core
