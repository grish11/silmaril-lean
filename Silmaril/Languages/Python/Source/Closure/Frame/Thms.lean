module

public import Silmaril.Languages.Python.Source.Closure.Frame.Defs

public section
namespace Silmaril.Languages.Python.Source.Closure

theorem Layout.entriesVector_toList {parent : Scope} {captures : List Capture}
    (layout : Layout parent captures) : layout.entriesVector.toList = layout.entries := by
  simp [Layout.entriesVector]

namespace Frame

theorem ParameterLayout.destinations_distinct {scope : Scope} (layout : ParameterLayout scope) :
    layout.destinations.toList.Nodup := by
  simpa [ParameterLayout.destinations] using layout.distinct

theorem ParameterLayout.destinations_names {scope : Scope} (layout : ParameterLayout scope) :
    layout.destinations.toList.map (Destination.nameAt scope) = scope.context.parameters := by
  have names : (layout.entries.map fun entry => Destination.nameAt scope entry.destination) =
      layout.entries.map ParameterSlot.name := List.map_congr_left (fun entry _ => entry.lookup_eq)
  simpa [ParameterLayout.destinations, List.map_map, Function.comp_def] using names.trans layout.inOrder

end Frame
end Silmaril.Languages.Python.Source.Closure
