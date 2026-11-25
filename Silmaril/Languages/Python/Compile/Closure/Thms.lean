module

public import Silmaril.Languages.Python.Compile.Closure.Defs
public import Silmaril.Languages.Python.Core.Closure.Thms

public section
namespace Silmaril.Languages.Python.Compile.Closure

open Source (Scope)
open Source.Closure (Layout)
open Source.Closure.Frame (Destination ParameterLayout)

theorem parameterName_slot (scope : Scope) (destination : Destination scope) :
    parameterName scope (parameterSlot scope destination) = Destination.nameAt scope destination := by
  cases destination <;> rfl

theorem parameters_order {scope : Scope} (layout : ParameterLayout scope) :
    (parameters layout).slots.map (parameterName scope) = scope.context.parameters := by
  simpa [parameters, List.map_map, Function.comp_def, parameterName_slot] using layout.destinations_names

theorem function_order {parent child : Scope} (key : Nat) (layout : Layout parent child.captures)
    (frame : Core.Closure.Frame (frameLayout parent)) :
    (function key layout frame).captures.toList = layout.cells frame.owned frame.captures :=
  Core.Closure.Function.ofCaptureList_order _ _ _

theorem captureOperand_cell {parent : Scope} (entry : Source.Closure.Entry parent)
    (frame : Core.Closure.Frame (frameLayout parent)) :
    frame.captureCell (captureOperand entry) = entry.slot.cell frame.owned frame.captures := by
  cases entry with
  | mk capture slot => cases slot <;> rfl

theorem capture_at {parent child : Scope} (key : Nat) (layout : Layout parent child.captures)
    (frame : Core.Closure.Frame (frameLayout parent)) (index : Fin child.captures.length) :
    (frame.closure (codeRef child key) (captureOperands layout)).captures[index] =
      (layout.entriesVector.get index).slot.cell frame.owned frame.captures :=
  (Core.Closure.Frame.capture_at frame (codeRef child key) (captureOperands layout) index).trans
    (captureOperand_cell (layout.entriesVector.get index) frame)

end Silmaril.Languages.Python.Compile.Closure
