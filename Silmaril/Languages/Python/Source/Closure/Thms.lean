module

public import Silmaril.Languages.Python.Source.Closure.Defs
import Silmaril.Proofs.Languages.Python.Source.Closure.Thms

public section
namespace Silmaril.Languages.Python.Source.Closure

theorem slot_iff (parent : Scope) (capture : Capture) :
    (Slot.find? parent capture).isSome ↔ Available parent capture :=
  Proofs.Languages.Python.Source.Closure.slot_iff parent capture

theorem layout_iff (parent : Scope) (captures : List Capture) :
    (layout? parent captures).isSome ↔ ∀ capture ∈ captures, Available parent capture :=
  Proofs.Languages.Python.Source.Closure.layout_iff parent captures

theorem Layout.cells_length {Cell : Type} {parent : Scope} {captures : List Capture}
    (layout : Layout parent captures) (owned : Fin parent.cells.length → Cell)
    (incoming : Fin parent.captures.length → Cell) :
    (layout.cells owned incoming).length = captures.length := by
  simpa [Layout.cells] using congrArg List.length layout.inOrder

end Silmaril.Languages.Python.Source.Closure
