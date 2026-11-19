module

public import Silmaril.Cerberus.Elaboration.Functions.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Functions
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- Ordinary void fallthrough uses the pinned upstream unit default, not UB088. -/
theorem returnSave_void (symbol label temporary : Sym) (location : Loc)
    (annotations : List Annot) :
    returnSave none symbol label temporary location (.mk annotations .void) .unit =
      saveWith [.label .return_, .loc location] (label, .unit)
        [(temporary, ((.unit, some (.mk annotations .void, .value)), Construction.unit))]
        (pureEffect (symbolPure temporary)) := rfl

end Silmaril.Cerberus.Elaboration.Functions
