module
public import Silmaril.Project.Shapes.Contextual.Defs
@[expose] public section
namespace Silmaril.Project.Shapes.Contextual
open Silmaril.Project.Shapes
/-- An empty entry relation cannot discharge the contextual obligation. -/
theorem Obligation.entry_exists {Input Observation : Type}
    {sig : Silmaril.X86.SystemV.CApi.Signature} {F : C.CFn sig} {M : Model}
    {p : Placement} {C : Context Input Observation}
    (h : Obligation F M p C) (i : Input) : ∃ s m, C.Initial M i s m := h.1 i
end Silmaril.Project.Shapes.Contextual
