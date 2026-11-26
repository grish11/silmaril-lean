module

public import Silmaril.Semantics.ReadWrite.Defs
public import Silmaril.Semantics.Operational.Determinism.Defs

/-! Read/write traces as labelled paths in the generic operational API. -/

@[expose] public section
namespace Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}

/-- Every accepted access is visible. Any state can end a finite observation. -/
def Access.labelled (access : Access Address Value State) :
    Operational.Labelled State (Event Address Value) Unit where
  step initial event final := match event with
    | none => False
    | some (.read address value) => access.read initial address = some value ∧ initial = final
    | some (.write address value) => access.write initial address value = some final
  observe _ result := result = .returned ()

end Silmaril.Semantics.ReadWrite
