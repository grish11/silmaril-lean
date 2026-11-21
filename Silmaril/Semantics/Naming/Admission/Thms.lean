module

public import Silmaril.Semantics.Naming.Admission.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Semantics.Naming.Admission

public section

namespace Silmaril.Semantics.Naming

variable {Name Payload : Type} [DecidableEq Name] [DecidableEq Payload]

/-- Success returns precisely the union, with no overwrites; failure witnesses a
collision in that union, including collisions internal to the proposed batch. -/
theorem admit_spec (read : Name → Option Payload) (writes : List (Name × Payload)) :
    match admit read writes with
    | .ok updated => graph updated = union (graph read) (listed writes)
    | .error name => name ∈ collisions (union (graph read) (listed writes)) :=
  Proofs.Semantics.Naming.Admission.admit_spec read writes

theorem admit_exists_iff (read : Name → Option Payload) (writes : List (Name × Payload)) :
    (∃ updated, admit read writes = .ok updated) ↔ Binding (union (graph read) (listed writes)) :=
  Proofs.Semantics.Naming.Admission.admit_exists_iff read writes

theorem admit_eq_union {read updated : Name → Option Payload} {writes : List (Name × Payload)}
    (accepted : admit read writes = .ok updated) : graph updated = union (graph read) (listed writes) := by
  simpa only [accepted] using admit_spec read writes

theorem admit_preserves {read updated : Name → Option Payload} {writes : List (Name × Payload)}
    (accepted : admit read writes = .ok updated) : Subset (graph read) (graph updated) :=
  admit_eq_union accepted ▸ fun _ _ hit => Or.inl hit

end Silmaril.Semantics.Naming
