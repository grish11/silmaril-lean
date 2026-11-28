module

public import Silmaril.Semantics.ReadWrite.Labelled.Defs
import Silmaril.Proofs.Semantics.ReadWrite.Labelled

public section
namespace Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}
variable {access : Access Address Value State} {trace : Trace Address Value} {initial final : State}

theorem Trace.replays_iff_path :
    trace.Replays access initial final ↔ access.labelled.Path initial trace final :=
  Proofs.Semantics.ReadWrite.replays_iff_path

theorem Trace.consistent_iff_finishes :
    trace.Consistent access initial ↔ access.labelled.Finishes initial trace (.returned ()) := by
  simp only [Trace.Consistent, Operational.Labelled.Finishes, Access.labelled, and_true,
    Trace.replays_iff_path]

end Silmaril.Semantics.ReadWrite
