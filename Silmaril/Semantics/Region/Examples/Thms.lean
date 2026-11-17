module

public import Silmaril.Semantics.Region.Examples.Defs
import Silmaril.Proofs.Semantics.Region.Examples

@[expose] public section
namespace Silmaril.Semantics.Region.Examples

/-- Region certification does not require unrestricted local certification. -/
theorem region_valid : Valid machine (fun _ => True) (fun s => s.1 = 0) support 0 {2} :=
  Proofs.region_valid
theorem local_failure : ¬ Sound machine (fun s => s.1 = 1) (fun l => l = 1) (fun l => l = 2) :=
  Proofs.local_failure
theorem restricted_success : Sound machine (fun s => s = (1, true)) (fun l => l = 1)
    (fun l => l = 2) := Proofs.restricted_success
theorem empty_exits_loop : Sound loop (fun _ => True) (fun l => l = 0) (fun _ => False) :=
  Proofs.empty_exits_loop
theorem loop_diverges : Diverges loop (fun l => l = 0) () := Proofs.loop_diverges
theorem erased_incompatible :
    witnessModel.erase.Reg () () false ∅ ∧ witnessModel.erase.Reg () () true ∅ ∧
      ¬ ∃ ss, witnessModel.Reg () () ss false ∅ ∧ witnessModel.Reg () () ss true ∅ :=
  Proofs.erased_incompatible
theorem nonvacuity : ¬ Valid machine (fun _ => True) (fun _ => False) support 0 {2} :=
  Proofs.nonvacuity
end Silmaril.Semantics.Region.Examples
