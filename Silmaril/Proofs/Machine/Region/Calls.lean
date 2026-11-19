module

public import Silmaril.Machine.Region.Calls.Defs

@[expose] public section
namespace Silmaril.Machine.Region.Calls.Proofs
open Silmaril.X86

 theorem first_return_result {σ : Type} {I : SegVC.Isa σ} (C : FnContract.Strict I)
    {s t : σ} (admit : Admitted C s) (run : FnContract.FirstReturn I s t) :
    C.Result s t := by
  obtain ⟨u, first, result⟩ := C.firstReturn admit.1 admit.2.1 admit.2.2
  have eq := FnContract.firstReturn_unique run first
  exact eq ▸ result

end Silmaril.Machine.Region.Calls.Proofs
