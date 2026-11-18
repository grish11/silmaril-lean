module

public import Silmaril.Machine.Region.Calls.Defs
import Silmaril.Proofs.Machine.Region.Calls

@[expose] public section
namespace Silmaril.Machine.Region.Calls
open Silmaril.X86

/-- There is an actual first return; summary support is not just an assumed
resumption edge. The callee contract supplies termination under admission. -/
theorem first_return_exists {σ : Type} {I : SegVC.Isa σ} (C : FnContract.Strict I)
    {s : σ} (admit : Admitted C s) :
    ∃ t, FnContract.FirstReturn I s t ∧ C.Result s t :=
  C.firstReturn admit.1 admit.2.1 admit.2.2

/-- Determinism plus a strict contract covers every actual first return, not
merely some later returned state. Result includes the write frame and ABI. -/
theorem first_return_result {σ : Type} {I : SegVC.Isa σ} (C : FnContract.Strict I)
    {s t : σ} (admit : Admitted C s) (run : FnContract.FirstReturn I s t) :
    C.Result s t := Proofs.first_return_result C admit run

/-- The justified singleton label allowance applies at the first return. It
does not cover indirect call targets or intermediate callee transfers. -/
theorem first_return_target {σ : Type} {I : SegVC.Isa σ} (C : FnContract.Strict I)
    {s t : σ} (admit : Admitted C s) (run : FnContract.FirstReturn I s t) :
    (I.core t).rip.toNat = resumption I s :=
  congrArg BitVec.toNat (first_return_result C admit run).abi.pc

end Silmaril.Machine.Region.Calls
