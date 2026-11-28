module

public import Silmaril.Logic.SAT.Institution.Thms
import Silmaril.Proofs.Logic.SAT.Institution.Examples

@[expose] public section

namespace Silmaril.Logic.SAT.Institution.Examples

/-- Identifying the two atoms of `p ∨ ¬q` removes every falsifying completion.
The resulting `p ∨ ¬p` still evaluates to unknown compositionally at an unknown atom. -/
theorem identification_counterexample :
    let F : Problem Bool := [[⟨false, true⟩, ⟨true, false⟩]]
    let f : Bool → Unit := fun _ => ()
    ¬ Function.Injective f ∧
      F.superEval (reduct f (fun _ => none)) = none ∧
      (F.rename f).superEval (fun _ => none) = some true ∧
      (F.rename f).evalK3 (fun _ => none) = none :=
  Proofs.Logic.SAT.Institution.identification_counterexample

/-- A one-atom problem preserves a conflict as well as a gap in evidence. -/
theorem conflict_and_gap :
    let F : Problem Unit := [[⟨(), true⟩]]
    F.evalEvidence (fun _ => Evidence.both) = Evidence.both ∧
      F.evalEvidence (fun _ => Evidence.neither) = Evidence.neither := ⟨rfl, rfl⟩

end Silmaril.Logic.SAT.Institution.Examples
