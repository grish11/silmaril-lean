module

public import Silmaril.SSA.Peggy.EPEG.Selection.Legality.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Selection.Legality

public section

namespace Silmaril.SSA.Peggy.EPEG.Selection

open PEG

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l}

/-- The printed clauses exclude a cycle whose source vertices are all
selected non-θ rows. -/
theorem PrintedCycles.excludes_nonTheta_cycle {chosen : Fin n → Bool}
    {reaches : Fin n → Fin n → Bool} (printed : PrintedCycles g chosen reaches)
    {i : Fin n} {ks : List (EdgeKind (Fin l))}
    (cycle : Walk (SelectedNonThetaEdge g chosen) i ks i) (nonempty : ks ≠ []) : False :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Selection.excludes_nonTheta_cycle printed cycle nonempty

/-- The repaired check supplies Definition 5.1(1). Loop scope, cycles
through observers, and Figure 11 demand well-foundedness are separate. -/
theorem FeedbackRank.feedbackCycles (ranked : FeedbackRank g) : g.FeedbackCycles :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Selection.feedbackCycles ranked

end Silmaril.SSA.Peggy.EPEG.Selection
