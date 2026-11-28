module

public import Silmaril.SSA.Peggy.EPEG.Selection.Legality.Defs
public import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Selection

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Selection

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l}

theorem excludes_nonTheta_cycle {chosen : Fin n → Bool}
    {reaches : Fin n → Fin n → Bool} (printed : PrintedCycles g chosen reaches)
    {i : Fin n} {ks : List (EdgeKind (Fin l))}
    (cycle : Walk (SelectedNonThetaEdge g chosen) i ks i) (nonempty : ks ≠ []) : False := by
  have step {j k : Fin n} {ks : List (EdgeKind (Fin l))}
      (walk : Walk (SelectedNonThetaEdge g chosen) j ks k) (base : reaches i j = true) :
      reaches i k = true := by
    induction walk with
    | nil => exact base
    | cons edge _ ih =>
      exact ih (printed.propagate _ _ _ _ base edge.1 edge.2.1 edge.2.2)
  cases cycle with
  | nil => exact nonempty rfl
  | cons edge tail =>
    have direct := printed.immediate _ _ _ edge.1 edge.2.1 edge.2.2
    have diagonal := step tail direct
    rw [printed.irreflexive _ edge.2.1] at diagonal
    cases diagonal

theorem feedbackCycles (ranked : FeedbackRank g) : g.FeedbackCycles := by
  intro a kinds cycle nonempty
  by_contra absent
  apply Nat.lt_irrefl (ranked.rank a)
  apply cycle.strictRank nonempty ranked.rank
  rintro i j kind ⟨slot, rfl, rfl⟩ mem
  exact ranked.decreases i slot (fun feedback => absent ⟨_, mem, feedback⟩)

end Silmaril.Proofs.SSA.Peggy.EPEG.Selection
