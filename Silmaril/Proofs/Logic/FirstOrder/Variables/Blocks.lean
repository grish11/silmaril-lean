module

public import Silmaril.Proofs.Logic.FirstOrder.Variables.Semantics

@[expose] public section
namespace Silmaril.Logic.FirstOrder.Variables
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature} (M : FOL.Structure Sg)

private theorem pullback_captureShift {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S)
    (w : M.carrier cfg) (x : M.carrier bound) (a : (i : Fin k) → M.carrier (Γ i)) :
    pullback M (liftIndex Fin.succ) (capturedShiftSort cfg bound Γ)
      (consAssignment M cfg (Fin.cases bound Γ) w (consAssignment M bound Γ x a)) =
        consAssignment M cfg Γ w a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem weakenCaptured_holds {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S)
    (p : FOL.Formula Sg (Fin.cases cfg Γ))
    (w : M.carrier cfg) (x : M.carrier bound) (a : (i : Fin k) → M.carrier (Γ i)) :
    FOL.Formula.Holds M (weakenCaptured cfg bound Γ p)
      (consAssignment M cfg (Fin.cases bound Γ) w (consAssignment M bound Γ x a)) ↔
    FOL.Formula.Holds M p (consAssignment M cfg Γ w a) := by
  unfold weakenCaptured
  rw [holds_rename]
  exact Iff.of_eq (congrArg (FOL.Formula.Holds M p) (pullback_captureShift M cfg bound Γ w x a))

/-- Weakening ignores every new captured value, with no nonempty-sort hypothesis. -/
theorem weakenBlock_holds {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (xs : List Sg.S) (p : FOL.Formula Sg (Fin.cases cfg Γ))
    (w : M.carrier cfg) (a : (i : Fin k) → M.carrier (Γ i))
    (b : BlockAssignment M xs) :
    FOL.Formula.Holds M (weakenBlock cfg Γ xs p)
      (consAssignment M cfg (blockContext Γ xs) w (joinAssignment M a xs b)) ↔
    FOL.Formula.Holds M p (consAssignment M cfg Γ w a) := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    change FOL.Formula.Holds M
      (weakenCaptured cfg s (blockContext Γ xs) (weakenBlock cfg Γ xs p))
      (consAssignment M cfg (Fin.cases s (blockContext Γ xs)) w
        (consAssignment M s (blockContext Γ xs) b.1 (joinAssignment M a xs b.2))) ↔ _
    rw [weakenCaptured_holds]
    exact ih b.2

end Silmaril.Logic.FirstOrder.Variables
