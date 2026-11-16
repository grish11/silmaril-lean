module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.RuleBlocks.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature} (M : FOL.Structure Sg)

/-- The rule-only projection of a joined assignment is precisely the independent
rule block, irrespective of the outer claim's captured assignment. -/
theorem pullback_prefix {k : Nat} (Γ : Fin k → Sg.S) (xs : List Sg.S)
    (a : (i : Fin k) → M.carrier (Γ i)) (b : BlockAssignment M xs) :
    pullback M (prefixIndex xs) (prefixSort Γ xs) (joinAssignment M a xs b) =
      joinAssignment M (Γ := emptyContext) (fun i => i.elim0) xs b := by
  induction xs with
  | nil => funext i; exact i.elim0
  | cons s xs ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih b.2) j

private theorem pullback_capturedPrefix {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (xs : List Sg.S) (w : M.carrier cfg)
    (a : (i : Fin k) → M.carrier (Γ i)) (b : BlockAssignment M xs) :
    pullback M (liftIndex (prefixIndex xs)) (capturedPrefixSort cfg Γ xs)
      (consAssignment M cfg (blockContext Γ xs) w (joinAssignment M a xs b)) =
    consAssignment M cfg (blockContext emptyContext xs) w
      (joinAssignment M (Γ := emptyContext) (fun i => i.elim0) xs b) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact congrFun (pullback_prefix M Γ xs a b) j

/-- An actual renamed rule formula reads exactly its own sorted valuation and
configuration. Its semantics is independent of all outer claim captures. -/
theorem liftRule_holds {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S) (xs : List Sg.S)
    (p : RulePattern cfg xs) (w : M.carrier cfg)
    (a : (i : Fin k) → M.carrier (Γ i)) (b : BlockAssignment M xs) :
    FOL.Formula.Holds M (liftRule cfg Γ xs p)
      (consAssignment M cfg (blockContext Γ xs) w (joinAssignment M a xs b)) ↔
    FOL.Formula.Holds M p
      (consAssignment M cfg (blockContext emptyContext xs) w
        (joinAssignment M (Γ := emptyContext) (fun i => i.elim0) xs b)) := by
  unfold liftRule
  rw [holds_rename]
  exact Iff.of_eq (congrArg (FOL.Formula.Holds M p) (pullback_capturedPrefix M cfg Γ xs w a b))

/-- Different outer captured assignments give the same operational-rule meaning. -/
theorem liftRule_independent_outer {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (xs : List Sg.S) (p : RulePattern cfg xs) (w : M.carrier cfg)
    (a a' : (i : Fin k) → M.carrier (Γ i)) (b : BlockAssignment M xs) :
    FOL.Formula.Holds M (liftRule cfg Γ xs p)
      (consAssignment M cfg (blockContext Γ xs) w (joinAssignment M a xs b)) ↔
    FOL.Formula.Holds M (liftRule cfg Γ xs p)
      (consAssignment M cfg (blockContext Γ xs) w (joinAssignment M a' xs b)) :=
  (liftRule_holds M cfg Γ xs p w a b).trans (liftRule_holds M cfg Γ xs p w a' b).symm

end Silmaril.Logic.Reachability.Derivation.FirstOrder
