module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic

open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.Diamond (Signature ValueSort)

universe u v w

theorem classesOf_preserves_key {K : Type w} [DecidableEq K] {n : Nat}
    (key : Fin n → K) (i : Fin n) : key (classesOf key i) = key i := by
  unfold classesOf
  cases found : (List.finRange n).find? (fun j => decide (key i = key j)) with
  | none => rfl
  | some j =>
    have accepted := List.find?_some (p := fun k => decide (key i = key k)) found
    exact (of_decide_eq_true accepted).symm

theorem classesOf_eq_iff {K : Type w} [DecidableEq K] {n : Nat}
    (key : Fin n → K) (i j : Fin n) : classesOf key i = classesOf key j ↔ key i = key j := by
  constructor
  · intro same
    exact (classesOf_preserves_key key i).symm.trans
      ((congrArg key same).trans (classesOf_preserves_key key j))
  · intro same
    have sameTest : (fun k => decide (key i = key k)) = (fun k => decide (key j = key k)) := by
      simp only [same]
    unfold classesOf
    rw [sameTest]
    cases found : (List.finRange n).find? (fun k => decide (key j = key k)) with
    | some k => rfl
    | none => exact False.elim (List.find?_eq_none.mp found j (List.mem_finRange j) (by simp))

variable {Data : Type u} {Op : Signature.{u,v} Data} {n : Nat}
variable {inputs : List (ValueSort Data)} {sorts : Fin n → ValueSort Data}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

theorem seed_eq (g : Graph Op inputs sorts) (i j : Fin n) :
    seed g i = seed g j ↔ (g.node i).profile = (g.node j).profile :=
  classesOf_eq_iff _ i j

theorem refine_eq (g : Graph Op inputs sorts) (p : Partition n) (i j : Fin n) :
    refine g p i = refine g p j ↔
      p i = p j ∧ (g.node i).profile = (g.node j).profile ∧
        g.operandClasses p i = g.operandClasses p j := by
  unfold refine
  rw [classesOf_eq_iff]
  simp

theorem checkStable_correct (g : Graph Op inputs sorts) (p : Partition n) :
    checkStable g p = true ↔ Stable g p := by
  simp only [checkStable, Stable, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem stable_iff_no_split (g : Graph Op inputs sorts) (p : Partition n) :
    Stable g p ↔ ∀ i j, refine g p i = refine g p j ↔ p i = p j := by
  constructor
  · intro stable i j
    exact ⟨fun same => ((refine_eq g p i j).mp same).1,
      fun same => (refine_eq g p i j).mpr ⟨same, stable i j same⟩⟩
  · intro unchanged i j same
    exact ((refine_eq g p i j).mp ((unchanged i j).mpr same)).2

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic
