module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint

open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint
open Silmaril.SSA.SeaOfNodes.Diamond (Signature ValueSort)

universe u v

variable {n : Nat}

private theorem refinesRefl (p : Partition n) : Refines p p :=
  fun _ _ eq => eq

private theorem refinesTrans {p q r : Partition n} (pq : Refines p q) (qr : Refines q r) :
    Refines p r :=
  fun i j eq => qr i j (pq i j eq)

/-- Read the coarse label through any vertex in the fine class.
For unused labels the choice of result is immaterial. -/
private noncomputable def coarseLabel (fine coarse : Partition n) (label : Fin n) : Fin n :=
  if h : ∃ i, fine i = label then coarse (Classical.choose h) else label

private theorem coarseLabel_apply {fine coarse : Partition n} (h : Refines fine coarse)
    (i : Fin n) : coarseLabel fine coarse (fine i) = coarse i := by
  have witness : ∃ j, fine j = fine i := ⟨i, rfl⟩
  rw [coarseLabel, dite_eq_left witness]
  exact h _ _ (Classical.choose_spec witness)

theorem classCount_le (p : Partition n) : classCount p ≤ n := by
  simpa [classCount] using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := p)

theorem classCount_lt_of_split {fine coarse : Partition n} (h : Refines fine coarse)
    {i j : Fin n} (same : coarse i = coarse j) (different : fine i ≠ fine j) :
    classCount coarse < classCount fine := by
  have imageEq : (Finset.univ.image fine).image (coarseLabel fine coarse) =
      Finset.univ.image coarse := by
    rw [Finset.image_image]
    exact congrArg (Finset.univ.image) (funext (coarseLabel_apply h))
  have notInj : ¬ Set.InjOn (coarseLabel fine coarse) (↑(Finset.univ.image fine)) := by
    intro injective
    apply different
    exact injective (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)) (by simpa only [coarseLabel_apply h] using same)
  have countLE := Finset.card_image_le (s := Finset.univ.image fine) (f := coarseLabel fine coarse)
  have countNE := mt Finset.injOn_of_card_image_eq notInj
  rw [imageEq] at countLE countNE
  exact Nat.lt_of_le_of_ne countLE countNE

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs : List (ValueSort Data)} {sorts : Fin n → ValueSort Data}

private theorem operandClasses_transport (g : Graph Op inputs sorts) {fine coarse : Partition n}
    (h : Refines fine coarse) (i : Fin n) :
    (g.operandClasses fine i).map (Address.relabel (coarseLabel fine coarse)) =
      g.operandClasses coarse i := by
  simp only [Graph.operandClasses, List.map_map]
  apply List.map_congr_left
  intro operand _
  cases operand with
  | argument => rfl
  | producer => simp only [Function.comp_apply, Address.relabel, coarseLabel_apply h]

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

theorem refine_refines (g : Graph Op inputs sorts) (p : Partition n) : Refines (refine g p) p :=
  fun i j same => ((refine_eq_iff g p i j).mp same).1

theorem refine_count_lt (g : Graph Op inputs sorts) (p : Partition n) (unstable : ¬ Stable g p) :
    classCount p < classCount (refine g p) := by
  classical
  have split : ∃ i j, p i = p j ∧ refine g p i ≠ refine g p j := by
    by_contra noSplit
    apply unstable
    apply (stable_iff_refine_eq g p).mpr
    intro i j
    exact ⟨refine_refines g p i j, fun eq => by
      by_contra distinct
      exact noSplit ⟨i, j, eq, distinct⟩⟩
  obtain ⟨i, j, same, different⟩ := split
  exact classCount_lt_of_split (refine_refines g p) same different

theorem run_refines (g : Graph Op inputs sorts) (fuel : Nat) (p : Partition n) :
    Refines (run g fuel p) p := by
  induction fuel generalizing p with
  | zero => exact refinesRefl _
  | succ fuel ih =>
      rw [run]
      split
      · exact refinesRefl _
      · exact refinesTrans (ih (refine g p)) (refine_refines g p)

theorem run_stable (g : Graph Op inputs sorts) (fuel : Nat) (p : Partition n)
    (enough : n - classCount p ≤ fuel) : Stable g (run g fuel p) := by
  induction fuel generalizing p with
  | zero =>
      change Stable g p
      by_contra unstable
      have increase := refine_count_lt g p unstable
      have bound := classCount_le (refine g p)
      omega
  | succ fuel ih =>
      rw [run]
      split
      · exact (checkStable_eq_true_iff g p).mp ‹checkStable g p = true›
      · have unstable : ¬ Stable g p :=
          mt (checkStable_eq_true_iff g p).mpr ‹¬ checkStable g p = true›
        have increase := refine_count_lt g p unstable
        exact ih (refine g p) (by omega)

private theorem stable_refines_round (g : Graph Op inputs sorts) {fine coarse : Partition n}
    (stable : Stable g fine) (h : Refines fine coarse) : Refines fine (refine g coarse) := by
  intro i j same
  obtain ⟨profiles, operands⟩ := stable i j same
  apply (refine_eq_iff g coarse i j).mpr
  refine ⟨h i j same, profiles, ?_⟩
  rw [← operandClasses_transport g h i, ← operandClasses_transport g h j, operands]

theorem stable_refines_run (g : Graph Op inputs sorts) {fine : Partition n} (stable : Stable g fine)
    (fuel : Nat) (p : Partition n) (h : Refines fine p) : Refines fine (run g fuel p) := by
  induction fuel generalizing p with
  | zero => exact h
  | succ fuel ih =>
      rw [run]
      split
      · exact h
      · exact ih _ (stable_refines_round g stable h)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint
