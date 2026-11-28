module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Transfer

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness Family
open Silmaril.Semantics.Dataflow.FiniteHeight (HeightBound)

universe u v
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {shape : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {calls : CallTransfer shape} {past : List (Ports (Ty V S))}
variable (template : Template Op shape imports calls past)

private theorem includes_mono {n : Nat} {small large : Feedback.Mask n} (h : small ⊆ large)
    (p : Nat) (live : Feedback.includes small p = true) : Feedback.includes large p = true := by
  by_cases valid : p < n
  · simp only [Feedback.includes, dite_eq_left valid, decide_eq_true_eq] at live ⊢
    exact h live
  · simp [Feedback.includes, valid] at live

private theorem includes_demandMask {n : Nat} (demand : Demand) {p : Nat} (valid : p < n) :
    Feedback.includes (demandMask (arity := n) demand) p = demand p := by
  simp [Feedback.includes, valid, demandMask]

private theorem rowTransfer_mono {low high : Rows shape} (le : low ≤ high) :
    TransferLE (member := some shape) (rowTransfer shape low) (rowTransfer shape high) :=
  fun _ _ => inputAddresses_mono (Finset.biUnion_mono fun _ _ _ h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le (Finset.mem_filter.mp h).2⟩)

private theorem step_le {low high : MemberTransfer shape.members.length}
    (le : TransferLE (member := some shape) low high) : step template low ≤ step template high := by
  intro bit live
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact plan_compare (template.body bit.1) (left := calls.lift low) (right := calls.lift high) (calls.lift_mono le)
    (fun _ _ h => h) (Finset.mem_filter.mp live).2

theorem round_mono : Monotone template.round :=
  fun _ _ le => step_le template (rowTransfer_mono le)

private def operator : Rows shape →o Rows shape :=
  ⟨template.round, round_mono template⟩

private theorem synthesize_eq_solve :
    template.synthesize = (height (shape := shape)).solve (operator template) := by
  have h := (height (shape := shape)).iterateUntilStable_eq_some (operator template)
  unfold Template.synthesize
  rw [show (operator template : Rows shape → Rows shape) = template.round from rfl] at h
  rw [h]

theorem synthesize_fixed : template.round template.synthesize = template.synthesize := by
  rw [synthesize_eq_solve template]
  exact (height (shape := shape)).solve_fixed (operator template)

theorem synthesize_le {upper : Rows shape} (prefixed : template.round upper ≤ upper) :
    template.synthesize ≤ upper := by
  rw [synthesize_eq_solve template]
  exact (height (shape := shape)).solve_le_of_prefixed (operator template) prefixed

private theorem projection_le (reads : MemberTransfer shape.members.length) :
    TransferLE (member := some shape) (rowTransfer shape (rowsOfTransfer (shape := shape) reads)) reads := by
  intro i demand address live
  obtain ⟨p, _, selected⟩ := List.mem_filterMap.mp live
  split at selected
  · next needed =>
      cases selected
      obtain ⟨mask, contained, active⟩ := Finset.mem_biUnion.mp needed
      have submask := Finset.mem_powerset.mp contained
      have more (q : Nat) (demanded : Feedback.includes mask q = true) : demand q = true := by
        by_cases valid : q < (shape.at i).fn.results.length
        · have fromMask : (⟨q, valid⟩ : Fin (shape.at i).fn.results.length) ∈ mask := by
            simpa only [Feedback.includes, dite_eq_left valid, decide_eq_true_eq] using demanded
          simpa only [demandMask, Finset.mem_filter, Finset.mem_univ, true_and] using submask fromMask
        · unfold Feedback.includes at demanded
          split at demanded
          · exact False.elim (valid (by assumption))
          · simp at demanded
      apply reads.monotone i more
      simpa only [row, rowsOfTransfer, Finset.mem_filter, Finset.mem_univ, true_and] using active
  · simp at selected

theorem synthesize_le_supplied (reads : MemberTransfer shape.members.length)
    (closed : step template reads ≤ rowsOfTransfer (shape := shape) reads) :
    ∀ i demand, template.summaries.live i demand ⊆ reads.live i demand := by
  have bounds := synthesize_le template ((step_le template (projection_le reads)).trans closed)
  intro i demand address live
  exact projection_le reads i demand (rowTransfer_mono bounds i demand live)

theorem round_rows_mono (rows : Rows shape) (i : Fin shape.members.length) :
    Monotone (row shape (template.round rows) i) := by
  intro smaller larger le p h
  simp only [row, Template.round, step, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  let reads := calls.lift (rowTransfer shape rows)
  exact plan_compare (template.body i) (left := reads) (right := reads) (fun _ _ _ live => live) (fun q _ => includes_mono le q) h

theorem synthesize_rows_mono (i : Fin shape.members.length) : Monotone (row shape template.synthesize i) := by
  rw [← synthesize_fixed template]
  exact round_rows_mono template template.synthesize i

theorem synthesize_read (i : Fin shape.members.length) (demand : Demand) :
    readRow shape template.synthesize i demand = row shape template.synthesize i (demandMask demand) := by
  apply Finset.Subset.antisymm
  · apply Finset.biUnion_subset.mpr
    exact fun _ small => synthesize_rows_mono template i (Finset.mem_powerset.mp small)
  · exact Finset.subset_biUnion_of_mem _ (Finset.mem_powerset_self _)

theorem synthesized_closed (safe : template.ReferenceSafe) (i : Fin shape.members.length) (demand : Demand) :
    let live := (((template.body i).withTransfer template.callReads).plan demand).live
    (∀ p, p < (memberPorts shape.members).length → .arg p ∉ live) ∧
    ∀ p, .arg ((memberPorts shape.members).length + p) ∈ live → .arg p ∈ template.summaries.live i demand := by
  dsimp only
  let reads := template.callReads
  refine ⟨?_, ?_⟩
  · intro p below active
    exact safe i ⟨p, below⟩ (plan_compare (template.body i) (left := reads) (right := reads)
      (fun _ _ _ h => h) (fun _ _ _ => rfl) active)
  · intro p active
    have bounded := plan_arg_in_range _ demand active
    simp only [List.length_append] at bounded
    have valid : p < ((shape.at i).captures ++ (shape.at i).fn.args).length := by
      simp only [List.length_append]
      omega
    let position : Fin ((shape.at i).captures ++ (shape.at i).fn.args).length := ⟨p, valid⟩
    have found : position ∈ row shape (template.round template.synthesize) i (demandMask demand) := by
      simp only [row, Template.round, step, Finset.mem_filter, Finset.mem_univ, true_and]
      exact plan_compare (template.body i) (left := reads) (right := reads)
        (fun _ _ _ h => h) (fun q inRange h => (includes_demandMask demand inRange).trans h) active
    rw [synthesize_fixed template] at found
    change .arg p ∈ inputAddresses (readRow shape template.synthesize i demand)
    rw [synthesize_read template]
    exact List.mem_filterMap.mpr ⟨position, List.mem_finRange _, by rw [ite_eq_left found]⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
