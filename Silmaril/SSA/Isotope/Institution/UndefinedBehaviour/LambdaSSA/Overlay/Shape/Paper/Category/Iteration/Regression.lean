module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Thms

/-! A state-changing request precedes the tag-producing request on each step.
From zero the iterator repeats once before returning, faulting, or diverging
inside the second step. From two it instead has an infinite repeat path. -/

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion iterateSum)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
  (singlePayload iterationGraph tagIterationOutcome iterationGraph_block_ordinary)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

namespace LambdaSSAUBPaperIterationRegression

private inductive Instr where
  | advance | request

private abbrev U : Ty Empty := .unit

local instance : HasTy Instr (Ty Empty) :=
  ⟨fun _ => U, fun f => match f with | .advance => U | .request => .coprod U U⟩

private abbrev fixture : Shape.Model Instr ([] : List (Ty Empty)) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun f a s v t =>
      a = .unit ∧ match f with
      | .advance => v = .unit ∧ t = s + 1
      | .request => v = (if s = 2 then .inl .unit else .inr .unit) ∧ t = s
    faults := fun f _ s t => match f with
      | .advance => False
      | .request => s = 2 ∧ t = 12
    prim := fun f _ s => match f with
      | .advance => False
      | .request => s = 2
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    intro f _ _ v s _ h
    cases f with
    | advance => obtain ⟨_, rfl, _⟩ := h; exact .unit
    | request =>
      obtain ⟨_, reply, _⟩ := h
      rw [reply]
      split
      · exact .inl .unit
      · exact .inr .unit

private abbrev stepSyntax : LambdaSSA.Region Instr :=
  .let₁ (.op .advance (.var 0)) (.let₁ (.op .request (.var 0)) (.br 0 (.var 0)))

private theorem stepTyped : ValueBranches [U] stepSyntax [.coprod U U] :=
  .let₁ (.op (f := Instr.advance) (.var (i := 0) rfl))
    (.let₁ (.op (f := Instr.request) (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl)))

private abbrev step : ofType (Φ := Instr) U ⟶ ofType (.coprod U U) := ofRegion stepTyped
private abbrev input : singlePayload (atomType := fixture.atomType) U := ⟨.unit, .unit⟩

private noncomputable abbrev seen := (singletonInterpretation fixture).map step
private noncomputable abbrev seenAt (s : Nat) : Behaviour 1 Unit Nat :=
  Shape.denote (.native ⟨stepSyntax, stepTyped.hasType⟩) (fixture.extend (A := U) .unit) s

private noncomputable abbrev graph : Feedback.Run [U] [U] Unit Nat := iterationGraph seen input

private noncomputable abbrev loop (s : Nat) : Behaviour 1 Unit Nat :=
  ((singletonInterpretation fixture).map (iterateSum step)).run (0 : Fin 1) input s

private theorem first_step (s : Nat) : Feedback.Step graph (.entry s) (.block 0 .unit s) :=
  .branch ⟨WithTop.coe_ne_top, rfl⟩

private theorem block_ordinary (s : Nat) (o : Outcome 2 Unit Nat) :
    (graph (.block 0 .unit s)).Ordinary o ↔ (seenAt s).Ordinary (tagIterationOutcome o) :=
  iterationGraph_block_ordinary seen input input s o

private theorem step_return (s : Nat) :
    (seenAt s).Ordinary (.ret 0 (if s + 1 = 2 then .inl .unit else .inr .unit) (s + 1)) :=
  ⟨WithTop.coe_ne_top, Region.Eval.let₁ (.op .var ⟨rfl, rfl, rfl⟩)
    (.let₁ (.op .var ⟨rfl, rfl, rfl⟩) (.br .var))⟩

private theorem repeat_edge {s : Nat} (next : s + 1 ≠ 2) :
    Feedback.Step graph (.block 0 .unit s) (.block 0 .unit (s + 1)) := by
  apply Feedback.Step.branch
  apply (block_ordinary s (.ret 0 .unit (s + 1))).mpr
  simpa [tagIterationOutcome, next] using step_return s

private theorem reach_second : Feedback.Reaches graph (.entry 0) (.block 0 .unit 1) :=
  (Relation.ReflTransGen.single (first_step 0)).tail (repeat_edge (s := 0) (by decide))

private theorem return_after_repeat : (loop 0).Ordinary (.ret 0 .unit 2) := by
  apply (singleton_iterateSum_ordinary_iff fixture step input 0 _).mpr
  refine .inl ⟨.block 0 .unit 1, reach_second, ?_⟩
  apply (block_ordinary 1 (.ret 1 .unit 2)).mpr
  simpa [tagIterationOutcome] using step_return 1

private theorem fault_after_repeat : (loop 0).Ordinary (.fault 12) := by
  apply (singleton_iterateSum_ordinary_iff fixture step input 0 _).mpr
  refine .inl ⟨.block 0 .unit 1, reach_second, ?_⟩
  apply (block_ordinary 1 (.fault 12)).mpr
  exact ⟨WithTop.coe_ne_top, Region.Fault.let₁_body (.op .var ⟨rfl, rfl, rfl⟩)
    (.let₁_arg (.op_fault .var ⟨rfl, rfl⟩))⟩

private theorem divergence_in_second_step :
    Feedback.Finite graph (.entry 0) .diverge ∧ (loop 0).Ordinary .diverge := by
  have finite : Feedback.Finite graph (.entry 0) .diverge := by
    refine ⟨.block 0 .unit 1, reach_second, ?_⟩
    apply (block_ordinary 1 .diverge).mpr
    exact ⟨WithTop.coe_ne_top, External.Diverges.fold_core (.let₁ (.op .var ⟨rfl, rfl, rfl⟩)
      (.fold (.let₁_arg (.primitive .var rfl))))⟩
  exact ⟨finite, (singleton_iterateSum_ordinary_iff fixture step input 0 _).mpr (.inl finite)⟩

private theorem infinite_replay :
    Feedback.Infinite graph (.entry 2) ∧ (loop 2).Ordinary .diverge := by
  have infinite : Feedback.Infinite graph (.entry 2) := by
    refine ⟨fun | 0 => .entry 2 | n + 1 => .block 0 .unit (2 + n), rfl, ?_⟩
    intro j
    cases j with
    | zero => exact first_step 2
    | succ j => exact repeat_edge (by omega)
  exact ⟨infinite, (singleton_iterateSum_ordinary_iff fixture step input 2 _).mpr (.inr ⟨rfl, infinite⟩)⟩

#print axioms singleton_map_iterateSum
#print axioms singleton_map_iterateSum_eq_overlay
#print axioms singleton_map_iterateSum_unfold
#print axioms singleton_iterateSum_ordinary_iff
#print axioms return_after_repeat
#print axioms fault_after_repeat
#print axioms divergence_in_second_step
#print axioms infinite_replay

end LambdaSSAUBPaperIterationRegression
