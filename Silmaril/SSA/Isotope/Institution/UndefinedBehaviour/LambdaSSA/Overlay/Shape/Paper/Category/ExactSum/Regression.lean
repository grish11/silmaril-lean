module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.ExactSum.Thms

/-! The actual guarded Paper copair keeps the selected arm's state changes,
faults and divergence. Its left input cannot see observations of the right. -/

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumCofanIsColimit)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape (ValueTyped)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBPaperExactSumRegression

private inductive Instr where
  | left | right

private abbrev τ := Ty Empty
private abbrev U : τ := .unit

local instance : HasTy Instr τ := ⟨fun _ => U, fun _ => U⟩

private abbrev fixture : Shape.Model Instr ([] : List τ) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun f a s v t =>
      a = .unit ∧ v = .unit ∧ t = s + (match f with | .left => 1 | .right => 2)
    faults := fun f _ s t => t = s + (match f with | .left => 10 | .right => 20)
    prim := fun f _ _ => match f with | .left => False | .right => True
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by rintro _ _ _ _ _ _ ⟨_, rfl, _⟩; exact .unit

private abbrev arm (f : Instr) : LambdaSSA.Region Instr :=
  .let₁ (.op f (.var 0)) (.br 0 (.var 0))

private theorem arm_typed (f : Instr) : ValueBranches [U] (arm f) [U] :=
  .let₁ (.op (f := f) (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private noncomputable def caseArrow : ofType (Φ := Instr) (.coprod U U) ⟶ ofType U :=
  (sumCofanIsColimit U U).desc (BinaryCofan.mk (ofRegion (arm_typed .left)) (ofRegion (arm_typed .right)))

private noncomputable def observations {v : Value Unit} (typed : ValueTyped fixture.atomType v (.coprod U U)) :
    Behaviour 1 Unit Nat :=
  ((singletonInterpretation fixture).map caseArrow).run (0 : Fin 1) ⟨v, typed⟩ 4

private noncomputable def armObservations (f : Instr) : Behaviour 1 Unit Nat :=
  Shape.denote (.native ⟨arm f, (arm_typed f).hasType⟩) (fixture.extend .unit) 4

private theorem selected_left :
    observations (.inl .unit) = armObservations .left := by
  have mapped := singleton_map_sumDesc fixture (ofRegion (arm_typed .left)) (ofRegion (arm_typed .right))
  exact (congrArg (fun f => f.run (0 : Fin 1) ⟨.inl .unit, .inl .unit⟩ 4) mapped).trans
    (singletonInterpretation_map_ofRegion fixture (arm_typed .left) .unit 4)

private theorem selected_right :
    observations (.inr .unit) = armObservations .right := by
  have mapped := singleton_map_sumDesc fixture (ofRegion (arm_typed .left)) (ofRegion (arm_typed .right))
  exact (congrArg (fun f => f.run (0 : Fin 1) ⟨.inr .unit, .inr .unit⟩ 4) mapped).trans
    (singletonInterpretation_map_ofRegion fixture (arm_typed .right) .unit 4)

private abbrev runtime := envOfBound (fixture.extend (A := U) .unit).raw.bound

private theorem left_return : (observations (.inl .unit)).Ordinary (.ret (0 : Fin 1) .unit 5) := by
  rw [selected_left]
  exact ⟨WithTop.coe_ne_top, Region.Eval.let₁ (.op .var ⟨rfl, rfl, rfl⟩) (.br .var)⟩

private theorem left_fault : (observations (.inl .unit)).Ordinary (.fault 14) := by
  rw [selected_left]
  exact ⟨WithTop.coe_ne_top, Region.Fault.let₁_arg (.op_fault .var rfl)⟩

private theorem left_excludes_right_fault : ¬ (observations (.inl .unit)).Ordinary (.fault 24) := by
  rw [selected_left]
  intro bad
  have fault : Region.Fault fixture.raw.instr fixture.raw.faults runtime (arm .left) 4 24 := bad.2
  cases fault with
  | let₁_arg arg =>
    cases arg with
    | op_arg arg => cases arg
    | op_fault evaluated wrong =>
      cases evaluated
      change 24 = 4 + 10 at wrong
      omega
  | let₁_body _ body => cases body with | br arg => cases arg

private theorem left_excludes_right_divergence : ¬ (observations (.inl .unit)).Ordinary .diverge := by
  rw [selected_left]
  intro bad
  have diverges : External.Diverges fixture.raw.instr fixture.raw.prim (.region runtime (arm .left) 4) := bad.2
  cases diverges.unfold with
  | let₁_arg arg =>
    cases arg with
    | op_arg arg => cases arg
    | primitive _ impossible => exact impossible
  | core step =>
    cases step with
    | let₁ _ body =>
      cases body.unfold with
      | core step => cases step
      | br arg => cases arg

private theorem right_return : (observations (.inr .unit)).Ordinary (.ret (0 : Fin 1) .unit 6) := by
  rw [selected_right]
  exact ⟨WithTop.coe_ne_top, Region.Eval.let₁ (.op .var ⟨rfl, rfl, rfl⟩) (.br .var)⟩

private theorem right_fault : (observations (.inr .unit)).Ordinary (.fault 24) := by
  rw [selected_right]
  exact ⟨WithTop.coe_ne_top, Region.Fault.let₁_arg (.op_fault .var rfl)⟩

private theorem right_divergence : (observations (.inr .unit)).Ordinary .diverge := by
  rw [selected_right]
  exact ⟨WithTop.coe_ne_top, External.Diverges.fold (.let₁_arg (.primitive .var trivial))⟩

#print axioms singleton_preservesFiniteCoproducts
#print axioms singleton_map_sumDesc
#print axioms singleton_map_emptyElim
#print axioms left_return
#print axioms left_fault
#print axioms left_excludes_right_fault
#print axioms left_excludes_right_divergence
#print axioms right_return
#print axioms right_fault
#print axioms right_divergence

end LambdaSSAUBPaperExactSumRegression
