module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Native constructor readback of the two retained-bit rows -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameIteration

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.NativeFrame WithBoundEntryEta.NativeFrame.Retained.Example
open WithBoundEntryEta.Generators (weakenRows)
open EntryLetObstruction (U)
open SequencingObstruction (Instruction)
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Silmaril.DeBruijn (lift)

set_option backward.isDefEq.respectTransparency false

private abbrev labels : Fin 2 → Ty Empty := fun _ => U

private abbrev leftArm : Region Instruction := .br 0 (.var 0)
private abbrev rightArm : Region Instruction := .br 1 (.var 0)

private theorem row_typed (j : Fin 2) : HasType [U, U, U] (rows j) [U, U, Bit] :=
  Fin.cases (.br (ℓ := 2) rfl (.inr .unit)) (fun _ => .br (ℓ := 2) rfl (.inl .unit)) j

private theorem rows_specialized (θ : Nat → Tm Instruction) :
    (fun j => ((weakenRows rows) j).substVars (Tm.liftSubst (Tm.liftSubst θ))) = rows := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

private theorem reduce_table {entry : Region Instruction} {reply : Tm Instruction} (j : Fin 2)
    (entry_eq : Paper.Eqv [U, U] entry (.br j (.var 1)) [U, U, Bit])
    (row_eq : (rows j).substVars (Tm.singleSubst (.var 1)) = .br 2 reply)
    (value : Tm.BranchValue [U, U] reply Bit) :
    Paper.Eqv [U, U] (.cfg entry 2 rows) (.br 0 reply) [Bit] := by
  have arg : Tm.BranchValue [U, U] (.var 1 : Tm Instruction) U := .var rfl
  have enter : Paper.Eqv [U, U] (.cfg (.br j (.var 1)) 2 rows)
      (.cfg (.let₁ (.var 1) (rows j)) 2 rows) [Bit] :=
    .cfgEta (.native (.base (.entry (.cfgBrLocal labels j arg row_typed))))
  have beta : Paper.Eqv [U, U] (.let₁ (.var 1) (rows j)) (.br 2 reply) [U, U, Bit] := by
    rw [← row_eq]
    exact .cfgEta (.native (.letValue arg (row_typed j)))
  have exit : Paper.Eqv [U, U] (.cfg (.br 2 reply) 2 rows) (.br 0 reply) [Bit] :=
    .cfgEta (.native (.base (.entry (.cfgBrExit labels (ℓ := 0) rfl value row_typed))))
  exact (Paper.Eqv.cfg labels entry_eq (fun k => .refl (row_typed k))).trans
    (enter.trans ((Paper.Eqv.cfg labels beta (fun k => .refl (row_typed k))).trans exit))

private abbrev leftValue : Tm.BranchValue [U] (.inl (.var 0) : Tm Instruction) Bit := .inl (.var rfl)
private abbrev rightValue : Tm.BranchValue [U] (.inr (.var 0) : Tm Instruction) Bit := .inr (.var rfl)

private abbrev leftSub : Nat → Tm Instruction := Tm.singleSubst (.inl (.var 0)) ∘ lift Nat.succ
private abbrev rightSub : Nat → Tm Instruction := Tm.singleSubst (.inr (.var 0)) ∘ lift Nat.succ

private def requestThen (reply : Tm Instruction) : Region Instruction :=
  .let₁ (.op .tick .unit) (.br 0 reply)

private theorem left_selected :
    Paper.Eqv [U] (update.substVars leftSub) (requestThen (.inr .unit)) [Bit] := by
  change Paper.Eqv [U] (.let₁ (.op .tick .unit) (.cfg (.case (.inl (.var 1)) leftArm rightArm) 2
    (fun j => ((weakenRows rows) j).substVars (Tm.liftSubst (Tm.liftSubst leftSub))))) _ _
  rw [rows_specialized]
  have arg : Tm.BranchValue [U, U] (.var 1 : Tm Instruction) U := .var rfl
  have hl : HasType [U, U, U] leftArm [U, U, Bit] := .br (ℓ := 0) rfl (.var rfl)
  have hr : HasType [U, U, U] rightArm [U, U, Bit] := .br (ℓ := 1) rfl (.var rfl)
  exact .let₁ (.op .unit) (reduce_table 0
    (.cfgEta (.native ((SubstitutionEquiv.base (.caseInl arg.hasType hl hr)).trans (.letValue arg hl))))
    rfl (.inr .unit))

private theorem right_selected :
    Paper.Eqv [U] (update.substVars rightSub) (requestThen (.inl .unit)) [Bit] := by
  change Paper.Eqv [U] (.let₁ (.op .tick .unit) (.cfg (.case (.inr (.var 1)) leftArm rightArm) 2
    (fun j => ((weakenRows rows) j).substVars (Tm.liftSubst (Tm.liftSubst rightSub))))) _ _
  rw [rows_specialized]
  have arg : Tm.BranchValue [U, U] (.var 1 : Tm Instruction) U := .var rfl
  have hl : HasType [U, U, U] leftArm [U, U, Bit] := .br (ℓ := 0) rfl (.var rfl)
  have hr : HasType [U, U, U] rightArm [U, U, Bit] := .br (ℓ := 1) rfl (.var rfl)
  exact .let₁ (.op .unit) (reduce_table 1
    (.cfgEta (.native ((SubstitutionEquiv.base (.caseInr arg.hasType hl hr)).trans (.letValue arg hr))))
    rfl (.inl .unit))

private theorem request_guarded : ValueBranches [U] (requestThen .unit) [U] :=
  .let₁ (.op .unit) (.br rfl .unit)

private noncomputable abbrev requestArrow : B ⟶ B := ofRegion request_guarded

private noncomputable abbrev leftTag : B ⟶ A := (sumCofan U U).inl
private noncomputable abbrev rightTag : B ⟶ A := (sumCofan U U).inr

private theorem leftTag_eq : leftTag = ofRegion (.br (ℓ := 0) rfl leftValue) :=
  sumCofan_inl U U

private theorem rightTag_eq : rightTag = ofRegion (.br (ℓ := 0) rfl rightValue) :=
  sumCofan_inr U U

private theorem left_round :
    leftTag ≫ ofRegion update_guarded = requestArrow ≫ rightTag := by
  let h := specialize_guarded leftValue update_guarded
  have result : ValueBranches [U] (requestThen (.inr .unit)) [Bit] :=
    .let₁ (.op .unit) (.br rfl (.inr .unit))
  rw [leftTag_eq, WithEntryLet.ofRegion_comp_constructor leftValue update_guarded h,
    (ofRegion_eq_iff h result).2 left_selected, rightTag_eq]
  exact (ofRegion_comp request_guarded (.br (ℓ := 0) rfl rightValue) result).symm

private theorem right_round :
    rightTag ≫ ofRegion update_guarded = requestArrow ≫ leftTag := by
  let h := specialize_guarded rightValue update_guarded
  have result : ValueBranches [U] (requestThen (.inl .unit)) [Bit] :=
    .let₁ (.op .unit) (.br rfl (.inl .unit))
  rw [rightTag_eq, WithEntryLet.ofRegion_comp_constructor rightValue update_guarded h,
    (ofRegion_eq_iff h result).2 right_selected, leftTag_eq]
  exact (ofRegion_comp request_guarded (.br (ℓ := 0) rfl leftValue) result).symm

theorem double_iterate : iterate g₂ = iterate g := by
  apply iterate_double_of_switching_rows g requestArrow requestArrow
  · change leftTag ≫ (ofRegion update_guarded ≫ (coprod.inr : A ⟶ B ⨿ A)) = _
    rw [← Category.assoc, left_round, Category.assoc]
    rfl
  · change rightTag ≫ (ofRegion update_guarded ≫ (coprod.inr : A ⟶ B ⨿ A)) = _
    rw [← Category.assoc, right_round, Category.assoc]
    rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameIteration
