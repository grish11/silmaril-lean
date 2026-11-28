module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Example.Defs
import all Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.FlatPaper

/-! # Exact observations of the retained-bit fold and the two round endpoints -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Paper.EntryLetObstruction (U Observation)
open Paper.WithBoundEntryEta.NativeFrame.Retained (foldRegion)
open Paper.WithBoundEntryEta.NativeFrame.Retained.Example

private local instance : MarkArity where
  enabled n := decide (2 ≤ n)

private theorem singletonEnv {C : Ty Empty} {value : Val}
    (hv : Resumption.Typing.ValueTyped (fun (_ _ : Empty) => False) value C) :
    EnvTyped [C] (fun _ => value) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact hv
  | succ i => simp [At] at hi

private theorem separate {Γ L : VCtx (Ty Empty)} {r s : Region Instruction} {env : Env}
    (he : EnvTyped Γ env) {x y : Observation}
    (hx : observesFlat env r x) (hy : observesFlat env s y) (ne : x.payload ≠ y.payload) :
    ¬ Paper.Eqv Γ r s L := by
  intro eq
  have hx' := (observesFlat_eq_of_paper eq env he x).mp hx
  exact ne (congrArg Exit.value (observe_unique _ _ hx' hy))

theorem retained_rounds_ne : ¬ Paper.Eqv [Bit] once twice [Output] := by
  let env : Env := fun _ => .inl .unit
  let changed : Observation := ⟨0, .inr (.inr .unit), true, false⟩
  let original : Observation := ⟨0, .inr (.inl .unit), true, false⟩
  have left : observesFlat env once changed := execute_sound 10 _ env rfl
  have right : observesFlat env twice original := execute_sound 10 _ env rfl
  exact separate (singletonEnv (.inl .unit)) left right (by intro h; cases h)

private theorem unit_literal {a : Tm Instruction} (ha : Tm.BranchValue [TaggedBit] a U) :
    a = .unit := by
  cases ha with
  | @var i _ hi => cases i <;> simp [At, TaggedBit, Bit, U] at hi
  | unit => rfl

private theorem bit_literal {a : Tm Instruction} (ha : Tm.BranchValue [TaggedBit] a Bit) :
    a = .inl .unit ∨ a = .inr .unit := by
  cases ha with
  | @var i _ hi => cases i <;> simp [At, TaggedBit, Bit, U] at hi
  | inl hv => exact Or.inl (congrArg Tm.inl (unit_literal hv))
  | inr hv => exact Or.inr (congrArg Tm.inr (unit_literal hv))

theorem retained_fold_ne_constructor {a : Tm Instruction} (ha : Tm.BranchValue [TaggedBit] a Bit) :
    ¬ Paper.Eqv [TaggedBit] foldRegion (.br 0 a) [Bit] := by
  let left : Observation := ⟨0, .inl .unit, false, false⟩
  let right : Observation := ⟨0, .inr .unit, false, false⟩
  rcases bit_literal ha with rfl | rfl
  · let env : Env := fun _ => .inl (.inr .unit)
    have x : observesFlat env foldRegion right := execute_sound 4 _ env rfl
    have y : observesFlat env (.br 0 (.inl .unit)) left := execute_sound 4 _ env rfl
    exact separate (singletonEnv (.inl (.inr .unit))) x y (by intro h; cases h)
  · let env : Env := fun _ => .inl (.inl .unit)
    have x : observesFlat env foldRegion left := execute_sound 4 _ env rfl
    have y : observesFlat env (.br 0 (.inr .unit)) right := execute_sound 4 _ env rfl
    exact separate (singletonEnv (.inl (.inl .unit))) x y (by intro h; cases h)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
